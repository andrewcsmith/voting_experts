extern crate radix_trie;
use radix_trie::{Trie, TrieKey, TrieCommon, NibbleVec, ContainsTrieNode};

use std::iter::Iterator;
use std::str::*;
use std::collections::HashMap;
use std::ops::Neg;

#[derive(PartialEq, Eq, Clone, Debug, Copy)]
pub struct Key<'a>(pub &'a str);

impl<'a> Key<'a> {
    pub fn new(s: &'a str) -> Key {
        Key(s)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a> TrieKey for Key<'a> {
    fn encode(&self) -> NibbleVec {
        NibbleVec::from_byte_vec(self.0.bytes().collect())
    }
}

/// If the key exists, increment the value. Otherwise, insert the key and initialize to a value of
/// 1.
pub fn insert_or_increment<'a>(trie: &mut Trie<Key<'a>, u32>, key: Key<'a>) {
    let old_value = trie.insert(key, 1u32);
    match old_value {
        Some(x) => { *trie.get_mut(&key).unwrap() = x + 1u32; }
        None => { }
    }
}

/// Constructs a frequency trie from a boxed iterator
pub fn build_frequency_trie<'a, I: Iterator<Item=Key<'a>>>(items: Box<I>) -> Trie<Key<'a>, u32> {
    let mut trie: Trie<Key<'a>, u32> = Trie::new();
    for item in items {
        insert_or_increment(&mut trie, item);
    }
    trie
}

/// Constructs a frequency trie from a string, which must be made of 1-byte chars
pub fn frequency_trie_from_string<'a, 'b: 'a>(string: &'a str, limit: usize) -> Trie<Key<'a>, u32> {
    let vector: &'a [u8] = string.as_bytes();
    let chained_iter = (1..(limit+1)).flat_map(|i| vector.windows(i)).map(|v| {
        Key(from_utf8(v).unwrap())
    });
    build_frequency_trie(Box::new(chained_iter))
}

/// Only works with ascii strings
#[allow(dead_code)]
pub fn conditional_probability<'a>(trie: &Trie<Key<'a>, u32>, key: Key<'a>) -> Option<f64> {
    trie.subtrie(&key).and_then(|node| {
        node.value().and_then(|node_val| {
            let prefix = from_utf8(&key.0.as_bytes()[0..key.0.len() - 1]).unwrap();
            trie.get_ancestor(&Key(prefix)).and_then(|ancestor| {
                println!("{:?} {:?}", node.key().unwrap(), ancestor.key().unwrap());
                Some(*node_val as f64 / *ancestor.value().unwrap() as f64)
            })
        })
    })
}

/// Get the boundary entropy of a given node
pub fn boundary_entropy<'b, 'a: 'b>(trie: &'b Trie<Key<'a>, u32>, key: Key) -> Option<f64> {
    trie.subtrie(&key)
        .and_then(|ref n| Some(boundary_entropy_recur(trie, n).neg()))
}

fn boundary_entropy_recur<'a: 'b, 'b, 'c: 'd, 'd, T, S>(trie: T, start: &'d S) -> f64 
    where T: TrieCommon<'a, Key<'a>, u32>,
          &'d S: TrieCommon<'c, Key<'c>, u32>
{
    // Starting from the top, iterate through all children of the given trie or subtrie
    trie.children().fold(0f64, |acc, ref child| {
        // If the particular child node has a value
        match child.value() {
            Some(val) => {
                let n = start.trie_node();
                let start_key_len = n.key().and_then(|k| Some(k.len() + 1));
                let zero = 0;
                let start_key_val = n.value().unwrap_or(&zero);
                let c_key_len = child.key().and_then(|k| Some(k.len()));
                // If the key length is greater than the start key length + 1
                if c_key_len > start_key_len {
                    let cond_prob = (*start_key_val as f64).recip();
                    acc + cond_prob * cond_prob.log2()
                } else {
                    let cond_prob = *val as f64 / *start_key_val as f64;
                    acc + cond_prob * cond_prob.log2()
                }
            }
            None => { 
                boundary_entropy_recur(child, start) 
            }
        }
    })
}

#[derive(Debug)]
pub struct TrieStats {
    /// Frequency stats for a given length as (mean, stddev)
    pub frequency: HashMap<usize, (f64, f64)>,
    /// Boundary entropy stats for a given length as (mean, stddev)
    pub entropy: HashMap<usize, (f64, f64)>
}

impl TrieStats {
    pub fn new() -> TrieStats {
        TrieStats {
            frequency: HashMap::new(),
            entropy: HashMap::new()
        }
    }

    pub fn from_trie<'a>(trie: &Trie<Key<'a>, u32>) -> TrieStats {
        let mut stats = TrieStats::new();
        let max_key_length: usize = trie.keys().max_by_key(|x| x.len()).unwrap().len();

        for key_length in 1..(max_key_length + 1) {
            let frequencies: Vec<&u32> = trie.keys().filter_map(|k| {
                if k.len() == key_length {
                    trie.get(&k)
                } else {
                    None
                }
            }).collect();

            if frequencies.len() == 0 { continue }

            let mean_frequency = frequencies.iter().fold(0, |acc, &f| {
                acc + f
            }) as f64 / frequencies.len() as f64;

            let stddev_frequency = (frequencies.iter().fold(0f64, |acc, &f| {
                let dev: f64 = *f as f64 - mean_frequency;
                acc + dev.abs()
            }) / frequencies.len() as f64).sqrt();

            let entropies: Vec<f64> = trie.keys().filter_map(|k| {
                if k.len() == key_length {
                    boundary_entropy(&trie, *k)
                } else {
                    None
                }
            }).collect();

            let mean_entropy = entropies.iter().fold(0f64, |acc, &f| {
                acc + f
            }) as f64 / entropies.len() as f64;

            let stddev_entropy = (entropies.iter().fold(0f64, |acc, &f| {
                let dev: f64 = f as f64 - mean_entropy;
                acc + dev.abs()
            }) / entropies.len() as f64).sqrt();

            stats.frequency.insert(key_length, (mean_frequency, stddev_frequency));
            stats.entropy.insert(key_length, (mean_entropy, stddev_entropy));
        }

        stats
    }

    pub fn normalized<'a>(&self, trie: &Trie<Key<'a>, u32>, key: Key<'a>) -> (Option<f64>, Option<f64>) {
        let default: (f64, f64) = (0., 0.);
        let f: &(f64, f64) = self.frequency.get(&key.len())
            .unwrap_or(&default);
        let e: &(f64, f64) = self.entropy.get(&key.len())
            .unwrap_or(&default);
        let norm_freq = trie.get(&key)
            .map(|v| norm_stat(*v as f64, f));
        let norm_entr = boundary_entropy(&trie, key)
            .map(|v| norm_stat(v, e));
        (norm_freq, norm_entr)
    }
}

fn norm_stat(val: f64, mean_std: &(f64, f64)) -> f64 {
    if val == mean_std.0 || mean_std.1 == 0. {
        0.
    } else {
        (val - mean_std.0) / mean_std.1
    }
}

#[test]
fn test_insert_or_increment() {
    let key = Key("hi");
    let mut trie = Trie::new();
    insert_or_increment(&mut trie, key);
    assert_eq!((&key, &1u32), trie.iter().next().unwrap());
    insert_or_increment(&mut trie, key);
    assert_eq!((&key, &2u32), trie.iter().next().unwrap());
}

#[test]
fn test_build_frequency_trie() {
    let string = "banana";
    let vector: Vec<char> = string.chars().collect();
    let str_vec: Vec<String> = vector.windows(1).chain(vector.windows(2)).map(|v| {
        v.iter().map(|s| s.to_owned()).collect::<String>()
    }).collect();
    let chained_iter = str_vec.iter().map(|s| Key(&s));
    let trie = build_frequency_trie(Box::new(chained_iter));
    // We expect there to be a frequency of 3 for "a"
    assert_eq!(&3u32, trie.get(&Key("a")).unwrap());
    // We expect there to be a frequency of 2 for "an"
    assert_eq!(&2u32, trie.get(&Key("an")).unwrap());
    // We expect there to be a frequency of 1 for "ba"
    assert_eq!(&1u32, trie.get(&Key("ba")).unwrap());
}

#[test]
fn test_frequency_trie_from_string() {
    let string = "banana";
    let vector: Vec<char> = string.chars().collect();
    let str_vec: Vec<String> = vector.windows(1).chain(vector.windows(2)).map(|v| {
        v.iter().map(|s| s.to_owned()).collect::<String>()
    }).collect();
    let chained_iter = str_vec.iter().map(|s| Key(&s));
    let trie = build_frequency_trie(Box::new(chained_iter));
    let another_trie = frequency_trie_from_string(string, 2);
    for (k, v) in another_trie.iter() { 
        println!("{}: {}", &k.0, &v);
    }
    assert_eq!(trie.len(), another_trie.len());
}

#[test]
fn test_conditional_probability() {
    let string = "banani";
    let vector: Vec<char> = string.chars().collect();
    let str_vec: Vec<String> = vector.windows(1).chain(vector.windows(2)).map(|v| {
        v.iter().map(|s| s.to_owned()).collect::<String>()
    }).collect();
    let chained_iter = str_vec.iter().map(|s| Key(&s));
    let trie = build_frequency_trie(Box::new(chained_iter));

    let key = Key("an");
    let res: f64 = conditional_probability(&trie, key).unwrap();
    assert_eq!(1.0, res);
    let key = Key("na");
    let res: f64 = conditional_probability(&trie, key).unwrap();
    assert_eq!(0.5, res);
}

#[test]
fn test_boundary_entropy() {
    let string = "abcabd";
    let trie = frequency_trie_from_string(string, 2);
    assert_eq!(0.0, boundary_entropy(&trie, Key("a")).unwrap());
    assert_eq!(1.0, boundary_entropy(&trie, Key("b")).unwrap());
}

#[test]
fn test_trie_stats() {
    let string = "abcabd";
    let trie = frequency_trie_from_string(string, 2);
    let stats = TrieStats::from_trie(&trie);
    println!("stats: {:?}", stats);
    let normed = stats.normalized(&trie, Key("a"));
    println!("normed: {:?}", normed);
    assert!((normed.0.unwrap() - 0.707107).abs() < 1.0e-4);
    assert!((normed.1.unwrap() - -0.408248).abs() < 1.0e-4);
}
