#![feature(str_char)]
mod trie;

use trie::{Trie, TrieKey, TrieStats, Key};

pub trait Expert {
    /// Casts a vote to place a boundary after usize
    fn vote(&self, string: &str) -> usize;
}

pub struct EntropyExpert<'a, K: 'a + TrieKey, V: 'a> {
    trie: &'a Trie<K, V>,
    stats: &'a TrieStats
}

pub struct FrequencyExpert<'a, K: 'a + TrieKey, V: 'a> {
    trie: &'a Trie<K, V>,
    stats: &'a TrieStats
}

impl<'a, K, V> EntropyExpert<'a, K, V> 
where K: 'a + TrieKey, 
      V: 'a
{
    pub fn new(trie: &'a Trie<K, V>, stats: &'a TrieStats) -> EntropyExpert<'a, K, V> {
        EntropyExpert {
            trie: trie,
            stats: stats
        }
    }
}

impl<'a, K, V> FrequencyExpert<'a, K, V> 
where K: 'a + TrieKey, 
      V: 'a
{
    pub fn new(trie: &'a Trie<K, V>, stats: &'a TrieStats) -> FrequencyExpert<'a, K, V> {
        FrequencyExpert {
            trie: trie,
            stats: stats
        }
    }
}

impl<'a> Expert for EntropyExpert<'a, Key<'a>, u32> {
    fn vote(&self, string: &str) -> usize {
        let mut winner: (usize, f64) = (0, 0.);
        for i in 1..(string.len()+1) {
            if string.is_char_boundary(i) {
                let (a, b): (&str, &str) = string.split_at(i);
                println!("(a, b): {:?}", (a, b));
                let aent = self.stats.normalized(self.trie, &Key(a))
                    .1.unwrap_or(0.);
                let bent = self.stats.normalized(self.trie, &Key(b))
                    .1.unwrap_or(0.);

                let entropy = aent + bent;
                if entropy > winner.1 {
                    winner = (i, entropy);
                }
            }
        }
        winner.0
    }
}

impl<'a> Expert for FrequencyExpert<'a, Key<'a>, u32> {
    fn vote(&self, string: &str) -> usize {
        let mut winner: (usize, f64) = (0, 0.);
        for i in 1..(string.len()+1) {
            if string.is_char_boundary(i) {
                let (a, b): (&str, &str) = string.split_at(i);
                let afreq = self.stats.normalized(self.trie, &Key(a))
                    .0.unwrap_or(0.);
                let bfreq = self.stats.normalized(self.trie, &Key(b))
                    .0.unwrap_or(0.);

                let frequency = afreq + bfreq;
                if frequency > winner.1 {
                    winner = (i, frequency);
                }
            }
        }
        winner.0
    }
}

#[test]
fn test_entropy_expert() {
    let string = "abcabd";
    let trie = trie::frequency_trie_from_string(string, 4);
    let stats = TrieStats::from_trie(&trie);
    let expert = EntropyExpert::new(&trie, &stats);
    println!("stats: {:?}", stats);
    println!("voted: {}", expert.vote(&"abc"));
    assert_eq!(2, expert.vote(&"abc"));
    assert_eq!(2, expert.vote(&"ab"));
    assert_eq!(1, expert.vote(&"bca"));
}

#[test]
fn test_frequency_expert() {
    let string = "abcabd";
    let trie = trie::frequency_trie_from_string(string, 4);
    let stats = TrieStats::from_trie(&trie);
    let expert = FrequencyExpert::new(&trie, &stats);
    println!("stats: {:?}", stats);
    println!("voted: {}", expert.vote(&"abc"));
    assert_eq!(2, expert.vote(&"abc"));
    assert_eq!(1, expert.vote(&"ab"));
    assert_eq!(1, expert.vote(&"bca"));
}

