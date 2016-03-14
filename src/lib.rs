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
                // println!("(a, b): {:?}", (a, b));
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

pub fn cast_votes(string: &str, window_size: usize) -> Vec<usize> {
    let mut out: Vec<usize> = vec![0; string.chars().count()];

    let trie = trie::frequency_trie_from_string(string, window_size+1);
    let stats = TrieStats::from_trie(&trie);
    let entropy_expert = EntropyExpert::new(&trie, &stats);
    let frequency_expert = FrequencyExpert::new(&trie, &stats);
    let experts: [Box<Expert>; 2] = [
        Box::new(entropy_expert), 
        Box::new(frequency_expert)
    ];

    for offset in 0..(string.len()-window_size) {
        let offset_bytes = string.chars()
            .take(offset).fold(0usize, |acc, c| acc + c.len_utf8());
        let byte_len = string[offset_bytes..].chars()
            .take(window_size).fold(0usize, |acc, c| acc + c.len_utf8());
        let key = &string[offset_bytes..(offset_bytes + byte_len)];

        for expert in experts.iter() {
            let vote = expert.vote(&key);
            out[vote + offset] += 1;
        }
    }
    out
}

pub fn split_string<'a>(string: &'a str, votes: &[usize], window_size: usize, threshold: usize) -> Vec<&'a str> {
    let mut boundaries: Vec<usize> = Vec::new();
    for (idx, window) in votes.windows(window_size).enumerate() {
        let (max_idx, max_val) = window.iter().enumerate().max_by_key(|w| w.1).unwrap();
        let abs_index = max_idx + idx;
        if *max_val >= threshold && boundaries.last().and_then(|b| Some(*b != abs_index)).unwrap_or(true) {
            boundaries.push(abs_index);
        }
    }

    let mut out: Vec<&str> = Vec::new();

    let mut byte_index = 0usize;
    let mut char_iter = string.chars();
    let mut last_boundary = 0;

    for boundary in boundaries {
        let mut new_byte_index = byte_index;
        for _ in 0..(boundary - last_boundary) {
            new_byte_index += char_iter.next().unwrap().len_utf8();
        }
        out.push(&string[byte_index..new_byte_index]);
        last_boundary = boundary;
        byte_index = new_byte_index;
    }
    out
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

#[test]
fn test_vote_casting() {
    let string = "itwasabright";
    let votes = cast_votes(&string, 3);
    println!("votes: {:?}", votes);
}

#[test]
fn test_splitting() {
    let string = "itwasabrightcolddayinaprilandtheclockswerestrikingthirteenwinstonsmithhischinnuzzledintohisbreastinanefforttoescapethevilewindslippedquicklythroughtheglassdoorsofvictorymansionsthoughnotquicklyenoughtopreventaswirlofgrittydustfromenteringalongwithhimthehallwaysmeltofboiledcabbageandoldragmatsatoneendofitacolouredpostertoolargeforindoordisplayhadbeentackedtothewallitdepictedsimplyanenormousfacemorethanametrewidethefaceofamanofaboutfortyfivewithaheavyblackmoustacheandruggedlyhandsomefeatur";
    let votes = cast_votes(&string, 6);
    let res: Vec<&str> = split_string(&string, &votes, 6, 3);
    for r in res {
        println!("{}", r);
    }
}
