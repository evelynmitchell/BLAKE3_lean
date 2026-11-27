//! The calls the other vector tests leave out, against both vector files
//! (official BLAKE3's and the Lean definition's, `vectors::FILES`): the
//! throughput calls on one thread and on many (`hash`, `hash_each`,
//! `hash_many`, `update_each`), and a `Hasher` fed through
//! `update_multithreaded`, its extended output read whole. The `Hasher`'s
//! own calls are `test_vectors/`'s, the C API's `capi/tests/vectors.rs`,
//! and the `Pipeline`'s `pipeline_pool.rs`.
//!
//! Every message is a prefix of one buffer: byte i of every vector file's
//! input is i % 251, whatever the input's length.

#[path = "../../tools/require_nextest.rs"]
mod require_nextest;

#[path = "../../test_vectors/src/parse.rs"]
mod vectors;

use blake3_servil::convenience::Hasher;
use blake3_servil::throughput::{self, Batch, Block};
use blake3_servil::{BLOCK_LEN, Mode, OUT_LEN};

/// A file's cases: each input length and its expected output in each mode,
/// in `modes` order.
struct Case {
    len: usize,
    outputs: [Vec<u8>; 3],
}

fn cases(file: &str, json: &str) -> (Vec<Case>, [Mode<'static>; 3]) {
    let data = vectors::parse_json(json);
    assert_eq!(data.key, "whats the Elvish word for friend", "{file}: the key");
    assert_eq!(data.context_string, "BLAKE3 2019-12-27 16:29:52 test vectors context", "{file}: the context");
    let cases =
        data.cases.iter().map(|c| Case { len: c.input_len, outputs: [&c.hash, &c.keyed_hash, &c.derive_key].map(|h| vectors::hex_decode(h)) }).collect();
    (cases, [Mode::Plain, Mode::Keyed(b"whats the Elvish word for friend"), Mode::DeriveKey("BLAKE3 2019-12-27 16:29:52 test vectors context")])
}

/// Blocks holding the longest input: every case's input is a prefix.
fn painted(cases: &[Case]) -> Vec<Block> {
    let max = cases.iter().map(|c| c.len).max().unwrap_or(0);
    let mut blocks = vec![Block::ZERO; max.div_ceil(BLOCK_LEN).max(1)];
    for (i, b) in Block::bytes_mut(&mut blocks).iter_mut().enumerate() {
        *b = (i % 251) as u8;
    }
    blocks
}

/// A message of `len` bytes from `painted`'s blocks: its own blocks alone.
fn message(blocks: &[Block], len: usize) -> (&[Block], usize) {
    (&blocks[..len.div_ceil(BLOCK_LEN).max(1)], len)
}

fn digest(case: &Case, m: usize) -> [u8; OUT_LEN] {
    case.outputs[m][..OUT_LEN].try_into().unwrap()
}

#[test]
fn hash_and_hash_each_on_one_thread_and_many() {
    blake3_servil::initialize_multithreaded(None);
    for (file, json) in vectors::FILES {
        let (cases, modes) = cases(file, json);
        let blocks = painted(&cases);
        let items: Vec<(&[Block], usize)> = cases.iter().map(|c| message(&blocks, c.len)).collect();
        for (m, mode) in modes.into_iter().enumerate() {
            for case in &cases {
                let (input, len) = message(&blocks, case.len);
                let what = format!("{file}, mode {m}, {len} bytes");
                assert_eq!(*throughput::hash(mode, input, len).as_bytes(), digest(case, m), "throughput::hash, {what}");
                assert_eq!(*throughput::hash_multithreaded(mode, input, len).as_bytes(), digest(case, m), "hash_multithreaded, {what}");
            }
            // Every case in one call: messages of every length side by side.
            let (mut one, mut many) = (vec![[0u8; OUT_LEN]; items.len()], vec![[0u8; OUT_LEN]; items.len()]);
            throughput::hash_each(mode, &items, &mut one);
            throughput::hash_each_multithreaded(mode, &items, &mut many);
            for ((case, a), b) in cases.iter().zip(&one).zip(&many) {
                assert_eq!(*a, digest(case, m), "hash_each, {file}, mode {m}, {} bytes", case.len);
                assert_eq!(*b, digest(case, m), "hash_each_multithreaded, {file}, mode {m}, {} bytes", case.len);
            }
        }
    }
}

#[test]
fn batches_on_one_thread_and_many() {
    blake3_servil::initialize_multithreaded(None);
    for (file, json) in vectors::FILES {
        let (cases, modes) = cases(file, json);
        let blocks = painted(&cases);
        for case in &cases {
            // Three copies of the message: lanes side by side.
            let mut batch = Batch::new(case.len, 3);
            for i in 0..3 {
                batch.set(i, &Block::bytes(&blocks)[..case.len]);
            }
            for (m, mode) in modes.into_iter().enumerate() {
                let (mut one, mut many) = ([[0u8; OUT_LEN]; 3], [[0u8; OUT_LEN]; 3]);
                throughput::hash_many(mode, &batch, &mut one);
                throughput::hash_many_multithreaded(mode, &batch, &mut many);
                let what = format!("{file}, mode {m}, {} bytes", case.len);
                assert!(one.iter().all(|d| *d == digest(case, m)), "hash_many, {what}");
                assert!(many.iter().all(|d| *d == digest(case, m)), "hash_many_multithreaded, {what}");
            }
        }
    }
}

#[test]
fn hashers_through_update_each_and_update_multithreaded() {
    blake3_servil::initialize_multithreaded(None);
    for (file, json) in vectors::FILES {
        let (cases, modes) = cases(file, json);
        let blocks = painted(&cases);
        let bytes = Block::bytes(&blocks);
        for (m, mode) in modes.into_iter().enumerate() {
            // A hasher a case, fed in two turns: the first 1000 bytes of
            // each, then the rest.
            let mut hashers: Vec<Hasher> = cases.iter().map(|_| Hasher::new(mode, None)).collect();
            let first: Vec<(usize, &[u8])> = cases.iter().enumerate().map(|(i, c)| (i, &bytes[..c.len.min(1000)])).collect();
            let rest: Vec<(usize, &[u8])> = cases.iter().enumerate().map(|(i, c)| (i, &bytes[c.len.min(1000)..c.len])).collect();
            throughput::update_each(&mut hashers, &first);
            throughput::update_each(&mut hashers, &rest);
            let mut out = vec![[0u8; OUT_LEN]; cases.len()];
            let which: Vec<usize> = (0..cases.len()).collect();
            throughput::finalize_each(&mut hashers, &which, &mut out);
            for (case, got) in cases.iter().zip(&out) {
                assert_eq!(*got, digest(case, m), "update_each, {file}, mode {m}, {} bytes", case.len);
            }
            // Pieces of 640 KiB, over the split threshold, and the whole
            // extended output.
            for case in &cases {
                let mut hasher = Hasher::new(mode, Some(case.len as u64));
                for piece in bytes[..case.len].chunks(640 * 1024) {
                    throughput::update_multithreaded(&mut hasher, piece);
                }
                let mut output = vec![0u8; case.outputs[m].len()];
                hasher.finalize_xof().fill(&mut output);
                assert_eq!(output, case.outputs[m], "update_multithreaded, {file}, mode {m}, {} bytes", case.len);
            }
        }
    }
}
