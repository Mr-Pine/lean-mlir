type CVWords = [u32; 8];
const BLOCK_LEN: usize = 64;
const IV: &CVWords = &[
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];
const MSG_SCHEDULE: [[usize; 16]; 7] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8],
    [3, 4, 10, 12, 13, 2, 7, 14, 6, 5, 9, 0, 11, 15, 8, 1],
    [10, 7, 12, 9, 14, 3, 13, 15, 4, 0, 11, 2, 5, 8, 1, 6],
    [12, 13, 9, 11, 15, 10, 14, 8, 7, 2, 5, 3, 0, 1, 6, 4],
    [9, 14, 11, 5, 8, 12, 15, 1, 13, 3, 0, 10, 2, 6, 4, 7],
    [11, 15, 5, 0, 1, 9, 8, 6, 14, 10, 2, 12, 3, 4, 7, 13],
];
#[inline(always)]
fn counter_low(counter: u64) -> u32 {
    counter as u32
}
#[inline(always)]
fn counter_high(counter: u64) -> u32 {
    (counter >> 32) as u32
}
mod platform {
#[inline(always)]
pub fn words_from_le_bytes_64(bytes: &[u8; 64]) -> [u32; 16] {
    let mut out = [0; 16];
    out[0] = u32::from_le_bytes(bytes[0 * 4..][..4].try_into().unwrap());
    out[1] = u32::from_le_bytes(bytes[1 * 4..][..4].try_into().unwrap());
    out[2] = u32::from_le_bytes(bytes[2 * 4..][..4].try_into().unwrap());
    out[3] = u32::from_le_bytes(bytes[3 * 4..][..4].try_into().unwrap());
    out[4] = u32::from_le_bytes(bytes[4 * 4..][..4].try_into().unwrap());
    out[5] = u32::from_le_bytes(bytes[5 * 4..][..4].try_into().unwrap());
    out[6] = u32::from_le_bytes(bytes[6 * 4..][..4].try_into().unwrap());
    out[7] = u32::from_le_bytes(bytes[7 * 4..][..4].try_into().unwrap());
    out[8] = u32::from_le_bytes(bytes[8 * 4..][..4].try_into().unwrap());
    out[9] = u32::from_le_bytes(bytes[9 * 4..][..4].try_into().unwrap());
    out[10] = u32::from_le_bytes(bytes[10 * 4..][..4].try_into().unwrap());
    out[11] = u32::from_le_bytes(bytes[11 * 4..][..4].try_into().unwrap());
    out[12] = u32::from_le_bytes(bytes[12 * 4..][..4].try_into().unwrap());
    out[13] = u32::from_le_bytes(bytes[13 * 4..][..4].try_into().unwrap());
    out[14] = u32::from_le_bytes(bytes[14 * 4..][..4].try_into().unwrap());
    out[15] = u32::from_le_bytes(bytes[15 * 4..][..4].try_into().unwrap());
    out
}
#[inline(always)]
pub fn le_bytes_from_words_64(words: &[u32; 16]) -> [u8; 64] {
    let mut out = [0; 64];
    *<&mut [u8; 4]>::try_from(&mut out[0 * 4..][..4]).unwrap() = words[0].to_le_bytes();
    *<&mut [u8; 4]>::try_from(&mut out[1 * 4..][..4]).unwrap() = words[1].to_le_bytes();
    *<&mut [u8; 4]>::try_from(&mut out[2 * 4..][..4]).unwrap() = words[2].to_le_bytes();
    *<&mut [u8; 4]>::try_from(&mut out[3 * 4..][..4]).unwrap() = words[3].to_le_bytes();
    *<&mut [u8; 4]>::try_from(&mut out[4 * 4..][..4]).unwrap() = words[4].to_le_bytes();
    *<&mut [u8; 4]>::try_from(&mut out[5 * 4..][..4]).unwrap() = words[5].to_le_bytes();
    *<&mut [u8; 4]>::try_from(&mut out[6 * 4..][..4]).unwrap() = words[6].to_le_bytes();
    *<&mut [u8; 4]>::try_from(&mut out[7 * 4..][..4]).unwrap() = words[7].to_le_bytes();
    *<&mut [u8; 4]>::try_from(&mut out[8 * 4..][..4]).unwrap() = words[8].to_le_bytes();
    *<&mut [u8; 4]>::try_from(&mut out[9 * 4..][..4]).unwrap() = words[9].to_le_bytes();
    *<&mut [u8; 4]>::try_from(&mut out[10 * 4..][..4]).unwrap() = words[10].to_le_bytes();
    *<&mut [u8; 4]>::try_from(&mut out[11 * 4..][..4]).unwrap() = words[11].to_le_bytes();
    *<&mut [u8; 4]>::try_from(&mut out[12 * 4..][..4]).unwrap() = words[12].to_le_bytes();
    *<&mut [u8; 4]>::try_from(&mut out[13 * 4..][..4]).unwrap() = words[13].to_le_bytes();
    *<&mut [u8; 4]>::try_from(&mut out[14 * 4..][..4]).unwrap() = words[14].to_le_bytes();
    *<&mut [u8; 4]>::try_from(&mut out[15 * 4..][..4]).unwrap() = words[15].to_le_bytes();
    out
}
}
#[inline(always)]
fn g(state: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize, x: u32, y: u32) {
    state[a] = state[a].wrapping_add(state[b]).wrapping_add(x);
    state[d] = (state[d] ^ state[a]).rotate_right(16);
    state[c] = state[c].wrapping_add(state[d]);
    state[b] = (state[b] ^ state[c]).rotate_right(12);
    state[a] = state[a].wrapping_add(state[b]).wrapping_add(y);
    state[d] = (state[d] ^ state[a]).rotate_right(8);
    state[c] = state[c].wrapping_add(state[d]);
    state[b] = (state[b] ^ state[c]).rotate_right(7);
}
#[inline(always)]
fn round(state: &mut [u32; 16], msg: &[u32; 16], round: usize) {
    // Select the message schedule based on the round.
    let schedule = MSG_SCHEDULE[round];

    // Mix the columns.
    g(state, 0, 4, 8, 12, msg[schedule[0]], msg[schedule[1]]);
    g(state, 1, 5, 9, 13, msg[schedule[2]], msg[schedule[3]]);
    g(state, 2, 6, 10, 14, msg[schedule[4]], msg[schedule[5]]);
    g(state, 3, 7, 11, 15, msg[schedule[6]], msg[schedule[7]]);

    // Mix the diagonals.
    g(state, 0, 5, 10, 15, msg[schedule[8]], msg[schedule[9]]);
    g(state, 1, 6, 11, 12, msg[schedule[10]], msg[schedule[11]]);
    g(state, 2, 7, 8, 13, msg[schedule[12]], msg[schedule[13]]);
    g(state, 3, 4, 9, 14, msg[schedule[14]], msg[schedule[15]]);
}
#[inline(always)]
fn compress_pre(
    cv: &CVWords,
    block: &[u8; BLOCK_LEN],
    block_len: u8,
    counter: u64,
    flags: u8,
) -> [u32; 16] {
    let block_words = crate::platform::words_from_le_bytes_64(block);

    let mut state = [
        cv[0],
        cv[1],
        cv[2],
        cv[3],
        cv[4],
        cv[5],
        cv[6],
        cv[7],
        IV[0],
        IV[1],
        IV[2],
        IV[3],
        counter_low(counter),
        counter_high(counter),
        block_len as u32,
        flags as u32,
    ];

    round(&mut state, &block_words, 0);
    round(&mut state, &block_words, 1);
    round(&mut state, &block_words, 2);
    round(&mut state, &block_words, 3);
    round(&mut state, &block_words, 4);
    round(&mut state, &block_words, 5);
    round(&mut state, &block_words, 6);

    state
}
#[inline(always)]
pub fn compress_xof(
    cv: &CVWords,
    block: &[u8; BLOCK_LEN],
    block_len: u8,
    counter: u64,
    flags: u8,
) -> [u8; 64] {
    let mut state = compress_pre(cv, block, block_len, counter, flags);
    state[0] ^= state[8];
    state[1] ^= state[9];
    state[2] ^= state[10];
    state[3] ^= state[11];
    state[4] ^= state[12];
    state[5] ^= state[13];
    state[6] ^= state[14];
    state[7] ^= state[15];
    state[8] ^= cv[0];
    state[9] ^= cv[1];
    state[10] ^= cv[2];
    state[11] ^= cv[3];
    state[12] ^= cv[4];
    state[13] ^= cv[5];
    state[14] ^= cv[6];
    state[15] ^= cv[7];
    crate::platform::le_bytes_from_words_64(&state)
}
#[inline(always)]
pub fn compress_in_place(
    cv: &mut CVWords,
    block: &[u8; BLOCK_LEN],
    block_len: u8,
    counter: u64,
    flags: u8,
) {
    let state = compress_pre(cv, block, block_len, counter, flags);

    cv[0] = state[0] ^ state[8];
    cv[1] = state[1] ^ state[9];
    cv[2] = state[2] ^ state[10];
    cv[3] = state[3] ^ state[11];
    cv[4] = state[4] ^ state[12];
    cv[5] = state[5] ^ state[13];
    cv[6] = state[6] ^ state[14];
    cv[7] = state[7] ^ state[15];
}

#[unsafe(no_mangle)]
pub fn agave_portable_compress_xof(cv:&CVWords, block:&[u8;64], len:u8,counter:u64,flags:u8)->[u8;64] { compress_xof(cv,block,len,counter,flags) }
#[unsafe(no_mangle)]
pub fn agave_portable_compress_in_place(cv:&mut CVWords, block:&[u8;64], len:u8,counter:u64,flags:u8) { compress_in_place(cv,block,len,counter,flags); }
