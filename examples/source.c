#include "stdint.h"

/* floor((a + b) / 2) with no overflow */
uint64_t avg(uint64_t a, uint64_t b) {
    return (a & b) + ((a ^ b) >> 1);
}

/* Feistel encrypt and decrypt */
__attribute__((noinline)) __uint128_t encrypt_round(uint64_t left, uint64_t right, uint64_t key) {
    __uint128_t f = ((__uint128_t) right * (__uint128_t) key) ^ (((__uint128_t)0x1234567890abcdef) << 56 | 0xdeadbeefcaffee);
    uint64_t new_right = left ^ f;
    return ((__uint128_t)right << 64) | new_right;
}

__attribute__((noinline)) __uint128_t decrypt_round(__uint128_t encrypted, uint64_t key) {
    uint64_t original_right = encrypted >> 64;
    __uint128_t f = ((__uint128_t) original_right * (__uint128_t) key) ^ (((__uint128_t)0x1234567890abcdef) << 56 | 0xdeadbeefcaffee);
    uint64_t left = encrypted ^ f;
    return ((__uint128_t)left << 64) | original_right;
}

/* Collatz step */
int collatz_step(int n) {
    if (n % 2 == 0) {
        return n / 2;
    } else {
        return 3 * n + 1;
    }
}

/* Fibonacci */
uint64_t fib(uint64_t n) {
    uint64_t a = 0;
    uint64_t b = 1;
    while (n--) {
        a += b;
        uint64_t tmp = b;
        b = a;
        a = tmp;
    }
    return a;
}

/* Memory */
void swap_elements(int *array, int index_a, int index_b) {
    int temp = array[index_a];
    array[index_a] = array[index_b];
    array[index_b] = temp;
}

/* Function calls */
__uint128_t feistel_id (__uint128_t lr, uint64_t key) {
    uint64_t left = lr >> 64;
    uint64_t right = lr;
    __uint128_t enc = encrypt_round(left, right, key);
    return decrypt_round(enc, key);
}

/* Patterns */
#define encdec(lr, key) ({ \
    uint64_t encdec_left = (lr) >> 64; \
    uint64_t encdec_right = (lr); \
    __uint128_t encdec_enc = encrypt_round(encdec_left, encdec_right, (key)); \
    decrypt_round(encdec_enc, (key)); \
})

__uint128_t feistel_id_20 (__uint128_t lr, uint64_t key) {
    #pragma clang loop unroll(full)
    for (int i = 0; i < 20; i++) lr = encdec(lr, key);
    return lr;
}