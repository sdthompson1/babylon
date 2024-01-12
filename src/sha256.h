/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

/*
This particular file is based on sha256.h by Brad Conte obtained from
here: https://github.com/B-Con/crypto-algorithms/blob/master/sha256.h.

The original code was released into the public domain by its author.

Original file information:
* Filename:   sha256.h
* Author:     Brad Conte (brad AT bradconte.com)
* Copyright:
* Disclaimer: This code is presented "as is" without any guarantees.
* Details:    Defines the API for the corresponding SHA1 implementation.
*/

#ifndef SHA256_H
#define SHA256_H

#include <stddef.h>
#include <stdint.h>

#define SHA256_HASH_LENGTH 32

struct SHA256_CTX {
    uint8_t data[64];
    uint32_t datalen;
    uint64_t bitlen;
    uint32_t state[8];
};

// start a new SHA256 hash
void sha256_init(struct SHA256_CTX *ctx);

// add a byte, or bytes, to the message
void sha256_add_byte(struct SHA256_CTX *ctx, uint8_t byte);
void sha256_add_bytes(struct SHA256_CTX *ctx, const uint8_t bytes[], size_t num_bytes);

// retrieve the final hash (of SHA256_HASH_LENGTH = 32 bytes)
void sha256_final(struct SHA256_CTX *ctx, uint8_t hash[]);

#endif
