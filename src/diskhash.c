/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

/*
This particular file is a fork of the "diskhash" library by Luis
Pedro Coelho and others. All changes from the original are marked
with my initials (SDT).

Original source: https://github.com/luispedro/diskhash/

Copyright information for the original diskhash library:

Copyright (c) 2017
Luis Pedro Coelho <luis@luispedro.org>

Permission is hereby granted, free of charge, to any person
obtaining a copy of this software and associated documentation
files (the "Software"), to deal in the Software without
restriction, including without limitation the rights to use,
copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following
conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
OTHER DEALINGS IN THE SOFTWARE.
*/

#define _GNU_SOURCE  /* SDT; needed for F_OFD_SETLK */

#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <errno.h>

#include <unistd.h>
#include <fcntl.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>

#include "diskhash.h"
/* SDT: removed includes of primes.h and rtable.h */

enum {
    HT_FLAG_CAN_WRITE = 1
    /* SDT: removed flag HT_FLAG_HASH_2 */
    /* SDT: removed HT_FLAG_IS_LOADED */
};

typedef struct HashTableHeader {
    char magic[16];
    HashTableOpts opts_;
    size_t cursize_;
    size_t slots_used_;
    size_t padding_;  /* SDT added to make header a multiple of 16 bytes */
} HashTableHeader;

typedef struct HashTableEntry {
    const char* ht_key;
    /* SDT: removed ht_data */
} HashTableEntry;

static
uint64_t hash_key(const char* k) {
    /* SDT: replaced the hash function with something that just takes the
       first 64 bytes of the input. Our keys are SHA-256 hashes already
       so there is no need to hash them any further. */
    /* SDT: also removed "use_hash_2" function parameter. */
    uint64_t result = 0;
    for (int i = 0; i < 8; ++i) {
        result <<= 8;
        result |= (uint64_t)(uint8_t)(k[i]);
    }
    return result;
}

inline static
size_t aligned_size(size_t s) {
    size_t s_8bytes = s & ~0x7;
    return s_8bytes == s ? s : (s_8bytes + 8);
}

inline static
HashTableHeader* header_of(DiskHashTable* ht) {
    return (HashTableHeader*)ht->data_;
}

inline static
const HashTableHeader* cheader_of(const DiskHashTable* ht) {
    return (const HashTableHeader*)ht->data_;
}

inline static
int is_64bit(const DiskHashTable* ht) {
    return cheader_of(ht)->cursize_ > (1L << 32);
}

inline static
size_t node_size_opts(HashTableOpts opts) {
    /* SDT: removed object_datalen */
    /* SDT: renamed key_maxlen, and removed +1 as we no longer have
       null terminators */
    return aligned_size(opts.key_len);
}

inline static
size_t node_size(const DiskHashTable* ht) {
    return node_size_opts(cheader_of(ht)->opts_);
}

inline static
int entry_empty(const HashTableEntry et) {
    return !et.ht_key;
}

void* hashtable_of(DiskHashTable* ht) {
    return (unsigned char*)ht->data_ + sizeof(HashTableHeader);
}


static
uint64_t get_table_at(const DiskHashTable* ht, uint64_t ix) {
    assert(ix < cheader_of(ht)->cursize_);
    if (is_64bit(ht)) {
        uint64_t* table = (uint64_t*)hashtable_of((DiskHashTable*)ht);
        return table[ix];
    } else {
        uint32_t* table = (uint32_t*)hashtable_of((DiskHashTable*)ht);
        return table[ix];
    }
}

static
void set_table_at(DiskHashTable* ht, uint64_t ix, const uint64_t val) {
    if (is_64bit(ht)) {
        uint64_t* table = (uint64_t*)hashtable_of(ht);
        table[ix] = val;
    } else {
        uint32_t* table = (uint32_t*)hashtable_of(ht);
        table[ix] = val;
    }
}

/* SDT: removed show_ht function */

static
HashTableEntry entry_at(const DiskHashTable* ht, size_t ix) {
    ix = get_table_at(ht, ix);
    HashTableEntry r;
    if (ix == 0) {
        r.ht_key = 0;
        /* SDT: removed ht_data */
        return r;
    }
    --ix;
    const size_t sizeof_table_elem = is_64bit(ht) ? sizeof(uint64_t) : sizeof(uint32_t);
    const char* node_data = (const char*)ht->data_
                            + sizeof(HashTableHeader)
                            + cheader_of(ht)->cursize_ * sizeof_table_elem;
    r.ht_key = node_data + ix * node_size(ht);
    /* SDT: removed ht_data */
    return r;
}

HashTableOpts dht_zero_opts() {
    HashTableOpts r;
    /* SDT: renamed key_maxlen and removed object_datalen */
    r.key_len = 0;
    return r;
}

/* SDT: added lock_file function. Note we don't need a corresponding
   unlock_file because the lock is automatically released when the file
   is closed. */
static bool lock_file(int fd, bool read_only)
{
    struct flock lock = {0};
    lock.l_type = read_only ? F_RDLCK : F_WRLCK;
    lock.l_whence = SEEK_SET;
    int result = fcntl(fd, F_OFD_SETLK, &lock);
    return result == 0;  // zero means success
}

DiskHashTable* dht_open(const char* fpath, HashTableOpts opts, int flags, char** err) {
    if (!fpath || !*fpath) return NULL;
    const int fd = open(fpath, flags, 0644);
    int needs_init = 0;
    if (fd < 0) {
        if (err) { *err = strdup("open call failed."); }
        return NULL;
    }

    /* SDT: added file locking. */
    if (!lock_file(fd, (flags & O_ACCMODE) == O_RDONLY)) {
        if (err) *err = strdup("failed to obtain lock");
        return NULL;
    }

    DiskHashTable* rp = (DiskHashTable*)malloc(sizeof(DiskHashTable));
    if (!rp) {
        if (err) { *err = NULL; }
        return NULL;
    }
    rp->fd_ = fd;
    rp->fname_ = strdup(fpath);
    if (!rp->fname_) {
        if (err) { *err = NULL; }
        close(rp->fd_);
        free(rp);
        return NULL;
    }
    struct stat st;
    fstat(rp->fd_, &st);
    rp->datasize_ = st.st_size;
    if (rp->datasize_ == 0) {
        needs_init = 1;
        /* SDT: initial size changed to 8 (from 7) */
        rp->datasize_ = sizeof(HashTableHeader) + 8 * sizeof(uint32_t) + 4 * node_size_opts(opts);
        if (ftruncate(fd, rp->datasize_) < 0) {
            if (err) {
                *err = malloc(256);
                if (*err) {
                    snprintf(*err, 256, "Could not allocate disk space. Error: %s.", strerror(errno));
                }
            }
            close(rp->fd_);
            free((char*)rp->fname_);
            free(rp);
            return NULL;
        }
    }
    rp->flags_ = 0;

    /* SDT: changed flags == O_RDONLY to a bit-test, as flags might contain
       other things such as O_CLOEXEC. */
    const int prot = ((flags & O_ACCMODE) == O_RDONLY) ?
                                PROT_READ
                                : PROT_READ|PROT_WRITE;
    if (prot & PROT_WRITE) rp->flags_ |= HT_FLAG_CAN_WRITE;
    rp->data_ = mmap(NULL,
            rp->datasize_,
            prot,
            MAP_SHARED,
            rp->fd_,
            0);
    if (rp->data_ == MAP_FAILED) {
        if (err) { *err = strdup("mmap() call failed."); }
        close(rp->fd_);
        free((char*)rp->fname_);
        free(rp);
        return NULL;
    }
    if (needs_init) {
        /* SDT: changed magic number as this format is now incompatible
           with the original DiskBasedHash. Also I wanted a non-ascii
           character in the magic number to reduce probability of
           confusion with a text file. */
        strcpy(header_of(rp)->magic, "BAB_CACHE\001");
        header_of(rp)->opts_ = opts;
        header_of(rp)->cursize_ = 8; /* SDT (was 7) */
        header_of(rp)->slots_used_ = 0;
        header_of(rp)->padding_ = 0; /* SDT */
    } else if (strcmp(header_of(rp)->magic, "BAB_CACHE\001")) {
        if (err) { *err = strdup("Magic number does not match expected."); }
        dht_free(rp);
        return 0;
    /* SDT: renamed key_maxlen, removed object_datalen */
    } else if ((header_of(rp)->opts_.key_len != opts.key_len && opts.key_len != 0)) {
        if (err) { *err = strdup("Options mismatch (diskhash table on disk was not created with the same options used to open it)."); }
        dht_free(rp);
        return 0;
    }
    return rp;
}

/* SDT: removed function dht_load_to_memory */

void dht_free(DiskHashTable* ht) {
    /* SDT: removed flag HT_FLAG_IS_LOADED */
    /* SDT: added null ptr check */
    if (ht == NULL) return;
    munmap(ht->data_, ht->datasize_);
    fsync(ht->fd_);
    close(ht->fd_);
    free((char*)ht->fname_);
    free(ht);
}

char random_char(void) {
    const char* available =
        "0123456789"
        "abcdefghijklmnopqrstuvwxyz"
        "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    return available[rand() % (26*2 + 10)];
}


char* generate_tempname_from(const char* base) {
    char* res = (char*)malloc(strlen(base) + 21);
    if (!res) return NULL;
    strcpy(res, base);
    char* p = res;
    while (*p) ++p;
    *p++ = '.';
    int i;
    for (i = 0; i < 19; ++i) {
        *p++ = random_char();
    }
    *p = 0;
    return res;
}

size_t dht_reserve(DiskHashTable* ht, size_t cap, char** err) {
    if (!(ht->flags_ & HT_FLAG_CAN_WRITE)) {
        if (err) { *err = strdup("Hash table is read-only. Cannot call dht_reserve."); }
        return -EACCES;
    }
    if (header_of(ht)->cursize_ / 2 > cap) {
        return header_of(ht)->cursize_ / 2;
    }
    const uint64_t starting_slots = cheader_of(ht)->slots_used_;
    const uint64_t min_slots = cap * 2;  /* SDT removed +1 here. */

    /* SDT: Removed the requirement for the size to be prime. Our keys
       are SHA-256 (truncated) so should be pretty randomly distributed,
       so there isn't really any need to use a prime size.
       However, I decided to make the size a multiple of 8, so that the
       keys start on a 16-byte boundary, for what that's worth.
    */
    const uint64_t n = (min_slots + 7u) & (~(uint64_t)7);

    cap = n / 2;
    const size_t sizeof_table_elem = is_64bit(ht) ? sizeof(uint64_t) : sizeof(uint32_t);
    const size_t total_size = sizeof(HashTableHeader) + n * sizeof_table_elem + cap * node_size(ht);

    DiskHashTable* temp_ht = (DiskHashTable*)malloc(sizeof(DiskHashTable));
    while (1) {
        temp_ht->fname_ = generate_tempname_from(ht->fname_);
        if (!temp_ht->fname_) {
            if (err) { *err = NULL; }
            free(temp_ht);
            return 0;
        }
        temp_ht->fd_ = open(temp_ht->fname_, O_EXCL | O_CREAT | O_RDWR, 0600 );
        if (temp_ht->fd_) break;
        free((char*)temp_ht->fname_);
    }
    if (ftruncate(temp_ht->fd_, total_size) < 0) {
        if (err) {
            *err = malloc(256);
            if (*err) {
                snprintf(*err, 256, "Could not allocate disk space. Error: %s.", strerror(errno));
            }
        }
        free((char*)temp_ht->fname_);
        free(temp_ht);
        return 0;
    }
    temp_ht->datasize_ = total_size;
    temp_ht->data_ = mmap(NULL,
            temp_ht->datasize_,
            PROT_READ|PROT_WRITE,
            MAP_SHARED,
            temp_ht->fd_,
            0);
    temp_ht->flags_ = ht->flags_;
    if (temp_ht->data_ == MAP_FAILED) {
        if (err) {
            const int errorbufsize = 512;
            *err = (char*)malloc(errorbufsize);
            if (*err) {
                snprintf(*err, errorbufsize, "Could not mmap() new hashtable: %s.\n", strerror(errno));
            }
        }
        close(temp_ht->fd_);
        unlink(temp_ht->fname_);
        free((char*)temp_ht->fname_);
        free(temp_ht);
        return 0;
    }
    memcpy(header_of(temp_ht), header_of(ht), sizeof(HashTableHeader));
    header_of(temp_ht)->cursize_ = n;
    header_of(temp_ht)->slots_used_ = 0;

    /* SDT: removed reference to DiskBasedHash10 */

    HashTableEntry et;
    for (uint64_t i = 0; i < header_of(ht)->slots_used_; ++i) {
        set_table_at(ht, 0, i + 1);
        et = entry_at(ht, 0);
        /* SDT: removed reference to ht_data */
        dht_insert(temp_ht, et.ht_key, NULL);
    }

    const char* temp_fname = strdup(temp_ht->fname_);
    if (!temp_fname) {
        if (err) { *err = NULL; }
        unlink(temp_ht->fname_);
        dht_free(temp_ht);
        return 0;
    }

    dht_free(temp_ht);
    const HashTableOpts opts = header_of(ht)->opts_;

    munmap(ht->data_, ht->datasize_);
    close(ht->fd_);

    rename(temp_fname, ht->fname_);
    free((void*)temp_fname);  /* SDT changed to fix compiler warning (discarded qualifier) */

    temp_ht = dht_open(ht->fname_, opts, O_RDWR, err);
    if (!temp_ht) {
        /* err is set by dht_open */
        return 0;
    }
    free((char*)ht->fname_);
    memcpy(ht, temp_ht, sizeof(DiskHashTable));
    free(temp_ht);
    assert(starting_slots == cheader_of(ht)->slots_used_);
    return cap;
}

size_t dht_size(const DiskHashTable* ht) {
    return cheader_of(ht)->slots_used_;
}

/* SDT: return changed to bool */
bool dht_lookup(const DiskHashTable* ht, const char* key) {
    /* SDT: removed HT_FLAG_HASH_2 reference */
    uint64_t h = hash_key(key) % cheader_of(ht)->cursize_;
    uint64_t i;
    for (i = 0; i < cheader_of(ht)->cursize_; ++i) {
        HashTableEntry et = entry_at(ht, h);
        if (!et.ht_key) return false;
        /* SDT: strcmp changed to memcmp */
        if (!memcmp(et.ht_key, key, cheader_of(ht)->opts_.key_len)) return true;
        ++h;
        if (h == cheader_of(ht)->cursize_) h = 0;
    }
    fprintf(stderr, "dht_lookup: the code should never have reached this line.\n");
    return false;
}

/* SDT: removed data arg */
int dht_insert(DiskHashTable* ht, const char* key, char** err) {
    if (!(ht->flags_ & HT_FLAG_CAN_WRITE)) {
        if (err) { *err = strdup("Hash table is read-only. Cannot insert."); }
        return -EACCES;
    }
    /* SDT: removed keylen check */
    /* Max load is 50% */
    if (cheader_of(ht)->cursize_ / 2 <= cheader_of(ht)->slots_used_) {
        /* SDT: because I removed the primes table, this cannot be
           slots_used + 1 any more. Multiply up by 1.5 instead. */
        if (!dht_reserve(ht, cheader_of(ht)->slots_used_ * 3u / 2u, err)) return -ENOMEM;
    }
    /* SDT: removed reference to HT_FLAG_HASH_2 */
    uint64_t h = hash_key(key) % cheader_of(ht)->cursize_;
    while (1) {
        HashTableEntry et = entry_at(ht, h);
        if (entry_empty(et)) break;
        /* SDT: changed strcmp to memcmp */
        if (!memcmp(et.ht_key, key, cheader_of(ht)->opts_.key_len)) {
            return 0;
        }
        ++h;
        if (h == cheader_of(ht)->cursize_) {
            h = 0;
        }
    }
    set_table_at(ht, h, header_of(ht)->slots_used_ + 1);
    ++header_of(ht)->slots_used_;
    HashTableEntry et = entry_at(ht, h);

    /* SDT: changed strcpy to memcpy; removed memcpy of object */
    memcpy((char*)et.ht_key, key, cheader_of(ht)->opts_.key_len);

    return 1;
}
