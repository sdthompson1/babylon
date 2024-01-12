/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

/*
This particular file is a fork of the "diskhash" library by Luis
Pedro Coelho and others. All changes from the original are marked
with my initials (SDT). The main changes are:

 - Key is now exactly "n" bytes long (without null terminator)
   instead of upto "n" bytes long (with a null terminator).
   I do this because my keys are all exactly 32 bytes, so a
   terminator character isn't needed.

 - "Objects" associated with each key were removed (as I only need the
   keys).

 - Some simple file locking was added (to reduce the risk of multiple
   processes opening the DB at the same time and therefore corrupting
   it).

 - Removed some features that I am not using.

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


#ifndef DISKHASH_H_INCLUDE_GUARD__
#define DISKHASH_H_INCLUDE_GUARD__
#include <stddef.h>
#include <stdbool.h>   /* SDT */

#ifdef __cplusplus
extern "C" {
#endif


/* SDT: changed from "key_maxlen" to "key_len" here, and removed
 * "object_datalen". */

/**
 * key_len is the length of the key (in bytes). All keys must
 * have the exact same size.
 *
 * Internally, space is allocated on 8-Byte aligned boundaries, so multiples
 * of 8 are good choices for key_len.
 *
 */
typedef struct HashTableOpts {
    size_t key_len;
} HashTableOpts;

/* SDT: renamed the struct from HashTable to DiskHashTable to avoid
   conflicts with hash_table.h. */
typedef struct DiskHashTable {
    int fd_;
    const char* fname_;
    void* data_;
    size_t datasize_;
    int flags_;
} DiskHashTable;


/** Zero-valued options
 */
HashTableOpts dht_zero_opts(void);

/* SDT: changed key_maxlen to key_len in the below example, and
   removed object_datalen. */

/** Open a hash table file
 *
 * fpath is the file path
 * flags are passed to call to open() and the user should read the documentation therein
 *
 * Values returned from dht_open must be freed with dht_free.
 *
 * Examples:
 *
 * Read-write:
 *
 *      HashTableOpts opts;
 *      opts.key_len = 16;
 *      char* err;
 *      HashTable* ht = dht_open("hashtable.dht", opts, O_RDWR|O_CREAT, &err);
 *
 * Read-only:
 *
 *      char* err;
 *      HashTable* ht = dht_open("hashtable.dht", opts, O_RDONLY, &err);
 *
 * When opening an existing disk table, you can pass `{ 0, 0 }` (the return
 * value of `dht_zero_opts()`) as the options, in which case the values will be
 * taken from the table on disk. If you do pass values > 0, they are checked
 * against the values on disk and it is an error if there is a mismatch.
 *
 * The last argument is an error output argument. If it is set to a non-NULL
 * value, then the memory must be released with free(). Passing NULL is valid
 * (and no error message will be produced). An error return with *err == NULL
 * will mean an out-of-memory error (when dht fails to allocate memory, it does
 * not try to allocate memory for an error message).
 */
DiskHashTable* dht_open(const char* fpath, HashTableOpts opts, int flags, char**);

/** Load table into memory
 *
 * Return:
 *   0 : success
 *
 *   1 : impossible operation: nothing has been done. Attempting to load a
 *   previously loaded table or a read/write table is impossible.
 *
 *   2 : error: the HashTable has been freed and must not be used.
 */
int dht_load_to_memory(DiskHashTable*, char**);

/* SDT: Changed dht_lookup to return boolean. */
/** Lookup a value by key
 *
 * If the hash table was opened in read-write mode, then the memory returned
 * can be written to (the hash table itself does not inspect the values in any
 * way). Writing to a read-only hashtable will probably trigger a segmentation
 * fault.
 *
 * If the object is not found, returns false.
 *
 * Thread safety: multiple concurrent reads are perfectly safe. No guarantees
 * are given whenever writing is performed.
 */
bool dht_lookup(const DiskHashTable*, const char* key);

/* SDT: Changed dht_insert to remove the "data" parameter. */
/** Insert a value.
 *
 * The hashtable must be opened in read write mode.
 *
 * If a value with the given key is already present in the table, then no
 * action is performed and 0 is returned.
 *
 * This operation is typically O(1) amortized. However, if table is at capacity
 * when dht_insert is called, then it must be grown which can be a
 * time-consuming operation as all the values are copied to the newly allocated
 * memory block (see dht_reserve).
 *
 * Errors can occur if table expansion is needed and memory cannot be
 * allocated.
 *
 * Returns 1 if the value was inserted.
 *         0 if the key was already present in the table. The hash table was
 *         not modified.
 *         -EACCES : attempted to insert into a read-only table.
 *         -ENOMEM : dht_reserve failed.
 *
 * The last argument is an error output argument. If it is set to a non-NULL
 * value, then the memory must be released with free(). Passing NULL is valid
 * (and no error message will be produced). An error return with *err == NULL
 * will mean an out-of-memory error (when dht fails to allocate memory, it does
 * not try to allocate memory for an error message).
 */
int dht_insert(DiskHashTable*, const char* key, char** err);

/** Preallocate memory for the table.
 *
 * Calling this function if the number of elements is known apriori can improve
 * performance. Additionally, if capacity exists, then dht_insert never fails.
 *
 * This function returns the actual capacity allocated (which may be more than
 * requested, but never less). Calling dht_reserve asking for _less_ capacity
 * than is currently used is a no-op.
 *
 * If capacity cannot be allocated, this function returns 0 (but no changes to
 * the hash table are made).
 *
 * This function can be used to query the current capacity by passing the value
 * 1 as the desired capacity.
 *
 * The last argument is an error output argument. If it is set to a non-NULL
 * value, then the memory must be released with free(). Passing NULL is valid
 * (and no error message will be produced).
 *
 * Attempting to call this function on a read-only table will fail (return
 * value: -EACCES).
 */
size_t dht_reserve(DiskHashTable*, size_t capacity, char** err);

/**
 * Return the number of elements
 */
size_t dht_size(const DiskHashTable*);

/** Free the hashtable and sync to disk.
 */
void dht_free(DiskHashTable*);

/* SDT: removed show_ht */


#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* DISKHASH_H_INCLUDE_GUARD__*/
