/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#include "alloc.h"
#include "cache_db.h"
#include "error.h"
#include "util.h"

#include <sqlite3.h>

#include <stdio.h>
#include <stdlib.h>

struct CacheDb {
    // these pointers should always be non-NULL in a valid CacheDb object
    sqlite3 *db;
    sqlite3_stmt *query_stmt[NUM_HASH_TYPES];
    sqlite3_stmt *insert_stmt[NUM_HASH_TYPES];
};

static const char* TABLE_NAMES[] =
{
    "modules",
    "decls",
    "smt_queries"
};

static void create_table(sqlite3 *db, const char *table_name)
{
    // For now, we just want a one-column table containing the SHA256 hash.

    // Note: Constructing the SQL into a buffer should be fine here,
    // because table_name is hard-coded into the source (i.e. it
    // doesn't come from user input)

    char buf[1000];
    sprintf(buf,
            "CREATE TABLE IF NOT EXISTS %s ( hash BLOB PRIMARY KEY )",
            table_name);

    int rc = sqlite3_exec(db, buf, NULL, NULL, NULL);

    if (rc != SQLITE_OK) {
        fatal_error("sqlite3 CREATE TABLE query failed (babylon.cache file corrupt?)");
    }
}

struct CacheDb * open_cache_db(const char *prefix)
{
    char *filename = copy_string_2(prefix, "babylon.cache");

    struct CacheDb *db = alloc(sizeof(struct CacheDb));
    int rc = sqlite3_open(filename, &db->db);

    if (rc != SQLITE_OK) {
        fprintf(stderr, "Warning: failed to open '%s', disabling caching.\n", filename);
        fprintf(stderr, "(sqlite error message was: %s)\n", sqlite3_errmsg(db->db));
        sqlite3_close(db->db);
        free(filename);
        free(db);
        return NULL;
    }

    free(filename);

    // Make sure our tables exist.
    for (int i = 0; i < NUM_HASH_TYPES; ++i) {
        create_table(db->db, TABLE_NAMES[i]);
    }

    // Create prepared statements.
    // Table name can't be a parameter, so we create one prepared statement
    // for each table.
    char buf[1000];
    for (int i = 0; i < NUM_HASH_TYPES; ++i) {
        sprintf(buf,
                "SELECT 1 FROM %s WHERE hash = ?",
                TABLE_NAMES[i]);
        rc = sqlite3_prepare_v2(db->db, buf, -1, &db->query_stmt[i], NULL);
        if (rc != SQLITE_OK) {
            fatal_error("sqlite3_prepare_v2 failed");
        }

        // We must use ON CONFLICT DO NOTHING because we run jobs in parallel,
        // so we might start a second verification of the same "thing", before
        // realising that we already started a previous verification of it.
        sprintf(buf,
                "INSERT INTO %s (hash) VALUES (?) ON CONFLICT(hash) DO NOTHING",
                TABLE_NAMES[i]);
        rc = sqlite3_prepare_v2(db->db, buf, -1, &db->insert_stmt[i], NULL);
        if (rc != SQLITE_OK) {
            fatal_error("sqlite3_prepare_v2 failed");
        }
    }

    return db;
}

void close_cache_db(struct CacheDb *db)
{
    if (db != NULL) {
        for (int i = 0; i < NUM_HASH_TYPES; ++i) {
            sqlite3_finalize(db->insert_stmt[i]);
            sqlite3_finalize(db->query_stmt[i]);
        }
        sqlite3_close(db->db);
        free(db);
    }
}

static void fatal_sqlite_error(sqlite3 *db, int rc, const char *msg)
{
    switch (rc) {
    case SQLITE_BUSY:
        fprintf(stderr, "sqlite returned SQLITE_BUSY\n");
        break;

    case SQLITE_ERROR:
        fprintf(stderr, "sqlite returned SQLITE_ERROR\n");
        fprintf(stderr, "sqlite3_errmsg: %s\n", sqlite3_errmsg(db));
        break;

    case SQLITE_MISUSE:
        fprintf(stderr, "sqlite returned SQLITE_MISUSE\n");
        break;

    default:
        fprintf(stderr, "sqlite unknown result code %d\n", rc);
        break;
    }

    fatal_error(msg);
}

bool sha256_exists_in_db(struct CacheDb *db,
                         enum HashType hash_type,
                         const uint8_t hash[SHA256_HASH_LENGTH])
{
    if (!db) return false;

    int rc = sqlite3_bind_blob(db->query_stmt[hash_type], 1, hash, SHA256_HASH_LENGTH, SQLITE_TRANSIENT);
    if (rc != SQLITE_OK) {
        fatal_error("sha256_exists_in_db: sqlite3_bind_blob failed");
    }

    bool found;
    rc = sqlite3_step(db->query_stmt[hash_type]);
    if (rc == SQLITE_DONE) {
        found = false;
    } else if (rc == SQLITE_ROW) {
        found = true;
    } else {
        fatal_sqlite_error(db->db, rc, "sha256_exists_in_db: sqlite3_step failed");
    }

    rc = sqlite3_reset(db->query_stmt[hash_type]);
    if (rc != SQLITE_OK) {
        fatal_error("sha256_exists_in_db: sqlite3_reset failed");
    }

    return found;
}

void add_sha256_to_db(struct CacheDb *db,
                      enum HashType hash_type,
                      const uint8_t hash[SHA256_HASH_LENGTH])
{
    if (!db) return;

    int rc = sqlite3_bind_blob(db->insert_stmt[hash_type], 1, hash, SHA256_HASH_LENGTH, SQLITE_TRANSIENT);
    if (rc != SQLITE_OK) {
        fatal_sqlite_error(db->db, rc, "add_sha256_to_db: sqlite3_bind_blob failed");
    }

    rc = sqlite3_step(db->insert_stmt[hash_type]);
    if (rc != SQLITE_DONE) {
        fatal_sqlite_error(db->db, rc, "add_sha256_to_db: sqlite3_step failed");
    }

    rc = sqlite3_reset(db->insert_stmt[hash_type]);
    if (rc != SQLITE_OK) {
        fatal_sqlite_error(db->db, rc, "sha256_exists_in_db: sqlite3_reset failed");
    }
}
