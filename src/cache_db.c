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
    sqlite3_stmt *query_stmt;
    sqlite3_stmt *insert_stmt;
};

struct CacheDb * open_cache_db(const char *prefix)
{
    char *filename = copy_string_2(prefix, "babylon.cache");

    struct CacheDb *db = alloc(sizeof(struct CacheDb));
    int rc = sqlite3_open(filename, &db->db);

    free(filename);

    if (rc != SQLITE_OK) {
        fprintf(stderr, "Warning: failed to open '%s', disabling caching.\n", filename);
        fprintf(stderr, "(sqlite error message was: %s)\n", sqlite3_errmsg(db->db));
        sqlite3_close(db->db);
        free(db);
        return NULL;
    }

    // Make sure our table exists.
    // For now, we just want a one-column table containing the SHA256 key.
    const char *query =
        "CREATE TABLE IF NOT EXISTS smt_queries ( hash BLOB PRIMARY KEY )";
    rc = sqlite3_exec(db->db, query, NULL, NULL, NULL);
    if (rc != SQLITE_OK) {
        fatal_error("sqlite3 CREATE TABLE query failed (babylon.cache file corrupt?)");
    }

    // Create prepared statements.
    const char *query_sql = "SELECT 1 FROM smt_queries WHERE hash = ?";
    rc = sqlite3_prepare_v2(db->db, query_sql, -1, &db->query_stmt, NULL);
    if (rc != SQLITE_OK) {
        fatal_error("sqlite3_prepare_v2 failed");
    }

    const char *insert_sql = "INSERT INTO smt_queries (hash) VALUES (?)";
    rc = sqlite3_prepare_v2(db->db, insert_sql, -1, &db->insert_stmt, NULL);
    if (rc != SQLITE_OK) {
        fatal_error("sqlite3_prepare_v2 failed");
    }

    return db;
}

void close_cache_db(struct CacheDb *db)
{
    if (db != NULL) {
        sqlite3_finalize(db->insert_stmt);
        sqlite3_finalize(db->query_stmt);
        sqlite3_close(db->db);
    }
}

bool sha256_exists_in_db(struct CacheDb *db, const uint8_t hash[SHA256_HASH_LENGTH])
{
    if (!db) return false;

    int rc = sqlite3_bind_blob(db->query_stmt, 1, hash, SHA256_HASH_LENGTH, SQLITE_TRANSIENT);
    if (rc != SQLITE_OK) {
        fatal_error("sha256_exists_in_db: sqlite3_bind_blob failed");
    }

    bool found;
    rc = sqlite3_step(db->query_stmt);
    if (rc == SQLITE_DONE) {
        found = false;
    } else if (rc == SQLITE_ROW) {
        found = true;
    } else {
        fatal_error("sha256_exists_in_db: sqlite3_step failed");
    }

    rc = sqlite3_reset(db->query_stmt);
    if (rc != SQLITE_OK) {
        fatal_error("sha256_exists_in_db: sqlite3_reset failed");
    }

    return found;
}

void add_sha256_to_db(struct CacheDb *db, const uint8_t hash[SHA256_HASH_LENGTH])
{
    if (!db) return;

    int rc = sqlite3_bind_blob(db->insert_stmt, 1, hash, SHA256_HASH_LENGTH, SQLITE_TRANSIENT);
    if (rc != SQLITE_OK) {
        fatal_error("add_sha256_to_db: sqlite3_bind_blob failed");
    }

    rc = sqlite3_step(db->insert_stmt);
    if (rc != SQLITE_DONE) {
        fatal_error("add_sha256_to_db: sqlite3_step failed");
    }

    rc = sqlite3_reset(db->insert_stmt);
    if (rc != SQLITE_OK) {
        fatal_error("sha256_exists_in_db: sqlite3_reset failed");
    }
}
