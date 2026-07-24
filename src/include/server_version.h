/*
 * server_version.h
 *
 * The ClickHouse server version reported by an active connection. Kept in its
 * own dependency-free header so it can be shared between the low-level driver
 * state in internal.h (which pulls in no Postgres headers) and the FDW layer
 * in fdw.h, without coupling the two.
 */

#ifndef CLICKHOUSE_SERVER_VERSION_H
#define CLICKHOUSE_SERVER_VERSION_H

#include <stdbool.h>

typedef struct ch_server_version {
    int major;
    int minor;
    int patch;
} ch_server_version;

/* True if version v is at least major.minor. */
static inline bool
chfdw_version_ge(ch_server_version v, int major, int minor) {
    return v.major > major || (v.major == major && v.minor >= minor);
}

#endif /* CLICKHOUSE_SERVER_VERSION_H */
