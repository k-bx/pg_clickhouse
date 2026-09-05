-- Echo ZP2 cursor 12823417; upstream #300, #338 and #347 regressions.
SET timezone = 'UTC';
SET statement_timeout = '15s';
CREATE SERVER precision FOREIGN DATA WRAPPER clickhouse_fdw OPTIONS (driver 'binary');
CREATE USER MAPPING FOR CURRENT_USER SERVER precision;
SELECT clickhouse_raw_query('DROP DATABASE IF EXISTS precision_test');
SELECT clickhouse_raw_query('CREATE DATABASE precision_test');
SELECT clickhouse_raw_query('CREATE TABLE precision_test.messages
    (id Int64, ts Nullable(DateTime64(6, ''UTC'')), tz Nullable(DateTime64(6, ''UTC'')), stamp Nullable(String))
    ENGINE=MergeTree ORDER BY id');
CREATE FOREIGN TABLE precision_remote (id bigint, ts timestamp, tz timestamptz, stamp text)
    SERVER precision OPTIONS (database 'precision_test', table_name 'messages');
CREATE TABLE precision_local (LIKE precision_remote);
SELECT clickhouse_raw_query('CREATE TABLE precision_test.roundtrip AS precision_test.messages');
CREATE FOREIGN TABLE precision_roundtrip (id bigint, ts timestamp, tz timestamptz, stamp text)
    SERVER precision OPTIONS (database 'precision_test', table_name 'roundtrip');
INSERT INTO precision_local VALUES
    (12823414,'2026-09-05 09:07:58.999999','2026-09-05 09:07:58.999999+00','2026-09-05 09:07:58.999999'),
    (12823415,'2026-09-05 09:07:59.026667','2026-09-05 09:07:59.026667+00','2026-09-05 09:07:59.026667'),
    (12823416,'2026-09-05 09:07:59.026668','2026-09-05 09:07:59.026668+00','2026-09-05 09:07:59.026668'),
    (12823417,'2026-09-05 09:07:59.026668','2026-09-05 09:07:59.026668+00','2026-09-05 09:07:59.026668'),
    (12823418,'2026-09-05 09:07:59.026668','2026-09-05 09:07:59.026668+00','2026-09-05 09:07:59.026668'),
    (12823419,'2026-09-05 09:07:59.026669','2026-09-05 09:07:59.026669+00','2026-09-05 09:07:59.026669'),
    (12823420,'2026-09-05 09:08:00.000001','2026-09-05 09:08:00.000001+00','2026-09-05 09:08:00.000001'),
    (12823421,NULL,NULL,NULL);
INSERT INTO precision_remote SELECT * FROM precision_local;
DO $test$
DECLARE
    driver text;
    zone text;
    mode text;
    column_name text;
    pg_type text;
    boundary text;
    predicate text;
    query text;
    expected jsonb;
    actual jsonb;
    plan jsonb;
BEGIN
    FOREACH driver IN ARRAY ARRAY['binary','http'] LOOP
        EXECUTE format('ALTER SERVER precision OPTIONS (SET driver %L)', driver);
        FOREACH zone IN ARRAY ARRAY['UTC','Europe/Kyiv','America/New_York'] LOOP
            PERFORM set_config('TimeZone', zone, false);
            PERFORM clickhouse_raw_query('TRUNCATE TABLE precision_test.roundtrip');
            INSERT INTO precision_roundtrip SELECT * FROM precision_local;
            SELECT jsonb_agg(t) INTO expected FROM (SELECT * FROM precision_local ORDER BY id) t;
            SELECT jsonb_agg(t) INTO actual FROM (SELECT * FROM precision_roundtrip ORDER BY id) t;
            IF actual IS DISTINCT FROM expected THEN
                RAISE EXCEPTION '%/% timestamp roundtrip mismatch: % vs %',driver,zone,actual,expected;
            END IF;
            FOREACH column_name IN ARRAY ARRAY['ts','tz'] LOOP
                pg_type := CASE column_name WHEN 'ts' THEN 'timestamp' ELSE 'timestamptz' END;
                boundary := '2026-09-05 09:07:59.026668' || CASE column_name WHEN 'tz' THEN '+00' ELSE '' END;
                FOREACH predicate IN ARRAY ARRAY[
                    '%1$I > %2$L::%3$s OR (%1$I = %2$L::%3$s AND id > 12823417)',
                    '%1$I < %2$L::%3$s OR (%1$I = %2$L::%3$s AND id < 12823417)',
                    '%1$I >= %2$L::%3$s AND %1$I <= %2$L::%3$s',
                    '%1$I IS NULL',
                    'true'
                ] LOOP
                    query := format('SELECT id,%1$I FROM precision_remote WHERE ' || predicate || ' ORDER BY %1$I,id LIMIT 3', column_name,boundary,pg_type);
                    EXECUTE 'SELECT jsonb_agg(t) FROM (' || replace(query,'precision_remote','precision_local') || ') t' INTO expected;
                    EXECUTE 'SELECT jsonb_agg(t) FROM (' || query || ') t' INTO actual;
                    IF actual IS DISTINCT FROM expected THEN
                        RAISE EXCEPTION '%/% constant mismatch: % vs %, %',driver,zone,actual,expected,query;
                    END IF;
                    EXECUTE 'EXPLAIN (VERBOSE,COSTS OFF,FORMAT JSON) ' || query INTO plan;
                    IF plan #>> '{0,Plan,Node Type}' <> 'Foreign Scan' THEN
                        RAISE EXCEPTION 'precision query stayed local: %',plan;
                    END IF;
                    IF position('%2$L' IN predicate) > 0 AND position('.026668' IN plan::text) = 0 THEN
                        RAISE EXCEPTION 'remote SQL lost fractional boundary: %',plan;
                    END IF;
                END LOOP;
                FOREACH mode IN ARRAY ARRAY['force_custom_plan','force_generic_plan'] LOOP
                    PERFORM set_config('plan_cache_mode',mode,false);
                    FOREACH predicate IN ARRAY ARRAY[
                        '%1$I > $1 OR (%1$I = $1 AND id > $2)',
                        '%1$I < $1 OR (%1$I = $1 AND id < $2)',
                        '%1$I >= $1 AND %1$I <= $1',
                        '%1$I IS NOT DISTINCT FROM $1'
                    ] LOOP
                        query := format('SELECT id,%1$I FROM precision_remote WHERE ' || predicate || ' ORDER BY %1$I,id LIMIT 3',column_name);
                        EXECUTE format('PREPARE precision_query(%s,bigint) AS SELECT jsonb_agg(t) FROM (%s) t',pg_type,query);
                        FOREACH boundary IN ARRAY ARRAY[
                            '2026-09-05 09:07:59.026668' || CASE column_name WHEN 'tz' THEN '+00' ELSE '' END,
                            NULL
                        ] LOOP
                            EXECUTE format('EXECUTE precision_query(%L,12823417)',boundary) INTO actual;
                            EXECUTE 'SELECT jsonb_agg(t) FROM (' || replace(replace(replace(query,'precision_remote','precision_local'),'$1',quote_nullable(boundary) || '::' || pg_type),'$2','12823417') || ') t' INTO expected;
                            IF actual IS DISTINCT FROM expected THEN
                                RAISE EXCEPTION '%/%/% prepared mismatch: % vs %, %',driver,zone,mode,actual,expected,query;
                            END IF;
                        END LOOP;
                        DEALLOCATE precision_query;
                    END LOOP;
                END LOOP;
            END LOOP;
            FOREACH query IN ARRAY ARRAY[
                'SELECT id,stamp::timestamp FROM precision_remote ORDER BY id',
                'SELECT id,stamp::timestamptz FROM precision_remote ORDER BY id',
                'SELECT id,ts::timestamptz,tz::timestamp FROM precision_remote ORDER BY id',
                'SELECT id,to_timestamp(id::float8 / 1000000) FROM precision_remote ORDER BY id',
                'SELECT id,to_timestamp(1788599279.0 + (id-12823417)::float8 / 1000000) FROM precision_remote ORDER BY id',
                'SELECT id FROM precision_remote ORDER BY ts DESC,id DESC LIMIT 3',
                'SELECT id FROM precision_remote WHERE ts < ''2026-09-05 09:07:59.026668'' OR (ts = ''2026-09-05 09:07:59.026668'' AND id < 12823418) ORDER BY ts DESC,id DESC LIMIT 3',
                'SELECT id FROM precision_remote WHERE ts > ''2026-09-05 09:07:59.026668'' OR (ts = ''2026-09-05 09:07:59.026668'' AND id > 12823416) ORDER BY ts,id LIMIT 3'
            ] LOOP
                EXECUTE 'SELECT jsonb_agg(t) FROM (' || replace(query,'precision_remote','precision_local') || ') t' INTO expected;
                EXECUTE 'SELECT jsonb_agg(t) FROM (' || query || ') t' INTO actual;
                IF actual IS DISTINCT FROM expected THEN
                    RAISE EXCEPTION '%/% cast/page mismatch: % vs %, %',driver,zone,actual,expected,query;
                END IF;
            END LOOP;
        END LOOP;
    END LOOP;
END;
$test$;
RESET timezone;
RESET plan_cache_mode;
DROP TABLE precision_local;
DROP FOREIGN TABLE precision_remote, precision_roundtrip;
DROP SERVER precision CASCADE;
SELECT clickhouse_raw_query('DROP DATABASE precision_test');
RESET statement_timeout;
