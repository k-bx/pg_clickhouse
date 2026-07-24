-- Tests for SubPlan (unflattened subquery) pushdown.
--
-- These cover the planner residue that pull_up_sublinks CANNOT convert to
-- joins: correlated scalar subqueries, uncorrelated scalar subqueries in
-- WHERE/HAVING, IN-subqueries with GROUP BY/HAVING, and NOT IN. Each shape
-- pins the deparsed Remote SQL via EXPLAIN and then executes to validate the
-- results.
--
-- SubPlan pushdown is gated on ClickHouse 25.8+ (older analyzers reject the
-- correlated / NOT IN SQL we generate), so the whole test aborts on older
-- servers rather than carry version-specific expected output.
SET datestyle = 'ISO';

SELECT clickhouse_raw_query($$SELECT version()$$) AS ch_version \gset
SELECT (split_part(:'ch_version', '.', 1)::int,
        split_part(:'ch_version', '.', 2)::int) < (25, 8) AS no_ch258 \gset
\if :no_ch258
\echo 'SKIP: SubPlan pushdown requires ClickHouse 25.8 or higher'
\quit
\endif

CREATE SERVER subplan_svr FOREIGN DATA WRAPPER clickhouse_fdw
    OPTIONS(dbname 'subplan_test', driver 'binary');
CREATE USER MAPPING FOR CURRENT_USER SERVER subplan_svr;

SELECT clickhouse_raw_query('DROP DATABASE IF EXISTS subplan_test');
SELECT clickhouse_raw_query('CREATE DATABASE subplan_test');

SELECT clickhouse_raw_query('CREATE TABLE subplan_test.items
    (item_id Int32, grp Int32, price Decimal(15,2), qty Int32)
    ENGINE = MergeTree ORDER BY item_id');
SELECT clickhouse_raw_query('CREATE TABLE subplan_test.sales
    (sale_id Int32, item_id Int32, amount Decimal(15,2), region String)
    ENGINE = MergeTree ORDER BY sale_id');

SELECT clickhouse_raw_query($$
    INSERT INTO subplan_test.items VALUES
    (1, 1, 10.00, 5), (2, 1, 20.00, 3), (3, 1, 30.00, 8),
    (4, 2, 15.00, 2), (5, 2, 25.00, 7), (6, 3, 50.00, 1)
$$);
-- Sale 8 distinguishes correct correlation from inner-scope capture: under
-- correct per-item correlation its group (item 1) has avg 166.67 so the
-- 1.5x threshold is 250.00 and sale 8 (250.00) does NOT qualify; under a
-- capture bug the threshold collapses to the global 1.5*avg = 241.88 and
-- sale 8 WOULD qualify.
SELECT clickhouse_raw_query($$
    INSERT INTO subplan_test.sales VALUES
    (1, 1, 100.00, 'east'), (2, 1, 150.00, 'west'),
    (3, 2, 200.00, 'east'), (4, 3, 120.00, 'east'),
    (5, 4,  80.00, 'west'), (6, 5, 300.00, 'east'),
    (7, 5,  90.00, 'west'), (8, 1, 250.00, 'east')
$$);

CREATE SCHEMA subplan_test;
IMPORT FOREIGN SCHEMA subplan_test FROM SERVER subplan_svr INTO subplan_test;
SET SESSION search_path = subplan_test,public;

-- ============================================================
-- 1. Uncorrelated scalar subquery (TPC-H Q22 shape)
-- ============================================================
EXPLAIN (VERBOSE, COSTS OFF)
SELECT item_id, price FROM items
WHERE price > (SELECT avg(price) FROM items)
ORDER BY item_id;

SELECT item_id, price FROM items
WHERE price > (SELECT avg(price) FROM items)
ORDER BY item_id;

-- ============================================================
-- 2. Correlated scalar subquery (TPC-H Q2/Q17 shape)
-- ============================================================
EXPLAIN (VERBOSE, COSTS OFF)
SELECT s.sale_id, s.amount FROM sales s
WHERE s.amount > (SELECT 1.5 * avg(s2.amount) FROM sales s2
                  WHERE s2.item_id = s.item_id)
ORDER BY s.sale_id;

SELECT s.sale_id, s.amount FROM sales s
WHERE s.amount > (SELECT 1.5 * avg(s2.amount) FROM sales s2
                  WHERE s2.item_id = s.item_id)
ORDER BY s.sale_id;

-- ============================================================
-- 3. Correlated scalar against a joined outer (Q2's exact shape:
--    correlation reaches a DIFFERENT outer table than the compared column)
-- ============================================================
EXPLAIN (VERBOSE, COSTS OFF)
SELECT i.item_id, s.amount FROM items i, sales s
WHERE i.item_id = s.item_id
  AND s.amount = (SELECT max(s2.amount) FROM sales s2
                  WHERE s2.item_id = i.item_id)
ORDER BY i.item_id;

SELECT i.item_id, s.amount FROM items i, sales s
WHERE i.item_id = s.item_id
  AND s.amount = (SELECT max(s2.amount) FROM sales s2
                  WHERE s2.item_id = i.item_id)
ORDER BY i.item_id;

-- ============================================================
-- 4. IN subquery with GROUP BY + HAVING (TPC-H Q18 shape)
--    HAVING blocks semijoin conversion, so this stays a SubPlan.
-- ============================================================
EXPLAIN (VERBOSE, COSTS OFF)
SELECT item_id, grp FROM items
WHERE item_id IN (SELECT item_id FROM sales
                  GROUP BY item_id HAVING sum(amount) > 150.00)
ORDER BY item_id;

SELECT item_id, grp FROM items
WHERE item_id IN (SELECT item_id FROM sales
                  GROUP BY item_id HAVING sum(amount) > 150.00)
ORDER BY item_id;

-- ============================================================
-- 5. NOT IN (TPC-H Q16 shape) — arrives as NOT(ANY-SubPlan)
-- ============================================================
EXPLAIN (VERBOSE, COSTS OFF)
SELECT item_id FROM items
WHERE item_id NOT IN (SELECT item_id FROM sales WHERE region = 'east')
ORDER BY item_id;

SELECT item_id FROM items
WHERE item_id NOT IN (SELECT item_id FROM sales WHERE region = 'east')
ORDER BY item_id;

-- ============================================================
-- 6. Scalar subquery in HAVING (TPC-H Q11 shape)
-- ============================================================
EXPLAIN (VERBOSE, COSTS OFF)
SELECT grp, sum(price * qty) AS value FROM items
GROUP BY grp
HAVING sum(price * qty) > (SELECT sum(price * qty) * 0.2 FROM items)
ORDER BY value DESC;

SELECT grp, sum(price * qty) AS value FROM items
GROUP BY grp
HAVING sum(price * qty) > (SELECT sum(price * qty) * 0.2 FROM items)
ORDER BY value DESC;

-- ============================================================
-- 7. Negative case: nested SubPlan must NOT push down (stays local)
-- ============================================================
EXPLAIN (VERBOSE, COSTS OFF)
SELECT item_id FROM items
WHERE price > (SELECT avg(price) FROM items
               WHERE qty > (SELECT avg(qty) FROM items))
ORDER BY item_id;

SELECT item_id FROM items
WHERE price > (SELECT avg(price) FROM items
               WHERE qty > (SELECT avg(qty) FROM items))
ORDER BY item_id;

-- ============================================================
-- 8. Negative case: multi-row correlated scalar (no aggregate) must
--    NOT push down — zero-row semantics differ between PG and CH.
-- ============================================================
EXPLAIN (VERBOSE, COSTS OFF)
SELECT s.sale_id FROM sales s
WHERE s.amount = (SELECT s2.amount FROM sales s2
                  WHERE s2.sale_id = s.sale_id + 1)
ORDER BY s.sale_id;

-- ============================================================
-- 9. Identity: the plan-time version probe must connect as the user the
--    executor will scan as — the view owner, via the RTE's checkAsUser —
--    not the invoker. regress_subplan_nomap has NO user mapping of its
--    own, so resolving the invoker instead would fail the EXPLAIN with
--    "user mapping not found".
-- ============================================================
CREATE ROLE regress_subplan_nomap;
GRANT USAGE ON SCHEMA subplan_test TO regress_subplan_nomap;
CREATE VIEW sales_v AS SELECT * FROM sales;
GRANT SELECT ON sales_v TO regress_subplan_nomap;

SET ROLE regress_subplan_nomap;
EXPLAIN (VERBOSE, COSTS OFF)
SELECT v.sale_id, v.amount FROM sales_v v
WHERE v.amount > (SELECT 1.5 * avg(v2.amount) FROM sales_v v2
                  WHERE v2.item_id = v.item_id)
ORDER BY v.sale_id;

SELECT v.sale_id, v.amount FROM sales_v v
WHERE v.amount > (SELECT 1.5 * avg(v2.amount) FROM sales_v v2
                  WHERE v2.item_id = v.item_id)
ORDER BY v.sale_id;
RESET ROLE;

DROP VIEW sales_v;
DROP OWNED BY regress_subplan_nomap;
DROP ROLE regress_subplan_nomap;

-- Cleanup
SET SESSION search_path = public;
DROP SCHEMA subplan_test CASCADE;
DROP USER MAPPING FOR CURRENT_USER SERVER subplan_svr;
DROP SERVER subplan_svr CASCADE;
SELECT clickhouse_raw_query('DROP DATABASE subplan_test');
