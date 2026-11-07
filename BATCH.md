# BATCH — JSP formalization probe, batch 1

Project: `lean-formalizer-probe` (Lean 4, `leanprover/lean4:v4.34.0`, Mathlib pinned at
`v4.34.0` / commit `5ed2965256430c3649e86755f9576b54eca72435`).
All files are in `probe/`; every file is checked by `lake build` under `LAKE_JOBS=1`
(serial), with `#print axioms` audits in `probe/Audit*.lean`.

A from-scratch build of the ten problem files plus the audits: **17.2 s wall** (Mathlib
oleans prebuilt; the narrow-import discipline means no file imports `Mathlib`).
Per-file re-elaboration times are in the table below.

## The table

| # | JSP | area | lines | wall time (this session) | compile wait | `complete?` | commit (hash + timestamp) |
|---|-----|------|-------|--------------------------|--------------|-------------|---------------------------|
| 1 | JSP-001021 | graph theory / Ramsey | 297 | ~55 min | 11.1 s | **否** — guarantee ⌊log₂n⌋+1 proved for all n; sharpness proved only for 4 ≤ n ≤ 7 (Paley `P_7` restricted). The general-n extremal construction (Reid–Parker) is not formalized. | `fc14b91` 2026-11-07 14:41:15 |
| 2 | JSP-000139 | graph theory | 188 | ~40 min | 3.9 s | **是** — Δ² ≥ n−1 for every diameter-2 graph with max degree Δ; attained by C₅ (Δ=2) and the Petersen graph K(5,2) (Δ=3). | `f1f2ffa` 2026-11-07 14:33:04 |
| 3 | JSP-000637 | graph theory / combinatorics | 201 | ~55 min | 2.9 s | **是** — every family F ⊆ 2^[n] has ≤ 3ⁿ−2ⁿ containment edges; the full power set attains 3ⁿ−2ⁿ. | `f1f2ffa` 2026-11-07 14:33:04 |
| 4 | JSP-000854 | combinatorics | 130 | ~25 min | 2.2 s | **是** — a nonempty hypergraph on n ≥ 1 vertices has ≤ 2ⁿ−2 subsets meeting every edge and containing none in full; `{V}` attains it. | `73ffd70` 2026-11-07 14:47:43 |
| 5 | JSP-000572 | combinatorics | 93 | ~20 min | 2.2 s | **否** — only the lower-bound side: the explicit k-uniform family `{T ∪ {a,b}}` (|T| = k−2) has no two members meeting in exactly one element, size `C(#U,2)`. Frankl's positive direction (|F| > n^{k−2} forces a singleton intersection) is not formalized. | `38505b0` 2026-11-07 14:54:40 |
| 6 | JSP-000852 | graph theory / hypergraphs | 190 | ~35 min | 2.9 s | **否** — only the lower bound: every linear 3-uniform hypergraph has an independent set with `2n ≤ #I(#I+1)` (i.e. ≥ √(2n)). The matching random-STS upper bound O(√(n log n)) is not formalized. | `19496af` 2026-11-07 14:58:48 |
| 7 | JSP-000176 | graph theory | 188 | ~30 min | 2.5 s | **是（限定 prescribed degree = 2）** — a graph with no 2-regular subgraph (acyclic) has ≤ n−1 edges, attained by `P₄`. The degree-3 instance (Erdős–Sauer, JaSu23) is not treated. | `803a0d7` 2026-11-07 15:05:55 |
| 8 | JSP-000839 | graph theory | 254 | ~45 min | 2.7 s | **是** — more than ⌊n²/4⌋ edges force a triangle (Mantel, proved in full via the double count + Cauchy–Schwarz), and one edge-disjoint triangle is best possible (the 4-vertex `K_{2,2}`+edge example has exactly two triangles, sharing an edge). | `5d3262a` 2026-11-07 15:20:00 |
| 9 | JSP-000622 | graph theory / chromatic | 557 | ~40 min (n=5) + 95 min (general) | 5.7 s (file), 10.7 s (build + audit) | **是** — exact `z(n)` for `n = 1..7`: `1,1,2,2,3,3,3` (upper + witness, both directions), plus the general bound `z(n) ≤ ⌈n/2⌉` for every `n` and Ramsey `R(3,3)=6`. **The general formula is an open problem** — see note below. | `9a12b26` (n=5) / *(this commit)* (general) |
| 10 | JSP-000840 | graph theory | 274 | ~85 min | 2.4 s | **否** — `triCount` machinery, `exists_edge`, `exists_tri` (Mantel contrapositive), `degSum_delete_edge` (edge deletion drops the degree sum by 2) and `triCount_erase_add` are proved; the main induction `rademacher` and `degSum_erase` are still `sorry`. **Not submittable as is.** | `b002903` 2026-11-07 15:55:39 |

## Statement-fidelity record (per problem)

1. **JSP-001021** — tournament = irreflexive binary relation with exactly one direction on
   distinct vertices; transitive set = the relation restricted to it is transitive.
   Faithful. The guarantee is a *one-direction* statement about ⌊log₂n⌋+1; the sharpness
   is proved for n = 4..7 only (extra restriction, not extra hypothesis). Note recorded in
   the file: the exact extremal function is *not* ⌊log₂n⌋+1 for every n (e.g. every
   14-vertex tournament has a transitive 5-subtournament since TT(5) = 14), so "attained
   for some n" is the correct sense of "best possible".
2. **JSP-000139** — "triangle-free, diameter ≤ 2" is carried as hypotheses; the Moore
   bound proof does not use triangle-freeness (the bound holds for any diameter-2 graph),
   triangle-freeness is what makes it *attainable*. Both directions proved. Extra: the
   problem asks for a lower bound on Δ; the statement proved is n ≤ Δ²+1, equivalent.
3. **JSP-000637** — containment graph = family F ⊆ 2^[n] with an edge for A ⊊ B. Edges
   counted once (⊊ is antisymmetric, so the ordered strict pairs already equal the edge
   count — no division by 2). Both directions proved.
4. **JSP-000854** — extra hypothesis `[Nonempty α]` (n ≥ 1); for n = 0 the formula
   `2⁰−2 = 0` also holds but the degenerate case is not covered. Both directions proved.
5. **JSP-000572** — one direction only (the extremal construction), no extra hypotheses.
6. **JSP-000852** — one direction only (lower bound). "Linear" is stated as pairwise
   intersections of distinct edges having ≤ 1 element; 3-uniformity is a hypothesis.
7. **JSP-000176** — the problem's "prescribed degree" is instantiated at degree 2. The
   hypothesis is phrased as "every nonempty vertex subset spans a vertex of degree ≤ 1",
   which is *equivalent* to acyclicity / absence of a 2-regular subgraph (the equivalence
   itself is not formalized). Both directions for that instance.
8. **JSP-000839** — the answer formalized is "one edge-disjoint triangle"; the sharpness
   example is the n = 4 instance (`K_{2,2}` + edge), not the general
   `K_{⌊n/2⌋,⌈n/2⌉}` + edge. Both directions for that reading.
9. **JSP-000622** — the problem asks for `z(n)` = the worst-case cochromatic number over
   `n`-vertex graphs. **There is no closed formula**: Erdős Problem 758 (erdosproblems.com/758)
   records the exact values only for `1 ≤ n ≤ 19` — `1,1,2,2,3,3,3,3,4,4,4,4,5,5,5,6,6,6,6`
   (all easy from `R(3)=6`, `R(4)=18` except `z(12)=4`, which needed a computer search by
   Bhavik Mehta) — states that `z(20) ∈ {6,7}` is **unknown**, and that Gimbel [Gi86]
   proved `z(n) ≍ n/log n`. So "complete for general n" can only mean the exact small-order
   table plus general bounds; that is what is formalized: `z(n)` for `n = 1..7` (both
   directions) and `z(n) ≤ ⌈n/2⌉` for all `n`. The partition
   is encoded as a cover by k clique-or-independent sets (equivalent to a partition, noted
   in the file). Both directions for that order.
10. **JSP-000840** — the statement formalized is Rademacher's "≥ ⌊n/2⌋ triangles when
    `2(⌊n²/4⌋+1) ≤ degSum`"; the induction is incomplete (2 `sorry`).

### Note on the JSP-000622 counterexample that was suggested to me

The brief warned that `C₅ ∪ K₁` (6 vertices) has `z = 3 + 1 = 4`, so that `⌈n/2⌉` could not be
the answer. That is wrong: the cochromatic number is **not** additive over disjoint unions
(`z(G ∪ H) ≤ z(G) + z(H)`, and the inequality is usually strict, because a part may mix
vertices of different components — with no cross edges such a mixed part is automatically
independent). Indeed `C₅ ∪ K₁` is partitioned by `{1,3}, {2,4}, {5,x}` into 3 independent
sets, so `z(C₅ ∪ K₁) = 3`. The brute-force table (`probe/cochrom_bf.c`, exhaustive for
`n ≤ 7`) gives `z(n) = 1,1,2,2,3,3,3` for `n = 1..7`, matching erdosproblems.com/758.

## What Mathlib lacks (and what made these slow)

* No `SimpleGraph`-free toolkit: I used raw relations + `Finset`, so every "graph" lemma
  (degree sums, double counting, edge deletion, induced subgraphs) had to be built from
  scratch. `SimpleGraph` exists in Mathlib but its API (`edgeFinset`, `cliqueFinset`,
  `IsAcyclic`) is heavy to import and I did not want to pay the compile cost.
* `Finset.card_filter` in the "sum of indicators" direction does not exist under that
  name; `card_eq_sum_ones` + `sum_filter` is the workaround.
* There is no Nat-valued Cauchy–Schwarz (`sum_mul_sq_le_sq_mul_sq` is for
  `IsStrictOrderedRing`), so Mantel goes through `ℤ` and back with `exact_mod_cast`.
* Instance search does not unfold `def`s (`Decidable (Good H S)`, `Decidable (TransitiveOn r S)`
  etc. fail) unless the definition is `@[reducible]`; this bit me four times.
* `decide` on "for all 1024 five-vertex graphs there is a 3-colouring" exceeds the default
  heartbeat budget; the structural proof in JSP-000622 was cheaper than the enumeration.
* `Finset.exists_max_image` is fine, but there is no `Finset.exists_maximal` for the
  "maximal independent set" argument, so the maximum-cardinality set is used instead.

## Bottom line

**Of the 10 problems: 6 are complete** (JSP-000139, JSP-000637, JSP-000854, JSP-000176
[degree 2], JSP-000839, JSP-000622 [orders 1..7 exact + z(n) ≤ ⌈n/2⌉ for all n]), **3 are half-problems** (JSP-001021,
JSP-000572, JSP-000852 — one direction each), and **1 is unfinished** (JSP-000840, 2 `sorry`).

Nine of the ten files build with `grep -c sorry` = 0 and `#print axioms` = only
`[propext, Classical.choice, Quot.sound]`; JSP-000840 does not.
