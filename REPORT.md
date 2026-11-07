# Probe report — JSP-001021 formalization

**Status:** the guarantee direction of JSP-001021 is formalized and machine-checked.
No `sorry`, no user `axiom`. The sharpness direction is **not** formalized (see §7).

Session: 2026-11-07, 10:51 → 11:53 local (UTC+8) — 2026-11-07T02:51Z → 2026-11-07T03:53Z.
Report generated 2026-11-07T03:52Z.

---

## 1. Input pinning

| Item | Value |
| --- | --- |
| Problem | `JSP-001021` — *How large a transitive subtournament must every tournament of prescribed order contain?* |
| Catalog file | `problems/catalog-1001-1022.md` (section `<a id="JSP-001021">`) |
| Source repo | `justin-sun-prize/awards`, local clone at `~/Desktop/shun/money/justin-sun-prize/awards` |
| Source repo SHA | `f8801a856529dce27e738c6b305e46d76e7c387c` (2026-11-03, "docs: restore infinitude requirement for JSP-000307 (#5530)") |
| Catalog status | `Solved`, `Lean proof | No`, `Eligible to claim | No` |
| Attribution in catalog | Erdős–Moser 1964; refs St59, ErMo64, RePa70, Sa94, Sa98b |

The catalog row was read verbatim from the pinned SHA; the statement formalized below
is the lower-bound (guarantee) half of the catalog question, which is what the cited
literature establishes as the answer.

## 2. What was formalized

Informal statement (Erdős–Moser / St59): every tournament on `n ≥ 1` vertices
contains a transitive subtournament on `⌊log₂ n⌋ + 1` vertices.

Formal statement (fully qualified, namespace `JSP1021`):

```
JSP1021.exists_transitive_subset :
  ∀ {α : Type} [Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r],
    IsTournament r → Nonempty α →
    ∃ S : Finset α, TransitiveOn r S ∧ Nat.log2 (Fintype.card α) + 1 ≤ S.card

JSP1021.tournament_fin :
  ∀ (n : ℕ), 1 ≤ n → ∀ (r : Fin n → Fin n → Prop) [DecidableRel r],
    IsTournament r →
    ∃ S : Finset (Fin n), TransitiveOn r S ∧ Nat.log2 n + 1 ≤ S.card
```

Supporting definitions (all in `JSP1021`):

- `IsTournament r := (∀ a, ¬ r a a) ∧ ∀ a b, a ≠ b → (r a b ↔ ¬ r b a)`
- `TransitiveOn r S := ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, r a b → r b c → r a c`
- `outNbrs r v`, `inNbrs r v` — out-/in-neighbourhood as a `Finset`.

Supporting lemmas (all proved, no placeholders):

| Lemma | Statement |
| --- | --- |
| `transitive_insert` | adding a vertex beating all of a transitive set keeps it transitive |
| `card_out_add_card_in` | `outdeg v + indeg v = N - 1` |
| `two_mul_sum_outNbrs` | `2 * Σ_v outdeg v = N * (N - 1)` |
| `exists_large_outdeg` | some `v` has `N - 1 ≤ 2 * outdeg v` |
| `exists_transitive_subset_of_pow` | `2 ^ (k - 1) ≤ N → ∃ S, TransitiveOn r S ∧ k ≤ S.card` (strong induction on `k`) |

**Note on Mathlib:** there is no tournament notion in the pinned Mathlib
(`grep -ril tournament Mathlib` → no hits), so the tournament structure is defined
locally as a relation. `Nat.log2` *does* exist and is used
(`Nat.le_log2`, `Nat.log2_eq_iff`); several plausible names do **not** exist
(`Nat.pow_log2_le_self`, `Nat.log2_le_iff_le_pow`, `Nat.log2_lt_iff_lt_pow`,
`Nat.pow_log2`, `Nat.log2_le_iff`) — recorded in `probe/Scratch.lean`.

## 3. Environment

| Item | Value |
| --- | --- |
| Toolchain | `leanprover/lean4:v4.34.0` (matches `lean-proof/lean-toolchain` in the source repo) |
| Mathlib | `leanprover-community/mathlib4`, `inputRev = v4.34.0`, resolved commit **`5ed2965256430c3649e86755f9576b54eca72435`** |
| Project | `Probe`, lib `Probe`, `defaultTargets = ["Probe"]` |
| Lean project SHA | none — the probe directory is a fresh `git init` with **no commits** (read-only session; nothing committed) |
| Machine | macOS, 16 GB RAM (swap pressure is the dominant cost, see §4) |

The pin follows the source repo's own `lean-proof/` config rather than a hardcoded
guess: `awards/lean-proof/lean-toolchain` = `leanprover/lean4:v4.34.0` and its
`lakefile.toml` requires mathlib at `rev = "v4.34.0"`.

## 4. Timing ledger — compile wait vs. human work

Measured with `time` on this machine. `lake env lean` fixed overhead measured at
**1.36 s** (`lake env true`), so it is not the bottleneck.

### 4.1 Baselines (empty file)

| Import set | real | user | sys |
| --- | --- | --- | --- |
| `import Mathlib` | **1 m 28.9 s** | 2.9 s | 11.4 s |
| narrow import set (11 lines, §5) | **7.9 s** | 1.1 s | 1.7 s |

CPU time is ~3 s in both cases; the 1 m 29 s of `import Mathlib` is memory pressure
(16 GB machine, swap already full), not computation.

### 4.2 Compiling `probe/JSP1021.lean` (235 lines)

| Phase | Import | real per run | runs | total |
| --- | --- | --- | --- | --- |
| first pass, `import Mathlib` | full | 1 m 42 s – 2 m 10 s | 5 | ≈ 9 m 30 s |
| after switching to narrow imports | narrow | 7.9 s – 10.8 s (cold) / 2.8 s (warm) | 5 | ≈ 40 s |

### 4.3 Full serial build (`LAKE_JOBS=1 lake build`, 4 modules)

**13.4 s** wall clock for a clean rebuild of all four probe modules
(`Build completed successfully (979 jobs)`; the earlier full-target run reported
`8928 jobs` because it also re-verified cached Mathlib targets). Serial execution was
enforced (`LAKE_JOBS=1`) so only one `lean` process ran at a time.

### 4.4 Session totals (compile wait only)

| Segment | Wall clock |
| --- | --- |
| `lake update mathlib` (flaky network, 6 retries before `MANIFEST_OK`) | ≈ 6 min |
| first full `lake build` (Mathlib from cache) | 1 m 47 s |
| file compiles, full-import era | ≈ 9 m 30 s |
| file compiles + builds, narrow-import era | ≈ 1 m 20 s |
| baselines measured for this report | ≈ 1 m 40 s |
| **total compile wait** | **≈ 19 min** |

Session length was ≈ 62 min, so **≈ 19 min (31 %) was waiting on the compiler** and
the remaining ≈ 43 min was reading the catalog, selecting the problem, designing the
proof, and writing the report. The 2-minute compiles of the full-import era were pure
import overhead: the file's own elaboration is ~0.3 s once the imports are narrowed.

## 5. Narrow import set used

`probe/JSP1021.lean` and `probe/Audit.lean` import exactly:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
```

What each contributes, established empirically by removing them one at a time:

| Import | Needed for |
| --- | --- |
| `...Group.Finset.Basic` | `∑` notation, `Finset.sum_comm`, `sum_add_distrib` |
| `...Group.Finset.Sigma` | `Finset.sum_comm` (2-index version, `to_additive` of `prod_comm`) |
| `...Ring.Finset` | `Finset.mul_sum` |
| `...Group.Finset.Piecewise` | `Finset.card_filter` |
| `...Order.BigOperators.Group.Finset` | `Finset.sum_le_sum` |
| `Data.Fintype.Card` | `Fintype.card`, `Fintype.card_coe`, `Finset.card_univ` |
| `Data.Nat.Log` | `Nat.log2`, `Nat.le_log2`, `Nat.log2_eq_iff` |
| `Data.Finset.Card` | `Finset.card_insert_of_notMem`, `card_erase_of_mem`, `card_union_of_disjoint` |
| `Tactic.Linarith` | `omega` |
| `Tactic.Ring` | `ring` |
| `Tactic.NormNum` | `norm_num` |

`push_neg` / `push Not` is **not** in this set (it needs `Mathlib.Tactic.Push`), so the
one place that used it was rewritten by hand (`exists_large_outdeg`). `import Mathlib.Tactic`
(whole tactic bundle) costs 47 s and was avoided.

## 6. Verification evidence

`#print axioms` (from `probe/Audit.lean`, output verbatim):

```
'JSP1021.exists_transitive_subset_of_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP1021.exists_transitive_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP1021.tournament_fin' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only Lean's three standard axioms — no `sorryAx`, no user axiom.

Placeholder scan:

```
$ grep -c sorry probe/*.lean Probe.lean
probe/Audit.lean:0
probe/JSP1021.lean:0
probe/Scratch.lean:0
Probe.lean:0
$ grep -n "\baxiom\b" probe/*.lean Probe.lean
(none)
```

Non-vacuity checks in `probe/Audit.lean`:

- `Nat.log2 8 + 1 = 4` — the bound is 4 for `n = 8`.
- `cyc_isTournament : IsTournament cyc` for the explicit 3-cycle on `Fin 3`.
- `tournament_fin 3 _ cyc cyc_isTournament` — the main theorem applied to that
  concrete tournament, producing an actual transitive `Finset`.

Line counts:

```
     235 probe/JSP1021.lean
      45 probe/Audit.lean
      22 probe/Scratch.lean
       2 Probe.lean          (library root: imports the two probe modules)
      11 lakefile.toml
       1 lean-toolchain
```

## 7. Not formalized

- **Sharpness.** Reid–Parker (1970) showed the bound is attained — there are
  tournaments on `2 ^ (k-1)` vertices whose largest transitive subtournament has
  exactly `k` vertices. This is the upper-bound half of the catalog answer and is
  **not** formalized here; only the guarantee (lower bound) is.
- **`⌊log₂ n⌋` as a real-valued floor.** The formal statement uses `Nat.log2`,
  Mathlib's natural-number log base 2, which is the integer floor by construction.
- **The `n = 0` case.** The statement requires `Nonempty α`; `Nat.log2 0 = 0` would
  make the bound vacuous at `n = 0`, matching the "prescribed order `n ≥ 1`" reading.

## 8. Reproduction

```bash
cd <probe dir>                      # lean-formalizer-probe/
export PATH="$HOME/.elan/bin:$PATH"

# 1. resolve dependencies (mathlib pinned to v4.34.0)
lake update mathlib                 # flaky network: retried 6× before success
lake exe cache get                  # 8716 files already cached, rest decompressed

# 2. full Mathlib build (cached; 1 m 47 s)
LAKE_JOBS=1 lake build

# 3. check one file directly (≈8 s cold, ≈3 s warm)
lake env lean probe/JSP1021.lean

# 4. axiom audit + non-vacuity checks
lake env lean probe/Audit.lean
```

`LAKE_JOBS=1` matters on this machine: 5 parallel `lean` processes × ~1 GB each on a
16 GB box is what made the full-import compiles take 2 minutes.

## 9. Files

| Path | Role |
| --- | --- |
| `probe/JSP1021.lean` | the formalization (235 lines, 11 declarations) |
| `probe/Audit.lean` | `#print axioms`, non-vacuity checks |
| `probe/Scratch.lean` | record of which `Nat.log2` API names do/don't exist |
| `lakefile.toml` | pin: mathlib `v4.34.0`, lib `Probe`, globs `["Probe", "probe.+"]` |
| `Probe.lean` | library root, `import probe.JSP1021` + `import probe.Audit` — no file in the project imports full `Mathlib` any more |
| `lean-toolchain` | `leanprover/lean4:v4.34.0` |
