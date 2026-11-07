/-
Scratch file: records which `Nat.log2` API names exist in the pinned Mathlib
(commit 5ed2965256430c3649e86755f9576b54eca72435, inputRev `v4.34.0`).

Checked during the probe with `import Mathlib`; the names that do *not* exist are
kept as comments so that this file itself still compiles under the narrow imports
used by the rest of the probe.
-/
import Mathlib.Data.Nat.Log

-- do not exist (verified with `#check` under `import Mathlib`):
-- Nat.log2_le_iff_le_pow
-- Nat.pow_log2_le_self
-- Nat.log2_le_iff
-- Nat.log2_lt_iff_lt_pow
-- Nat.lt_pow_iff_log2_lt
-- Nat.pow_log2

#check Nat.le_log2
#check Nat.log2_eq_iff

example (n : ℕ) (hn : n ≠ 0) : Nat.log2 n ≤ Nat.log2 n := le_rfl
