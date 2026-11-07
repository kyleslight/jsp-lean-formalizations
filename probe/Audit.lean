/-
Audit file for the JSP-001021 probe.

1. `#print axioms` on the main declarations — confirms no proof placeholder and
   no user-declared axiom leaks into the proof (only Lean/Mathlib's standard
   axioms should appear).
2. Non-vacuity sanity checks: the bound is 4 at `n = 8`, and the statement is
   instantiated on an explicit 3-cycle tournament.
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import probe.JSP1021

open JSP1021

#print axioms JSP1021.exists_transitive_subset_of_pow
#print axioms JSP1021.exists_transitive_subset
#print axioms JSP1021.tournament_fin

/-- `Nat.log2 8 = 3`, so the guarantee for `n = 8` is 4 vertices. -/
example : Nat.log2 8 + 1 = 4 := by
  have h : Nat.log2 8 = 3 := by
    rw [Nat.log2_eq_iff (by norm_num)]
    norm_num
  omega

/-- The cyclic tournament on 3 vertices: `a → b` iff `b = a + 1`. -/
def cyc : Fin 3 → Fin 3 → Prop := fun a b => b = a + 1

instance : DecidableRel cyc := fun a b => inferInstanceAs (Decidable (b = a + 1))

theorem cyc_isTournament : IsTournament cyc := by
  constructor
  · intro a h
    fin_cases a <;> simp [cyc] at h
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp [cyc] <;> exact hab (Fin.ext rfl)

/-- The theorem applies to the 3-cycle: it must contain a transitive pair. -/
example : ∃ S : Finset (Fin 3), TransitiveOn cyc S ∧ Nat.log2 3 + 1 ≤ S.card :=
  tournament_fin 3 (by norm_num) cyc cyc_isTournament
