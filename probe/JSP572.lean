/-
# JSP-000572 probe

Problem (catalog `problems/catalog-0501-0600.md#JSP-000572`, Frankl 1977):

  Must every sufficiently large uniform set family contain two members
  intersecting in exactly one element?

Answer (Frankl 1977): yes — for `k`-uniform families on an `n`-element ground
set with more than about `n ^ (k - 2)` members, two members must meet in
exactly one element.

This file formalizes the *lower-bound side* of that threshold, i.e. the
explicit extremal construction showing that "sufficiently large" cannot be
weakened: for every `k ≥ 4` and every ground set containing a `(k-2)`-set `T`
and a disjoint set `U`, the family

  `F = { T ∪ {a, b} : {a, b} ⊆ U }`

is `k`-uniform, has `Nat.choose #U 2` members (so it grows like `n ^ 2 / 2`,
which for `k = 4` is the same order as Frankl's threshold `n ^ (k - 2)`), and
**no two of its members meet in exactly one element** (any two members both
contain `T`, which has `k - 2 ≥ 2` elements).

Frankl's positive direction (that more than `n ^ (k - 2)` members force a
singleton intersection) is not formalized here.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open Finset

namespace JSP572

variable {α : Type} [DecidableEq α]

/-- The extremal construction: all `k`-sets of the form `T ∪ {a, b}` with
`{a, b} ⊆ U`. -/
def family (T U : Finset α) : Finset (Finset α) :=
  U.powersetCard 2 |>.image (fun P => T ∪ P)

lemma mem_family {T U : Finset α} {A : Finset α} :
    A ∈ family T U ↔ ∃ P ∈ U.powersetCard 2, T ∪ P = A := by
  simp [family]

/-- **JSP-000572, lower-bound construction.**  For `k ≥ 4`, if the ground set
splits into a `(k-2)`-set `T` and a disjoint set `U` with at least two
elements, then the family of all `T ∪ {a, b}` is `k`-uniform, has
`Nat.choose #U 2` members, and no two of its members meet in exactly one
element. -/
theorem construction (T U : Finset α) (k : ℕ)
    (hk : 4 ≤ k) (hT : T.card = k - 2) (hdisj : Disjoint T U) :
    (∀ A ∈ family T U, A.card = k) ∧
      (∀ A ∈ family T U, ∀ B ∈ family T U, A ≠ B → (A ∩ B).card ≠ 1) ∧
      (family T U).card = Nat.choose U.card 2 := by
  have hinj : ∀ P ∈ U.powersetCard 2, ∀ Q ∈ U.powersetCard 2, T ∪ P = T ∪ Q → P = Q := by
    intro P hP Q hQ h
    have hPsub : P ⊆ U := (mem_powersetCard.mp hP).1
    have hQsub : Q ⊆ U := (mem_powersetCard.mp hQ).1
    have hPd : Disjoint T P := hdisj.mono_right hPsub
    have hQd : Disjoint T Q := hdisj.mono_right hQsub
    have := congrArg (fun X => X \ T) h
    rwa [union_sdiff_cancel_left hPd, union_sdiff_cancel_left hQd] at this
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨P, hP, rfl⟩ := mem_family.mp hA
    have hP2 : P.card = 2 := (mem_powersetCard.mp hP).2
    have hPsub : P ⊆ U := (mem_powersetCard.mp hP).1
    have hPd : Disjoint T P := hdisj.mono_right hPsub
    rw [card_union_of_disjoint hPd, hT, hP2]
    omega
  · intro A hA B hB hne
    obtain ⟨P, hP, rfl⟩ := mem_family.mp hA
    obtain ⟨Q, hQ, rfl⟩ := mem_family.mp hB
    have hTsub : T ⊆ (T ∪ P) ∩ (T ∪ Q) := by
      intro x hx
      exact mem_inter.mpr ⟨mem_union_left _ hx, mem_union_left _ hx⟩
    have hge : (k - 2) ≤ ((T ∪ P) ∩ (T ∪ Q)).card := by
      rw [← hT]
      exact card_le_card hTsub
    have hne1 : ((T ∪ P) ∩ (T ∪ Q)).card ≠ 1 := by omega
    exact hne1
  · have h := card_bij (s := U.powersetCard 2) (t := family T U)
        (fun P _ => T ∪ P)
        (fun P hP => mem_family.mpr ⟨P, hP, rfl⟩)
        (fun P hP Q hQ h => hinj P hP Q hQ h)
        (fun A hA => by obtain ⟨P, hP, rfl⟩ := mem_family.mp hA; exact ⟨P, hP, rfl⟩)
    rw [card_powersetCard] at h
    exact h.symm

end JSP572
