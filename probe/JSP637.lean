/-
# JSP-000637 probe

Problem (catalog `problems/catalog-0401-0500.md#JSP-000637`):

  How many edges can the containment graph of a set family have?

The containment graph of a family `F` of subsets of an `n`-element ground set
has vertex set `F` and an edge `{A, B}` whenever `A ⊊ B`.  Answer:
`3 ^ n - 2 ^ n`, attained by the full power set.

Why: an ordered pair `(A, B)` with `A ⊆ B` corresponds to a function
`x ↦ (0 if x ∈ A, 1 if x ∈ B \ A, 2 otherwise)`, so there are exactly
`3 ^ n` such pairs; `2 ^ n` of them have `A = B`; and for a strict pair
`A ⊊ B` exactly one of `(A,B)` and `(B,A)` qualifies, so the number of
*edges* is the number of strict ordered pairs, i.e. `3 ^ n - 2 ^ n`.

This file proves BOTH halves:

* `edges_le` — every family `F ⊆ 2 ^ n` has at most `3 ^ n - 2 ^ n` edges;
* `edges_powerset` — the full power set has exactly `3 ^ n - 2 ^ n` edges.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Finset

namespace JSP637

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Ordered pairs `(A, B)` of subsets of the ground set with `A ⊆ B`. -/
def subsetPairs : Finset (Finset α × Finset α) :=
  (univ.powerset ×ˢ univ.powerset).filter (fun p => p.1 ⊆ p.2)

/-- Ordered pairs `(A, B)` of subsets of the ground set with `A = B`. -/
def eqPairs : Finset (Finset α × Finset α) :=
  (univ.powerset ×ˢ univ.powerset).filter (fun p => p.1 = p.2)

/-- Ordered strict containment pairs of a family `F`: the edges of the
containment graph, counted once (since `⊊` is antisymmetric). -/
def strictPairs (F : Finset (Finset α)) : Finset (Finset α × Finset α) :=
  (F ×ˢ F).filter (fun p => p.1 ⊂ p.2)

/-- The type of ordered pairs of subsets with `A ⊆ B`. -/
def PairType (α : Type) [Fintype α] [DecidableEq α] : Type :=
  {p : Finset α × Finset α // p.1 ⊆ p.2}

lemma mem_subsetPairs {p : Finset α × Finset α} : p ∈ subsetPairs ↔ p.1 ⊆ p.2 := by
  simp [subsetPairs, mem_product, mem_powerset]

lemma mem_eqPairs {p : Finset α × Finset α} : p ∈ eqPairs ↔ p.1 = p.2 := by
  simp [eqPairs, mem_product, mem_powerset]

/-- The value attached to `x` by a pair `(A, B)` with `A ⊆ B`: `0` if `x ∈ A`,
`1` if `x ∈ B \ A`, `2` otherwise. -/
def pairVal (p : Finset α × Finset α) (x : α) : Fin 3 :=
  if x ∈ p.1 then 0 else if x ∈ p.2 then 1 else 2

lemma pairVal_eq_zero {p : Finset α × Finset α} (h : p.1 ⊆ p.2) {x : α} :
    pairVal p x = 0 ↔ x ∈ p.1 := by
  unfold pairVal
  by_cases h1 : x ∈ p.1
  · rw [if_pos h1]
    exact ⟨fun _ => h1, fun _ => rfl⟩
  · by_cases h2 : x ∈ p.2
    · rw [if_neg h1, if_pos h2]
      exact ⟨fun hh => absurd hh (by decide), fun hh => absurd hh h1⟩
    · rw [if_neg h1, if_neg h2]
      exact ⟨fun hh => absurd hh (by decide), fun hh => absurd hh h1⟩

lemma pairVal_ne_two {p : Finset α × Finset α} (h : p.1 ⊆ p.2) {x : α} :
    pairVal p x ≠ 2 ↔ x ∈ p.2 := by
  unfold pairVal
  by_cases h2 : x ∈ p.2
  · by_cases h1 : x ∈ p.1
    · rw [if_pos h1]
      exact ⟨fun _ => h2, fun _ => by decide⟩
    · rw [if_neg h1, if_pos h2]
      exact ⟨fun _ => h2, fun _ => by decide⟩
  · by_cases h1 : x ∈ p.1
    · rw [if_pos h1]
      exact ⟨fun hh => absurd (h h1) h2, fun hh => absurd hh h2⟩
    · rw [if_neg h1, if_neg h2]
      exact ⟨fun hh => absurd rfl hh, fun hh => absurd hh h2⟩

/-- The bijection `(A, B) ↦ (x ↦ pairVal (A,B) x)` between pairs with
`A ⊆ B` and functions into a 3-element set. -/
def pairEquiv : PairType α ≃ (α → Fin 3) where
  toFun p := pairVal p.1
  invFun f :=
    ⟨(univ.filter (fun x => f x = 0), univ.filter (fun x => f x ≠ 2)), by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      rw [hx]
      decide⟩
  left_inv p := by
    obtain ⟨⟨A, B⟩, hAB⟩ := p
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · ext x
      simp only [mem_filter, mem_univ, true_and]
      exact pairVal_eq_zero hAB
    · ext x
      simp only [mem_filter, mem_univ, true_and]
      exact pairVal_ne_two hAB
  right_inv f := by
    funext x
    show (if x ∈ univ.filter (fun y => f y = 0) then (0 : Fin 3)
          else if x ∈ univ.filter (fun y => f y ≠ 2) then 1 else 2) = f x
    generalize hfx : f x = v
    fin_cases v <;> simp [hfx]

instance : Fintype (PairType α) := Fintype.ofEquiv (α → Fin 3) pairEquiv.symm

/-- There are exactly `3 ^ n` ordered pairs of subsets with `A ⊆ B`. -/
theorem card_subset_pairs : Fintype.card (PairType α) = 3 ^ Fintype.card α := by
  calc Fintype.card (PairType α) = Fintype.card (α → Fin 3) := Fintype.card_congr pairEquiv
    _ = 3 ^ Fintype.card α := by simp

lemma subsetPairs_card_coe :
    Fintype.card ↥(subsetPairs (α := α)) = Fintype.card (PairType α) :=
  Fintype.card_congr
    { toFun := fun x => ⟨x.1, mem_subsetPairs.mp x.2⟩
      invFun := fun y => ⟨y.1, mem_subsetPairs.mpr y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- `subsetPairs` has `3 ^ n` elements. -/
theorem card_subsetPairs : (subsetPairs (α := α)).card = 3 ^ Fintype.card α := by
  rw [← Fintype.card_coe, subsetPairs_card_coe, card_subset_pairs]

/-- `eqPairs` has `2 ^ n` elements. -/
theorem card_eqPairs : (eqPairs (α := α)).card = 2 ^ Fintype.card α := by
  have himg : (eqPairs (α := α)) = (univ : Finset α).powerset.image (fun A => (A, A)) := by
    ext p
    obtain ⟨A, B⟩ := p
    constructor
    · intro hp
      have h : A = B := mem_eqPairs.mp hp
      exact mem_image.mpr ⟨A, mem_univ _, by rw [h]⟩
    · intro hmem
      obtain ⟨C, hC, hCB⟩ := mem_image.mp hmem
      simp only [Prod.mk.injEq] at hCB
      exact mem_eqPairs.mpr (by rw [← hCB.1, ← hCB.2])
  rw [himg, card_image_of_injective _ (fun A B h => congrArg Prod.fst h), card_powerset,
    card_univ]

lemma eqPairs_subset : (eqPairs (α := α)) ⊆ (subsetPairs (α := α)) := by
  intro p hp
  exact mem_subsetPairs.mpr (le_of_eq (mem_eqPairs.mp hp))

lemma mem_strictPairs {F : Finset (Finset α)} {p : Finset α × Finset α} :
    p ∈ strictPairs F ↔ p.1 ∈ F ∧ p.2 ∈ F ∧ p.1 ⊂ p.2 := by
  simp only [strictPairs, mem_filter, mem_product]
  tauto

/-- The strict containment pairs of the full power set. -/
theorem strictPairs_powerset_eq :
    strictPairs (univ : Finset (Finset α)) = (subsetPairs (α := α)) \ (eqPairs (α := α)) := by
  ext p
  rw [mem_strictPairs, mem_sdiff, mem_subsetPairs, mem_eqPairs]
  constructor
  · rintro ⟨-, -, hlt⟩
    exact ⟨(Finset.ssubset_iff_subset_ne.mp hlt).1, (Finset.ssubset_iff_subset_ne.mp hlt).2⟩
  · rintro ⟨hsub, hne⟩
    exact ⟨mem_univ _, mem_univ _, Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩⟩

/-- **JSP-000637, upper bound**: every family of subsets of an `n`-element set
has at most `3 ^ n - 2 ^ n` containment edges. -/
theorem edges_le (F : Finset (Finset α)) (hF : F ⊆ univ.powerset) :
    (strictPairs F).card ≤ 3 ^ Fintype.card α - 2 ^ Fintype.card α := by
  have hsub : strictPairs F ⊆ strictPairs (univ : Finset (Finset α)) := by
    intro p hp
    obtain ⟨h1, h2, hlt⟩ := mem_strictPairs.mp hp
    exact mem_strictPairs.mpr ⟨mem_univ _, mem_univ _, hlt⟩
  have hcard := card_le_card hsub
  rw [strictPairs_powerset_eq, card_sdiff_of_subset eqPairs_subset, card_subsetPairs, card_eqPairs] at hcard
  exact hcard

/-- **JSP-000637, attainment**: the full power set of an `n`-element set has
exactly `3 ^ n - 2 ^ n` containment edges. -/
theorem edges_powerset :
    (strictPairs (univ : Finset (Finset α))).card = 3 ^ Fintype.card α - 2 ^ Fintype.card α := by
  rw [strictPairs_powerset_eq, card_sdiff_of_subset eqPairs_subset, card_subsetPairs, card_eqPairs]

/-- The answer to JSP-000637, packaged. -/
theorem containment_answer (F : Finset (Finset α)) (hF : F ⊆ univ.powerset) :
    (strictPairs F).card ≤ 3 ^ Fintype.card α - 2 ^ Fintype.card α ∧
      ∃ G : Finset (Finset α), G ⊆ univ.powerset ∧
        (strictPairs G).card = 3 ^ Fintype.card α - 2 ^ Fintype.card α :=
  ⟨edges_le F hF, ⟨univ.powerset, subset_refl _, edges_powerset⟩⟩

end JSP637
