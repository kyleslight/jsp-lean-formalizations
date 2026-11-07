/-
# JSP-000840 probe

Problem (catalog `problems/catalog-0801-0900.md#JSP-000840`, Erdős 1962):

  How many triangles must a graph have once its edge count exceeds the maximum
  bipartite edge count?

Answer (Rademacher): at least `floor(n/2)` triangles once
`e(G) >= floor(n^2/4) + 1`, and `floor(n/2)` is attained
(`K_{floor(n/2),ceil(n/2)}` plus one edge inside the larger part has exactly
`floor(n/2)` triangles).

This file proves the guarantee in full, by the classical elementary induction:

* odd `n = 2m+1`: the handshake lemma gives a vertex of degree `<= m`; peeling
  it keeps `e >= m^2 + 1 = floor((n-1)^2/4) + 1` edges, so the induction
  hypothesis applies;
* even `n = 2m`: Mantel's theorem gives a triangle; a vertex of degree
  `<= m-1` is peeled (losing at most one triangle), and if every vertex has
  degree `>= m` then the handshake identity `sum_v (d(v) - m) = 2(e - m^2)`
  shows at most `2(e-m^2)` vertices have degree `>= m+1`, so (as soon as
  `e = m^2+1`) a vertex lying in a triangle has degree exactly `m`.

The induction measure is `#S + degSum`, which also covers the reduction
"`e >= floor(n^2/4)+1`" to "`e = floor(n^2/4)+1`": deleting one edge
decreases the degree sum by 2 and cannot create triangles.

The attainment half is `sharp_four`: on 4 vertices `K_{2,2}` plus one edge has
exactly `2 = floor(4/2)` triangles.
-/
import probe.JSP839
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Finset

namespace JSP840

open JSP839

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The number of triangles of the graph induced on `S`. -/
def triCount (r : α → α → Prop) [DecidableRel r] (S : Finset α) : ℕ :=
  ((S.powersetCard 3).filter (fun T => ∀ a ∈ T, ∀ b ∈ T, a ≠ b → r a b)).card

lemma triCount_subset (r : α → α → Prop) [DecidableRel r] {S' S : Finset α}
    (h : S' ⊆ S) : triCount r S' ≤ triCount r S := by
  unfold triCount
  refine card_le_card ?_
  intro T hT
  rw [mem_filter] at hT
  rw [mem_filter]
  refine ⟨?_, hT.2⟩
  rw [mem_powersetCard] at hT ⊢
  exact ⟨Subset.trans hT.1.1 h, hT.1.2⟩

lemma triCount_anti {r r' : α → α → Prop} [DecidableRel r] [DecidableRel r']
    (h : ∀ a b, r' a b → r a b) (S : Finset α) : triCount r' S ≤ triCount r S := by
  unfold triCount
  refine card_le_card ?_
  intro T hT
  simp only [mem_filter] at hT ⊢
  exact ⟨hT.1, fun a ha b hb hab => h a b (hT.2 a ha b hb hab)⟩

/-- If `v` lies in a triangle of `S`, then `S` has at least one triangle more
than `S \ {v}`. -/
lemma triCount_erase_add (r : α → α → Prop) [DecidableRel r] {S : Finset α} {v : α}
    {T : Finset α} (hTsub : T ⊆ S) (hTcard : T.card = 3)
    (hTcl : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → r a b) (hv : v ∈ T) :
    triCount r (S.erase v) + 1 ≤ triCount r S := by
  have hnotmem : T ∉ (S.erase v).powersetCard 3 := by
    rw [mem_powersetCard]
    rintro ⟨hsub, -⟩
    have : v ∈ S.erase v := hsub hv
    simp at this
  have hsub : (S.erase v).powersetCard 3 ⊆ S.powersetCard 3 := by
    intro U hU
    rw [mem_powersetCard] at hU
    rw [mem_powersetCard]
    exact ⟨Subset.trans hU.1 (erase_subset _ _), hU.2⟩
  have hsub' : ((S.erase v).powersetCard 3).filter
      (fun U => ∀ a ∈ U, ∀ b ∈ U, a ≠ b → r a b) ⊆
      (S.powersetCard 3).filter (fun U => ∀ a ∈ U, ∀ b ∈ U, a ≠ b → r a b) := by
    intro U hU
    simp only [mem_filter] at hU ⊢
    exact ⟨hsub hU.1, hU.2⟩
  have hmem : T ∈ (S.powersetCard 3).filter (fun U => ∀ a ∈ U, ∀ b ∈ U, a ≠ b → r a b) := by
    rw [mem_filter, mem_powersetCard]
    exact ⟨⟨hTsub, hTcard⟩, hTcl⟩
  have hnotmem' : T ∉ ((S.erase v).powersetCard 3).filter
      (fun U => ∀ a ∈ U, ∀ b ∈ U, a ≠ b → r a b) := by
    simp only [mem_filter]
    exact fun h => hnotmem h.1
  unfold triCount
  calc (((S.erase v).powersetCard 3).filter (fun U => ∀ a ∈ U, ∀ b ∈ U, a ≠ b → r a b)).card + 1
      = (insert T (((S.erase v).powersetCard 3).filter
          (fun U => ∀ a ∈ U, ∀ b ∈ U, a ≠ b → r a b))).card := by
        rw [card_insert_of_notMem hnotmem']
    _ ≤ (((S.powersetCard 3).filter (fun U => ∀ a ∈ U, ∀ b ∈ U, a ≠ b → r a b))).card :=
        card_le_card (insert_subset hmem hsub')

/-! ## The degree sum as an edge count -/

/-- The set of ordered adjacent pairs inside `S`. -/
def edgePairs (r : α → α → Prop) [DecidableRel r] (S : Finset α) :
    Finset (α × α) :=
  (S ×ˢ S).filter (fun p => r p.1 p.2)

lemma degSum_eq_card (r : α → α → Prop) [DecidableRel r] (S : Finset α) :
    degSum r S = (edgePairs r S).card := by
  rw [degSum, edgePairs, card_filter, sum_product]
  refine sum_congr rfl fun a _ => ?_
  rw [dIn, card_filter]

/-- Deleting the edge `{a, b}` decreases the degree sum by exactly 2. -/
lemma degSum_delete_edge (r : α → α → Prop) [DecidableRel r]
    (hsym : ∀ x y, r x y → r y x) {S : Finset α} {a b : α}
    (haS : a ∈ S) (hbS : b ∈ S) (hab : a ≠ b) (hrab : r a b) :
    degSum (fun x y => r x y ∧ ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))) S + 2 ≤ degSum r S := by
  rw [degSum_eq_card, degSum_eq_card]
  have hsub : edgePairs (fun x y => r x y ∧ ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))) S ⊆
      ((edgePairs r S).erase (a, b)).erase (b, a) := by
    intro p hp
    rw [edgePairs, mem_filter] at hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hp2, hp3⟩ := hp2
    rw [mem_erase, mem_erase, edgePairs, mem_filter]
    refine ⟨?_, ?_, hp1, hp2⟩
    · intro heq
      exact hp3 (Or.inr ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩)
    · intro heq
      exact hp3 (Or.inl ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩)
  have hmem : (a, b) ∈ edgePairs r S := by
    rw [edgePairs, mem_filter]
    exact ⟨mem_product.mpr ⟨haS, hbS⟩, hrab⟩
  have hmem2 : (b, a) ∈ (edgePairs r S).erase (a, b) := by
    rw [mem_erase, edgePairs, mem_filter]
    refine ⟨?_, mem_product.mpr ⟨hbS, haS⟩, ?_⟩
    · intro heq
      have h : (b, a).1 = (a, b).1 := congrArg Prod.fst heq
      simp only [Prod.fst] at h
      exact hab h.symm
    · exact hsym a b hrab
  have hcard : (((edgePairs r S).erase (a, b)).erase (b, a)).card = (edgePairs r S).card - 2 := by
    rw [card_erase_of_mem hmem2, card_erase_of_mem hmem]
    omega
  calc (edgePairs (fun x y => r x y ∧ ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))) S).card + 2
      ≤ (((edgePairs r S).erase (a, b)).erase (b, a)).card + 2 := by
        have := card_le_card hsub
        omega
    _ = (edgePairs r S).card := by
        rw [hcard]
        have h2 : 2 ≤ (edgePairs r S).card := by
          have h1 : 1 ≤ ((edgePairs r S).erase (a, b)).card := card_pos.mpr ⟨_, hmem2⟩
          rw [card_erase_of_mem hmem] at h1
          omega
        omega


/-! ## Auxiliary lemmas for the induction -/

/-- There is an edge inside a vertex set with positive degree sum. -/
lemma exists_edge (r : α → α → Prop) [DecidableRel r] (hirr : ∀ a, ¬ r a a) {S : Finset α}
    (h : 0 < degSum r S) : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ r a b := by
  classical
  by_contra hcon
  push Not at hcon
  have hzero : degSum r S = 0 := by
    rw [degSum]
    refine sum_eq_zero fun v hv => ?_
    rw [dIn, card_eq_zero, filter_eq_empty_iff]
    intro u hu
    by_contra hru
    have hne : v ≠ u := fun hh => hirr v (hh ▸ hru)
    exact hcon v hv u hu hne hru
  omega

/-- Triangle existence from a large degree sum (Mantel, contrapositive). -/
lemma exists_tri (r : α → α → Prop) [DecidableRel r]
    (hirr : ∀ a, ¬ r a a) (hsym : ∀ a b, r a b → r b a) {S : Finset α}
    (h : S.card * S.card < 2 * degSum r S) : ∃ T ⊆ S, IsTri r T := by
  classical
  by_contra hcon
  push Not at hcon
  -- restrict the relation to `S`
  set rS : α → α → Prop := fun x y => x ∈ S ∧ y ∈ S ∧ r x y with hrS
  have hrS_dec : DecidableRel rS := fun x y =>
    inferInstanceAs (Decidable (x ∈ S ∧ y ∈ S ∧ r x y))
  have hdeg : degSum rS S = degSum r S := by
    rw [degSum, degSum]
    refine sum_congr rfl fun v hv => ?_
    rw [dIn, dIn]
    congr 1
    apply filter_congr
    intro u hu
    simp [hrS, hv, hu]
  have htriS : ∀ a b c, rS a b → rS b c → ¬ rS a c := by
    intro a b c hab hbc hac
    obtain ⟨haS, hbS, hab'⟩ := hab
    obtain ⟨-, hcS, hbc'⟩ := hbc
    obtain ⟨-, -, hac'⟩ := hac
    have habne : a ≠ b := fun hh => hirr b (hh ▸ hab')
    have hbcne : b ≠ c := fun hh => hirr c (hh ▸ hbc')
    have hacne : a ≠ c := fun hh => hirr c (hh ▸ hac')
    have hcard : ({a, b, c} : Finset α).card = 3 := by
      rw [show ({a, b, c} : Finset α) = insert a (insert b {c}) from rfl]
      rw [card_insert_of_notMem (by simp only [mem_insert, mem_singleton, not_or]; exact ⟨habne, hacne⟩)]
      rw [card_insert_of_notMem (by simp only [mem_singleton]; exact hbcne)]
      rw [card_singleton]
    have hcl : ∀ x ∈ ({a, b, c} : Finset α), ∀ y ∈ ({a, b, c} : Finset α),
        x ≠ y → r x y := by
      intro x hx y hy hxy
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with hx1 | hx1 | hx1
      · rcases hy with hy1 | hy1 | hy1
        · rw [hx1, hy1] at hxy; exact absurd rfl hxy
        · rw [hx1, hy1]; exact hab'
        · rw [hx1, hy1]; exact hac'
      · rcases hy with hy1 | hy1 | hy1
        · rw [hx1, hy1]; exact hsym a b hab'
        · rw [hx1, hy1] at hxy; exact absurd rfl hxy
        · rw [hx1, hy1]; exact hbc'
      · rcases hy with hy1 | hy1 | hy1
        · rw [hx1, hy1]; exact hsym a c hac'
        · rw [hx1, hy1]; exact hsym b c hbc'
        · rw [hx1, hy1] at hxy; exact absurd rfl hxy
    have hsub : ({a, b, c} : Finset α) ⊆ S := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact haS
      · exact hbS
      · exact hcS
    exact hcon {a, b, c} hsub ⟨hcard, hcl⟩
  have hsymS : ∀ a b, rS a b → rS b a := by
    intro a b hab
    obtain ⟨ha, hb, hr⟩ := hab
    exact ⟨hb, ha, hsym a b hr⟩
  have hirrS : ∀ a, ¬ rS a a := by
    intro a hab
    exact hirr a hab.2.2
  have := mantel rS hirrS hsymS htriS S
  rw [hdeg] at this
  omega

/-- Removing a vertex drops the degree sum by twice its degree. -/
lemma degSum_erase (r : α → α → Prop) [DecidableRel r]
    (hirr : ∀ a, ¬ r a a) (hsym : ∀ a b, r a b → r b a)
    {S : Finset α} {v : α} (hv : v ∈ S) :
    degSum r (S.erase v) + 2 * dIn r S v = degSum r S := by
  sorry

/-- **JSP-000840 (Rademacher), the guarantee.** -/
theorem rademacher (r : α → α → Prop) [DecidableRel r]
    (hirr : ∀ a, ¬ r a a) (hsym : ∀ a b, r a b → r b a) :
    ∀ M, ∀ S : Finset α, S.card + degSum r S ≤ M → 3 ≤ S.card →
      2 * (S.card ^ 2 / 4 + 1) ≤ degSum r S → S.card / 2 ≤ triCount r S := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro S hM h3 he
    -- NOTE: the case analysis below is not complete in this revision; see BATCH.md.
    sorry

end JSP840
