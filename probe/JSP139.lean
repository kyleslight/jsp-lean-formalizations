/-
# JSP-000139 probe

Problem (catalog `problems/catalog-0101-0200.md#JSP-000139`, Erdős 1997):

  How large must the maximum degree of a triangle-free graph of diameter at most
  two be?

Answer: at least `sqrt (n - 1)`, i.e. `n <= Delta ^ 2 + 1`; this is the
diameter-two Moore bound and it is attained (the 5-cycle at `Delta = 2`,
`n = 5`; the Petersen graph at `Delta = 3`, `n = 10`).

This file proves BOTH halves:

* `card_le_sq_add_one` — for every finite simple graph (symmetric, irreflexive
  relation) of diameter at most two whose degrees are all at most `d`, the
  vertex count is at most `d ^ 2 + 1`.  The counting argument does not use
  triangle-freeness; the hypothesis is nevertheless carried in the statement
  because the problem is about triangle-free graphs, and it is what makes the
  bound *attainable* (see the sharpness section).

* the sharpness section exhibits the 5-cycle (`d = 2`, `n = 5`) and the
  Petersen graph as `Kneser(5,2)` (`d = 3`, `n = 10`), both triangle-free of
  diameter two, with `n = d ^ 2 + 1`.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Finset

namespace JSP139

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Neighbourhood of `v` in the relation `r`. -/
def Nbr (r : α → α → Prop) [DecidableRel r] (v : α) : Finset α :=
  univ.filter (fun u => r v u)

/-- A relation is triangle-free when no three vertices are pairwise related. -/
def TriangleFree (r : α → α → Prop) : Prop :=
  ∀ a b c, r a b → r b c → ¬ r a c

/-- **Diameter at most two**: distinct vertices are adjacent, or joined by a
two-step path. -/
def DiameterLeTwo (r : α → α → Prop) : Prop :=
  ∀ a b, a ≠ b → r a b ∨ ∃ c, r a c ∧ r c b

/-- **JSP-000139, Moore bound**: a finite simple graph of diameter at most two
with maximum degree at most `d` has at most `d ^ 2 + 1` vertices. -/
theorem card_le_sq_add_one (r : α → α → Prop) [DecidableRel r] (d : ℕ)
    (hirr : ∀ a, ¬ r a a)
    (hsym : ∀ a b, r a b → r b a)
    (hdiam : DiameterLeTwo r)
    (hdeg : ∀ a, (Nbr r a).card ≤ d) :
    Fintype.card α ≤ d ^ 2 + 1 := by
  rcases isEmpty_or_nonempty α with hemp | hne
  · rw [Fintype.card_eq_zero]; exact Nat.zero_le _
  · obtain ⟨v⟩ := hne
    set N : Finset α := Nbr r v with hN
    set S : α → Finset α := fun u => (Nbr r u) \ (insert v N) with hS
    have hvN : v ∉ N := by simp [hN, Nbr, hirr v]
    -- every vertex is `v`, a neighbour of `v`, or two steps away from `v`
    have hcover : (univ : Finset α) ⊆ insert v N ∪ N.biUnion S := by
      intro w hw
      by_cases hwN : w ∈ insert v N
      · exact mem_union_left _ hwN
      · have hwv : w ≠ v := fun h => hwN (by simp [h])
        have hnr : ¬ r v w := fun h => hwN (by simp [hN, Nbr, h])
        rcases hdiam v w hwv.symm with h | ⟨c, hvc, hcw⟩
        · exact absurd h hnr
        · refine mem_union_right _ ?_
          exact mem_biUnion.mpr ⟨c, by simp [hN, Nbr, hvc], by simp [hS, Nbr, hcw, hwN]⟩
    -- each two-step set has at most `d - 1` elements
    have hScard : ∀ u ∈ N, (S u).card ≤ d - 1 := by
      intro u hu
      have hvu : r u v := hsym v u (by simpa [hN, Nbr] using hu)
      have hsub : S u ⊆ (Nbr r u).erase v := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := mem_sdiff.mp hx
        exact mem_erase.mpr ⟨fun h => hx2 (by simp [h]), hx1⟩
      calc (S u).card ≤ ((Nbr r u).erase v).card := card_le_card hsub
        _ = (Nbr r u).card - 1 := card_erase_of_mem (by simp [Nbr, hvu])
        _ ≤ d - 1 := Nat.sub_le_sub_right (hdeg u) 1
    have hNcard : N.card ≤ d := by simpa [hN] using hdeg v
    have hins : (insert v N).card = N.card + 1 := by
      rw [card_insert_of_notMem hvN]
    calc Fintype.card α = (univ : Finset α).card := rfl
      _ ≤ (insert v N ∪ N.biUnion S).card := card_le_card hcover
      _ ≤ (insert v N).card + (N.biUnion S).card := card_union_le _ _
      _ ≤ (N.card + 1) + N.card * (d - 1) := by
            rw [hins]
            gcongr
            exact card_biUnion_le_card_mul N S (d - 1) hScard
      _ = N.card * d + 1 := by
            by_cases hd0 : d = 0
            · subst hd0
              have h0 : N.card = 0 := by omega
              rw [h0]
            · have hdpos : 1 ≤ d := by omega
              have h1 : N.card * (d - 1) + N.card = N.card * d := by
                rw [← Nat.mul_succ]
                congr 1
                omega
              omega
      _ ≤ d * d + 1 := by
            have : N.card * d ≤ d * d := Nat.mul_le_mul_right d hNcard
            omega
      _ = d ^ 2 + 1 := by rw [pow_two]

/-- The triangle-free version, i.e. the statement of JSP-000139 proper. -/
theorem card_le_sq_add_one_triangleFree (r : α → α → Prop) [DecidableRel r] (d : ℕ)
    (hirr : ∀ a, ¬ r a a) (hsym : ∀ a b, r a b → r b a)
    (htri : TriangleFree r) (hdiam : DiameterLeTwo r)
    (hdeg : ∀ a, (Nbr r a).card ≤ d) :
    Fintype.card α ≤ d ^ 2 + 1 :=
  card_le_sq_add_one r d hirr hsym hdiam hdeg

/-! ## Sharpness: the bound `d ^ 2 + 1` is attained -/

/-- The 5-cycle. -/
def cyc5 : Fin 5 → Fin 5 → Prop := fun a b => b = a + 1 ∨ a = b + 1

instance : DecidableRel cyc5 := fun a b => inferInstanceAs (Decidable (b = a + 1 ∨ a = b + 1))

theorem cyc5_irr : ∀ a, ¬ cyc5 a a := by decide

theorem cyc5_sym : ∀ a b, cyc5 a b → cyc5 b a := by decide

theorem cyc5_diam : DiameterLeTwo cyc5 := by
  unfold DiameterLeTwo
  decide

theorem cyc5_tri : TriangleFree cyc5 := by
  unfold TriangleFree
  decide

theorem cyc5_deg : ∀ a, (Nbr cyc5 a).card ≤ 2 := by
  intro a
  revert a
  decide

/-- The 5-cycle attains the bound at `d = 2`: `n = 5 = 2 ^ 2 + 1`. -/
theorem sharp_d2 :
    Fintype.card (Fin 5) = 2 ^ 2 + 1 ∧ (∀ a, (Nbr cyc5 a).card ≤ 2) ∧
      TriangleFree cyc5 ∧ DiameterLeTwo cyc5 := by
  refine ⟨by norm_num, cyc5_deg, cyc5_tri, cyc5_diam⟩


/-- Vertices of the Petersen graph: the 2-element subsets of a 5-set. -/
def TwoSub : Type := {s : Finset (Fin 5) // s.card = 2}

instance : Fintype TwoSub := inferInstanceAs (Fintype {s : Finset (Fin 5) // s.card = 2})
instance : DecidableEq TwoSub := inferInstanceAs (DecidableEq {s : Finset (Fin 5) // s.card = 2})

/-- The Petersen graph as the Kneser graph `K(5,2)`: two pairs are adjacent
when they are disjoint. -/
def petersen : TwoSub → TwoSub → Prop := fun x y => Disjoint x.1 y.1

instance : DecidableRel petersen := fun x y => inferInstanceAs (Decidable (Disjoint x.1 y.1))

theorem petersen_card : Fintype.card TwoSub = 10 := by decide

theorem petersen_deg : ∀ x, (Nbr petersen x).card ≤ 3 := by
  intro x
  revert x
  decide

theorem petersen_tri : TriangleFree petersen := by
  unfold TriangleFree
  decide

theorem petersen_diam : DiameterLeTwo petersen := by
  unfold DiameterLeTwo
  decide

/-- The Petersen graph attains the bound at `d = 3`: `n = 10 = 3 ^ 2 + 1`. -/
theorem sharp_d3 :
    Fintype.card TwoSub = 3 ^ 2 + 1 ∧ (∀ a, (Nbr petersen a).card ≤ 3) ∧
      TriangleFree petersen ∧ DiameterLeTwo petersen :=
  ⟨by rw [petersen_card]; norm_num, petersen_deg, petersen_tri, petersen_diam⟩

end JSP139
