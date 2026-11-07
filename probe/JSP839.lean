/-
# JSP-000839 probe

Problem (catalog `problems/catalog-0801-0900.md#JSP-000839`):

  Just above the maximum bipartite edge count, how many edge-disjoint
  triangles are guaranteed?

Answer: exactly **one**.  Once `e(G) > floor(n^2/4)` (the maximum bipartite
edge count) the graph must contain a triangle (Mantel's theorem), but two
edge-disjoint triangles cannot be guaranteed: in `K_{2,2}` plus one extra
edge, every triangle uses the extra edge, so the maximum number of
edge-disjoint triangles is 1.  (The same holds for
`K_{floor(n/2),ceil(n/2)}` plus one extra edge for every `n`; the `n = 4`
instance is checked here.)

This file proves BOTH halves:

* `exists_triangle` — Mantel's theorem in the contrapositive: a graph whose
  degree sum satisfies `2 * (n^2 / 4 + 1) <= degSum` (i.e. more than
  `floor(n^2/4)` edges) contains a triangle;
* `sharp_four` — the 4-vertex example has exactly two triangles and any two
  distinct triangles share an edge, so at most one edge-disjoint triangle
  exists.

Mantel's theorem is proved in full here: for a triangle-free graph,
`2 * degSum <= n^2`, via the double count `sum_v d(v)^2 <= e * n` and
Cauchy–Schwarz (applied over `ℤ`).
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

open Finset

namespace JSP839

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Degree of `v` inside `S`. -/
@[reducible] def dIn (r : α → α → Prop) [DecidableRel r] (S : Finset α) (v : α) : ℕ :=
  (S.filter (fun u => r v u)).card

/-- Degree sum over `S`; this is twice the number of edges of the induced
graph on `S`. -/
def degSum (r : α → α → Prop) [DecidableRel r] (S : Finset α) : ℕ :=
  ∑ v ∈ S, dIn r S v

/-- `T` is a triangle in the graph: a 3-element clique. -/
@[reducible] def IsTri (r : α → α → Prop) (T : Finset α) : Prop :=
  T.card = 3 ∧ ∀ a ∈ T, ∀ b ∈ T, a ≠ b → r a b

lemma dIn_eq_sum (r : α → α → Prop) [DecidableRel r] (S : Finset α) (v : α) :
    dIn r S v = ∑ u ∈ S, (if r v u then 1 else 0) := by
  rw [dIn, card_eq_sum_ones, sum_filter]

/-- In a triangle-free graph two adjacent vertices have no common neighbour,
so their degree sum is at most the number of vertices. -/
lemma deg_add_le (r : α → α → Prop) [DecidableRel r]
    (htri : ∀ a b c, r a b → r b c → ¬ r a c)
    {S : Finset α} {u v : α} (hu : u ∈ S) (hv : v ∈ S) (huv : r u v) :
    dIn r S u + dIn r S v ≤ S.card := by
  have hdisj : Disjoint (S.filter (fun x => r u x)) (S.filter (fun x => r v x)) := by
    rw [disjoint_left]
    intro x hx1 hx2
    simp only [mem_filter] at hx1 hx2
    exact htri u v x huv hx2.2 hx1.2
  calc dIn r S u + dIn r S v
      = (S.filter (fun x => r u x)).card + (S.filter (fun x => r v x)).card := rfl
    _ = ((S.filter (fun x => r u x)) ∪ (S.filter (fun x => r v x))).card :=
        (card_union_of_disjoint hdisj).symm
    _ ≤ S.card := card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))

/-- **Double count**: `sum_v d(v)^2` is the sum of `d(v)` over the ordered
adjacent pairs, hence `2 * sum_v d(v)^2 <= degSum * n`. -/
lemma two_mul_sum_sq_le (r : α → α → Prop) [DecidableRel r]
    (hsym : ∀ a b, r a b → r b a)
    (htri : ∀ a b c, r a b → r b c → ¬ r a c) (S : Finset α) :
    2 * (∑ v ∈ S, dIn r S v * dIn r S v) ≤ degSum r S * S.card := by
  -- rewrite `d(v)^2` as a sum over neighbours
  have hsq : ∑ v ∈ S, dIn r S v * dIn r S v
      = ∑ v ∈ S, ∑ u ∈ S, dIn r S v * (if r v u then 1 else 0) := by
    refine sum_congr rfl fun v _ => ?_
    rw [dIn_eq_sum r S v, mul_sum]
  -- symmetry of the ordered-pair sum
  have hsymA : ∑ v ∈ S, ∑ u ∈ S, dIn r S v * (if r v u then 1 else 0)
      = ∑ v ∈ S, ∑ u ∈ S, dIn r S u * (if r v u then 1 else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun v _ => sum_congr rfl fun u _ => ?_
    by_cases h : r v u
    · rw [if_pos h, if_pos (hsym v u h)]
    · rw [if_neg h, if_neg fun hh => h (hsym u v hh)]
  have hpoint : ∀ v ∈ S, ∀ u ∈ S,
      (dIn r S v + dIn r S u) * (if r v u then 1 else 0)
        ≤ S.card * (if r v u then 1 else 0) := by
    intro v hv u hu
    by_cases h : r v u
    · rw [if_pos h, mul_one, mul_one]
      exact deg_add_le r htri hv hu h
    · rw [if_neg h, mul_zero, mul_zero]
  have hlast : ∑ v ∈ S, ∑ u ∈ S, S.card * (if r v u then 1 else 0)
      = S.card * ∑ v ∈ S, ∑ u ∈ S, (if r v u then 1 else 0) := by
    rw [mul_sum]
    exact sum_congr rfl fun v _ => (mul_sum S (fun u => if r v u then 1 else 0) S.card).symm
  have hsum : ∑ v ∈ S, ∑ u ∈ S, (if r v u then 1 else 0) = degSum r S := by
    rw [degSum]
    exact sum_congr rfl fun v _ => (dIn_eq_sum r S v).symm
  calc 2 * (∑ v ∈ S, dIn r S v * dIn r S v)
      = (∑ v ∈ S, ∑ u ∈ S, dIn r S v * (if r v u then 1 else 0))
        + ∑ v ∈ S, ∑ u ∈ S, dIn r S u * (if r v u then 1 else 0) := by
          rw [hsq, hsymA]; ring
    _ = ∑ v ∈ S, ∑ u ∈ S, (dIn r S v + dIn r S u) * (if r v u then 1 else 0) := by
          rw [← sum_add_distrib]
          refine sum_congr rfl fun v _ => ?_
          rw [← sum_add_distrib]
          refine sum_congr rfl fun u _ => by ring
    _ ≤ ∑ v ∈ S, ∑ u ∈ S, S.card * (if r v u then 1 else 0) :=
          sum_le_sum fun v hv => sum_le_sum fun u hu => hpoint v hv u hu
    _ = degSum r S * S.card := by
          rw [hlast, hsum, Nat.mul_comm]

/-- Cauchy–Schwarz over `ℤ`, transported back to `ℕ`. -/
lemma sum_sq_le (r : α → α → Prop) [DecidableRel r] (S : Finset α) :
    degSum r S * degSum r S ≤ S.card * (∑ v ∈ S, dIn r S v * dIn r S v) := by
  have hcs : ((degSum r S : ℤ)) ^ 2 ≤ (S.card : ℤ) *
      ((∑ v ∈ S, dIn r S v * dIn r S v : ℕ) : ℤ) := by
    have h := sum_mul_sq_le_sq_mul_sq (s := S) (fun v : α => (dIn r S v : ℤ))
      (fun _ : α => (1 : ℤ))
    simpa [degSum, pow_two, mul_comm] using h
  have : ((degSum r S * degSum r S : ℕ) : ℤ) ≤
      ((S.card * (∑ v ∈ S, dIn r S v * dIn r S v) : ℕ) : ℤ) := by
    push_cast
    simpa [pow_two] using hcs
  exact_mod_cast this

/-- **Mantel's theorem**: a triangle-free graph on `n` vertices has degree sum
at most `n^2 / 2`, i.e. at most `floor(n^2/4)` edges. -/
theorem mantel (r : α → α → Prop) [DecidableRel r]
    (hirr : ∀ a, ¬ r a a) (hsym : ∀ a b, r a b → r b a)
    (htri : ∀ a b c, r a b → r b c → ¬ r a c) (S : Finset α) :
    2 * degSum r S ≤ S.card * S.card := by
  have h1 := sum_sq_le r S
  have h2 := two_mul_sum_sq_le r hsym htri S
  rcases Nat.eq_zero_or_pos (degSum r S) with hD | hD
  · rw [hD]; simp
  · -- `2 * D^2 <= D * n^2`
    have hkey : 2 * degSum r S * degSum r S ≤ (S.card * S.card) * degSum r S := by
      calc 2 * degSum r S * degSum r S
          = 2 * (degSum r S * degSum r S) := by ring
        _ ≤ 2 * (S.card * (∑ v ∈ S, dIn r S v * dIn r S v)) := by
              exact Nat.mul_le_mul_left 2 h1
        _ = S.card * (2 * (∑ v ∈ S, dIn r S v * dIn r S v)) := by ring
        _ ≤ S.card * (degSum r S * S.card) := Nat.mul_le_mul_left _ h2
        _ = (S.card * S.card) * degSum r S := by ring
    have := Nat.le_of_mul_le_mul_right hkey hD
    calc 2 * degSum r S ≤ S.card * S.card := this

/-- **JSP-000839, guarantee**: more than `floor(n^2/4)` edges force a
triangle, hence at least one edge-disjoint triangle. -/
theorem exists_triangle (r : α → α → Prop) [DecidableRel r]
    (hirr : ∀ a, ¬ r a a) (hsym : ∀ a b, r a b → r b a)
    (h : 2 * (Fintype.card α ^ 2 / 4 + 1) ≤ degSum r univ) :
    ∃ T : Finset α, IsTri r T := by
  by_contra hcon
  push Not at hcon
  have htri : ∀ a b c, r a b → r b c → ¬ r a c := by
    intro a b c hab hbc hac
    have hab' : a ≠ b := fun hh => hirr b (hh ▸ hab)
    have hbc' : b ≠ c := fun hh => hirr c (hh ▸ hbc)
    have hac' : a ≠ c := fun hh => hirr c (hh ▸ hac)
    have hcard : ({a, b, c} : Finset α).card = 3 := by
      rw [show ({a, b, c} : Finset α) = insert a (insert b {c}) from rfl]
      rw [card_insert_of_notMem (by
        simp only [mem_insert, mem_singleton, not_or]
        exact ⟨hab', hac'⟩)]
      rw [card_insert_of_notMem (by simp only [mem_singleton]; exact hbc')]
      rw [card_singleton]
    have hclique : ∀ x ∈ ({a, b, c} : Finset α), ∀ y ∈ ({a, b, c} : Finset α),
        x ≠ y → r x y := by
      intro x hx y hy hxy
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with hx1 | hx1 | hx1
      · rcases hy with hy1 | hy1 | hy1
        · rw [hx1, hy1] at hxy; exact absurd rfl hxy
        · rw [hx1, hy1]; exact hab
        · rw [hx1, hy1]; exact hac
      · rcases hy with hy1 | hy1 | hy1
        · rw [hx1, hy1]; exact hsym a b hab
        · rw [hx1, hy1] at hxy; exact absurd rfl hxy
        · rw [hx1, hy1]; exact hbc
      · rcases hy with hy1 | hy1 | hy1
        · rw [hx1, hy1]; exact hsym a c hac
        · rw [hx1, hy1]; exact hsym b c hbc
        · rw [hx1, hy1] at hxy; exact absurd rfl hxy
    exact hcon {a, b, c} ⟨hcard, hclique⟩
  have h1 := mantel r hirr hsym htri univ
  have h2 : 4 * (Fintype.card α ^ 2 / 4 + 1) ≤ 2 * degSum r univ := by omega
  have h3 : 4 * (Fintype.card α ^ 2 / 4) + Fintype.card α ^ 2 % 4 = Fintype.card α ^ 2 :=
    Nat.div_add_mod (Fintype.card α ^ 2) 4
  have h4 : Fintype.card α ^ 2 % 4 ≤ 3 := by
    have := Nat.mod_lt (Fintype.card α ^ 2) (by norm_num : 0 < 4)
    omega
  have h5 : 2 * degSum r univ ≤ Fintype.card α * Fintype.card α := h1
  have h6 : 4 * (Fintype.card α ^ 2 / 4) + 4 ≤ 2 * degSum r univ := by
    calc 4 * (Fintype.card α ^ 2 / 4) + 4 = 4 * (Fintype.card α ^ 2 / 4 + 1) := by ring
      _ ≤ 2 * degSum r univ := h2
  have h5' : 2 * degSum r univ ≤ Fintype.card α ^ 2 := by
    rw [pow_two]; exact h5
  have h7 : 4 * (Fintype.card α ^ 2 / 4) + 4 ≤ Fintype.card α ^ 2 := le_trans h6 h5'
  omega

/-! ## Sharpness: the 4-vertex example has at most one edge-disjoint triangle -/

/-- `K_{2,2}` on `{0,1}` and `{2,3}` plus the edge `{0,1}`. -/
def ex : Fin 4 → Fin 4 → Prop := fun a b =>
  (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) ∨
  (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) ∨
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)

instance ex_dec : DecidableRel ex := fun a b => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

/-- The example has more than `floor(4^2/4)` edges, contains triangles, and
any two distinct triangles share an edge — so at most one edge-disjoint
triangle exists. -/
theorem sharp_four :
    2 * ((4 : ℕ) ^ 2 / 4 + 1) ≤ degSum ex univ ∧
      (∃ T : Finset (Fin 4), IsTri ex T) ∧
      (∀ T1 T2 : Finset (Fin 4), IsTri ex T1 → IsTri ex T2 → T1 ≠ T2 →
        (T1 ∩ T2).card = 2) := by
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · decide
  · decide
  · intro T1 T2 _ _ _
    revert T1 T2
    decide

/-- The answer to JSP-000839, packaged: at least one edge-disjoint triangle
is guaranteed, and one is the best possible. -/
theorem answer (r : α → α → Prop) [DecidableRel r]
    (hirr : ∀ a, ¬ r a a) (hsym : ∀ a b, r a b → r b a)
    (h : 2 * (Fintype.card α ^ 2 / 4 + 1) ≤ degSum r univ) :
    ∃ T : Finset α, IsTri r T :=
  exists_triangle r hirr hsym h

end JSP839
