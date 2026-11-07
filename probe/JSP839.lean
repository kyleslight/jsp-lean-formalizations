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
`K_{floor(n/2),ceil(n/2)}` plus one extra edge for every `n`, which is what
`answer_general` proves: for every `n >= 4` the example `exV n` on the
`n`-element vertex set `V n` has at least `floor(n^2/4) + 1` edges, contains a
triangle, and any two of its triangles share an edge — so one edge-disjoint
triangle is optimal at every order.  The `n = 4` instance is also kept as
`sharp_four`.)

This file proves BOTH halves:

* `exists_triangle` — Mantel's theorem in the contrapositive: a graph whose
  degree sum satisfies `2 * (n^2 / 4 + 1) <= degSum` (i.e. more than
  `floor(n^2/4)` edges) contains a triangle;
* `answer_general` — for every `n >= 4` an `n`-vertex graph with more than
  `floor(n^2/4)` edges in which any two distinct triangles share an edge
  (`sharp_four` is its `n = 4` instance).

Mantel's theorem is proved in full here: for a triangle-free graph,
`2 * degSum <= n^2`, via the double count `sum_v d(v)^2 <= e * n` and
Cauchy–Schwarz (applied over `ℤ`).
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum
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


/-! ## Sharpness for general `n`

The example: `K_{⌊n/2⌋,⌈n/2⌉}` plus the single edge inside the larger part.
Vertex set `V n = Fin (n/2) ⊕ Fin (n - n/2)`, so `Fintype.card (V n) = n`
(`card_V`); the left side is the `Sum.inl` half, the right side the `Sum.inr`
half, and the extra edge joins the right vertices numbered `0` and `1`. -/

/-- Vertex set of the sharp example: `⌊n/2⌋ + ⌈n/2⌉ = n` vertices. -/
@[reducible] def V (n : ℕ) : Type := Fin (n / 2) ⊕ Fin (n - n / 2)

/-- The sharp example: complete bipartite between the two sides, plus the
single edge between the right vertices numbered `0` and `1`. -/
@[reducible] def exV (n : ℕ) (a b : V n) : Prop :=
  match a, b with
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => True
  | Sum.inr i, Sum.inr j => i.val = 0 ∧ j.val = 1 ∨ i.val = 1 ∧ j.val = 0
  | Sum.inl _, Sum.inl _ => False

instance (n : ℕ) : DecidableRel (exV n) := fun a b =>
  match a, b with
  | Sum.inl _, Sum.inr _ => isTrue trivial
  | Sum.inr _, Sum.inl _ => isTrue trivial
  | Sum.inr i, Sum.inr j =>
      inferInstanceAs (Decidable (i.val = 0 ∧ j.val = 1 ∨ i.val = 1 ∧ j.val = 0))
  | Sum.inl _, Sum.inl _ => isFalse (by simp [exV])

/-- The left side as a `Finset`. -/
def Lset (n : ℕ) : Finset (V n) := (univ : Finset (Fin (n / 2))).image Sum.inl

/-- The right side as a `Finset`. -/
def Rset (n : ℕ) : Finset (V n) := (univ : Finset (Fin (n - n / 2))).image Sum.inr

lemma card_V (n : ℕ) : Fintype.card (V n) = n := by
  have h : Fintype.card (Fin (n / 2) ⊕ Fin (n - n / 2)) = n / 2 + (n - n / 2) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  have h2 : n / 2 + (n - n / 2) = n := by omega
  rw [h2] at h
  exact h

lemma mem_Lset {n : ℕ} {a : V n} : a ∈ Lset n ↔ ∃ i, a = Sum.inl i := by
  rw [Lset, mem_image]
  constructor
  · rintro ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, mem_univ i, rfl⟩

lemma mem_Rset {n : ℕ} {a : V n} : a ∈ Rset n ↔ ∃ j, a = Sum.inr j := by
  rw [Rset, mem_image]
  constructor
  · rintro ⟨j, _, rfl⟩; exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩; exact ⟨j, mem_univ j, rfl⟩

lemma card_Lset (n : ℕ) : (Lset n).card = n / 2 := by
  rw [Lset, card_image_of_injective _ Sum.inl_injective, card_univ, Fintype.card_fin]

lemma card_Rset (n : ℕ) : (Rset n).card = n - n / 2 := by
  rw [Rset, card_image_of_injective _ Sum.inr_injective, card_univ, Fintype.card_fin]

lemma disjoint_Lset_Rset (n : ℕ) : Disjoint (Lset n) (Rset n) := by
  rw [disjoint_left]
  intro a ha hb
  rw [mem_Lset] at ha
  rw [mem_Rset] at hb
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  rw [hi] at hj
  exact Sum.inl_ne_inr hj

lemma univ_eq_Lset_union_Rset (n : ℕ) : Lset n ∪ Rset n = (univ : Finset (V n)) := by
  ext a
  rw [mem_union, mem_Lset, mem_Rset]
  constructor
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩) <;> simp
  · intro _
    rcases a with i | j
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨j, rfl⟩

/-- The only edge inside a part is the extra one between right vertices `0`
and `1`. -/
lemma exV_inr_inr {n : ℕ} (i j : Fin (n - n / 2)) :
    exV n (Sum.inr i) (Sum.inr j) ↔ (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) :=
  Iff.rfl

lemma exV_inl_inl {n : ℕ} (i j : Fin (n / 2)) : ¬ exV n (Sum.inl i) (Sum.inl j) := by
  simp [exV]

lemma not_inr_iff_inl {n : ℕ} {a : V n} :
    (¬ ∃ j, a = Sum.inr j) ↔ ∃ i, a = Sum.inl i := by
  rcases a with i | j
  · constructor
    · intro _; exact ⟨i, rfl⟩
    · rintro ⟨i', hi⟩ hcon
      obtain ⟨j', hj⟩ := hcon
      exact Sum.inl_ne_inr hj
  · constructor
    · intro h; exact absurd ⟨j, rfl⟩ h
    · rintro ⟨i', hi⟩ hcon
      exact Sum.inr_ne_inl hi

/-- A left vertex is joined to every right vertex. -/
lemma le_deg_inl (n : ℕ) (i : Fin (n / 2)) :
    n - n / 2 ≤ dIn (exV n) univ (Sum.inl i) := by
  rw [dIn]
  refine le_trans (le_of_eq (card_Rset n).symm) (card_le_card ?_)
  intro b hb
  rw [mem_Rset] at hb
  obtain ⟨j, rfl⟩ := hb
  simp only [mem_filter, mem_univ, true_and]
  trivial

/-- A right vertex `j` is joined to every left vertex, and additionally to
`1` (resp. `0`) when `j` is `0` (resp. `1`). -/
lemma le_deg_inr (n : ℕ) (hn : 4 ≤ n) (j : Fin (n - n / 2)) :
    n / 2 + (if j.val = 0 ∨ j.val = 1 then 1 else 0) ≤ dIn (exV n) univ (Sum.inr j) := by
  have hm2 : 2 ≤ n - n / 2 := by omega
  obtain ⟨z0, hz0⟩ : ∃ z : Fin (n - n / 2), z.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨z1, hz1⟩ : ∃ z : Fin (n - n / 2), z.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hz1L : Sum.inr z1 ∉ Lset n := by
    rw [mem_Lset]
    rintro ⟨i, hi⟩
    exact Sum.inr_ne_inl hi
  have hz0L : Sum.inr z0 ∉ Lset n := by
    rw [mem_Lset]
    rintro ⟨i, hi⟩
    exact Sum.inr_ne_inl hi
  rw [dIn]
  have hbase : Lset n ⊆ (univ : Finset (V n)).filter (fun b => exV n (Sum.inr j) b) := by
    intro b hb
    rw [mem_Lset] at hb
    obtain ⟨i, rfl⟩ := hb
    simp only [mem_filter, mem_univ, true_and]
    trivial
  by_cases h0 : j.val = 0
  · have hsub : Lset n ∪ {Sum.inr z1} ⊆
        (univ : Finset (V n)).filter (fun b => exV n (Sum.inr j) b) := by
      intro b hb
      rw [mem_union, mem_singleton] at hb
      rcases hb with hb | hb
      · exact hbase hb
      · subst hb
        simp only [mem_filter, mem_univ, true_and, exV_inr_inr]
        exact Or.inl ⟨h0, hz1⟩
    have hc : (Lset n ∪ {Sum.inr z1}).card = n / 2 + 1 := by
      rw [card_union_of_disjoint (disjoint_singleton_right.mpr hz1L), card_Lset, card_singleton]
    have hval : (if j.val = 0 ∨ j.val = 1 then 1 else 0) = 1 := by
      rw [if_pos]; exact Or.inl h0
    rw [hval]
    calc n / 2 + 1 = (Lset n ∪ {Sum.inr z1}).card := hc.symm
      _ ≤ _ := card_le_card hsub
  · by_cases h1 : j.val = 1
    · have hsub : Lset n ∪ {Sum.inr z0} ⊆
          (univ : Finset (V n)).filter (fun b => exV n (Sum.inr j) b) := by
        intro b hb
        rw [mem_union, mem_singleton] at hb
        rcases hb with hb | hb
        · exact hbase hb
        · subst hb
          simp only [mem_filter, mem_univ, true_and, exV_inr_inr]
          exact Or.inr ⟨h1, hz0⟩
      have hc : (Lset n ∪ {Sum.inr z0}).card = n / 2 + 1 := by
        rw [card_union_of_disjoint (disjoint_singleton_right.mpr hz0L), card_Lset, card_singleton]
      have hval : (if j.val = 0 ∨ j.val = 1 then 1 else 0) = 1 := by
        rw [if_pos]; exact Or.inr h1
      rw [hval]
      calc n / 2 + 1 = (Lset n ∪ {Sum.inr z0}).card := hc.symm
        _ ≤ _ := card_le_card hsub
    · have hval : (if j.val = 0 ∨ j.val = 1 then 1 else 0) = 0 := by
        rw [if_neg]; rintro (h | h) <;> [exact h0 h; exact h1 h]
      rw [hval]
      exact le_trans (le_of_eq (card_Lset n).symm) (card_le_card hbase)

/-- `⌊n²/4⌋ = ⌊n/2⌋ · ⌈n/2⌉`. -/
lemma sq_div_four (n : ℕ) : n ^ 2 / 4 = n / 2 * (n - n / 2) := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Nat.even_or_odd n
  · have h1 : (k + k) / 2 = k := by omega
    have h2 : k + k - (k + k) / 2 = k := by omega
    have h3 : (k + k) ^ 2 = 4 * (k * k) := by ring
    have h4 : (k + k) ^ 2 / 4 = k * k := by
      rw [h3]
      omega
    rw [h4, h2, h1]
  · have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : 2 * k + 1 - (2 * k + 1) / 2 = k + 1 := by omega
    have h3 : (2 * k + 1) ^ 2 = 1 + 4 * (k * k + k) := by ring
    have h4 : (2 * k + 1) ^ 2 / 4 = k * k + k := by
      rw [h3]
      omega
    rw [h4, h2, h1]
    ring

/-- The number of right vertices numbered `0` or `1` is `2`. -/
lemma card_zero_one (n : ℕ) (hn : 4 ≤ n) :
    ((univ : Finset (Fin (n - n / 2))).filter (fun j => j.val = 0 ∨ j.val = 1)).card = 2 := by
  have hset : (univ : Finset (Fin (n - n / 2))).filter (fun j => j.val = 0 ∨ j.val = 1)
      = {(⟨0, by omega⟩ : Fin (n - n / 2)), (⟨1, by omega⟩ : Fin (n - n / 2))} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl (Fin.ext (by simpa using h))
      · exact Or.inr (Fin.ext (by simpa using h))
    · rintro (h | h) <;> rw [h] <;> simp
  rw [hset, card_pair]
  intro h
  have : (⟨0, by omega⟩ : Fin (n - n / 2)).val = (⟨1, by omega⟩ : Fin (n - n / 2)).val :=
    congrArg Fin.val h
  simp at this

/-- The example has at least `⌊n²/4⌋ + 1` edges. -/
theorem edge_count (n : ℕ) (hn : 4 ≤ n) :
    2 * (n ^ 2 / 4 + 1) ≤ degSum (exV n) univ := by
  set f : V n → ℕ := fun a => dIn (exV n) univ a with hf
  have hdeg : degSum (exV n) univ = ∑ a ∈ (univ : Finset (V n)), f a := by
    rw [degSum, hf]
  rw [hdeg]
  have hsplit : (∑ a ∈ (univ : Finset (V n)), f a)
      = (∑ a ∈ Lset n, f a) + ∑ a ∈ Rset n, f a := by
    rw [← univ_eq_Lset_union_Rset n]
    exact sum_union (s₁ := Lset n) (s₂ := Rset n) (disjoint_Lset_Rset n)
  rw [hsplit]
  simp only [hf]
  have hL : n / 2 * (n - n / 2) ≤ ∑ a ∈ Lset n, dIn (exV n) univ a := by
    rw [Lset, sum_image (fun x _ y _ h => Sum.inl.inj h)]
    calc n / 2 * (n - n / 2) = ∑ _i ∈ (univ : Finset (Fin (n / 2))), (n - n / 2) := by
          rw [sum_const, card_univ, Fintype.card_fin]
          simp [nsmul_eq_mul]
      _ ≤ ∑ i ∈ (univ : Finset (Fin (n / 2))), dIn (exV n) univ (Sum.inl i) :=
          sum_le_sum fun i _ => le_deg_inl n i
  have hR : (n - n / 2) * (n / 2) + 2 ≤ ∑ a ∈ Rset n, dIn (exV n) univ a := by
    rw [Rset, sum_image (fun x _ y _ h => Sum.inr.inj h)]
    have h1 : (∑ j ∈ (univ : Finset (Fin (n - n / 2))), n / 2)
        = (n - n / 2) * (n / 2) := by
      rw [sum_const, card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    have h2 : (∑ j ∈ (univ : Finset (Fin (n - n / 2))),
          (if j.val = 0 ∨ j.val = 1 then 1 else 0)) = 2 := by
      rw [← sum_filter, ← card_eq_sum_ones]
      exact card_zero_one n hn
    calc (n - n / 2) * (n / 2) + 2
        = ∑ j ∈ (univ : Finset (Fin (n - n / 2))),
            ((n / 2 + (if j.val = 0 ∨ j.val = 1 then 1 else 0)) : ℕ) := by
          rw [sum_add_distrib, h1, h2]
      _ ≤ ∑ j ∈ (univ : Finset (Fin (n - n / 2))), dIn (exV n) univ (Sum.inr j) :=
          sum_le_sum fun j _ => le_deg_inr n hn j
  have hsq := sq_div_four n
  calc 2 * (n ^ 2 / 4 + 1) = 2 * (n / 2 * (n - n / 2) + 1) := by rw [hsq]
    _ = n / 2 * (n - n / 2) + ((n - n / 2) * (n / 2) + 2) := by ring
    _ ≤ _ := Nat.add_le_add hL hR

/-- The left vertices of `T`. -/
def inlPart (n : ℕ) (T : Finset (V n)) : Finset (V n) :=
  T.filter (fun a => ∃ i, a = Sum.inl i)

/-- The right vertices of `T`. -/
def inrPart (n : ℕ) (T : Finset (V n)) : Finset (V n) :=
  T.filter (fun a => ∃ j, a = Sum.inr j)

lemma inlPart_le_one (n : ℕ) {T : Finset (V n)} (hT : IsTri (exV n) T) :
    (inlPart n T).card ≤ 1 := by
  rw [card_le_one]
  intro a ha b hb
  rw [inlPart, mem_filter] at ha hb
  obtain ⟨haT, ⟨i, rfl⟩⟩ := ha
  obtain ⟨hbT, ⟨k, rfl⟩⟩ := hb
  by_contra hne
  exact exV_inl_inl i k (hT.2 (Sum.inl i) haT (Sum.inl k) hbT hne)

lemma inrPart_ge_two (n : ℕ) (hn : 4 ≤ n) {T : Finset (V n)} (hT : IsTri (exV n) T) :
    2 ≤ (inrPart n T).card := by
  have hcompl : (T.filter (fun a => ¬ ∃ j, a = Sum.inr j)).card = (inlPart n T).card := by
    rw [inlPart]
    congr 1
    ext a
    simp only [mem_filter]
    exact and_congr_right fun _ => not_inr_iff_inl
  have hsum := card_filter_add_card_filter_not (s := T) (fun a : V n => ∃ j, a = Sum.inr j)
  rw [hcompl, hT.1] at hsum
  have hleft := inlPart_le_one n hT
  show 2 ≤ (T.filter (fun a : V n => ∃ j, a = Sum.inr j)).card
  omega

/-- Every triangle of the example contains the two right vertices numbered
`0` and `1`. -/
lemma tri_contains_pair (n : ℕ) (hn : 4 ≤ n) {T : Finset (V n)} (hT : IsTri (exV n) T) :
    ∃ i j : Fin (n - n / 2), i.val = 0 ∧ j.val = 1 ∧
      Sum.inr i ∈ T ∧ Sum.inr j ∈ T := by
  have hright : 2 ≤ (inrPart n T).card := inrPart_ge_two n hn hT
  have hne2 : ∃ a ∈ inrPart n T, ∃ b ∈ inrPart n T, a ≠ b := by
    rw [← one_lt_card]; omega
  obtain ⟨a, ha, b, hb, hab⟩ := hne2
  rw [inrPart, mem_filter] at ha hb
  obtain ⟨haT, ⟨i, hi⟩⟩ := ha
  obtain ⟨hbT, ⟨k, hk⟩⟩ := hb
  rw [hi] at haT
  rw [hk] at hbT
  have hne : (Sum.inr i : V n) ≠ (Sum.inr k : V n) := by
    rw [← hi, ← hk]; exact hab
  have hstep := (exV_inr_inr i k).mp (hT.2 (Sum.inr i : V n) haT (Sum.inr k : V n) hbT hne)
  rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨i, k, h1, h2, haT, hbT⟩
  · exact ⟨k, i, h2, h1, hbT, haT⟩

/-- The example does contain a triangle. -/
lemma exists_tri_exV (n : ℕ) (hn : 4 ≤ n) : ∃ T : Finset (V n), IsTri (exV n) T := by
  obtain ⟨z0, hz0⟩ : ∃ z : Fin (n - n / 2), z.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨z1, hz1⟩ : ∃ z : Fin (n - n / 2), z.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hh : 0 < n / 2 := by omega
  have hxy : (Sum.inl (⟨0, hh⟩ : Fin (n / 2)) : V n) ≠ Sum.inr z0 := by
    intro h; exact Sum.inl_ne_inr h
  have hxz : (Sum.inl (⟨0, hh⟩ : Fin (n / 2)) : V n) ≠ Sum.inr z1 := by
    intro h; exact Sum.inl_ne_inr h
  have hyz : (Sum.inr z0 : V n) ≠ Sum.inr z1 := by
    intro h
    have hv : z0.val = z1.val := congrArg Fin.val (Sum.inr.inj h)
    omega
  refine ⟨{(Sum.inl (⟨0, hh⟩ : Fin (n / 2)) : V n), Sum.inr z0, Sum.inr z1}, ?_, ?_⟩
  · rw [card_eq_three]
    exact ⟨_, _, _, hxy, hxz, hyz, rfl⟩
  · intro a ha b hb hab
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact absurd rfl hab
    · trivial
    · trivial
    · trivial
    · exact absurd rfl hab
    · rw [exV_inr_inr]
      exact Or.inl ⟨hz0, hz1⟩
    · trivial
    · rw [exV_inr_inr]
      exact Or.inr ⟨hz1, hz0⟩
    · exact absurd rfl hab

/-- **Sharpness**: any two distinct triangles of the example share an edge,
so at most one edge-disjoint triangle exists. -/
theorem share_pair (n : ℕ) (hn : 4 ≤ n) {T1 T2 : Finset (V n)}
    (h1 : IsTri (exV n) T1) (h2 : IsTri (exV n) T2) (hne : T1 ≠ T2) :
    (T1 ∩ T2).card = 2 := by
  obtain ⟨i, j, hi, hj, h1i, h1j⟩ := tri_contains_pair n hn h1
  obtain ⟨i', j', hi', hj', h2i, h2j⟩ := tri_contains_pair n hn h2
  have hii : i = i' := Fin.ext (by omega)
  have hjj : j = j' := Fin.ext (by omega)
  have hmem : ({Sum.inr i, Sum.inr j} : Finset (V n)) ⊆ T1 ∩ T2 := by
    intro x hx
    rw [mem_inter]
    simp only [mem_insert, mem_singleton] at hx
    constructor
    · rcases hx with rfl | rfl
      · exact h1i
      · exact h1j
    · rcases hx with rfl | rfl
      · rw [hii]; exact h2i
      · rw [hjj]; exact h2j
  have hdist : (Sum.inr i : V n) ≠ Sum.inr j := by
    intro h
    have hv : i.val = j.val := congrArg Fin.val (Sum.inr.inj h)
    omega
  have hge : 2 ≤ (T1 ∩ T2).card := by
    have hle' := card_le_card hmem
    rw [card_pair hdist] at hle'
    exact hle'
  have hle : (T1 ∩ T2).card ≤ 2 := by
    have hc := card_le_card (inter_subset_left : T1 ∩ T2 ⊆ T1)
    rw [h1.1] at hc
    by_contra hcon
    push Not at hcon
    have heq : T1 ∩ T2 = T1 := eq_of_subset_of_card_le inter_subset_left (by omega)
    have hsub2 : T1 ⊆ T2 := by rw [← heq]; exact inter_subset_right
    have heq2 : T1 = T2 := eq_of_subset_of_card_le hsub2 (by omega)
    exact hne heq2
  omega

/-- **JSP-000839, sharpness at every order `n ≥ 4`**: an `n`-vertex graph with
`⌊n²/4⌋ + 1` edges in which at most one edge-disjoint triangle exists. -/
theorem answer_general (n : ℕ) (hn : 4 ≤ n) :
    Fintype.card (V n) = n ∧
      2 * (n ^ 2 / 4 + 1) ≤ degSum (exV n) univ ∧
      (∃ T : Finset (V n), IsTri (exV n) T) ∧
      (∀ T1 T2 : Finset (V n), IsTri (exV n) T1 → IsTri (exV n) T2 → T1 ≠ T2 →
        (T1 ∩ T2).card = 2) :=
  ⟨card_V n, edge_count n hn, exists_tri_exV n hn,
    fun _ _ h1 h2 hne => share_pair n hn h1 h2 hne⟩

end JSP839
