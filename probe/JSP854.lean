/-
# JSP-000854 probe

Problem (catalog `problems/catalog-0801-0900.md#JSP-000854`):

  How many vertex subsets meet every hyperedge while containing none of them in
  full?

Answer: at most `2 ^ n - 2` for a nonempty hypergraph on `n ≥ 1` vertices, and
`2 ^ n - 2` is attained (take the hypergraph with the single edge `V`).

Why: the empty set meets no edge, and the whole vertex set `V` contains every
edge in full, so at most the `2 ^ n - 2` remaining subsets qualify; for the
one-edge hypergraph `{V}` exactly those `2 ^ n - 2` subsets qualify.

This file proves BOTH halves:
* `good_card_le` — at most `2 ^ n - 2` qualifying subsets for any nonempty
  hypergraph;
* `good_attained` — the one-edge hypergraph `{univ}` has exactly `2 ^ n - 2`
  qualifying subsets.

The vertex set is assumed nonempty (`n ≥ 1`); for `n = 0` the answer
`2 ^ 0 - 2 = 0` also holds, but that degenerate case is not treated here.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum

open Finset

namespace JSP854

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

/-- `S` meets every edge of `H` and contains no edge of `H` in full. -/
@[reducible] def Good (H : Finset (Finset α)) (S : Finset α) : Prop :=
  (∀ e ∈ H, (S ∩ e).Nonempty) ∧ ∀ e ∈ H, ¬ e ⊆ S

/-- The family of qualifying vertex subsets. -/
def goodFamily (H : Finset (Finset α)) : Finset (Finset α) :=
  (univ : Finset α).powerset.filter (fun S => Good H S)

lemma mem_goodFamily {H : Finset (Finset α)} {S : Finset α} :
    S ∈ goodFamily H ↔ S ⊆ univ ∧ Good H S := by
  unfold goodFamily
  rw [mem_filter, mem_powerset]

lemma empty_not_good (H : Finset (Finset α)) (hne : H.Nonempty) :
    (∅ : Finset α) ∉ goodFamily H := by
  rw [mem_goodFamily]
  rintro ⟨-, h1, -⟩
  obtain ⟨e, he⟩ := hne
  have h := h1 e he
  simp at h

lemma univ_not_good (H : Finset (Finset α)) (hne : H.Nonempty) :
    (univ : Finset α) ∉ goodFamily H := by
  rw [mem_goodFamily]
  rintro ⟨-, -, h2⟩
  obtain ⟨e, he⟩ := hne
  exact h2 e he (subset_univ e)

lemma pair_card : ({∅, univ} : Finset (Finset α)).card = 2 := by
  rw [card_insert_of_notMem]
  · simp
  · rw [mem_singleton]
    intro h
    have hne := Finset.univ_nonempty (α := α)
    rw [← h] at hne
    exact Finset.not_nonempty_empty hne

/-- **JSP-000854, upper bound**: a nonempty hypergraph on `n` vertices has at
most `2 ^ n - 2` subsets meeting every edge and containing none in full. -/
theorem good_card_le (H : Finset (Finset α)) (hne : H.Nonempty) :
    (goodFamily H).card ≤ 2 ^ Fintype.card α - 2 := by
  have hsub : goodFamily H ⊆ (univ : Finset α).powerset \ ({∅, univ} : Finset (Finset α)) := by
    intro S hS
    have hmem := hS
    rw [mem_goodFamily] at hmem
    refine mem_sdiff.mpr ⟨?_, ?_⟩
    · rw [mem_powerset]; exact hmem.1
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨fun h => empty_not_good H hne (h ▸ hS), fun h => univ_not_good H hne (h ▸ hS)⟩
  have hcard : (goodFamily H).card ≤
      ((univ : Finset α).powerset \ ({∅, univ} : Finset (Finset α))).card :=
    card_le_card hsub
  rw [card_sdiff_of_subset (by simp [mem_powerset]), card_powerset, pair_card, card_univ] at hcard
  exact hcard

/-- **JSP-000854, attainment**: the hypergraph with the single edge `univ` has
exactly `2 ^ n - 2` qualifying subsets. -/
theorem good_attained :
    (goodFamily ({univ} : Finset (Finset α))).card = 2 ^ Fintype.card α - 2 := by
  have hfam : goodFamily ({univ} : Finset (Finset α)) =
      (univ : Finset α).powerset \ ({∅, univ} : Finset (Finset α)) := by
    ext S
    rw [mem_goodFamily, mem_sdiff, mem_powerset]
    simp only [mem_singleton, mem_insert, not_or, Good]
    constructor
    · rintro ⟨hsub, h1, h2⟩
      refine ⟨hsub, ?_, ?_⟩
      · intro hS
        subst hS
        have h1' := h1 univ (by simp)
        simp at h1'
      · intro hS
        subst hS
        exact h2 univ (by simp) (subset_refl univ)
    · rintro ⟨hsub, hne1, hne2⟩
      refine ⟨hsub, ?_, ?_⟩
      · intro e he
        subst he
        obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hne1
        exact ⟨x, by simp [hx]⟩
      · intro e he
        subst he
        intro hsub
        exact hne2 (Finset.eq_univ_of_forall (fun x => hsub (mem_univ x)))
  rw [hfam, card_sdiff_of_subset (by simp [mem_powerset]), card_powerset, pair_card, card_univ]

/-- The answer to JSP-000854, packaged. -/
theorem answer (H : Finset (Finset α)) (hne : H.Nonempty) :
    (goodFamily H).card ≤ 2 ^ Fintype.card α - 2 ∧
      ∃ H' : Finset (Finset α), H'.Nonempty ∧
        (goodFamily H').card = 2 ^ Fintype.card α - 2 :=
  ⟨good_card_le H hne, ⟨{univ}, ⟨univ, mem_singleton.mpr rfl⟩, good_attained⟩⟩

end JSP854
