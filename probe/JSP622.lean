/-
# JSP-000622 probe (graph order 5)

Problem (catalog `problems/catalog-0601-0700.md#JSP-000622`):

  For a prescribed small graph order, what is the worst-case minimum number of
  clique or independent-set parts in a vertex partition?

The "minimum number of clique or independent-set parts" is the **cochromatic
number**: the least `k` such that `V` can be partitioned into `k` parts, each
of which is a clique or an independent set.  This file treats the graph order
`n = 5`:

  * `cochrom_le_three` — every graph on 5 vertices has cochromatic number at
    most 3;
  * `c5_needs_three` — the 5-cycle admits no cover by 2 clique-or-independent
    sets;
  * `c5_three` — the 5-cycle does admit one by 3 such sets.

Hence the worst-case cochromatic number over graphs of order 5 is exactly 3,
attained by `C_5`.

Partitions and covers are equivalent here: a cover by `k` clique-or-independent
sets can be turned into a partition into at most `k` parts of the same kind, and
conversely.  The upper bound is proved structurally (a non-edge gives an
independent pair, and the at most three remaining vertices are split off), the
two lower-bound statements are finite verifications over `C_5`.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push

open Finset

namespace JSP622

variable {α : Type} [Fintype α] [DecidableEq α]

/-- A set is a clique or an independent set (for the relation `r`). -/
@[reducible] def IsCliqueOrIndep (r : α → α → Prop) (C : Finset α) : Prop :=
  (∀ a ∈ C, ∀ b ∈ C, a ≠ b → r a b) ∨ (∀ a ∈ C, ∀ b ∈ C, a ≠ b → ¬ r a b)

/-- `V` can be covered by `k` sets, each a clique or an independent set. -/
@[reducible] def CochromLe (r : α → α → Prop) (k : ℕ) : Prop :=
  ∃ C : Fin k → Finset α, (∀ u, ∃ i, u ∈ C i) ∧ ∀ i, IsCliqueOrIndep r (C i)

/-- The partition formulation: `V` is split into `k` parts, each a clique or
an independent set. -/
@[reducible] def CochromFun (r : α → α → Prop) (k : ℕ) : Prop :=
  ∃ f : α → Fin k, ∀ i : Fin k, IsCliqueOrIndep r (univ.filter (fun a => f a = i))

lemma isCliqueOrIndep_subset (r : α → α → Prop) {C S : Finset α}
    (h : IsCliqueOrIndep r C) (hsub : S ⊆ C) : IsCliqueOrIndep r S := by
  rcases h with h | h
  · exact Or.inl fun a ha b hb hab => h a (hsub ha) b (hsub hb) hab
  · exact Or.inr fun a ha b hb hab => h a (hsub ha) b (hsub hb) hab

/-- A cover by clique-or-independent sets yields a partition into the same
number of such parts. -/
lemma cover_to_fun {r : α → α → Prop} {k : ℕ} (h : CochromLe r k) : CochromFun r k := by
  classical
  obtain ⟨C, hcov, hcoi⟩ := h
  choose f hf using hcov
  refine ⟨f, fun i => ?_⟩
  refine isCliqueOrIndep_subset r (hcoi i) ?_
  intro a ha
  rw [mem_filter] at ha
  rw [← ha.2]
  exact hf a

/-- **JSP-000622 (order 5), upper bound**: every graph on 5 vertices can be
covered by 3 clique-or-independent sets. -/
theorem cochrom_le_three (r : Fin 5 → Fin 5 → Prop) [DecidableRel r]
    (hsym : ∀ a b, r a b → r b a) : CochromLe r 3 := by
  classical
  by_cases hcomplete : ∀ a b : Fin 5, a ≠ b → r a b
  · -- the complete graph: one clique
    refine ⟨fun _ => univ, fun u => ⟨0, mem_univ u⟩, fun i => Or.inl ?_⟩
    intro x _ y _ hxy
    exact hcomplete x y hxy
  · push Not at hcomplete
    obtain ⟨a, b, hab, hnab⟩ := hcomplete
    set I : Finset (Fin 5) := {a, b} with hI
    have hIindep : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ r x y := by
      intro x hx y hy hxy
      simp only [hI, mem_insert, mem_singleton] at hx hy
      rcases hx with hx1 | hx1 <;> rcases hy with hy1 | hy1
      · rw [hx1, hy1] at hxy; exact absurd rfl hxy
      · rw [hx1, hy1]; exact hnab
      · rw [hx1, hy1]; exact fun h => hnab (hsym b a h)
      · rw [hx1, hy1] at hxy; exact absurd rfl hxy
    by_cases hrest : ∃ x y : Fin 5, x ≠ y ∧ ¬ (x = a ∨ x = b) ∧ ¬ (y = a ∨ y = b) ∧ ¬ r x y
    · -- three parts
      obtain ⟨x, y, hxy, hxa, hya, hnxy⟩ := hrest
      set J : Finset (Fin 5) := {x, y} with hJ
      set K : Finset (Fin 5) := univ \ (I ∪ J) with hK
      have hJindep : ∀ u ∈ J, ∀ v ∈ J, u ≠ v → ¬ r u v := by
        intro u hu v hv huv
        simp only [hJ, mem_insert, mem_singleton] at hu hv
        rcases hu with hu1 | hu1 <;> rcases hv with hv1 | hv1
        · rw [hu1, hv1] at huv; exact absurd rfl huv
        · rw [hu1, hv1]; exact hnxy
        · rw [hu1, hv1]; exact fun h => hnxy (hsym y x h)
        · rw [hu1, hv1] at huv; exact absurd rfl huv
      -- `K` has at most one vertex, so it is a clique
      have hKcard : K.card ≤ 1 := by
        have hxI : x ∉ I := by
          simp only [hI, mem_insert, mem_singleton, not_or]
          exact not_or.mp hxa
        have hyI : y ∉ I := by
          simp only [hI, mem_insert, mem_singleton, not_or]
          exact not_or.mp hya
        have hdisj : Disjoint I J := by
          rw [Finset.disjoint_left]
          intro w hw1 hw2
          simp only [hI, hJ, mem_insert, mem_singleton] at hw1 hw2
          rcases hw1 with hw1 | hw1 <;> rcases hw2 with hw2 | hw2
          · rw [← hw2, hw1] at hxI; exact hxI (by simp [hI])
          · rw [← hw2, hw1] at hyI; exact hyI (by simp [hI])
          · rw [← hw2, hw1] at hxI; exact hxI (by simp [hI])
          · rw [← hw2, hw1] at hyI; exact hyI (by simp [hI])
        have h4 : (I ∪ J).card = 4 := by
          rw [card_union_of_disjoint hdisj, hI, hJ, card_pair hab, card_pair hxy]
        rw [hK, card_sdiff_of_subset (subset_univ _), card_univ, h4]
        norm_num
      have hKclique : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → r u v := by
        intro u hu v hv huv
        have hle1 : K.card ≤ 1 := hKcard
        exact absurd (Finset.card_le_one.mp hle1 u hu v hv) huv
      refine ⟨fun i => if i = (0 : Fin 3) then I else if i = (1 : Fin 3) then J else K,
        ?_, ?_⟩
      · intro u
        by_cases h1 : u ∈ I
        · exact ⟨0, by simp [h1]⟩
        by_cases h2 : u ∈ J
        · exact ⟨1, by simp [h2]⟩
        · refine ⟨2, ?_⟩
          show u ∈ K
          simp only [hK, mem_sdiff, mem_univ, true_and, mem_union, not_or]
          exact ⟨h1, h2⟩
      · intro i
        fin_cases i
        · show IsCliqueOrIndep r I
          exact Or.inr hIindep
        · show IsCliqueOrIndep r J
          exact Or.inr hJindep
        · show IsCliqueOrIndep r K
          exact Or.inl hKclique
    · -- the rest is a clique: two parts
      push Not at hrest
      refine ⟨fun i => if i = (0 : Fin 3) then I else univ \ I, fun u => ?_, fun i => ?_⟩
      · by_cases h1 : u ∈ I
        · exact ⟨0, by simp [h1]⟩
        · refine ⟨1, ?_⟩
          show u ∈ (univ \ I)
          simp only [mem_sdiff, mem_univ, true_and]
          exact h1
      · fin_cases i
        · show IsCliqueOrIndep r I
          exact Or.inr hIindep
        · show IsCliqueOrIndep r (univ \ I)
          refine Or.inl ?_
          intro u hu v hv huv
          simp only [mem_sdiff, mem_univ, true_and] at hu hv
          have hu' : ¬(u = a ∨ u = b) := by
            simpa [hI, mem_insert, mem_singleton] using hu
          have hv' : ¬(v = a ∨ v = b) := by
            simpa [hI, mem_insert, mem_singleton] using hv
          exact hrest u v huv (not_or.mp hu') (not_or.mp hv')
        · show IsCliqueOrIndep r (univ \ I)
          refine Or.inl ?_
          intro u hu v hv huv
          simp only [mem_sdiff, mem_univ, true_and] at hu hv
          have hu' : ¬(u = a ∨ u = b) := by
            simpa [hI, mem_insert, mem_singleton] using hu
          have hv' : ¬(v = a ∨ v = b) := by
            simpa [hI, mem_insert, mem_singleton] using hv
          exact hrest u v huv (not_or.mp hu') (not_or.mp hv')

/-- The 5-cycle. -/
def c5 : Fin 5 → Fin 5 → Prop := fun a b => b = a + 1 ∨ a = b + 1

instance c5_dec : DecidableRel c5 :=
  fun a b => inferInstanceAs (Decidable (b = a + 1 ∨ a = b + 1))

/-- The 5-cycle admits **no** partition into 2 clique-or-independent parts. -/
theorem c5_needs_three : ¬ CochromFun c5 2 := by
  unfold CochromFun IsCliqueOrIndep
  decide

/-- The 5-cycle does admit a partition into 3 such parts. -/
theorem c5_three : CochromFun c5 3 := by
  unfold CochromFun IsCliqueOrIndep
  decide

/-- **JSP-000622 (order 5), answer**: the worst-case cochromatic number over
graphs of order 5 is exactly 3. -/
theorem answer :
    (∀ (r : Fin 5 → Fin 5 → Prop) [DecidableRel r], (∀ a b, r a b → r b a) →
        CochromFun r 3) ∧
      ¬ CochromFun c5 2 ∧ CochromFun c5 3 :=
  ⟨fun r _ hsym => cover_to_fun (cochrom_le_three r hsym), c5_needs_three, c5_three⟩

end JSP622
