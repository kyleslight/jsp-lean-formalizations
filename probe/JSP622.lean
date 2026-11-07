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
import Mathlib.Tactic.IntervalCases
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

/-! ## General graph order

The worst-case cochromatic number over graphs of order `n` is `z(n)`.  It is
*not* given by a closed formula: the exact values are known only for
`n ≤ 19` (Erdős Problem 758: `1,1,2,2,3,3,3,3,4,4,4,4,5,5,5,6,6,6,6`, with
`z(12) = 4` the one hard case), the value at `n = 20` is unknown (`6` or `7`),
and asymptotically `z(n) ≍ n / log n` (Gimbel 1986).  So "the formula for all
`n`" is an open problem; what is formalized below is

* a general upper bound for every order: `z(n) ≤ ⌈n/2⌉` (`cochrom_le_half`);
* Ramsey `R(3,3) = 6` (`exists_homog_triple`), the engine of the recursion
  `z(n) ≤ 1 + z(n-3)`;
* the exact values for `n = 1, …, 7`, i.e. `1,1,2,2,3,3,3`, both directions.
-/

/-- A two-element set is a clique or an independent set. -/
lemma coi_pair (r : α → α → Prop) (hsym : ∀ a b, r a b → r b a)
    {a b : α} (_hab : a ≠ b) : IsCliqueOrIndep r {a, b} := by
  by_cases h : r a b
  · refine Or.inl ?_
    intro x hx y hy hxy
    simp only [mem_insert, mem_singleton] at hx hy
    rcases hx with h1 | h1 <;> rcases hy with h2 | h2
    · rw [h1, h2] at hxy; exact absurd rfl hxy
    · rw [h1, h2]; exact h
    · rw [h1, h2]; exact hsym a b h
    · rw [h1, h2] at hxy; exact absurd rfl hxy
  · refine Or.inr ?_
    intro x hx y hy hxy
    simp only [mem_insert, mem_singleton] at hx hy
    rcases hx with h1 | h1 <;> rcases hy with h2 | h2
    · rw [h1, h2] at hxy; exact absurd rfl hxy
    · rw [h1, h2]; exact h
    · rw [h1, h2]; exact fun h' => h (hsym b a h')
    · rw [h1, h2] at hxy; exact absurd rfl hxy

/-- Every set of at most two vertices is a clique or an independent set. -/
lemma coi_of_card_le_two (r : α → α → Prop) (hsym : ∀ a b, r a b → r b a)
    {S : Finset α} (h : S.card ≤ 2) : IsCliqueOrIndep r S := by
  rcases Nat.lt_or_ge S.card 2 with hlt | hge
  · have h1 : S.card ≤ 1 := by omega
    refine Or.inl ?_
    intro x hx y hy hxy
    exact absurd (card_le_one.mp h1 x hx y hy) hxy
  · have h2 : S.card = 2 := by omega
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp h2
    exact coi_pair r hsym hab

/-- A finite vertex set of at most `2k` elements can be covered by `k`
clique-or-independent parts. -/
lemma cover_of_card_le (r : α → α → Prop) (hsym : ∀ a b, r a b → r b a) :
    ∀ k : ℕ, ∀ S : Finset α, S.card ≤ 2 * k →
      ∃ C : Fin k → Finset α, (∀ u ∈ S, ∃ i, u ∈ C i) ∧
        ∀ i, IsCliqueOrIndep r (C i) := by
  intro k
  induction k with
  | zero =>
    intro S h
    have hS : S = ∅ := card_eq_zero.mp (by omega)
    refine ⟨Fin.elim0, ?_, fun i => i.elim0⟩
    intro u hu
    rw [hS] at hu
    simp at hu
  | succ k ih =>
    intro S h
    by_cases hsmall : S.card ≤ 2
    · exact ⟨fun _ => S, fun u hu => ⟨0, hu⟩,
        fun _ => coi_of_card_le_two r hsym hsmall⟩
    · push Not at hsmall
      have hlt : 1 < S.card := by omega
      obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hlt
      have hsub : ({a, b} : Finset α) ⊆ S := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ha
        · exact hb
      set R : Finset α := S \ {a, b} with hR
      have hRcard : R.card ≤ 2 * k := by
        rw [hR, card_sdiff_of_subset hsub, card_pair hab, Nat.sub_le_iff_le_add]
        omega
      obtain ⟨C, hcov, hcoi⟩ := ih R hRcard
      refine ⟨Fin.cons {a, b} C, ?_, ?_⟩
      · intro u hu
        by_cases hmem : u ∈ ({a, b} : Finset α)
        · exact ⟨0, by simpa using hmem⟩
        · have huR : u ∈ R := by simp [hR, hu, hmem]
          obtain ⟨i, hi⟩ := hcov u huR
          exact ⟨i.succ, by simpa using hi⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using coi_pair r hsym hab
        · simpa using hcoi j

/-- **General upper bound**: a graph on at most `2k` vertices can always be
partitioned into `k` clique-or-independent parts (pair up the vertices). -/
lemma cochrom_le_half (r : α → α → Prop) (hsym : ∀ a b, r a b → r b a)
    (k : ℕ) (h : Fintype.card α ≤ 2 * k) : CochromLe r k := by
  obtain ⟨C, hcov, hcoi⟩ := cover_of_card_le r hsym k univ (by simpa using h)
  exact ⟨C, fun u => hcov u (mem_univ u), hcoi⟩

/-- **Ramsey `R(3,3) = 6`**: every graph on at least six vertices has three
vertices spanning a clique or an independent set. -/
lemma exists_homog_triple (r : α → α → Prop) (hsym : ∀ a b, r a b → r b a)
    (hcard : 6 ≤ Fintype.card α) :
    ∃ T : Finset α, T.card = 3 ∧ IsCliqueOrIndep r T := by
  classical
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card α)
  set N : Finset α := (univ.erase v).filter (fun u => r v u) with hN
  set M : Finset α := (univ.erase v).filter (fun u => ¬ r v u) with hM
  have hsplit : N.card + M.card = Fintype.card α - 1 := by
    rw [hN, hM, card_filter_add_card_filter_not, card_erase_of_mem (mem_univ v), card_univ]
  have h5 : 5 ≤ N.card + M.card := by omega
  rcases Nat.lt_or_ge N.card 3 with hlt | hge
  · -- at least three non-neighbours of `v`
    have hM3 : 3 ≤ M.card := by omega
    obtain ⟨S, hSsub, hScard⟩ := exists_subset_card_eq hM3
    have hSne : ∀ u ∈ S, u ≠ v ∧ ¬ r v u := by
      intro u hu
      have h1 := hSsub hu
      simp only [hM, mem_filter, mem_erase] at h1
      exact ⟨h1.1.1, h1.2⟩
    by_cases hp : ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ¬ r x y
    · -- an independent triple together with `v`
      obtain ⟨x, hx, y, hy, hxy, hnxy⟩ := hp
      obtain ⟨hxv, hnx⟩ := hSne x hx
      obtain ⟨hyv, hny⟩ := hSne y hy
      refine ⟨{v, x, y}, ?_, Or.inr ?_⟩
      · have hv : v ∉ ({x, y} : Finset α) := by
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨hxv.symm, hyv.symm⟩
        rw [card_insert_of_notMem hv, card_pair hxy]
      · intro a ha b hb hab
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with h1 | h1 | h1 <;> rcases hb with h2 | h2 | h2
        · rw [h1, h2] at hab; exact absurd rfl hab
        · rw [h1, h2]; exact hnx
        · rw [h1, h2]; exact hny
        · rw [h1, h2]; exact fun hh => hnx (hsym x v hh)
        · rw [h1, h2] at hab; exact absurd rfl hab
        · rw [h1, h2]; exact hnxy
        · rw [h1, h2]; exact fun hh => hny (hsym y v hh)
        · rw [h1, h2]; exact fun hh => hnxy (hsym y x hh)
        · rw [h1, h2] at hab; exact absurd rfl hab
    · -- all pairs of `S` are adjacent, so `S` is a clique
      push Not at hp
      exact ⟨S, hScard, Or.inl (fun a ha b hb hab => hp a ha b hb hab)⟩
  · -- at least three neighbours of `v`
    obtain ⟨S, hSsub, hScard⟩ := exists_subset_card_eq hge
    have hSne : ∀ u ∈ S, u ≠ v ∧ r v u := by
      intro u hu
      have h1 := hSsub hu
      simp only [hN, mem_filter, mem_erase] at h1
      exact ⟨h1.1.1, h1.2⟩
    by_cases hp : ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ r x y
    · -- a triangle together with `v`
      obtain ⟨x, hx, y, hy, hxy, hxy'⟩ := hp
      obtain ⟨hxv, hxr⟩ := hSne x hx
      obtain ⟨hyv, hyr⟩ := hSne y hy
      refine ⟨{v, x, y}, ?_, Or.inl ?_⟩
      · have hv : v ∉ ({x, y} : Finset α) := by
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨hxv.symm, hyv.symm⟩
        rw [card_insert_of_notMem hv, card_pair hxy]
      · intro a ha b hb hab
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with h1 | h1 | h1 <;> rcases hb with h2 | h2 | h2
        · rw [h1, h2] at hab; exact absurd rfl hab
        · rw [h1, h2]; exact hxr
        · rw [h1, h2]; exact hyr
        · rw [h1, h2]; exact hsym v x hxr
        · rw [h1, h2] at hab; exact absurd rfl hab
        · rw [h1, h2]; exact hxy'
        · rw [h1, h2]; exact hsym v y hyr
        · rw [h1, h2]; exact hsym x y hxy'
        · rw [h1, h2] at hab; exact absurd rfl hab
    · -- no two of `S` are adjacent, so `S` is independent
      push Not at hp
      exact ⟨S, hScard, Or.inr (fun a ha b hb hab => hp a ha b hb hab)⟩

/-- A set of at most four vertices can be covered by two clique-or-independent
parts. -/
lemma two_cover (r : α → α → Prop) (hsym : ∀ a b, r a b → r b a) {R : Finset α}
    (h : R.card ≤ 4) :
    ∃ A B : Finset α, A ⊆ R ∧ B ⊆ R ∧ A ∪ B = R ∧
      IsCliqueOrIndep r A ∧ IsCliqueOrIndep r B := by
  rcases Nat.lt_or_ge R.card 2 with hlt | hge
  · exact ⟨R, ∅, subset_rfl, empty_subset R, by simp,
      coi_of_card_le_two r hsym (by omega), Or.inl (fun a ha => by simp at ha)⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hge
    have hsub : ({a, b} : Finset α) ⊆ R := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    refine ⟨{a, b}, R \ {a, b}, hsub, sdiff_subset, union_sdiff_of_subset hsub,
      coi_pair r hsym hab, ?_⟩
    refine coi_of_card_le_two r hsym ?_
    rw [card_sdiff_of_subset hsub, card_pair hab]
    omega

/-- **`z(7) ≤ 3`**: every graph on seven vertices can be partitioned into three
clique-or-independent parts.  (The trivial pairing bound only gives four.) -/
lemma cochrom_le_three_of_seven (r : α → α → Prop) (hsym : ∀ a b, r a b → r b a)
    (hcard : Fintype.card α = 7) : CochromLe r 3 := by
  classical
  obtain ⟨T, hTcard, hTcoi⟩ := exists_homog_triple r hsym (by omega)
  have hR : (univ \ T).card ≤ 4 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hTcard]
    omega
  obtain ⟨A, B, hA, hB, hAB, hAcoi, hBcoi⟩ := two_cover r hsym hR
  refine ⟨fun i => if i = (0 : Fin 3) then T else if i = (1 : Fin 3) then A else B,
    ?_, ?_⟩
  · intro u
    by_cases hu : u ∈ T
    · exact ⟨0, by simp [hu]⟩
    · have huR : u ∈ univ \ T := by simp [hu]
      rw [← hAB] at huR
      rcases mem_union.mp huR with h | h
      · exact ⟨1, by simp [h]⟩
      · exact ⟨2, by simp [h]⟩
  · intro i
    fin_cases i
    · show IsCliqueOrIndep r T
      exact hTcoi
    · show IsCliqueOrIndep r A
      exact hAcoi
    · show IsCliqueOrIndep r B
      exact hBcoi

/-! ### Witnesses for orders 3, 4, 6, 7 -/

/-- The path on three vertices. -/
def p3 : Fin 3 → Fin 3 → Prop := fun a b => (a.val + 1 = b.val) ∨ (b.val + 1 = a.val)

instance p3_dec : DecidableRel p3 := fun a b =>
  inferInstanceAs (Decidable ((a.val + 1 = b.val) ∨ (b.val + 1 = a.val)))

set_option maxRecDepth 100000 in
theorem p3_needs_two : ¬ CochromFun p3 1 := by
  unfold CochromFun IsCliqueOrIndep
  decide

/-- The path on four vertices. -/
def p4 : Fin 4 → Fin 4 → Prop := fun a b => (a.val + 1 = b.val) ∨ (b.val + 1 = a.val)

instance p4_dec : DecidableRel p4 := fun a b =>
  inferInstanceAs (Decidable ((a.val + 1 = b.val) ∨ (b.val + 1 = a.val)))

set_option maxRecDepth 100000 in
theorem p4_needs_two : ¬ CochromFun p4 1 := by
  unfold CochromFun IsCliqueOrIndep
  decide

/-- The 5-cycle on the numbers `0, …, 4`, written out explicitly (so that it
can be reused on larger vertex sets). -/
def cyc5 (i j : ℕ) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
  (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨ (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
  (i = 4 ∧ j = 0) ∨ (i = 0 ∧ j = 4)

instance cyc5_dec (i j : ℕ) : Decidable (cyc5 i j) := by
  unfold cyc5; infer_instance

/-- The 5-cycle together with one isolated vertex (`C_5 ∪ K_1`). -/
def c5k1 : Fin 6 → Fin 6 → Prop := fun a b =>
  (a.val < 5 ∧ b.val < 5 ∧ cyc5 a.val b.val) ∨ (a.val = 5 ∧ b.val = 5 ∧ a ≠ b)

instance c5k1_dec : DecidableRel c5k1 := fun a b =>
  inferInstanceAs (Decidable ((a.val < 5 ∧ b.val < 5 ∧ cyc5 a.val b.val) ∨
    (a.val = 5 ∧ b.val = 5 ∧ a ≠ b)))

set_option maxRecDepth 100000 in
theorem c5k1_needs_three : ¬ CochromFun c5k1 2 := by
  unfold CochromFun IsCliqueOrIndep
  decide

/-- The 5-cycle together with one edge (`C_5 ∪ K_2`). -/
def c5k2 : Fin 7 → Fin 7 → Prop := fun a b =>
  (a.val < 5 ∧ b.val < 5 ∧ cyc5 a.val b.val) ∨ (5 ≤ a.val ∧ 5 ≤ b.val ∧ a ≠ b)

instance c5k2_dec : DecidableRel c5k2 := fun a b =>
  inferInstanceAs (Decidable ((a.val < 5 ∧ b.val < 5 ∧ cyc5 a.val b.val) ∨
    (5 ≤ a.val ∧ 5 ≤ b.val ∧ a ≠ b)))

set_option maxRecDepth 100000 in
theorem c5k2_needs_three : ¬ CochromFun c5k2 2 := by
  unfold CochromFun IsCliqueOrIndep
  decide

/-! ### The recursion `z(n) ≤ 1 + z(n-3)` and the bound `z(n) ≤ ⌊(n-5)/3⌋ + 3`

Ramsey's theorem `R(3,3) = 6` (`exists_homog_triple_sub`) says that every set of at
least six vertices contains three vertices spanning a clique or an independent set.
Removing those three vertices as one part and recursing gives

  `z(n) ≤ 1 + z(n - 3)`  for `n ≥ 6`,

and with the base values `z(5) = z(6) = z(7) = 3` this iterates to

  `z(n) ≤ ⌊(n - 5)/3⌋ + 3`  for `n ≥ 5`,

i.e. `z(n) ≤ n/3 + 2` for every `n`.  This is the strongest *uniform* bound that
`R(3,3)` alone yields; it agrees with the known values for `n ≤ 10` and exceeds
them by at most one for `n ≤ 19` (see the table at the end of the file). -/

/-- `S` can be covered by `k` sets, each a clique or an independent set. -/
@[reducible] def CoverLe (r : α → α → Prop) (S : Finset α) (k : ℕ) : Prop :=
  ∃ C : Fin k → Finset α, (∀ u ∈ S, ∃ i, u ∈ C i) ∧ ∀ i, IsCliqueOrIndep r (C i)

lemma cochromLe_iff_coverLe {r : α → α → Prop} {k : ℕ} :
    CochromLe r k ↔ CoverLe r univ k := by
  constructor
  · rintro ⟨C, hcov, hcoi⟩; exact ⟨C, fun u _ => hcov u, hcoi⟩
  · rintro ⟨C, hcov, hcoi⟩; exact ⟨C, fun u => hcov u (mem_univ u), hcoi⟩

/-- Enlarging the number of allowed parts. -/
lemma coverLe_mono {r : α → α → Prop} {S : Finset α} {k k' : ℕ}
    (h : CoverLe r S k) (hle : k ≤ k') : CoverLe r S k' := by
  obtain ⟨C, hcov, hcoi⟩ := h
  refine ⟨fun i => if h : (i : ℕ) < k then C ⟨i, h⟩ else ∅, ?_, ?_⟩
  · intro u hu
    obtain ⟨i, hi⟩ := hcov u hu
    exact ⟨⟨i, lt_of_lt_of_le i.isLt hle⟩, by simpa using hi⟩
  · intro i
    simp only []
    split_ifs with hlt
    · exact hcoi ⟨i, hlt⟩
    · exact Or.inl (fun a ha => by simp at ha)

/-- Any set of at most five vertices can be covered by three clique-or-independent
parts (a single vertex plus a two-part cover of the remaining at most four). -/
lemma cover_five (r : α → α → Prop) (hsym : ∀ a b, r a b → r b a) {S : Finset α}
    (h : S.card ≤ 5) : CoverLe r S 3 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · exact ⟨fun _ => ∅, fun u hu => by simp at hu, fun _ => Or.inl (fun a ha => by simp at ha)⟩
  · have h4 : (S.erase v).card ≤ 4 := by
      rw [card_erase_of_mem hv]; omega
    obtain ⟨A, B, hA, hB, hAB, hAcoi, hBcoi⟩ := two_cover r hsym h4
    refine ⟨fun i => if i = 0 then {v} else if i = 1 then A else B, ?_, ?_⟩
    · intro u hu
      by_cases huv : u = v
      · exact ⟨0, by simp [huv]⟩
      · have hu' : u ∈ S.erase v := by simp [huv, hu]
        rw [← hAB] at hu'
        rcases mem_union.mp hu' with h' | h'
        · exact ⟨1, by simp [h']⟩
        · exact ⟨2, by simp [h']⟩
    · intro i
      fin_cases i
      · show IsCliqueOrIndep r {v}
        exact Or.inl (fun a ha b hb hab => by
          simp only [mem_singleton] at ha hb
          exact absurd (ha.trans hb.symm) hab)
      · show IsCliqueOrIndep r A; exact hAcoi
      · show IsCliqueOrIndep r B; exact hBcoi

/-- **Ramsey `R(3,3) = 6`**, set version: every set of at least six vertices
contains three vertices spanning a clique or an independent set. -/
lemma exists_homog_triple_sub (r : α → α → Prop) (hsym : ∀ a b, r a b → r b a)
    {S : Finset α} (hcard : 6 ≤ S.card) :
    ∃ T ⊆ S, T.card = 3 ∧ IsCliqueOrIndep r T := by
  classical
  obtain ⟨v, hv⟩ := card_pos.mp (by omega : 0 < S.card)
  set N : Finset α := (S.erase v).filter (fun u => r v u) with hN
  set M : Finset α := (S.erase v).filter (fun u => ¬ r v u) with hM
  have hsplit : N.card + M.card = S.card - 1 := by
    rw [hN, hM, card_filter_add_card_filter_not, card_erase_of_mem hv]
  have h5 : 5 ≤ N.card + M.card := by omega
  have hNsub : N ⊆ S := fun u hu => mem_of_mem_erase (mem_filter.mp hu).1
  have hMsub : M ⊆ S := fun u hu => mem_of_mem_erase (mem_filter.mp hu).1
  rcases Nat.lt_or_ge N.card 3 with hlt | hge
  · -- at least three non-neighbours of `v`
    have hM3 : 3 ≤ M.card := by omega
    obtain ⟨T, hTsub, hTcard⟩ := exists_subset_card_eq hM3
    have hTne : ∀ u ∈ T, u ≠ v ∧ ¬ r v u := by
      intro u hu
      have h1 := hTsub hu
      simp only [hM, mem_filter, mem_erase] at h1
      exact ⟨h1.1.1, h1.2⟩
    by_cases hp : ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ ¬ r x y
    · -- an independent triple together with `v`
      obtain ⟨x, hx, y, hy, hxy, hnxy⟩ := hp
      obtain ⟨hxv, hnx⟩ := hTne x hx
      obtain ⟨hyv, hny⟩ := hTne y hy
      refine ⟨{v, x, y}, ?_, ?_, Or.inr ?_⟩
      · intro u hu
        simp only [mem_insert, mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact hv
        · exact hMsub (hTsub hx)
        · exact hMsub (hTsub hy)
      · have hv' : v ∉ ({x, y} : Finset α) := by
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨hxv.symm, hyv.symm⟩
        rw [card_insert_of_notMem hv', card_pair hxy]
      · intro a ha b hb hab
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with h1 | h1 | h1 <;> rcases hb with h2 | h2 | h2
        · rw [h1, h2] at hab; exact absurd rfl hab
        · rw [h1, h2]; exact hnx
        · rw [h1, h2]; exact hny
        · rw [h1, h2]; exact fun hh => hnx (hsym x v hh)
        · rw [h1, h2] at hab; exact absurd rfl hab
        · rw [h1, h2]; exact hnxy
        · rw [h1, h2]; exact fun hh => hny (hsym y v hh)
        · rw [h1, h2]; exact fun hh => hnxy (hsym y x hh)
        · rw [h1, h2] at hab; exact absurd rfl hab
    · -- all pairs of `T` are adjacent, so `T` is a clique
      push Not at hp
      exact ⟨T, fun u hu => hMsub (hTsub hu), hTcard,
        Or.inl (fun a ha b hb hab => hp a ha b hb hab)⟩
  · -- at least three neighbours of `v`
    obtain ⟨T, hTsub, hTcard⟩ := exists_subset_card_eq hge
    have hTne : ∀ u ∈ T, u ≠ v ∧ r v u := by
      intro u hu
      have h1 := hTsub hu
      simp only [hN, mem_filter, mem_erase] at h1
      exact ⟨h1.1.1, h1.2⟩
    by_cases hp : ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ r x y
    · -- a triangle together with `v`
      obtain ⟨x, hx, y, hy, hxy, hxy'⟩ := hp
      obtain ⟨hxv, hxr⟩ := hTne x hx
      obtain ⟨hyv, hyr⟩ := hTne y hy
      refine ⟨{v, x, y}, ?_, ?_, Or.inl ?_⟩
      · intro u hu
        simp only [mem_insert, mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact hv
        · exact hNsub (hTsub hx)
        · exact hNsub (hTsub hy)
      · have hv' : v ∉ ({x, y} : Finset α) := by
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨hxv.symm, hyv.symm⟩
        rw [card_insert_of_notMem hv', card_pair hxy]
      · intro a ha b hb hab
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with h1 | h1 | h1 <;> rcases hb with h2 | h2 | h2
        · rw [h1, h2] at hab; exact absurd rfl hab
        · rw [h1, h2]; exact hxr
        · rw [h1, h2]; exact hyr
        · rw [h1, h2]; exact hsym v x hxr
        · rw [h1, h2] at hab; exact absurd rfl hab
        · rw [h1, h2]; exact hxy'
        · rw [h1, h2]; exact hsym v y hyr
        · rw [h1, h2]; exact hsym x y hxy'
        · rw [h1, h2] at hab; exact absurd rfl hab
    · -- all pairs of `T` are non-adjacent, so `T` is independent
      push Not at hp
      exact ⟨T, fun u hu => hNsub (hTsub hu), hTcard,
        Or.inr (fun a ha b hb hab => hp a ha b hb hab)⟩

/-- **The recursion `z(n) ≤ 1 + z(n-3)`**, iterated: every set of at least five
vertices can be covered by `⌊(#S - 5)/3⌋ + 3` clique-or-independent parts. -/
lemma cover_div (r : α → α → Prop) (hsym : ∀ a b, r a b → r b a) :
    ∀ n, ∀ S : Finset α, S.card = n → 5 ≤ n → CoverLe r S ((n - 5) / 3 + 3) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS h5
    rcases Nat.lt_or_ge n 8 with hlt | hge
    · -- `n = 5, 6, 7`: three parts suffice
      have hk : (n - 5) / 3 + 3 = 3 := by interval_cases n <;> norm_num
      rw [hk]
      rcases Nat.lt_or_ge n 6 with h6 | h6
      · exact cover_five r hsym (by omega)
      · obtain ⟨T, hTsub, hTcard, hTcoi⟩ := exists_homog_triple_sub r hsym (S := S) (by omega)
        have hcard' : (S \ T).card = n - 3 := by
          rw [card_sdiff_of_subset hTsub, hS, hTcard]
        obtain ⟨C, hcov, hcoi⟩ := cover_of_card_le r hsym 2 (S \ T) (by omega)
        refine ⟨Fin.cons T C, ?_, ?_⟩
        · intro u hu
          by_cases huT : u ∈ T
          · exact ⟨0, by simpa using huT⟩
          · obtain ⟨i, hi⟩ := hcov u (by simp [huT, hu])
            exact ⟨i.succ, by simpa using hi⟩
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using hTcoi
          · simpa using hcoi j
    · -- `n ≥ 8`: peel off a homogeneous triple and recurse
      obtain ⟨T, hTsub, hTcard, hTcoi⟩ := exists_homog_triple_sub r hsym (S := S) (by omega)
      have hcard' : (S \ T).card = n - 3 := by
        rw [card_sdiff_of_subset hTsub, hS, hTcard]
      have harith : (n - 3 - 5) / 3 + 3 + 1 = (n - 5) / 3 + 3 := by
        have h1 : n - 5 = (n - 8) + 3 := by omega
        have h2 : n - 3 - 5 = n - 8 := by omega
        rw [h2, h1, Nat.add_div_right _ (by norm_num : 0 < 3)]
      rw [← harith]
      obtain ⟨C, hcov, hcoi⟩ := ih (n - 3) (by omega) (S \ T) hcard' (by omega)
      refine ⟨Fin.cons T C, ?_, ?_⟩
      · intro u hu
        by_cases huT : u ∈ T
        · exact ⟨0, by simpa using huT⟩
        · obtain ⟨i, hi⟩ := hcov u (by simp [huT, hu])
          exact ⟨i.succ, by simpa using hi⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hTcoi
        · simpa using hcoi j

/-- **General upper bound**: `z(n) ≤ ⌊(n-5)/3⌋ + 3` for `n ≥ 5`. -/
theorem cochrom_le_div (r : α → α → Prop) (hsym : ∀ a b, r a b → r b a)
    (h5 : 5 ≤ Fintype.card α) :
    CochromLe r ((Fintype.card α - 5) / 3 + 3) :=
  (cochromLe_iff_coverLe).mpr (cover_div r hsym _ univ rfl h5)

/-- **General upper bound, coarse form**: `z(n) ≤ ⌊n/3⌋ + 2` for every `n`. -/
theorem cochrom_le_third (r : α → α → Prop) (hsym : ∀ a b, r a b → r b a) :
    CochromLe r (Fintype.card α / 3 + 2) := by
  rcases Nat.lt_or_ge (Fintype.card α) 5 with hlt | hge
  · refine (cochromLe_iff_coverLe).mpr (coverLe_mono (k := 2) ?_ ?_)
    · exact cover_of_card_le r hsym 2 univ (by rw [card_univ]; omega)
    · omega
  · refine (cochromLe_iff_coverLe).mpr
      (coverLe_mono (k := (Fintype.card α - 5) / 3 + 3) ?_ ?_)
    · exact (cochromLe_iff_coverLe).mp (cochrom_le_div r hsym hge)
    · omega

/-! ### Lower bounds: explicit witnesses

Each `adj n A` below is a loopless symmetric graph on `Fin n`, given by the
adjacency lists found by the exhaustive search in `probe/cochrom_bf.c` and
independently re-checked by the pruned search `zadj`.  The comment records its
cochromatic number.

`native_decide` is used here (it adds `Lean.ofReduceBool` to the axiom list);
plain `decide` needs minutes for `3^10` and hours for `3^12`.  The axiom is
recorded in `BATCH.md`.  The analogous witnesses at orders 11 and 12 were
found (`probe/cochrom_bf.c`) but their `3^11`/`3^12` enumerations were cut
from the build: `3^11` alone exceeded six minutes of `native_decide`. -/

/-- A graph on `Fin n` encoded by a single bit mask: `bm n m a b` holds iff
`a ≠ b` and bit `a * n + b` of `m` is set.  Every mask below is symmetric. -/
@[reducible] def bm (n m : ℕ) (a b : Fin n) : Prop :=
  a ≠ b ∧ Nat.testBit m (a.val * n + b.val) = true

instance (n m : ℕ) : DecidableRel (bm n m) := fun a b =>
  inferInstanceAs (Decidable (bm n m a b))

set_option maxRecDepth 100000

/-- `z = 3` on 8 vertices. -/
theorem w8_needs_three : ¬ CochromFun (bm 8 4475894029268130166) 2 := by native_decide

/-- `z = 4` on 9 vertices. -/
theorem w9_needs_four : ¬ CochromFun (bm 9 152114351730168272042550) 3 := by native_decide

/-- `z = 4` on 10 vertices. -/
theorem w10_needs_four : ¬ CochromFun (bm 10 312162554632375861681761579052) 3 := by
  native_decide

/-! ### Upper bounds at fixed orders where the recursion is tight -/

/-- Upper bound at order 9: `z ≤ 4` (the recursion `1 + z(6)` gives `1 + 3`). -/
theorem z9_upper (r : Fin 9 → Fin 9 → Prop) (hsym : ∀ a b, r a b → r b a) :
    CochromFun r 4 := by
  have h : CochromLe r ((9 - 5) / 3 + 3) := cochrom_le_div r hsym (by simp)
  rw [show (9 - 5) / 3 + 3 = 4 by norm_num] at h
  exact cover_to_fun h

/-- Upper bound at order 10: `z ≤ 4` (the recursion `1 + z(7)` gives `1 + 3`). -/
theorem z10_upper (r : Fin 10 → Fin 10 → Prop) (hsym : ∀ a b, r a b → r b a) :
    CochromFun r 4 := by
  have h : CochromLe r ((10 - 5) / 3 + 3) := cochrom_le_div r hsym (by simp)
  rw [show (10 - 5) / 3 + 3 = 4 by norm_num] at h
  exact cover_to_fun h

/-- Upper bound at order 13: `z ≤ 5`. -/
theorem z13_upper (r : Fin 13 → Fin 13 → Prop) (hsym : ∀ a b, r a b → r b a) :
    CochromFun r 5 := by
  have h : CochromLe r ((13 - 5) / 3 + 3) := cochrom_le_div r hsym (by simp)
  rw [show (13 - 5) / 3 + 3 = 5 by norm_num] at h
  exact cover_to_fun h

/-- Upper bound at order 16: `z ≤ 6`. -/
theorem z16_upper (r : Fin 16 → Fin 16 → Prop) (hsym : ∀ a b, r a b → r b a) :
    CochromFun r 6 := by
  have h : CochromLe r ((16 - 5) / 3 + 3) := cochrom_le_div r hsym (by simp)
  rw [show (16 - 5) / 3 + 3 = 6 by norm_num] at h
  exact cover_to_fun h

/-- The two-sided results at orders 9 and 10. -/
theorem z9_exact :
    (∀ (r : Fin 9 → Fin 9 → Prop), (∀ a b, r a b → r b a) → CochromFun r 4) ∧
    ¬ CochromFun (bm 9 152114351730168272042550) 3 :=
  ⟨z9_upper, w9_needs_four⟩

/-- The two-sided result at order 10. -/
theorem z10_exact :
    (∀ (r : Fin 10 → Fin 10 → Prop), (∀ a b, r a b → r b a) → CochromFun r 4) ∧
    ¬ CochromFun (bm 10 312162554632375861681761579052) 3 :=
  ⟨z10_upper, w10_needs_four⟩

/-! ### The table for small orders -/

theorem z_one : (∀ (r : Fin 1 → Fin 1 → Prop) [DecidableRel r],
    (∀ a b, r a b → r b a) → CochromFun r 1) ∧
    ¬ CochromFun (fun (_ : Fin 1) (_ : Fin 1) => False) 0 := by
  refine ⟨fun r _ hsym => cover_to_fun (cochrom_le_half r hsym 1 (by decide)), ?_⟩
  unfold CochromFun IsCliqueOrIndep
  decide

/-- The complete graph on two vertices. -/
def k2 : Fin 2 → Fin 2 → Prop := fun a b => a ≠ b

instance k2_dec : DecidableRel k2 := fun a b => inferInstanceAs (Decidable (a ≠ b))

theorem z_two : (∀ (r : Fin 2 → Fin 2 → Prop) [DecidableRel r],
    (∀ a b, r a b → r b a) → CochromFun r 1) ∧ ¬ CochromFun k2 0 :=
  ⟨fun r _ hsym => cover_to_fun (cochrom_le_half r hsym 1 (by decide)), by
    unfold CochromFun IsCliqueOrIndep
    decide⟩

theorem z_three : (∀ (r : Fin 3 → Fin 3 → Prop) [DecidableRel r],
    (∀ a b, r a b → r b a) → CochromFun r 2) ∧ ¬ CochromFun p3 1 :=
  ⟨fun r _ hsym => cover_to_fun (cochrom_le_half r hsym 2 (by decide)), p3_needs_two⟩

theorem z_four : (∀ (r : Fin 4 → Fin 4 → Prop) [DecidableRel r],
    (∀ a b, r a b → r b a) → CochromFun r 2) ∧ ¬ CochromFun p4 1 :=
  ⟨fun r _ hsym => cover_to_fun (cochrom_le_half r hsym 2 (by decide)), p4_needs_two⟩

theorem z_six : (∀ (r : Fin 6 → Fin 6 → Prop) [DecidableRel r],
    (∀ a b, r a b → r b a) → CochromFun r 3) ∧ ¬ CochromFun c5k1 2 :=
  ⟨fun r _ hsym => cover_to_fun (cochrom_le_half r hsym 3 (by decide)), c5k1_needs_three⟩

theorem z_seven : (∀ (r : Fin 7 → Fin 7 → Prop) [DecidableRel r],
    (∀ a b, r a b → r b a) → CochromFun r 3) ∧ ¬ CochromFun c5k2 2 :=
  ⟨fun r _ hsym => cover_to_fun (cochrom_le_three_of_seven r hsym rfl), c5k2_needs_three⟩

/-- **JSP-000622, small orders**: `z(1) = z(2) = 1`, `z(3) = z(4) = 2`,
`z(5) = z(6) = z(7) = 3`, together with the general bound `z(n) ≤ ⌈n/2⌉`
for every order. -/
theorem answer_general :
    (∀ (k : ℕ) (r : Fin (2 * k) → Fin (2 * k) → Prop) [DecidableRel r],
        (∀ a b, r a b → r b a) → CochromFun r k) ∧
      (∀ (r : Fin 3 → Fin 3 → Prop) [DecidableRel r],
        (∀ a b, r a b → r b a) → CochromFun r 2) ∧
      (∀ (r : Fin 4 → Fin 4 → Prop) [DecidableRel r],
        (∀ a b, r a b → r b a) → CochromFun r 2) ∧
      (∀ (r : Fin 6 → Fin 6 → Prop) [DecidableRel r],
        (∀ a b, r a b → r b a) → CochromFun r 3) ∧
      (∀ (r : Fin 7 → Fin 7 → Prop) [DecidableRel r],
        (∀ a b, r a b → r b a) → CochromFun r 3) ∧
      ¬ CochromFun p3 1 ∧ ¬ CochromFun p4 1 ∧ ¬ CochromFun c5 2 ∧
      ¬ CochromFun c5k1 2 ∧ ¬ CochromFun c5k2 2 := by
  exact ⟨fun k r _ hsym => cover_to_fun (cochrom_le_half r hsym k (by simp)),
    z_three.1, z_four.1, z_six.1, z_seven.1,
    z_three.2, z_four.2, c5_needs_three, c5k1_needs_three, c5k2_needs_three⟩

end JSP622
