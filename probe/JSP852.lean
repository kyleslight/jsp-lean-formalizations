/-
# JSP-000852 probe

Problem (catalog `problems/catalog-0801-0900.md#JSP-000852`):

  How large an independent set is guaranteed in a three-uniform hypergraph
  whose edges intersect pairwise in at most one vertex?

Setting: `H` is a family of 3-element subsets of an `n`-element vertex set,
and any two distinct edges meet in at most one vertex ("linear" 3-graph, e.g.
a Steiner triple system).

Answer (PhRo86): the guaranteed independent set has size `Theta(sqrt (n log n))`
— there are Steiner triple systems whose independence number is `O(sqrt (n log n))`,
while every such hypergraph has an independent set of size `Omega(sqrt n)`.

This file formalizes the *lower-bound side*: every linear 3-uniform hypergraph
on `n` vertices has an independent set `I` with

  `2 * n <= #I * (#I + 1)`,

i.e. `#I >= sqrt (2 n)`.  The proof is the standard maximal-independent-set
count: for a maximal independent set `I` and `v ∉ I`, some edge `{v, x, y}`
has `x, y ∈ I`; distinct `v` give distinct pairs `{x, y}` (linearity), so
`n - #I <= Nat.choose #I 2`.

The matching upper bound (a Steiner triple system with independence number
`O(sqrt (n log n))`) is not formalized here.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Finset

namespace JSP852

variable {α : Type} [Fintype α] [DecidableEq α]

/-- `I` is independent: it contains no edge in full. -/
@[reducible] def Indep (H : Finset (Finset α)) (I : Finset α) : Prop :=
  ∀ e ∈ H, ¬ e ⊆ I

/-- The hypergraph is linear: distinct edges meet in at most one vertex. -/
def Linear (H : Finset (Finset α)) : Prop :=
  ∀ e ∈ H, ∀ e' ∈ H, e ≠ e' → (e ∩ e').card ≤ 1

/-- The hypergraph is 3-uniform. -/
def ThreeUniform (H : Finset (Finset α)) : Prop :=
  ∀ e ∈ H, e.card = 3

/-- **JSP-000852, lower bound.**  Every linear 3-uniform hypergraph on `n`
vertices has an independent set `I` with `2 * n ≤ #I * (#I + 1)`, i.e.
`#I ≥ sqrt (2 n)`. -/
theorem exists_indep (H : Finset (Finset α)) (h3 : ThreeUniform H) (hlin : Linear H) :
    ∃ I : Finset α, Indep H I ∧ 2 * Fintype.card α ≤ I.card * (I.card + 1) := by
  classical
  set fam : Finset (Finset α) := (univ : Finset α).powerset.filter (fun I => Indep H I)
    with hfam
  have hfamne : fam.Nonempty := ⟨∅, by
    rw [hfam]
    refine mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), ?_⟩
    intro e he hsub
    have h := h3 e he
    have he0 : e = ∅ := by simpa using hsub
    rw [he0] at h
    simp at h⟩
  obtain ⟨I, hIfam, hImax⟩ := exists_max_image fam (fun s => s.card) hfamne
  have hIndep : Indep H I := (mem_filter.mp hIfam).2
  have hIsub : I ⊆ univ := (mem_powerset.mp (mem_filter.mp hIfam).1)
  -- maximality: adding a vertex outside `I` destroys independence
  have hstep : ∀ v, v ∉ I → ∃ e ∈ H, v ∈ e ∧ e ⊆ insert v I := by
    intro v hv
    by_contra hcon
    push_neg at hcon
    have hIndep' : Indep H (insert v I) := by
      intro e he hsub
      by_cases hI : e ⊆ I
      · exact hIndep e he hI
      · obtain ⟨x, hxe, hxI⟩ := Finset.not_subset.mp hI
        have hxins : x ∈ insert v I := hsub hxe
        have hxv : x = v := by
          rcases mem_insert.mp hxins with rfl | hxin
          · rfl
          · exact absurd hxin hxI
        exact hcon e he (hxv ▸ hxe) hsub
    have hmem : insert v I ∈ fam := by
      rw [hfam]
      exact mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hIndep'⟩
    have hcard := hImax (insert v I) hmem
    rw [card_insert_of_notMem hv] at hcard
    omega
  -- the injection `v ↦ e_v \ {v}` into the 2-subsets of `I`
  set e : α → Finset α :=
    fun v => if h : v ∉ I then Classical.choose (hstep v h) else ∅ with he
  have heprop : ∀ v (hv : v ∉ I), e v ∈ H ∧ v ∈ e v ∧ e v ⊆ insert v I := by
    intro v hv
    rw [he]
    simp only [dif_pos hv]
    exact Classical.choose_spec (hstep v hv)
  set φ : α → Finset α := fun v => e v \ {v} with hφ
  have hφsub : ∀ v (hv : v ∉ I), φ v ⊆ I := by
    intro v hv x hx
    have hsub := (heprop v hv).2.2
    have hxe : x ∈ e v := (mem_sdiff.mp hx).1
    have hxins := hsub hxe
    have hxne : x ≠ v := by simpa using (mem_sdiff.mp hx).2
    rcases mem_insert.mp hxins with rfl | hxin
    · exact absurd rfl hxne
    · exact hxin
  have hφcard : ∀ v (hv : v ∉ I), (φ v).card = 2 := by
    intro v hv
    have hve : v ∈ e v := (heprop v hv).2.1
    have h3e : (e v).card = 3 := h3 (e v) (heprop v hv).1
    rw [hφ, card_sdiff_of_subset (by
      intro x hx
      rw [mem_singleton] at hx
      exact hx ▸ hve), h3e]
    rfl
  have hφinj : ∀ v (hv : v ∉ I) w (hw : w ∉ I), φ v = φ w → v = w := by
    intro v hv w hw heq
    by_contra hne
    have hve : v ∈ e v := (heprop v hv).2.1
    have hwe : w ∈ e w := (heprop w hw).2.1
    have hwv : v ∉ e w := by
      intro hmem
      have := (heprop w hw).2.2 hmem
      rcases mem_insert.mp this with rfl | hxin
      · exact hne rfl
      · exact hv hxin
    have hne' : e v ≠ e w := by
      intro h
      exact hwv (h ▸ hve)
    -- both `e v` and `e w` contain the 2-element set `φ v = φ w`
    have hsub : φ v ⊆ e v ∩ e w := by
      intro x hx
      refine mem_inter.mpr ⟨(mem_sdiff.mp hx).1, ?_⟩
      have hxw : x ∈ φ w := heq ▸ hx
      exact (mem_sdiff.mp hxw).1
    have hle : (φ v).card ≤ (e v ∩ e w).card := card_le_card hsub
    rw [hφcard v hv] at hle
    have := hlin (e v) (heprop v hv).1 (e w) (heprop w hw).1 hne'
    omega
  -- count: `univ \ I` injects into the 2-subsets of `I`
  have himg : (univ \ I).image φ ⊆ I.powersetCard 2 := by
    intro P hP
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hP
    have hvI : v ∉ I := (mem_sdiff.mp hv).2
    exact mem_powersetCard.mpr ⟨hφsub v hvI, hφcard v hvI⟩
  have hcard1 : ((univ \ I).image φ).card = (univ \ I).card := by
    rw [card_image_iff]
    intro v hv w hw heq
    exact hφinj v (mem_sdiff.mp hv).2 w (mem_sdiff.mp hw).2 heq
  have hcount : (univ \ I).card ≤ Nat.choose I.card 2 := by
    calc (univ \ I).card = ((univ \ I).image φ).card := hcard1.symm
      _ ≤ (I.powersetCard 2).card := card_le_card himg
      _ = Nat.choose I.card 2 := card_powersetCard 2 I
  have hcard2 : (univ \ I).card = Fintype.card α - I.card := by
    rw [card_sdiff_of_subset hIsub, card_univ]
  rw [hcard2] at hcount
  -- arithmetic: `2 n ≤ #I (#I + 1)`
  have hchoose : Nat.choose I.card 2 = I.card * (I.card - 1) / 2 := Nat.choose_two_right _
  have hle2 : 2 * Nat.choose I.card 2 ≤ I.card * (I.card - 1) := by
    rw [hchoose]
    exact Nat.mul_div_le (I.card * (I.card - 1)) 2
  have hIle : I.card ≤ Fintype.card α := by
    rw [← card_univ]; exact card_le_card hIsub
  have hkey : I.card * (I.card - 1) + 2 * I.card = I.card * (I.card + 1) := by
    rcases Nat.eq_zero_or_pos I.card with h0 | hpos
    · rw [h0]
    · have h1 : I.card * (I.card - 1) = I.card * I.card - I.card := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      have h3 : I.card * (I.card + 1) = I.card * I.card + I.card := Nat.mul_succ I.card I.card
      have hle : I.card ≤ I.card * I.card := Nat.le_mul_of_pos_left I.card hpos
      rw [h1, h3]
      omega
  have step1 : 2 * (Fintype.card α - I.card) ≤ I.card * (I.card - 1) :=
    (Nat.mul_le_mul_left 2 hcount).trans hle2
  have step2 : 2 * Fintype.card α = 2 * (Fintype.card α - I.card) + 2 * I.card := by omega
  refine ⟨I, hIndep, ?_⟩
  calc 2 * Fintype.card α = 2 * (Fintype.card α - I.card) + 2 * I.card := step2
    _ ≤ I.card * (I.card - 1) + 2 * I.card := Nat.add_le_add_right step1 _
    _ = I.card * (I.card + 1) := hkey

end JSP852
