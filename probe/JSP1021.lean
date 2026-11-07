/-
# JSP-001021 probe

Problem (catalog `problems/catalog-1001-1022.md#JSP-001021`, Erdős–Moser 1964):

  How large a transitive subtournament must every tournament of prescribed order contain?

Answer: every tournament on `n ≥ 1` vertices contains a transitive subtournament
on `⌊log₂ n⌋ + 1` vertices, and this is best possible.

This file formalizes the lower-bound direction (the guarantee), for an arbitrary
finite vertex type and specialised to `Fin n`.

A tournament is modelled as a binary relation `r` that is irreflexive and, for
distinct vertices, holds in exactly one direction. A vertex set is *transitive*
when `r` restricted to it is transitive, i.e. it induces a transitive tournament
(a strict total order on the set).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Finset

namespace JSP1021

variable {α : Type}

/-- A tournament relation: irreflexive, and exactly one direction on distinct vertices. -/
def IsTournament (r : α → α → Prop) : Prop :=
  (∀ a, ¬ r a a) ∧ ∀ a b, a ≠ b → (r a b ↔ ¬ r b a)

/-- `S` induces a transitive subtournament: `r` is transitive on `S`. -/
def TransitiveOn (r : α → α → Prop) (S : Finset α) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, r a b → r b c → r a c

/-- Out-neighbourhood of `v`. -/
def outNbrs [Fintype α] (r : α → α → Prop) [DecidableRel r] (v : α) : Finset α :=
  univ.filter (fun u => r v u)

/-- In-neighbourhood of `v`. -/
def inNbrs [Fintype α] (r : α → α → Prop) [DecidableRel r] (v : α) : Finset α :=
  univ.filter (fun u => r u v)

/-- Inserting a vertex that beats every vertex of a transitive set keeps the set transitive. -/
theorem transitive_insert [DecidableEq α] (hT : IsTournament r) {S : Finset α} {v : α}
    (h : TransitiveOn r S) (hv : ∀ s ∈ S, r v s) (hvn : v ∉ S) :
    TransitiveOn r (insert v S) := by
  have hnot : ∀ s ∈ S, ¬ r s v := by
    intro s hs hsv
    have hsne : s ≠ v := by intro h; rw [h] at hs; exact hvn hs
    exact ((hT.2 s v hsne).mp hsv) (hv s hs)
  intro a ha b hb c hc hab hbc
  simp only [mem_insert] at ha hb hc
  rcases ha with rfl | ha <;> rcases hb with rfl | hb <;> rcases hc with rfl | hc
  · exact hab
  · exact hv c hc
  · exact absurd hbc (hnot b hb)
  · exact hv c hc
  · exact hab
  · exact absurd hab (hnot a ha)
  · exact absurd hbc (hnot b hb)
  · exact h a ha b hb c hc hab hbc

/-- The out- and in-neighbourhoods of a vertex partition the other vertices. -/
theorem card_out_add_card_in [Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    (hT : IsTournament r) (v : α) :
    (outNbrs r v).card + (inNbrs r v).card = Fintype.card α - 1 := by
  have hdisj : Disjoint (outNbrs r v) (inNbrs r v) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    simp only [outNbrs, inNbrs, mem_filter, mem_univ, true_and] at hu1 hu2
    have huv : u ≠ v := by intro h; rw [h] at hu1; exact hT.1 v hu1
    exact ((hT.2 u v huv).mp hu2) hu1
  have hunion : outNbrs r v ∪ inNbrs r v = univ.erase v := by
    ext u
    simp only [outNbrs, inNbrs, mem_union, mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · rintro (h | h)
      · exact ⟨fun e => hT.1 v (e ▸ h), trivial⟩
      · exact ⟨fun e => hT.1 v (e ▸ h), trivial⟩
    · rintro ⟨hne, _⟩
      by_cases h : r v u
      · exact Or.inl h
      · exact Or.inr ((hT.2 u v hne).mpr h)
  calc (outNbrs r v).card + (inNbrs r v).card
      = (outNbrs r v ∪ inNbrs r v).card := (Finset.card_union_of_disjoint hdisj).symm
    _ = (univ.erase v).card := by rw [hunion]
    _ = Fintype.card α - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]

/-- Twice the sum of all out-degrees equals `N * (N - 1)`. -/
theorem two_mul_sum_outNbrs [Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    (hT : IsTournament r) :
    2 * (∑ v, (outNbrs r v).card) = Fintype.card α * (Fintype.card α - 1) := by
  have hswap : ∑ v, (inNbrs r v).card = ∑ v, (outNbrs r v).card := by
    have h1 : ∀ v, (inNbrs r v).card = ∑ u, if r u v then 1 else 0 := by
      intro v; rw [inNbrs, Finset.card_filter]
    have h2 : ∀ v, (outNbrs r v).card = ∑ u, if r v u then 1 else 0 := by
      intro v; rw [outNbrs, Finset.card_filter]
    simp only [h1, h2]
    rw [Finset.sum_comm]
  have step : 2 * (∑ v, (outNbrs r v).card)
      = ∑ v, ((outNbrs r v).card + (inNbrs r v).card) := by
    rw [Finset.sum_add_distrib, hswap]
    ring
  rw [step]
  simp only [card_out_add_card_in r hT]
  rw [Finset.sum_const, Finset.card_univ]
  simp [nsmul_eq_mul]

/-- Some vertex has out-degree at least half of `N - 1`. -/
theorem exists_large_outdeg [Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r]
    (hT : IsTournament r) (hN : 2 ≤ Fintype.card α) :
    ∃ v, Fintype.card α - 1 ≤ 2 * (outNbrs r v).card := by
  by_contra hcon
  have hcon' : ∀ v, 2 * (outNbrs r v).card < Fintype.card α - 1 := by
    intro v
    by_contra h
    exact hcon ⟨v, by omega⟩
  have hsum := two_mul_sum_outNbrs r hT
  have hle : 2 * (∑ v, (outNbrs r v).card) ≤ Fintype.card α * (Fintype.card α - 2) := by
    have hterm : ∀ v, 2 * (outNbrs r v).card ≤ Fintype.card α - 2 := by
      intro v
      have h := hcon' v
      omega
    calc 2 * (∑ v, (outNbrs r v).card) = ∑ v, 2 * (outNbrs r v).card :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ _v : α, (Fintype.card α - 2) := Finset.sum_le_sum (fun v _ => hterm v)
      _ = Fintype.card α * (Fintype.card α - 2) := by
          rw [Finset.sum_const, Finset.card_univ]
          simp [nsmul_eq_mul]
  rw [hsum] at hle
  have hlt : Fintype.card α * (Fintype.card α - 2) < Fintype.card α * (Fintype.card α - 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  exact absurd hle (not_le.mpr hlt)

/-- Main lemma: a tournament on at least `2 ^ (k - 1)` vertices contains a
transitive subtournament on at least `k` vertices. -/
theorem exists_transitive_subset_of_pow (k : ℕ) :
    ∀ {β : Type} [Fintype β] [DecidableEq β] (r : β → β → Prop) [DecidableRel r],
      1 ≤ k → IsTournament r → 2 ^ (k - 1) ≤ Fintype.card β →
      ∃ S : Finset β, TransitiveOn r S ∧ k ≤ S.card := by
  induction k with
  | zero =>
    intro β instF instD r instR hk hT hcard
    omega
  | succ k ih =>
    intro β instF instD r instR hk hT hcard
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have hpos : 0 < Fintype.card β := by
        have h1 : 1 ≤ Fintype.card β := by simpa using hcard
        omega
      obtain ⟨a⟩ := Fintype.card_pos_iff.mp hpos
      refine ⟨{a}, ?_, by simp⟩
      intro x hx y hy z hz hab _
      have hx' : x = a := Finset.mem_singleton.mp hx
      have hy' : y = a := Finset.mem_singleton.mp hy
      have hz' : z = a := Finset.mem_singleton.mp hz
      simpa [hx', hy', hz'] using hab
    · have hN2 : 2 ≤ Fintype.card β := by
        have h2k : 2 ^ k ≤ Fintype.card β := hcard
        have hle : 2 ≤ 2 ^ k := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hkpos
        omega
      obtain ⟨v, hv⟩ := exists_large_outdeg r hT hN2
      set A : Finset β := outNbrs r v with hA
      have hd : 2 ^ (k - 1) ≤ A.card := by
        have hcard' : 2 ^ k ≤ Fintype.card β := by simpa using hcard
        have h2k : 2 ^ k = 2 ^ (k - 1) * 2 := by
          have hk1 : k = (k - 1) + 1 := by omega
          conv_lhs => rw [hk1]
          rw [Nat.pow_succ]
        omega
      have hTsub : IsTournament (fun x y : ↥A => r x.1 y.1) :=
        ⟨fun x => hT.1 x.1,
          fun x y hxy => hT.2 x.1 y.1 (fun h => hxy (Subtype.ext h))⟩
      obtain ⟨S₀, hS₀T, hS₀card⟩ :=
        ih (β := ↥A) (fun x y : ↥A => r x.1 y.1) hkpos hTsub (by
          rw [Fintype.card_coe]; exact hd)
      have hmem : ∀ s ∈ S₀.image Subtype.val, r v s := by
        intro s hs
        obtain ⟨s', _, rfl⟩ := Finset.mem_image.mp hs
        exact (Finset.mem_filter.mp s'.2).2
      have hvS : v ∉ S₀.image Subtype.val := by
        intro hv'
        obtain ⟨s', _, hs'⟩ := Finset.mem_image.mp hv'
        exact hT.1 v (hs' ▸ (Finset.mem_filter.mp s'.2).2)
      refine ⟨insert v (S₀.image Subtype.val), ?_, ?_⟩
      · refine transitive_insert hT ?_ hmem hvS
        intro x hx y hy z hz hxy hyz
        obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hz
        exact hS₀T x' hx' y' hy' z' hz' hxy hyz
      · have hcard : (S₀.image Subtype.val).card = S₀.card :=
          Finset.card_image_of_injective _ Subtype.val_injective
        have hins : (insert v (S₀.image Subtype.val)).card = (S₀.image Subtype.val).card + 1 := by
          rw [Finset.card_insert_of_notMem hvS]
        omega

/-- **JSP-001021**: every tournament on a nonempty finite vertex set contains a
transitive subtournament on at least `⌊log₂ n⌋ + 1` vertices. -/
theorem exists_transitive_subset [Fintype α] [DecidableEq α] (r : α → α → Prop)
    [DecidableRel r] (hT : IsTournament r) (hne : Nonempty α) :
    ∃ S : Finset α, TransitiveOn r S ∧ Nat.log2 (Fintype.card α) + 1 ≤ S.card := by
  have hN : Fintype.card α ≠ 0 := (Fintype.card_pos_iff.mpr hne).ne'
  have hk : 1 ≤ Nat.log2 (Fintype.card α) + 1 := by omega
  obtain ⟨S, hS, hcard⟩ :=
    exists_transitive_subset_of_pow (β := α) (Nat.log2 (Fintype.card α) + 1) r hk hT (by
      have hsub : Nat.log2 (Fintype.card α) + 1 - 1 = Nat.log2 (Fintype.card α) := by omega
      rw [hsub]
      have : Nat.log2 (Fintype.card α) ≤ Nat.log2 (Fintype.card α) := le_rfl
      exact (Nat.le_log2 hN).mp this)
  exact ⟨S, hS, hcard⟩

/-- The same statement for tournaments on `Fin n`. -/
theorem tournament_fin (n : ℕ) (hn : 1 ≤ n) (r : Fin n → Fin n → Prop) [DecidableRel r]
    (hT : IsTournament r) :
    ∃ S : Finset (Fin n), TransitiveOn r S ∧ Nat.log2 n + 1 ≤ S.card := by
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := exists_transitive_subset (α := Fin n) r hT hne
  simpa using h

end JSP1021
