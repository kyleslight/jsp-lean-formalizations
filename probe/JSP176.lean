/-
# JSP-000176 probe (prescribed degree 2)

Problem (catalog `problems/catalog-0101-0200.md#JSP-000176`):

  How many edges can a graph have if it contains no regular subgraph of a
  prescribed degree?

The famous instance is degree 3 (the Erdős–Sauer problem).  This file treats
the instance **degree 2**, where the answer is exact and elementary:

  a graph with no 2-regular subgraph has at most `n - 1` edges,
  and `n - 1` is attained (a tree).

Reason: a 2-regular subgraph is a disjoint union of cycles, so "no 2-regular
subgraph" is the same as "acyclic", i.e. a forest; a forest on `n` vertices
has at most `n - 1` edges.

Because Mathlib-style raw relations are used here (no `SimpleGraph`), the
acyclicity hypothesis is phrased in the equivalent *minimum-degree* form: every
nonempty vertex subset spans a vertex of degree at most 1.  (A finite graph
with minimum degree at least 2 contains a cycle; conversely a forest has such a
vertex in every induced subgraph.)  The equivalence itself is standard and is
not formalized here; the counting statement is proved in full.

Main results:
* `sum_deg_le` — the degree sum over a vertex set satisfying the hypothesis is
  at most `2 * (#S - 1)`;
* `edges_le` — hence at most `n - 1` edges;
* `path_attained` — the path on 4 vertices has exactly `4 - 1 = 3` edges and
  satisfies the hypothesis (the extremal value is attained; `P_n` attains it
  for every `n`, this is checked here at `n = 4`).
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Finset

namespace JSP176

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Degree of `v` inside the vertex set `S`. -/
@[reducible] def degIn (r : α → α → Prop) [DecidableRel r] (S : Finset α) (v : α) : ℕ :=
  (S.filter (fun u => r v u)).card

/-- The degree sum over `S`. -/
def degSum (r : α → α → Prop) [DecidableRel r] (S : Finset α) : ℕ :=
  ∑ v ∈ S, degIn r S v

/-- **Degree-sum bound**: if every nonempty subset of `S` spans a vertex of
degree at most 1, then the degree sum over `S` is at most `2 * (#S - 1)`. -/
theorem sum_deg_le (r : α → α → Prop) [DecidableRel r]
    (hirr : ∀ a, ¬ r a a) (hsym : ∀ a b, r a b → r b a) :
    ∀ n, ∀ S : Finset α, S.card = n →
      (∀ T ⊆ S, T.Nonempty → ∃ v ∈ T, degIn r T v ≤ 1) → degSum r S ≤ 2 * (S.card - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS hmin
    rcases S.eq_empty_or_nonempty with hempty | hne
    · subst hempty
      simp [degSum]
    · obtain ⟨v, hvS, hvdeg⟩ := hmin S (subset_refl S) hne
      set T := S.erase v with hT
      have hvT : v ∉ T := by simp [hT]
      have hTsub : T ⊆ S := erase_subset _ _
      have hSins : S = insert v T := (insert_erase hvS).symm
      have hTcard : T.card = n - 1 := by
        rw [hT, card_erase_of_mem hvS, hS]
      have hnpos : 1 ≤ n := by
        have := S.card_pos.mpr hne
        omega
      have ihT : degSum r T ≤ 2 * (T.card - 1) :=
        ih T.card (by omega) T rfl
          (fun U hU hUne => hmin U (Subset.trans hU hTsub) hUne)
      -- split the degree sum
      have hsplit : degSum r S = (∑ w ∈ T, degIn r S w) + degIn r S v := by
        rw [degSum, hSins, sum_insert hvT, add_comm]
      -- each `w ∈ T` gains at most one from `v`
      have hstep : ∀ w ∈ T, degIn r S w = degIn r T w + (if r w v then 1 else 0) := by
        intro w hw
        have hwv : w ≠ v := by intro h; rw [h] at hw; exact hvT hw
        unfold degIn
        rw [hSins, filter_insert]
        by_cases h : r w v
        · rw [if_pos h, if_pos h]
          rw [card_insert_of_notMem (by
            simp only [mem_filter, not_and]
            intro hv hh
            exact hvT hv)]
        · rw [if_neg h, if_neg h]
          simp
      have hstep2 : (∑ w ∈ T, degIn r S w) =
          (∑ w ∈ T, degIn r T w) + ∑ w ∈ T, (if r w v then 1 else 0) := by
        rw [← sum_add_distrib]
        exact sum_congr rfl hstep
      -- the `v`-neighbours inside `S` are exactly those inside `T`
      have hself : degIn r S v = degIn r T v := by
        unfold degIn
        rw [hSins, filter_insert, if_neg (hirr v)]
      have hcount : (∑ w ∈ T, (if r w v then 1 else 0)) = degIn r S v := by
        have h1 : (∑ w ∈ T, (if r w v then 1 else 0)) = (T.filter (fun w => r w v)).card := by
          rw [card_eq_sum_ones, sum_filter]
        have h2 : degIn r S v = (T.filter (fun w => r v w)).card := by
          unfold degIn
          rw [hSins, filter_insert, if_neg (hirr v)]
        rw [h1, h2]
        congr 1
        exact filter_congr (fun w _ => ⟨fun h => hsym w v h, fun h => hsym v w h⟩)
      by_cases hT0 : T.card = 0
      · -- `S` is a single vertex, so the degree sum is `0`
        have hScard : S.card = T.card + 1 := by rw [hSins, card_insert_of_notMem hvT]
        have hTempty : T = ∅ := card_eq_zero.mp hT0
        have hdeg : degSum r S = 0 := by
          rw [degSum, hSins, hTempty]
          simp [degIn, hirr]
        rw [hdeg, hScard, hT0]
      · -- `T` is nonempty
        have hpos : 1 ≤ T.card := by omega
        calc degSum r S = (∑ w ∈ T, degIn r S w) + degIn r S v := hsplit
          _ = ((∑ w ∈ T, degIn r T w) + degIn r S v) + degIn r S v := by
                rw [hstep2, hcount]
          _ = degSum r T + 2 * degIn r S v := by
                rw [degSum]; ring
          _ ≤ 2 * (T.card - 1) + 2 := by
                have h1 := ihT; have h2 := hvdeg
                calc degSum r T + 2 * degIn r S v
                    ≤ 2 * (T.card - 1) + 2 * degIn r S v := Nat.add_le_add_right h1 _
                  _ ≤ 2 * (T.card - 1) + 2 * 1 := Nat.add_le_add_left (Nat.mul_le_mul_left 2 h2) _
                  _ = 2 * (T.card - 1) + 2 := by norm_num
          _ = 2 * (S.card - 1) := by
                have hScard : S.card = T.card + 1 := by rw [hSins, card_insert_of_notMem hvT]
                rw [hScard]
                omega

/-- The number of edges, i.e. half of the total degree sum. -/
def edgeCount (r : α → α → Prop) [DecidableRel r] : ℕ :=
  degSum r univ / 2

/-- **JSP-000176 (degree 2), upper bound**: a graph in which every nonempty
vertex subset spans a vertex of degree at most 1 has at most `n - 1` edges. -/
theorem edges_le (r : α → α → Prop) [DecidableRel r]
    (hirr : ∀ a, ¬ r a a) (hsym : ∀ a b, r a b → r b a)
    (hmin : ∀ T : Finset α, T.Nonempty → ∃ v ∈ T, degIn r T v ≤ 1) :
    edgeCount r ≤ Fintype.card α - 1 := by
  have h := sum_deg_le r hirr hsym (Fintype.card α) univ rfl
    (fun T _ hT => hmin T hT)
  rw [card_univ] at h
  unfold edgeCount
  omega

/-! ## Attainment: the path on 4 vertices has `4 - 1 = 3` edges -/

/-- The path on `n` vertices. -/
def pathRel (n : ℕ) : Fin n → Fin n → Prop :=
  fun a b => b.val = a.val + 1 ∨ a.val = b.val + 1

instance pathRel_dec (n : ℕ) : DecidableRel (pathRel n) := fun a b =>
  inferInstanceAs (Decidable (b.val = a.val + 1 ∨ a.val = b.val + 1))

/-- The path on 4 vertices has exactly `4 - 1 = 3` edges and satisfies the
minimum-degree hypothesis, so the bound `n - 1` is attained. -/
theorem path_attained :
    edgeCount (pathRel 4) = 4 - 1 ∧
      (∀ T : Finset (Fin 4), T.Nonempty →
        ∃ v ∈ T, (T.filter (fun u => pathRel 4 v u)).card ≤ 1) := by
  constructor
  · decide
  · intro T _
    revert T
    decide

/-- The answer to JSP-000176 (prescribed degree 2), packaged. -/
theorem answer (r : α → α → Prop) [DecidableRel r]
    (hirr : ∀ a, ¬ r a a) (hsym : ∀ a b, r a b → r b a)
    (hmin : ∀ T : Finset α, T.Nonempty → ∃ v ∈ T, degIn r T v ≤ 1) :
    edgeCount r ≤ Fintype.card α - 1 :=
  edges_le r hirr hsym hmin

end JSP176
