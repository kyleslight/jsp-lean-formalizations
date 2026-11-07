/-
JSP-001058 — Hilbert's sixteenth problem: uniform bounds for planar limit cycles.

Statement of Theorem 1.1 of the OpenAI preprint "Uniform bounds for planar polynomial
limit cycles" (2026-09-24), plus one fully proved instance (degree 0).
-/
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Topology.Basic
import Mathlib.Data.Set.Card

namespace JSP1058

open MvPolynomial Set

/-- A real planar polynomial vector field of degree at most `d`. -/
structure PolyField (d : ℕ) where
  P : MvPolynomial (Fin 2) ℝ
  Q : MvPolynomial (Fin 2) ℝ
  hP : P.totalDegree ≤ d
  hQ : Q.totalDegree ≤ d

/-- The vector field as a function on the plane. -/
noncomputable def PolyField.toFun {d : ℕ} (V : PolyField d) : ℝ × ℝ → ℝ × ℝ :=
  fun z => (MvPolynomial.eval ![z.1, z.2] V.P, MvPolynomial.eval ![z.1, z.2] V.Q)

/-- A nonconstant periodic integral curve of `V`. -/
def IsPeriodicOrbit {d : ℕ} (V : PolyField d) (γ : ℝ → ℝ × ℝ) : Prop :=
  ∃ T : ℝ, 0 < T ∧ IsIntegralCurve γ (fun _ => V.toFun) ∧
    (∀ t : ℝ, γ (t + T) = γ t) ∧ ¬ ∃ c : ℝ × ℝ, ∀ t : ℝ, γ t = c

/-- The *image* of a periodic orbit, counted once without multiplicity. -/
def OrbitImage {d : ℕ} (V : PolyField d) : Set (Set (ℝ × ℝ)) :=
  {S | ∃ γ : ℝ → ℝ × ℝ, IsPeriodicOrbit V γ ∧ S = Set.range γ}

/-- A limit cycle: a periodic orbit image with an open neighbourhood containing no
other periodic orbit image. -/
def IsLimitCycleImage {d : ℕ} (V : PolyField d) (S : Set (ℝ × ℝ)) : Prop :=
  S ∈ OrbitImage V ∧
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ S ⊆ U ∧
      ∀ S' ∈ OrbitImage V, S' ⊆ U → S' = S

/-- The set of limit-cycle images of `V`. -/
def LimitCycles {d : ℕ} (V : PolyField d) : Set (Set (ℝ × ℝ)) :=
  {S | IsLimitCycleImage V S}

/-- Theorem 1.1: for every degree `d` there is a finite `B d` bounding the number of
limit cycles of every real planar polynomial vector field of degree at most `d`. -/
def UniformBound : Prop :=
  ∀ d : ℕ, ∃ B : ℕ, ∀ V : PolyField d, (LimitCycles V).encard ≤ (B : ℕ∞)

/-! ### The degree-zero instance -/

/-- A degree-zero field is constant, so it has no nonconstant periodic integral curve. -/
theorem no_periodicOrbit_zero (V : PolyField 0) (γ : ℝ → ℝ × ℝ) :
    ¬ IsPeriodicOrbit V γ := by
  rintro ⟨T, hT, hInt, hper, hnon⟩
  have hP : V.P = C (V.P.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp V.hP)
  have hQ : V.Q = C (V.Q.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp V.hQ)
  set c : ℝ × ℝ := (V.P.coeff 0, V.Q.coeff 0)
  have hconst : ∀ z : ℝ × ℝ, V.toFun z = c := by
    intro z
    show (MvPolynomial.eval ![z.1, z.2] V.P, MvPolynomial.eval ![z.1, z.2] V.Q) = c
    rw [hP, hQ]
    simp only [MvPolynomial.eval_C]
    rfl
  have hderiv : ∀ t : ℝ, HasDerivAt γ c t := fun t => by
    simpa [hconst] using hInt t
  have hgderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => γ s - s • c) 0 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s • c) c t := by
      simpa using (hasDerivAt_id t).smul_const c
    convert (hderiv t).sub h1 using 1
    simp
  have hgdiff : Differentiable ℝ (fun s : ℝ => γ s - s • c) :=
    fun t => (hgderiv t).differentiableAt
  have hgz : ∀ t : ℝ, deriv (fun s : ℝ => γ s - s • c) t = 0 :=
    fun t => (hgderiv t).deriv
  have hgconst : ∀ t : ℝ, γ t - t • c = γ 0 - (0 : ℝ) • c :=
    fun t => is_const_of_deriv_eq_zero hgdiff hgz t 0
  have hγ : ∀ t : ℝ, γ t = (γ 0 - (0 : ℝ) • c) + t • c := by
    intro t
    have h := hgconst t
    rw [sub_eq_iff_eq_add] at h
    rw [h, add_comm]
  have hTc : T • c = 0 := by
    have h := hper 0
    rw [hγ (0 + T), hγ 0, zero_add] at h
    simpa using h
  have hc0 : c = 0 := by
    rcases smul_eq_zero.mp hTc with h | h
    · exact absurd h hT.ne'
    · exact h
  refine hnon ⟨γ 0 - (0 : ℝ) • c, fun t => ?_⟩
  rw [hγ t, hc0]
  simp

/-- The degree-zero field has no limit cycles at all. -/
theorem limitCycles_zero (V : PolyField 0) : LimitCycles V = ∅ := by
  ext S
  simp only [LimitCycles, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
  rintro ⟨⟨γ, hper, rfl⟩, -⟩
  exact no_periodicOrbit_zero V γ hper

/-- Theorem 1.1 holds at `d = 0` with the bound `B = 0`. -/
theorem uniformBound_zero : ∃ B : ℕ, ∀ V : PolyField 0, (LimitCycles V).encard ≤ (B : ℕ∞) :=
  ⟨0, fun V => by rw [limitCycles_zero V]; simp⟩

end JSP1058
