/-
JSP-000036 — Modularity theorem for rational elliptic curves (Taniyama–Shimura–Weil).

This file records the statement only. The proof is the Breuil–Conrad–Diamond–Taylor
theorem (built on Wiles/Taylor–Wiles); nothing in Mathlib v4.34.0 proves it, so the
statement below is not discharged here.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion

namespace JSP36

open CongruenceSubgroup UpperHalfPlane

/-- The modularity statement over `ℚ`: every elliptic curve over `ℚ` (i.e. every
Weierstrass curve with nonzero discriminant) is attached to a weight-2 cusp form on
some `Γ₀(N)`, in the sense that the `q`-expansion coefficients of the form equal the
Dirichlet coefficients of the curve's `L`-function. -/
def Modularity : Prop :=
  ∀ W : WeierstrassCurve ℚ, W.Δ ≠ 0 →
    ∃ (N : ℕ) (f : CuspForm (Gamma0 N) 2),
      ∀ n : ℕ, (W.LFunction n : ℂ) = (qExpansion 1 (f : ℍ → ℂ)).coeff n

end JSP36
