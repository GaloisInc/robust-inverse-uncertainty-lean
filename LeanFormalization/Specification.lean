import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.FieldTheory.Finiteness

/-!
# Auditor-facing statement of robust inverse uncertainty

This file contains only the elementary objects needed to read the theorem.
It deliberately depends on Mathlib alone, not on its proof implementation.
-/

namespace RobustInverseUncertainty.Specification

noncomputable section

open scoped BigOperators Finset symmDiff
attribute [local instance] Classical.propDecidable

/-- The Boolean cube `F₂ⁿ`. -/
abbrev Cube (n : ℕ) := Fin n → ZMod 2

noncomputable local instance {n : ℕ}
    {H : Submodule (ZMod 2) (Cube n)} : Fintype H :=
  Fintype.ofFinite H

/-- Squared `ℓ₂` mass of `f` on `S`. -/
def massOn {n : ℕ} (S : Finset (Cube n)) (f : Cube n → ℂ) : ℝ :=
  ∑ x ∈ S, Complex.normSq (f x)

/-- The unnormalized Walsh-Hadamard transform. -/
def walshTransform {n : ℕ} (f : Cube n → ℂ) (y : Cube n) : ℂ :=
  ∑ x, (if dotProduct x y = 0 then 1 else -1) * f x

/-- The affine coset `a + H`, as a finite set. -/
def affineCoset {n : ℕ} (H : Submodule (ZMod 2) (Cube n))
    (a : Cube n) : Finset (Cube n) :=
  Finset.univ.filter fun x ↦ x + a ∈ H

/-- The dual affine coset `b + Hᗮ`, as a finite set. -/
def dualCoset {n : ℕ} (H : Submodule (ZMod 2) (Cube n))
    (b : Cube n) : Finset (Cube n) :=
  Finset.univ.filter fun y ↦
    ∀ h : Cube n, h ∈ H → dotProduct h (y + b) = 0

/-- A normalized, modulated uniform state on `a + H`. -/
def normalizedCosetState {n : ℕ}
    (H : Submodule (ZMod 2) (Cube n)) (a b : Cube n) (c : ℂ)
    (x : Cube n) : ℂ :=
  if x + a ∈ H then
    c * (Real.sqrt (Fintype.card H) : ℂ)⁻¹ *
      (if dotProduct b x = 0 then 1 else -1)
  else 0

/--
The hypotheses say that `f` nearly minimizes Boolean support uncertainty.
Here `ε` is the mass lost outside each concentration set, `δ` is the excess
in the support-product bound, and `q` is the desired approximation scale.
-/
structure NearExtremizer {n : ℕ} (ε δ q : ℝ)
    (S T : Finset (Cube n)) (f : Cube n → ℂ) : Prop where
  concentration_error_nonnegative : 0 ≤ ε
  support_error_nonnegative : 0 ≤ δ
  q_pos : 0 < q
  q_small : q ≤ 1 / 100
  concentration_error_control : ε ≤ q ^ 4 / 1024
  support_error_control : δ ≤ q ^ 2 / 16
  primal_nonempty : S.Nonempty
  dual_nonempty : T.Nonempty
  normalized : massOn Finset.univ f = 1
  primal_concentration : 1 - ε ≤ massOn S f
  dual_concentration :
    (1 - ε) * Fintype.card (Cube n) ≤
      massOn T (walshTransform f)
  near_minimal_support :
    (S.card : ℝ) * T.card ≤
      (1 + δ) * Fintype.card (Cube n)

/-- The conclusion says that the supports and state have hidden-coset form. -/
structure HiddenCosetApproximation {n : ℕ} (q : ℝ)
    (S T : Finset (Cube n)) (f : Cube n → ℂ)
    (H : Submodule (ZMod 2) (Cube n)) (a b : Cube n) (c : ℂ) : Prop where
  primal_shape :
    (((S ∆ affineCoset H a).card : ℝ) ≤ 5 * q * S.card)
  dual_shape :
    (((T ∆ dualCoset H b).card : ℝ) ≤ 12 * q * T.card)
  unit_phase : Complex.normSq c = 1
  state_distance :
    massOn Finset.univ
      (fun x ↦ f x - normalizedCosetState H a b c x) ≤ 264 * q

end

end RobustInverseUncertainty.Specification
