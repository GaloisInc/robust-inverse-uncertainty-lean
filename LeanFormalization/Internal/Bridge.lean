import LeanFormalization.Specification
import LeanFormalization.Robust

/-!
# Internal bridge to the auditor-facing specification

This module is proof plumbing, not part of the public audit surface. It proves
that the transparent objects in `Specification.lean` agree with the objects
used by the detailed implementation.
-/

namespace RobustInverseUncertainty.Internal

noncomputable section

open scoped BigOperators Finset symmDiff
open Specification
attribute [local instance] Classical.propDecidable

noncomputable local instance theoremSubmoduleFintype {n : ℕ}
    {H : Submodule (ZMod 2) (Cube n)} : Fintype H :=
  Fintype.ofFinite H

private theorem massOn_eq_energyOn {n : ℕ} (S : Finset (Cube n))
    (f : Cube n → ℂ) :
    massOn S f = energyOn S f := by
  rfl

private theorem massOn_univ_eq_complexEnergy {n : ℕ} (f : Cube n → ℂ) :
    massOn Finset.univ f = complexEnergy f := by
  simp [massOn, complexEnergy]

private theorem walshTransform_eq_walshFourier {n : ℕ} (f : Cube n → ℂ) :
    walshTransform f = walshFourier f := by
  funext y
  rw [walshTransform, walshFourier]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [phase, bitPhase, dot, dotProduct]
  rfl

private theorem affineCoset_eq_affineSubspacePoints {n : ℕ}
    (H : Submodule (ZMod 2) (Cube n)) (a : Cube n) :
    affineCoset H a = affineSubspacePoints H a := by
  ext x
  simp [affineCoset, mem_affineSubspacePoints]

private theorem dualCoset_eq_affineSubspacePoints_perp {n : ℕ}
    (H : Submodule (ZMod 2) (Cube n)) (b : Cube n) :
    dualCoset H b = affineSubspacePoints (perp H) b := by
  ext y
  simp [dualCoset, mem_affineSubspacePoints, mem_perp_iff,
    dot, dotProduct]

private theorem normalizedCosetState_eq {n : ℕ}
    (H : Submodule (ZMod 2) (Cube n)) (a b : Cube n) (c : ℂ) :
    normalizedCosetState H a b c =
      fun x ↦ c * (Real.sqrt (Fintype.card H) : ℂ)⁻¹ *
        cosetWave H a b x := by
  funext x
  simp only [normalizedCosetState, cosetWave, phase, bitPhase,
    dot, dotProduct]
  split_ifs <;> ring

theorem robust_inverse_uncertainty_phase_from_implementation
    {n : ℕ} {ε δ q : ℝ}
    {S T : Finset (Cube n)} {f : Cube n → ℂ}
    (h : NearExtremizer ε δ q S T f) :
    ∃ (H : Submodule (ZMod 2) (Cube n)) (a b : Cube n) (c : ℂ),
      HiddenCosetApproximation q S T f H a b c := by
  have hnormalized : complexEnergy f = 1 := by
    rw [← massOn_univ_eq_complexEnergy]
    exact h.normalized
  have hprimal : 1 - q ^ 4 / 1024 ≤ energyOn S f := by
    calc
      1 - q ^ 4 / 1024 ≤ 1 - ε := by
        linarith [h.concentration_error_control]
      _ ≤ massOn S f := h.primal_concentration
      _ = energyOn S f := massOn_eq_energyOn S f
  have hdual :
      (1 - q ^ 4 / 1024) * Fintype.card (Cube n) ≤
        energyOn T (walshFourier f) := by
    calc
      (1 - q ^ 4 / 1024) * Fintype.card (Cube n) ≤
          (1 - ε) * Fintype.card (Cube n) := by
        gcongr
        linarith [h.concentration_error_control]
      _ ≤ massOn T (walshTransform f) := h.dual_concentration
      _ = energyOn T (walshFourier f) := by
        rw [massOn_eq_energyOn, walshTransform_eq_walshFourier]
  have hproduct :
      (S.card : ℝ) * T.card ≤
        (1 + q ^ 2 / 16) * Fintype.card (Cube n) := by
    calc
      (S.card : ℝ) * T.card ≤
          (1 + δ) * Fintype.card (Cube n) :=
        h.near_minimal_support
      _ ≤ (1 + q ^ 2 / 16) * Fintype.card (Cube n) := by
        gcongr
        exact h.support_error_control
  obtain ⟨H, a, b, hS, hT, c, hc, hf⟩ :=
    robust_inverse_uncertainty_phase_implementation S T f
      h.q_pos h.q_small h.primal_nonempty h.dual_nonempty
      hnormalized hprimal hdual
      hproduct
  refine ⟨H, a, b, c, ?_⟩
  constructor
  · simpa [affineCoset_eq_affineSubspacePoints] using hS
  · simpa [dualCoset_eq_affineSubspacePoints_perp] using hT
  · exact hc
  · rw [massOn_univ_eq_complexEnergy, normalizedCosetState_eq]
    exact hf

end

end RobustInverseUncertainty.Internal
