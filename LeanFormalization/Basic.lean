/-
Copyright (c) 2026 Galois, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Marios Georgiou
-/

import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Combinatorics.Additive.VerySmallDoubling
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic

/-!
# Algebraic core of hidden cosets on the Boolean cube

This file formalizes the exact finite Fourier identities used by the proposed
robust inverse-uncertainty argument without proof placeholders or added axioms.
-/

namespace RobustInverseUncertainty

noncomputable section

open scoped BigOperators Finset Pointwise
attribute [local instance] Classical.propDecidable

/-- The Boolean vector space `F₂ⁿ`. -/
abbrev BooleanSpace (n : ℕ) := Fin n → ZMod 2

noncomputable local instance submoduleFintype {n : ℕ}
    {H : Submodule (ZMod 2) (BooleanSpace n)} : Fintype H :=
  Fintype.ofFinite H

/-- The standard bilinear pairing on `F₂ⁿ`. -/
def dot {n : ℕ} (x y : BooleanSpace n) : ZMod 2 :=
  ∑ i, x i * y i

/-- The real sign `(-1)^z`, embedded in `ℂ`, for `z ∈ F₂`. -/
def bitPhase (z : ZMod 2) : ℂ :=
  if z = 0 then 1 else -1

theorem zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    rw [← ZMod.val_eq_one (by norm_num) x]
    have hxpos : 0 < x.val := ZMod.val_pos.mpr hx
    have hxlt : x.val < 2 := ZMod.val_lt x
    omega

@[simp]
theorem bitPhase_zero : bitPhase 0 = 1 := by
  simp [bitPhase]

@[simp]
theorem bitPhase_one : bitPhase 1 = -1 := by
  norm_num [bitPhase]

@[simp]
theorem bitPhase_add (x y : ZMod 2) :
    bitPhase (x + y) = bitPhase x * bitPhase y := by
  rcases zmod_two_eq_zero_or_one x with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one y with rfl | rfl
  all_goals norm_num [bitPhase, show (1 : ZMod 2) ≠ 0 by decide,
    show (1 + 1 : ZMod 2) = 0 by decide] <;> decide

@[simp]
theorem bitPhase_eq_one_iff {x : ZMod 2} : bitPhase x = 1 ↔ x = 0 := by
  fin_cases x <;> norm_num [bitPhase]

@[simp]
theorem bitPhase_ne_zero (x : ZMod 2) : bitPhase x ≠ 0 := by
  rcases zmod_two_eq_zero_or_one x with rfl | rfl <;>
    norm_num [bitPhase, show (1 : ZMod 2) ≠ 0 by decide]

@[simp]
theorem bitPhase_mul_self (x : ZMod 2) : bitPhase x * bitPhase x = 1 := by
  rcases zmod_two_eq_zero_or_one x with rfl | rfl <;>
    norm_num [bitPhase, show (1 : ZMod 2) ≠ 0 by decide]

@[simp]
theorem dot_zero_left {n : ℕ} (y : BooleanSpace n) : dot 0 y = 0 := by
  simp [dot]

@[simp]
theorem dot_zero_right {n : ℕ} (x : BooleanSpace n) : dot x 0 = 0 := by
  simp [dot]

theorem dot_add_left {n : ℕ} (x y z : BooleanSpace n) :
    dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem dot_add_right {n : ℕ} (x y z : BooleanSpace n) :
    dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_smul_right {n : ℕ} (c : ZMod 2) (x y : BooleanSpace n) :
    dot x (c • y) = c * dot x y := by
  simp [dot, Finset.mul_sum, mul_left_comm]

theorem dot_comm {n : ℕ} (x y : BooleanSpace n) : dot x y = dot y x := by
  simp only [dot]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem dot_smul_left {n : ℕ} (c : ZMod 2) (x y : BooleanSpace n) :
    dot (c • x) y = c * dot x y := by
  rw [dot_comm, dot_smul_right, dot_comm]

@[simp]
theorem dot_single_left {n : ℕ} (i : Fin n) (c : ZMod 2) (y : BooleanSpace n) :
    dot (Pi.single i c) y = c * y i := by
  classical
  simp only [dot]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- The Walsh character `(-1)^{x·y}`. -/
def phase {n : ℕ} (x y : BooleanSpace n) : ℂ :=
  bitPhase (dot x y)

@[simp]
theorem phase_zero_left {n : ℕ} (y : BooleanSpace n) : phase 0 y = 1 := by
  simp [phase]

@[simp]
theorem phase_zero_right {n : ℕ} (x : BooleanSpace n) : phase x 0 = 1 := by
  simp [phase]

@[simp]
theorem phase_add_left {n : ℕ} (x y z : BooleanSpace n) :
    phase (x + y) z = phase x z * phase y z := by
  simp [phase, dot_add_left]

@[simp]
theorem phase_add_right {n : ℕ} (x y z : BooleanSpace n) :
    phase x (y + z) = phase x y * phase x z := by
  simp [phase, dot_add_right]

theorem phase_comm {n : ℕ} (x y : BooleanSpace n) : phase x y = phase y x := by
  simp [phase, dot_comm]

@[simp]
theorem phase_ne_zero {n : ℕ} (x y : BooleanSpace n) : phase x y ≠ 0 := by
  exact bitPhase_ne_zero _

@[simp]
theorem phase_mul_self {n : ℕ} (x y : BooleanSpace n) :
    phase x y * phase x y = 1 := by
  exact bitPhase_mul_self _

/-- The four-point test used to turn a rank-one sign pattern into orthogonality. -/
theorem four_point_identity {n : ℕ} (t t₀ s s₀ : BooleanSpace n) :
    phase t s * phase t s₀ * phase t₀ s * phase t₀ s₀ =
      phase (t + t₀) (s + s₀) := by
  simp only [phase_add_left, phase_add_right]
  ring

/-- The Walsh sign as a bundled complex additive character. -/
def phaseChar {n : ℕ} (y : BooleanSpace n) : AddChar (BooleanSpace n) ℂ where
  toFun x := phase x y
  map_zero_eq_one' := phase_zero_left y
  map_add_eq_mul' := fun x z ↦ phase_add_left x z y

@[simp]
theorem phaseChar_apply {n : ℕ} (x y : BooleanSpace n) :
    phaseChar y x = phase x y := rfl

@[simp]
theorem phaseChar_eq_zero_iff {n : ℕ} (y : BooleanSpace n) :
    phaseChar y = 0 ↔ y = 0 := by
  constructor
  · intro h
    funext i
    have hi := DFunLike.congr_fun h (Pi.single i (1 : ZMod 2))
    change phase (Pi.single i 1) y = 1 at hi
    simpa [phase] using (bitPhase_eq_one_iff.mp hi)
  · rintro rfl
    ext x
    simp [phaseChar]

/-- Orthogonality of all Walsh characters on the Boolean cube. -/
theorem sum_phase_eq_ite {n : ℕ} (y : BooleanSpace n) :
    ∑ x : BooleanSpace n, phase x y =
      if y = 0 then (Fintype.card (BooleanSpace n) : ℂ) else 0 := by
  simpa using AddChar.sum_eq_ite (phaseChar y)

/-- The unnormalized Walsh-Fourier transform. -/
def walshFourier {n : ℕ} (f : BooleanSpace n → ℂ) :
    BooleanSpace n → ℂ :=
  fun y ↦ ∑ x : BooleanSpace n, phase x y * f x

@[simp]
theorem card_booleanSpace (n : ℕ) :
    Fintype.card (BooleanSpace n) = 2 ^ n := by
  simp [BooleanSpace]

/-- The standard dot product as a bilinear form. -/
def dotBilin (n : ℕ) :
    LinearMap.BilinForm (ZMod 2) (BooleanSpace n) :=
  LinearMap.mk₂ (ZMod 2) dot dot_add_left dot_smul_left dot_add_right dot_smul_right

@[simp]
theorem dotBilin_apply {n : ℕ} (x y : BooleanSpace n) :
    dotBilin n x y = dot x y := rfl

/-- The standard dot product on `F₂ⁿ` is nondegenerate. -/
theorem dotBilin_nondegenerate (n : ℕ) : (dotBilin n).Nondegenerate := by
  constructor
  · intro x hx
    funext i
    change x i = 0
    have hi := hx (Pi.single i (1 : ZMod 2))
    change dot x (Pi.single i (1 : ZMod 2)) = 0 at hi
    rw [dot_comm x (Pi.single i (1 : ZMod 2))] at hi
    simpa using hi
  · intro y hy
    funext i
    change y i = 0
    have hi := hy (Pi.single i (1 : ZMod 2))
    change dot (Pi.single i (1 : ZMod 2)) y = 0 at hi
    simpa using hi

theorem dotBilin_isRefl (n : ℕ) : (dotBilin n).IsRefl := by
  intro x y
  rw [dotBilin_apply, dotBilin_apply, dot_comm]
  intro h
  exact h

/-- The orthogonal complement with respect to the standard Boolean pairing. -/
def perp {n : ℕ} (H : Submodule (ZMod 2) (BooleanSpace n)) :
    Submodule (ZMod 2) (BooleanSpace n) where
  carrier := {y | ∀ h ∈ H, dot h y = 0}
  zero_mem' := by simp
  add_mem' := by
    intro y z hy hz h hH
    rw [dot_add_right, hy h hH, hz h hH, add_zero]
  smul_mem' := by
    intro c y hy h hH
    rw [dot_smul_right, hy h hH, mul_zero]

@[simp]
theorem mem_perp_iff {n : ℕ} {H : Submodule (ZMod 2) (BooleanSpace n)}
    {y : BooleanSpace n} :
    y ∈ perp H ↔ ∀ h ∈ H, dot h y = 0 := Iff.rfl

theorem perp_eq_orthogonal {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) :
    perp H = (dotBilin n).orthogonal H := by
  ext y
  rfl

/-- The dimensions of a Boolean subspace and its orthogonal complement add to `n`. -/
theorem finrank_perp {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) :
    Module.finrank (ZMod 2) (perp H) =
      n - Module.finrank (ZMod 2) H := by
  rw [perp_eq_orthogonal,
    LinearMap.BilinForm.finrank_orthogonal (dotBilin_nondegenerate n)]
  simp

/-- Cardinality saturation for dual Boolean subspaces. -/
theorem card_mul_card_perp {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) :
    Fintype.card H * Fintype.card (perp H) = 2 ^ n := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := H),
    Module.card_eq_pow_finrank (K := ZMod 2) (V := perp H),
    ZMod.card, finrank_perp, ← pow_add]
  congr 1
  have hle : Module.finrank (ZMod 2) H ≤ n := by
    simpa using H.finrank_le
  exact Nat.add_sub_of_le hle

@[simp]
theorem perp_perp {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) :
    perp (perp H) = H := by
  calc
    perp (perp H) = (dotBilin n).orthogonal (perp H) :=
      perp_eq_orthogonal (perp H)
    _ = (dotBilin n).orthogonal ((dotBilin n).orthogonal H) := by
      rw [perp_eq_orthogonal]
    _ = H := LinearMap.BilinForm.orthogonal_orthogonal
      (dotBilin_nondegenerate n) (dotBilin_isRefl n) H

theorem inv_card_booleanSpace_mul_card_perp {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) :
    (Fintype.card (BooleanSpace n) : ℂ)⁻¹ *
        (Fintype.card (perp H) : ℂ) =
      (Fintype.card H : ℂ)⁻¹ := by
  have hcard :
      (Fintype.card (BooleanSpace n) : ℂ) =
        (Fintype.card H : ℂ) * (Fintype.card (perp H) : ℂ) := by
    exact_mod_cast (card_booleanSpace n).trans (card_mul_card_perp H).symm
  rw [hcard, mul_inv_rev]
  have hperp : (Fintype.card (perp H) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- A Walsh character restricted to a linear subspace. -/
def restrictedPhaseChar {n : ℕ} (H : Submodule (ZMod 2) (BooleanSpace n))
    (y : BooleanSpace n) : AddChar H ℂ :=
  (phaseChar y).compAddMonoidHom H.subtype.toAddMonoidHom

@[simp]
theorem restrictedPhaseChar_apply {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (y : BooleanSpace n) (h : H) :
    restrictedPhaseChar H y h = phase h y := rfl

@[simp]
theorem restrictedPhaseChar_eq_zero_iff {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (y : BooleanSpace n) :
    restrictedPhaseChar H y = 0 ↔ y ∈ perp H := by
  constructor
  · intro hzero
    rw [mem_perp_iff]
    intro h hh
    have hv := DFunLike.congr_fun hzero ⟨h, hh⟩
    change phase h y = 1 at hv
    exact bitPhase_eq_one_iff.mp hv
  · intro hy
    rw [mem_perp_iff] at hy
    ext h
    simp [restrictedPhaseChar, phase, hy h h.property]

/-- Character orthogonality on a subspace. -/
theorem sum_phase_subspace_eq_ite {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (y : BooleanSpace n) :
    ∑ h : H, phase h y =
      if y ∈ perp H then (Fintype.card H : ℂ) else 0 := by
  simpa using AddChar.sum_eq_ite (restrictedPhaseChar H y)

/-- Fourier sum of an affine subspace indicator. -/
theorem sum_phase_coset {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (a y : BooleanSpace n) :
    ∑ h : H, phase (a + (h : BooleanSpace n)) y =
      phase a y * if y ∈ perp H then (Fintype.card H : ℂ) else 0 := by
  simp_rw [phase_add_left]
  rw [← Finset.mul_sum]
  simp [sum_phase_subspace_eq_ite]

/--
The exact hidden-coset Fourier identity.  Modulating the indicator of `a + H`
by frequency `b` translates its Fourier support to `b + Hᗮ`.
-/
theorem modulated_coset_fourier_sum {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (a b y : BooleanSpace n) :
    ∑ h : H, phase (a + (h : BooleanSpace n)) y *
        phase b (a + (h : BooleanSpace n)) =
      phase a (y + b) *
        if y + b ∈ perp H then (Fintype.card H : ℂ) else 0 := by
  calc
    ∑ h : H, phase (a + (h : BooleanSpace n)) y *
          phase b (a + (h : BooleanSpace n)) =
        ∑ h : H, phase (a + (h : BooleanSpace n)) (y + b) := by
          apply Finset.sum_congr rfl
          intro h _
          rw [phase_comm b (a + (h : BooleanSpace n)), phase_add_right]
    _ = phase a (y + b) *
        if y + b ∈ perp H then (Fintype.card H : ℂ) else 0 :=
      sum_phase_coset H a (y + b)

/-- The Fourier sum above is nonzero exactly on the dual affine subspace. -/
theorem modulated_coset_fourier_sum_ne_zero_iff {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (a b y : BooleanSpace n) :
    (∑ h : H, phase (a + (h : BooleanSpace n)) y *
      phase b (a + (h : BooleanSpace n))) ≠ 0 ↔
      y + b ∈ perp H := by
  rw [modulated_coset_fourier_sum]
  by_cases hy : y + b ∈ perp H
  · simp [hy, Fintype.card_ne_zero]
  · simp [hy]

/-- Negation is trivial in the Boolean vector space. -/
@[simp]
theorem neg_eq_self {n : ℕ} (x : BooleanSpace n) : -x = x := by
  funext i
  exact ZMod.neg_eq_self_mod_two _

@[simp]
theorem add_self_eq_zero {n : ℕ} (x : BooleanSpace n) : x + x = 0 := by
  simpa only [neg_eq_self] using add_neg_cancel x

/-- Adding two points is in `H` exactly when they are in the same `H`-coset. -/
theorem add_mem_iff_of_mem_coset {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (a x y : BooleanSpace n)
    (hx : x + a ∈ H) :
    x + y ∈ H ↔ y + a ∈ H := by
  constructor
  · intro hxy
    have := H.add_mem hx hxy
    have heq : (x + a) + (x + y) = y + a := by
      calc
        (x + a) + (x + y) = (x + x) + (a + y) := by ac_rfl
        _ = y + a := by simp [add_comm]
    rwa [heq] at this
  · intro hy
    have := H.add_mem hx hy
    have heq : (x + a) + (y + a) = x + y := by
      calc
        (x + a) + (y + a) = (a + a) + (x + y) := by ac_rfl
        _ = x + y := by simp
    rwa [heq] at this

/-- The unnormalized modulated indicator of the affine subspace `a + H`. -/
def cosetWave {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (a b x : BooleanSpace n) : ℂ :=
  if x + a ∈ H then phase b x else 0

/-- Coordinate projection onto the affine subspace `a + H`. -/
def coordinateProjector {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (a : BooleanSpace n)
    (f : BooleanSpace n → ℂ) : BooleanSpace n → ℂ :=
  fun x ↦ if x + a ∈ H then f x else 0

/--
The dual-coset projection after evaluating its Fourier kernel by character
orthogonality.  The factor is `1 / |H|`.
-/
def dualCosetKernelProjector {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (b : BooleanSpace n)
    (f : BooleanSpace n → ℂ) : BooleanSpace n → ℂ :=
  fun x ↦ (Fintype.card H : ℂ)⁻¹ *
    ∑ y : BooleanSpace n,
      if x + y ∈ H then phase b (x + y) * f y else 0

/--
Inverse Walsh transform after restricting the Walsh transform to the dual
affine subspace `b + Hᗮ`.  Frequencies are parametrized uniquely as `b + k`
with `k : Hᗮ`.
-/
def dualCosetFourierProjector {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (b : BooleanSpace n)
    (f : BooleanSpace n → ℂ) : BooleanSpace n → ℂ :=
  fun x ↦ (Fintype.card (BooleanSpace n) : ℂ)⁻¹ *
    ∑ k : perp H,
      phase x (b + (k : BooleanSpace n)) *
        walshFourier f (b + (k : BooleanSpace n))

theorem sum_phase_dual_coset {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n))
    (b x y : BooleanSpace n) :
    (∑ k : perp H,
      phase x (b + (k : BooleanSpace n)) *
        phase y (b + (k : BooleanSpace n))) =
      phase b (x + y) *
        if x + y ∈ H then (Fintype.card (perp H) : ℂ) else 0 := by
  calc
    (∑ k : perp H,
      phase x (b + (k : BooleanSpace n)) *
        phase y (b + (k : BooleanSpace n))) =
        ∑ k : perp H, phase (b + (k : BooleanSpace n)) (x + y) := by
          apply Finset.sum_congr rfl
          intro k _
          calc
            phase x (b + (k : BooleanSpace n)) *
                phase y (b + (k : BooleanSpace n)) =
              phase (b + (k : BooleanSpace n)) x *
                phase (b + (k : BooleanSpace n)) y := by
                  rw [phase_comm x, phase_comm y]
            _ = phase (b + (k : BooleanSpace n)) (x + y) :=
              (phase_add_right (b + (k : BooleanSpace n)) x y).symm
    _ = phase b (x + y) *
        if x + y ∈ perp (perp H) then
          (Fintype.card (perp H) : ℂ) else 0 :=
      sum_phase_coset (perp H) b (x + y)
    _ = phase b (x + y) *
        if x + y ∈ H then (Fintype.card (perp H) : ℂ) else 0 := by
      rw [perp_perp]

/-- The Fourier-side definition evaluates to the character-orthogonality kernel. -/
theorem dualCosetFourierProjector_eq_kernel {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (b : BooleanSpace n)
    (f : BooleanSpace n → ℂ) :
    dualCosetFourierProjector H b f = dualCosetKernelProjector H b f := by
  funext x
  calc
    dualCosetFourierProjector H b f x =
        (Fintype.card (BooleanSpace n) : ℂ)⁻¹ *
          ∑ k : perp H, ∑ y : BooleanSpace n,
            (phase x (b + (k : BooleanSpace n)) *
              phase y (b + (k : BooleanSpace n))) * f y := by
        simp only [dualCosetFourierProjector, walshFourier]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
    _ = (Fintype.card (BooleanSpace n) : ℂ)⁻¹ *
          ∑ y : BooleanSpace n, ∑ k : perp H,
            (phase x (b + (k : BooleanSpace n)) *
              phase y (b + (k : BooleanSpace n))) * f y := by
        rw [Finset.sum_comm]
    _ = (Fintype.card (BooleanSpace n) : ℂ)⁻¹ *
          ∑ y : BooleanSpace n,
            (∑ k : perp H,
              phase x (b + (k : BooleanSpace n)) *
                phase y (b + (k : BooleanSpace n))) * f y := by
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.sum_mul]
    _ = (Fintype.card (BooleanSpace n) : ℂ)⁻¹ *
          ∑ y : BooleanSpace n,
            (phase b (x + y) *
              if x + y ∈ H then (Fintype.card (perp H) : ℂ) else 0) * f y := by
        simp_rw [sum_phase_dual_coset]
    _ = (Fintype.card (BooleanSpace n) : ℂ)⁻¹ *
          (Fintype.card (perp H) : ℂ) *
          ∑ y : BooleanSpace n,
            if x + y ∈ H then phase b (x + y) * f y else 0 := by
        rw [mul_assoc]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : x + y ∈ H
        · simp [hy]
          ring
        · simp [hy]
    _ = dualCosetKernelProjector H b f x := by
        rw [inv_card_booleanSpace_mul_card_perp]
        rfl

/-- The rank-one operator generated by the modulated affine-subspace wave. -/
def cosetRankOne {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (a b : BooleanSpace n)
    (f : BooleanSpace n → ℂ) : BooleanSpace n → ℂ :=
  fun x ↦ (Fintype.card H : ℂ)⁻¹ * cosetWave H a b x *
    ∑ y : BooleanSpace n, cosetWave H a b y * f y

theorem dualCosetKernelProjector_apply_of_mem_coset {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (a b x : BooleanSpace n)
    (f : BooleanSpace n → ℂ) (hx : x + a ∈ H) :
    dualCosetKernelProjector H b f x =
      (Fintype.card H : ℂ)⁻¹ * phase b x *
        ∑ y : BooleanSpace n, cosetWave H a b y * f y := by
  simp [dualCosetKernelProjector, cosetWave,
    add_mem_iff_of_mem_coset H a x, hx, phase_add_right,
    Finset.mul_sum, mul_assoc]

/-- `P_(a+H) Q_(b+Hᗮ)` is the expected rank-one coset-state operator. -/
theorem coordinate_comp_dualCosetKernelProjector {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (a b : BooleanSpace n)
    (f : BooleanSpace n → ℂ) :
    coordinateProjector H a (dualCosetKernelProjector H b f) =
      cosetRankOne H a b f := by
  funext x
  by_cases hx : x + a ∈ H
  · simp [coordinateProjector, cosetRankOne, cosetWave, hx,
      dualCosetKernelProjector_apply_of_mem_coset H a b x f hx]
  · simp [coordinateProjector, cosetRankOne, cosetWave, hx]

/-- The same rank-one operator is obtained in the opposite order. -/
theorem dualCosetKernelProjector_comp_coordinate {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (a b : BooleanSpace n)
    (f : BooleanSpace n → ℂ) :
    dualCosetKernelProjector H b (coordinateProjector H a f) =
      cosetRankOne H a b f := by
  funext x
  by_cases hx : x + a ∈ H
  · rw [dualCosetKernelProjector_apply_of_mem_coset H a b x _ hx]
    have hsum :
        (∑ y : BooleanSpace n,
          cosetWave H a b y * coordinateProjector H a f y) =
        ∑ y : BooleanSpace n, cosetWave H a b y * f y := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y + a ∈ H <;>
        simp [coordinateProjector, cosetWave, hy]
    rw [hsum]
    simp [cosetRankOne, cosetWave, hx]
  · have hsum :
        (∑ y : BooleanSpace n,
          if x + y ∈ H then
            phase b (x + y) * coordinateProjector H a f y
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy : y + a ∈ H
      · have hxy : x + y ∉ H := by
          intro hxy
          have := H.add_mem hxy hy
          apply hx
          have heq : (x + y) + (y + a) = x + a := by
            calc
              (x + y) + (y + a) = (y + y) + (x + a) := by ac_rfl
              _ = x + a := by simp
          rwa [heq] at this
        simp [hxy]
      · simp [coordinateProjector, hy]
    have hdual : dualCosetKernelProjector H b (coordinateProjector H a f) x = 0 := by
      simp only [dualCosetKernelProjector]
      rw [hsum, mul_zero]
    rw [hdual]
    simp [cosetRankOne, cosetWave, hx]

/-- The primal and dual affine-coset projectors commute. -/
theorem coordinate_dualCosetKernelProjector_commute {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (a b : BooleanSpace n)
    (f : BooleanSpace n → ℂ) :
    coordinateProjector H a (dualCosetKernelProjector H b f) =
      dualCosetKernelProjector H b (coordinateProjector H a f) := by
  rw [coordinate_comp_dualCosetKernelProjector,
    dualCosetKernelProjector_comp_coordinate]

/-- In the multiplicative type tag, every Boolean vector is self-inverse. -/
@[simp]
theorem multiplicative_inv_eq_self {n : ℕ}
    (x : Multiplicative (BooleanSpace n)) : x⁻¹ = x := by
  apply Multiplicative.toAdd.injective
  simp

@[simp]
theorem finset_inv_eq_self {n : ℕ}
    (A : Finset (Multiplicative (BooleanSpace n))) : A⁻¹ = A := by
  ext x
  simp

/--
The small-doubling input needed in the robust proof, obtained from Mathlib's
sharp `< 3/2` theorem.  Multiplication here is addition on `F₂ⁿ` via the
`Multiplicative` type tag.
-/
theorem small_doubling_is_subgroup {n : ℕ}
    (A : Finset (Multiplicative (BooleanSpace n)))
    (hA : #(A * A) < (3 / 2 : ℚ) * #A) :
    ∃ H : Subgroup (Multiplicative (BooleanSpace n)),
      (H : Set (Multiplicative (BooleanSpace n))) = A * A := by
  refine ⟨Finset.invMulSubgroup A hA, ?_⟩
  rw [Finset.invMulSubgroup_eq_inv_mul, finset_inv_eq_self]

end

end RobustInverseUncertainty
