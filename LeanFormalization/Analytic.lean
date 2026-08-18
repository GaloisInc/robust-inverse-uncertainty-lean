/-
Copyright (c) 2026 Galois, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Marios Georgiou
-/

import LeanFormalization.Combinatorial

/-!
# Finite-energy identities for robust inverse uncertainty

This file supplies the analytic Walsh identities in explicit finite-sum form.
-/

namespace RobustInverseUncertainty

noncomputable section

open scoped BigOperators Finset Pointwise symmDiff
attribute [local instance] Classical.propDecidable

/-- Squared `ℓ₂` norm of a real vector on a finite type. -/
def realEnergy {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  ∑ x, f x ^ 2

/-- Squared `ℓ₂` norm of a complex vector on a finite type. -/
def complexEnergy {α : Type*} [Fintype α] (f : α → ℂ) : ℝ :=
  ∑ x, Complex.normSq (f x)

/-- Energy restricted to a finite set of coordinates. -/
def energyOn {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (f : α → ℂ) : ℝ :=
  ∑ x ∈ S, Complex.normSq (f x)

/-- The unnormalized real Walsh transform. -/
def realWalshTransform {n : ℕ} (f : BooleanSpace n → ℝ) :
    BooleanSpace n → ℝ :=
  fun y ↦ ∑ x, realPhase x y * f x

theorem realWalshTransform_parseval {n : ℕ}
    (f : BooleanSpace n → ℝ) :
    realEnergy (realWalshTransform f) =
      Fintype.card (BooleanSpace n) * realEnergy f := by
  classical
  calc
    realEnergy (realWalshTransform f) =
        ∑ y : BooleanSpace n, ∑ x : BooleanSpace n,
          ∑ z : BooleanSpace n,
            (realPhase x y * realPhase z y) * (f x * f z) := by
      simp only [realEnergy, realWalshTransform, pow_two,
        Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ = ∑ x : BooleanSpace n, ∑ z : BooleanSpace n,
          (∑ y : BooleanSpace n,
            realPhase x y * realPhase z y) * (f x * f z) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_mul]
    _ = ∑ x : BooleanSpace n, ∑ z : BooleanSpace n,
          (if x = z then
            (Fintype.card (BooleanSpace n) : ℝ) else 0) * (f x * f z) := by
      simp_rw [sum_realPhase_mul_realPhase]
    _ = Fintype.card (BooleanSpace n) * realEnergy f := by
      simp [realEnergy]
      rw [← Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      ring

theorem walshFourier_re {n : ℕ} (f : BooleanSpace n → ℂ)
    (y : BooleanSpace n) :
    (walshFourier f y).re =
      realWalshTransform (fun x ↦ (f x).re) y := by
  classical
  rw [walshFourier, realWalshTransform]
  calc
    (∑ x : BooleanSpace n, phase x y * f x).re =
        ∑ x : BooleanSpace n, (phase x y * f x).re := by
      simpa using Complex.re_sum (s := Finset.univ)
        (fun x : BooleanSpace n ↦ phase x y * f x)
    _ = ∑ x : BooleanSpace n, realPhase x y * (f x).re := by
      apply Finset.sum_congr rfl
      intro x hx
      have hp : phase x y = (realPhase x y : ℂ) :=
        (ofReal_realPhase x y).symm
      simp only [hp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]

theorem walshFourier_im {n : ℕ} (f : BooleanSpace n → ℂ)
    (y : BooleanSpace n) :
    (walshFourier f y).im =
      realWalshTransform (fun x ↦ (f x).im) y := by
  classical
  rw [walshFourier, realWalshTransform]
  calc
    (∑ x : BooleanSpace n, phase x y * f x).im =
        ∑ x : BooleanSpace n, (phase x y * f x).im := by
      simpa using Complex.im_sum (s := Finset.univ)
        (fun x : BooleanSpace n ↦ phase x y * f x)
    _ = ∑ x : BooleanSpace n, realPhase x y * (f x).im := by
      apply Finset.sum_congr rfl
      intro x hx
      have hp : phase x y = (realPhase x y : ℂ) :=
        (ofReal_realPhase x y).symm
      simp only [hp, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]

/-- Parseval for the unnormalized complex Walsh transform. -/
theorem walshFourier_parseval {n : ℕ}
    (f : BooleanSpace n → ℂ) :
    complexEnergy (walshFourier f) =
      Fintype.card (BooleanSpace n) * complexEnergy f := by
  rw [complexEnergy, complexEnergy]
  simp_rw [Complex.normSq_apply, walshFourier_re, walshFourier_im]
  rw [Finset.sum_add_distrib]
  have hre := realWalshTransform_parseval
    (fun x : BooleanSpace n ↦ (f x).re)
  have him := realWalshTransform_parseval
    (fun x : BooleanSpace n ↦ (f x).im)
  simp only [realEnergy, pow_two] at hre him
  rw [hre, him, Finset.sum_add_distrib, mul_add]

theorem energyOn_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (f : α → ℂ) :
    0 ≤ energyOn S f := by
  exact Finset.sum_nonneg fun x hx ↦ Complex.normSq_nonneg _

theorem energyOn_le_complexEnergy {α : Type*}
    [Fintype α] [DecidableEq α]
    (S : Finset α) (f : α → ℂ) :
    energyOn S f ≤ complexEnergy f := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (show S ⊆ Finset.univ from Finset.subset_univ S)
  intro x hx hnot
  exact Complex.normSq_nonneg _

/-- Coordinate restriction to a finite set. -/
def restrictTo {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℂ) : α → ℂ :=
  fun x ↦ if x ∈ S then f x else 0

theorem complexEnergy_restrictTo {α : Type*}
    [Fintype α] [DecidableEq α]
    (S : Finset α) (f : α → ℂ) :
    complexEnergy (restrictTo S f) = energyOn S f := by
  rw [complexEnergy, energyOn]
  calc
    (∑ x : α, Complex.normSq (restrictTo S f x)) =
        ∑ x : α, if x ∈ S then Complex.normSq (f x) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x ∈ S <;> simp [restrictTo, h]
    _ = ∑ x ∈ S, Complex.normSq (f x) := by
      simp [Finset.sum_ite_mem]

theorem complexEnergy_sub_restrictTo {α : Type*}
    [Fintype α] [DecidableEq α]
    (S : Finset α) (f : α → ℂ) :
    complexEnergy (fun x ↦ f x - restrictTo S f x) =
      complexEnergy f - energyOn S f := by
  rw [complexEnergy, energyOn, complexEnergy]
  have hsplit :
      (∑ x : α, Complex.normSq (f x)) =
        (∑ x ∈ S, Complex.normSq (f x)) +
          ∑ x ∈ Finset.univ \ S, Complex.normSq (f x) := by
    rw [← Finset.sum_union]
    · congr
      ext x
      simp
    · exact Finset.disjoint_sdiff
  calc
    (∑ x : α, Complex.normSq (f x - restrictTo S f x)) =
        ∑ x : α, if x ∈ S then 0 else Complex.normSq (f x) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x ∈ S <;> simp [restrictTo, h]
    _ = ∑ x ∈ Finset.univ \ S, Complex.normSq (f x) := by
      simp [Finset.sum_ite, Finset.filter_notMem_eq_sdiff]
    _ = (∑ x : α, Complex.normSq (f x)) -
        ∑ x ∈ S, Complex.normSq (f x) := by
      rw [hsplit]
      ring

/-- The unnormalized sign-matrix action from coordinates in `S`. -/
def restrictedWalshApply {n : ℕ}
    (S : Finset (BooleanSpace n)) (v : S → ℝ)
    (t : BooleanSpace n) : ℝ :=
  ∑ s : S, realPhase (s : BooleanSpace n) t * v s

/-- Squared Frobenius error of the canonical rank-one approximation. -/
def rankOneResidual {n : ℕ}
    (S T : Finset (BooleanSpace n)) (v : S → ℝ) : ℝ :=
  ∑ t : T, ∑ s : S,
    (realPhase (s : BooleanSpace n) (t : BooleanSpace n) -
      restrictedWalshApply S v t * v s) ^ 2

set_option maxHeartbeats 1000000 in
theorem rankOneResidual_eq {n : ℕ}
    (S T : Finset (BooleanSpace n)) (v : S → ℝ)
    (hv : ∑ s : S, v s ^ 2 = 1) :
    rankOneResidual S T v =
      (S.card : ℝ) * T.card -
        ∑ t : T, restrictedWalshApply S v t ^ 2 := by
  have hone (t : T) :
      (∑ s : S,
        (realPhase (s : BooleanSpace n) (t : BooleanSpace n) -
          restrictedWalshApply S v t * v s) ^ 2) =
        (S.card : ℝ) - restrictedWalshApply S v t ^ 2 := by
    calc
      (∑ s : S,
        (realPhase (s : BooleanSpace n) (t : BooleanSpace n) -
          restrictedWalshApply S v t * v s) ^ 2) =
          ∑ s : S,
            (1 - 2 * restrictedWalshApply S v t *
                (realPhase (s : BooleanSpace n) (t : BooleanSpace n) * v s) +
              restrictedWalshApply S v t ^ 2 * v s ^ 2) := by
        apply Finset.sum_congr rfl
        intro s hs
        have hp :
            realPhase (s : BooleanSpace n) (t : BooleanSpace n) ^ 2 = 1 :=
          realPhase_sq (n := n) (s : BooleanSpace n) (t : BooleanSpace n)
        nlinarith
      _ = (S.card : ℝ) -
          2 * restrictedWalshApply S v t *
            restrictedWalshApply S v t +
          restrictedWalshApply S v t ^ 2 * 1 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
          ← Finset.mul_sum, restrictedWalshApply, hv]
        have hcard : (Finset.univ : Finset S).card = S.card := by simp
        rw [hcard]
      _ = (S.card : ℝ) - restrictedWalshApply S v t ^ 2 := by ring
  rw [rankOneResidual]
  simp_rw [hone]
  rw [Finset.sum_sub_distrib]
  simp
  ring

/-- A deterministic sign used to round a real rank-one factor. -/
def realSign (x : ℝ) : ℝ :=
  if x < 0 then -1 else 1

@[simp]
theorem realSign_sq (x : ℝ) : realSign x ^ 2 = 1 := by
  simp only [realSign]
  split_ifs <;> norm_num

theorem one_le_sq_sub_of_sign_mismatch
    {m a b : ℝ} (hm : m = 1 ∨ m = -1)
    (hbad : m ≠ realSign a * realSign b) :
    1 ≤ (m - a * b) ^ 2 := by
  have hsign : m * (a * b) ≤ 0 := by
    rcases hm with rfl | rfl
    · by_cases ha : a < 0 <;> by_cases hb : b < 0
      · simp [realSign, ha, hb] at hbad
      · have hab : a * b ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg ha.le (le_of_not_gt hb)
        simpa using hab
      · have hab : a * b ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_not_gt ha) hb.le
        simpa using hab
      · simp [realSign, ha, hb] at hbad
    · by_cases ha : a < 0 <;> by_cases hb : b < 0
      · have hab : 0 ≤ a * b :=
          mul_nonneg_of_nonpos_of_nonpos ha.le hb.le
        nlinarith
      · simp [realSign, ha, hb] at hbad
      · simp [realSign, ha, hb] at hbad
      · have hab : 0 ≤ a * b :=
          mul_nonneg (le_of_not_gt ha) (le_of_not_gt hb)
        nlinarith
  rcases hm with rfl | rfl <;> nlinarith [sq_nonneg (a * b)]

/-- Entries where the Walsh sign disagrees with the rounded rank-one pattern. -/
def mismatchEntries {n : ℕ}
    (S T : Finset (BooleanSpace n)) (v : S → ℝ) :
    Finset (T × S) :=
  Finset.univ.filter fun p ↦
    realPhase (p.2 : BooleanSpace n) (p.1 : BooleanSpace n) ≠
      realSign (restrictedWalshApply S v p.1) * realSign (v p.2)

set_option maxHeartbeats 1000000 in
theorem mismatchEntries_card_le_residual {n : ℕ}
    (S T : Finset (BooleanSpace n)) (v : S → ℝ) :
    ((mismatchEntries S T v).card : ℝ) ≤ rankOneResidual S T v := by
  calc
    ((mismatchEntries S T v).card : ℝ) =
        ∑ p : T × S,
          if realPhase (p.2 : BooleanSpace n) (p.1 : BooleanSpace n) ≠
              realSign (restrictedWalshApply S v p.1) * realSign (v p.2)
          then 1 else 0 := by
      calc
        ((mismatchEntries S T v).card : ℝ) =
            ∑ p ∈ mismatchEntries S T v, (1 : ℝ) := by simp
        _ = ∑ p : T × S,
            if realPhase (p.2 : BooleanSpace n) (p.1 : BooleanSpace n) ≠
                realSign (restrictedWalshApply S v p.1) * realSign (v p.2)
            then 1 else 0 := by
          simp only [mismatchEntries, Finset.sum_filter]
    _ ≤ ∑ p : T × S,
        (realPhase (p.2 : BooleanSpace n) (p.1 : BooleanSpace n) -
          restrictedWalshApply S v p.1 * v p.2) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hbad :
          realPhase (p.2 : BooleanSpace n) (p.1 : BooleanSpace n) ≠
            realSign (restrictedWalshApply S v p.1) * realSign (v p.2)
      · simp only [if_pos hbad]
        apply one_le_sq_sub_of_sign_mismatch
        · rcases zmod_two_eq_zero_or_one
              (dot (p.2 : BooleanSpace n) (p.1 : BooleanSpace n)) with h | h
          · exact Or.inl (by simp [realPhase, h])
          · exact Or.inr (by simp [realPhase, h])
        · exact hbad
      · simp only [if_neg hbad]
        positivity
    _ = rankOneResidual S T v := by
      rw [rankOneResidual, Fintype.sum_prod_type]

theorem real_four_point_identity {n : ℕ}
    (t t₀ s s₀ : BooleanSpace n) :
    realPhase s t * realPhase s₀ t *
        realPhase s t₀ * realPhase s₀ t₀ =
      realPhase (s + s₀) (t + t₀) := by
  simp only [realPhase_add_left, realPhase_add_right]
  ring

def entryMismatch {n : ℕ}
    (S : Finset (BooleanSpace n)) (v : S → ℝ)
    (t : BooleanSpace n) (s : S) : Prop :=
  realPhase s t ≠
    realSign (restrictedWalshApply S v t) * realSign (v s)

/--
If the translated pair `(s+s₀,t+t₀)` is nonorthogonal, at least one corner
of its Walsh rectangle disagrees with the rounded rank-one sign pattern.
-/
theorem rectangle_bad_implies_entryMismatch {n : ℕ}
    (S T : Finset (BooleanSpace n)) (v : S → ℝ)
    (s s₀ : S) (t t₀ : T)
    (hbad : dot ((s : BooleanSpace n) + (s₀ : BooleanSpace n))
      ((t : BooleanSpace n) + (t₀ : BooleanSpace n)) = 1) :
    entryMismatch S v t s ∨
      entryMismatch S v t s₀ ∨
      entryMismatch S v t₀ s ∨
      entryMismatch S v t₀ s₀ := by
  by_contra hnone
  have h₁ : ¬entryMismatch S v t s := by
    intro h
    exact hnone (Or.inl h)
  have h₂ : ¬entryMismatch S v t s₀ := by
    intro h
    exact hnone (Or.inr (Or.inl h))
  have h₃ : ¬entryMismatch S v t₀ s := by
    intro h
    exact hnone (Or.inr (Or.inr (Or.inl h)))
  have h₄ : ¬entryMismatch S v t₀ s₀ := by
    intro h
    exact hnone (Or.inr (Or.inr (Or.inr h)))
  simp only [entryMismatch, not_ne_iff] at h₁ h₂ h₃ h₄
  have hprod := real_four_point_identity
    (t : BooleanSpace n) (t₀ : BooleanSpace n)
    (s : BooleanSpace n) (s₀ : BooleanSpace n)
  have hleft :
      realPhase (s : BooleanSpace n) t *
          realPhase (s₀ : BooleanSpace n) t *
          realPhase (s : BooleanSpace n) t₀ *
          realPhase (s₀ : BooleanSpace n) t₀ = 1 := by
    rw [h₁, h₂, h₃, h₄]
    calc
      (realSign (restrictedWalshApply S v t) * realSign (v s)) *
          (realSign (restrictedWalshApply S v t) * realSign (v s₀)) *
          (realSign (restrictedWalshApply S v t₀) * realSign (v s)) *
          (realSign (restrictedWalshApply S v t₀) * realSign (v s₀)) =
          realSign (restrictedWalshApply S v t) ^ 2 *
            realSign (restrictedWalshApply S v t₀) ^ 2 *
            realSign (v s) ^ 2 * realSign (v s₀) ^ 2 := by ring
      _ = 1 := by simp
  have hright :
      realPhase ((s : BooleanSpace n) + (s₀ : BooleanSpace n))
        ((t : BooleanSpace n) + (t₀ : BooleanSpace n)) = -1 :=
    realPhase_eq_neg_one_iff.mpr hbad
  rw [hleft, hright] at hprod
  norm_num at hprod

/-- The `0`/`1` indicator of a proposition. -/
def propIndicator (P : Prop) [Decidable P] : ℕ :=
  if P then 1 else 0

/-- Number of bad translated pairs for a fixed choice of anchors. -/
def rectangleBadCount {n : ℕ}
    (S T : Finset (BooleanSpace n)) (s₀ : S) (t₀ : T) : ℕ :=
  ((Finset.univ : Finset (S × T)).filter fun p ↦
    dot ((p.1 : BooleanSpace n) + (s₀ : BooleanSpace n))
      ((p.2 : BooleanSpace n) + (t₀ : BooleanSpace n)) = 1).card

theorem mismatchEntries_card_eq_sum {n : ℕ}
    (S T : Finset (BooleanSpace n)) (v : S → ℝ) :
    (mismatchEntries S T v).card =
      ∑ t : T, ∑ s : S, propIndicator (entryMismatch S v t s) := by
  calc
    (mismatchEntries S T v).card =
        ∑ p ∈ mismatchEntries S T v, 1 :=
      Finset.card_eq_sum_ones _
    _ = ∑ p : T × S,
        propIndicator (entryMismatch S v p.1 p.2) := by
      simp only [mismatchEntries, Finset.sum_filter, propIndicator,
        entryMismatch]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases h :
          realPhase (p.2 : BooleanSpace n) (p.1 : BooleanSpace n) ≠
            realSign (restrictedWalshApply S v p.1) * realSign (v p.2)
      · simp [h, propIndicator, entryMismatch]
      · simp [h, propIndicator, entryMismatch]
    _ = ∑ t : T, ∑ s : S,
        propIndicator (entryMismatch S v t s) := by
      rw [Fintype.sum_prod_type]

theorem rectangleBadCount_eq_sum {n : ℕ}
    (S T : Finset (BooleanSpace n)) (s₀ : S) (t₀ : T) :
    rectangleBadCount S T s₀ t₀ =
      ∑ s : S, ∑ t : T,
        propIndicator
          (dot ((s : BooleanSpace n) + (s₀ : BooleanSpace n))
            ((t : BooleanSpace n) + (t₀ : BooleanSpace n)) = 1) := by
  calc
    rectangleBadCount S T s₀ t₀ =
        ∑ p ∈
          ((Finset.univ : Finset (S × T)).filter fun p ↦
            dot ((p.1 : BooleanSpace n) + (s₀ : BooleanSpace n))
              ((p.2 : BooleanSpace n) + (t₀ : BooleanSpace n)) = 1), 1 :=
      Finset.card_eq_sum_ones _
    _ = ∑ p : S × T,
        propIndicator
          (dot ((p.1 : BooleanSpace n) + (s₀ : BooleanSpace n))
            ((p.2 : BooleanSpace n) + (t₀ : BooleanSpace n)) = 1) := by
      simp only [Finset.sum_filter, propIndicator]
    _ = ∑ s : S, ∑ t : T,
        propIndicator
          (dot ((s : BooleanSpace n) + (s₀ : BooleanSpace n))
            ((t : BooleanSpace n) + (t₀ : BooleanSpace n)) = 1) := by
      rw [Fintype.sum_prod_type]

theorem rectangle_indicator_le_mismatch_indicators {n : ℕ}
    (S T : Finset (BooleanSpace n)) (v : S → ℝ)
    (s s₀ : S) (t t₀ : T) :
    propIndicator
        (dot ((s : BooleanSpace n) + (s₀ : BooleanSpace n))
          ((t : BooleanSpace n) + (t₀ : BooleanSpace n)) = 1) ≤
      propIndicator (entryMismatch S v t s) +
      propIndicator (entryMismatch S v t s₀) +
      propIndicator (entryMismatch S v t₀ s) +
      propIndicator (entryMismatch S v t₀ s₀) := by
  by_cases hbad :
      dot ((s : BooleanSpace n) + (s₀ : BooleanSpace n))
        ((t : BooleanSpace n) + (t₀ : BooleanSpace n)) = 1
  · have hcorner :=
      rectangle_bad_implies_entryMismatch S T v s s₀ t t₀ hbad
    rcases hcorner with h | h | h | h <;>
      simp [propIndicator, hbad, h] <;> omega
  · simp [propIndicator, hbad]

set_option maxHeartbeats 1000000 in
theorem sum_rectangleBadCount_le {n : ℕ}
    (S T : Finset (BooleanSpace n)) (v : S → ℝ) :
    (∑ s₀ : S, ∑ t₀ : T, rectangleBadCount S T s₀ t₀) ≤
      4 * (mismatchEntries S T v).card * S.card * T.card := by
  rw [show (∑ s₀ : S, ∑ t₀ : T, rectangleBadCount S T s₀ t₀) =
      ∑ s₀ : S, ∑ t₀ : T, ∑ s : S, ∑ t : T,
        propIndicator
          (dot ((s : BooleanSpace n) + (s₀ : BooleanSpace n))
            ((t : BooleanSpace n) + (t₀ : BooleanSpace n)) = 1) by
    simp_rw [rectangleBadCount_eq_sum]]
  calc
    (∑ s₀ : S, ∑ t₀ : T, ∑ s : S, ∑ t : T,
      propIndicator
        (dot ((s : BooleanSpace n) + (s₀ : BooleanSpace n))
          ((t : BooleanSpace n) + (t₀ : BooleanSpace n)) = 1)) ≤
        ∑ s₀ : S, ∑ t₀ : T, ∑ s : S, ∑ t : T,
          (propIndicator (entryMismatch S v t s) +
          propIndicator (entryMismatch S v t s₀) +
          propIndicator (entryMismatch S v t₀ s) +
          propIndicator (entryMismatch S v t₀ s₀)) := by
      apply Finset.sum_le_sum
      intro s₀ hs₀
      apply Finset.sum_le_sum
      intro t₀ ht₀
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro t ht
      exact rectangle_indicator_le_mismatch_indicators S T v s s₀ t t₀
    _ = 4 * (mismatchEntries S T v).card * S.card * T.card := by
      let M : ℕ :=
        ∑ t : T, ∑ s : S, propIndicator (entryMismatch S v t s)
      have hM : M = (mismatchEntries S T v).card :=
        (mismatchEntries_card_eq_sum S T v).symm
      have h₁ :
          (∑ s₀ : S, ∑ t₀ : T, ∑ s : S, ∑ t : T,
            propIndicator (entryMismatch S v t s)) =
            S.card * T.card * M := by
        simp [M]
        rw [Finset.sum_comm]
        ring
      have h₂ :
          (∑ s₀ : S, ∑ t₀ : T, ∑ s : S, ∑ t : T,
            propIndicator (entryMismatch S v t s₀)) =
            S.card * T.card * M := by
        simp [M]
        rw [Finset.sum_comm]
        rw [← Finset.mul_sum]
        rw [← Finset.mul_sum]
        ring
      have h₃ :
          (∑ s₀ : S, ∑ t₀ : T, ∑ s : S, ∑ t : T,
            propIndicator (entryMismatch S v t₀ s)) =
            S.card * T.card * M := by
        simp [M]
        rw [mul_assoc]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mul_sum]
      have h₄ :
          (∑ s₀ : S, ∑ t₀ : T, ∑ s : S, ∑ t : T,
            propIndicator (entryMismatch S v t₀ s₀)) =
            S.card * T.card * M := by
        simp [M]
        rw [Finset.sum_comm]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
      simp_rw [Finset.sum_add_distrib]
      rw [h₁, h₂, h₃, h₄, hM]
      ring

theorem exists_anchors_rectangleBadCount_le {n : ℕ}
    (S T : Finset (BooleanSpace n)) (v : S → ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    ∃ s₀ : S, ∃ t₀ : T,
      rectangleBadCount S T s₀ t₀ ≤
        4 * (mismatchEntries S T v).card := by
  let F : S × T → ℕ := fun p ↦ rectangleBadCount S T p.1 p.2
  let C : ℕ := 4 * (mismatchEntries S T v).card
  have hsum :
      (∑ p : S × T, F p) ≤ ∑ _p : S × T, C := by
    rw [Fintype.sum_prod_type]
    have htotal := sum_rectangleBadCount_le S T v
    simp only [F, C]
    calc
      (∑ x : S, ∑ x_1 : T, rectangleBadCount S T x x_1) ≤
          4 * (mismatchEntries S T v).card * S.card * T.card :=
        htotal
      _ = (Fintype.card (S × T)) *
          (4 * (mismatchEntries S T v).card) := by
        simp [Fintype.card_prod]
        ring
      _ = ∑ _p : S × T, 4 * (mismatchEntries S T v).card := by
        simp
  have huniv : (Finset.univ : Finset (S × T)).Nonempty := by
    obtain ⟨s, hs⟩ := hS
    obtain ⟨t, ht⟩ := hT
    exact ⟨⟨⟨s, hs⟩, ⟨t, ht⟩⟩, Finset.mem_univ _⟩
  obtain ⟨p, hp, hple⟩ :=
    Finset.exists_le_of_sum_le
      (s := (Finset.univ : Finset (S × T)))
      (f := F) (g := fun _ ↦ C) huniv (by simpa using hsum)
  exact ⟨p.1, p.2, hple⟩

/-- Translation of a finite set in the Boolean vector space. -/
def translateFinset {n : ℕ}
    (S : Finset (BooleanSpace n)) (a : BooleanSpace n) :
    Finset (BooleanSpace n) :=
  S.image fun x ↦ x + a

@[simp]
theorem card_translateFinset {n : ℕ}
    (S : Finset (BooleanSpace n)) (a : BooleanSpace n) :
    (translateFinset S a).card = S.card := by
  exact Finset.card_image_of_injective S (add_left_injective a)

theorem zero_mem_translateFinset {n : ℕ}
    {S : Finset (BooleanSpace n)} {a : BooleanSpace n}
    (ha : a ∈ S) :
    0 ∈ translateFinset S a := by
  exact Finset.mem_image.mpr ⟨a, ha, add_self_eq_zero a⟩

theorem badPairCount_translate_eq_rectangleBadCount {n : ℕ}
    (S T : Finset (BooleanSpace n)) (s₀ : S) (t₀ : T) :
    badPairCount
        (translateFinset S s₀) (translateFinset T t₀) =
      rectangleBadCount S T s₀ t₀ := by
  rw [rectangleBadCount_eq_sum]
  conv_rhs => rw [Finset.sum_comm]
  have hR :
      (∑ t : T, ∑ s : S,
        propIndicator
          (dot ((s : BooleanSpace n) + (s₀ : BooleanSpace n))
            ((t : BooleanSpace n) + (t₀ : BooleanSpace n)) = 1)) =
      ∑ t ∈ T, ∑ s ∈ S,
        propIndicator
          (dot (s + (s₀ : BooleanSpace n))
            (t + (t₀ : BooleanSpace n)) = 1) := by
    calc
      (∑ t : T, ∑ s : S,
        propIndicator
          (dot ((s : BooleanSpace n) + (s₀ : BooleanSpace n))
            ((t : BooleanSpace n) + (t₀ : BooleanSpace n)) = 1)) =
          ∑ t : T, ∑ s ∈ S,
            propIndicator
              (dot (s + (s₀ : BooleanSpace n))
                ((t : BooleanSpace n) + (t₀ : BooleanSpace n)) = 1) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact (Finset.sum_subtype (p := fun s ↦ s ∈ S) S
          (by simp) (fun s ↦ propIndicator
            (dot (s + (s₀ : BooleanSpace n))
              ((t : BooleanSpace n) + (t₀ : BooleanSpace n)) = 1))).symm
      _ = ∑ t ∈ T, ∑ s ∈ S,
          propIndicator
            (dot (s + (s₀ : BooleanSpace n))
              (t + (t₀ : BooleanSpace n)) = 1) := by
        exact (Finset.sum_subtype (p := fun t ↦ t ∈ T) T
          (by simp) (fun t ↦ ∑ s ∈ S, propIndicator
            (dot (s + (s₀ : BooleanSpace n))
              (t + (t₀ : BooleanSpace n)) = 1))).symm
  rw [hR]
  simp only [badPairCount, badCount, translateFinset]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.card_eq_sum_ones]
    rw [Finset.sum_filter]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro s hs
      by_cases h :
          dot (s + (s₀ : BooleanSpace n))
            (t + (t₀ : BooleanSpace n)) = 1
      · simp [propIndicator, h]
      · simp [propIndicator, h]
    · exact (add_left_injective (s₀ : BooleanSpace n)).injOn
  · exact (add_left_injective (t₀ : BooleanSpace n)).injOn

/--
Support inverse theorem from a real unit vector that nearly saturates the
restricted Walsh matrix.
-/
theorem support_inverse_of_real_witness {n : ℕ}
    (S T : Finset (BooleanSpace n)) (v : S → ℝ) {q : ℝ}
    (hq0 : 0 < q) (hq : q ≤ 1 / 100)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hv : ∑ s : S, v s ^ 2 = 1)
    (henergy :
      (1 - q ^ 2 / 16) * Fintype.card (BooleanSpace n) ≤
        ∑ t : T, restrictedWalshApply S v t ^ 2)
    (hproduct :
      (S.card : ℝ) * T.card ≤
        (1 + q ^ 2 / 16) * Fintype.card (BooleanSpace n)) :
    ∃ s₀ : S, ∃ t₀ : T,
      ∃ L : Submodule (ZMod 2) (BooleanSpace n),
        (((translateFinset S s₀ ∆
            submodulePoints (perp L)).card : ℝ) ≤ 5 * q * S.card) ∧
        (((translateFinset T t₀ ∆
            submodulePoints L).card : ℝ) ≤ 12 * q * T.card) := by
  let N : ℝ := Fintype.card (BooleanSpace n)
  have hresEq := rankOneResidual_eq S T v hv
  have hresNonneg : 0 ≤ rankOneResidual S T v := by
    apply Finset.sum_nonneg
    intro t ht
    apply Finset.sum_nonneg
    intro s hs
    positivity
  have hresUpper :
      rankOneResidual S T v ≤ q ^ 2 / 8 * N := by
    dsimp [N]
    nlinarith
  have hmismatch :
      ((mismatchEntries S T v).card : ℝ) ≤
        q ^ 2 / 8 * N := by
    exact (mismatchEntries_card_le_residual S T v).trans hresUpper
  obtain ⟨s₀, t₀, hanchor⟩ :=
    exists_anchors_rectangleBadCount_le S T v hS hT
  let A := translateFinset S s₀
  let B := translateFinset T t₀
  have hAcard : A.card = S.card := by simp [A]
  have hBcard : B.card = T.card := by simp [B]
  have hA : A.Nonempty := by
    obtain ⟨s, hs⟩ := hS
    exact ⟨s + (s₀ : BooleanSpace n),
      Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩
  have hzeroB : 0 ∈ B := by
    exact zero_mem_translateFinset t₀.property
  have hprodLower :
      (1 - q ^ 2 / 16) * N ≤ (S.card : ℝ) * T.card := by
    dsimp [N] at hresEq henergy ⊢
    nlinarith
  have hsat :
      (1 - q) * Fintype.card (BooleanSpace n) ≤
        (A.card : ℝ) * B.card := by
    rw [hAcard, hBcard]
    dsimp [N] at hprodLower
    have hqsmall : q ^ 2 / 16 ≤ q := by
      nlinarith [sq_nonneg q]
    nlinarith
  have hanchorR :
      (rectangleBadCount S T s₀ t₀ : ℝ) ≤
        4 * (mismatchEntries S T v).card := by
    exact_mod_cast hanchor
  have hbadN :
      (rectangleBadCount S T s₀ t₀ : ℝ) ≤ q ^ 2 / 2 * N := by
    nlinarith
  have hhalfN :
      q ^ 2 / 2 * N ≤ q ^ 2 * ((S.card : ℝ) * T.card) := by
    have hhalf : (1 / 2 : ℝ) ≤ 1 - q ^ 2 / 16 := by
      nlinarith [sq_nonneg q]
    have hNnonneg : 0 ≤ N := by positivity
    have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
    calc
      q ^ 2 / 2 * N =
          q ^ 2 * ((1 / 2 : ℝ) * N) := by ring
      _ ≤ q ^ 2 * ((1 - q ^ 2 / 16) * N) := by
        gcongr
      _ ≤ q ^ 2 * ((S.card : ℝ) * T.card) := by
        gcongr
  have hbadAB :
      (badPairCount A B : ℝ) ≤ q ^ 2 * A.card * B.card := by
    rw [show badPairCount A B = rectangleBadCount S T s₀ t₀ by
      simpa [A, B] using
        badPairCount_translate_eq_rectangleBadCount S T s₀ t₀]
    rw [hAcard, hBcard]
    nlinarith
  obtain ⟨L, hLA, hLB⟩ :=
    saturated_almost_orthogonality A B (q := q)
      hq0 hq hA hzeroB hsat hbadAB
  exact ⟨s₀, t₀, L, by simpa [A, hAcard] using hLA,
    by simpa [B, hBcard] using hLB⟩

end

end RobustInverseUncertainty
