/-
Copyright (c) 2026 Galois, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Marios Georgiou
-/

import LeanFormalization.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Finset.SymmDiff

/-!
# Quantitative combinatorics for robust inverse uncertainty

This file develops the real Walsh counting identities used in the robust
almost-orthogonality argument.
-/

namespace RobustInverseUncertainty

noncomputable section

open scoped BigOperators Finset Pointwise symmDiff
attribute [local instance] Classical.propDecidable

/-- The real Walsh sign associated to the standard Boolean pairing. -/
def realPhase {n : ℕ} (x y : BooleanSpace n) : ℝ :=
  if dot x y = 0 then 1 else -1

@[simp]
theorem realPhase_zero_left {n : ℕ} (y : BooleanSpace n) :
    realPhase 0 y = 1 := by
  simp [realPhase]

@[simp]
theorem realPhase_zero_right {n : ℕ} (x : BooleanSpace n) :
    realPhase x 0 = 1 := by
  simp [realPhase]

@[simp]
theorem realPhase_eq_one_iff {n : ℕ} {x y : BooleanSpace n} :
    realPhase x y = 1 ↔ dot x y = 0 := by
  simp only [realPhase]
  split_ifs with h
  · simp [h]
  · norm_num [h]

@[simp]
theorem realPhase_eq_neg_one_iff {n : ℕ} {x y : BooleanSpace n} :
    realPhase x y = -1 ↔ dot x y = 1 := by
  rcases zmod_two_eq_zero_or_one (dot x y) with h | h
  · simp [realPhase, h, show (1 : ℝ) ≠ -1 by norm_num]
  · simp [realPhase, h]

@[simp]
theorem realPhase_sq {n : ℕ} (x y : BooleanSpace n) :
    realPhase x y ^ 2 = 1 := by
  simp only [realPhase]
  split_ifs <;> norm_num

@[simp]
theorem ofReal_realPhase {n : ℕ} (x y : BooleanSpace n) :
    (realPhase x y : ℂ) = phase x y := by
  simp only [realPhase, phase, bitPhase]
  split_ifs <;> norm_num

@[simp]
theorem realPhase_add_left {n : ℕ} (x y z : BooleanSpace n) :
    realPhase (x + y) z = realPhase x z * realPhase y z := by
  apply Complex.ofReal_injective
  calc
    (realPhase (x + y) z : ℂ) = phase (x + y) z :=
      ofReal_realPhase (x + y) z
    _ = phase x z * phase y z := phase_add_left x y z
    _ = (realPhase x z * realPhase y z : ℝ) := by
      rw [Complex.ofReal_mul, ofReal_realPhase, ofReal_realPhase]

@[simp]
theorem realPhase_add_right {n : ℕ} (x y z : BooleanSpace n) :
    realPhase x (y + z) = realPhase x y * realPhase x z := by
  apply Complex.ofReal_injective
  calc
    (realPhase x (y + z) : ℂ) = phase x (y + z) :=
      ofReal_realPhase x (y + z)
    _ = phase x y * phase x z := phase_add_right x y z
    _ = (realPhase x y * realPhase x z : ℝ) := by
      rw [Complex.ofReal_mul, ofReal_realPhase, ofReal_realPhase]

theorem realPhase_comm {n : ℕ} (x y : BooleanSpace n) :
    realPhase x y = realPhase y x := by
  simp [realPhase, dot_comm]

/-- The real Walsh sign as a bundled additive character. -/
def realPhaseChar {n : ℕ} (y : BooleanSpace n) :
    AddChar (BooleanSpace n) ℝ where
  toFun x := realPhase x y
  map_zero_eq_one' := realPhase_zero_left y
  map_add_eq_mul' := fun x z ↦ realPhase_add_left x z y

@[simp]
theorem realPhaseChar_apply {n : ℕ} (x y : BooleanSpace n) :
    realPhaseChar y x = realPhase x y := rfl

@[simp]
theorem realPhaseChar_eq_zero_iff {n : ℕ} (y : BooleanSpace n) :
    realPhaseChar y = 0 ↔ y = 0 := by
  constructor
  · intro h
    funext i
    have hi := DFunLike.congr_fun h (Pi.single i (1 : ZMod 2))
    change realPhase (Pi.single i 1) y = 1 at hi
    simpa using (realPhase_eq_one_iff.mp hi)
  · rintro rfl
    ext x
    simp [realPhaseChar]

/-- Orthogonality of the real Walsh characters on the Boolean cube. -/
theorem sum_realPhase_eq_ite {n : ℕ} (y : BooleanSpace n) :
    ∑ x : BooleanSpace n, realPhase x y =
      if y = 0 then (Fintype.card (BooleanSpace n) : ℝ) else 0 := by
  simpa using AddChar.sum_eq_ite (realPhaseChar y)

/-- The unnormalized real Walsh sum of a finite set. -/
def realWalshSum {n : ℕ} (A : Finset (BooleanSpace n))
    (y : BooleanSpace n) : ℝ :=
  ∑ x ∈ A, realPhase x y

theorem realWalshSum_eq_card_sub_two_bad {n : ℕ}
    (A : Finset (BooleanSpace n)) (y : BooleanSpace n) :
    realWalshSum A y =
      (A.card : ℝ) -
        2 * ((A.filter fun x ↦ dot x y = 1).card : ℝ) := by
  classical
  rw [realWalshSum]
  calc
    (∑ x ∈ A, realPhase x y) =
        ∑ x ∈ A, (1 - 2 * if dot x y = 1 then 1 else 0 : ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      rcases zmod_two_eq_zero_or_one (dot x y) with h | h
      · simp [realPhase, h]
      · simp [realPhase, h]
        norm_num
    _ = (A.card : ℝ) -
        2 * ((A.filter fun x ↦ dot x y = 1).card : ℝ) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [← Finset.mul_sum]
      simp

theorem sum_realPhase_mul_realPhase {n : ℕ}
    (x z : BooleanSpace n) :
    ∑ y : BooleanSpace n, realPhase x y * realPhase z y =
      if x = z then (Fintype.card (BooleanSpace n) : ℝ) else 0 := by
  calc
    (∑ y : BooleanSpace n, realPhase x y * realPhase z y) =
        ∑ y : BooleanSpace n, realPhase y (x + z) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [realPhase_comm x y, realPhase_comm z y,
        ← realPhase_add_right]
    _ = if x + z = 0 then
          (Fintype.card (BooleanSpace n) : ℝ) else 0 :=
      sum_realPhase_eq_ite (x + z)
    _ = if x = z then
          (Fintype.card (BooleanSpace n) : ℝ) else 0 := by
      by_cases h : x = z
      · simp [h]
      · simp [h, add_eq_zero_iff_eq_neg, neg_eq_self]

/-- Parseval for an indicator, in unnormalized real Walsh coordinates. -/
theorem realWalshSum_parseval {n : ℕ}
    (A : Finset (BooleanSpace n)) :
    ∑ y : BooleanSpace n, realWalshSum A y ^ 2 =
      (Fintype.card (BooleanSpace n) : ℝ) * A.card := by
  classical
  calc
    (∑ y : BooleanSpace n, realWalshSum A y ^ 2) =
        ∑ y : BooleanSpace n, ∑ x ∈ A, ∑ z ∈ A,
          realPhase x y * realPhase z y := by
      simp only [realWalshSum, pow_two, Finset.sum_mul_sum]
    _ = ∑ x ∈ A, ∑ z ∈ A, ∑ y : BooleanSpace n,
          realPhase x y * realPhase z y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ x ∈ A, ∑ z ∈ A,
          if x = z then (Fintype.card (BooleanSpace n) : ℝ) else 0 := by
      simp_rw [sum_realPhase_mul_realPhase]
    _ = (Fintype.card (BooleanSpace n) : ℝ) * A.card := by
      simp
      ring

/-- Number of elements of `A` that pair nontrivially with `y`. -/
def badCount {n : ℕ} (A : Finset (BooleanSpace n))
    (y : BooleanSpace n) : ℕ :=
  (A.filter fun x ↦ dot x y = 1).card

/-- Number of nonorthogonal pairs in `A × B`. -/
def badPairCount {n : ℕ} (A B : Finset (BooleanSpace n)) : ℕ :=
  ∑ y ∈ B, badCount A y

@[simp]
theorem badCount_zero {n : ℕ} (A : Finset (BooleanSpace n)) :
    badCount A 0 = 0 := by
  simp [badCount]

theorem badCount_le_card {n : ℕ} (A : Finset (BooleanSpace n))
    (y : BooleanSpace n) :
    badCount A y ≤ A.card := by
  exact Finset.card_filter_le _ _

theorem badCount_add_le {n : ℕ} (A : Finset (BooleanSpace n))
    (y z : BooleanSpace n) :
    badCount A (y + z) ≤ badCount A y + badCount A z := by
  classical
  let Ay := A.filter fun x ↦ dot x y = 1
  let Az := A.filter fun x ↦ dot x z = 1
  have hsub :
      A.filter (fun x ↦ dot x (y + z) = 1) ⊆ Ay ∪ Az := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    simp only [Finset.mem_union, Finset.mem_filter, Ay, Az, hx.1, true_and]
    rw [dot_add_right] at hx
    rcases zmod_two_eq_zero_or_one (dot x y) with hy | hy <;>
      rcases zmod_two_eq_zero_or_one (dot x z) with hz | hz
    · simp [hy, hz] at hx
    · exact Or.inr hz
    · exact Or.inl hy
    · simp [hy, hz] at hx
  calc
    badCount A (y + z) ≤ (Ay ∪ Az).card :=
      Finset.card_le_card hsub
    _ ≤ Ay.card + Az.card := Finset.card_union_le _ _
    _ = badCount A y + badCount A z := rfl

/-- Elements of `B` whose bad count against `A` is at most `q |A|`. -/
def lowBiasSet {n : ℕ} (A B : Finset (BooleanSpace n)) (q : ℝ) :
    Finset (BooleanSpace n) :=
  B.filter fun y ↦ (badCount A y : ℝ) ≤ q * A.card

theorem lowBiasSet_subset_right {n : ℕ}
    (A B : Finset (BooleanSpace n)) (q : ℝ) :
    lowBiasSet A B q ⊆ B :=
  Finset.filter_subset _ _

theorem zero_mem_lowBiasSet {n : ℕ}
    (A B : Finset (BooleanSpace n)) {q : ℝ}
    (hzero : 0 ∈ B) (hq : 0 ≤ q) :
    0 ∈ lowBiasSet A B q := by
  simp [lowBiasSet, hzero]
  positivity

theorem badPairCount_eq_sum {n : ℕ}
    (A B : Finset (BooleanSpace n)) :
    (badPairCount A B : ℝ) =
      ∑ y ∈ B, (badCount A y : ℝ) := by
  simp [badPairCount]

/--
Finite Markov inequality for bad counts.  The denominator-free hypothesis is
`badPairCount A B ≤ q² |A| |B|`.
-/
theorem card_sdiff_lowBiasSet_le {n : ℕ}
    (A B : Finset (BooleanSpace n)) {q : ℝ}
    (hq : 0 ≤ q)
    (hbad :
      (badPairCount A B : ℝ) ≤ q ^ 2 * A.card * B.card) :
    ((B \ lowBiasSet A B q).card : ℝ) * q * A.card ≤
      q ^ 2 * A.card * B.card := by
  classical
  have heach : ∀ y ∈ B \ lowBiasSet A B q,
      q * (A.card : ℝ) ≤ badCount A y := by
    intro y hy
    simp only [Finset.mem_sdiff, lowBiasSet, Finset.mem_filter,
      not_and, not_le] at hy
    exact (hy.2 hy.1).le
  calc
    ((B \ lowBiasSet A B q).card : ℝ) * q * A.card =
        ∑ y ∈ B \ lowBiasSet A B q, q * (A.card : ℝ) := by
      simp [mul_assoc]
    _ ≤ ∑ y ∈ B \ lowBiasSet A B q, (badCount A y : ℝ) :=
      Finset.sum_le_sum fun y hy ↦ heach y hy
    _ ≤ ∑ y ∈ B, (badCount A y : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      intro y hyB hyDiff
      positivity
    _ = (badPairCount A B : ℝ) := (badPairCount_eq_sum A B).symm
    _ ≤ q ^ 2 * A.card * B.card := hbad

theorem card_lowBiasSet_lower {n : ℕ}
    (A B : Finset (BooleanSpace n)) {q : ℝ}
    (hq : 0 < q) (hA : A.Nonempty)
    (hbad :
      (badPairCount A B : ℝ) ≤ q ^ 2 * A.card * B.card) :
    (1 - q) * B.card ≤ (lowBiasSet A B q).card := by
  have hmarkov := card_sdiff_lowBiasSet_le A B hq.le hbad
  have hApos : (0 : ℝ) < A.card := by
    exact_mod_cast hA.card_pos
  have hqA : 0 < q * (A.card : ℝ) := mul_pos hq hApos
  have hdiff :
      ((B \ lowBiasSet A B q).card : ℝ) ≤ q * B.card := by
    nlinarith [hmarkov]
  have hpartition :
      ((B \ lowBiasSet A B q).card : ℝ) +
          (lowBiasSet A B q).card = B.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card
      (lowBiasSet_subset_right A B q)
  nlinarith

/-- Frequencies whose bad count against `A` is at most `2q |A|`. -/
def highBiasSet {n : ℕ} (A : Finset (BooleanSpace n)) (q : ℝ) :
    Finset (BooleanSpace n) :=
  Finset.univ.filter fun y ↦
    (badCount A y : ℝ) ≤ 2 * q * A.card

theorem lowBiasSet_add_self_subset_highBiasSet {n : ℕ}
    (A B : Finset (BooleanSpace n)) {q : ℝ} :
    lowBiasSet A B q + lowBiasSet A B q ⊆ highBiasSet A q := by
  classical
  intro w hw
  obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_add.mp hw
  simp only [lowBiasSet, Finset.mem_filter] at hy hz
  simp only [highBiasSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hadd := badCount_add_le A y z
  have haddR :
      (badCount A (y + z) : ℝ) ≤
        badCount A y + badCount A z := by
    exact_mod_cast hadd
  nlinarith

/-- Parseval bounds the number of frequencies with very high Walsh bias. -/
theorem highBiasSet_card_bound {n : ℕ}
    (A : Finset (BooleanSpace n)) {q : ℝ}
    (hq0 : 0 ≤ q) (hq4 : 4 * q ≤ 1) :
    ((highBiasSet A q).card : ℝ) *
        (((1 - 4 * q) * A.card) ^ 2) ≤
      Fintype.card (BooleanSpace n) * A.card := by
  classical
  let c : ℝ := (1 - 4 * q) * A.card
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hpoint : ∀ y ∈ highBiasSet A q,
      c ^ 2 ≤ realWalshSum A y ^ 2 := by
    intro y hy
    have hybad :
        (badCount A y : ℝ) ≤ 2 * q * A.card := by
      simpa [highBiasSet] using hy
    have hwalsh :
        c ≤ realWalshSum A y := by
      rw [realWalshSum_eq_card_sub_two_bad]
      dsimp [badCount] at hybad ⊢
      dsimp [c]
      nlinarith
    exact (sq_le_sq₀ hc (hc.trans hwalsh)).2 hwalsh
  calc
    ((highBiasSet A q).card : ℝ) * (((1 - 4 * q) * A.card) ^ 2) =
        ∑ y ∈ highBiasSet A q, c ^ 2 := by
      simp [c]
    _ ≤ ∑ y ∈ highBiasSet A q, realWalshSum A y ^ 2 :=
      Finset.sum_le_sum fun y hy ↦ hpoint y hy
    _ ≤ ∑ y : BooleanSpace n, realWalshSum A y ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (show highBiasSet A q ⊆ Finset.univ from Finset.subset_univ _)
      intro y hy hnot
      positivity
    _ = Fintype.card (BooleanSpace n) * A.card :=
      realWalshSum_parseval A

theorem lowBiasSet_sum_card_bound {n : ℕ}
    (A B : Finset (BooleanSpace n)) {q : ℝ}
    (hq0 : 0 ≤ q) (hq4 : 4 * q ≤ 1) :
    (((lowBiasSet A B q + lowBiasSet A B q).card : ℝ) *
        (((1 - 4 * q) * A.card) ^ 2)) ≤
      (Fintype.card (BooleanSpace n) : ℝ) * (A.card : ℝ) := by
  have hcard : (lowBiasSet A B q + lowBiasSet A B q).card ≤
      (highBiasSet A q).card :=
    Finset.card_le_card (lowBiasSet_add_self_subset_highBiasSet A B)
  have hnonneg : 0 ≤ (((1 - 4 * q) * (A.card : ℝ)) ^ 2) := sq_nonneg _
  calc
    (((lowBiasSet A B q + lowBiasSet A B q).card : ℝ) *
        (((1 - 4 * q) * A.card) ^ 2)) ≤
        ((highBiasSet A q).card : ℝ) *
          (((1 - 4 * q) * A.card) ^ 2) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hnonneg
    _ ≤ (Fintype.card (BooleanSpace n) : ℝ) * (A.card : ℝ) :=
      highBiasSet_card_bound A hq0 hq4

/-- The elementary numerical estimate behind the `< 3/2` threshold. -/
theorem numerical_doubling_bound
    {q a b N x y : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 100)
    (ha : 0 < a) (hy : 0 < y)
    (hN : (1 - q) * N ≤ a * b)
    (hx : (1 - q) * b ≤ x)
    (hparseval : y * (((1 - 4 * q) * a) ^ 2) ≤ N * a) :
    y < (3 / 2 : ℝ) * x := by
  have hq1 : 0 < 1 - q := by linarith
  have hcancelA :
      y * (1 - 4 * q) ^ 2 * a ≤ N := by
    apply (mul_le_mul_iff_left₀ ha).mp
    calc
      (y * (1 - 4 * q) ^ 2 * a) * a =
          y * (((1 - 4 * q) * a) ^ 2) := by ring
      _ ≤ N * a := hparseval
  have htoB :
      (1 - q) * (y * (1 - 4 * q) ^ 2) ≤ b := by
    apply (mul_le_mul_iff_right₀ ha).mp
    calc
      a * ((1 - q) * (y * (1 - 4 * q) ^ 2)) =
          (1 - q) * (y * (1 - 4 * q) ^ 2 * a) := by ring
      _ ≤ (1 - q) * N :=
        mul_le_mul_of_nonneg_left hcancelA hq1.le
      _ ≤ a * b := hN
  have hdenom :
      (1 - q) ^ 2 * (1 - 4 * q) ^ 2 * y ≤ x := by
    calc
      (1 - q) ^ 2 * (1 - 4 * q) ^ 2 * y =
          (1 - q) * ((1 - q) * (y * (1 - 4 * q) ^ 2)) := by ring
      _ ≤ (1 - q) * b :=
        mul_le_mul_of_nonneg_left htoB hq1.le
      _ ≤ x := hx
  have h19a : (19 / 20 : ℝ) ≤ 1 - q := by linarith
  have h19b : (19 / 20 : ℝ) ≤ 1 - 4 * q := by linarith
  have hsqa : (19 / 20 : ℝ) ^ 2 ≤ (1 - q) ^ 2 := by
    exact (sq_le_sq₀ (by norm_num) (by linarith)).2 h19a
  have hsqb : (19 / 20 : ℝ) ^ 2 ≤ (1 - 4 * q) ^ 2 := by
    exact (sq_le_sq₀ (by norm_num) (by linarith)).2 h19b
  have hprod :
      (19 / 20 : ℝ) ^ 4 ≤
        (1 - q) ^ 2 * (1 - 4 * q) ^ 2 := by
    calc
      (19 / 20 : ℝ) ^ 4 =
          (19 / 20 : ℝ) ^ 2 * (19 / 20 : ℝ) ^ 2 := by ring
      _ ≤ (1 - q) ^ 2 * (1 - 4 * q) ^ 2 :=
        mul_le_mul hsqa hsqb (sq_nonneg _) (sq_nonneg _)
  have htwoThirds :
      (2 / 3 : ℝ) <
        (1 - q) ^ 2 * (1 - 4 * q) ^ 2 := by
    have : (2 / 3 : ℝ) < (19 / 20 : ℝ) ^ 4 := by norm_num
    linarith
  have hstrict :
      (2 / 3 : ℝ) * y <
        ((1 - q) ^ 2 * (1 - 4 * q) ^ 2) * y :=
    mul_lt_mul_of_pos_right htwoThirds hy
  nlinarith

/--
For saturated almost-orthogonal sets, the low-bias subset has doubling
strictly below `3/2`.
-/
theorem lowBiasSet_doubling_lt_three_halves {n : ℕ}
    (A B : Finset (BooleanSpace n)) {q : ℝ}
    (hq0 : 0 < q) (hq : q ≤ 1 / 100)
    (hA : A.Nonempty) (hzero : 0 ∈ B)
    (hsat :
      (1 - q) * Fintype.card (BooleanSpace n) ≤
        (A.card : ℝ) * B.card)
    (hbad :
      (badPairCount A B : ℝ) ≤ q ^ 2 * A.card * B.card) :
    ((lowBiasSet A B q + lowBiasSet A B q).card : ℚ) <
      (3 / 2 : ℚ) * (lowBiasSet A B q).card := by
  let X := lowBiasSet A B q
  have hXzero : 0 ∈ X := zero_mem_lowBiasSet A B hzero hq0.le
  have hX : X.Nonempty := ⟨0, hXzero⟩
  have hXX : (X + X).Nonempty := by
    exact ⟨0, Finset.mem_add.mpr ⟨0, hXzero, 0, hXzero, by simp⟩⟩
  have hq4 : 4 * q ≤ 1 := by linarith
  have hx := card_lowBiasSet_lower A B hq0 hA hbad
  have hp := lowBiasSet_sum_card_bound A B hq0.le hq4
  have hreal :
      ((X + X).card : ℝ) < (3 / 2 : ℝ) * X.card := by
    apply numerical_doubling_bound
      (q := q) (a := (A.card : ℝ)) (b := (B.card : ℝ))
      (N := (Fintype.card (BooleanSpace n) : ℝ))
      (x := (X.card : ℝ)) (y := ((X + X).card : ℝ))
      hq0.le hq
    · exact_mod_cast hA.card_pos
    · exact_mod_cast hXX.card_pos
    · simpa [X] using hsat
    · simpa [X] using hx
    · simpa [X] using hp
  have hrat :
      (((X + X).card : ℚ) < (3 / 2 : ℚ) * X.card) := by
    have hreal' :
        (2 : ℝ) * (X + X).card < 3 * X.card := by
      nlinarith
    have hnat : 2 * (X + X).card < 3 * X.card := by
      exact_mod_cast hreal'
    have hrat' :
        (2 : ℚ) * (X + X).card < 3 * X.card := by
      exact_mod_cast hnat
    nlinarith
  simpa [X] using hrat

/--
The additive form of the sharp small-doubling theorem, specialized to the
Boolean vector space and returned as a `ZMod 2` submodule.
-/
theorem small_sumset_is_submodule {n : ℕ}
    (X : Finset (BooleanSpace n))
    (hX : ((X + X).card : ℚ) < (3 / 2 : ℚ) * X.card) :
    ∃ L : Submodule (ZMod 2) (BooleanSpace n),
      (L : Set (BooleanSpace n)) =
        (↑(X + X) : Set (BooleanSpace n)) := by
  classical
  let XM : Finset (Multiplicative (BooleanSpace n)) :=
    X.image Multiplicative.ofAdd
  have hprod :
      XM * XM = (X + X).image Multiplicative.ofAdd := by
    ext w
    simp only [Finset.mem_mul, Finset.mem_image, Finset.mem_add, XM]
    constructor
    · rintro ⟨wy, ⟨y, hy, rfl⟩, wz, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨y + z, ⟨y, hy, z, hz, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨y, hy, z, hz, rfl⟩, rfl⟩
      exact ⟨Multiplicative.ofAdd y, ⟨y, hy, rfl⟩,
        Multiplicative.ofAdd z, ⟨z, hz, rfl⟩, rfl⟩
  have hcardX : XM.card = X.card := by
    exact Finset.card_image_of_injective X Multiplicative.ofAdd.injective
  have hcardXX : (XM * XM).card = (X + X).card := by
    rw [hprod]
    exact Finset.card_image_of_injective (X + X)
      Multiplicative.ofAdd.injective
  have hXM :
      ((XM * XM).card : ℚ) < (3 / 2 : ℚ) * XM.card := by
    simpa [hcardX, hcardXX] using hX
  obtain ⟨H, hH⟩ := small_doubling_is_subgroup XM hXM
  let L : Submodule (ZMod 2) (BooleanSpace n) :=
    AddSubgroup.toZModSubmodule 2 H.toAddSubgroup'
  refine ⟨L, ?_⟩
  ext w
  change w ∈ AddSubgroup.toZModSubmodule 2 H.toAddSubgroup' ↔
    w ∈ X + X
  simp only [AddSubgroup.mem_toZModSubmodule, Subgroup.mem_toAddSubgroup']
  change Multiplicative.ofAdd w ∈
      (H : Set (Multiplicative (BooleanSpace n))) ↔ w ∈ X + X
  have hwH := Set.ext_iff.mp hH (Multiplicative.ofAdd w)
  rw [hwH]
  rw [← Finset.coe_mul]
  change Multiplicative.ofAdd w ∈ XM * XM ↔ w ∈ X + X
  rw [hprod]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨z, hz, hzw⟩
    have hzw' : z = w := Multiplicative.ofAdd.injective hzw
    simpa [hzw'] using hz
  · intro hw
    exact ⟨w, hw, rfl⟩

/-- The finite set of vectors in a Boolean subspace. -/
def submodulePoints {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n)) :
    Finset (BooleanSpace n) :=
  Finset.univ.filter fun x ↦ x ∈ L

@[simp]
theorem mem_submodulePoints {n : ℕ}
    {L : Submodule (ZMod 2) (BooleanSpace n)}
    {x : BooleanSpace n} :
    x ∈ submodulePoints L ↔ x ∈ L := by
  simp [submodulePoints]

@[simp]
theorem card_submodulePoints {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n)) :
    (submodulePoints L).card = Fintype.card L := by
  rw [Fintype.card_subtype]
  rfl

theorem submodulePoints_perp_card_mul {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n)) :
    (submodulePoints L).card * (submodulePoints (perp L)).card = 2 ^ n := by
  rw [card_submodulePoints, card_submodulePoints,
    Module.card_eq_pow_finrank (K := ZMod 2) (V := L),
    Module.card_eq_pow_finrank (K := ZMod 2) (V := perp L),
    ZMod.card, finrank_perp, ← pow_add]
  congr 1
  have hle : Module.finrank (ZMod 2) L ≤ n := by
    simpa using L.finrank_le
  exact Nat.add_sub_of_le hle

/-- The real Walsh character restricted to a Boolean subspace. -/
def restrictedRealPhaseChar {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n))
    (y : BooleanSpace n) : AddChar L ℝ :=
  (realPhaseChar y).compAddMonoidHom L.subtype.toAddMonoidHom

@[simp]
theorem restrictedRealPhaseChar_apply {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n))
    (y : BooleanSpace n) (x : L) :
    restrictedRealPhaseChar L y x = realPhase x y := rfl

@[simp]
theorem restrictedRealPhaseChar_eq_zero_iff {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n))
    (y : BooleanSpace n) :
    restrictedRealPhaseChar L y = 0 ↔ y ∈ perp L := by
  constructor
  · intro hzero
    rw [mem_perp_iff]
    intro x hx
    have hv := DFunLike.congr_fun hzero ⟨x, hx⟩
    change realPhase x y = 1 at hv
    exact realPhase_eq_one_iff.mp hv
  · intro hy
    rw [mem_perp_iff] at hy
    ext x
    simp [restrictedRealPhaseChar, realPhase, hy x x.property]

theorem sum_realPhase_submodule_eq_ite {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n))
    (y : BooleanSpace n) :
    ∑ x : L, realPhase x y =
      if y ∈ perp L then (Fintype.card L : ℝ) else 0 := by
  simpa using AddChar.sum_eq_ite (restrictedRealPhaseChar L y)

theorem realWalshSum_submodulePoints {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n))
    (y : BooleanSpace n) :
    realWalshSum (submodulePoints L) y =
      ∑ x : L, realPhase x y := by
  classical
  rw [realWalshSum]
  exact Finset.sum_subtype (p := fun x ↦ x ∈ L)
    (submodulePoints L) (by simp) (fun x ↦ realPhase x y)

/-- Outside `Lᗮ`, exactly half of `L` pairs nontrivially with `y`. -/
theorem two_mul_badCount_submodulePoints {n : ℕ}
    (L : Submodule (ZMod 2) (BooleanSpace n))
    (y : BooleanSpace n) (hy : y ∉ perp L) :
    2 * badCount (submodulePoints L) y =
      (submodulePoints L).card := by
  have hsum : realWalshSum (submodulePoints L) y = 0 := by
    rw [realWalshSum_submodulePoints, sum_realPhase_submodule_eq_ite]
    simp [hy]
  rw [realWalshSum_eq_card_sub_two_bad] at hsum
  dsimp [badCount] at hsum ⊢
  exact_mod_cast (by nlinarith : (2 : ℝ) *
    ((submodulePoints L).filter fun x ↦ dot x y = 1).card =
      (submodulePoints L).card)

theorem badPairCount_comm {n : ℕ}
    (A B : Finset (BooleanSpace n)) :
    badPairCount A B = badPairCount B A := by
  classical
  simp only [badPairCount, badCount, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [dot_comm]

/-- Removing points can reduce a bad count by at most the number removed. -/
theorem badCount_le_badCount_add_sdiff {n : ℕ}
    {X L : Finset (BooleanSpace n)} (hXL : X ⊆ L)
    (y : BooleanSpace n) :
    badCount L y ≤ badCount X y + (L \ X).card := by
  classical
  have hsub :
      L.filter (fun z ↦ dot z y = 1) ⊆
        X.filter (fun z ↦ dot z y = 1) ∪ (L \ X) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff] at hz ⊢
    by_cases hzX : z ∈ X
    · exact Or.inl ⟨hzX, hz.2⟩
    · exact Or.inr ⟨hz.1, hzX⟩
  calc
    badCount L y ≤
        (X.filter (fun z ↦ dot z y = 1) ∪ (L \ X)).card :=
      Finset.card_le_card hsub
    _ ≤ (X.filter fun z ↦ dot z y = 1).card + (L \ X).card :=
      Finset.card_union_le _ _
    _ = badCount X y + (L \ X).card := rfl

/-- A coarse upper bound for the high-bias sumset. -/
theorem numerical_sumset_upper
    {q a b N y : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 100)
    (ha : 0 < a) (hy : 0 ≤ y)
    (hN : (1 - q) * N ≤ a * b)
    (hparseval : y * (((1 - 4 * q) * a) ^ 2) ≤ N * a) :
    y ≤ (1 + 10 * q) * b := by
  have hq1 : 0 ≤ 1 - q := by linarith
  have hcancelA :
      y * (1 - 4 * q) ^ 2 * a ≤ N := by
    apply (mul_le_mul_iff_left₀ ha).mp
    calc
      (y * (1 - 4 * q) ^ 2 * a) * a =
          y * (((1 - 4 * q) * a) ^ 2) := by ring
      _ ≤ N * a := hparseval
  have htoB :
      (1 - q) * (y * (1 - 4 * q) ^ 2) ≤ b := by
    apply (mul_le_mul_iff_right₀ ha).mp
    calc
      a * ((1 - q) * (y * (1 - 4 * q) ^ 2)) =
          (1 - q) * (y * (1 - 4 * q) ^ 2 * a) := by ring
      _ ≤ (1 - q) * N :=
        mul_le_mul_of_nonneg_left hcancelA hq1
      _ ≤ a * b := hN
  have h3 : 0 ≤ 3 - 2 * q := by linarith
  have hpoly : 0 ≤ 8 * q ^ 2 * (3 - 2 * q) :=
    mul_nonneg (by positivity) h3
  have hdenom :
      1 - 9 * q ≤ (1 - q) * (1 - 4 * q) ^ 2 := by
    nlinarith
  have h90 : 0 ≤ 1 - 90 * q := by linarith
  have hscalePoly : 0 ≤ q * (1 - 90 * q) :=
    mul_nonneg hq0 h90
  have hscale : 1 ≤ (1 + 10 * q) * (1 - 9 * q) := by
    nlinarith
  calc
    y = 1 * y := by ring
    _ ≤ ((1 + 10 * q) * (1 - 9 * q)) * y :=
      mul_le_mul_of_nonneg_right hscale hy
    _ ≤ (1 + 10 * q) *
        ((1 - q) * (y * (1 - 4 * q) ^ 2)) := by
      have h10 : 0 ≤ 1 + 10 * q := by linarith
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ h10
      calc
        (1 - 9 * q) * y ≤
            ((1 - q) * (1 - 4 * q) ^ 2) * y :=
          mul_le_mul_of_nonneg_right hdenom hy
        _ = (1 - q) * (y * (1 - 4 * q) ^ 2) := by ring
    _ ≤ (1 + 10 * q) * b :=
      mul_le_mul_of_nonneg_left htoB (by linarith)

/-- Saturation and a large subgroup force its orthogonal complement to be small. -/
theorem numerical_perp_upper
    {q a b N x l c : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 100)
    (hb : 0 < b) (hc : 0 ≤ c)
    (hsat : (1 - q) * N ≤ a * b)
    (hx : (1 - q) * b ≤ x) (hxl : x ≤ l)
    (hcard : l * c = N) :
    c ≤ (1 + 3 * q) * a := by
  have hq1 : 0 ≤ 1 - q := by linarith
  have hlower : (1 - q) * b ≤ l := hx.trans hxl
  have hcN : c * ((1 - q) * b) ≤ N := by
    calc
      c * ((1 - q) * b) ≤ c * l :=
        mul_le_mul_of_nonneg_left hlower hc
      _ = N := by nlinarith [hcard]
  have hpreCancel :
      ((1 - q) ^ 2 * c) * b ≤ a * b := by
    calc
      ((1 - q) ^ 2 * c) * b =
          (1 - q) * (c * ((1 - q) * b)) := by ring
      _ ≤ (1 - q) * N :=
        mul_le_mul_of_nonneg_left hcN hq1
      _ ≤ a * b := hsat
  have hbase : (1 - q) ^ 2 * c ≤ a :=
    (mul_le_mul_iff_left₀ hb).mp hpreCancel
  have hinside : 0 ≤ 1 - 5 * q + 3 * q ^ 2 := by
    nlinarith [sq_nonneg q]
  have hscalePoly :
      0 ≤ q * (1 - 5 * q + 3 * q ^ 2) :=
    mul_nonneg hq0 hinside
  have hscale : 1 ≤ (1 + 3 * q) * (1 - q) ^ 2 := by
    nlinarith
  calc
    c = 1 * c := by ring
    _ ≤ ((1 + 3 * q) * (1 - q) ^ 2) * c :=
      mul_le_mul_of_nonneg_right hscale hc
    _ = (1 + 3 * q) * ((1 - q) ^ 2 * c) := by ring
    _ ≤ (1 + 3 * q) * a :=
      mul_le_mul_of_nonneg_left hbase (by linarith)

theorem card_symmDiff_le_sdiff_add_sdiff {α : Type*}
    [DecidableEq α] (S T : Finset α) :
    (S ∆ T).card ≤ (S \ T).card + (T \ S).card := by
  rw [Finset.symmDiff_def]
  exact Finset.card_union_le _ _

theorem card_symmDiff_le_of_common_subset {α : Type*}
    [DecidableEq α] {X S T : Finset α}
    (hXS : X ⊆ S) (hXT : X ⊆ T) :
    (S ∆ T).card ≤ (S \ X).card + (T \ X).card := by
  calc
    (S ∆ T).card ≤ (S \ T).card + (T \ S).card :=
      card_symmDiff_le_sdiff_add_sdiff S T
    _ ≤ (S \ X).card + (T \ X).card := by
      apply Nat.add_le_add
      · apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_sdiff] at hz ⊢
        exact ⟨hz.1, fun hzX ↦ hz.2 (hXT hzX)⟩
      · apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_sdiff] at hz ⊢
        exact ⟨hz.1, fun hzX ↦ hz.2 (hXS hzX)⟩

/--
Quantitative saturated almost-orthogonality on the Boolean cube.

The hypotheses use counts rather than probabilities, so no nonzero
denominators are hidden.  The constants are deliberately coarse.
-/
theorem saturated_almost_orthogonality {n : ℕ}
    (A B : Finset (BooleanSpace n)) {q : ℝ}
    (hq0 : 0 < q) (hq : q ≤ 1 / 100)
    (hA : A.Nonempty) (hzero : 0 ∈ B)
    (hsat :
      (1 - q) * Fintype.card (BooleanSpace n) ≤
        (A.card : ℝ) * B.card)
    (hbad :
      (badPairCount A B : ℝ) ≤ q ^ 2 * A.card * B.card) :
    ∃ L : Submodule (ZMod 2) (BooleanSpace n),
      (((A ∆ submodulePoints (perp L)).card : ℝ) ≤
          5 * q * A.card) ∧
      (((B ∆ submodulePoints L).card : ℝ) ≤
          12 * q * B.card) := by
  classical
  let X := lowBiasSet A B q
  have hXzero : 0 ∈ X := zero_mem_lowBiasSet A B hzero hq0.le
  have hXsubB : X ⊆ B := lowBiasSet_subset_right A B q
  have hdouble :=
    lowBiasSet_doubling_lt_three_halves A B hq0 hq hA hzero hsat hbad
  obtain ⟨L, hLset⟩ := small_sumset_is_submodule X (by simpa [X] using hdouble)
  let LF := submodulePoints L
  let C := submodulePoints (perp L)
  have hLF : LF = X + X := by
    ext z
    change z ∈ submodulePoints L ↔ z ∈ X + X
    rw [mem_submodulePoints]
    exact Set.ext_iff.mp hLset z
  have hXsubL : X ⊆ LF := by
    intro z hz
    rw [hLF]
    exact Finset.mem_add.mpr ⟨z, hz, 0, hXzero, by simp⟩
  have hApos : (0 : ℝ) < A.card := by
    exact_mod_cast hA.card_pos
  have hBnonempty : B.Nonempty := ⟨0, hzero⟩
  have hBpos : (0 : ℝ) < B.card := by
    exact_mod_cast hBnonempty.card_pos
  have hXlower :
      (1 - q) * (B.card : ℝ) ≤ X.card := by
    simpa [X] using card_lowBiasSet_lower A B hq0 hA hbad
  have hparseval :
      ((LF.card : ℝ) * (((1 - 4 * q) * A.card) ^ 2)) ≤
        (Fintype.card (BooleanSpace n) : ℝ) * A.card := by
    simpa [hLF, X] using
      lowBiasSet_sum_card_bound A B hq0.le (by linarith : 4 * q ≤ 1)
  have hLupper :
      (LF.card : ℝ) ≤ (1 + 10 * q) * B.card := by
    apply numerical_sumset_upper
      (q := q) (a := (A.card : ℝ)) (b := (B.card : ℝ))
      (N := (Fintype.card (BooleanSpace n) : ℝ))
      (y := (LF.card : ℝ)) hq0.le hq hApos
      (by positivity) hsat hparseval
  have hBX :
      ((B \ X).card : ℝ) = B.card - X.card := by
    rw [Finset.card_sdiff_of_subset hXsubB,
      Nat.cast_sub (Finset.card_mono hXsubB)]
  have hLX :
      ((LF \ X).card : ℝ) = LF.card - X.card := by
    rw [Finset.card_sdiff_of_subset hXsubL,
      Nat.cast_sub (Finset.card_mono hXsubL)]
  have hsymmB :
      ((B ∆ LF).card : ℝ) ≤ 12 * q * B.card := by
    have hcommon :=
      card_symmDiff_le_of_common_subset hXsubB hXsubL
    have hcommonR :
        ((B ∆ LF).card : ℝ) ≤
          (B \ X).card + (LF \ X).card := by
      exact_mod_cast hcommon
    nlinarith
  have hcardLC :
      (LF.card : ℝ) * C.card =
        Fintype.card (BooleanSpace n) := by
    have hnat := submodulePoints_perp_card_mul L
    rw [card_booleanSpace]
    exact_mod_cast (by simpa [LF, C] using hnat)
  have hCupper :
      (C.card : ℝ) ≤ (1 + 3 * q) * A.card := by
    apply numerical_perp_upper
      (q := q) (a := (A.card : ℝ)) (b := (B.card : ℝ))
      (N := (Fintype.card (BooleanSpace n) : ℝ))
      (x := (X.card : ℝ)) (l := (LF.card : ℝ))
      (c := (C.card : ℝ)) hq0.le hq hBpos (by positivity)
      hsat hXlower
    · exact_mod_cast Finset.card_mono hXsubL
    · exact hcardLC
  have hthirdR :
      (3 : ℝ) * (LF \ X).card ≤ X.card := by
    nlinarith
  have hthird :
      3 * (LF \ X).card ≤ X.card := by
    exact_mod_cast hthirdR
  have hpoint : ∀ a ∈ A \ C,
      X.card ≤ 3 * badCount X a := by
    intro a ha
    have haC : a ∉ C := (Finset.mem_sdiff.mp ha).2
    have haNot : a ∉ perp L := by
      simpa [C] using haC
    have hhalf := two_mul_badCount_submodulePoints L a haNot
    have hremove := badCount_le_badCount_add_sdiff hXsubL a
    have hLXnat := Finset.card_sdiff_add_card_eq_card hXsubL
    change 2 * badCount LF a = LF.card at hhalf
    omega
  have hsumLower :
      (A \ C).card * X.card ≤ 3 * badPairCount A X := by
    calc
      (A \ C).card * X.card =
          ∑ a ∈ A \ C, X.card := by simp
      _ ≤ ∑ a ∈ A \ C, 3 * badCount X a :=
        Finset.sum_le_sum fun a ha ↦ hpoint a ha
      _ ≤ ∑ a ∈ A, 3 * badCount X a := by
        apply Finset.sum_le_sum_of_subset Finset.sdiff_subset
      _ = 3 * badPairCount X A := by
        simp [badPairCount, Finset.mul_sum]
      _ = 3 * badPairCount A X := by
        rw [badPairCount_comm]
  have hbadAX :
      (badPairCount A X : ℝ) ≤ q ^ 2 * A.card * B.card := by
    calc
      (badPairCount A X : ℝ) ≤ badPairCount A B := by
        exact_mod_cast (show badPairCount A X ≤ badPairCount A B by
          apply Finset.sum_le_sum_of_subset hXsubB)
      _ ≤ q ^ 2 * A.card * B.card := hbad
  have hsumLowerR :
      ((A \ C).card : ℝ) * X.card ≤
        3 * q ^ 2 * A.card * B.card := by
    have hcast :
        ((A \ C).card : ℝ) * X.card ≤
          3 * (badPairCount A X : ℝ) := by
      exact_mod_cast hsumLower
    nlinarith
  have hpreCancel :
      (((A \ C).card : ℝ) * (1 - q)) * B.card ≤
        (3 * q ^ 2 * A.card) * B.card := by
    calc
      (((A \ C).card : ℝ) * (1 - q)) * B.card =
          ((A \ C).card : ℝ) * ((1 - q) * B.card) := by ring
      _ ≤ ((A \ C).card : ℝ) * X.card :=
        mul_le_mul_of_nonneg_left hXlower (by positivity)
      _ ≤ 3 * q ^ 2 * A.card * B.card := hsumLowerR
      _ = (3 * q ^ 2 * A.card) * B.card := by ring
  have hcancel :
      ((A \ C).card : ℝ) * (1 - q) ≤
        3 * q ^ 2 * A.card :=
    (mul_le_mul_iff_left₀ hBpos).mp hpreCancel
  have hcoef : 3 * q ^ 2 ≤ q * (1 - q) := by
    nlinarith [sq_nonneg q]
  have hOutside :
      ((A \ C).card : ℝ) ≤ q * A.card := by
    have hq1 : 0 < 1 - q := by linarith
    apply (mul_le_mul_iff_right₀ hq1).mp
    calc
      (1 - q) * (A \ C).card =
          ((A \ C).card : ℝ) * (1 - q) := by ring
      _ ≤ 3 * q ^ 2 * A.card := hcancel
      _ ≤ (q * (1 - q)) * A.card :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = (1 - q) * (q * A.card) := by ring
  have hpartA :
      ((A \ C).card : ℝ) + (A ∩ C).card = A.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter A C
  have hpartC :
      ((C \ A).card : ℝ) + (C ∩ A).card = C.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter C A
  have hinter : (C ∩ A).card = (A ∩ C).card := by
    rw [Finset.inter_comm]
  have hinterR :
      ((C ∩ A).card : ℝ) = (A ∩ C).card := by
    exact_mod_cast hinter
  have hsymmA :
      ((A ∆ C).card : ℝ) ≤ 5 * q * A.card := by
    have hsymm :=
      card_symmDiff_le_sdiff_add_sdiff A C
    have hsymmR :
        ((A ∆ C).card : ℝ) ≤
          (A \ C).card + (C \ A).card := by
      exact_mod_cast hsymm
    linarith only [hsymmR, hpartA, hpartC, hinterR, hCupper, hOutside]
  refine ⟨L, ?_, ?_⟩
  · simpa [C] using hsymmA
  · simpa [LF] using hsymmB

end

end RobustInverseUncertainty
