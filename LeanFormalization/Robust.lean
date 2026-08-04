import LeanFormalization.Analytic
import Mathlib.Algebra.Order.Chebyshev

/-!
# Robust inverse uncertainty

This file assembles the combinatorial and analytic parts of the robust
inverse-uncertainty theorem.
-/

namespace RobustInverseUncertainty

noncomputable section

open scoped BigOperators Finset Pointwise symmDiff
attribute [local instance] Classical.propDecidable

noncomputable local instance robustSubmoduleFintype {n : ℕ}
    {H : Submodule (ZMod 2) (BooleanSpace n)} : Fintype H :=
  Fintype.ofFinite H

theorem fintype_card_irrel (α : Type*) (i₁ i₂ : Fintype α) :
    @Fintype.card α i₁ = @Fintype.card α i₂ :=
  @Fintype.card_congr α α i₁ i₂ (Equiv.refl α)

/-- The real part of a complex vector, restricted to a finite coordinate set. -/
def restrictedRealPart {n : ℕ} (S : Finset (BooleanSpace n))
    (f : BooleanSpace n → ℂ) : S → ℝ :=
  fun s ↦ (f s).re

/-- The imaginary part of a complex vector, restricted to a finite coordinate set. -/
def restrictedImagPart {n : ℕ} (S : Finset (BooleanSpace n))
    (f : BooleanSpace n → ℂ) : S → ℝ :=
  fun s ↦ (f s).im

theorem restricted_parts_energy {n : ℕ}
    (S : Finset (BooleanSpace n)) (f : BooleanSpace n → ℂ) :
    (∑ s : S, restrictedRealPart S f s ^ 2) +
        ∑ s : S, restrictedImagPart S f s ^ 2 =
      energyOn S f := by
  rw [energyOn, ← Finset.sum_add_distrib]
  calc
    (∑ s : S,
        (restrictedRealPart S f s ^ 2 +
          restrictedImagPart S f s ^ 2)) =
        ∑ s : S, Complex.normSq (f s) := by
      apply Finset.sum_congr rfl
      intro s hs
      simp [restrictedRealPart, restrictedImagPart,
        Complex.normSq_apply, pow_two]
    _ = ∑ x ∈ S, Complex.normSq (f x) := by
      symm
      rw [Finset.sum_subtype]
      simp

theorem walsh_restrictTo_re {n : ℕ}
    (S : Finset (BooleanSpace n)) (f : BooleanSpace n → ℂ)
    (t : BooleanSpace n) :
    (walshFourier (restrictTo S f) t).re =
      restrictedWalshApply S (restrictedRealPart S f) t := by
  rw [walshFourier_re, realWalshTransform, restrictedWalshApply]
  calc
    (∑ x : BooleanSpace n,
        realPhase x t * (restrictTo S f x).re) =
        ∑ x : BooleanSpace n,
          if x ∈ S then realPhase x t * (f x).re else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxS : x ∈ S <;> simp [restrictTo, hxS]
    _ = ∑ x ∈ S, realPhase x t * (f x).re := by
      rw [Finset.sum_ite_mem]
      simp
    _ = ∑ s : S,
        realPhase (s : BooleanSpace n) t * restrictedRealPart S f s := by
      rw [Finset.sum_subtype]
      · rfl
      · simp

theorem walsh_restrictTo_im {n : ℕ}
    (S : Finset (BooleanSpace n)) (f : BooleanSpace n → ℂ)
    (t : BooleanSpace n) :
    (walshFourier (restrictTo S f) t).im =
      restrictedWalshApply S (restrictedImagPart S f) t := by
  rw [walshFourier_im, realWalshTransform, restrictedWalshApply]
  calc
    (∑ x : BooleanSpace n,
        realPhase x t * (restrictTo S f x).im) =
        ∑ x : BooleanSpace n,
          if x ∈ S then realPhase x t * (f x).im else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxS : x ∈ S <;> simp [restrictTo, hxS]
    _ = ∑ x ∈ S, realPhase x t * (f x).im := by
      rw [Finset.sum_ite_mem]
      simp
    _ = ∑ s : S,
        realPhase (s : BooleanSpace n) t * restrictedImagPart S f s := by
      rw [Finset.sum_subtype]
      · rfl
      · simp

theorem restricted_walsh_parts_energy {n : ℕ}
    (S T : Finset (BooleanSpace n)) (f : BooleanSpace n → ℂ) :
    (∑ t : T,
        restrictedWalshApply S (restrictedRealPart S f) t ^ 2) +
        ∑ t : T,
          restrictedWalshApply S (restrictedImagPart S f) t ^ 2 =
      energyOn T (walshFourier (restrictTo S f)) := by
  rw [energyOn, ← Finset.sum_add_distrib]
  calc
    (∑ t : T,
        (restrictedWalshApply S (restrictedRealPart S f) t ^ 2 +
          restrictedWalshApply S (restrictedImagPart S f) t ^ 2)) =
        ∑ t : T, Complex.normSq
          (walshFourier (restrictTo S f) t) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Complex.normSq_apply, walsh_restrictTo_re,
        walsh_restrictTo_im]
      simp [pow_two]
    _ = ∑ x ∈ T,
        Complex.normSq (walshFourier (restrictTo S f) x) := by
      symm
      rw [Finset.sum_subtype]
      simp

theorem real_vector_eq_zero_of_energy_eq_zero {α : Type*} [Fintype α]
    (u : α → ℝ) (hu : ∑ x, u x ^ 2 = 0) :
    u = 0 := by
  funext x
  have hx : u x ^ 2 = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ ↦ sq_nonneg (u i))).mp hu x (Finset.mem_univ x)
  exact (sq_eq_zero_iff).mp hx

theorem restrictedWalshApply_eq_zero_of_energy_eq_zero {n : ℕ}
    (S : Finset (BooleanSpace n)) (u : S → ℝ)
    (hu : ∑ s : S, u s ^ 2 = 0) :
    ∀ t, restrictedWalshApply S u t = 0 := by
  have hzero := real_vector_eq_zero_of_energy_eq_zero u hu
  intro t
  simp [hzero, restrictedWalshApply]

/-- Normalize a nonzero real vector without changing its Walsh-energy ratio. -/
theorem normalize_real_witness {n : ℕ}
    (S : Finset (BooleanSpace n)) (u : S → ℝ)
    (hu : 0 < ∑ s : S, u s ^ 2) :
    ∃ v : S → ℝ,
      (∑ s : S, v s ^ 2 = 1) ∧
      ∀ t, restrictedWalshApply S v t =
        restrictedWalshApply S u t /
          Real.sqrt (∑ s : S, u s ^ 2) := by
  let e := ∑ s : S, u s ^ 2
  let v : S → ℝ := fun s ↦ u s / Real.sqrt e
  have he : 0 < e := by simpa [e] using hu
  have hsqrt : Real.sqrt e ≠ 0 := ne_of_gt (Real.sqrt_pos.2 he)
  refine ⟨v, ?_, ?_⟩
  · dsimp [v]
    simp_rw [div_pow]
    rw [← Finset.sum_div]
    change (∑ s : S, u s ^ 2) / Real.sqrt e ^ 2 = 1
    rw [show (∑ s : S, u s ^ 2) = e by rfl,
      Real.sq_sqrt (le_of_lt he), div_self (ne_of_gt he)]
  · intro t
    change
      (∑ s : S, realPhase (s : BooleanSpace n) t *
        (u s / Real.sqrt e)) =
      (∑ s : S, realPhase (s : BooleanSpace n) t * u s) /
        Real.sqrt e
    calc
      (∑ s : S, realPhase (s : BooleanSpace n) t *
          (u s / Real.sqrt e)) =
          ∑ s : S,
            (realPhase (s : BooleanSpace n) t * u s) /
              Real.sqrt e := by
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = (∑ s : S, realPhase (s : BooleanSpace n) t * u s) /
          Real.sqrt e := by
        exact (Finset.sum_div (s := Finset.univ)
          (f := fun s : S ↦
            realPhase (s : BooleanSpace n) t * u s)
          (a := Real.sqrt e)).symm

/--
If two real components together have Walsh-energy ratio at least `c`, one
nonzero normalized component has ratio at least `c`.
-/
theorem exists_normalized_real_component {n : ℕ}
    (S T : Finset (BooleanSpace n)) (u₁ u₂ : S → ℝ) (c : ℝ)
    (hpositive : 0 < (∑ s : S, u₁ s ^ 2) + ∑ s : S, u₂ s ^ 2)
    (hratio :
      c * ((∑ s : S, u₁ s ^ 2) + ∑ s : S, u₂ s ^ 2) ≤
        (∑ t : T, restrictedWalshApply S u₁ t ^ 2) +
          ∑ t : T, restrictedWalshApply S u₂ t ^ 2) :
    ∃ v : S → ℝ,
      (∑ s : S, v s ^ 2 = 1) ∧
      c ≤ ∑ t : T, restrictedWalshApply S v t ^ 2 := by
  let e₁ := ∑ s : S, u₁ s ^ 2
  let e₂ := ∑ s : S, u₂ s ^ 2
  let A₁ := ∑ t : T, restrictedWalshApply S u₁ t ^ 2
  let A₂ := ∑ t : T, restrictedWalshApply S u₂ t ^ 2
  have he₁ : 0 ≤ e₁ := by
    dsimp [e₁]
    positivity
  have he₂ : 0 ≤ e₂ := by
    dsimp [e₂]
    positivity
  have hA₁ : 0 ≤ A₁ := by
    dsimp [A₁]
    positivity
  have hA₂ : 0 ≤ A₂ := by
    dsimp [A₂]
    positivity
  have hpositive' : 0 < e₁ + e₂ := by simpa [e₁, e₂] using hpositive
  have hratio' : c * (e₁ + e₂) ≤ A₁ + A₂ := by
    simpa [e₁, e₂, A₁, A₂] using hratio
  have choose_component :
      (0 < e₁ ∧ c * e₁ ≤ A₁) ∨
        (0 < e₂ ∧ c * e₂ ≤ A₂) := by
    by_cases he₁zero : e₁ = 0
    · right
      have he₂pos : 0 < e₂ := by nlinarith
      have hA₁zero : A₁ = 0 := by
        dsimp [A₁]
        apply Finset.sum_eq_zero
        intro t ht
        rw [restrictedWalshApply_eq_zero_of_energy_eq_zero S u₁
          (by simpa [e₁] using he₁zero)]
        norm_num
      exact ⟨he₂pos, by nlinarith⟩
    · have he₁pos : 0 < e₁ := lt_of_le_of_ne he₁ (Ne.symm he₁zero)
      by_cases hfirst : c * e₁ ≤ A₁
      · exact Or.inl ⟨he₁pos, hfirst⟩
      · right
        have he₂pos : 0 < e₂ := by
          by_contra hnot
          have he₂zero : e₂ = 0 := le_antisymm (le_of_not_gt hnot) he₂
          have hA₂zero : A₂ = 0 := by
            dsimp [A₂]
            apply Finset.sum_eq_zero
            intro t ht
            rw [restrictedWalshApply_eq_zero_of_energy_eq_zero S u₂
              (by simpa [e₂] using he₂zero)]
            norm_num
          nlinarith
        exact ⟨he₂pos, by nlinarith⟩
  rcases choose_component with ⟨he, hratio_component⟩ |
      ⟨he, hratio_component⟩
  · obtain ⟨v, hv, htransform⟩ :=
      normalize_real_witness S u₁ (by simpa [e₁] using he)
    refine ⟨v, hv, ?_⟩
    have hsqrt_sq :
        Real.sqrt e₁ ^ 2 = e₁ := Real.sq_sqrt (le_of_lt he)
    have he_ne : e₁ ≠ 0 := ne_of_gt he
    have htransform' (t : BooleanSpace n) :
        restrictedWalshApply S v t =
          restrictedWalshApply S u₁ t / Real.sqrt e₁ := by
      simpa [e₁] using htransform t
    simp_rw [htransform', div_pow, hsqrt_sq]
    rw [← Finset.sum_div]
    change c ≤ A₁ / e₁
    exact (le_div_iff₀ he).2 hratio_component
  · obtain ⟨v, hv, htransform⟩ :=
      normalize_real_witness S u₂ (by simpa [e₂] using he)
    refine ⟨v, hv, ?_⟩
    have hsqrt_sq :
        Real.sqrt e₂ ^ 2 = e₂ := Real.sq_sqrt (le_of_lt he)
    have he_ne : e₂ ≠ 0 := ne_of_gt he
    have htransform' (t : BooleanSpace n) :
        restrictedWalshApply S v t =
          restrictedWalshApply S u₂ t / Real.sqrt e₂ := by
      simpa [e₂] using htransform t
    simp_rw [htransform', div_pow, hsqrt_sq]
    rw [← Finset.sum_div]
    change c ≤ A₂ / e₂
    exact (le_div_iff₀ he).2 hratio_component

/-- Complex near-extremizers yield real normalized near-extremizers. -/
theorem exists_real_witness_of_complex_restriction {n : ℕ}
    (S T : Finset (BooleanSpace n)) (f : BooleanSpace n → ℂ) (c : ℝ)
    (hSenergy : 0 < energyOn S f)
    (hratio :
      c * energyOn S f ≤
        energyOn T (walshFourier (restrictTo S f))) :
    ∃ v : S → ℝ,
      (∑ s : S, v s ^ 2 = 1) ∧
      c ≤ ∑ t : T, restrictedWalshApply S v t ^ 2 := by
  apply exists_normalized_real_component S T
    (restrictedRealPart S f) (restrictedImagPart S f) c
  · rwa [restricted_parts_energy]
  · rwa [restricted_parts_energy, restricted_walsh_parts_energy]

/-- The support inverse theorem with a genuinely complex input vector. -/
theorem support_inverse_of_complex_restriction {n : ℕ}
    (S T : Finset (BooleanSpace n)) (f : BooleanSpace n → ℂ) {q : ℝ}
    (hq0 : 0 < q) (hq : q ≤ 1 / 100)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hSenergy : 0 < energyOn S f)
    (henergy :
      (1 - q ^ 2 / 16) * Fintype.card (BooleanSpace n) *
          energyOn S f ≤
        energyOn T (walshFourier (restrictTo S f)))
    (hproduct :
      (S.card : ℝ) * T.card ≤
        (1 + q ^ 2 / 16) * Fintype.card (BooleanSpace n)) :
    ∃ s₀ : S, ∃ t₀ : T,
      ∃ L : Submodule (ZMod 2) (BooleanSpace n),
        (((translateFinset S s₀ ∆
            submodulePoints (perp L)).card : ℝ) ≤ 5 * q * S.card) ∧
        (((translateFinset T t₀ ∆
            submodulePoints L).card : ℝ) ≤ 12 * q * T.card) := by
  obtain ⟨v, hv, hvEnergy⟩ :=
    exists_real_witness_of_complex_restriction S T f
      ((1 - q ^ 2 / 16) * Fintype.card (BooleanSpace n))
      hSenergy (by simpa [mul_assoc] using henergy)
  exact support_inverse_of_real_witness S T v hq0 hq hS hT hv
    hvEnergy hproduct

theorem abs_realPhase {n : ℕ} (x y : BooleanSpace n) :
    |realPhase x y| = 1 := by
  simp only [realPhase]
  split_ifs <;> norm_num

theorem realSign_mul_self_eq_abs (x : ℝ) :
    realSign x * x = |x| := by
  by_cases hx : x < 0
  · simp [realSign, hx, abs_of_neg hx]
  · have hx0 : 0 ≤ x := le_of_not_gt hx
    simp [realSign, hx, abs_of_nonneg hx0]

/-- Every Walsh coefficient is bounded by the input's `ℓ₁` norm. -/
theorem abs_restrictedWalshApply_le {n : ℕ}
    (S : Finset (BooleanSpace n)) (u : S → ℝ)
    (t : BooleanSpace n) :
    |restrictedWalshApply S u t| ≤ ∑ s : S, |u s| := by
  rw [restrictedWalshApply]
  calc
    |∑ s : S, realPhase (s : BooleanSpace n) t * u s| ≤
        ∑ s : S,
          |realPhase (s : BooleanSpace n) t * u s| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s : S, |u s| := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [abs_mul, abs_realPhase, one_mul]

theorem restrictedWalshApply_sq_le_l1_sq {n : ℕ}
    (S : Finset (BooleanSpace n)) (u : S → ℝ)
    (t : BooleanSpace n) :
    restrictedWalshApply S u t ^ 2 ≤ (∑ s : S, |u s|) ^ 2 := by
  have h := abs_restrictedWalshApply_le S u t
  have hsum : 0 ≤ ∑ s : S, |u s| := by positivity
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg (restrictedWalshApply S u t)) hsum).2 h

theorem restrictedWalsh_energy_le_card_mul_l1_sq {n : ℕ}
    (S T : Finset (BooleanSpace n)) (u : S → ℝ) :
    (∑ t : T, restrictedWalshApply S u t ^ 2) ≤
      T.card * (∑ s : S, |u s|) ^ 2 := by
  calc
    (∑ t : T, restrictedWalshApply S u t ^ 2) ≤
        ∑ t : T, (∑ s : S, |u s|) ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      exact restrictedWalshApply_sq_le_l1_sq S u t
    _ = T.card * (∑ s : S, |u s|) ^ 2 := by simp

theorem l1_sq_le_card_mul_energy {α : Type*} [Fintype α]
    (u : α → ℝ) :
    (∑ x, |u x|) ^ 2 ≤
      Fintype.card α * ∑ x, u x ^ 2 := by
  simpa [sq_abs] using
    (sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun x ↦ |u x|))

/-- The signed vector with constant magnitude equal to the mean magnitude of `u`. -/
def flatRealApprox {α : Type*} [Fintype α]
    (u : α → ℝ) : α → ℝ :=
  fun x ↦ realSign (u x) *
    ((∑ y, |u y|) / Fintype.card α)

theorem flatRealApprox_sq {α : Type*} [Fintype α]
    (u : α → ℝ) (x : α) :
    flatRealApprox u x ^ 2 =
      ((∑ y, |u y|) / Fintype.card α) ^ 2 := by
  simp [flatRealApprox, mul_pow]

theorem flatRealApprox_error_eq {α : Type*} [Fintype α]
    [Nonempty α] (u : α → ℝ) :
    (∑ x, (u x - flatRealApprox u x) ^ 2) =
      (∑ x, u x ^ 2) -
        (∑ x, |u x|) ^ 2 / Fintype.card α := by
  let B : ℝ := ∑ x, |u x|
  let m : ℝ := Fintype.card α
  have hm : m ≠ 0 := by
    dsimp [m]
    exact_mod_cast Fintype.card_ne_zero
  have hcross :
      ∑ x, u x * flatRealApprox u x = B ^ 2 / m := by
    calc
      (∑ x, u x * flatRealApprox u x) =
          ∑ x, |u x| * (B / m) := by
        apply Finset.sum_congr rfl
        intro x hx
        change
          u x * (realSign (u x) * (B / m)) = |u x| * (B / m)
        rw [← mul_assoc, mul_comm (u x) (realSign (u x)),
          realSign_mul_self_eq_abs]
      _ = B * (B / m) := by
        simpa [B] using
          (Finset.sum_mul (s := Finset.univ)
            (f := fun x : α ↦ |u x|) (a := B / m)).symm
      _ = B ^ 2 / m := by ring
  have hflat :
      ∑ x, flatRealApprox u x ^ 2 = B ^ 2 / m := by
    calc
      (∑ x, flatRealApprox u x ^ 2) =
          ∑ _x : α, (B / m) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        simpa [B, m] using flatRealApprox_sq u x
      _ = m * (B / m) ^ 2 := by
        simp [m]
      _ = B ^ 2 / m := by field_simp
  have htwo :
      (∑ x, 2 * u x * flatRealApprox u x) =
        2 * ∑ x, u x * flatRealApprox u x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  calc
    (∑ x, (u x - flatRealApprox u x) ^ 2) =
        (∑ x, u x ^ 2) -
          2 * (∑ x, u x * flatRealApprox u x) +
            ∑ x, flatRealApprox u x ^ 2 := by
      simp_rw [sub_sq]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        htwo]
    _ = (∑ x, u x ^ 2) - B ^ 2 / m := by
      rw [hcross, hflat]
      ring
    _ = (∑ x, u x ^ 2) -
        (∑ x, |u x|) ^ 2 / Fintype.card α := by rfl

/--
Near-maximal restricted Walsh energy forces a real vector to be close to a
signed constant-magnitude vector.
-/
theorem flatRealApprox_error_le_restricted_defect {n : ℕ}
    (S T : Finset (BooleanSpace n)) (u : S → ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    (∑ s : S, (u s - flatRealApprox u s) ^ 2) ≤
      (∑ s : S, u s ^ 2) -
        (∑ t : T, restrictedWalshApply S u t ^ 2) /
          ((S.card : ℝ) * T.card) := by
  letI : Nonempty S := hS.to_subtype
  let A : ℝ := ∑ t : T, restrictedWalshApply S u t ^ 2
  let B : ℝ := ∑ s : S, |u s|
  let m : ℝ := S.card
  let k : ℝ := T.card
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast hS.card_pos
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast hT.card_pos
  have hA : A ≤ k * B ^ 2 := by
    simpa [A, B, k] using
      restrictedWalsh_energy_le_card_mul_l1_sq S T u
  have hratio : A / (m * k) ≤ B ^ 2 / m := by
    calc
      A / (m * k) = (A / k) / m := by field_simp
      _ ≤ B ^ 2 / m := by
        gcongr
        exact (div_le_iff₀ hk).2 (by simpa [mul_comm] using hA)
  rw [flatRealApprox_error_eq]
  simpa [A, B, m, k] using
    (sub_le_sub_left hratio (∑ s : S, u s ^ 2))

/--
Mass on an exceptional subset is bounded by the flatness error plus the
relative size of that subset.
-/
theorem real_mass_on_finset_le_flat_error {α : Type*} [Fintype α]
    [Nonempty α] (u : α → ℝ) (U : Finset α) :
    (∑ x ∈ U, u x ^ 2) ≤
      2 * (∑ x, (u x - flatRealApprox u x) ^ 2) +
        2 * (U.card / Fintype.card α) * ∑ x, u x ^ 2 := by
  let B : ℝ := ∑ x, |u x|
  let e : ℝ := ∑ x, u x ^ 2
  let m : ℝ := Fintype.card α
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast Fintype.card_pos
  have hB : B ^ 2 ≤ m * e := by
    simpa [B, e, m] using l1_sq_le_card_mul_energy u
  have hflat (x : α) :
      flatRealApprox u x ^ 2 ≤ e / m := by
    rw [flatRealApprox_sq]
    change (B / m) ^ 2 ≤ e / m
    calc
      (B / m) ^ 2 = B ^ 2 / m ^ 2 := by ring
      _ ≤ (m * e) / m ^ 2 := by gcongr
      _ = e / m := by field_simp
  have hpoint (x : α) :
      u x ^ 2 ≤
        2 * (u x - flatRealApprox u x) ^ 2 +
          2 * flatRealApprox u x ^ 2 := by
    nlinarith [sq_nonneg (u x - 2 * flatRealApprox u x)]
  have herrorSubset :
      (∑ x ∈ U, (u x - flatRealApprox u x) ^ 2) ≤
        ∑ x, (u x - flatRealApprox u x) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ U)
    intro x hx hnot
    positivity
  calc
    (∑ x ∈ U, u x ^ 2) ≤
        ∑ x ∈ U,
          (2 * (u x - flatRealApprox u x) ^ 2 +
            2 * flatRealApprox u x ^ 2) := by
      apply Finset.sum_le_sum
      intro x hx
      exact hpoint x
    _ = 2 * (∑ x ∈ U, (u x - flatRealApprox u x) ^ 2) +
        2 * (∑ x ∈ U, flatRealApprox u x ^ 2) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 2 * (∑ x, (u x - flatRealApprox u x) ^ 2) +
        2 * (∑ _x ∈ U, e / m) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left herrorSubset (by norm_num)
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro x hx
        exact hflat x
    _ = 2 * (∑ x, (u x - flatRealApprox u x) ^ 2) +
        2 * (U.card / Fintype.card α) * ∑ x, u x ^ 2 := by
      simp [e, m]
      ring

/-- A direct quantitative flatness bound on any exceptional subset of `S`. -/
theorem real_mass_on_finset_le_restricted_defect {n : ℕ}
    (S T : Finset (BooleanSpace n)) (u : S → ℝ) (U : Finset S)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    (∑ s ∈ U, u s ^ 2) ≤
      2 * ((∑ s : S, u s ^ 2) -
        (∑ t : T, restrictedWalshApply S u t ^ 2) /
          ((S.card : ℝ) * T.card)) +
        2 * (U.card / S.card) * ∑ s : S, u s ^ 2 := by
  letI : Nonempty S := hS.to_subtype
  have hbase :
      (∑ s ∈ U, u s ^ 2) ≤
        2 * (∑ s : S, (u s - flatRealApprox u s) ^ 2) +
          2 * (U.card / S.card) * ∑ s : S, u s ^ 2 := by
    simpa using real_mass_on_finset_le_flat_error u U
  apply hbase.trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (flatRealApprox_error_le_restricted_defect S T u hS hT)
      (by norm_num)
  · rfl

/-- The affine coset `a + H`, represented as a finite coordinate set. -/
def affineSubspacePoints {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (a : BooleanSpace n) :
    Finset (BooleanSpace n) :=
  translateFinset (submodulePoints H) a

@[simp]
theorem card_affineSubspacePoints {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (a : BooleanSpace n) :
    (affineSubspacePoints H a).card = Fintype.card H := by
  rw [affineSubspacePoints, card_translateFinset, card_submodulePoints]
  exact fintype_card_irrel H _ _

@[simp]
theorem mem_affineSubspacePoints {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n)) (a x : BooleanSpace n) :
    x ∈ affineSubspacePoints H a ↔ x + a ∈ H := by
  constructor
  · intro hx
    rw [affineSubspacePoints, translateFinset] at hx
    obtain ⟨y, hy, hya⟩ := Finset.mem_image.mp hx
    rw [mem_submodulePoints] at hy
    have : x + a = y := by
      rw [← hya]
      simp [add_assoc]
    rwa [this]
  · intro hx
    rw [affineSubspacePoints, translateFinset, Finset.mem_image]
    refine ⟨x + a, ?_, ?_⟩
    · rwa [mem_submodulePoints]
    · simp [add_assoc]

@[simp]
theorem translateFinset_twice {n : ℕ}
    (A : Finset (BooleanSpace n)) (a : BooleanSpace n) :
    translateFinset (translateFinset A a) a = A := by
  ext x
  simp only [translateFinset, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa [add_assoc] using hz
  · intro hx
    refine ⟨x + a, ?_, by simp [add_assoc]⟩
    exact ⟨x, hx, rfl⟩

theorem card_symmDiff_affine_eq_translated {n : ℕ}
    (S : Finset (BooleanSpace n))
    (H : Submodule (ZMod 2) (BooleanSpace n)) (a : BooleanSpace n) :
    (S ∆ affineSubspacePoints H a).card =
      (translateFinset S a ∆ submodulePoints H).card := by
  let addA : BooleanSpace n → BooleanSpace n := fun x ↦ x + a
  have hadd : Function.Injective addA := by
    simpa [addA, add_comm] using add_left_injective a
  calc
    (S ∆ affineSubspacePoints H a).card =
        ((S ∆ affineSubspacePoints H a).image addA).card := by
      rw [Finset.card_image_of_injective _ hadd]
    _ = (S.image addA ∆
        (affineSubspacePoints H a).image addA).card := by
      rw [Finset.image_symmDiff S (affineSubspacePoints H a) hadd]
    _ = (translateFinset S a ∆ submodulePoints H).card := by
      change
        (translateFinset S a ∆
          translateFinset (affineSubspacePoints H a) a).card =
        (translateFinset S a ∆ submodulePoints H).card
      rw [affineSubspacePoints, translateFinset_twice]

/-- Points of `S` that miss a second coordinate set, bundled as a subtype finset. -/
def missedSubtype {α : Type*} [DecidableEq α]
    (S C : Finset α) : Finset S :=
  Finset.univ.filter fun s ↦ (s : α) ∉ C

@[simp]
theorem card_missedSubtype {α : Type*} [DecidableEq α]
    (S C : Finset α) :
    (missedSubtype S C).card = (S \ C).card := by
  refine Finset.card_bij
    (s := missedSubtype S C) (t := S \ C)
    (fun s _ ↦ (s : α)) ?_ ?_ ?_
  · intro s hs
    simp [missedSubtype] at hs
    exact Finset.mem_sdiff.mpr ⟨s.property, hs⟩
  · intro s₁ hs₁ s₂ hs₂ h
    exact Subtype.ext h
  · intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact ⟨⟨x, hx'.1⟩, by simp [missedSubtype, hx'.2], rfl⟩

theorem restricted_parts_energy_missed {n : ℕ}
    (S C : Finset (BooleanSpace n)) (f : BooleanSpace n → ℂ) :
    (∑ s ∈ missedSubtype S C, restrictedRealPart S f s ^ 2) +
        ∑ s ∈ missedSubtype S C, restrictedImagPart S f s ^ 2 =
      energyOn (S \ C) f := by
  rw [energyOn, ← Finset.sum_add_distrib]
  refine Finset.sum_bij
    (s := missedSubtype S C) (t := S \ C)
    (fun s _ ↦ (s : BooleanSpace n)) ?_ ?_ ?_ ?_
  · intro s hs
    simp [missedSubtype] at hs
    exact Finset.mem_sdiff.mpr ⟨s.property, hs⟩
  · intro s₁ hs₁ s₂ hs₂ h
    exact Subtype.ext h
  · intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact ⟨⟨x, hx'.1⟩, by simp [missedSubtype, hx'.2], rfl⟩
  · intro s hs
    simp [restrictedRealPart, restrictedImagPart,
      Complex.normSq_apply, pow_two]

/-- Flatness for a complex vector on an arbitrary exceptional subset of `S`. -/
theorem complex_mass_on_sdiff_le_restricted_defect {n : ℕ}
    (S T C : Finset (BooleanSpace n)) (f : BooleanSpace n → ℂ)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    energyOn (S \ C) f ≤
      2 * (energyOn S f -
        energyOn T (walshFourier (restrictTo S f)) /
          ((S.card : ℝ) * T.card)) +
        2 * ((S \ C).card / S.card) * energyOn S f := by
  let U := missedSubtype S C
  have hre := real_mass_on_finset_le_restricted_defect S T
    (restrictedRealPart S f) U hS hT
  have him := real_mass_on_finset_le_restricted_defect S T
    (restrictedImagPart S f) U hS hT
  have hparts := restricted_parts_energy S f
  have hwalsh := restricted_walsh_parts_energy S T f
  have hmissed := restricted_parts_energy_missed S C f
  have hcard : (U.card : ℝ) = (S \ C).card := by
    exact_mod_cast card_missedSubtype S C
  calc
    energyOn (S \ C) f =
        (∑ s ∈ U, restrictedRealPart S f s ^ 2) +
          ∑ s ∈ U, restrictedImagPart S f s ^ 2 := by
      simpa [U] using hmissed.symm
    _ ≤
        (2 * ((∑ s : S, restrictedRealPart S f s ^ 2) -
          (∑ t : T,
            restrictedWalshApply S (restrictedRealPart S f) t ^ 2) /
              ((S.card : ℝ) * T.card)) +
          2 * (U.card / S.card) *
            ∑ s : S, restrictedRealPart S f s ^ 2) +
        (2 * ((∑ s : S, restrictedImagPart S f s ^ 2) -
          (∑ t : T,
            restrictedWalshApply S (restrictedImagPart S f) t ^ 2) /
              ((S.card : ℝ) * T.card)) +
          2 * (U.card / S.card) *
            ∑ s : S, restrictedImagPart S f s ^ 2) :=
      add_le_add hre him
    _ = 2 * (energyOn S f -
        energyOn T (walshFourier (restrictTo S f)) /
          ((S.card : ℝ) * T.card)) +
        2 * ((S \ C).card / S.card) * energyOn S f := by
      rw [← hparts, ← hwalsh, ← hcard]
      ring

/--
Fourier-side flatness.  The mass of the restricted Walsh output on `U` is
controlled by its Frobenius defect and the relative size of `U`.
-/
theorem restrictedWalsh_mass_on_finset_le_defect {n : ℕ}
    (S T : Finset (BooleanSpace n)) (u : S → ℝ) (U : Finset T)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    (∑ t ∈ U, restrictedWalshApply S u t ^ 2) ≤
      2 * (((S.card : ℝ) * T.card * ∑ s : S, u s ^ 2) -
        ∑ t : T, restrictedWalshApply S u t ^ 2) +
      2 * (U.card / T.card) *
        ∑ t : T, restrictedWalshApply S u t ^ 2 := by
  letI : Nonempty T := hT.to_subtype
  let w : T → ℝ := fun t ↦ restrictedWalshApply S u t
  let e : ℝ := ∑ s : S, u s ^ 2
  let A : ℝ := ∑ t : T, w t ^ 2
  let B : ℝ := ∑ s : S, |u s|
  let C : ℝ := ∑ t : T, |w t|
  let m : ℝ := S.card
  let k : ℝ := T.card
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast hS.card_pos
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast hT.card_pos
  have he0 : 0 ≤ e := by
    dsimp [e]
    positivity
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  by_cases hezero : e = 0
  · have hu : u = 0 := by
      apply real_vector_eq_zero_of_energy_eq_zero
      simpa [e] using hezero
    simp [hu, restrictedWalshApply]
  · have he : 0 < e := lt_of_le_of_ne he0 (Ne.symm hezero)
    have hB : B ^ 2 ≤ m * e := by
      simpa [B, e, m] using l1_sq_le_card_mul_energy u
    have hwabs (t : T) : |w t| ≤ B := by
      simpa [w, B] using
        abs_restrictedWalshApply_le S u (t : BooleanSpace n)
    have hABC : A ≤ B * C := by
      calc
        A = ∑ t : T, |w t| ^ 2 := by
          simp [A, sq_abs]
        _ ≤ ∑ t : T, B * |w t| := by
          apply Finset.sum_le_sum
          intro t ht
          have ht0 : 0 ≤ |w t| := abs_nonneg _
          nlinarith [hwabs t]
        _ = B * C := by
          rw [Finset.mul_sum]
    have hA2 : A ^ 2 ≤ (m * e) * C ^ 2 := by
      calc
        A ^ 2 ≤ (B * C) ^ 2 :=
          (sq_le_sq₀ hA0 (mul_nonneg hB0 hC0)).2 hABC
        _ = B ^ 2 * C ^ 2 := by ring
        _ ≤ (m * e) * C ^ 2 := by
          gcongr
    have hAupper : A ≤ m * k * e := by
      calc
        A ≤ k * B ^ 2 := by
          simpa [A, B, k, w] using
            restrictedWalsh_energy_le_card_mul_l1_sq S T u
        _ ≤ k * (m * e) := by gcongr
        _ = m * k * e := by ring
    have hsquare :
        (m * k * e) * (2 * A - m * k * e) ≤ A ^ 2 := by
      nlinarith [sq_nonneg (m * k * e - A)]
    have hinner :
        k * (2 * A - m * k * e) ≤ C ^ 2 := by
      apply le_of_mul_le_mul_left _ (mul_pos hm he)
      calc
        m * e * (k * (2 * A - m * k * e)) =
            (m * k * e) * (2 * A - m * k * e) := by ring
        _ ≤ A ^ 2 := hsquare
        _ ≤ m * e * C ^ 2 := by simpa [mul_assoc] using hA2
    have hflat :
        A - C ^ 2 / k ≤ m * k * e - A := by
      apply le_of_mul_le_mul_left _ hk
      field_simp [ne_of_gt hk]
      nlinarith [hinner]
    have hbase := real_mass_on_finset_le_flat_error w U
    rw [flatRealApprox_error_eq] at hbase
    have hbase' :
        (∑ t ∈ U, w t ^ 2) ≤
          2 * (A - C ^ 2 / k) +
            2 * (U.card / T.card) * A := by
      simpa [A, C, k] using hbase
    calc
      (∑ t ∈ U, restrictedWalshApply S u t ^ 2) =
          ∑ t ∈ U, w t ^ 2 := by rfl
      _ ≤ 2 * (A - C ^ 2 / k) +
          2 * (U.card / T.card) * A := hbase'
      _ ≤ 2 * (m * k * e - A) +
          2 * (U.card / T.card) * A := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hflat (by norm_num)
        · rfl
      _ = 2 * (((S.card : ℝ) * T.card *
          ∑ s : S, u s ^ 2) -
            ∑ t : T, restrictedWalshApply S u t ^ 2) +
          2 * (U.card / T.card) *
            ∑ t : T, restrictedWalshApply S u t ^ 2 := by
        rfl

/-- Fourier-side flatness for a complex vector restricted to `S`. -/
theorem complex_walsh_mass_on_sdiff_le_defect {n : ℕ}
    (S T D : Finset (BooleanSpace n)) (f : BooleanSpace n → ℂ)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    energyOn (T \ D) (walshFourier (restrictTo S f)) ≤
      2 * (((S.card : ℝ) * T.card * energyOn S f) -
        energyOn T (walshFourier (restrictTo S f))) +
      2 * ((T \ D).card / T.card) *
        energyOn T (walshFourier (restrictTo S f)) := by
  let U := missedSubtype T D
  have hre := restrictedWalsh_mass_on_finset_le_defect S T
    (restrictedRealPart S f) U hS hT
  have him := restrictedWalsh_mass_on_finset_le_defect S T
    (restrictedImagPart S f) U hS hT
  have hparts := restricted_parts_energy S f
  have hwalsh := restricted_walsh_parts_energy S T f
  have hmissed := restricted_parts_energy_missed T D
    (walshFourier (restrictTo S f))
  have hcard : (U.card : ℝ) = (T \ D).card := by
    exact_mod_cast card_missedSubtype T D
  calc
    energyOn (T \ D) (walshFourier (restrictTo S f)) =
        (∑ t ∈ U,
          restrictedWalshApply S (restrictedRealPart S f) t ^ 2) +
        ∑ t ∈ U,
          restrictedWalshApply S (restrictedImagPart S f) t ^ 2 := by
      rw [← hmissed]
      simp only [restrictedRealPart, restrictedImagPart]
      simp_rw [walsh_restrictTo_re, walsh_restrictTo_im]
      rfl
    _ ≤
        (2 * (((S.card : ℝ) * T.card *
            ∑ s : S, restrictedRealPart S f s ^ 2) -
          ∑ t : T,
            restrictedWalshApply S (restrictedRealPart S f) t ^ 2) +
          2 * (U.card / T.card) *
            ∑ t : T,
              restrictedWalshApply S (restrictedRealPart S f) t ^ 2) +
        (2 * (((S.card : ℝ) * T.card *
            ∑ s : S, restrictedImagPart S f s ^ 2) -
          ∑ t : T,
            restrictedWalshApply S (restrictedImagPart S f) t ^ 2) +
          2 * (U.card / T.card) *
            ∑ t : T,
              restrictedWalshApply S (restrictedImagPart S f) t ^ 2) :=
      add_le_add hre him
    _ = 2 * (((S.card : ℝ) * T.card * energyOn S f) -
        energyOn T (walshFourier (restrictTo S f))) +
        2 * ((T \ D).card / T.card) *
          energyOn T (walshFourier (restrictTo S f)) := by
      rw [← hparts, ← hwalsh, ← hcard]
      ring

theorem sum_phase_mul_phase {n : ℕ}
    (x z : BooleanSpace n) :
    (∑ y : BooleanSpace n, phase y x * phase z y) =
      if x = z then (Fintype.card (BooleanSpace n) : ℂ) else 0 := by
  have hxz : x + z = 0 ↔ x = z := by
    constructor
    · intro h
      have h' := congrArg (fun w ↦ w + z) h
      simpa [add_assoc] using h'
    · rintro rfl
      simp
  calc
    (∑ y : BooleanSpace n, phase y x * phase z y) =
        ∑ y : BooleanSpace n, phase y (x + z) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [phase_comm z y, phase_add_right]
    _ = if x + z = 0 then
        (Fintype.card (BooleanSpace n) : ℂ) else 0 :=
      sum_phase_eq_ite (x + z)
    _ = if x = z then
        (Fintype.card (BooleanSpace n) : ℂ) else 0 := by
      simp only [hxz]

/-- Applying the unnormalized Walsh transform twice multiplies by `2^n`. -/
theorem walshFourier_involution {n : ℕ}
    (f : BooleanSpace n → ℂ) (x : BooleanSpace n) :
    walshFourier (walshFourier f) x =
      Fintype.card (BooleanSpace n) * f x := by
  calc
    walshFourier (walshFourier f) x =
        ∑ y : BooleanSpace n, ∑ z : BooleanSpace n,
          (phase y x * phase z y) * f z := by
      rw [walshFourier]
      apply Finset.sum_congr rfl
      intro y hy
      rw [walshFourier, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ = ∑ z : BooleanSpace n, ∑ y : BooleanSpace n,
        (phase y x * phase z y) * f z := by
      rw [Finset.sum_comm]
    _ = ∑ z : BooleanSpace n,
        (∑ y : BooleanSpace n, phase y x * phase z y) * f z := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_mul]
    _ = ∑ z : BooleanSpace n,
        (if x = z then
          (Fintype.card (BooleanSpace n) : ℂ) else 0) * f z := by
      simp_rw [sum_phase_mul_phase]
    _ = Fintype.card (BooleanSpace n) * f x := by
      simp

theorem walshFourier_sub {n : ℕ}
    (f g : BooleanSpace n → ℂ) :
    walshFourier (fun x ↦ f x - g x) =
      fun y ↦ walshFourier f y - walshFourier g y := by
  funext y
  rw [walshFourier, walshFourier, walshFourier,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem complexEnergy_const_mul {α : Type*} [Fintype α]
    (c : ℂ) (f : α → ℂ) :
    complexEnergy (fun x ↦ c * f x) =
      Complex.normSq c * complexEnergy f := by
  rw [complexEnergy, complexEnergy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Complex.normSq_mul]

/--
The normalized inverse Walsh transform after retaining only frequencies in
`D`.
-/
def fourierCoordinateProjector {n : ℕ}
    (D : Finset (BooleanSpace n)) (f : BooleanSpace n → ℂ) :
    BooleanSpace n → ℂ :=
  fun x ↦ (Fintype.card (BooleanSpace n) : ℂ)⁻¹ *
    walshFourier (restrictTo D (walshFourier f)) x

theorem sub_fourierCoordinateProjector {n : ℕ}
    (D : Finset (BooleanSpace n)) (f : BooleanSpace n → ℂ) :
    (fun x ↦ f x - fourierCoordinateProjector D f x) =
      fun x ↦ (Fintype.card (BooleanSpace n) : ℂ)⁻¹ *
        walshFourier
          (fun y ↦ walshFourier f y -
            restrictTo D (walshFourier f) y) x := by
  funext x
  rw [fourierCoordinateProjector, walshFourier_sub]
  change
    f x - (Fintype.card (BooleanSpace n) : ℂ)⁻¹ *
        walshFourier (restrictTo D (walshFourier f)) x =
      (Fintype.card (BooleanSpace n) : ℂ)⁻¹ *
        (walshFourier (walshFourier f) x -
          walshFourier (restrictTo D (walshFourier f)) x)
  rw [walshFourier_involution]
  have hN :
      (Fintype.card (BooleanSpace n) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Exact rejection energy of a normalized Fourier coordinate projector. -/
theorem complexEnergy_sub_fourierCoordinateProjector {n : ℕ}
    (D : Finset (BooleanSpace n)) (f : BooleanSpace n → ℂ) :
    complexEnergy
        (fun x ↦ f x - fourierCoordinateProjector D f x) =
      (complexEnergy (walshFourier f) -
        energyOn D (walshFourier f)) /
          Fintype.card (BooleanSpace n) := by
  rw [sub_fourierCoordinateProjector,
    complexEnergy_const_mul, Complex.normSq_inv,
    Complex.normSq_natCast, walshFourier_parseval,
    complexEnergy_sub_restrictTo]
  have hN : (Fintype.card (BooleanSpace n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem walshFourier_restrictTo_affine {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n))
    (b x : BooleanSpace n) (f : BooleanSpace n → ℂ) :
    walshFourier (restrictTo (affineSubspacePoints H b) f) x =
      ∑ h : H, phase x (b + (h : BooleanSpace n)) *
        f (b + (h : BooleanSpace n)) := by
  let D := affineSubspacePoints H b
  calc
    walshFourier (restrictTo D f) x =
        ∑ y ∈ D, phase y x * f y := by
      rw [walshFourier]
      calc
        (∑ y : BooleanSpace n, phase y x * restrictTo D f y) =
            ∑ y : BooleanSpace n,
              if y ∈ D then phase y x * f y else 0 := by
          apply Finset.sum_congr rfl
          intro y hy
          by_cases hyD : y ∈ D <;> simp [restrictTo, hyD]
        _ = ∑ y ∈ D, phase y x * f y := by
          rw [Finset.sum_ite_mem]
          simp
    _ = ∑ h : H, phase x (b + (h : BooleanSpace n)) *
        f (b + (h : BooleanSpace n)) := by
      symm
      refine Finset.sum_bij
        (s := Finset.univ) (t := D)
        (fun h _ ↦ b + (h : BooleanSpace n)) ?_ ?_ ?_ ?_
      · intro h hh
        rw [mem_affineSubspacePoints]
        have heq :
            (b + (h : BooleanSpace n)) + b =
              (h : BooleanSpace n) := by
          calc
            (b + (h : BooleanSpace n)) + b =
                (b + b) + (h : BooleanSpace n) := by ac_rfl
            _ = (h : BooleanSpace n) := by simp
        rw [heq]
        exact h.property
      · intro h₁ hh₁ h₂ hh₂ heq
        apply Subtype.ext
        exact add_left_cancel heq
      · intro y hy
        have hyH : y + b ∈ H := by
          rwa [mem_affineSubspacePoints] at hy
        refine ⟨⟨y + b, hyH⟩, Finset.mem_univ _, ?_⟩
        calc
          b + (y + b) = (b + b) + y := by ac_rfl
          _ = y := by simp
      · intro h hh
        rw [phase_comm]

theorem fourierCoordinateProjector_affine_eq_dual {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n))
    (b : BooleanSpace n) (f : BooleanSpace n → ℂ) :
    fourierCoordinateProjector (affineSubspacePoints (perp H) b) f =
      dualCosetFourierProjector H b f := by
  funext x
  rw [fourierCoordinateProjector, dualCosetFourierProjector,
    walshFourier_restrictTo_affine]

theorem fourierCoordinateProjector_affine_eq_kernel {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n))
    (b : BooleanSpace n) (f : BooleanSpace n → ℂ) :
    fourierCoordinateProjector (affineSubspacePoints (perp H) b) f =
      dualCosetKernelProjector H b f := by
  rw [fourierCoordinateProjector_affine_eq_dual,
    dualCosetFourierProjector_eq_kernel]

theorem coordinateProjector_eq_restrictTo_affine {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n))
    (a : BooleanSpace n) (f : BooleanSpace n → ℂ) :
    coordinateProjector H a f =
      restrictTo (affineSubspacePoints H a) f := by
  funext x
  simp only [coordinateProjector, restrictTo, mem_affineSubspacePoints]

theorem complexEnergy_sub_coordinateProjector {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n))
    (a : BooleanSpace n) (f : BooleanSpace n → ℂ) :
    complexEnergy (fun x ↦ f x - coordinateProjector H a f x) =
      complexEnergy f - energyOn (affineSubspacePoints H a) f := by
  rw [coordinateProjector_eq_restrictTo_affine,
    complexEnergy_sub_restrictTo]

theorem complexEnergy_coordinateProjector_le {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n))
    (a : BooleanSpace n) (f : BooleanSpace n → ℂ) :
    complexEnergy (coordinateProjector H a f) ≤ complexEnergy f := by
  rw [coordinateProjector_eq_restrictTo_affine,
    complexEnergy_restrictTo]
  exact energyOn_le_complexEnergy _ _

theorem normSq_add_le_two (z w : ℂ) :
    Complex.normSq (z + w) ≤
      2 * Complex.normSq z + 2 * Complex.normSq w := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im - w.im)]

theorem complexEnergy_add_le_two {α : Type*} [Fintype α]
    (f g : α → ℂ) :
    complexEnergy (fun x ↦ f x + g x) ≤
      2 * complexEnergy f + 2 * complexEnergy g := by
  rw [complexEnergy, complexEnergy, complexEnergy,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  exact normSq_add_le_two (f x) (g x)

theorem sub_cosetRankOne_decomposition {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n))
    (a b : BooleanSpace n) (f : BooleanSpace n → ℂ) :
    (fun x ↦ f x - cosetRankOne H a b f x) =
      fun x ↦
        (f x - coordinateProjector H a f x) +
          coordinateProjector H a
            (fun y ↦ f y - dualCosetKernelProjector H b f y) x := by
  rw [← coordinate_comp_dualCosetKernelProjector H a b f]
  funext x
  by_cases hx : x + a ∈ H <;>
    simp [coordinateProjector, hx]

/--
Passing both commuting affine-coset projectors approximately forces proximity
to their rank-one intersection.
-/
theorem complexEnergy_sub_cosetRankOne_le {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n))
    (a b : BooleanSpace n) (f : BooleanSpace n → ℂ) :
    complexEnergy (fun x ↦ f x - cosetRankOne H a b f x) ≤
      2 * complexEnergy
        (fun x ↦ f x - coordinateProjector H a f x) +
      2 * complexEnergy
        (fun x ↦ f x - dualCosetKernelProjector H b f x) := by
  rw [sub_cosetRankOne_decomposition]
  refine (complexEnergy_add_le_two
    (fun x ↦ f x - coordinateProjector H a f x)
    (coordinateProjector H a
      (fun x ↦ f x - dualCosetKernelProjector H b f x))).trans ?_
  apply add_le_add
  · rfl
  · exact mul_le_mul_of_nonneg_left
      (complexEnergy_coordinateProjector_le H a
        (fun x ↦ f x - dualCosetKernelProjector H b f x))
      (by norm_num)

theorem energyOn_sdiff_add_ge {α : Type*} [Fintype α] [DecidableEq α]
    (S C : Finset α) (f : α → ℂ) :
    energyOn S f ≤ energyOn C f + energyOn (S \ C) f := by
  rw [energyOn, energyOn, energyOn]
  have hsplit :
      (∑ x ∈ S, Complex.normSq (f x)) =
        (∑ x ∈ S ∩ C, Complex.normSq (f x)) +
          ∑ x ∈ S \ C, Complex.normSq (f x) := by
    rw [← Finset.sum_union]
    · congr
      ext x
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    · rw [Finset.disjoint_left]
      intro x hxI hxD
      have hxI' := Finset.mem_inter.mp hxI
      have hxD' := Finset.mem_sdiff.mp hxD
      exact hxD'.2 hxI'.2
  rw [hsplit]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.inter_subset_right)
    intro x hx hnot
    exact Complex.normSq_nonneg _
  · rfl

theorem complexEnergy_sub_energyOn_le {α : Type*}
    [Fintype α] [DecidableEq α]
    (S C : Finset α) (f : α → ℂ) :
    complexEnergy f - energyOn C f ≤
      (complexEnergy f - energyOn S f) + energyOn (S \ C) f := by
  have h := energyOn_sdiff_add_ge S C f
  linarith

theorem complexEnergy_sub_energyOn_eq_compl {α : Type*}
    [Fintype α] [DecidableEq α]
    (C : Finset α) (f : α → ℂ) :
    complexEnergy f - energyOn C f =
      energyOn (Finset.univ \ C) f := by
  rw [complexEnergy, energyOn, energyOn]
  have hsplit :
      (∑ x : α, Complex.normSq (f x)) =
        (∑ x ∈ C, Complex.normSq (f x)) +
          ∑ x ∈ Finset.univ \ C, Complex.normSq (f x) := by
    rw [← Finset.sum_union]
    · congr
      ext x
      simp
    · exact Finset.disjoint_sdiff
  rw [hsplit]
  ring

theorem energyOn_add_le_two {α : Type*} [Fintype α] [DecidableEq α]
    (C : Finset α) (f g : α → ℂ) :
    energyOn C (fun x ↦ f x + g x) ≤
      2 * energyOn C f + 2 * energyOn C g := by
  rw [energyOn, energyOn, energyOn,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  exact normSq_add_le_two (f x) (g x)

theorem energyOn_le_complexEnergy' {α : Type*}
    [Fintype α] [DecidableEq α]
    (C : Finset α) (f : α → ℂ) :
    energyOn C f ≤ complexEnergy f :=
  energyOn_le_complexEnergy C f

theorem walshFourier_eq_restrict_add_error {n : ℕ}
    (S : Finset (BooleanSpace n)) (f : BooleanSpace n → ℂ) :
    walshFourier f =
      fun y ↦ walshFourier (restrictTo S f) y +
        walshFourier (fun x ↦ f x - restrictTo S f x) y := by
  funext y
  rw [walshFourier, walshFourier, walshFourier,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

set_option maxHeartbeats 1000000 in
/--
Robust inverse uncertainty under the direct restricted-Walsh near-extremizer
hypothesis.  The final estimate is a squared `ℓ₂` distance to the rank-one
coset-state line.
-/
theorem robust_inverse_uncertainty_restricted {n : ℕ}
    (S T : Finset (BooleanSpace n)) (f : BooleanSpace n → ℂ) {q : ℝ}
    (hq0 : 0 < q) (hq : q ≤ 1 / 100)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hf : complexEnergy f = 1)
    (hprimal : 1 - q ≤ energyOn S f)
    (hrestricted :
      (1 - q ^ 2 / 16) * Fintype.card (BooleanSpace n) *
          energyOn S f ≤
        energyOn T (walshFourier (restrictTo S f)))
    (hproduct :
      (S.card : ℝ) * T.card ≤
        (1 + q ^ 2 / 16) * Fintype.card (BooleanSpace n)) :
    ∃ H : Submodule (ZMod 2) (BooleanSpace n),
      ∃ a b : BooleanSpace n,
        (((S ∆ affineSubspacePoints H a).card : ℝ) ≤
          5 * q * S.card) ∧
        (((T ∆ affineSubspacePoints (perp H) b).card : ℝ) ≤
          12 * q * T.card) ∧
        complexEnergy (fun x ↦ f x - cosetRankOne H a b f x) ≤
          132 * q := by
  have hSenergy : 0 < energyOn S f := by
    have hqsmall : q < 1 := lt_of_le_of_lt hq (by norm_num)
    nlinarith
  obtain ⟨s₀, t₀, L, hSL, hTL⟩ :=
    support_inverse_of_complex_restriction S T f hq0 hq hS hT
      hSenergy hrestricted hproduct
  let H := perp L
  let a : BooleanSpace n := s₀
  let b : BooleanSpace n := t₀
  let C := affineSubspacePoints H a
  let D := affineSubspacePoints (perp H) b
  have hSC :
      (((S ∆ C).card : ℝ) ≤ 5 * q * S.card) := by
    rw [show (S ∆ C).card =
      (translateFinset S s₀ ∆ submodulePoints (perp L)).card by
        simpa [C, H, a] using
          card_symmDiff_affine_eq_translated S (perp L)
            (s₀ : BooleanSpace n)]
    exact hSL
  have hTD :
      (((T ∆ D).card : ℝ) ≤ 12 * q * T.card) := by
    rw [show (T ∆ D).card =
      (translateFinset T t₀ ∆ submodulePoints L).card by
        simpa [D, H, b] using
          card_symmDiff_affine_eq_translated T L
            (t₀ : BooleanSpace n)]
    exact hTL
  have hSdiff :
      (((S \ C).card : ℝ) ≤ 5 * q * S.card) := by
    have hcard : (S \ C).card ≤ (S ∆ C).card :=
      Finset.card_le_card
        (Finset.symmDiff_subset_sdiff (s := S) (t := C))
    exact_mod_cast (le_trans (Nat.cast_le.mpr hcard) hSC)
  have hTdiff :
      (((T \ D).card : ℝ) ≤ 12 * q * T.card) := by
    have hcard : (T \ D).card ≤ (T ∆ D).card :=
      Finset.card_le_card
        (Finset.symmDiff_subset_sdiff (s := T) (t := D))
    exact_mod_cast (le_trans (Nat.cast_le.mpr hcard) hTD)
  let N : ℝ := Fintype.card (BooleanSpace n)
  let G : ℝ := energyOn S f
  let A : ℝ := energyOn T (walshFourier (restrictTo S f))
  let P : ℝ := (S.card : ℝ) * T.card
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hScard : 0 < (S.card : ℝ) := by
    exact_mod_cast hS.card_pos
  have hTcard : 0 < (T.card : ℝ) := by
    exact_mod_cast hT.card_pos
  have hP : 0 < P := by
    dsimp [P]
    positivity
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact energyOn_nonneg S f
  have hGle : G ≤ 1 := by
    dsimp [G]
    rw [← hf]
    exact energyOn_le_complexEnergy S f
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact energyOn_nonneg T _
  have htotalRestricted :
      complexEnergy (walshFourier (restrictTo S f)) = N * G := by
    dsimp [N, G]
    rw [walshFourier_parseval, complexEnergy_restrictTo]
  have hAle : A ≤ N * G := by
    dsimp [A]
    rw [← htotalRestricted]
    exact energyOn_le_complexEnergy T _
  have hproduct' : P ≤ (1 + q ^ 2 / 16) * N := by
    simpa [P, N] using hproduct
  have hlower : (1 - q ^ 2 / 16) * N * G ≤ A := by
    simpa [N, G, A] using hrestricted
  have hq2le : q ^ 2 ≤ q := by
    nlinarith [sq_nonneg q]
  have hfactor : 0 ≤ 1 - q ^ 2 / 4 := by
    nlinarith [sq_nonneg q]
  have hcoeff :
      (1 - q ^ 2 / 4) * (1 + q ^ 2 / 16) ≤
        1 - q ^ 2 / 16 := by
    nlinarith [sq_nonneg q, sq_nonneg (q ^ 2)]
  have hratioLower : (1 - q ^ 2 / 4) * G ≤ A / P := by
    apply (le_div_iff₀ hP).2
    calc
      (1 - q ^ 2 / 4) * G * P ≤
          (1 - q ^ 2 / 4) * G *
            ((1 + q ^ 2 / 16) * N) := by
        gcongr
      _ = ((1 - q ^ 2 / 4) * (1 + q ^ 2 / 16)) *
          N * G := by ring
      _ ≤ (1 - q ^ 2 / 16) * N * G := by
        gcongr
      _ ≤ A := hlower
  have hdefect : G - A / P ≤ q ^ 2 / 4 * G := by
    nlinarith
  have hSratio : ((S \ C).card : ℝ) / S.card ≤ 5 * q := by
    exact (div_le_iff₀ hScard).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hSdiff)
  have hTratio : ((T \ D).card : ℝ) / T.card ≤ 12 * q := by
    exact (div_le_iff₀ hTcard).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hTdiff)
  have hprimalMissBase :=
    complex_mass_on_sdiff_le_restricted_defect S T C f hS hT
  have hprimalMiss :
      energyOn (S \ C) f ≤ 11 * q := by
    have hfirst : 2 * (G - A / P) ≤ q ^ 2 / 2 := by
      calc
        2 * (G - A / P) ≤ 2 * (q ^ 2 / 4 * G) := by
          gcongr
        _ ≤ 2 * (q ^ 2 / 4 * 1) := by
          gcongr
        _ = q ^ 2 / 2 := by ring
    have hsecond :
        2 * (((S \ C).card : ℝ) / S.card) * G ≤ 10 * q := by
      calc
        2 * (((S \ C).card : ℝ) / S.card) * G ≤
            2 * (5 * q) * 1 := by
          gcongr
        _ = 10 * q := by ring
    apply hprimalMissBase.trans
    change
      2 * (G - A / P) +
        2 * (((S \ C).card : ℝ) / S.card) * G ≤ 11 * q
    nlinarith
  have hcoordReject :
      complexEnergy
        (fun x ↦ f x - coordinateProjector H a f x) ≤ 12 * q := by
    rw [complexEnergy_sub_coordinateProjector]
    change complexEnergy f - energyOn C f ≤ 12 * q
    calc
      complexEnergy f - energyOn C f ≤
          (complexEnergy f - energyOn S f) +
            energyOn (S \ C) f :=
        complexEnergy_sub_energyOn_le S C f
      _ ≤ q + 11 * q := by
        rw [hf]
        nlinarith [hprimal, hprimalMiss]
      _ = 12 * q := by ring
  have hPGupper : P * G ≤ (1 + q ^ 2 / 16) * N * G := by
    gcongr
  have hPGdefect : P * G - A ≤ q ^ 2 / 8 * N := by
    calc
      P * G - A ≤
          (1 + q ^ 2 / 16) * N * G -
            (1 - q ^ 2 / 16) * N * G := by
        gcongr
      _ = q ^ 2 / 8 * N * G := by ring
      _ ≤ q ^ 2 / 8 * N * 1 := by
        gcongr
      _ = q ^ 2 / 8 * N := by ring
  have hdualMissBase :=
    complex_walsh_mass_on_sdiff_le_defect S T D f hS hT
  have hdualMiss :
      energyOn (T \ D) (walshFourier (restrictTo S f)) ≤
        25 * q * N := by
    have hfirst : 2 * (P * G - A) ≤ q ^ 2 / 4 * N := by
      nlinarith
    have hsecond :
        2 * (((T \ D).card : ℝ) / T.card) * A ≤
          24 * q * N := by
      calc
        2 * (((T \ D).card : ℝ) / T.card) * A ≤
            2 * (12 * q) * (N * G) := by
          gcongr
        _ ≤ 2 * (12 * q) * (N * 1) := by
          gcongr
        _ = 24 * q * N := by ring
    apply hdualMissBase.trans
    change
      2 * (P * G - A) +
        2 * (((T \ D).card : ℝ) / T.card) * A ≤ 25 * q * N
    have hqN : q ^ 2 / 4 * N ≤ q * N := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hN)
      nlinarith
    nlinarith
  have houtsideT : N * G - A ≤ q ^ 2 / 16 * N := by
    calc
      N * G - A ≤ N * G -
          (1 - q ^ 2 / 16) * N * G := by gcongr
      _ = q ^ 2 / 16 * N * G := by ring
      _ ≤ q ^ 2 / 16 * N * 1 := by gcongr
      _ = q ^ 2 / 16 * N := by ring
  have hgOutsideD :
      complexEnergy (walshFourier (restrictTo S f)) -
          energyOn D (walshFourier (restrictTo S f)) ≤
        26 * q * N := by
    calc
      complexEnergy (walshFourier (restrictTo S f)) -
          energyOn D (walshFourier (restrictTo S f)) ≤
        (complexEnergy (walshFourier (restrictTo S f)) -
          energyOn T (walshFourier (restrictTo S f))) +
        energyOn (T \ D) (walshFourier (restrictTo S f)) :=
          complexEnergy_sub_energyOn_le T D _
      _ = (N * G - A) +
          energyOn (T \ D) (walshFourier (restrictTo S f)) := by
        rw [htotalRestricted]
      _ ≤ q ^ 2 / 16 * N + 25 * q * N := by
        gcongr
      _ ≤ 26 * q * N := by
        have : q ^ 2 / 16 * N ≤ q * N := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hN)
          nlinarith
        nlinarith
  let e : BooleanSpace n → ℂ := fun x ↦ f x - restrictTo S f x
  have heEnergy : complexEnergy e = 1 - G := by
    dsimp [e, G]
    rw [complexEnergy_sub_restrictTo, hf]
  have heBound : complexEnergy e ≤ q := by
    rw [heEnergy]
    dsimp [G]
    nlinarith [hprimal]
  have heFourier :
      complexEnergy (walshFourier e) ≤ q * N := by
    rw [walshFourier_parseval]
    simpa [mul_comm, N] using
      mul_le_mul_of_nonneg_left heBound (by positivity :
        (0 : ℝ) ≤ Fintype.card (BooleanSpace n))
  have hfullOutsideD :
      complexEnergy (walshFourier f) - energyOn D (walshFourier f) ≤
        54 * q * N := by
    rw [complexEnergy_sub_energyOn_eq_compl]
    have hadd := energyOn_add_le_two (Finset.univ \ D)
      (walshFourier (restrictTo S f)) (walshFourier e)
    have hdecomp :
        walshFourier f =
          fun y ↦ walshFourier (restrictTo S f) y +
            walshFourier e y := by
      simpa [e] using walshFourier_eq_restrict_add_error S f
    rw [← hdecomp] at hadd
    calc
      energyOn (Finset.univ \ D) (walshFourier f) ≤
          2 * energyOn (Finset.univ \ D)
              (walshFourier (restrictTo S f)) +
            2 * energyOn (Finset.univ \ D) (walshFourier e) := hadd
      _ ≤ 2 * (26 * q * N) + 2 * (q * N) := by
        gcongr
        · rwa [← complexEnergy_sub_energyOn_eq_compl]
        · exact (energyOn_le_complexEnergy _ _).trans heFourier
      _ = 54 * q * N := by ring
  have hdualReject :
      complexEnergy
        (fun x ↦ f x - dualCosetKernelProjector H b f x) ≤
          54 * q := by
    rw [← fourierCoordinateProjector_affine_eq_kernel H b f,
      complexEnergy_sub_fourierCoordinateProjector]
    change
      (complexEnergy (walshFourier f) -
        energyOn D (walshFourier f)) / N ≤ 54 * q
    exact (div_le_iff₀ hN).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hfullOutsideD)
  refine ⟨H, a, b, hSC, hTD, ?_⟩
  exact (complexEnergy_sub_cosetRankOne_le H a b f).trans
    (by nlinarith)

theorem normSq_add_le_young (z w : ℂ) {r : ℝ} (hr : 0 < r) :
    Complex.normSq (z + w) ≤
      (1 + r) * Complex.normSq z +
        (1 + 1 / r) * Complex.normSq w := by
  apply le_of_mul_le_mul_left _ hr
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  field_simp [ne_of_gt hr]
  nlinarith [sq_nonneg (r * z.re - w.re),
    sq_nonneg (r * z.im - w.im)]

theorem energyOn_add_le_young {α : Type*} [Fintype α] [DecidableEq α]
    (C : Finset α) (f g : α → ℂ) {r : ℝ} (hr : 0 < r) :
    energyOn C (fun x ↦ f x + g x) ≤
      (1 + r) * energyOn C f +
        (1 + 1 / r) * energyOn C g := by
  rw [energyOn, energyOn, energyOn,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  exact normSq_add_le_young (f x) (g x) hr

set_option maxHeartbeats 1000000 in
/--
The concentration form of robust inverse uncertainty.  The concentration
loss is `q^4 / 1024`, while support saturation is measured at
scale `q^2 / 16`.
-/
theorem robust_inverse_uncertainty {n : ℕ}
    (S T : Finset (BooleanSpace n)) (f : BooleanSpace n → ℂ) {q : ℝ}
    (hq0 : 0 < q) (hq : q ≤ 1 / 100)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hf : complexEnergy f = 1)
    (hprimal :
      1 - q ^ 4 / 1024 ≤ energyOn S f)
    (hdual :
      (1 - q ^ 4 / 1024) * Fintype.card (BooleanSpace n) ≤
        energyOn T (walshFourier f))
    (hproduct :
      (S.card : ℝ) * T.card ≤
        (1 + q ^ 2 / 16) * Fintype.card (BooleanSpace n)) :
    ∃ H : Submodule (ZMod 2) (BooleanSpace n),
      ∃ a b : BooleanSpace n,
        (((S ∆ affineSubspacePoints H a).card : ℝ) ≤
          5 * q * S.card) ∧
        (((T ∆ affineSubspacePoints (perp H) b).card : ℝ) ≤
          12 * q * T.card) ∧
        complexEnergy (fun x ↦ f x - cosetRankOne H a b f x) ≤
          132 * q := by
  let N : ℝ := Fintype.card (BooleanSpace n)
  let G : ℝ := energyOn S f
  let A : ℝ := energyOn T (walshFourier (restrictTo S f))
  let e : BooleanSpace n → ℂ := fun x ↦ f x - restrictTo S f x
  let E : ℝ := energyOn T (walshFourier e)
  let eta : ℝ := q ^ 4 / 1024
  let r : ℝ := q ^ 2 / 32
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact energyOn_nonneg S f
  have hGle : G ≤ 1 := by
    dsimp [G]
    rw [← hf]
    exact energyOn_le_complexEnergy S f
  have heta0 : 0 ≤ eta := by
    dsimp [eta]
    positivity
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have heEnergy : complexEnergy e = 1 - G := by
    dsimp [e, G]
    rw [complexEnergy_sub_restrictTo, hf]
  have heBound : complexEnergy e ≤ eta := by
    rw [heEnergy]
    simpa [G, eta, add_comm] using hprimal
  have hE :
      E ≤ eta * N := by
    calc
      E ≤ complexEnergy (walshFourier e) := by
        dsimp [E]
        exact energyOn_le_complexEnergy T _
      _ = N * complexEnergy e := by
        dsimp [N]
        rw [walshFourier_parseval]
      _ ≤ N * eta := by gcongr
      _ = eta * N := by ring
  have hdecomp :
      walshFourier f =
        fun y ↦ walshFourier (restrictTo S f) y +
          walshFourier e y := by
    simpa [e] using walshFourier_eq_restrict_add_error S f
  have hYoung :
      energyOn T (walshFourier f) ≤
        (1 + r) * A + (1 + 1 / r) * E := by
    rw [hdecomp]
    simpa [A, E] using energyOn_add_le_young T
      (walshFourier (restrictTo S f)) (walshFourier e) hr
  have hbudget :
      (1 + r) * (1 - q ^ 2 / 16) +
          (1 + 1 / r) * eta ≤
        1 - eta := by
    dsimp [r, eta]
    field_simp [ne_of_gt hq0]
    nlinarith [sq_nonneg q, sq_nonneg (q ^ 2)]
  have hmainCoeff0 :
      0 ≤ (1 + r) * (1 - q ^ 2 / 16) * N := by
    have : 0 ≤ 1 - q ^ 2 / 16 := by
      nlinarith [sq_nonneg q]
    positivity
  have hbudgetN :
      (1 + r) * (1 - q ^ 2 / 16) * N * G +
          (1 + 1 / r) * eta * N ≤
        (1 - eta) * N := by
    calc
      (1 + r) * (1 - q ^ 2 / 16) * N * G +
          (1 + 1 / r) * eta * N ≤
        (1 + r) * (1 - q ^ 2 / 16) * N * 1 +
          (1 + 1 / r) * eta * N := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hGle hmainCoeff0) le_rfl
      _ = ((1 + r) * (1 - q ^ 2 / 16) +
          (1 + 1 / r) * eta) * N := by ring
      _ ≤ (1 - eta) * N := by gcongr
  have hrestricted :
      (1 - q ^ 2 / 16) * N * G ≤ A := by
    have hdual' :
        (1 - eta) * N ≤ energyOn T (walshFourier f) := by
      simpa [eta, N] using hdual
    have hweight : 0 ≤ 1 + 1 / r := by positivity
    have hEweighted :
        (1 + 1 / r) * E ≤ (1 + 1 / r) * (eta * N) :=
      mul_le_mul_of_nonneg_left hE hweight
    apply le_of_mul_le_mul_left _ (by positivity : 0 < 1 + r)
    nlinarith [hdual', hYoung, hEweighted, hbudgetN]
  have hq4le : q ^ 4 / 1024 ≤ q := by
    have hq1 : q ≤ 1 := hq.trans (by norm_num)
    have hq2le : q ^ 2 ≤ q := by
      nlinarith [sq_nonneg q]
    have hq4le2 : q ^ 4 ≤ q ^ 2 := by
      calc
        q ^ 4 = (q ^ 2) ^ 2 := by ring
        _ ≤ q ^ 2 :=
          (sq_le_sq₀ (sq_nonneg q) (le_of_lt hq0)).2 hq2le
    nlinarith [sq_nonneg (q ^ 2)]
  have hprimal' : 1 - q ≤ G := by
    dsimp [G, eta] at hprimal ⊢
    nlinarith
  exact robust_inverse_uncertainty_restricted S T f hq0 hq hS hT hf
    hprimal' (by simpa [N, G, A] using hrestricted) hproduct

/-- Coefficient of the rank-one projection generated by a real vector. -/
def realRankOneCoefficient {α : Type*} [Fintype α]
    (v : α → ℝ) (f : α → ℂ) : ℂ :=
  ∑ x, (v x : ℂ) * f x

/-- Rank-one operator generated by a real vector. -/
def realRankOne {α : Type*} [Fintype α]
    (v : α → ℝ) (f : α → ℂ) : α → ℂ :=
  fun x ↦ realRankOneCoefficient v f * (v x : ℂ)

theorem complexEnergy_ofReal {α : Type*} [Fintype α]
    (v : α → ℝ) :
    complexEnergy (fun x ↦ (v x : ℂ)) = ∑ x, v x ^ 2 := by
  rw [complexEnergy]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Complex.normSq_ofReal]
  ring

theorem complexEnergy_realRankOne {α : Type*} [Fintype α]
    (v : α → ℝ) (f : α → ℂ)
    (hv : ∑ x, v x ^ 2 = 1) :
    complexEnergy (realRankOne v f) =
      Complex.normSq (realRankOneCoefficient v f) := by
  change
    complexEnergy
      (fun x ↦ realRankOneCoefficient v f * (v x : ℂ)) =
      Complex.normSq (realRankOneCoefficient v f)
  rw [complexEnergy_const_mul,
    complexEnergy_ofReal, hv, mul_one]

/-- Pythagoras for a rank-one projection generated by a real unit vector. -/
theorem complexEnergy_sub_realRankOne {α : Type*} [Fintype α]
    (v : α → ℝ) (f : α → ℂ)
    (hv : ∑ x, v x ^ 2 = 1) :
    complexEnergy (fun x ↦ f x - realRankOne v f x) =
      complexEnergy f -
        Complex.normSq (realRankOneCoefficient v f) := by
  let d := realRankOneCoefficient v f
  have hcrossComplex :
      (∑ x, f x * (starRingEnd ℂ) (d * (v x : ℂ))) =
        (Complex.normSq d : ℂ) := by
    calc
      (∑ x, f x * (starRingEnd ℂ) (d * (v x : ℂ))) =
          ∑ x, ((v x : ℂ) * f x) * (starRingEnd ℂ) d := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [map_mul, starRingEnd_apply, Complex.conj_ofReal]
        ring
      _ = (∑ x, (v x : ℂ) * f x) * (starRingEnd ℂ) d := by
        rw [Finset.sum_mul]
      _ = d * (starRingEnd ℂ) d := by rfl
      _ = (Complex.normSq d : ℂ) := by
        simp [Complex.normSq_eq_conj_mul_self, mul_comm]
  have hcross :
      (∑ x, (f x * (starRingEnd ℂ) (d * (v x : ℂ))).re) =
        Complex.normSq d := by
    rw [← Complex.re_sum, hcrossComplex]
    simp
  change
    complexEnergy (fun x ↦ f x - d * (v x : ℂ)) =
      complexEnergy f - Complex.normSq d
  rw [complexEnergy, complexEnergy]
  simp_rw [Complex.normSq_sub, Complex.normSq_mul,
    Complex.normSq_ofReal]
  have hv' : ∑ x, v x * v x = 1 := by
    simpa [pow_two] using hv
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hv', mul_one, ← Finset.mul_sum, hcross]
  ring

/-- Real-valued normalized modulated indicator of `a + H`. -/
def normalizedRealCosetWave {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n))
    (a b x : BooleanSpace n) : ℝ :=
  if x + a ∈ H then
    realPhase b x / Real.sqrt (Fintype.card H)
  else 0

theorem normalizedRealCosetWave_energy {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n))
    (a b : BooleanSpace n) :
    ∑ x, normalizedRealCosetWave H a b x ^ 2 = 1 := by
  let h : ℝ := Fintype.card H
  have hh : 0 < h := by
    dsimp [h]
    positivity
  have hsqrt : Real.sqrt h ^ 2 = h :=
    Real.sq_sqrt (le_of_lt hh)
  calc
    (∑ x, normalizedRealCosetWave H a b x ^ 2) =
        ∑ x : BooleanSpace n,
          if x ∈ affineSubspacePoints H a then 1 / h else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxH : x + a ∈ H
      · have hxC : x ∈ affineSubspacePoints H a :=
          (mem_affineSubspacePoints H a x).2 hxH
        simp [normalizedRealCosetWave, hxH, hxC, div_pow,
          realPhase_sq]
        norm_cast
      · have hxC : x ∉ affineSubspacePoints H a := by
          simpa [mem_affineSubspacePoints] using hxH
        simp [normalizedRealCosetWave, hxH, hxC]
    _ = (affineSubspacePoints H a).card * (1 / h) := by
      rw [Finset.sum_ite_mem]
      simp
    _ = h * (1 / h) := by
      rw [card_affineSubspacePoints]
    _ = 1 := by field_simp

theorem ofReal_normalizedRealCosetWave {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n))
    (a b x : BooleanSpace n) :
    (normalizedRealCosetWave H a b x : ℂ) =
      (Real.sqrt (Fintype.card H) : ℂ)⁻¹ *
        cosetWave H a b x := by
  by_cases hx : x + a ∈ H
  · simp [normalizedRealCosetWave, cosetWave, hx,
      div_eq_mul_inv, ← ofReal_realPhase, mul_comm]
  · simp [normalizedRealCosetWave, cosetWave, hx]

theorem realRankOne_normalizedCosetWave_eq {n : ℕ}
    (H : Submodule (ZMod 2) (BooleanSpace n))
    (a b : BooleanSpace n) (f : BooleanSpace n → ℂ) :
    realRankOne (normalizedRealCosetWave H a b) f =
      cosetRankOne H a b f := by
  let r : ℝ := Real.sqrt (Fintype.card H)
  let d : ℂ := ∑ y : BooleanSpace n, cosetWave H a b y * f y
  have hcard : (0 : ℝ) < Fintype.card H := by positivity
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrsq : r * r = Fintype.card H := by
    dsimp [r]
    rw [Real.mul_self_sqrt (le_of_lt hcard)]
  have hscalar :
      (r : ℂ)⁻¹ * (r : ℂ)⁻¹ =
        (Fintype.card H : ℂ)⁻¹ := by
    have hrsqC :
        (r : ℂ) * (r : ℂ) = (Fintype.card H : ℂ) := by
      exact_mod_cast hrsq
    rw [← mul_inv_rev, hrsqC]
  have hcoeff :
      realRankOneCoefficient (normalizedRealCosetWave H a b) f =
        (r : ℂ)⁻¹ * d := by
    rw [realRankOneCoefficient]
    simp_rw [ofReal_normalizedRealCosetWave]
    change
      (∑ y : BooleanSpace n,
        (r : ℂ)⁻¹ * cosetWave H a b y * f y) =
        (r : ℂ)⁻¹ * d
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  funext x
  rw [realRankOne, hcoeff, ofReal_normalizedRealCosetWave]
  rw [show Real.sqrt (Fintype.card H) = r by rfl]
  calc
    ((r : ℂ)⁻¹ * d) * ((r : ℂ)⁻¹ * cosetWave H a b x) =
        (Fintype.card H : ℂ)⁻¹ * cosetWave H a b x * d := by
      rw [← hscalar]
      ring
    _ = cosetRankOne H a b f x := by
      rw [cosetRankOne]

/-- Unit-modulus normalization of a complex scalar, with an arbitrary value at zero. -/
def unitPhase (d : ℂ) : ℂ :=
  if d = 0 then 1
  else d * (Real.sqrt (Complex.normSq d) : ℂ)⁻¹

theorem normSq_unitPhase (d : ℂ) :
    Complex.normSq (unitPhase d) = 1 := by
  by_cases hd : d = 0
  · simp [unitPhase, hd]
  · have hD : 0 < Complex.normSq d :=
      (Complex.normSq_pos).2 hd
    have hsqrt :
        Real.sqrt (Complex.normSq d) ^ 2 =
          Complex.normSq d :=
      Real.sq_sqrt (le_of_lt hD)
    rw [unitPhase]
    simp only [hd, ↓reduceIte, Complex.normSq_mul,
      Complex.normSq_inv, Complex.normSq_ofReal]
    rw [Real.mul_self_sqrt (le_of_lt hD),
      mul_inv_cancel₀ (ne_of_gt hD)]

theorem complexEnergy_sub_const_mul_real {α : Type*} [Fintype α]
    (v : α → ℝ) (f : α → ℂ) (c : ℂ)
    (hv : ∑ x, v x ^ 2 = 1) :
    complexEnergy (fun x ↦ f x - c * (v x : ℂ)) =
      complexEnergy f + Complex.normSq c -
        2 * (realRankOneCoefficient v f *
          (starRingEnd ℂ) c).re := by
  let d := realRankOneCoefficient v f
  have hcrossComplex :
      (∑ x, f x * (starRingEnd ℂ) (c * (v x : ℂ))) =
        d * (starRingEnd ℂ) c := by
    calc
      (∑ x, f x * (starRingEnd ℂ) (c * (v x : ℂ))) =
          ∑ x, ((v x : ℂ) * f x) * (starRingEnd ℂ) c := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [map_mul, starRingEnd_apply, Complex.conj_ofReal]
        ring
      _ = (∑ x, (v x : ℂ) * f x) * (starRingEnd ℂ) c := by
        rw [Finset.sum_mul]
      _ = d * (starRingEnd ℂ) c := by rfl
  have hcross :
      (∑ x, (f x * (starRingEnd ℂ) (c * (v x : ℂ))).re) =
        (d * (starRingEnd ℂ) c).re := by
    rw [← Complex.re_sum, hcrossComplex]
  have hv' : ∑ x, v x * v x = 1 := by
    simpa [pow_two] using hv
  change
    complexEnergy (fun x ↦ f x - c * (v x : ℂ)) =
      complexEnergy f + Complex.normSq c -
        2 * (d * (starRingEnd ℂ) c).re
  rw [complexEnergy, complexEnergy]
  simp_rw [Complex.normSq_sub, Complex.normSq_mul,
    Complex.normSq_ofReal]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hv', mul_one, ← Finset.mul_sum, hcross]

set_option maxHeartbeats 1000000 in
/--
Normalizing the coefficient of a real rank-one projection costs at most a
factor two in squared distance.
-/
theorem exists_unit_phase_close_to_real_rankOne
    {α : Type*} [Fintype α]
    (v : α → ℝ) (f : α → ℂ)
    (hv : ∑ x, v x ^ 2 = 1)
    (hf : complexEnergy f = 1) :
    ∃ c : ℂ, Complex.normSq c = 1 ∧
      complexEnergy (fun x ↦ f x - c * (v x : ℂ)) ≤
        2 * complexEnergy (fun x ↦ f x - realRankOne v f x) := by
  let d := realRankOneCoefficient v f
  let D := Complex.normSq d
  let R := complexEnergy (fun x ↦ f x - realRankOne v f x)
  have hR0 : 0 ≤ R := by
    dsimp [R, complexEnergy]
    exact Finset.sum_nonneg fun x hx ↦ Complex.normSq_nonneg _
  have hR : R = 1 - D := by
    dsimp [R, D, d]
    rw [complexEnergy_sub_realRankOne v f hv, hf]
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact Complex.normSq_nonneg _
  have hDle : D ≤ 1 := by nlinarith
  refine ⟨unitPhase d, normSq_unitPhase d, ?_⟩
  by_cases hd : d = 0
  · have hphase : unitPhase d = 1 := by simp [unitPhase, hd]
    have hDzero : D = 0 := by simp [D, d, hd]
    change
      complexEnergy (fun x ↦ f x - unitPhase d * (v x : ℂ)) ≤
        2 * R
    rw [complexEnergy_sub_const_mul_real v f (unitPhase d) hv,
      hf, normSq_unitPhase, hphase]
    change
      1 + 1 - 2 * (d * (starRingEnd ℂ) (1 : ℂ)).re ≤
        2 * R
    rw [hd, hR, hDzero]
    norm_num
  · have hDpos : 0 < D := by
      dsimp [D, d]
      exact (Complex.normSq_pos).2 hd
    let r := Real.sqrt D
    have hr : 0 < r := by
      dsimp [r]
      exact Real.sqrt_pos.2 hDpos
    have hrsq : r ^ 2 = D := by
      dsimp [r]
      exact Real.sq_sqrt (le_of_lt hDpos)
    have hrle : r ≤ 1 := by
      apply (sq_le_sq₀ (le_of_lt hr) (by norm_num)).mp
      rw [hrsq]
      nlinarith
    have hphase :
        unitPhase d = d * (r : ℂ)⁻¹ := by
      simp [unitPhase, hd, r, D]
    have hcrossPhase :
        (d * (starRingEnd ℂ) (unitPhase d)).re = r := by
      have hdNorm : d * (starRingEnd ℂ) d = (D : ℂ) := by
        simp [D, Complex.normSq_eq_conj_mul_self, mul_comm]
      have hcomplex :
          d * (starRingEnd ℂ) (unitPhase d) =
            (D : ℂ) * (r : ℂ)⁻¹ := by
        rw [hphase, map_mul, starRingEnd_apply, map_inv₀,
          Complex.conj_ofReal]
        rw [← mul_assoc]
        rw [show d * star d = (D : ℂ) by
          simpa only [starRingEnd_apply] using hdNorm]
      rw [hcomplex, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
      simp only [Complex.ofReal_re]
      field_simp [ne_of_gt hr]
      nlinarith [hrsq]
    change
      complexEnergy (fun x ↦ f x - unitPhase d * (v x : ℂ)) ≤
        2 * R
    rw [complexEnergy_sub_const_mul_real v f (unitPhase d) hv,
      hf, normSq_unitPhase]
    change
      1 + 1 - 2 * (d * (starRingEnd ℂ) (unitPhase d)).re ≤
        2 * R
    rw [hcrossPhase, hR]
    nlinarith [hrsq,
      mul_nonneg (le_of_lt hr) (sub_nonneg.mpr hrle)]

set_option maxHeartbeats 1000000 in
/--
Phase-adjusted form of robust inverse uncertainty.  In addition to identifying
the primal and Fourier supports with affine subspaces, it approximates `f` by
a unit-modulus scalar times the normalized modulated indicator of the primal
coset.
-/
theorem robust_inverse_uncertainty_phase_implementation {n : ℕ}
    (S T : Finset (BooleanSpace n)) (f : BooleanSpace n → ℂ) {q : ℝ}
    (hq0 : 0 < q) (hq : q ≤ 1 / 100)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hf : complexEnergy f = 1)
    (hprimal :
      1 - q ^ 4 / 1024 ≤ energyOn S f)
    (hdual :
      (1 - q ^ 4 / 1024) * Fintype.card (BooleanSpace n) ≤
        energyOn T (walshFourier f))
    (hproduct :
      (S.card : ℝ) * T.card ≤
        (1 + q ^ 2 / 16) * Fintype.card (BooleanSpace n)) :
    ∃ H : Submodule (ZMod 2) (BooleanSpace n),
      ∃ a b : BooleanSpace n,
        (((S ∆ affineSubspacePoints H a).card : ℝ) ≤
          5 * q * S.card) ∧
        (((T ∆ affineSubspacePoints (perp H) b).card : ℝ) ≤
          12 * q * T.card) ∧
        ∃ c : ℂ, Complex.normSq c = 1 ∧
          complexEnergy
            (fun x ↦ f x -
              c * (Real.sqrt (Fintype.card H) : ℂ)⁻¹ *
                cosetWave H a b x) ≤
            264 * q := by
  obtain ⟨H, a, b, hSC, hTD, hrank⟩ :=
    robust_inverse_uncertainty S T f hq0 hq hS hT hf
      hprimal hdual hproduct
  let v := normalizedRealCosetWave H a b
  have hv : ∑ x, v x ^ 2 = 1 := by
    simpa [v] using normalizedRealCosetWave_energy H a b
  have hprojection :
      complexEnergy (fun x ↦ f x - realRankOne v f x) ≤
        132 * q := by
    simpa [v, realRankOne_normalizedCosetWave_eq H a b f] using hrank
  obtain ⟨c, hc, hphase⟩ :=
    exists_unit_phase_close_to_real_rankOne v f hv hf
  refine ⟨H, a, b, hSC, hTD, c, hc, ?_⟩
  calc
    complexEnergy
        (fun x ↦ f x -
          c * (Real.sqrt (Fintype.card H) : ℂ)⁻¹ *
            cosetWave H a b x) =
      complexEnergy (fun x ↦ f x - c * (v x : ℂ)) := by
        congr 1
        funext x
        rw [show v x = normalizedRealCosetWave H a b x by rfl,
          ofReal_normalizedRealCosetWave]
        ring
    _ ≤ 2 * complexEnergy
          (fun x ↦ f x - realRankOne v f x) := hphase
    _ ≤ 2 * (132 * q) :=
      mul_le_mul_of_nonneg_left hprojection (by norm_num)
    _ = 264 * q := by ring

end

end RobustInverseUncertainty
