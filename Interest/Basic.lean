import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic --  Orientation.oangle
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine --  EuclideanGeometry.oangle
import Mathlib.Order.Filter.Defs
/-!

## Financial Mathematis
Math 370
-/
section actuarial
open Finset

/-- The sum of a finite geometric series. -/
lemma sum_pow (n : ℕ) {x : ℝ} (hx : x ≠ 1) : ∑ i ∈ range n, x^i = (x ^ n - 1) / (x - 1) := by
  have hx : x - 1 ≠ 0 := sub_ne_zero_of_ne hx
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    suffices ((x ^ n - 1) / (x - 1) + x ^ n) * (x-1) =
             (x ^ (n + 1) - 1) / (x - 1) * (x-1) by
      rcases mul_eq_mul_right_iff.mp this with (h | h)
      exact h
      exact (hx h).elim
    rw [right_distrib]
    repeat rw [div_mul_cancel₀ _ hx]
    ring_nf

theorem sum_pow_interest {n : ℕ} {i : ℝ} (hi : i ≠ 0) (hi' : 1 + i ≠ 0) :
  ∑ k ∈ range (n + 1), (1 + i)⁻¹ ^ k - 1 = (1 - (1 + i)⁻¹ ^ n) / i := by
    have h₁ : (∑ k ∈ range (n + 1), (1 + i)⁻¹ ^ k ) - 1
      = ((1 + i)⁻¹ ^ (n + 1) - 1) / ((1 + i)⁻¹ - 1) - 1 := by
        rw [sum_pow (n+1) (fun hc => hi <| left_eq_add.mp (inv_eq_one.mp hc).symm)]
    have h₂ : ((1 + i)⁻¹ ^ (n + 1) - 1) / ((1 + i)⁻¹ - 1) - 1
       =  (1 - (1 + i)⁻¹ ^ n) / i := by
        suffices (((1 + i)⁻¹ ^ (n + 1) - 1) / ((1 + i)⁻¹ - 1) - 1) * i = (1 - (1 + i)⁻¹ ^ n) / i * i by
          cases mul_eq_mul_right_iff.mp this <;> tauto
        rw [div_mul_cancel₀ (1 - (1 + i)⁻¹ ^ n) hi, ← mul_div_mul_right _ _ hi']
        rw [sub_mul (1 + i)⁻¹ 1 _, one_mul, inv_mul_cancel₀ hi', sub_add_cancel_left 1 i]
        have : ((1 + i)⁻¹ ^ (n + 1) - 1) * (1 + i)
          = ((1 + i)⁻¹ ^ (n + 1) * (1+i) - 1*(1+i)) := by
            rw [sub_mul]
        rw [this]
        simp only [one_mul]
        rw [pow_succ, mul_assoc,inv_mul_cancel₀ hi', mul_one, sub_mul, one_mul]
        have : ((1 + i)⁻¹ ^ n - (1 + i)) / -i =
          - ((1 + i)⁻¹ ^ n - (1 + i)) / i := by
            field_simp
            ring_nf
        rw [this]
        rw [div_mul_cancel₀ _ hi, neg_sub]
        linarith
    exact h₁.trans h₂

/-- Annuities. -/
noncomputable def a : ℕ → ℝ → ℝ := fun n i =>
  ∑ k ∈ Icc 1 n, (1 + i)⁻¹ ^ k

/-- Annuity-due. -/
noncomputable def aquote : ℕ → ℝ → ℝ := fun n i =>
  ∑ k ∈ range n, (1 + i) ^ (n - k)


--ä ä
local notation "ä" n "⌝" i => aquote n i

theorem annuity_due_interest_zero {n : ℕ} : (ä n ⌝ 0) = n := by
  unfold aquote
  simp



/-- Annuities. This formula is only valid when i ≠ 0. -/
noncomputable def a_formula : ℕ → ℝ → ℝ  := fun n i =>
  (1 - ((1+i)⁻¹) ^ n) / i

/-- Annuities. Another variant. -/
noncomputable def a_variant : ℕ → ℝ → ℝ := fun n i =>
  ∑ k ∈ range (n + 1), (1 + i)⁻¹ ^ k - 1


/-- Actuarial notation. -/
local notation n "⌝" i => n i

open Finset
theorem a_eq_a_variant (n : ℕ) (i : ℝ) : (a n ⌝ i) = a_variant n i := by
  unfold a a_variant
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    symm at ih
    have :  ∑ x ∈ range (n + 1), ((1 + i)⁻¹ ^ x)
          = ∑ x ∈ Icc 1 n, ((1 + i)⁻¹ ^ x) + 1 := by
      linarith

    rw [this]
    suffices ∑ x ∈ Icc 1 (n + 1), ((1 + i)⁻¹ ^ x)
           = ∑ x ∈ Icc 1 n,       ((1 + i)⁻¹ ^ x) + ((1 + i)⁻¹ ^ (n + 1))
      by linarith
    exact sum_Icc_succ_top (by simp) fun k => (1+i)⁻¹ ^ k

example {n : ℕ} : a_variant n 0 = n := by simp [a_variant]

theorem a_eq_a_formula {i : ℝ} (hi : i ≠ 0) (hi' : 1 + i ≠ 0) :
  (fun n => a n ⌝ i) = fun n => a_formula n i := by
  ext n
  rw [a_eq_a_variant]
  rw [a_formula]
  rw [a_variant]
  rw [← @sum_pow_interest n i]
  tauto
  tauto

open Real
/-- A way too long proof ... -/
theorem annuity_limiting_value {i : ℝ} (hi : 0 < i) :
  Filter.Tendsto (fun n => a n ⌝ i)
  (Filter.atTop) (nhds (1/i)) := by
  rw [a_eq_a_formula (by linarith) (by linarith)]
  have h₃ : 0 ≤ 1 + i := by linarith
  have h₁ : 0 < (1+i)⁻¹ := by simp; linarith
  have h₀ : 0 ≤ (1+i)⁻¹ := by linarith
  have h₂ : 1 < 1 + i := by linarith
  have h₄ : 1 ≤ 1 + i := by linarith
  unfold a_formula
  apply ((continuous_mul_right _).tendsto _).comp
  conv => right; rw [← sub_zero 1]
  apply ((continuous_const.sub continuous_id').tendsto _).comp

  suffices Filter.Tendsto (fun n : ℝ ↦ (1 + i)⁻¹ ^ n) Filter.atTop (nhds 0) by
    refine tendsto_pow_atTop_nhds_zero_of_abs_lt_one ?_
    rw [abs_of_nonneg (by positivity)]
    exact inv_lt_one_iff₀.mpr $ .inr h₂
  apply Metric.tendsto_atTop'.mpr
  intro ε hε
  have h₅ : ε ≠ 0 := by linarith
  by_cases H : ε > 1
  · use 0
    intro n hn
    refine lt_trans ?_ H
    simp [abs_of_nonneg $ rpow_nonneg h₀ n]
    exact rpow_lt_one h₀ (inv_lt_one_iff₀.mpr <| .inr h₂) hn
  · have h₆ : 1 * ε ≤ 1 := by linarith
    use log (1/ε) / log (1+i)
    intro n hnε
    have hn : 0 ≤ n := by
      apply le_trans
      · show _ ≤ log (1 / ε) / log (1 + i)
        refine div_nonneg (log_nonneg (le_of_mul_le_mul_right ?_ hε)) (log_nonneg h₄)
        · rw [one_div_mul_cancel h₅]
          exact one_div_mul_cancel h₅ ▸ h₆
      · linarith
    simp [abs_of_nonneg $ rpow_nonneg h₀ n]
    refine (rpow_lt_iff_lt_log h₁ hε).mpr ?_
    have : log ε = - log (1/ε) := by
      rw [log_div (by simp) h₅, log_one]
      linarith
    rw [this, log_inv, mul_neg, neg_lt_neg_iff]
    exact (div_mul_cancel₀ (log (1 / ε)) (ne_of_gt ((log_pos_iff h₃).mpr h₂)))
            ▸ mul_lt_mul hnε (le_refl _) ((log_pos_iff h₃).mpr h₂) hn


  /-- The value of an annuity decreases with rising interest. -/
  theorem annuity_value_decreasing_with_rising_interest {n : ℕ}
      {i j : ℝ} (hj : 0 < i) (hij : i ≤ j) :
    (a_formula n ⌝ j) ≤ a_formula n ⌝ i := by
    unfold a_formula
    rw [← @sum_pow_interest n i]
    rw [← @sum_pow_interest n j]
    suffices  ∑ k ∈ range (n + 1), (1 + j)⁻¹ ^ k ≤ ∑ k ∈ range (n + 1), (1 + i)⁻¹ ^ k by linarith
    refine sum_le_sum ?_
    intro k hk
    refine pow_le_pow_left₀ ?_ ?_ k
    suffices 0 ≤ 1 + j by positivity
    linarith
    refine inv_anti₀ ?_ ?_
    linarith
    linarith
    linarith
    linarith
    linarith
    linarith

theorem annuity_value_pos {i : ℝ} (hi : i > 0) (n : ℕ) (hn : n >0) :
    0 < a_formula n ⌝ i := by
  unfold a_formula
  apply div_pos
  simp
  refine inv_lt_one_of_one_lt₀ ?_
  refine one_lt_pow₀ ?_ ?_
  linarith
  omega
  tauto

theorem annuity_value_bounded {i : ℝ} (hi : i > 0) (n : ℕ) :
  (a_formula n ⌝ i) ≤ 1/i := by
  unfold a_formula
  apply div_le_div₀
  · simp
  · simp
    positivity
  · tauto
  · simp

example (n : ℕ) : ∑ i ∈ range (n+1), (1/(2 : ℝ))^i = 2 - (1/(2 : ℝ))^n := by
  induction n with
  | zero => simp;linarith
  | succ n ih =>
    rw [sum_range_succ]
    rw [ih]
    field_simp
    ring_nf

  /-- The value of an annuity increases with time. -/
theorem annuity_value_increasing_with_time
  {n : ℕ} {i : ℝ} (hi : 0 < i) : (a_formula n ⌝ i) ≤ a_formula (n+1) ⌝ i := by
    have h₀ : (1 + i)⁻¹ ≤ 1 := by
      suffices 1 ≤ 1 + i by exact inv_le_one_of_one_le₀ this
      field_simp
      linarith
    unfold a_formula
    apply @div_le_div₀
    · suffices (1 + i)⁻¹ ^ (n + 1) ≤ 1 by
        linarith
      apply pow_le_one₀
      positivity
      tauto
    ring_nf
    suffices   (1 + i)⁻¹ * (1 + i)⁻¹ ^ n  ≤ (1 + i)⁻¹ ^ n by
      linarith
    suffices (1 + i)⁻¹ * (1 + i)⁻¹ ^ n ≤ 1 * (1 + i)⁻¹ ^ n by
      linarith
    refine mul_le_mul_of_nonneg_right h₀ ?_
    positivity
    tauto
    linarith

theorem annuity_at_time_two {i : ℝ} (H₀ : 1 + i ≠ 0) (H₁ : i ≠ 0) :
      (a_formula 2 ⌝ i) = (2+i) / ((1+i)^2) := by
    have := (@mul_eq_mul_right_iff ℝ _
      ((1 - (1 + i)⁻¹ ^ 2) / i)  ((2 + i) / (1 + i) ^ 2) (i*(1+i)^2)).mp (by
        field_simp
        ring_nf
      )
    cases this with
    | inl h => exact h
    | inr h =>
      exfalso
      cases mul_eq_zero.mp h with
      | inl h => tauto
      | inr h => apply H₀;exact pow_eq_zero h

theorem annuity_at_time_one {i : ℝ} (H₀ : 1 + i ≠ 0) (H₁ : i ≠ 0) :
      (a_formula 1 ⌝ i) = (1+i)⁻¹ := by
    unfold a_formula
    simp
    show  (1 - (1 + i)⁻¹) / i = (1 + i)⁻¹
    have help (a y₀ y₁ : ℝ) (h : a ≠ 0) (h₀ : a * y₀ = a * y₁) :
      y₀ = y₁ := by
        have := (@mul_eq_mul_left_iff ℝ _ a y₀ y₁).mp h₀
        tauto
    apply help
    exact H₁
    nth_rewrite 1 [mul_comm]

    have (x y : ℝ) (hx : y ≠ 0) : x / y * y = x := by
      exact div_mul_cancel₀ x hx
    rw [this]
    apply help
    exact H₀
    nth_rewrite 1 [mul_comm]
    nth_rewrite 2 [mul_comm]
    rw [mul_assoc]
    simp_all
    rw [sub_mul]
    simp_all
    exact H₁

theorem annuity_at_time_zero {i : ℝ} : (a_formula 0 ⌝ i) = 0 := by
    unfold a_formula
    simp

theorem annuity_with_interest_zero {n : ℕ} : (a_formula n ⌝ 0) = 0 := by
    unfold a_formula
    simp

theorem annuity_with_interest_one {n : ℕ} : (a_formula n ⌝ 1) = 1 - (1/2) ^ n := by
    unfold a_formula
    simp
    congr
    exact one_add_one_eq_two

theorem annuity_with_interest_half {n : ℕ} : (a_formula n ⌝ (1/2)) = 2 * (1 - (2/3) ^ n) := by
    unfold a_formula
    simp
    nth_rewrite 1 [mul_comm]
    congr
    ring_nf
    cases n with
    | zero => simp
    | succ n =>
      refine (pow_left_inj₀ ?_ ?_ ?_).mpr ?_
      positivity
      positivity
      positivity
      simp

end actuarial
