import Mathlib.Analysis.InnerProductSpace.PiL2
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
    field_simp
    ring_nf

theorem sum_pow_interest (n : ℕ) {i : ℝ} (hi : i ≠ 0) (hi' : 1 + i ≠ 0) :
  ∑ k ∈ range (n + 1), (1 + i)⁻¹ ^ k - 1 = (1 - (1 + i)⁻¹ ^ n) / i :=
  .trans (congrArg (fun x => x-1) <| sum_pow (n+1)
    fun hc => hi <| left_eq_add.mp (inv_eq_one.mp hc).symm) (by grind)

/-- The value of the first `n` payments of an annuity of 1 per period,
with interest rate `i`. -/
noncomputable def a : ℕ → ℝ → ℝ := fun n i =>
  ∑ k ∈ Icc 1 n, (1 + i)⁻¹ ^ k

/-- Annuity-due. -/
noncomputable def aquote : ℕ → ℝ → ℝ := fun n i =>
  ∑ k ∈ range n, (1 + i) ^ (n - k)


--ä ä
local notation "ä" n "⌝" i => aquote n i

@[simp]
theorem annuity_due_interest_zero {n : ℕ} : (ä n ⌝ 0) = n := by simp [aquote]

example {n : ℕ} : (ä n ⌝ 0) + (ä n ⌝ 0) = 2 * n := by
  simp
  ring_nf

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
  simp only [a, a_variant]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← add_eq_of_eq_sub ih]
    suffices ∑ x ∈ Icc 1 (n + 1), ((1 + i)⁻¹ ^ x)
           = ∑ x ∈ Icc 1 n,       ((1 + i)⁻¹ ^ x) + ((1 + i)⁻¹ ^ (n + 1))
      by rw [this];ring_nf
    exact sum_Icc_succ_top (by simp) fun k => (1+i)⁻¹ ^ k

example {n : ℕ} : a_variant n 0 = n := by simp [a_variant]

theorem a_eq_a_formula {i : ℝ} (hi : i ≠ 0) (hi' : 1 + i ≠ 0) :
  (fun n => a n ⌝ i) = fun n => a_formula n i := by
  ext n
  rw [a_eq_a_variant, a_formula, a_variant, ← sum_pow_interest n hi hi']

open Real Filter
/-- The value of a perpetuity of `1` per period with interest rate `i`
 is `1 / i`. For example, if `i = 1` we get `1/2 + 1/4 + ... = 1`. -/
theorem annuity_limiting_value {i : ℝ} (hi : 0 < i) :
  Tendsto (fun n => a n ⌝ i) atTop (nhds (1/i)) := by
  rw [a_eq_a_formula (by linarith) (by linarith)]
  have h₀ : 0 ≤ (1 + i)⁻¹ := inv_nonneg_of_nonneg (le_of_lt <| by linarith)
  apply ((continuous_mul_right _).tendsto _).comp
  conv => right; rw [← sub_zero 1]
  exact ((continuous_const.sub continuous_id').tendsto _).comp $
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one $
    abs_of_nonneg h₀ ▸ inv_lt_one_iff₀.mpr $ .inr $ lt_add_of_pos_right 1 hi



  /-- The value of an annuity decreases with rising interest. -/
  theorem annuity_value_decreasing_with_rising_interest {n : ℕ}
      {i j : ℝ} (hj : 0 < i) (hij : i ≤ j) :
    (a_formula n ⌝ j) ≤ a_formula n ⌝ i := by
    unfold a_formula
    have hi₀ : i ≠ 0 := by linarith
    have hi₁ : 1 + i ≠ 0 := by linarith
    have hj₀ : j ≠ 0 := by linarith
    have hj₁ : 1 + j ≠ 0 := by linarith
    rw [← sum_pow_interest n hi₀ hi₁, ← sum_pow_interest n hj₀ hj₁]
    apply tsub_le_tsub_right
    apply sum_le_sum
    intro k hk
    apply pow_le_pow_left₀
    · rw [inv_nonneg]
      linarith
    · exact inv_anti₀ (by linarith) (by linarith)

theorem annuity_value_pos {i : ℝ} (hi : i > 0) (n : ℕ) (hn : n > 0) :
    0 < a_formula n ⌝ i := by
  apply div_pos
  · simp only [inv_pow, sub_pos]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by linarith) (by omega))
  · exact hi

theorem annuity_value_bounded {i : ℝ} (hi : i > 0) (n : ℕ) :
    (a_formula n ⌝ i) ≤ 1 / i :=
  div_le_div₀ zero_le_one (by ring_nf;simp;positivity) hi (by simp)

example (n : ℕ) : ∑ i ∈ range (n+1), (1/(2 : ℝ))^i = 2 - (1/(2 : ℝ))^n := by
  induction n with
  | zero => simp;linarith
  | succ n ih =>
    rw [sum_range_succ, ih]
    field_simp
    ring_nf

  /-- The value of an annuity increases with the number of pay periods. -/
theorem annuity_value_increasing_with_time
  {n : ℕ} {i : ℝ} (hi : 0 < i) : (a_formula n ⌝ i) ≤ a_formula (n+1) ⌝ i := by
    have h₀ : (1 + i)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      linarith
    apply div_le_div₀
    · suffices (1 + i)⁻¹ ^ (n + 1) ≤ 1 by linarith
      apply pow_le_one₀ (by positivity) h₀
    · ring_nf
      suffices (1 + i)⁻¹ * (1 + i)⁻¹ ^ n ≤ 1 * (1 + i)⁻¹ ^ n by
        linarith
      refine mul_le_mul_of_nonneg_right h₀ ?_
      positivity
    · exact hi
    · linarith

theorem annuity_at_time_two {i : ℝ} (H₀ : 1 + i ≠ 0) (H₁ : i ≠ 0) :
      (a_formula 2 ⌝ i) = (2+i) / ((1+i)^2) := by grind [a_formula]

theorem annuity_at_time_one {i : ℝ} (H₀ : 1 + i ≠ 0) (H₁ : i ≠ 0) :
      (a_formula 1 ⌝ i) = (1+i)⁻¹ := by grind [a_formula]

theorem annuity_at_time_zero {i : ℝ} : (a_formula 0 ⌝ i) = 0 := by simp [a_formula]

theorem annuity_with_interest_zero {n : ℕ} : (a_formula n ⌝ 0) = 0 := by simp [a_formula]

theorem annuity_with_interest_one {n : ℕ} : (a_formula n ⌝ 1) = 1 - (1/2) ^ n := by
    simp [a_formula]
    congr
    exact one_add_one_eq_two

theorem annuity_with_interest_half {n : ℕ} : (a_formula n ⌝ (1/2)) = 2 * (1 - (2/3) ^ n) := by
    simp [a_formula]
    nth_rewrite 1 [mul_comm]
    congr
    ring_nf
    cases n with
    | zero => simp
    | succ n =>
      apply (pow_left_inj₀ ?_ ?_ ?_).mpr (by simp) <;> positivity

end actuarial
