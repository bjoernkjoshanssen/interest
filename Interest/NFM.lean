import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-!

## Five implicit functions from the Annuity Equation

The BA II Plus calculator values PMT, I/Y, N, FV, PV
can each be computed from the other four.

Main results:

* `annuity_equation_unique_solvability`
* `TVM_equation_unique_solvability`: by setting PMT=0 in
  the annuity equation we obtain unique solution for the
  Time Value of Money equation as well.

-/

open Finset Real Filter

/-- The sum of a finite geometric series. -/
lemma sum_pow (n : ℕ) {x : ℝ} (hx : x ≠ 1) :
    ∑ i ∈ range n, x^i = (x ^ n - 1) / (x - 1) := by
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

lemma id_mul_geom_sum (x : ℝ) (hx : x ≠ 1) (n : ℕ) : ∑ k ∈ Finset.range (n+1), k * x^k =
  (x * (n * x^(n + 1) - ((n + 1) * x^n) + 1))/(x - 1)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp
    rw [ih]
    have h₀ : (x - 1) ^ 2 ≠ 0 := by
      simp
      contrapose! hx
      linarith
    field_simp
    ring_nf

lemma sum_Icc_succ_eq_sum_range (f : ℕ → ℝ) (n : ℕ) :
  f 0 + ∑ k ∈ Finset.Icc 1 n, f k
    = ∑ k ∈ Finset.range (n+1), f k := by
  have := @Nat.range_succ_eq_Icc_zero
  rw [this]
  have : Finset.Icc 0 n = Finset.Ico 0 1 ∪ Finset.Icc 1 n := by
    ext j
    simp
    constructor
    intro
    by_cases H : j = 0
    left
    tauto
    right
    simp at H
    constructor
    contrapose! H
    linarith
    tauto
    intro h
    cases h with
    | inl h => subst h;simp
    | inr h => tauto
  rw [this]
  simp
  rw [Finset.sum_union]
  simp
  simp

lemma id_mul_geom_sum₁ (x : ℝ) (hx : x ≠ 1) (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, k * x^k =
  (x * (n * x ^ (n + 1) - ((n + 1) * x ^ n) + 1)) / (x - 1) ^ 2 := by
  let f : ℕ → ℝ := fun k => k * x^ k
  show ∑ k ∈ Finset.Icc 1 n, f k =
  (x * (n * x ^ (n + 1) - ((n + 1) * x ^ n) + 1)) / (x - 1) ^ 2

  suffices f 0 + ∑ k ∈ Finset.Icc 1 n, f k =
    (x * (n * x ^ (n + 1) - ((n + 1) * x ^ n) + 1)) / (x - 1) ^ 2 by
    rw [← this]
    unfold f
    simp
  rw [sum_Icc_succ_eq_sum_range]
  apply id_mul_geom_sum
  tauto

namespace annuity

/-- The present value of the first `n` payments of an annuity of
1 per period, with interest rate `i`.
There is a notation clash with the accumulation function `a`.
`annuity.a` versus `a`.
Etymology: a for annuity.
-/
noncomputable def a : ℕ → ℝ → ℝ := fun n i =>
  ∑ k ∈ Icc 1 n, (1 + i)⁻¹ ^ k

/-- Increasing annuity. -/
noncomputable def Ia : ℕ → ℝ → ℝ := fun n i =>
  ∑ k ∈ Icc 1 n, k * (1 + i)⁻¹ ^ k

/-- Price of a bond with unit redemption value, coupon rate r, interest rate i. -/
noncomputable def bond_price : ℕ → ℝ → ℝ → ℝ := fun n i r =>
  (r * a n i + (1+i)⁻¹ ^ n)


/-- Macaulay duration of a maturity `n`, level-payments bond (with redemption value 1)
with coupon rate `r` and yield rate `i`. -/
noncomputable def D : ℕ → ℝ → ℝ → ℝ := fun n i r =>
  (r * Ia n i + n * (1+i)⁻¹ ^ n) /
  bond_price n i r



/-- The present value of a level-payments annuity
with at least one payment is positive. -/
lemma annuity_positive {n : ℕ} (hn : n ≠ 0) {i : ℝ} (hi : i > -1) :
  a n i > 0 := by
  unfold a
  have : 0 < 1 + i := by linarith
  have : 0 < (1 + i)⁻¹ := Right.inv_pos.mpr this
  have : ∀ k ∈ Finset.Icc 1 n, 0 < (1+i)⁻¹ ^ k := by
    intro k hk
    exact pow_pos this k
  suffices ∑ k ∈ Icc 1 n, (1 + i)⁻¹ ^ k >
     ∑ k ∈ Icc 1 n, 0 by simp at this ⊢;exact this
  refine sum_lt_sum ?_ ?_

  intro k hk
  apply le_of_lt
  apply this _ hk
  use 1
  constructor
  simp
  omega
  simp
  tauto

-- lemma annuity_antitone (n : ℕ) (hn : n ≠ 0) {i j : ℝ} (hi : i > -1)
--     (hij : i < j) :
--   a n j < a n i := by
--   unfold a
--   refine sum_lt_sum ?_ ?_
--   intro k hk
--   refine (pow_le_pow_iff_left₀ ?_ ?_ ?_).mpr ?_
--   simp
--   linarith
--   simp
--   linarith
--   simp at hk
--   linarith
--   apply inv_anti₀ <;>linarith
--   use 1
--   simp
--   constructor
--   contrapose! hn
--   linarith
--   refine (inv_lt_inv₀ ?_ ?_).mpr ?_
--   linarith
--   linarith
--   linarith



/-- The present value of a level-payments annuity is nonnegative. -/
lemma annuity_nonneg (n : ℕ) {i : ℝ} (hi : i > -1) :
  a n i ≥ 0 := by
  unfold a
  have : 0 < 1 + i := by linarith
  have : 0 < (1 + i)⁻¹ := Right.inv_pos.mpr this
  have : ∀ k ∈ Finset.Icc 1 n, 0 < (1+i)⁻¹ ^ k := by
    intro k hk
    exact pow_pos this k
  suffices ∑ k ∈ Icc 1 n, (1 + i)⁻¹ ^ k ≥
     ∑ k ∈ Icc 1 n, 0 by simp at this ⊢;exact this
  refine sum_le_sum ?_
  intro k hk
  apply le_of_lt
  apply this _ hk

lemma bond_price_pos (n : ℕ) {i r : ℝ} (hi : i > -1) (hr : 0 ≤ r) : 0 < bond_price n i r := by
  have h₀ : a n i ≥ 0 := annuity_nonneg n hi
  have h₁ : r * a n i ≥ 0 := by apply mul_nonneg;tauto;tauto
  have h₂ : ((1 + i)⁻¹) > 0 := by simp;linarith
  have h₃ : ((1 + i)⁻¹ ^ n) > 0 := by simp;apply pow_pos;linarith
  unfold bond_price
  exact calc 0 < (1 + i)⁻¹ ^ n := h₃
         _ ≤ _ := by apply le_add_of_nonneg_left;tauto


lemma increasing_annuity_nonneg (n : ℕ) {i : ℝ} (hi : i > -1) :
  Ia n i ≥ 0 := by
  unfold Ia
  have : 0 < 1 + i := by linarith
  have : 0 < (1 + i)⁻¹ := Right.inv_pos.mpr this
  have : ∀ k ∈ Finset.Icc 1 n, 0 < (1+i)⁻¹ ^ k := by
    intro k hk
    exact pow_pos this k
  suffices ∑ k ∈ Icc 1 n, k * (1 + i)⁻¹ ^ k ≥
     ∑ k ∈ Icc 1 n, 0 by simp at this ⊢;exact this
  refine sum_le_sum ?_
  intro k hk
  apply le_of_lt
  apply mul_pos
  simp at hk ⊢
  linarith
  apply this _ hk

/-- A bond with unit redemption value and maturity 1 has Macaulay duration 1. -/
lemma D_one {i r : ℝ} (hi : i > -1) (hr : r ≥ 0) : D 1 i r = 1 := by
  unfold D Ia bond_price a
  simp
  apply div_self
  apply ne_of_gt
  have h₄ := by apply bond_price_pos 1 hi hr
  simp [bond_price,a] at h₄
  exact h₄


def duration_equation (n : ℕ) (i r d : ℝ) :=
   d * bond_price n i r - (r * Ia n i + ↑n * (1 + i)⁻¹ ^ n) = 0

/-- A coupon-free bond has Macaulay duration equal to its maturity date. -/
lemma r_zero (n : ℕ) (i : ℝ) : duration_equation n i 0 n := by
  simp [duration_equation, bond_price]



/-- The Macaulay duration does indeed satisfy the duration equation. -/
lemma D_duration_equation (n : ℕ) {i r : ℝ} (hi : i > -1) (hr : r ≥ 0) :
  duration_equation n i r (D n i r) := by
  unfold duration_equation D
  have := bond_price_pos n hi hr
  generalize bond_price n i r = b at *
  field_simp

/-- The maturity date as a trivial upper bound on the Macaulay duration. -/
lemma D_upper_bound (n : ℕ) {i r : ℝ} (hi : i > -1) (hr : r ≥ 0) : D n i r ≤ n := by
  have h₄ := by apply bond_price_pos n hi hr
  unfold bond_price at h₄
  apply (div_le_iff₀ h₄).mpr
  suffices r * Ia n i ≤ r * (↑n * a n i) by
    linarith
  apply mul_le_mul_of_nonneg_left
  unfold Ia a
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro k hk
  simp at hk
  refine mul_le_mul_of_nonneg_right ?_ ?_
  simp
  exact hk.2
  apply pow_nonneg
  simp
  linarith
  exact hr



  lemma D_lower_bound (n : ℕ) {i r : ℝ} (hi : i > -1) (hr : r ≥ 0) : 0 ≤ D n i r := by
    have h : 1 + i ≥ 0 := by linarith
    apply div_nonneg
    apply add_nonneg $ mul_nonneg hr $ increasing_annuity_nonneg _ hi
    apply mul_nonneg $ Nat.cast_nonneg _
    apply pow_nonneg $ inv_nonneg.mpr h
    apply add_nonneg
    exact mul_nonneg hr $ annuity_nonneg _ hi
    apply pow_nonneg $ inv_nonneg.mpr h



/-- Future value of an annuity-immediate. s for sum.
-/
noncomputable def s : ℕ → ℝ → ℝ := fun n i => (1 + i) ^ n * a n i


/-- Present value of an annuity-due.
Because double-dot notation is used, we call it `a_double_dot`
or for short `a_dots`.
-/
noncomputable def a_dots : ℕ → ℝ → ℝ := fun n i =>
  ∑ k ∈ Ico 0 n, (1 + i)⁻¹ ^ k

/-- Future value of an annuity-due. -/
noncomputable def s_dots : ℕ → ℝ → ℝ := fun n i =>
  (1 + i) ^ n * a_dots n i


/-- Actuarial notation. -/
local notation n "⌝" i => n i


--ä ä  s̈
local notation "ä" => a_dots
local notation "s̈" => s_dots

/-- In case of zero interest,
the present value of the `n` payments of `1` is simply `n`. -/
@[simp]
theorem annuity_due_interest_zero {n : ℕ} :
    (ä n ⌝ 0) = n := by simp [a_dots]

@[simp]
theorem annuity_immediate_interest_zero {n : ℕ} :
    (a n ⌝ 0) = n := by simp [a]

/-- In case of zero interest,
the future value of the `n` payments of `1` is simply `n`. -/
theorem future_value_annuity_due_interest_zero {n : ℕ} :
    (s̈ n ⌝ 0) = n := by simp [s_dots]

/-- Formula for the present value of an annuity-immediate.
This formula is only valid when i ≠ 0. -/
noncomputable def a_formula : ℕ → ℝ → ℝ  := fun n i =>
  (1 - ((1+i)⁻¹) ^ n) / i

/-- Annuities. Another variant. -/
noncomputable def a_variant : ℕ → ℝ → ℝ := fun n i =>
  (∑ k ∈ range (n + 1), (1 + i)⁻¹ ^ k) - 1

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


lemma par_bond_price (n : ℕ) {i : ℝ} (hi : i > 0) :
    bond_price n i i = 1 := by
  unfold bond_price
  have := congrFun $ @a_eq_a_formula i (by linarith) (by linarith)
  rw [this]
  unfold a_formula
  field_simp
  linarith


/-- The maturity of an at-par bond with rate `i`
and Macaulay duration `d`. -/
noncomputable def CPT_N_from_D_par (i d : ℝ) :=
    log (1 - d * (1 - (1+i)⁻¹)) / log (1+i)⁻¹

/-- Determine the maturity from the duration
 for an at-par bond. -/
lemma eq_CPT_N_from_D_par (n : ℕ) {i : ℝ} (hi : i > 0) (d : ℝ)
    (h :  duration_equation n i i d) :
    n = CPT_N_from_D_par i d := by
    unfold CPT_N_from_D_par
    unfold duration_equation at h
    rw [par_bond_price n hi] at h
    unfold Ia at h
    have := @id_mul_geom_sum₁ (1+i)⁻¹ (by
        intro hc;simp at hc;subst hc;simp at hi) n
    rw [this] at h
    have : (1+i)⁻¹ ≠ 1 := by intro hc;simp at hc;linarith
    have : ((1+i)⁻¹ - 1)^2 ≠ 0 := by
        contrapose! this;simp at this;linarith
    have h₀ : i * (1+i)⁻¹ = 1 - (1+i)⁻¹ := by field_simp
    have : (1+i)⁻¹ - 1 ≠ 0 := by
        contrapose! this
        rw [this]
        simp
    have : 1 - (1+i)⁻¹ ≠ 0 := by
        contrapose! this
        linarith
    have : i * (1+i)⁻¹ ≠ 0 := by
        simp;constructor <;> linarith
    have hiv : i = ((1+i)⁻¹)⁻¹ - 1 := by field_simp
    have hivn : log ((1+i)⁻¹ ^ n) = n * log (1+i)⁻¹ := by
        simp
    have hlogv : log (1+i)⁻¹ ≠ 0 := by
        simp
        constructor
        linarith
        constructor <;> linarith
    set v := (1+i)⁻¹
    field_simp at h
    ring_nf at h
    set y := v^n
    have h :  d * (1-v) ^ 2 - v * i +
        y * (i * v * (1 + (1-v) * ↑n)
        -n * (1-v)^2) = 0 := by linarith [v,y]
    rw [h₀] at h
    have :  d * (1 - v) ^ 2 - v * i + y * ((1 - v)) = 0
        := by linarith
    have : y = (v * i - d * (1 - v) ^ 2)/ ((1 - v)) := by
        field_simp
        linarith
    have hv : v / (1 - v) = 1/i := by
        rw [← h₀];field_simp;ring_nf
    have : y = (v * i - d * (1 - v) ^ 2)/ ((1 - v)) := by
        field_simp
        linarith
    have : y = i * (v / (1 - v))  - d * (1-v):= by
        field_simp
        linarith
    rw [hv] at this
    field_simp at this
    have : log y = log (1 - d * (1-v)) := by rw [this]
    rw [hivn] at this
    rw [← this]
    field_simp



/- An ambitious quest: show that n can be computed from D,i,r when r < i: -/
-- lemma CPT_N_from_D (n : ℕ) {i r : ℝ} (hi : i > 0) (hr : r ≥ 0) (d x : ℝ)
--     (h :  duration_equation n i r d) : n = x := by
--   unfold duration_equation bond_price at h
--   unfold Ia at h
--   have := @id_mul_geom_sum₁ (1+i)⁻¹ (by intro hc;simp at hc;subst hc;simp at hi) n
--   rw [this] at h
--   have := congrFun $ @a_eq_a_formula i (by linarith) (by linarith)
--   rw [this] at h
--   repeat clear this
--   unfold a_formula at h
--   have : (1+i)⁻¹ ≠ 1 := by intro hc;simp at hc;linarith
--   have : ((1+i)⁻¹ - 1)^2 ≠ 0 := by intro hc;simp at hc;apply this;linarith
--   generalize (1+i)⁻¹ = v at *
--   field_simp at h
--   ring_nf at h
--   generalize v^n = y at h
--   have :  y * (d*(i-r)*(1-v)^2
--     + r * v * i * (1 + (1-v) * ↑n)
--         -i*n*(1-v)^2) =
--   - (d*r*(1-v)^2 - r * v * i) := by linarith
--   -- y -> 0
--   -- we see that if i=r we cannot solve for d.
--   sorry


/-- The value of a perpetuity of `1` per period with interest rate `i`
 is `1 / i`. For example, if `i = 1` we get `1/2 + 1/4 + ... = 1`. -/
theorem annuity_limiting_value {i : ℝ} (hi : 0 < i) :
  Tendsto (fun n => a n ⌝ i) atTop (nhds (1/i)) := by
  rw [a_eq_a_formula (by linarith) (by linarith)]
  have h₀ : 0 ≤ (1 + i)⁻¹ := inv_nonneg_of_nonneg (le_of_lt <| by linarith)
  apply ((continuous_mul_right _).tendsto _).comp
  conv => right; rw [← sub_zero 1]
  exact ((continuous_const.sub continuous_id').tendsto _).comp $
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one $ abs_of_nonneg h₀ ▸
    inv_lt_one_iff₀.mpr $ .inr $ lt_add_of_pos_right 1 hi


lemma annuity_antitone {N : ℕ} (hN : N ≠ 0)
    ⦃a b : ℝ⦄ (hab : a < b) (ha : -1 < a) :
    annuity.a N b < annuity.a N a := by
  unfold annuity.a
  apply sum_lt_sum
  intro t ht
  simp at ht ⊢
  refine inv_anti₀ ?_ ?_
  have : 0 < 1 + a := by linarith
  positivity
  refine (pow_le_pow_iff_left₀ ?_ ?_ ?_).mpr ?_ <;> linarith
  use 1
  constructor
  simp
  omega
  simp
  refine inv_strictAnti₀ ?_ ?_ <;> linarith


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


  /-- The value of an annuity increases with the number of payments. -/
theorem annuity_value_increasing_with_time
    {n : ℕ} {i : ℝ} (hi : 0 < i) :
    (a_formula n ⌝ i) ≤ a_formula (n+1) ⌝ i := by
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

end annuity

/-- The BA II Plus Professional equation. -/
def annuity_equation (IY PMT PV FV : ℝ) (N : ℕ) : Prop :=
  PV + PMT * (annuity.a N (IY / 100)) + FV * (1 + IY/100)⁻¹ ^ N = 0

noncomputable def CPT_PV (IY PMT FV : ℝ) (N : ℕ) :=
  - PMT * (annuity.a N (IY / 100)) - FV * (1 + IY/100)⁻¹ ^ N

noncomputable def CPT_FV (IY PMT PV : ℝ) (N : ℕ) :=
  (- PV - PMT * (annuity.a N (IY / 100))) / ((1 + IY/100)⁻¹ ^ N)

noncomputable def CPT_N (IY PMT PV FV : ℝ) :=
  (log ((PV * (IY / 100) + PMT) / (PMT - FV * (IY / 100)))) /
      (log (1 + IY / 100)⁻¹)

/-- [CPT] [PV] is quite simple: -/
lemma PV_eq_CPT_PV {IY PMT PV FV : ℝ} {N : ℕ}
    (h : annuity_equation IY PMT PV FV N) :
    PV = CPT_PV IY PMT FV N := by
  unfold annuity_equation at h
  unfold CPT_PV
  linarith

/-- [CPT] [FV] is simple as long as [I/Y] is not `-100`: -/
lemma FV_eq_CPT_FV {IY PMT PV FV : ℝ} {N : ℕ}
    (h : annuity_equation IY PMT PV FV N)
    (h₀ : IY ≠ -100) :
    FV = CPT_FV IY PMT PV N := by
  unfold annuity_equation at h
  rw [PV_eq_CPT_PV h]
  unfold CPT_PV CPT_FV
  ring_nf
  have : 1 + IY * (1 / 100) ≠ 0 := by
    contrapose! h₀
    linarith
  generalize 1 + IY * (1 / 100) = x at *
  field_simp



-- [CPT] [N] is simple enough using the `(1-v^n)/i` formula
lemma N_eq_CPT_N {IY PMT PV FV : ℝ} {N : ℕ}
    (h : annuity_equation IY PMT PV FV N)
    (h₀ : IY ≠ 0)
    (h₁ : IY ≠ -100)
    (h₄ : IY / 100 ≠ -2)
    (h_nonpar : FV * (IY / 100) - PMT ≠ 0) :
    N = CPT_N IY PMT PV FV := by
  unfold annuity_equation at h
  have := @annuity.a_eq_a_formula (IY / 100) (by contrapose! h₀; linarith)
    (by contrapose! h₁;linarith)
  rw [congrFun this] at h
  unfold annuity.a_formula at h
  have h₃ : log ((1 + IY / 100)⁻¹ ^ N) =
        N * log (1 + IY / 100)⁻¹ :=
    log_pow (1 + IY / 100)⁻¹ N
  generalize (1 + IY / 100)⁻¹ ^ N = V at *
  have g₀ : - (PMT * ((1 - V) / (IY / 100)) + FV * V) = PV := by linarith
  have g₁ : PMT * (1 - V) + FV * V * (IY / 100) = - PV * (IY / 100) := by
    rw [← g₀]
    field_simp
    linarith
  have g₂ : V * (FV * (IY / 100) - PMT) = - PV * (IY / 100) - PMT := by
    linarith
  have g₃ : V  = (- PV * (IY / 100) - PMT)
               / ((FV * (IY / 100) - PMT)) := by
    generalize FV * (IY / 100) - PMT = y at *
    field_simp
    linarith
  rw [g₃] at h₃
  have g₀ : log (1 + IY / 100)⁻¹ ≠ 0 := by
    simp
    constructor
    · contrapose! h₁
      linarith
    constructor
    · exact h₀
    · contrapose! h₄
      linarith
  have : N = (log ((-PV * (IY / 100) - PMT)
    / (FV * (IY / 100) - PMT))) / (log (1 + IY / 100)⁻¹) := by
      generalize (log (1 + IY / 100)⁻¹) = z at *
      generalize
        log ((-PV * (IY / 100) - PMT) / (FV * (IY / 100) - PMT))
        = w at *
      field_simp
      linarith
  unfold CPT_N
  suffices (PV * (IY / 100) + PMT) / (PMT - FV * (IY / 100))
   = (-PV * (IY / 100) - PMT) / (FV * (IY / 100) - PMT) by
    rw [this];linarith
  have : FV * (IY / 100) - PMT = - (PMT - FV * (IY / 100)) := by linarith
  rw [this]
  have : (-PV * (IY / 100) - PMT)
       = - (PV * (IY / 100) + PMT) := by linarith
  rw [this]
  exact (neg_div_neg_eq
    (PV * (IY / 100) + PMT) (PMT - FV * (IY / 100))).symm


lemma discount_continuity {i : ℝ} (k : ℕ) :
  ContinuousOn (fun y ↦ (1 + y)⁻¹ ^ k) (Set.Ioc (-1) i) := by
  apply ContinuousOn.pow
  apply (continuous_add_left _).continuousOn.inv₀
  intro x hx
  simp at hx
  apply ne_of_gt
  linarith

lemma annuity_continuous {i : ℝ} {N : ℕ} : ContinuousOn
    (fun i ↦ annuity.a N i)
    (Set.Ioc (-1) i) :=
        (continuous_finset_sum _ fun i _ ↦ continuous_apply i).comp_continuousOn'
        <|continuousOn_pi.mpr discount_continuity

lemma annuity_equation_continuity {PMT PV FV i : ℝ} {N : ℕ} : ContinuousOn
    (fun i ↦ PV + PMT * annuity.a N i + FV * (1 + i)⁻¹ ^ N)
    (Set.Ioc (-1) i) := by
  apply ContinuousOn.add
  · exact (continuous_add_left _).comp_continuousOn'
      <|(continuous_mul_left _).comp_continuousOn' annuity_continuous
  · exact (continuous_mul_left FV).comp_continuousOn' (discount_continuity _)

/-- We can eliminate the unnatural assumption by going to IY ≥ 0. -/
lemma of_IY_nonneg {IY PV PMT FV : ℝ} {N : ℕ}
    (h : annuity_equation IY PMT PV FV N)
    (hIY : IY ≥ 0) (hPMT : PMT ≥ 0) (hFV : FV > 0) :
    -- PMT ≥ 0 should be enough, and would give TVM equation as a special
    -- case.
    0 ≤ PV + PMT * ↑N + FV := by
  unfold annuity_equation at h
  rw [← h]
  suffices PMT * annuity.a N (IY / 100) + FV * (1 + IY / 100)⁻¹ ^ N
         ≤ PMT * ↑N + FV
    by linarith
  suffices PMT * annuity.a N (IY / 100) ≤ PMT * N ∧
    FV * (1 + IY / 100)⁻¹ ^ N ≤  FV by
      linarith
  constructor
  by_cases H : PMT = 0
  subst H
  simp
  have hPMT : PMT > 0 := by contrapose! H;linarith
  apply (mul_le_mul_iff_of_pos_left hPMT).mpr
  unfold annuity.a
  apply le_trans
  show _ ≤  ∑ k ∈ Icc 1 N, 1
  apply sum_le_sum
  intro i hi
  have : 1 + IY / 100 ≥ 1 := by linarith
  simp
  apply inv_le_one_of_one_le₀
  by_cases H : i = 0
  · subst H
    simp
  apply one_le_pow₀
  linarith
  simp
  apply (mul_le_iff_le_one_right hFV).mpr
  simp

  suffices 1 ≤ ((1 + IY / 100) ^ N) by
    exact inv_le_one_of_one_le₀ this
  by_cases H : N = 0
  · subst H
    simp
  refine one_le_pow₀ ?_
  linarith

lemma CPT_IY_unique.aux {PMT PV FV : ℝ}
    (hPMT : PMT > 0) (hPV : PV < 0) (hFV : FV > 0) :
    let ι := 2 * max FV PMT / -PV;
    PV + PMT * (1 / ι) + FV * (1 + ι)⁻¹ < 0 := by
  have his : IsUnit (-PV) := by simp;linarith
  intro ι
  rw [one_div_div, ← one_div, ← (IsUnit.mul_div_mul_left his 1 _)]
  rw [LeftDistribClass.left_distrib, mul_div_cancel₀ _ (by linarith)]
  have : PV + PMT * (-PV / (2 * max FV PMT))
       + FV * (-PV * 1 / (-PV * 1 + 2 * max FV PMT))
       = PV * (1 + PMT * (-1 / (2 * max FV PMT))
       + FV * (-1 * 1 / (-PV * 1 + 2 * max FV PMT))) := by
    ring_nf
  rw [this]
  apply mul_neg_of_neg_of_pos hPV
  simp
  suffices - (PMT * (-1 / (2 * max FV PMT))
    + FV * (-1 / (-PV + 2 * max FV PMT))) < 1 by linarith
  cases max_choice FV PMT with
  | inl h =>
    rw [h];ring_nf
    have : PMT * FV⁻¹ ≤ 1 :=
      mul_inv_le_one_of_le₀ (sup_eq_left.mp h) <| le_of_lt hFV
    have h₀ : 1 / 2 + FV * (FV * 2 - PV)⁻¹ < 1 := by
      suffices FV * (FV * 2 - PV)⁻¹ < 1/2 by linarith
      suffices FV / (FV * 2 + -PV) < 1/2 by simp at this ⊢;tauto
      apply (mul_lt_mul_left _).mp
      simp
      have : 2 * (FV / (FV * 2 + -PV)) = (FV * 2) / (FV * 2 + -PV) := by
        ring_nf
      rw [this]
      simp
      apply (div_lt_one₀ _).mpr
      linarith
      linarith
      simp
    calc _ ≤ (1 / 2) + FV * (FV * 2 - PV)⁻¹ := by linarith
         _ < _ := h₀
  | inr h =>
    rw [h];ring_nf
    rw [CommGroupWithZero.mul_inv_cancel PMT <| by linarith]
    suffices FV * (PMT * 2 - PV)⁻¹ < 1/2 by linarith
    have : FV ≤ PMT := le_of_sup_eq h
    have : (PMT * 2 + -PV)⁻¹ = (PMT * 2 - PV)⁻¹ := by ring_nf
    rw [← this]
    have : 0 < -PV := by simp;tauto
    have : 0 < PMT * 2 + -PV := by positivity
    have : 0 < (PMT * 2 + -PV)⁻¹ := by positivity
    suffices PMT * (PMT * 2 + -PV)⁻¹ < 1 / 2 by
      calc _ ≤ _ := (mul_le_mul_iff_of_pos_right (by tauto)).mpr (by tauto)
           _ < _ := this
    apply (mul_lt_mul_left _).mp
    have : 2 * (PMT * (PMT * 2 + -PV)⁻¹)
        =  PMT * 2 / (PMT * 2 + -PV) := by ring_nf
    rw [this]
    simp
    apply (div_lt_one₀ _).mpr
    linarith
    tauto
    simp


lemma natpow_rpow (M : ℕ) (x : ℝ) (hx : x > 0) :
    x ^ M = exp (M * log x) := by
  rw [mul_comm]
  apply Eq.trans (rpow_natCast x M).symm <| rpow_def_of_pos hx M

lemma TVM_interest_exists {PV FV : ℝ} {N : ℕ} (hN : N ≠ 0) (hPV : PV < 0)
    (hFV : FV > 0) (h : 0 ≤ PV + FV) :
    ∃ i, 0 ≤ i ∧ PV + FV * ((1 + i) ^ N)⁻¹ = 0 := by
  use exp (log (FV / -PV) * (1 / N)) - 1
  have : -PV ≤ FV := by linarith
  have : FV / -PV ≥ 1 := (one_le_div₀ (by linarith)).mpr (by linarith)
  constructor
  · generalize FV / -PV = α at *
    simp
    apply mul_nonneg
    · exact log_nonneg this
    · simp
  rw [add_sub_cancel, natpow_rpow]
  field_simp
  rw [exp_log]
  have h₀ : PV * (FV / -PV) = - (PV * (FV / PV)) := by ring_nf
  rw [h₀, mul_div_left_comm, div_self (by linarith)]
  field_simp
  aesop
  apply exp_pos

lemma PV_FV_aux {PV FV : ℝ} (hPV : PV < 0) (hFV : FV > 0) :
    let ι := 2 * FV / -PV;
    ι ≥ 0 → PV + FV * (1 + ι)⁻¹ < 0 := by
  intro ι hι
  suffices PV + FV / (1 + ι) < 0 by simp at this ⊢;tauto
  suffices FV / (1 + ι) < -PV by linarith
  suffices FV < (-PV) * (1 + ι) by
    refine (div_lt_iff₀ ?_).mpr this
    linarith
  unfold ι
  suffices FV + PV < -PV * (2 * FV / -PV) by linarith
  have : -PV * (2 * FV / -PV) = 2 * FV := by
    refine mul_div_cancel₀ (2 * FV) ?_
    simp
    linarith
  rw [this]
  linarith

lemma CPT_IY.concrete.aux₀ {PV FV : ℝ} {N : ℕ} (hN : N ≠ 0) (hPV : PV < 0) (hFV : FV > 0) :
    let ι := 2 * FV / -PV;
    PV + FV * (1 + ι)⁻¹ ^ N < 0 := by
  intro ι
  have hι : ι ≥ 0 := by
    repeat apply mul_nonneg
    all_goals
      try simp
      try linarith
  calc _ ≤  PV + FV * (1 + ι)⁻¹ := by -- same proof as below
        repeat apply (add_le_add_iff_left _).mpr
        apply (mul_le_mul_iff_of_pos_left hFV).mpr
        have h₀ : (1 + ι)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ <| by linarith
        have h₁ : (1 + ι)⁻¹ ≥ 0 := by simp;linarith
        exact pow_le_of_le_one h₁ h₀ hN
  _ < _ := by apply PV_FV_aux <;> tauto

lemma CPT_IY.concrete {PMT PV FV : ℝ} {N : ℕ} (hN : N ≠ 0) (hPV : PV < 0)
    (hFV : FV > 0) (H : ¬PMT = 0) :
    let ι := 2 * max FV PMT / -PV;
    ι > 0 → PV + PMT * annuity.a N ι + FV * (1 + ι)⁻¹ ^ N < 0 := by
      intro ι hι
      have (i : ℝ) (hi : i > 0) : annuity.a N i < 1/i := by
        rw [congrFun (annuity.a_eq_a_formula (i:=i) (by linarith) (by linarith)) N]
        apply (div_lt_div_iff_of_pos_right hi).mpr
        apply sub_lt_self
        positivity
      have hι₁ : ι > -1 := by
        apply lt_trans
        show -1 < 0
        simp
        apply mul_pos
        simp
        left
        exact hFV
        simp
        exact hPV
      have := this ι hι
      by_cases hPMT : PMT < 0
      · apply lt_trans
        show _ < PV + FV * (1 + ι)⁻¹ ^ N
        suffices PMT * annuity.a N ι < 0 by linarith
        apply mul_neg_iff.mpr
        · right
          constructor
          · exact hPMT
          · exact annuity.annuity_positive hN hι₁
        · convert CPT_IY.concrete.aux₀ hN hPV hFV
          apply max_eq_left
          linarith
      apply lt_trans
      · show _ < PV + PMT * (1 / ι) + FV * (1 + ι)⁻¹ ^ N
        have hPMT : PMT > 0 := by contrapose! H;linarith
        repeat rw [add_assoc]
        exact (add_lt_add_iff_left _).mpr <| (add_lt_add_iff_right _).mpr
          <| (mul_lt_mul_left hPMT).mpr this
      calc
      _ ≤ PV + PMT * (1 / ι) + FV * (1 + ι)⁻¹ := by
        repeat rw [add_assoc]
        repeat apply (add_le_add_iff_left _).mpr
        apply (mul_le_mul_iff_of_pos_left hFV).mpr
        have h₀ : (1 + ι)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ <| by linarith
        have h₁ : (1 + ι)⁻¹ ≥ 0 := by simp;linarith
        exact pow_le_of_le_one h₁ h₀ hN
      _ < _ := by
        apply CPT_IY_unique.aux
        contrapose! H; linarith
        tauto
        tauto

/-- Existence of interest rate satisfying
 annuity equation. -/
theorem CPT_IY.aux₀ {PMT PV FV : ℝ} {N : ℕ} (hN : N ≠ 0)
  (h : 0 ≤ PV + PMT * N + FV)
  (hPV : PV < 0) (hFV : FV > 0) :
  ∃ i ≥ 0, PV + PMT * annuity.a N i + FV * (1 + i)⁻¹ ^ N = 0 := by
    by_cases H : PMT = 0
    · subst H
      simp at h ⊢
      exact TVM_interest_exists hN hPV hFV h
    let ι := 2 * (max FV PMT) / (-PV)
    have hι : ι > 0 := by
      repeat apply mul_pos
      exact Nat.ofNat_pos
      exact lt_sup_of_lt_left hFV
      simp
      exact hPV
    let f := (fun i ↦ PV + PMT * annuity.a N i + FV * (1 + i)⁻¹ ^ N)
    have : 0 ∈ Set.Icc (f ι) (f 0) := by
        constructor
        · exact le_of_lt <| CPT_IY.concrete hN hPV hFV H hι
        · simp [f, annuity.a]
          exact h
    have ⟨j,hj⟩:= intermediate_value_Icc'
      (by show 0 ≤ ι;linarith) (by
        have := @annuity_equation_continuity
        apply ContinuousOn.mono
        apply this
        exact ι
        intro x hx
        simp at hx ⊢
        constructor
        linarith
        tauto
        ) this
    use j
    exact ⟨hj.1.1, hj.2⟩

lemma annuity_strictAnti {PMT PV FV : ℝ} {N : ℕ} (hN : N ≠ 0)
    (hPMT : PMT ≥ 0) (hFV : FV > 0) : StrictAntiOn
    (fun i ↦ PV + PMT * annuity.a N i + FV * (1 + i)⁻¹ ^ N)
    (Set.Ioi (-1)) := fun a ha b hb hab => by
  simp at ha hb ⊢
  have : ((1 + b) ^ N)⁻¹ < ((1 + a) ^ N)⁻¹ := by
      refine inv_strictAnti₀ ?_ ?_
      have : 0 < 1 + a := by linarith
      positivity
      refine pow_lt_pow_left₀ ?_ ?_ hN <;> linarith
  have : FV * ((1 + b) ^ N)⁻¹ < FV * ((1 + a) ^ N)⁻¹ :=
    (mul_lt_mul_left hFV).mpr <| by tauto
  by_cases H : PMT = 0
  · subst H
    simp
    exact this
  have hPMT : PMT > 0 := by contrapose! H;apply le_antisymm H hPMT
  have : PMT * annuity.a N b  < PMT * annuity.a N a :=
    (mul_lt_mul_left hPMT).mpr <| annuity.annuity_antitone hN hab ha
  linarith

noncomputable def a_inv_exists {n : ℕ} (hn : n ≠ 0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃! i > -1, ε = annuity.a n i := by
        have : (n:ℝ) ≥ 1 := by simp;omega
        have hmm (m : ℕ) (hm : m ≥ 1) : annuity.a n (-1 + 1/m) ≥ m := by
            unfold annuity.a
            have : ∑ k ∈ Icc 1 n, ((1:ℝ) + (-1 + 1 / m))⁻¹ ^ k
                = ∑ k ∈ Icc 1 n, (((1:ℝ) / m))⁻¹ ^ k := by
                apply sum_congr rfl
                intro k hk
                congr
                linarith
            rw [this]
            have : ((1:ℝ) / m)⁻¹ = m := by
                simp
            rw [this]
            simp
            calc (m:ℝ) ≤ ∑ k ∈ Icc 1 n, ↑m ^ 1 := by
                    simp
                    by_cases H : m = 0
                    subst H
                    simp
                    suffices (1:ℝ) * m ≤ n * m by simp at this; exact this
                    apply mul_le_mul_of_nonneg
                    tauto;simp;simp;simp
                  _ ≤ _ := by
                    apply sum_le_sum
                    intro k hk
                    simp at hk
                    refine Bound.pow_le_pow_right_of_le_one_or_one_le ?_
                    left
                    constructor
                    simp;tauto
                    tauto
        have : annuity.a n 0 = n := by unfold annuity.a;simp
        by_cases H : ε < 1
        have : annuity.a n (2 * n / ε - 1) < ε := by
            unfold annuity.a
            have : ∑ k ∈ Icc 1 n, (1 + (2*n / ε - 1))⁻¹ ^ k
                =  ∑ k ∈ Icc 1 n, (2*n / ε)⁻¹ ^ k := by
                congr
                ext k
                congr
                linarith
            rw [this]
            calc _ ≤  ∑ k ∈ Icc 1 n, (2*n / ε)⁻¹ := by
                    apply sum_le_sum
                    intro k hk
                    have : (2*n / ε)⁻¹ ≤ 1 := by
                        simp
                        calc ε / (2*n) ≤ 1 / (2*n) := by
                                refine div_mul_le_div_mul_of_div_le_div ?_ ?_
                                refine (div_le_div_iff_of_pos_right ?_).mpr ?_
                                simp
                                linarith
                                simp
                             _ ≤ _ := by
                                suffices 1 ≤ 2 * n by
                                    refine (one_div_le ?_ ?_).mp ?_
                                    simp
                                    simp
                                    linarith
                                    simp
                                    have : (n:ℝ) ≥ 1 := by simp;linarith
                                    linarith
                                calc 1 ≤ n := by contrapose! hn;linarith
                                     _ ≤ 2 * n := by omega
                    have : k ≥ 1 := by simp at hk;tauto
                    have : 0 ≤ (2*n / ε)⁻¹ := by
                        simp
                        apply div_nonneg
                        linarith
                        simp
                    apply pow_le_of_le_one
                    tauto
                    tauto
                    linarith
                 _ < _ := by
                    simp;ring_nf
                    simp
                    field_simp
                    tauto
        have : (n:ℝ) ≥ 1 := by simp;omega
        have : n / 1 ≤ n / ε := by
            refine (div_le_div_iff₀ ?_ ?_).mpr ?_
            simp
            tauto
            refine (mul_le_mul_iff_of_pos_left ?_).mpr ?_
            linarith
            linarith
        simp at this
        have ⟨i,hi⟩ := @intermediate_value_Icc' ℝ _ _ _ _ ℝ _ _ _ 0 (2 * n / ε - 1)
            (by
                calc (0:ℝ) ≤ 2 * n - 1 := by linarith
                     _ ≤ _ := by field_simp;rw [← mul_div];linarith)
                     (annuity.a n) (by
                        have := @annuity_continuous
                        apply @ContinuousOn.mono ℝ ℝ _ _ (annuity.a n)
                        apply this
                        exact (2 * ↑n / ε - 1)
                        intro x hx
                        simp at hx ⊢
                        constructor
                        linarith
                        tauto
                        ) ε (by
                     simp
                     constructor <;> linarith)
        simp at hi
        use i
        simp
        constructor
        constructor
        linarith
        tauto
        intro y hy hyε
        by_contra H
        have : y < i ∨ i < y := lt_or_gt_of_ne H
        cases this with
        | inl h =>
            have := @annuity.annuity_antitone n hn y i h hy
            linarith
        | inr h =>
            have := @annuity.annuity_antitone n hn i y h (by linarith)
            linarith

        have : annuity.a n (2 * n - 1) < ε := by
            unfold annuity.a
            simp at H
            have :  ∑ k ∈ Icc 1 n, ((1:ℝ) + (2 * ↑n - 1))⁻¹ ^ k
                =  ∑ k ∈ Icc 1 n, ( ((2:ℝ) * ↑n))⁻¹ ^ k := by
                simp
            rw [this]
            have :  ∑ k ∈ Icc 1 n, ( ((2:ℝ) * ↑n))⁻¹ ^ k
                ≤ ∑ k ∈ Icc 1 n, ( ((2:ℝ) * ↑n))⁻¹ := by
                apply sum_le_sum
                intro k hk
                simp at hk
                have :  ((2:ℝ) * ↑n)⁻¹ ≥ 0 := by
                    positivity
                refine pow_le_of_le_one ?_ ?_ ?_
                linarith
                suffices 1 ≤ 2 * (n:ℝ) by
                    exact inv_le_one_of_one_le₀ this
                calc _ ≤ (n:ℝ) := by linarith
                     _ ≤ _ := by linarith
                linarith

            calc _ ≤ _ := this
                 _ < (1:ℝ) := by
                    rw [Finset.sum_const];simp;field_simp
                    suffices (n:ℝ) < n * 2 by
                        refine (div_lt_one₀ ?_).mpr this
                        simp;omega
                    linarith
                 _ ≤ _ := H
        have ⟨m,hm⟩ : ∃ m : ℕ, m ≥ ε := exists_nat_ge ε

        have ⟨i,hi⟩ := @intermediate_value_Icc' ℝ _ _ _ _ ℝ _ _ _
            (-1 + 1/m) (2 * n - 1)
            (by
                suffices  (1:ℝ) / ↑m ≤ 2 * ↑n by linarith
                apply le_trans
                show (1:ℝ) / m ≤ 1
                simp at H
                apply le_trans
                show 1 / m ≤ 1 / ε
                exact one_div_le_one_div_of_le hε hm
                exact (div_le_one₀ hε).mpr H
                apply le_trans
                show (1:ℝ) ≤ n
                simp;omega
                apply le_trans
                show (n:ℝ) ≤ 1 * (n:ℝ)
                simp
                refine mul_le_mul_of_nonneg_right ?_ ?_
                simp
                simp) (annuity.a n) (by

                have := @annuity_continuous
                apply ContinuousOn.mono
                apply this
                exact 2*n-1
                intro x hx
                simp at hx ⊢
                constructor
                calc -1 < -1 + (m:ℝ)⁻¹ := by
                        refine lt_neg_add_iff_add_lt.mpr ?_
                        simp only [add_neg_cancel, inv_pos]
                        linarith
                     _  ≤ x := by linarith
                tauto
                ) ε
            (by
                simp
                constructor
                linarith
                apply le_trans hm
                specialize hmm m (by
                    simp at H
                    have : (1:ℝ) ≤ m := by linarith
                    simp at this
                    tauto)
                simp at hmm
                convert hmm)
        simp at hi this
        use i
        simp
        constructor
        constructor
        calc -1 < -1 + (m:ℝ)⁻¹ := by
                    refine lt_neg_add_iff_add_lt.mpr ?_
                    simp only [add_neg_cancel, inv_pos]
                    linarith
                _  ≤ i := by linarith

        tauto
        intro y hy hyε
        by_contra H
        have : y < i ∨ i < y := lt_or_gt_of_ne H
        cases this with
        | inl h =>
            have := @annuity.annuity_antitone n hn y i h hy
            linarith
        | inr h =>
            have := @annuity.annuity_antitone n hn i y h (by
                calc -1 < -1 + (m:ℝ)⁻¹ := by
                            refine lt_neg_add_iff_add_lt.mpr ?_
                            simp only [add_neg_cancel, inv_pos]
                            linarith
                        _  ≤ i := by linarith)
            linarith

/-- Inverse of the annuity function. -/
noncomputable def a_inv {n : ℕ} (hn : n ≠ 0) :
    Set.Ioc (0:ℝ) n →  ℝ :=
    fun ε => (a_inv_exists hn ε.2.1).choose

lemma sub_nat_real {n : ℕ} (hn : n ≥ 2) {i : ℝ} {d : ℝ}
  (hd₁ : d ≤ ↑n) (h : annuity.duration_equation n i i d) : d - 1 ≤ ↑(n - 1) := by
        simp
        convert hd₁
        obtain ⟨m,hm⟩ : ∃ m, n = m + 2 := Nat.exists_eq_add_of_le' hn
        subst hm
        simp
        linarith

/-- Perhaps surprisingly:
Let i be the implied interest rate for an n-period
par bond of duration d.
Then the PV of an (n-1)-period unit-payment annuity with rate i is d-1.
This lets us compute `i` from `n` and `d`.
 -/
lemma eq_CPT_I_from_D_par
    {n : ℕ} (hn : n ≥ 2 ) -- if n=1, then D=n and we can't infer i.
    {i : ℝ} (hi : i > 0)
    {d : ℝ} (hd : 0 < d - 1)
    (hd₁ : d ≤ n) -- can deduce this from `h`
    (h :  annuity.duration_equation n i i d) :
    i = a_inv (by show n-1 ≠ 0;contrapose! hn;omega)
        ⟨d - 1, ⟨hd, sub_nat_real hn hd₁ h⟩⟩ := by
    have ⟨j,hj⟩ := @a_inv_exists n (by linarith) i hi
    unfold annuity.duration_equation annuity.bond_price at h
    rw [congrFun $ annuity.a_eq_a_formula (by linarith) (by linarith)] at h
    unfold annuity.a_formula annuity.Ia at h
    have := @id_mul_geom_sum₁ (1+i)⁻¹ (by
        intro hc;simp at hc;subst hc;simp at hi) n
    rw [this] at h
    clear this
    have : i ≠ 0 := by linarith
    set v := (1+i)⁻¹
    have hv₂ : (v - 1) ^ 2 ≠ 0 := by
        unfold v
        simp
        intro hc
        have : (1 + i)⁻¹ = 1 := by linarith
        have : (1 + i) = 1 := by field_simp at this;rw [this];simp
        linarith
    rw [mul_comm i] at h
    rw [div_mul] at h
    field_simp at h
    have h₀ :
        - (i * v) * (
            ↑n * v ^ (n + 1)
            - (↑n + 1) * v ^ n
            + 1)
        + (d - ↑n * v ^ n) * (v - 1) ^ 2
        = 0 := by
        linarith
    have : i * v = 1 - v := by
        unfold v
        field_simp
    rw [this] at h₀
    have : -1 * ((v - 1) * (- (d * v) + d + v^n - 1)) = 0 := by
        ring_nf at h₀ this
        linarith
    have : v - 1 ≠ 0 := by contrapose! hv₂;rw [hv₂];simp
    have : (v - 1) * (- (d * v) + d + v^n - 1) = 0 := by
        linarith
    have : (- (d * v) + d + v^n - 1) = 0 := by
        apply (mul_eq_zero_iff_left _).mp this
        tauto
    have : d + v^n - (d * v) - 1 = 0 := by
        linarith
    have : v^n - d * v + d - 1 = 0 := by
        linarith
    have : (v^n - d * v + d - 1) / (v - 1) = 0 := by
        rw [this]
        simp
    obtain ⟨t,ht⟩ : ∃ m, n = m + 2 := Nat.exists_eq_add_of_le' hn
    obtain ⟨m,hm⟩ : ∃ m, n = m + 1 := by
        use t+1
    subst hm
    have hw : (v^(m+1) - d * v + d - 1) = (v - 1) * (annuity.a m i - d + 1) := by
        have : v ^ (m+1) = v^m * v := rfl
        rw [this]
        rw [sub_mul]
        have := congrFun $ @annuity.a_eq_a_formula i (by linarith) (by linarith)
        rw [this]
        unfold annuity.a_formula v
        field_simp
        ring_nf
    have : (annuity.a m i - d + 1) = 0 := by
        rw [hw, mul_comm] at this
        rw [← this]
        field_simp
    simp at hj
    have : annuity.a m i = d - 1 := by linarith
    have := (@a_inv_exists (m) (by linarith) (d-1) (by
        linarith
        )).choose_spec

    simp at this
    have := this.2 i (by linarith) (by tauto)
    simp_rw [this]
    unfold a_inv
    simp





-- lemma a_inv_is_inverse  (n : ℕ) (hn : n ≠ 0) (ε :Set.Icc (0:ℝ) n) :
--     Function.LeftInverse (a_inv n hn) (fun i => ⟨ite (0 ≤ i) (annuity.a n i) 0, by
--         simp
--         constructor
--         by_cases H : 0 ≤ i
--         rw [if_pos H]
--         apply annuity.annuity_positive hn (by linarith)
--         rw [if_neg H]

--         sorry⟩) := by
--     sorry

/-- Unique solution of annuity equation for interest rate,
 via the Intermediate Value Theorem. -/
theorem CPT_IY_unique {PMT PV FV : ℝ} {N : ℕ} (hN : N ≠ 0)
    (hPMT : PMT ≥ 0)
    (h : 0 ≤ PV + PMT * ↑N + FV)
    (hPV : PV < 0) (hFV : FV > 0):
    ∃ IY, (IY ≥ 0 ∧ annuity_equation IY PMT PV FV N)
    ∧ ∀ IY', (IY' > -100 ∧ annuity_equation IY' PMT PV FV N) → IY' = IY
    := by
  unfold annuity_equation
  let f : ℝ → ℝ := fun i => PV + PMT * annuity.a N i + FV * (1 + i)⁻¹ ^ N
  have ⟨i,hi⟩ : ∃ i ≥ 0, f i = 0 := CPT_IY.aux₀ hN h hPV hFV
  have : ∃ i, (i ≥ 0 ∧ f i = 0) ∧ ∀ j, (j > -1 ∧ f j = 0) → j = i := by
    use i
    constructor
    exact hi
    intro j hj
    by_contra H
    have Hi : i ∈ Set.Ioi (-1) := by simp;linarith
    have Hj : j ∈ Set.Ioi (-1) := by simp;linarith
    rcases (lt_or_gt_of_ne fun a ↦ H a.symm) with (g | g)
    all_goals
      have ha: StrictAntiOn f (Set.Ioi (-1)) := annuity_strictAnti hN hPMT hFV
      specialize ha (by tauto) (by tauto) g; linarith
  obtain ⟨i,hi⟩ := this
  use i * 100
  constructor
  · constructor
    · simp at hi
      linarith
    · unfold f at hi
      convert hi.1.2 <;> linarith
  · ring_nf
    intro J hJ
    have := hi.2 (J/100)
    simp at hJ ⊢ this
    specialize this (by linarith) (by
      unfold f
      rw [← hJ.2]
      congr
      simp
      congr)
    linarith


/-- The [CPT] [IY] button combination on the BA II Plus Financial. -/
noncomputable def CPT_IY₁ {PMT PV FV : ℝ} {N : ℕ} (hN : N ≠ 0)
    (hPMT : PMT ≥ 0) (h : 0 ≤ PV + PMT * ↑N + FV)
    (hPV : PV < 0) (hFV : FV > 0): ℝ :=
  (CPT_IY_unique hN hPMT h hPV hFV).choose


/-- [CPT] [IY] gives the only solution for interest rate per year. -/
lemma IY_eq_CPT_IY₁ {PMT PV FV IY : ℝ} {N : ℕ} (hN : N ≠ 0)
    (hPMT : PMT ≥ 0) (h : 0 ≤ PV + PMT * ↑N + FV)
    (hPV : PV < 0) (hFV : FV > 0) (hann : annuity_equation IY PMT PV FV N)
    (h₀ : IY > -100) : IY = CPT_IY₁ hN hPMT h hPV hFV :=
  (CPT_IY_unique hN hPMT h hPV hFV).choose_spec.2 _ ⟨h₀, hann⟩

noncomputable def CPT_PMT (IY PV FV : ℝ) (N : ℕ) :=
  (-PV - FV * (1 + IY / 100)⁻¹ ^ N) / annuity.a N (IY / 100)

lemma PMT_eq_CPT_PMT.aux {IY : ℝ} {N : ℕ}
    (h₀ : IY > -100) (hN : N ≠ 0)
    (h₂ : (100 / (100 + IY)) ^ N = 1 ^ N) : 100 / (100 + IY) = 1 := by
  simp at h₂
  have hα : 100 / (100 + IY) ≥ 0 := by
    apply div_nonneg
    simp
    linarith
  generalize 100 / (100 + IY) = α at *
  rw [← Nonneg.mk_eq_one hα, ← pow_eq_one_iff hN]
  exact NNReal.eq h₂


/-- [CPT] [PMT] gives the only solution for payment. -/
lemma PMT_eq_CPT_PMT {IY PMT PV FV : ℝ} {N : ℕ}
  (h : annuity_equation IY PMT PV FV N) (h₀ : IY > -100) (hN : N ≠ 0) :
  PMT = CPT_PMT IY PV FV (N) := by
  unfold annuity_equation at h
  have : annuity.a N (IY / 100) ≠ 0 := by
    by_cases H : IY = 0
    · unfold annuity.a
      subst H
      simp
      tauto
    have := @annuity.a_eq_a_formula (IY / 100)
      (by contrapose! H; linarith) (by contrapose! h₀;linarith)
    rw [congrFun this]
    unfold annuity.a_formula
    simp
    constructor
    · field_simp
      contrapose! H
      have : 100 ^ N / (100 + IY) ^ N
        = (100 / (100 + IY)) ^ N := by ring_nf
      rw [this] at H
      have : (100 / (100 + IY)) ^ N = 1 ^ N := by field_simp;linarith
      have : 100 / (100 + IY) = 1 := by
        apply PMT_eq_CPT_PMT.aux <;> tauto
      grind
    · tauto
  unfold CPT_PMT
  grind

noncomputable def CPT_IY {IY PMT PV FV : ℝ} {N : ℕ}
    (hann : annuity_equation IY PMT PV FV N)
    (hN : N ≠ 0) (hPMT : PMT ≥ 0) (hPV : PV < 0) (hFV : FV > 0)
    (h₀ : IY ≥ 0) :=
  CPT_IY₁ hN hPMT (of_IY_nonneg hann h₀ hPMT hFV) hPV hFV

/--
Main theorem on unique solvability of the Annuity Equation.
To deduce interest rate we need time to pass,
and hence the number of periods N>0.
To deduce the payment there must be at least one payment,
and hence again N>0.
To deduce N, the coupon rate should not equal the yield rate and hence
`FV * (IY / 100) - PMT ≠ 0`.
These assumptions, together with appropriate positivity and negativity,
suffice for unique existence of all variables.
-/
theorem annuity_equation_unique_solvability {IY PMT PV FV : ℝ} {N : ℕ}
    (hann : annuity_equation IY PMT PV FV N)
    (hPMT : PMT ≥ 0) (hPV : PV < 0) (hFV : FV > 0) (hIY : IY > 0) :
    ((hN : N ≠ 0) →
    PMT = CPT_PMT IY PV FV N ∧
    IY  = CPT_IY hann hN hPMT hPV hFV (by linarith)) ∧
    PV  = CPT_PV IY PMT FV N ∧
    FV  = CPT_FV IY PMT PV N ∧ (PMT ≠ FV * (IY / 100) →
    N   = CPT_N IY PMT PV FV) := by
  have hI₀ : IY > -100 := by linarith
  have hI₁ : IY ≠ -100 := by linarith
  have hI₂ : IY / 100 ≠ -2 := by linarith
  constructor
  · intro hN
    constructor
    exact PMT_eq_CPT_PMT hann hI₀ hN
    exact IY_eq_CPT_IY₁ _ _ _ _ _ hann hI₀
    -- exact IY_eq_CPT_IY _ _ (by apply of_IY_nonneg hann;linarith;tauto;tauto) _ _ hann hI₀
  · constructor
    exact PV_eq_CPT_PV hann
    constructor
    · exact FV_eq_CPT_FV hann hI₁
    · intro hx
      exact N_eq_CPT_N hann (ne_of_gt hIY) hI₁ hI₂ (by contrapose! hx;linarith)


/-- By setting `PMT=0` we obtain the unique solvability of the
Time Value of Money equation. -/
theorem TVM_equation_unique_solvability {IY PV FV : ℝ} {N : ℕ}
    (hann : annuity_equation IY 0 PV FV N)
    (hPV : PV < 0) (hFV : FV > 0) (hIY : IY > 0) :
    ((hN : N ≠ 0) →
    0  = CPT_PMT IY PV FV N ∧
    IY = CPT_IY hann hN (by simp) hPV hFV (by linarith)) ∧
    PV = CPT_PV IY 0 FV N ∧
    FV = CPT_FV IY 0 PV N ∧
    N  = CPT_N IY 0 PV FV := by
  have hI₀ : IY > -100 := by linarith
  have hI₁ : IY ≠ -100 := by linarith
  have hI₂ : IY / 100 ≠ -2 := by linarith
  constructor
  · intro hN
    constructor
    exact PMT_eq_CPT_PMT hann hI₀ hN
    exact IY_eq_CPT_IY₁ _ _ _ _ _ hann hI₀
  · constructor
    exact PV_eq_CPT_PV hann
    constructor
    · exact FV_eq_CPT_FV hann hI₁
    · exact N_eq_CPT_N hann (ne_of_gt hIY) hI₁ hI₂ (by
        simp
        constructor <;> linarith)

/-- CPT_IY returns a value satisfying the annuity equation. -/
lemma CPT_IY_satisfies {PV PMT FV : ℝ} {N : ℕ} (hN : N ≠ 0)
  (hFV : FV > 0) (hPV : PV < 0)
  (hPMT : PMT ≥ 0) (h : 0 ≤ PV + PMT * ↑N + FV) :
  let hann := (CPT_IY_unique hN hPMT h hPV hFV).choose_spec.1
  let IY := CPT_IY hann.2 hN hPMT hPV hFV hann.1
  annuity_equation IY PMT PV FV N :=
    (CPT_IY_unique hN hPMT h hPV hFV).choose_spec.1.2

-- of_IY_nonneg shows that `h` is equivalent to this happening:
lemma CPT_IY_satisfies_iff {PV PMT FV : ℝ} {N : ℕ} (hN : N ≠ 0)
  (hFV : FV > 0) (hPV : PV < 0)
  (hPMT : PMT ≥ 0) :
  0 ≤ PV + PMT * N + FV ↔
  ∃ IY ≥ 0,
  annuity_equation IY PMT PV FV N := by
    constructor
    · intro h
      let hann := (CPT_IY_unique hN hPMT h hPV hFV).choose_spec.1
      use CPT_IY hann.2 hN hPMT hPV hFV hann.1
      constructor
      · exact hann.1
      · exact CPT_IY_satisfies hN hFV hPV hPMT h
    · exact fun ⟨IY, hIY⟩ => of_IY_nonneg hIY.2 hIY.1 hPMT hFV



/-- If CPT_N returns a Nat then it satisfies the annuity equation.
(If it doesn't, we could prove it satisfies a modified annuity equation.)
-/
theorem CPT_N_satisfies {IY PMT PV FV : ℝ} (N : ℕ)
    (hIY₁ : IY/100 > 0)
    (h_nonpar : PMT - FV * (IY/100) ≠ 0) -- necessary if we're going to have hope computing N
    (hNat : N = CPT_N IY PMT PV FV) :
    0 < (PV * (IY/100) + PMT) / (PMT - FV * (IY/100)) ↔ annuity_equation IY PMT PV FV N := by
  constructor
  intro hIY
  unfold annuity_equation
  rw [congrFun (@annuity.a_eq_a_formula (IY / 100) (by linarith) (by linarith)) N]
  unfold annuity.a_formula
  rw [natpow_rpow N (1 + IY / 100)⁻¹ (by simp;linarith)]
  unfold CPT_N at hNat
  rw [hNat]
  have hln : log (1 + IY / 100)⁻¹ ≠ 0 := by
    refine log_ne_zero_of_pos_of_ne_one ?_ ?_
    all_goals simp;linarith
  rw [div_mul, div_self hln]
  simp
  generalize IY / 100 = i at *
  rw [exp_log hIY]
  field_simp
  ring_nf

  intro hann
  unfold annuity_equation at hann
  have := congrFun (@annuity.a_eq_a_formula (IY / 100) (by linarith) (by linarith)) N
  rw [this] at hann
  unfold annuity.a_formula at hann
  generalize IY / 100 = i at *
  have : (1 + i)⁻¹ ^ N > 0 := by
    apply pow_pos <| inv_pos.mpr <| by linarith
  generalize (1 + i)⁻¹ ^ N = x at *
  field_simp at hann
  have : PV * i + PMT  - (PMT - FV * i) * x = 0 := by
    linarith
  have : x = (PV * i + PMT) / (PMT - FV * i) := by
    field_simp
    linarith
  rw [← this]
  tauto

theorem CPT_PV_satisfies {IY PMT FV : ℝ} {N : ℕ} :
    annuity_equation IY PMT (CPT_PV IY PMT FV N) FV N := by
  unfold CPT_PV annuity_equation
  linarith

theorem CPT_FV_satisfies {IY PMT PV : ℝ} {N : ℕ} (hIY : IY > -100):
    annuity_equation IY PMT PV (CPT_FV IY PMT PV N) N := by
  unfold CPT_FV annuity_equation
  have : IY / 100 > -1 := by linarith
  generalize IY / 100 = i at *
  have : (1 + i)⁻¹ ^ N > 0 := by
    apply pow_pos <| inv_pos.mpr <| by linarith
  rw [div_mul]
  generalize (1 + i)⁻¹ ^ N = α at *
  field_simp

theorem CPT_PMT_satisfies {IY PV FV : ℝ} {N : ℕ} (hN : N ≠ 0)
 (hIY : IY > -100) :
    annuity_equation IY (CPT_PMT IY PV FV N) PV FV N := by
  unfold CPT_PMT annuity_equation
  rw [div_mul]
  have : IY / 100 > -1 := by linarith
  have : annuity.a N (IY / 100) > 0 := annuity.annuity_positive hN this
  have : (1 + IY / 100)⁻¹ ^ N > 0 := by
    apply pow_pos <| inv_pos.mpr <| by linarith
  field_simp
  linarith

/-- If PV=0 and i=-1, the annuity equation holds for
PMT = CPT_PMT or any other PMT value. -/
theorem CPT_PMT_satisfies_when_PV_eq_zero {FV PMT : ℝ} {N : ℕ} (hN : N ≠ 0) :
    annuity_equation (-100) PMT 0 FV N := by
  simp [annuity_equation, annuity.a]
  rw [zero_pow_eq_zero.mpr hN]
  simp
  right
  have : ∑ x ∈ Icc 1 N, (0 ^ x : ℝ) = ∑ x ∈ Icc 1 N, (0 : ℝ) :=
    sum_congr rfl fun x hx => by
    simp at hx ⊢
    linarith
  rw [this]
  simp
