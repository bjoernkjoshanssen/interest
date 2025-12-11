import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!

## Five-way solvability of the Annuity Equation in Lean
-/
open Finset

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


namespace annuity

/-- The present value of the first `n` payments of an annuity of
1 per period, with interest rate `i`.
There is a notation clash with the accumulation function `a`.
`annuity.a` versus `a`.
Etymology: a for annuity.
-/
noncomputable def a : ℕ → ℝ → ℝ := fun n i =>
  ∑ k ∈ Icc 1 n, (1 + i)⁻¹ ^ k


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

/-- The present value of a level-payments annuity is nonnegative. -/
lemma annuity_nonnegative (n : ℕ) {i : ℝ} (hi : i > -1) :
  a n i ≥ 0 := by
  unfold a
  have : 0 < 1 + i := by linarith
  have : 0 < (1 + i)⁻¹ := Right.inv_pos.mpr this
  have : ∀ k ∈ Finset.Icc 1 n, 0 < (1+i)⁻¹ ^ k := by
    intro k hk
    exact pow_pos this k
  suffices  ∑ k ∈ Icc 1 n, (1 + i)⁻¹ ^ k ≥
     ∑ k ∈ Icc 1 n, 0 by simp at this ⊢;exact this
  refine sum_le_sum ?_
  intro k hk
  apply le_of_lt
  apply this _ hk


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
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one $ abs_of_nonneg h₀ ▸
    inv_lt_one_iff₀.mpr $ .inr $ lt_add_of_pos_right 1 hi



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
  (Real.log ((PV * (IY / 100) + PMT) / (PMT - FV * (IY / 100)))) /
      (Real.log (1 + IY / 100)⁻¹)

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
  have h₃ : Real.log ((1 + IY / 100)⁻¹ ^ N) =
        N * Real.log (1 + IY / 100)⁻¹ :=
    Real.log_pow (1 + IY / 100)⁻¹ N
  generalize (1 + IY / 100)⁻¹ ^ N = V at *
  have g₀ : - (PMT * ((1 - V) / (IY / 100)) + FV * V) = PV := by linarith
  have g₁ :  PMT * (1 - V) + FV * V * (IY / 100) = - PV * (IY / 100) := by
    rw [← g₀]
    field_simp
    linarith
  have g₂ : V * (FV * (IY / 100) - PMT) = - PV * (IY / 100) - PMT := by
    linarith
  have g₃ : V  = (- PV * (IY / 100) - PMT)
               / ((FV * (IY / 100) - PMT)) := by
    generalize FV * (IY / 100) - PMT = y at *
    field_simp
    linarith -- uses h_nonpar
  rw [g₃] at h₃
  have g₀ : Real.log (1 + IY / 100)⁻¹ ≠ 0 := by
    simp
    constructor
    · contrapose! h₁
      linarith
    constructor
    · exact h₀
    · contrapose! h₄
      linarith
  have : N = (Real.log ((-PV * (IY / 100) - PMT)
    / (FV * (IY / 100) - PMT))) / (Real.log (1 + IY / 100)⁻¹) := by
      generalize (Real.log (1 + IY / 100)⁻¹) = z at *
      generalize
        Real.log ((-PV * (IY / 100) - PMT) / (FV * (IY / 100) - PMT))
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


lemma annuity_equation_continuity {PMT PV FV i : ℝ} {N : ℕ} : ContinuousOn
    (fun i ↦ PV + PMT * annuity.a N i + FV * (1 + i)⁻¹ ^ N)
    (Set.Icc 0 i) := by
  refine ContinuousOn.add ?_ ?_
  refine Continuous.comp_continuousOn' ?_ ?_
  exact continuous_add_left PV
  refine Continuous.comp_continuousOn' ?_ ?_
  exact continuous_mul_left PMT
  unfold annuity.a
  refine Continuous.comp_continuousOn' ?_ ?_
  exact continuous_finset_sum _ fun i a ↦ continuous_apply i
  refine continuousOn_pi.mpr ?_
  intro k
  refine ContinuousOn.pow ?_ k
  refine ContinuousOn.inv₀ ?_ ?_
  apply Continuous.continuousOn
  exact continuous_add_left 1
  intro x hx
  simp at hx
  apply ne_of_gt
  linarith

  refine Continuous.comp_continuousOn' ?_ ?_
  exact continuous_mul_left FV
  refine ContinuousOn.pow ?_ N

  refine ContinuousOn.inv₀ ?_ ?_
  apply Continuous.continuousOn
  exact continuous_add_left 1
  intro x hx
  simp at hx
  apply ne_of_gt
  linarith

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
  suffices annuity.a N (IY / 100) ≤ ↑N by
    exact (mul_le_mul_iff_of_pos_left hPMT).mpr this
  unfold annuity.a
  apply le_trans
  show _ ≤  ∑ k ∈ Icc 1 N, 1
  refine sum_le_sum ?_
  intro i hi
  have : 1 + IY / 100 ≥ 1 := by linarith
  simp
  suffices 1 ≤ ((1 + IY / 100) ^ i) by
    exact inv_le_one_of_one_le₀ this
  by_cases H : i = 0
  · subst H
    simp
  refine one_le_pow₀ ?_
  linarith
  simp
  suffices (1 + IY / 100)⁻¹ ^ N ≤ 1 by
    exact (mul_le_iff_le_one_right hFV).mpr this
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
  intro ι
  rw [one_div_div, ← one_div]
  have : 1 / (1 + 2 * max FV PMT / -PV) =
    ((-PV) * 1) / (-PV * (1 + 2 * max FV PMT / -PV)) := by
      refine (IsUnit.mul_div_mul_left ?_ 1 (1 + 2 * max FV PMT / -PV)).symm
      simp
      linarith
  rw [this]
  rw [LeftDistribClass.left_distrib]
  have : -PV * (2 * max FV PMT / -PV) = 2 * max FV PMT := by
          refine mul_div_cancel₀ (2 * max FV PMT) ?_
          simp
          linarith
  rw [this]
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
    have : PMT * FV⁻¹ ≤ 1 := by
      refine mul_inv_le_one_of_le₀ ?_ ?_
      exact sup_eq_left.mp h
      linarith
    have :  1 / 2 + FV * (FV * 2 - PV)⁻¹ < 1 := by
      suffices FV * (FV * 2 - PV)⁻¹ < 1/2 by linarith
      suffices FV / (FV * 2 + -PV) < 1/2 by simp at this ⊢;tauto
      suffices  2 * (FV / (FV * 2 + -PV)) < 2 * (1 / 2) by linarith
      simp
      have :  2 * (FV / (FV * 2 + -PV)) = (FV * 2) / (FV * 2 + -PV) := by
        ring_nf
      rw [this]
      suffices  FV * 2 < FV * 2 + -PV by
        apply (div_lt_one₀ _).mpr <;> linarith
      linarith
    calc _ ≤ (1 / 2) + FV * (FV * 2 - PV)⁻¹ := by linarith
         _ < _ := this
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
    suffices 2 * ( PMT * (PMT * 2 + -PV)⁻¹) < 2 * (1 / 2) by linarith
    simp
    have : 2 * (PMT * (PMT * 2 + -PV)⁻¹)
        =  PMT * 2 / (PMT * 2 + -PV) := by ring_nf
    rw [this]
    suffices PMT * 2 < (PMT * 2 + -PV) by
        apply (div_lt_one₀ _).mpr <;> tauto
    linarith

/-- We do not use Global Axiom of Choice here,
but just Intermediate Value Theorem.

Actually, ∀ ε > 0, ∃ i > 0, f i < PV + ε,
but we don't need to prove that here.
-/
theorem CPT_IY_unique {PMT PV FV : ℝ} {N : ℕ} (hN : N ≠ 0)
    (hPMT : PMT ≥ 0)
    (h :  0 ≤ PV + PMT * ↑N + FV) -- comes from specific choice of ι
    (hPV : PV < 0) (hFV : FV > 0):
    ∃! IY > -100, annuity_equation IY PMT PV FV N := by
  unfold annuity_equation
  let f : ℝ → ℝ :=
    fun i => PV + PMT * annuity.a N i + FV * (1 + i)⁻¹ ^ N
  have ⟨i,hi⟩ : ∃ i ≥ 0, f i = 0 := by
    by_cases H : PMT = 0
    · clear hPMT
      unfold f
      subst H
      simp
      use Real.exp ((1 / N) * Real.log (FV / -PV)) - 1
      -- unfold i
      -- simp

      simp at h
      have : -PV ≤ FV := by linarith
      have : FV / -PV ≥ 1 := by
        refine (one_le_div₀ ?_).mpr ?_
        linarith
        tauto
      constructor
      generalize FV / -PV = α at *
      simp
      apply mul_nonneg
      simp
      exact Real.log_nonneg this
      have : 1 + (Real.exp (1 / ↑N * Real.log (FV / -PV)) - 1)
        = Real.exp (1 / ↑N * Real.log (FV / -PV)) := by linarith
      rw [this]
      have (M : ℕ) (x : ℝ) (hx : x > 0) :
        x ^ M = Real.exp (M * Real.log x) := by
          induction M with
          | zero => simp
          | succ n ih =>
            simp
            have : x ^ (n+1) = x^ n * x := by rfl
            rw [this]
            have : (↑n + 1) * Real.log x
              = n * Real.log x + 1 * Real.log x := by ring_nf
            rw [this]
            rw [Real.exp_add]
            congr
            simp
            rw [Real.exp_log]
            exact hx
      rw [this]

      field_simp
      rw [Real.exp_log]
      have : -PV ≠ 0 := by linarith
      have :  PV * (FV / -PV) = - (PV * (FV / PV)) := by ring_nf
      rw [this]
      have : PV * (FV / PV) = FV * (PV / PV) := mul_div_left_comm PV FV PV
      rw [this]
      have : PV / PV = 1 := by
        refine IsUnit.div_self ?_
        refine Ne.isUnit ?_
        linarith
      rw [this]
      ring_nf
      field_simp
      aesop
      apply Real.exp_pos
    let ι := 2 * (max FV PMT) / (-PV)
    have hι : ι > 0 := by
      simp [ι]
      have : -PV > 0 := by linarith
      apply mul_pos
      apply mul_pos
      simp
      exact lt_sup_of_lt_left hFV
      simp
      linarith
    have h₀ : ι > 0 ∧ f ι < 0 := by
      constructor
      · tauto
      · unfold f
        have (i : ℝ) (hi : i > 0) : annuity.a N i < 1/i := by
          have := @annuity.a_eq_a_formula i (by linarith) (by linarith)
          have := congrFun this N
          rw [this]
          unfold annuity.a_formula
          suffices  (1 - (1 + i)⁻¹ ^ N) < 1 by
              exact (div_lt_div_iff_of_pos_right hi).mpr this
          suffices 0 < (1 + i)⁻¹ ^ N by linarith
          positivity
        have := this ι hι
        apply lt_trans
        · show PV + PMT * annuity.a N ι + FV * (1 + ι)⁻¹ ^ N <
                PV + PMT * (1 / ι) + FV * (1 + ι)⁻¹ ^ N
          have hPMT : PMT > 0 := by contrapose! H;linarith
          have : PMT * annuity.a N ι <
            PMT * (1 / ι) := (mul_lt_mul_left hPMT).mpr this
          linarith
        calc
        _ ≤ PV + PMT * (1 / ι) + FV * (1 + ι)⁻¹ := by
          suffices PMT * (1 / ι) + FV * (1 + ι)⁻¹ ^ N
                 ≤ PMT * (1 / ι) + FV * (1 + ι)⁻¹ by
            linarith
          suffices FV * (1 + ι)⁻¹ ^ N ≤ FV * (1 + ι)⁻¹ by linarith
          suffices (1 + ι)⁻¹ ^ N ≤ (1 + ι)⁻¹ by exact
            (mul_le_mul_iff_of_pos_left hFV).mpr this
          have : (1 + ι) > 1 := by linarith
          have : (1 + ι)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
          have : (1 + ι)⁻¹ > 0 := by simp;linarith
          generalize (1+ι)⁻¹ = α at *
          refine pow_le_of_le_one ?_ ?_ hN
          linarith
          linarith
        _ < _ := by
          apply CPT_IY_unique.aux
          contrapose! H; linarith
          tauto
          tauto
    have : 0 ∈ Set.Icc (f ι) (f 0) := by
        constructor
        · apply le_of_lt h₀.2
        simp [f, annuity.a]
        exact h
    have ⟨j,hj⟩:= @intermediate_value_Icc' ℝ _ _ _ _ ℝ _ _ _ 0 ι
      (by linarith) f annuity_equation_continuity 0 this
    use j
    simp at hj
    tauto
  have ha: StrictAntiOn f (Set.Ioi (-1)) := by
    intro a ha b hb hab
    simp [f] at ha hb ⊢
    have : ((1 + b) ^ N)⁻¹ < ((1 + a) ^ N)⁻¹ := by
        refine inv_strictAnti₀ ?_ ?_
        have : 0 < 1 + a := by linarith
        positivity
        refine pow_lt_pow_left₀ ?_ ?_ hN <;> linarith
    have : FV * ((1 + b) ^ N)⁻¹ < FV * ((1 + a) ^ N)⁻¹ :=
      (mul_lt_mul_left hFV).mpr <| by tauto
    by_cases H : PMT = 0
    subst H
    simp
    tauto
    have hPMT : PMT > 0 := by contrapose! H;linarith
    have : PMT * annuity.a N b  < PMT * annuity.a N a :=
      (mul_lt_mul_left hPMT).mpr <| annuity_antitone hN hab ha
    linarith

  have : ∃! i > -1, f i = 0 := by
    use i
    constructor
    simp
    constructor
    linarith
    tauto
    intro j hj
    by_contra H
    have : i < j ∨ j < i := lt_or_gt_of_ne fun a ↦ H a.symm
    rcases (lt_or_gt_of_ne fun a ↦ H a.symm) with (g | g)
    all_goals
      specialize ha (by simp;linarith) (by simp;linarith) g; linarith
  obtain ⟨i,hi⟩ := this
  use i * 100
  constructor
  · constructor
    simp
    simp_all
    linarith
    unfold f at hi
    simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, IsUnit.mul_div_cancel_right]
    tauto
  · ring_nf
    intro J hJ
    have := hi.2 (J/100)
    simp at hJ ⊢ this
    specialize this (by linarith) (by
        unfold f;rw [← hJ.2]
        congr
        simp
        congr)
    linarith


/-- The [CPT] [IY] button combination on the BA II Plus Financial. -/
noncomputable def CPT_IY₁ {PMT PV FV : ℝ} {N : ℕ} (hN : N ≠ 0)
    (hPMT : PMT ≥ 0) (h :  0 ≤ PV + PMT * ↑N + FV)
    (hPV : PV < 0) (hFV : FV > 0): ℝ :=
  (CPT_IY_unique hN hPMT h hPV hFV).choose

/-- [CPT] [IY] gives the only solution for interest rate per year. -/
lemma IY_eq_CPT_IY {PMT PV FV IY : ℝ} {N : ℕ} (hN : N ≠ 0)
    (hPMT : PMT ≥ 0) (h :  0 ≤ PV + PMT * ↑N + FV)
    (hPV : PV < 0) (hFV : FV > 0) (hann : annuity_equation IY PMT PV FV N)
    (h₀ : IY ≥ 0) : IY = CPT_IY₁ hN hPMT h hPV hFV :=
  (CPT_IY_unique hN hPMT h hPV hFV).choose_spec.2 _ ⟨by linarith, hann⟩

/-- [CPT] [IY] gives the only solution for interest rate per year. -/
lemma IY_eq_CPT_IYNegOne {PMT PV FV IY : ℝ} {N : ℕ} (hN : N ≠ 0)
    (hPMT : PMT ≥ 0) (h :  0 ≤ PV + PMT * ↑N + FV)
    (hPV : PV < 0) (hFV : FV > 0) (hann : annuity_equation IY PMT PV FV N)
    (h₀ : IY > -100) : IY = CPT_IY₁ hN hPMT h hPV hFV :=
  (CPT_IY_unique hN hPMT h hPV hFV).choose_spec.2 _ ⟨h₀, hann⟩

noncomputable def CPT_PMT (IY PV FV : ℝ) (N : ℕ) :=
  (- FV * (1 + IY / 100)⁻¹ ^ N  - PV) / (annuity.a N (IY / 100))

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
      (by contrapose! H; linarith)
      (by contrapose! h₀;linarith)
    rw [congrFun this]
    unfold annuity.a_formula
    simp
    constructor
    field_simp
    contrapose! H
    have : 100 ^ N / (100 + IY) ^ N
      = (100 / (100 + IY)) ^ N := by ring_nf
    rw [this] at H
    have : ((100) / ((100) + IY)) ^ N = 1 ^ N := by field_simp;linarith
    have : (100) / ((100) + IY) = 1 := by
      have : 100 + IY > 0 := by linarith
      generalize 100 + IY = i at *
      have : 100 / i > 0 := by field_simp;linarith
      generalize 100 / i = j at *
      simp at *
      have : N > 0 := by omega
      have : N * Real.log j = Real.log (j ^ N) := (Real.log_pow j N).symm
      have : j ^ N = Real.exp (N * Real.log j) := by
        rw [this]
        refine Eq.symm (Real.exp_log ?_)
        (expose_names; exact pow_pos this_5 N)
      have : Real.exp (N * Real.log j) = 1 := by linarith
      have : Real.exp (N * Real.log j) = Real.exp 0 := by
        rw [this];exact Eq.symm Real.exp_zero
      have : N * Real.log j = 0 := by apply Real.exp_injective this
      simp at this
      cases this with
      | inl h => omega
      | inr h =>
        cases h with
        | inl h => subst h;simp_all
        | inr h =>
          cases h with
          | inl h => tauto
          | inr h => linarith
    rw [this] at H
    simp at this
    have : 100 + IY ≠ 0 := by contrapose! h₀;linarith
    have : 100 / (100 + IY) = 100 / 100 := by simp;tauto
    have : 100 = 100 + IY := by
      generalize 100 + IY = z at *
      symm
      let hu := (100 : ℝ)
      have : hu / z = hu / 100 := this
      have : hu ≠ 0 := by simp [hu]
      have : z / hu = 100 / hu := by
        apply (div_eq_div_iff_comm hu z hu).mp
        tauto
      simp at this
      ring_nf at this
      rw [mul_comm] at this
      have : hu⁻¹ ≠ 0 := by simp;tauto
      linarith
    linarith
    · exact H
  unfold CPT_PMT
  generalize annuity.a N (IY / 100) = α at *
  generalize (1 + IY / 100)⁻¹ ^ N = β at *
  have : PMT * α = - (FV * β)  - PV := by
    linarith
  field_simp
  rw [this]


noncomputable def CPT_IY  {IY PMT PV FV : ℝ} {N : ℕ}
    (hann : annuity_equation IY PMT PV FV N)
    (hN : N ≠ 0) (hPMT : PMT ≥ 0)
    (hPV : PV < 0) (hFV : FV > 0)
    (h₀ : IY > 0) :=
  CPT_IY₁ hN hPMT (of_IY_nonneg hann (le_of_lt h₀)
    (hPMT) hFV) hPV hFV

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

The case `PMT = 0` is the Time Value of Money (TVM) Equation.
-/
theorem annuity_equation_unique_solvability {IY PMT PV FV : ℝ} {N : ℕ}
    (hann : annuity_equation IY PMT PV FV N)
    (hPMT : PMT ≥ 0) (hPV : PV < 0) (hFV : FV > 0) (hIY : IY > 0) :
    ((hN : N ≠ 0) →
    PMT = CPT_PMT IY PV FV N ∧ IY = CPT_IY hann hN hPMT hPV hFV hIY) ∧
    PV  = CPT_PV IY PMT FV N ∧
    FV  = CPT_FV IY PMT PV N ∧
    (FV * (IY / 100) - PMT ≠ 0 → N = CPT_N IY PMT PV FV) := by
  have hI₀ : IY > -100 := by linarith
  have hI₁ : IY ≠ -100 := by linarith
  have hI₂ : IY / 100 ≠ -2 := by linarith
  constructor
  · intro hN
    constructor
    exact PMT_eq_CPT_PMT hann hI₀ hN
    exact IY_eq_CPT_IYNegOne _ _ _ _ _ hann hI₀
  · constructor
    exact PV_eq_CPT_PV hann
    constructor
    · exact FV_eq_CPT_FV hann hI₁
    · exact N_eq_CPT_N hann (ne_of_gt hIY) hI₁ hI₂
