import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Interest.Aristotle_CPT_I
-- import Interest.Aristotle_CPT_N
import Interest.Aristotle_duration -- to eliminate d < 1 + 1/i assumption in Aristotle_CPT_N
import Interest.AristotleMagic
import Interest.NFM
import Mathlib.Topology.Algebra.Group.Defs
-- import Interest.AristotleDeriv
/-!

## Five implicit functions from the Annuity Equation: duration version

The BA II Plus calculator values PMT, I/Y, N, FV, PV
can each be computed from the other four. Here we replace PV by D (duration)
for a speculative future calculator.

Main results:

* `annuity_equation_unique_solvability`
* `TVM_equation_unique_solvability`: by setting PMT=0 in
  the annuity equation we obtain unique solution for the
  Time Value of Money equation as well.

lemma eq_CPT_I_from_D_maturity {n : ℕ} (hnn : n ≥ 2)
    {i d r : ℝ} (hd : d ∈ Set.Ioo (1:ℝ) n)
    (hr : r > 0) :
    ∃! i > -1, duration_equation n i r d
lemma eq_CPT_I_from_D_par {n : ℕ} (hn : n ≥ 2 ) -- if n=1, then D=n and we can't infer i.
    {i : ℝ} (hi : i > -1) {d : ℝ} (hd : 0 < d - 1)
    (h :  duration_equation n i i d) :
    let hn₀ : n - 1 ≠ 0 := by contrapose! hn;omega
    yield hn₀ ⟨d - 1, hd⟩ = i := by

lemma eq_CPT_N_from_D_I {n : ℕ} (hnn : n > 1)
    {i d r : ℝ} (hd : d ∈ Set.Ioi (1:ℝ)) (hi : i > 0)
    (hr : r > i)
    (hann : duration_equation n i r d) :
    let hdi : d < 1 + 1 / i :=
    eq_D_of_duration_equation hnn hi (lt_trans hi hr) hann ▸  @inequality_proof n hnn i r hi (le_of_lt hr)
    n = CPT_N_from_D hd hi hr hdi := by
lemma eq_CPT_N_from_D_par (n : ℕ) {i : ℝ} (hi : i > 0) (d : ℝ)
    (h :  duration_equation n i i d) :
    n = CPT_N_from_D_par i d := by


-/

open Finset Real Filter


/-

## DURATION

-/


open annuity

/-- Macaulay duration of a maturity `n`, level-payments bond (with redemption value 1)
with coupon rate `r` and yield rate `i`. -/
noncomputable def D : ℕ → ℝ → ℝ → ℝ := fun n i r =>
  (r * Ia n i + n * (1+i)⁻¹ ^ n) /
  bond_price n i r

/-- A bond with unit redemption value and maturity 1 has Macaulay duration 1. -/
lemma D_one {i r : ℝ} (hi : i > -1) (hr : r ≥ 0) : D 1 i r = 1 := by
  unfold D Ia bond_price bond_price_sum geom_sum annuity.id_mul_geom_sum
  simp
  have : (1 + i)⁻¹ > 0 := by
    simp
    linarith
  set v := (1+i)⁻¹
  intro hc
  have : (r+1) * v = 0 := by linarith
  revert this
  simp
  constructor
  linarith
  linarith


def duration_equation (n : ℕ) (i r d : ℝ) :=
   d * bond_price n i r - (r * Ia n i + ↑n * (1 + i)⁻¹ ^ n) = 0




/-- The Macaulay duration does indeed satisfy the duration equation. -/
lemma D_duration_equation (n : ℕ) {i r : ℝ} (hi : i > -1) (hr : r ≥ 0) :
  duration_equation n i r (D n i r) := by
  unfold duration_equation D
  have := bond_price_pos n hi hr
  generalize bond_price n i r = b at *
  field_simp
  unfold Ia
  simp

/-- The maturity date as a trivial upper bound on the Macaulay duration. -/
lemma D_upper_bound (n : ℕ) {i r : ℝ} (hi : i > -1) (hr : r ≥ 0) : D n i r ≤ n := by
  have h₄ := by apply bond_price_pos n hi hr
  unfold bond_price at h₄
  unfold bond_price_sum at *
  apply (div_le_iff₀ h₄).mpr
  suffices r * Ia n i ≤ r * (↑n * a n i) by
    unfold a at this
    linarith
  apply mul_le_mul_of_nonneg_left
  unfold Ia a geom_sum
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


lemma par_bond_price (n : ℕ) {i : ℝ} (hi : i > 0) :
    bond_price n i i = 1 := by
  unfold bond_price bond_price_sum
  have := congrFun $ @a_eq_a_formula i (by linarith) (by linarith)
  unfold annuity.a at this
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
    unfold Ia annuity.id_mul_geom_sum at h
    have := @id_mul_geom_sum₁ (1+i)⁻¹ (by
        intro hc;simp at hc;subst hc;simp at hi) n
    rw [this] at h
    have : (1+i)⁻¹ ≠ 1 := by intro hc;simp at hc;linarith
    have : ((1+i)⁻¹ - 1)^2 ≠ 0 := by
        contrapose! this;simp at this;linarith
    have h₀ : i * (1+i)⁻¹ = 1 - (1+i)⁻¹ := by
        field_simp
        linarith
    have : (1+i)⁻¹ - 1 ≠ 0 := by
        contrapose! this
        rw [this]
        simp
    have : 1 - (1+i)⁻¹ ≠ 0 := by
        contrapose! this
        linarith
    have : i * (1+i)⁻¹ ≠ 0 := by
        simp;constructor <;> linarith
    have hiv : i = ((1+i)⁻¹)⁻¹ - 1 := by field_simp;linarith
    have hivn : log ((1+i)⁻¹ ^ n) = n * log (1+i)⁻¹ := by
        simp
    have hlogv : log (1+i)⁻¹ ≠ 0 := by
        simp
        constructor
        linarith
        constructor <;> linarith
    have : (1+i)⁻¹ ≠ 0 := by simp;linarith
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
        rw [← h₀];field_simp
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


lemma sub_nat_real {n : ℕ} (hn : n ≥ 2) {i : ℝ} {d : ℝ}
  (hd₁ : d ≤ ↑n) (h : duration_equation n i i d) : d - 1 ≤ ↑(n - 1) := by
        simp
        convert hd₁
        obtain ⟨m,hm⟩ : ∃ m, n = m + 2 := Nat.exists_eq_add_of_le' hn
        subst hm
        simp
        linarith

/-- Present value of an increasing annuity with interest rate 0. -/
lemma increasing_annuity_zero {n : ℕ} :
    annuity.Ia n 0 = (n+1) * n / 2 := by
  unfold annuity.Ia annuity.id_mul_geom_sum
  simp
  have h := Finset.sum_range_id n
  have : ∑ i ∈ range n, (i:ℝ)
    = ((∑ i ∈ range n, i) : ℝ) := by
    congr
  let α : ℕ := ∑ i ∈ range (n+1), i
  let β : ℕ := (n+1) * (n+1 - 1) / 2
  have : α = β := Finset.sum_range_id (n+1)
  have hα : (α : ℝ) = (β : ℝ) := by
    rw [this]
  have := @sum_Icc_succ_eq_sum_range (fun n => n) n
  simp at this
  rw [this]
  unfold α at hα
  simp at hα
  rw [hα]
  unfold β
  simp
  have : Even n ∨ Odd n := by exact Nat.even_or_odd n
  cases this with
  | inl h =>
    obtain ⟨k,hk⟩ := h
    subst hk
    simp
    have : k + k = 2 * k := by omega
    repeat rw [this]
    have : (k:ℝ) + k = 2 * k := by ring_nf
    repeat rw [this]
    have : (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) := by
        ring_nf
    rw [this]
    simp
    ring_nf
  | inr h =>
    obtain ⟨k,hk⟩ := h
    subst hk
    simp
    have : (2 * k + 1 + 1) * (2 * k + 1) = 2 * ((k + 1) * (2 * k + 1)) := by
        ring_nf
    rw [this]
    simp
    ring_nf

/-- A pleasant formula for the Macaulay duration of a zero-yield bond
    in terms of the coupon rate `r` and maturity `n`.
    Note that when `r=0` it reduces to `d=n`.
     -/
lemma duration_yield_zero {n : ℕ}
    (hn : n ≠ 0 )
    {d : ℝ} {r : ℝ} (hr : 0 ≤ r)
    (h :  duration_equation n 0 r d) :
    d = (r*(n+1)*n/2 + n) / (r*n + 1) := by
    unfold duration_equation
      annuity.bond_price
      annuity.bond_price_sum
      annuity.geom_sum
      at h
    simp at h
    rw [increasing_annuity_zero] at h
    have : r * n + 1 ≠ 0 := by
        apply ne_of_gt
        positivity
    field_simp
    linarith

/-- A bond with coupon zero has duration equal to maturity. -/
lemma duration_coupon_zero {n : ℕ}
    {d : ℝ} {i : ℝ} (hr : -1 < i)
    (h : duration_equation n i 0 d) :
    d = n := by
    have : (1+i)⁻¹ ^ n > 0 := by
        apply pow_pos
        simp
        linarith
    unfold duration_equation
      annuity.bond_price
      annuity.bond_price_sum
      at h
    generalize (1+i)⁻¹ ^ n = α at *
    simp at h
    have : d * α = n * α := by linarith
    rw [mul_eq_mul_right_iff] at this
    cases this with
    | inl h => tauto
    | inr h => subst h;simp at this

/-- If the value of an annuity is `n-1` then the yield interest rate `i` must have been 0. -/
theorem yield_zero {n : ℕ} (hn : n ≥ 2) (hd : 0 < (n:ℝ) - 1) :
  let hn₀ : n - 1 ≠ 0 := by contrapose! hn;omega
  yield hn₀ ⟨↑n - 1, hd⟩ = 0 := by
    let hn₀ : n - 1 ≠ 0 := by contrapose! hn;omega
    have hspec:= (@yield_exists (n-1) hn₀ (n-1) (by linarith)).choose_spec.2 0
    simp at hspec
    have := hspec (by
        obtain ⟨m,hm⟩ : ∃ m, n = m+1 := Nat.exists_eq_succ_of_ne_zero (by linarith)
        subst hm
        simp)
    simp_rw [this]
    simp [yield]


/-- For a bond with maturity `n=2`, find the yield rate `i` from the Macaulay duration `d`
and the coupon rate `r`. For larger `n` it is not generally uniquely solvable.
`n=3` might be an interesting quadratic equation.
Note that if i=r, (d-1)r = 2-d, i.e., i = (2-d)/(d-1).
-/
lemma eq_CPT_I_from_D_maturity2
    {i d r : ℝ} (hi : i > -1) (hd : d ∈ Set.Ioo 1 2) (hri : r > 0)
    (h : duration_equation 2 i r d) :
    i = (2 - d) * (r + 1) / ((d - 1) * r) - 1 := by
  set v := (1+i)⁻¹
  unfold duration_equation annuity.bond_price
    annuity.bond_price_sum annuity.Ia annuity.geom_sum annuity.id_mul_geom_sum at h
  repeat rw [Finset.sum_Icc_succ_top] at h
  simp only [zero_lt_one, Icc_eq_empty_of_lt, sum_empty, zero_add, pow_one, Nat.reduceAdd,
    Nat.cast_one, one_mul, Nat.cast_ofNat] at h
  ring_nf at h
  have hv : v ≠ 0 := by
      simp [v]
      linarith
  have : (d-2) * (r+1) * v + (d-1) * r = 0 :=
      (mul_eq_zero_iff_left hv).mp $ by linarith
  simp at hd
  have hβ : (d-2) * (r+1) ≠ 0 := by simp; constructor <;> linarith
  have hγ : (1-d)*r       ≠ 0 := by simp; constructor <;> linarith
  have : v = (- (d-1) * r) / ((d-2) * (r+1)) :=
    CancelDenoms.cancel_factors_eq_div (by linarith) hβ
  field_simp [v] at this
  unfold v at this
  field_simp at this
  have h₃ : (1+i) ≠ 0 := by linarith
  have h₀ : (1+i)⁻¹ ≠ 0 := by simp;tauto
  have h₁ : d-1≠0 := by linarith
  have h₂ : d-2≠0 := by linarith
  field_simp at this ⊢
  linarith
  all_goals simp


lemma deriv_bond_price_sum {n : ℕ} (r x : ℝ) :
    deriv (annuity.bond_price_sum n r) x =
    r * ∑ k ∈ Icc 1 n, k * x ^ (k - 1) + n * x ^ (n - 1) := by
  unfold annuity.bond_price_sum annuity.geom_sum
  rw [deriv_fun_add]
  simp
  apply Differentiable.differentiableAt
  apply Differentiable.mul
  simp
  have : (fun v : ℝ ↦ ∑ k ∈ Icc 1 n, v ^ k)
    = ∑ k ∈ Icc 1 n, fun v ↦ v ^ k := by ext;simp
  rw [this]
  have := @Differentiable.sum ℝ _ ℝ _ _ ℝ _ _ ℕ (Icc 1 n)
    (fun k => fun v => v ^ k)
  apply this
  intro k hk
  simp
  apply Differentiable.differentiableAt
  simp


open Filter Finset

/-- With great help from Aristotle. -/
lemma eq_CPT_I_from_D_maturity {n : ℕ} (hnn : n ≥ 2)
    {i d r : ℝ} (hd : d ∈ Set.Ioo (1:ℝ) n)
    (hr : r > 0) :
    ∃! i > -1, duration_equation n i r d := by
  unfold duration_equation
    annuity.bond_price
  set v := (1+i)⁻¹
  let F := fun v => d * annuity.bond_price_sum n r v -
      (r * annuity.id_mul_geom_sum n v + ↑n * v ^ n)
  have ⟨v,hv⟩ := @unique_root_f n hnn d r hd hr
  use 1/v-1
  simp [f] at hv ⊢
  constructor
  · constructor
    · tauto
    · unfold annuity.bond_price_sum annuity.geom_sum annuity.Ia annuity.id_mul_geom_sum
      convert hv.1.2
      field_simp
      have : v ≠ 0 := by linarith
      ring_nf
      field_simp
  intro i hi h
  unfold annuity.bond_price_sum annuity.geom_sum annuity.Ia annuity.id_mul_geom_sum at h
  have := hv.2 (1 / (1 + i)) (by apply div_pos;simp;linarith) (by
    simp at h ⊢
    exact h)
  rw [← this]
  field_simp at this ⊢
  linarith




lemma annuity_bond_price_ne_zero {n : ℕ} (hnn : n > 1) {i r : ℝ} (hi : i > 0) (hr : r > 0) :
    annuity.bond_price n i r ≠ 0 := by
    apply ne_of_gt
    apply add_pos
    apply mul_pos
    linarith
    apply sum_pos
    intro j hj
    positivity
    simp
    linarith
    positivity


lemma eq_D_of_duration_equation {n : ℕ} (hnn : n > 1)
    {i d r : ℝ} (hi : i > 0) (hr : r > 0)
    (hann : duration_equation n i r d): d = D n i r := by
have := @D_duration_equation n i r (by linarith) (by linarith)
unfold duration_equation at hann this
have : d * annuity.bond_price n i r
    = D n i r * annuity.bond_price n i r := by linarith
apply mul_right_cancel₀ (by
    apply annuity_bond_price_ne_zero hnn hi (by linarith: r > 0)
    ) this



lemma duration_bounded_by_maturity {n : ℕ} (hnn : n > 1) {i d r : ℝ} (hi : i > 0) (hr : r > 0)
   (hann : duration_equation n i r d) :
  d ≤ ↑n := by
          have h₀ := @D_duration_equation n i r (by linarith) (by linarith)
          have h₁ := @D_upper_bound n i r (by linarith) (by linarith)
          unfold duration_equation at h₀ hann
          rw [← hann] at h₀
          have h₂ : annuity.bond_price n i r ≠ 0 := by
            apply annuity_bond_price_ne_zero ?_ hi ?_ <;> linarith
          have :  D n i r * annuity.bond_price n i r =
                                d * annuity.bond_price n i r := by linarith
          have : D n i r = d := by
            rw [← eq_D_of_duration_equation hnn hi hr hann]
          linarith

lemma eq_CPT_N_from_D_I.helper {n : ℕ} (hnn : n > 1)
    {i d r : ℝ} (hi : i > 0)
    (hr : r > i)
    (hann : duration_equation n i r d) :
     d < 1 + 1 / i := by
  have := @D_duration_equation n i r (by linarith) (by linarith)
  unfold duration_equation at hann this
  have : d = D n i r := by
    apply eq_D_of_duration_equation hnn hi (by linarith) hann
  rw [this]

  unfold D annuity.Ia annuity.id_mul_geom_sum annuity.bond_price annuity.bond_price_sum annuity.geom_sum
  exact inequality_proof n hnn i r hi $ le_of_lt hr


-- noncomputable def CPT_N_from_self {n : ℕ} (hnn : n > 1)
--     {i d r : ℝ} (hd : d ∈ Set.Ioi (1:ℝ)) (hi : i > 0)
--     (hr : r > i) (hr' : r < 1)
--     (hann : annuity.duration_equation n i r d) :=
--     CPT_N_from_D hd hi hr
--         (eq_D_of_duration_equation hnn hi (by linarith) hann ▸  @inequality_proof n hnn i r hi hr)


/-- Perhaps surprisingly:
Let i be the implied interest rate for an n-period
par bond of duration d.
Then the PV of an (n-1)-period unit-payment annuity with rate i is d-1.
This lets us compute `i` from `n` and `d`.
 -/
lemma eq_CPT_I_from_D_par {n : ℕ} (hn : n ≥ 2 ) -- if n=1, then D=n and we can't infer i.
    {i : ℝ} (hi : i > -1) {d : ℝ} (hd : 0 < d - 1)
    (h :  duration_equation n i i d) :
    let hn₀ : n - 1 ≠ 0 := by contrapose! hn;omega
    yield hn₀ ⟨d - 1, hd⟩ = i := by
    by_cases H : i = 0
    · subst H
      simp_rw [duration_coupon_zero hi h]
      apply yield_zero hn
    unfold duration_equation
      annuity.bond_price
      annuity.bond_price_sum
      at h
    have : annuity.geom_sum n (1 + i)⁻¹ = annuity.a n i := rfl
    rw [this] at h
    rw [congrFun $ annuity.a_eq_a_formula (H) (by linarith)] at h
    unfold annuity.a_formula annuity.Ia annuity.id_mul_geom_sum at h
    have := @id_mul_geom_sum₁ (1+i)⁻¹ (by
        intro hc;simp at hc;exact H hc) n
    rw [this] at h
    have : i ≠ 0 := H
    have : 1 + i ≠ 0 := by linarith
    set v := (1+i)⁻¹
    have hv₂ : (v - 1) ^ 2 ≠ 0 := by
        simp [v]
        intro hc
        have : (1 + i)⁻¹ = 1 := by linarith
        have : (1 + i) = 1 := by field_simp at this;tauto
        apply H
        linarith
    rw [mul_comm i, div_mul] at h
    field_simp at h ⊢
    simp at h

    have h₀ : - (i * v) * (↑n * v ^ (n + 1) - (↑n + 1) * v ^ n + 1)
              + (d - ↑n * v ^ n) * (v - 1) ^ 2 = 0 := by
        generalize (v-1)^2 = α at *
        field_simp at h
        linarith
    have h₁ : i * v = 1 - v := by unfold v; field_simp; ring_nf
    rw [h₁] at h₀
    have h₂ : -1 * ((v - 1) * (- (d * v) + d + v^n - 1)) = 0 := by
        ring_nf at h₀ this
        linarith
    have h₃ : v - 1 ≠ 0 := by contrapose! hv₂;rw [hv₂];simp
    have : (v - 1) * (- (d * v) + d + v^n - 1) = 0 := by linarith
    have : - (d * v) + d + v^n - 1 = 0 := (mul_eq_zero_iff_left h₃).mp this
    have : v^n - d * v + d - 1 = 0 := by linarith
    have : (v^n - d * v + d - 1) / (v - 1) = 0 := by rw [this]; simp
    obtain ⟨t,ht⟩ : ∃ m, n = m + 2 := Nat.exists_eq_add_of_le' hn
    obtain ⟨m,hm⟩ : ∃ m, n = m + 1 := by use t+1
    subst hm
    have hw : (v ^ (m + 1) - d * v + d - 1) = (v - 1) * (annuity.a m i - d + 1) := by
        have : v ^ (m + 1) = v ^ m * v := rfl
        rw [this, sub_mul, congrFun $ @annuity.a_eq_a_formula i H (by linarith)]
        unfold annuity.a_formula v
        field_simp
        ring_nf
    have h₃ : annuity.a m i - d + 1 = 0 := by
        rw [hw, mul_comm] at this
        rw [← this]
        field_simp
    have h₄ : d - 1 = annuity.a m i := by linarith
    have := (@yield_exists (m) (by linarith) (d - 1) hd).choose_spec
    simp at this
    simp_rw [this.2 i hi h₄]
    simp [yield]


/-- This version does not assume r<i or r>i. -/
noncomputable def CPT_N_from_D {i d r : ℝ} (hd : 0 < d) (hi : i > 0)
  (hr : r > 0)
  (hdi : d < 1 + 1 / i) : ℝ := by
    exact (@AriMagic.unique_solution_n i d r hd hi hr hdi).choose

lemma eq_CPT_N_from_D_I {n : ℕ} (hnn : n > 1)
    {i d r : ℝ} (hd : 0 < d) (hi : i > 0)
    (hr : 0 < r) (hdi : d < 1 + 1 / i)
    (hann : duration_equation n i r d) :
    n = @CPT_N_from_D i d r hd hi (by linarith) hdi := by
    unfold CPT_N_from_D
    simp
    have := (@AriMagic.unique_solution_n i d r hd hi hr hdi).choose_spec
    simp at this
    have := this.2 n (by simp;linarith)
      (by
      unfold duration_equation at hann
      unfold bond_price
        bond_price_sum geom_sum Ia annuity.id_mul_geom_sum at hann
      rw [← hann]
      have : (1+i)⁻¹ ≠ 0 := by simp;linarith
      have : (1+i)⁻¹ ≠ 1 := by simp;linarith
      set v := (1+i)⁻¹
      rw [id_mul_geom_sum₁ _ this]
      have : ∑ k ∈ Icc 1 n, v ^ k
       = (1-v^(n)) / i := by
        have := congrFun $ @annuity.a_eq_a_formula i (by linarith) (by linarith)
        unfold a geom_sum a_formula at this
        rw [this]
      rw [this]
      have h₀ : v ^ (n:ℝ) = v ^ n := by norm_num
      rw [h₀]
      have : v ^ ((n:ℝ) + 1) = v ^ (n+1) := by
        have : v ^ (n + 1) = v^n * v := rfl
        rw [this]
        rw [← h₀]
        refine rpow_add_one ?_ ↑n
        tauto
      rw [this])
    exact this
