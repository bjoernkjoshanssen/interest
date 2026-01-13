import Mathlib.Analysis.SpecialFunctions.Pow.Real -- Real.log
import Interest.NFM

/-!

## Annuity present value as an equivalence

-/

open Finset Real Filter


theorem yield_exists.x
    {ε : ℝ} (hε : 0 < ε)
    {m : ℕ} (hm : ε ≤ ↑m) ⦃x : ℝ⦄ (hx₀ : (↑m)⁻¹ ≤ 1 + x) :
    -1 < x := by
  calc -1 < -1 + (m:ℝ)⁻¹ := by
        refine lt_neg_add_iff_add_lt.mpr ?_
        simp only [add_neg_cancel, inv_pos]
        linarith
  _  ≤ x := by linarith

theorem yield_exists.y {n : ℕ} (hn : n ≠ 0) {ε : ℝ}
    {i : ℝ} (hi : annuity.a n i = ε)
    (hin : -1 < i) (y : ℝ) :
    -1 < y → ε = annuity.a n y → y = i := by
          intro hyn hyε
          by_contra H
          have : y < i ∨ i < y := lt_or_gt_of_ne H
          cases this with
          | inl h =>
            have := annuity.annuity_antitone hn h hyn
            linarith
          | inr h =>
            have := annuity.annuity_antitone hn h hin
            linarith

lemma yield_exists.sum {n : ℕ} (hn : n ≠ 0) (hnr : (n:ℝ) ≥ 1) :
    ∑ k ∈ Icc 1 n, ((2:ℝ) * ↑n)⁻¹ ^ k ≤ ∑ _ ∈ Icc 1 n, ((2:ℝ) * ↑n)⁻¹ := by
  apply sum_le_sum
  intro k hk
  simp at hk
  have :  ((2:ℝ) * ↑n)⁻¹ ≥ 0 := by
    positivity
  refine pow_le_of_le_one ?_ ?_ ?_
  linarith
  apply inv_le_one_of_one_le₀
  calc _ ≤ (n:ℝ) := hnr
       _ ≤ _     := by linarith
  linarith

lemma yield_exists.bound {n : ℕ} (hn : n ≠ 0) {ε : ℝ} (hε : 0 < ε) (hnr : (n:ℝ) ≥ 1)
    (hnr₀ : ↑n > 0) (H : ε < 1) :
    (2 * ↑n / ε)⁻¹ ≤ 1 := by
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
            · simp
            · simp
              linarith
            · simp
              linarith
        calc 1 ≤ n := by contrapose! hn;linarith
                _ ≤ 2 * n := by omega

lemma le_geom_self {n : ℕ} (hnr : ↑(n:ℝ) ≥ 1)
  (m : ℕ) (hm : m ≥ 1) : (m:ℝ) ≤ ∑ k ∈ Icc 1 n, (m:ℝ) ^ k := by
    calc (m:ℝ) ≤ ∑ k ∈ Icc 1 n, ↑m ^ 1 := by
                simp
                by_cases H : m = 0
                · subst H
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

lemma yield_exists.small_epsilon {n : ℕ} (hn : n ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hnr : (n:ℝ) ≥ 1) (hnr₀ : (n:ℝ) > 0)
    (hnn₀ : n > 0) (H : ε < 1) :
  ∃! i, i > -1 ∧ ε = annuity.a n i := by
          have : annuity.a n (2 * n / ε - 1) < ε := by
            unfold annuity.a
            rw [add_sub_cancel]
            calc _ ≤  ∑ k ∈ Icc 1 n, (2*n / ε)⁻¹ := by
                    apply sum_le_sum
                    intro k hk
                    have h₁ : k ≥ 1 := by simp at hk;tauto
                    have h₀ : 0 ≤ (2*n / ε)⁻¹ := by
                        simp
                        apply div_nonneg
                        linarith
                        simp
                    apply pow_le_of_le_one h₀ $ yield_exists.bound hn hε hnr hnn₀ H
                    omega
                 _ < _ := by
                    simp
                    ring_nf
                    field_simp
                    simp
          have : n / 1 ≤ n / ε := (div_le_div_iff₀ (by simp) hε).mpr
                $ (mul_le_mul_iff_of_pos_left hnr₀).mpr (by linarith)
          simp at this
          have ⟨i,hi⟩ := @intermediate_value_Icc' ℝ _ _ _ _ ℝ _ _ _ 0 (2 * n / ε - 1)
            (by
                calc (0:ℝ) ≤ 2 * n - 1 := by linarith
                     _ ≤ _ := by
                            field_simp;ring_nf
                            suffices  (↑n * ε) * 2 ≤ ↑n * 2 by linarith
                            suffices  (↑n * ε) ≤ ↑n by linarith
                            exact (le_div_iff₀ hε).mp this
                        )
                     (annuity.a n) (by
                        apply ContinuousOn.mono
                        apply annuity_continuous (i := (2 * ↑n / ε - 1))
                        intro x hx
                        simp at hx ⊢
                        constructor
                        linarith
                        tauto
                        ) ε (by
                     simp
                     constructor <;> linarith)
          simp at hi
          have hin : -1 < i := by linarith
          use i
          simp
          constructor
          · constructor
            · linarith
            · exact hi.2.symm
          · apply yield_exists.y <;> tauto

noncomputable def yield_exists {n : ℕ} (hn : n ≠ 0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃! i > -1, ε = annuity.a n i := by
        have hnr : (n:ℝ) ≥ 1 := by simp;omega
        have hnr₀ : (n:ℝ) > 0 := by simp;omega
        have hnn : n ≥ 1 := by omega
        have hnn₀ : n > 0 := by omega
        have hmm (m : ℕ) (hm : m ≥ 1) : annuity.a n (-1 + 1/m) ≥ m := by
            unfold annuity.a
            rw [add_neg_cancel_left, one_div, inv_inv]
            simp
            apply le_geom_self hnr m hm
        have : annuity.a n 0 = n := by unfold annuity.a annuity.geom_sum;simp
        by_cases H : ε < 1
        · exact yield_exists.small_epsilon hn hε hnr hnr₀ hnn₀ H
        have : annuity.a n (2 * n - 1) < ε := by
            unfold annuity.a
            rw [add_sub_cancel]
            simp at H
            calc _ ≤ _ := yield_exists.sum hn hnr
                 _ < (1:ℝ) := by
                    rw [Finset.sum_const]
                    field_simp
                    simp
                    field_simp
                    simp
                 _ ≤ _ := H
        have ⟨m,hm⟩ := exists_nat_ge ε
        have hbound:  (-1:ℝ) + 1 / ↑m ≤ 2 * ↑n - 1 := by
            suffices (1:ℝ) / ↑m ≤ 2 * ↑n by linarith
            apply le_trans
            show (1:ℝ) / m ≤ 1
            simp at H
            apply le_trans $ one_div_le_one_div_of_le hε hm
            · exact (div_le_one₀ hε).mpr H
            linarith
        have hcont : ContinuousOn (annuity.a n)
            (Set.Icc (-1 + 1 / ↑m) (2 * ↑n - 1)) := by
            apply ContinuousOn.mono
            · apply annuity_continuous
              exact 2*n-1
            intro x hx
            simp at hx ⊢
            constructor
            · exact yield_exists.x hε hm hx.1
            · exact hx.2
        have hrange : ε ∈ Set.Icc (annuity.a n (2 * ↑n - 1))
                                  (annuity.a n (-1 + 1 / ↑m)) := by
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
            exact hmm
        have ⟨i,hi⟩ := @intermediate_value_Icc' ℝ _ _ _ _ ℝ _ _ _
            (-1 + 1/m) (2 * n - 1) hbound (annuity.a n) hcont ε hrange
        simp at hi this
        have hin : -1 < i := by
            calc -1 < -1 + (m:ℝ)⁻¹ := by
                  refine lt_neg_add_iff_add_lt.mpr ?_
                  simp only [add_neg_cancel, inv_pos]
                  linarith
            _  ≤ i := by linarith
        use i
        simp
        constructor
        · exact ⟨yield_exists.x hε hm hi.1.1, hi.2.symm⟩
        have := @yield_exists.y
        intro y hyn hyε
        by_contra H
        have : y < i ∨ i < y := lt_or_gt_of_ne H
        cases this with
        | inl h =>
            have := annuity.annuity_antitone hn h hyn
            linarith
        | inr h =>
            have := annuity.annuity_antitone hn h hin
            linarith

/-- Inverse of the annuity function. -/
noncomputable def yield {n : ℕ} (hn : n ≠ 0) :
    Set.Ioi (0:ℝ) →  ℝ :=
    fun ε => (yield_exists hn ε.2).choose





/-- Now we can rename yield to annuity_equivalence.invFun -/
noncomputable def annuity_equivalence (n : ℕ) (hn : n ≥ 2) : Equiv (Set.Ioi (-1:ℝ)) (Set.Ioi (0:ℝ)) := {
    toFun := fun i =>
        ⟨annuity.a n i, annuity.annuity_positive (by linarith) i.2⟩
    invFun := fun x =>
        ⟨
          yield (Nat.ne_zero_of_lt hn) x,
          (yield_exists (Nat.ne_zero_of_lt hn) x.2).choose_spec.1.1
        ⟩
    left_inv := by
        intro i
        simp
        have := (@yield_exists n (by linarith)
            (annuity.a n i) (annuity.annuity_positive (by linarith) i.2)).choose_spec
        simp at this ⊢
        symm
        refine SetCoe.ext ?_
        unfold yield
        simp at this ⊢
        apply this.2
        exact i.2
        rfl
    right_inv := by
        intro x
        have := (@yield_exists n (by linarith) x x.2).choose_spec
        simp at this ⊢
        symm
        refine SetCoe.ext ?_
        convert this.1.2
        unfold yield
        simp
}

-- lemma yield_is_inverse  (n : ℕ) (hn : n ≠ 0) (ε :Set.Icc (0:ℝ) n) :
--     Function.LeftInverse (yield n hn) (fun i => ⟨ite (0 ≤ i) (annuity.a n i) 0, by
--         simp
--         constructor
--         by_cases H : 0 ≤ i
--         rw [if_pos H]
--         apply annuity.annuity_positive hn (by linarith)
--         rw [if_neg H]

--         sorry⟩) := by
--     sorry
