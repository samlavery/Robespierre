import Mathlib
import RequestProject.WeilArchKernelResidues
import RequestProject.UniformDigammaBoundCompact
import RequestProject.ArchOperatorBound

/-!
# Uniform log bound on `archKernel` on compact substrips of (0, 1)

For `σ ∈ [a, b] ⊂ (0, 1)` and `|T| ≥ 1`,
`‖archKernel(σ + iT)‖ ≤ C · log(1 + |T|)` with `C` independent of σ.

## Strategy

Use `gammaℝ_logDeriv_digamma_form` to reduce each term of `archKernel` to ψ.
Apply `digamma_log_bound_uniform_compact` on the half-argument intervals:
- Direct: σ/2 ∈ [a/2, b/2]; apply at t = T/2 when |T| ≥ 2 (so |T/2| ≥ 1).
- Reflected: (1-σ)/2 ∈ [(1-b)/2, (1-a)/2]; similarly.
For 1 ≤ |T| < 2 (so |T/2| < 1), bound ψ via continuity on the compact
[a/2, b/2] × [-1, 1] (and [(1-b)/2, (1-a)/2] × [-1, 1] for the reflected side).

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

open Complex Real

noncomputable section

namespace ZD.WeilArchKernelResidues

private lemma logpi_norm_half :
    ‖-(Complex.log (Real.pi : ℂ)) / 2‖ = Real.log Real.pi / 2 := by
  have hlogπ_nn : (0 : ℝ) ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h1 : ‖-(Complex.log (Real.pi : ℂ)) / 2‖ =
      ‖Complex.log (Real.pi : ℂ)‖ / ‖(2 : ℂ)‖ := by
    rw [norm_div, norm_neg]
  rw [h1, show ‖(2 : ℂ)‖ = 2 from by norm_num]
  rw [show Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) from
    (Complex.ofReal_log Real.pi_pos.le).symm, Complex.norm_real, Real.norm_of_nonneg hlogπ_nn]

private lemma half_norm : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) from by push_cast; ring, Complex.norm_real]
  norm_num

-- ψ(σ'+it') is ContinuousOn on [α,β]×[-1,1] when α > 0.
private lemma psi_continuousOn (α β : ℝ) (hα : 0 < α) :
    ContinuousOn (fun p : ℝ × ℝ =>
      ‖deriv Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) /
        Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖)
      (Set.Icc α β ×ˢ Set.Icc (-1 : ℝ) 1) := by
  -- The embedding map f(p) = p.1 + p.2*I is continuous ℝ×ℝ → ℂ.
  have hf_cont : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  -- The range of f on [α,β]×[-1,1] lies in {s | Re(s) ≥ α > 0} ⊆ {s | ∀ m, s ≠ -m}.
  have hrange : ∀ p ∈ Set.Icc α β ×ˢ Set.Icc (-1 : ℝ) 1,
      (p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈ {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} := by
    intro ⟨σ', t'⟩ hp m heq
    have hσ' : α ≤ σ' := hp.1.1
    have h_re : ((σ' : ℂ) + (t' : ℂ) * Complex.I).re = -(m : ℝ) := by rw [heq]; simp
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_one, Complex.ofReal_im, Complex.I_im, mul_zero, add_zero] at h_re
    linarith [Nat.cast_nonneg m (α := ℝ)]
  -- U = {s | ∀ m, s ≠ -m} is open.
  have hU_open : IsOpen {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} :=
    ZD.WeilPositivity.Contour.nonpole_isOpen
  -- Γ is differentiable on U.
  have hdiffOn : DifferentiableOn ℂ Complex.Gamma {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} :=
    fun z hz => (Complex.differentiableAt_Gamma _ hz).differentiableWithinAt
  -- deriv Γ is continuous on U.
  have hderivCont : ContinuousOn (deriv Complex.Gamma) {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} :=
    (hdiffOn.deriv hU_open).continuousOn
  -- Γ is continuous on U.
  have hGamma_cont : ContinuousOn Complex.Gamma {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} :=
    hdiffOn.continuousOn
  -- Γ ≠ 0 on range of f.
  have hne_zero : ∀ p ∈ Set.Icc α β ×ˢ Set.Icc (-1 : ℝ) 1,
      Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ≠ 0 := by
    intro ⟨σ', t'⟩ hp
    apply Complex.Gamma_ne_zero
    intro m heq
    exact absurd heq (hrange ⟨σ', t'⟩ hp m)
  -- Build continuity of p ↦ ψ(p.1 + p.2*I) on the product set.
  have h_deriv_cont_on : ContinuousOn
      (fun p : ℝ × ℝ => deriv Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))
      (Set.Icc α β ×ˢ Set.Icc (-1 : ℝ) 1) :=
    ContinuousOn.comp hderivCont hf_cont.continuousOn hrange
  have h_gamma_cont_on : ContinuousOn
      (fun p : ℝ × ℝ => Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))
      (Set.Icc α β ×ˢ Set.Icc (-1 : ℝ) 1) :=
    ContinuousOn.comp hGamma_cont hf_cont.continuousOn hrange
  exact ((h_deriv_cont_on.div h_gamma_cont_on hne_zero).norm)

set_option maxHeartbeats 800000 in
/-- **Uniform log bound on `archKernel` on compact substrips of (0,1).**
For any `[a, b] ⊂ (0, 1)`, `‖archKernel(σ+iT)‖ ≤ C · log(1+|T|)` with C uniform in σ. -/
theorem archKernel_log_bound_uniform_strip {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb_lt : b < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ : ℝ, σ ∈ Set.Icc a b → ∀ T : ℝ, 1 ≤ |T| →
        ‖archKernel ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        C * Real.log (1 + |T|) := by
  -- Half-argument intervals
  have ha2 : (0 : ℝ) < a / 2 := by linarith
  have hab2 : a / 2 ≤ b / 2 := by linarith
  have h1mb_pos : (0 : ℝ) < (1 - b) / 2 := by linarith
  have h1mb_le : (1 - b) / 2 ≤ (1 - a) / 2 := by linarith
  -- Uniform digamma bounds (require |t| ≥ 1)
  obtain ⟨Cd1, hCd1_pos, hCd1_bd⟩ := digamma_log_bound_uniform_compact (a / 2) (b / 2) ha2 hab2
  obtain ⟨Cd2, hCd2_pos, hCd2_bd⟩ :=
    digamma_log_bound_uniform_compact ((1 - b) / 2) ((1 - a) / 2) h1mb_pos h1mb_le
  -- Compact bounds on ψ for |t| ≤ 1 via ContinuousOn.
  have hCompact_dir : IsCompact (Set.Icc (a / 2) (b / 2) ×ˢ Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hBdd_dir : BddAbove ((fun p : ℝ × ℝ =>
      ‖deriv Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) /
        Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖) ''
      (Set.Icc (a / 2) (b / 2) ×ˢ Set.Icc (-1 : ℝ) 1)) :=
    hCompact_dir.bddAbove_image (psi_continuousOn (a / 2) (b / 2) ha2)
  set Mdir : ℝ := sSup ((fun p : ℝ × ℝ =>
      ‖deriv Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) /
        Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖) ''
      (Set.Icc (a / 2) (b / 2) ×ˢ Set.Icc (-1 : ℝ) 1))
  have hMdir_nn : 0 ≤ Mdir :=
    le_csSup_of_le hBdd_dir
      ⟨(a / 2, 0), Set.mem_prod.mpr ⟨Set.left_mem_Icc.mpr hab2, by norm_num⟩, rfl⟩
      (norm_nonneg _)
  have hCompact_refl : IsCompact
      (Set.Icc ((1 - b) / 2) ((1 - a) / 2) ×ˢ Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hBdd_refl : BddAbove ((fun p : ℝ × ℝ =>
      ‖deriv Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) /
        Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖) ''
      (Set.Icc ((1 - b) / 2) ((1 - a) / 2) ×ˢ Set.Icc (-1 : ℝ) 1)) :=
    hCompact_refl.bddAbove_image (psi_continuousOn ((1 - b) / 2) ((1 - a) / 2) h1mb_pos)
  set Mrefl : ℝ := sSup ((fun p : ℝ × ℝ =>
      ‖deriv Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) /
        Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖) ''
      (Set.Icc ((1 - b) / 2) ((1 - a) / 2) ×ˢ Set.Icc (-1 : ℝ) 1))
  have hMrefl_nn : 0 ≤ Mrefl :=
    le_csSup_of_le hBdd_refl
      ⟨((1 - b) / 2, 0),
        Set.mem_prod.mpr ⟨Set.left_mem_Icc.mpr h1mb_le, by norm_num⟩, rfl⟩
      (norm_nonneg _)
  -- Numeric constants
  have hlogπ_nn : (0 : ℝ) ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Big constant: works in both cases
  set Cbig : ℝ :=
    Real.log Real.pi + (Cd1 + Cd2) / 2 + 1 +
    (Real.log Real.pi + (Mdir + Mrefl) / 2 + 1) / Real.log 2
  refine ⟨Cbig, ?_, fun σ hσ T hT => ?_⟩
  · simp only [Cbig]
    have : 0 < (Real.log Real.pi + (Mdir + Mrefl) / 2 + 1) / Real.log 2 :=
      div_pos (by linarith) hlog2_pos
    linarith [hCd1_pos, hCd2_pos]
  -- Setup for the bound
  have hσ_pos : 0 < σ := lt_of_lt_of_le ha hσ.1
  have hσ_lt1 : σ < 1 := lt_of_le_of_lt hσ.2 hb_lt
  set s : ℂ := (σ : ℂ) + (T : ℂ) * Complex.I
  have hGR_ne : s.Gammaℝ ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp [s]; exact hσ_pos)
  have hGR_refl_ne : (1 - s).Gammaℝ ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp [s]; linarith)
  have hs_ne2n : ∀ n : ℕ, s ≠ -(2 * (n : ℂ)) := fun n h =>
    hGR_ne (Complex.Gammaℝ_eq_zero_iff.mpr ⟨n, h⟩)
  have hrefl_ne2n : ∀ n : ℕ, (1 : ℂ) - s ≠ -(2 * (n : ℂ)) := fun n h =>
    hGR_refl_ne (Complex.Gammaℝ_eq_zero_iff.mpr ⟨n, h⟩)
  have h_form1 :=
    ZD.WeilPositivity.Contour.gammaℝ_logDeriv_digamma_form s hGR_ne hs_ne2n
  have h_form2 :=
    ZD.WeilPositivity.Contour.gammaℝ_logDeriv_digamma_form (1 - s) hGR_refl_ne hrefl_ne2n
  have hs2_eq : s / 2 = ((σ / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I := by
    simp [s]; push_cast; ring
  have hrefl2_eq : (1 - s) / 2 = (((1 - σ) / 2 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I := by
    simp [s]; push_cast; ring
  -- Triangle inequality on archKernel
  have h_tri : ‖archKernel s‖ ≤
      ‖deriv Complex.Gammaℝ s / s.Gammaℝ‖ +
      ‖deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ‖ :=
    show ‖_ + _‖ ≤ _ from norm_add_le _ _
  -- Bound each Gammaℝ/logDeriv term by logπ/2 + (1/2)*ψ
  have h_term1 : ‖deriv Complex.Gammaℝ s / s.Gammaℝ‖ ≤
      Real.log Real.pi / 2 + (1 / 2) * ‖deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)‖ :=
    calc ‖deriv Complex.Gammaℝ s / s.Gammaℝ‖
        = ‖-(Complex.log (Real.pi : ℂ)) / 2 +
            (1 / 2 : ℂ) * (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2))‖ := by
              rw [h_form1]
      _ ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
            ‖(1 / 2 : ℂ) * (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2))‖ :=
              norm_add_le _ _
      _ = Real.log Real.pi / 2 + (1 / 2) * ‖deriv Complex.Gamma (s / 2) /
              Complex.Gamma (s / 2)‖ := by rw [logpi_norm_half, norm_mul, half_norm]
  have h_term2 : ‖deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ‖ ≤
      Real.log Real.pi / 2 + (1 / 2) * ‖deriv Complex.Gamma ((1 - s) / 2) /
        Complex.Gamma ((1 - s) / 2)‖ :=
    calc ‖deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ‖
        = ‖-(Complex.log (Real.pi : ℂ)) / 2 +
            (1 / 2 : ℂ) * (deriv Complex.Gamma ((1 - s) / 2) /
              Complex.Gamma ((1 - s) / 2))‖ := by rw [h_form2]
      _ ≤ ‖-(Complex.log (Real.pi : ℂ)) / 2‖ +
            ‖(1 / 2 : ℂ) * (deriv Complex.Gamma ((1 - s) / 2) /
              Complex.Gamma ((1 - s) / 2))‖ := norm_add_le _ _
      _ = Real.log Real.pi / 2 + (1 / 2) * ‖deriv Complex.Gamma ((1 - s) / 2) /
              Complex.Gamma ((1 - s) / 2)‖ := by rw [logpi_norm_half, norm_mul, half_norm]
  -- Membership
  have hσ2_mem : σ / 2 ∈ Set.Icc (a / 2) (b / 2) :=
    ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hrefl2_mem : (1 - σ) / 2 ∈ Set.Icc ((1 - b) / 2) ((1 - a) / 2) :=
    ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  -- Case split
  by_cases hT2 : 2 ≤ |T|
  · -- |T| ≥ 2: use uniform digamma bound at T/2, |T/2| ≥ 1.
    have hT2_half : 1 ≤ |T / 2| := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
    have h_psi1 := hCd1_bd (σ / 2) hσ2_mem (T / 2) hT2_half
    have h_psi2 := hCd2_bd ((1 - σ) / 2) hrefl2_mem (-(T / 2)) (by rw [abs_neg]; exact hT2_half)
    -- rewrite s/2 and (1-s)/2
    have h_psi1' : ‖deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)‖ ≤
        Cd1 * Real.log (1 + |T / 2|) := hs2_eq ▸ h_psi1
    have h_psi2' : ‖deriv Complex.Gamma ((1 - s) / 2) / Complex.Gamma ((1 - s) / 2)‖ ≤
        Cd2 * Real.log (1 + |T / 2|) := by
      have : (1 - s) / 2 = (((1 - σ) / 2 : ℝ) : ℂ) + ((-(T / 2) : ℝ) : ℂ) * Complex.I :=
        hrefl2_eq
      rw [this]
      have : |-(T / 2)| = |T / 2| := abs_neg _
      rw [this] at h_psi2
      exact h_psi2
    -- log(1+|T/2|) ≤ log(1+|T|)
    have h_log_half : Real.log (1 + |T / 2|) ≤ Real.log (1 + |T|) := by
      apply Real.log_le_log (by positivity)
      have : |T / 2| ≤ |T| := by
        rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        exact div_le_self (abs_nonneg T) (by norm_num)
      linarith
    have h_log_nn : 0 ≤ Real.log (1 + |T|) := Real.log_nonneg (by linarith [abs_nonneg T])
    have h_log2T : Real.log 2 ≤ Real.log (1 + |T|) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg T])
    -- Combine: logπ + (Cd1+Cd2)/2 * log(1+|T|) ≤ Cbig * log(1+|T|)
    have h_sum_bd : ‖archKernel s‖ ≤
        Real.log Real.pi + (Cd1 + Cd2) / 2 * Real.log (1 + |T|) := by
      calc ‖archKernel s‖
          ≤ ‖deriv Complex.Gammaℝ s / s.Gammaℝ‖ +
              ‖deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ‖ := h_tri
        _ ≤ (Real.log Real.pi / 2 + (1 / 2) * ‖deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)‖) +
              (Real.log Real.pi / 2 + (1 / 2) * ‖deriv Complex.Gamma ((1 - s) / 2) /
                Complex.Gamma ((1 - s) / 2)‖) := add_le_add h_term1 h_term2
        _ ≤ Real.log Real.pi + (Cd1 + Cd2) / 2 * Real.log (1 + |T|) := by
              have h1 : (1 / 2 : ℝ) * ‖deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)‖ ≤
                  Cd1 / 2 * Real.log (1 + |T|) :=
                calc (1 / 2) * ‖deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)‖
                    ≤ (1 / 2) * (Cd1 * Real.log (1 + |T / 2|)) :=
                      mul_le_mul_of_nonneg_left h_psi1' (by norm_num)
                  _ ≤ (1 / 2) * (Cd1 * Real.log (1 + |T|)) :=
                      mul_le_mul_of_nonneg_left
                        (mul_le_mul_of_nonneg_left h_log_half hCd1_pos.le) (by norm_num)
                  _ = Cd1 / 2 * Real.log (1 + |T|) := by ring
              have h2 : (1 / 2 : ℝ) * ‖deriv Complex.Gamma ((1 - s) / 2) /
                  Complex.Gamma ((1 - s) / 2)‖ ≤ Cd2 / 2 * Real.log (1 + |T|) :=
                calc (1 / 2) * ‖deriv Complex.Gamma ((1 - s) / 2) / Complex.Gamma ((1 - s) / 2)‖
                    ≤ (1 / 2) * (Cd2 * Real.log (1 + |T / 2|)) :=
                      mul_le_mul_of_nonneg_left h_psi2' (by norm_num)
                  _ ≤ (1 / 2) * (Cd2 * Real.log (1 + |T|)) :=
                      mul_le_mul_of_nonneg_left
                        (mul_le_mul_of_nonneg_left h_log_half hCd2_pos.le) (by norm_num)
                  _ = Cd2 / 2 * Real.log (1 + |T|) := by ring
              linarith
    -- logπ ≤ (logπ/log2) * log(1+|T|). And Cbig ≥ logπ/log2 + (Cd1+Cd2)/2.
    calc ‖archKernel s‖
        ≤ Real.log Real.pi + (Cd1 + Cd2) / 2 * Real.log (1 + |T|) := h_sum_bd
      _ ≤ Cbig * Real.log (1 + |T|) := by
            have h_logπ_coeff : Real.log Real.pi ≤
                (Real.log Real.pi / Real.log 2) * Real.log (1 + |T|) :=
              calc Real.log Real.pi
                  = (Real.log Real.pi / Real.log 2) * Real.log 2 := by
                    rw [div_mul_cancel₀ _ hlog2_pos.ne']
                _ ≤ (Real.log Real.pi / Real.log 2) * Real.log (1 + |T|) :=
                    mul_le_mul_of_nonneg_left h_log2T (div_nonneg hlogπ_nn hlog2_pos.le)
            -- logπ/log2 ≤ Cbig - (Cd1+Cd2)/2 because logπ < 2 ≤ 2*log2
            -- (since log2 > 0.6931 > 0.5, and logπ < log(4) = 2*log2 < 2)
            have hlog2_tight : (0.693 : ℝ) < Real.log 2 := by
              have := Real.log_two_gt_d9; linarith
            have hlogpi_lt2log2 : Real.log Real.pi < 2 * Real.log 2 := by
              have hpi_lt4 : Real.pi < 4 := Real.pi_lt_four
              calc Real.log Real.pi < Real.log 4 := Real.log_lt_log Real.pi_pos hpi_lt4
                _ = 2 * Real.log 2 := by
                    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; ring
            have h_logπ_over_log2 : Real.log Real.pi / Real.log 2 ≤ 2 := by
              rw [div_le_iff₀ hlog2_pos]; linarith
            simp only [Cbig]
            nlinarith [h_log_nn, hCd1_pos, hCd2_pos,
              div_nonneg (by linarith [hMdir_nn, hMrefl_nn] :
                0 ≤ Real.log Real.pi + (Mdir + Mrefl) / 2 + 1) hlog2_pos.le]
  · -- 1 ≤ |T| < 2: use compact bound on ψ.
    rw [not_le] at hT2
    have hT2_half_lt1 : |T / 2| < 1 := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
    -- T/2 ∈ [-1, 1] and -(T/2) ∈ [-1, 1]
    have hT2_mem : T / 2 ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨by have := (abs_lt.mp hT2_half_lt1).1; linarith,
       by have := (abs_lt.mp hT2_half_lt1).2; linarith⟩
    have hT2_neg_mem : -(T / 2) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨by have := (abs_lt.mp hT2_half_lt1).2; linarith,
       by have := (abs_lt.mp hT2_half_lt1).1; linarith⟩
    -- ψ(σ/2 + iT/2) ≤ Mdir via compact bound
    have hpair_dir : (σ / 2, T / 2) ∈ Set.Icc (a / 2) (b / 2) ×ˢ Set.Icc (-1 : ℝ) 1 :=
      Set.mem_prod.mpr ⟨hσ2_mem, hT2_mem⟩
    have h_psi1_compact : ‖deriv Complex.Gamma (((σ / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I) /
        Complex.Gamma (((σ / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ Mdir :=
      le_csSup hBdd_dir ⟨(σ / 2, T / 2), hpair_dir, rfl⟩
    have h_psi1' : ‖deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)‖ ≤ Mdir :=
      hs2_eq ▸ h_psi1_compact
    -- ψ((1-σ)/2 + i(-(T/2))) ≤ Mrefl via compact bound
    have hpair_refl : ((1 - σ) / 2, -(T / 2)) ∈
        Set.Icc ((1 - b) / 2) ((1 - a) / 2) ×ˢ Set.Icc (-1 : ℝ) 1 :=
      Set.mem_prod.mpr ⟨hrefl2_mem, hT2_neg_mem⟩
    have h_psi2_compact : ‖deriv Complex.Gamma ((((1 - σ) / 2 : ℝ) : ℂ) +
          ((-(T / 2) : ℝ) : ℂ) * Complex.I) /
        Complex.Gamma ((((1 - σ) / 2 : ℝ) : ℂ) +
          ((-(T / 2) : ℝ) : ℂ) * Complex.I)‖ ≤ Mrefl :=
      le_csSup hBdd_refl ⟨((1 - σ) / 2, -(T / 2)), hpair_refl, rfl⟩
    have h_psi2' : ‖deriv Complex.Gamma ((1 - s) / 2) / Complex.Gamma ((1 - s) / 2)‖ ≤ Mrefl := by
      rw [hrefl2_eq]; exact h_psi2_compact
    -- log(1+|T|) ≥ log 2
    have h_logT_ge_log2 : Real.log 2 ≤ Real.log (1 + |T|) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg T])
    have h_log_nn : 0 ≤ Real.log (1 + |T|) := le_trans hlog2_pos.le h_logT_ge_log2
    have hnum : 0 ≤ Real.log Real.pi + (Mdir + Mrefl) / 2 + 1 := by linarith
    calc ‖archKernel s‖
        ≤ ‖deriv Complex.Gammaℝ s / s.Gammaℝ‖ +
            ‖deriv Complex.Gammaℝ (1 - s) / (1 - s).Gammaℝ‖ := h_tri
      _ ≤ (Real.log Real.pi / 2 + (1 / 2) * ‖deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)‖) +
            (Real.log Real.pi / 2 + (1 / 2) * ‖deriv Complex.Gamma ((1 - s) / 2) /
              Complex.Gamma ((1 - s) / 2)‖) := add_le_add h_term1 h_term2
      _ ≤ Real.log Real.pi + (Mdir + Mrefl) / 2 := by nlinarith [h_psi1', h_psi2']
      _ ≤ Real.log Real.pi + (Mdir + Mrefl) / 2 + 1 := by linarith
      _ ≤ (Real.log Real.pi + (Mdir + Mrefl) / 2 + 1) / Real.log 2 * Real.log (1 + |T|) := by
            have h_ge_one : 1 ≤ Real.log (1 + |T|) / Real.log 2 :=
              (one_le_div hlog2_pos).mpr h_logT_ge_log2
            calc Real.log Real.pi + (Mdir + Mrefl) / 2 + 1
                ≤ (Real.log Real.pi + (Mdir + Mrefl) / 2 + 1) *
                    (Real.log (1 + |T|) / Real.log 2) :=
                  le_mul_of_one_le_right hnum h_ge_one
              _ = (Real.log Real.pi + (Mdir + Mrefl) / 2 + 1) / Real.log 2 *
                    Real.log (1 + |T|) := by ring
      _ ≤ Cbig * Real.log (1 + |T|) := by
            simp only [Cbig]
            have hc_nn : 0 ≤ Real.log Real.pi + (Cd1 + Cd2) / 2 + 1 := by
              linarith [hCd1_pos, hCd2_pos, hlogπ_nn]
            have hcoeff_le : (Real.log Real.pi + (Mdir + Mrefl) / 2 + 1) / Real.log 2 ≤
                Real.log Real.pi + (Cd1 + Cd2) / 2 + 1 +
                (Real.log Real.pi + (Mdir + Mrefl) / 2 + 1) / Real.log 2 := by linarith
            exact mul_le_mul_of_nonneg_right hcoeff_le h_log_nn

#print axioms archKernel_log_bound_uniform_strip

end ZD.WeilArchKernelResidues

end
