import Mathlib
import RequestProject.XiHadamardFactorization
import RequestProject.XiLogDerivTerms
import RequestProject.XiOrderSummable

/-!
# H8: Partial fraction `ξ'/ξ(s) = A + Σ_ρ xiOrderNat(ρ) · [1/(s-ρ) + 1/ρ]`

Unconditional partial fraction for `logDeriv xiProductMult`, and the H6-derived
version for `riemannXi`.
-/

open Complex Filter Topology Set

noncomputable section

namespace ZD

-- ═══════════════════════════════════════════════════════════════════════════
-- § Summability of per-factor log-derivatives over MultiZeroIdx
-- ═══════════════════════════════════════════════════════════════════════════

/-- Summable majorant over `MultiZeroIdx`: `Σ p, 2‖s‖/‖p.1.val‖² < ∞`. -/
private theorem summable_multi_weierstrassTerm_bound_aux (s : ℂ) :
    Summable (fun p : MultiZeroIdx => 2 * ‖s‖ / ‖p.1.val‖ ^ 2) := by
  have h_summ_weighted :
      Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} =>
        (ZD.xiOrderNat ρ.val : ℝ) * (2 * ‖s‖ / ‖ρ.val‖ ^ 2)) := by
    have := summable_xiOrderNat_div_norm_sq_nontrivialZeros.mul_left (2 * ‖s‖)
    refine this.congr ?_
    intro ρ
    show 2 * ‖s‖ * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) =
      (ZD.xiOrderNat ρ.val : ℝ) * (2 * ‖s‖ / ‖ρ.val‖ ^ 2)
    ring
  apply (summable_sigma_of_nonneg (fun p => by positivity)).mpr
  refine ⟨fun ρ => Summable.of_finite, ?_⟩
  refine h_summ_weighted.congr ?_
  intro ρ
  show (ZD.xiOrderNat ρ.val : ℝ) * (2 * ‖s‖ / ‖ρ.val‖ ^ 2) =
    ∑' (_ : Fin (ZD.xiOrderNat ρ.val)), 2 * ‖s‖ / ‖ρ.val‖ ^ 2
  rw [tsum_const, Nat.card_eq_fintype_card, Fintype.card_fin]
  push_cast; ring

/-- Summability of per-factor log-derivatives of `xiProductMult` over the
multiset `MultiZeroIdx`. Uses `summable_xiOrderNat_div_norm_sq_nontrivialZeros`
as the majorant (after fiber-collapsing). -/
theorem summable_logDeriv_multi {s : ℂ} (hs : s ∉ NontrivialZeros) :
    Summable (fun p : MultiZeroIdx =>
      logDeriv (fun w => 1 + xiWeierstrassTerm p.1.val w) s) := by
  -- Threshold: K = 2‖s‖ + 1.
  set K : ℝ := 2 * ‖s‖ + 1 with hK_def
  have hK_pos : 0 < K := by rw [hK_def]; linarith [norm_nonneg s]
  -- Weighted majorant over MultiZeroIdx: 2‖s‖ / ‖p.1.val‖² (constant in p.2).
  have h_maj_summ : Summable (fun p : MultiZeroIdx =>
      2 * ‖s‖ / ‖p.1.val‖ ^ 2) := summable_multi_weierstrassTerm_bound_aux s
  refine h_maj_summ.of_norm_bounded_eventually ?_
  -- Cofinite: for ‖p.1.val‖ ≥ K, bound holds.
  have hfin_base : {ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} | ‖ρ.val‖ < K}.Finite := by
    have h_ntz_fin : (NontrivialZeros ∩ Metric.closedBall (0 : ℂ) K).Finite :=
      ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite K
    have h_image_fin :
        ((fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => ρ.val) ''
          {ρ | ‖ρ.val‖ < K}).Finite := by
      apply h_ntz_fin.subset
      intro w hw
      rcases hw with ⟨ρ, hρ_lt, hρ_eq⟩
      simp only [Set.mem_setOf_eq] at hρ_lt
      subst hρ_eq
      refine ⟨ρ.property, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]; linarith
    exact h_image_fin.of_finite_image Subtype.val_injective.injOn
  have hfin_multi : {p : MultiZeroIdx | ‖p.1.val‖ < K}.Finite := by
    set bigFinset : Finset MultiZeroIdx :=
      hfin_base.toFinset.attach.biUnion (fun ρ =>
        (Finset.univ : Finset (Fin (ZD.xiOrderNat ρ.val.val))).image (fun k =>
          (⟨ρ.val, k⟩ : MultiZeroIdx))) with hbig_def
    have h_subset : {p : MultiZeroIdx | ‖p.1.val‖ < K} ⊆ ↑bigFinset := by
      intro p hp
      simp only [Set.mem_setOf_eq] at hp
      have hp_in : p.1 ∈ hfin_base.toFinset := by
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact hp
      rw [Finset.mem_coe, hbig_def, Finset.mem_biUnion]
      refine ⟨⟨p.1, hp_in⟩, Finset.mem_attach _ _, ?_⟩
      rw [Finset.mem_image]
      exact ⟨p.2, Finset.mem_univ _, rfl⟩
    exact bigFinset.finite_toSet.subset h_subset
  filter_upwards [hfin_multi.compl_mem_cofinite] with p hp
  have hp_ge_K : K ≤ ‖p.1.val‖ := by
    by_contra h; push_neg at h; exact hp h
  have hρ_ne : p.1.val ≠ 0 := by
    intro heq; rw [heq, norm_zero] at hp_ge_K; linarith
  have hρ_norm_pos : 0 < ‖p.1.val‖ := norm_pos_iff.mpr hρ_ne
  -- s ∉ NontrivialZeros ⟹ s ≠ p.1.val.
  have hs_ne_ρ : s ≠ p.1.val := fun h => hs (h ▸ p.1.property)
  -- logDeriv of factor at s = s/(ρ·(s-ρ)) by H7.
  rw [logDeriv_one_add_xiWeierstrassTerm hρ_ne hs_ne_ρ]
  -- Now bound ‖s/(ρ·(s-ρ))‖ ≤ 2‖s‖/‖ρ‖².
  have h_z_sub_norm : ‖s‖ + 1 ≤ ‖s - p.1.val‖ := by
    have h_abs : |‖p.1.val‖ - ‖s‖| ≤ ‖p.1.val - s‖ := abs_norm_sub_norm_le _ _
    have h_rev : ‖p.1.val - s‖ = ‖s - p.1.val‖ := norm_sub_rev _ _
    have h1 : ‖p.1.val‖ - ‖s‖ ≤ ‖s - p.1.val‖ := by
      have := le_abs_self (‖p.1.val‖ - ‖s‖)
      linarith
    linarith
  have h_z_sub_pos : 0 < ‖s - p.1.val‖ := by
    linarith [norm_nonneg s]
  have h_z_sub_ne : s - p.1.val ≠ 0 := fun heq => by
    rw [heq, norm_zero] at h_z_sub_pos; linarith
  -- ‖s/(ρ·(s-ρ))‖ ≤ 2‖s‖/‖ρ‖².
  have h_bound : ‖s / (p.1.val * (s - p.1.val))‖ ≤ 2 * ‖s‖ / ‖p.1.val‖ ^ 2 := by
    rw [norm_div, norm_mul]
    have h_denom_pos : 0 < ‖p.1.val‖ * ‖s - p.1.val‖ := by positivity
    have h_rhs_denom : 0 < ‖p.1.val‖ ^ 2 := by positivity
    rw [div_le_div_iff₀ h_denom_pos h_rhs_denom]
    have h_triangle : ‖p.1.val‖ ≤ ‖s‖ + ‖s - p.1.val‖ := by
      have h := norm_sub_norm_le p.1.val s
      have hrev : ‖p.1.val - s‖ = ‖s - p.1.val‖ := norm_sub_rev _ _
      linarith
    have h_sub_bd : ‖p.1.val‖ ≤ 2 * ‖s - p.1.val‖ := by
      linarith [h_z_sub_norm, h_triangle]
    have h_gap : ‖p.1.val‖ * (‖p.1.val‖ - 2 * ‖s - p.1.val‖) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (by linarith)
    nlinarith [h_gap, norm_nonneg s, h_denom_pos.le]
  exact h_bound

-- ═══════════════════════════════════════════════════════════════════════════
-- § Log-derivative of xiProductMult as a partial fraction
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Per-factor log-deriv partial fraction of `xiProductMult`** (off zeros).
Applies Mathlib's `logDeriv_tprod_eq_tsum` to the sigma-indexed product, then
converts via `Summable.tsum_sigma'` to the weighted-by-`xiOrderNat` form. -/
theorem logDeriv_xiProductMult_partial_fraction {s : ℂ} (hs : s ∉ NontrivialZeros) :
    logDeriv xiProductMult s =
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val) := by
  -- Hypotheses for logDeriv_tprod_eq_tsum.
  have hf : ∀ p : MultiZeroIdx, (1 + xiWeierstrassTerm p.1.val s) ≠ 0 := by
    intro p
    have hρ_ne : p.1.val ≠ 0 := by
      intro heq
      have hre : (0 : ℝ) < p.1.val.re := p.1.property.1
      rw [heq] at hre; simp at hre
    apply one_add_xiWeierstrassTerm_ne_zero_of_ne hρ_ne
    intro heq; exact hs (heq ▸ p.1.property)
  have hd : ∀ p : MultiZeroIdx,
      DifferentiableOn ℂ (fun w => 1 + xiWeierstrassTerm p.1.val w) Set.univ := by
    intro p
    have hρ_ne : p.1.val ≠ 0 := by
      intro heq
      have hre : (0 : ℝ) < p.1.val.re := p.1.property.1
      rw [heq] at hre; simp at hre
    exact (one_add_xiWeierstrassTerm_differentiable hρ_ne).differentiableOn
  have hm := summable_logDeriv_multi hs
  have htend := xiProductMult_multipliableLocallyUniformlyOn_univ
  have hnez : ∏' p : MultiZeroIdx, (1 + xiWeierstrassTerm p.1.val s) ≠ 0 :=
    xiProductMult_ne_zero_of_notMem_NontrivialZeros hs
  -- Apply Mathlib's tprod-log-deriv theorem.
  have h_log := logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ s) hf hd hm htend hnez
  -- h_log : logDeriv (fun x => ∏' i, (1 + xiWeierstrassTerm i.1.val x)) s = ∑' i, logDeriv (factor i) s
  show logDeriv xiProductMult s = _
  rw [show (xiProductMult : ℂ → ℂ) =
      (fun x => ∏' i : MultiZeroIdx, (1 + xiWeierstrassTerm i.1.val x)) from rfl, h_log]
  -- Now: ∑' p : MultiZeroIdx, logDeriv(factor p) s = Σ' ρ, xiOrderNat(ρ) · [1/(s-ρ) + 1/ρ].
  -- Step 1: express per-factor logDeriv via H7.
  have h_per_factor : ∀ p : MultiZeroIdx,
      logDeriv (fun w => 1 + xiWeierstrassTerm p.1.val w) s =
      s / (p.1.val * (s - p.1.val)) := by
    intro p
    have hρ_ne : p.1.val ≠ 0 := by
      intro heq
      have hre : (0 : ℝ) < p.1.val.re := p.1.property.1
      rw [heq] at hre; simp at hre
    have hs_ne_ρ : s ≠ p.1.val := fun h => hs (h ▸ p.1.property)
    exact logDeriv_one_add_xiWeierstrassTerm hρ_ne hs_ne_ρ
  rw [tsum_congr h_per_factor]
  -- Step 2: split sigma via Summable.tsum_sigma'.
  have h_sigma_summ : Summable (fun p : MultiZeroIdx => s / (p.1.val * (s - p.1.val))) := by
    have := hm
    refine this.congr ?_
    intro p; exact h_per_factor p
  rw [Summable.tsum_sigma'
    (γ := fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => Fin (ZD.xiOrderNat ρ.val))
    (f := fun p : MultiZeroIdx => s / (p.1.val * (s - p.1.val)))
    (fun _ => Summable.of_finite) h_sigma_summ]
  -- Now: Σ' ρ, Σ' k : Fin(xiOrderNat ρ), s/(ρ·(s-ρ)).
  -- Inner sum = xiOrderNat(ρ) · s/(ρ·(s-ρ)).
  apply tsum_congr
  intro ρ
  have hρ_ne : ρ.val ≠ 0 := by
    intro heq
    have hre : (0 : ℝ) < ρ.val.re := ρ.property.1
    rw [heq] at hre; simp at hre
  have hs_ne_ρ : s - ρ.val ≠ 0 := by
    intro heq
    have : s = ρ.val := by linear_combination heq
    exact hs (this ▸ ρ.property)
  -- ∑' (_ : Fin n), c = n · c
  rw [show (∑' (_ : Fin (ZD.xiOrderNat ρ.val)), s / (ρ.val * (s - ρ.val))) =
      (ZD.xiOrderNat ρ.val : ℂ) * (s / (ρ.val * (s - ρ.val))) from ?_]
  · -- s/(ρ·(s-ρ)) = 1/(s-ρ) + 1/ρ
    have h_alg : s / (ρ.val * (s - ρ.val)) = 1 / (s - ρ.val) + 1 / ρ.val := by
      field_simp
      ring
    rw [h_alg]
  · rw [tsum_const, Nat.card_eq_fintype_card, Fintype.card_fin]
    push_cast; ring

#print axioms logDeriv_xiProductMult_partial_fraction

-- ═══════════════════════════════════════════════════════════════════════════
-- § Main H8: ξ'/ξ partial fraction (requires H6 Hadamard factorization)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **H8 main theorem**: Hadamard partial fraction for `ξ'/ξ` with
multiplicity-weighted residues. Derived from H6
(`riemannXi_hadamard_factorization`) + `logDeriv_xiProductMult_partial_fraction`. -/
theorem xi_logDeriv_partial_fraction :
    ∃ A : ℂ, ∀ s : ℂ, s ∉ NontrivialZeros →
      deriv riemannXi s / riemannXi s =
        A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val) := by
  obtain ⟨A, B, hAB⟩ := riemannXi_hadamard_factorization
  refine ⟨A, fun s hs => ?_⟩
  -- logDeriv ξ s = A + logDeriv xiProductMult s, then apply the intermediate.
  have h_factor : riemannXi = fun z => Complex.exp (A * z + B) * xiProductMult z := by
    funext z; exact hAB z
  have hs_ne : xiProductMult s ≠ 0 := xiProductMult_ne_zero_of_notMem_NontrivialZeros hs
  have h_exp_ne : Complex.exp (A * s + B) ≠ 0 := Complex.exp_ne_zero _
  have h_diff_exp : DifferentiableAt ℂ (fun z => Complex.exp (A * z + B)) s := by
    apply DifferentiableAt.cexp
    exact (differentiableAt_id.const_mul A).add_const B
  have h_diff_P : DifferentiableAt ℂ xiProductMult s :=
    xiProductMult_differentiable s
  -- logDeriv(exp(A·z+B)) at s = A.
  have h_log_exp : logDeriv (fun z => Complex.exp (A * z + B)) s = A := by
    rw [show (fun z : ℂ => Complex.exp (A * z + B)) =
      Complex.exp ∘ (fun z : ℂ => A * z + B) from rfl]
    rw [logDeriv_comp (by fun_prop) (by fun_prop), Complex.logDeriv_exp]
    have h_deriv : deriv (fun z : ℂ => A * z + B) s = A := by
      rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'']; ring
    rw [h_deriv]; simp
  -- logDeriv ξ = logDeriv (exp · P) = logDeriv exp + logDeriv P = A + logDeriv P.
  have h_logDeriv_ξ : logDeriv riemannXi s = A + logDeriv xiProductMult s := by
    rw [h_factor]
    rw [logDeriv_mul s h_exp_ne hs_ne h_diff_exp h_diff_P]
    rw [h_log_exp]
  -- deriv ξ / ξ = logDeriv ξ; combine.
  show deriv riemannXi s / riemannXi s = _
  rw [show deriv riemannXi s / riemannXi s = logDeriv riemannXi s from
    (logDeriv_apply riemannXi s).symm]
  rw [h_logDeriv_ξ, logDeriv_xiProductMult_partial_fraction hs]

#print axioms xi_logDeriv_partial_fraction

end ZD
