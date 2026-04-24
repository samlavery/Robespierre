import Mathlib
import RequestProject.ZetaZeroDefs
import RequestProject.XiProductMultPartialFraction
import RequestProject.XiHadamardLog
import RequestProject.XiOverPGrowth

/-!
# Local open patches for the Hadamard contour argument

This file isolates the geometric part of the remaining H6 bridge.  The missing
analytic theorem is a local partial-fraction identity for `ξ'/ξ` on a zero-free
open patch; once that theorem exists, [XiHadamardFactorization.lean](/Users/samuellavery/codex3/RequestProject/XiHadamardFactorization.lean:300)
already upgrades it to the global constancy of `xiHadamardD`.

The point of this file is to keep the patch itself and its elementary geometry
out of the factorization file.

## Target theorem shape

The actual theorem still to prove from the rectangle/boundary-limit machinery is
intended to have the following form.

```lean
theorem xi_logDeriv_partial_fraction_on_open :
    ∃ U : Set ℂ,
      IsOpen U ∧ U.Nonempty ∧ U ⊆ ((NontrivialZeros : Set ℂ)ᶜ) ∧
      ∃ A : ℂ, ∀ s : ℂ, s ∈ U →
        deriv riemannXi s / riemannXi s =
          A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)
```

The remaining proof obligations after this file are:

1. prove the boundary-limit identity on `hadamardGoodPatch T δ`;
2. package the constant term coming from the limiting boundary integrals;
3. feed the resulting theorem into
   `xiHadamardD_eq_const_from_partial_fraction_on_open`.
-/

open Complex Set Filter Topology

noncomputable section

namespace ZD

/-- The local vertical patch on which the eventual Hadamard partial fraction
should be proved.  The real part is constrained to the critical strip, and the
imaginary part stays within `δ` of a chosen height `T`. -/
def hadamardGoodPatch (T δ : ℝ) : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ |s.im - T| < δ}

theorem mem_hadamardGoodPatch_iff {T δ : ℝ} {s : ℂ} :
    s ∈ hadamardGoodPatch T δ ↔ 0 < s.re ∧ s.re < 1 ∧ |s.im - T| < δ := Iff.rfl

theorem hadamardGoodPatch_isOpen (T δ : ℝ) : IsOpen (hadamardGoodPatch T δ) := by
  rw [hadamardGoodPatch]
  have h_re_gt : IsOpen {s : ℂ | 0 < s.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have h_re_lt : IsOpen {s : ℂ | s.re < 1} := Complex.continuous_re.isOpen_preimage _ isOpen_Iio
  have h_im_band :
      IsOpen {s : ℂ | |s.im - T| < δ} := by
    have h_cont : Continuous (fun s : ℂ => |s.im - T|) :=
      (continuous_abs.comp (Complex.continuous_im.sub continuous_const))
    simpa using h_cont.isOpen_preimage _ isOpen_Iio
  simpa [Set.setOf_and, Set.inter_assoc] using (h_re_gt.inter h_re_lt).inter h_im_band

theorem hadamardGoodPatch_nonempty {T δ : ℝ} (hδ : 0 < δ) :
    (hadamardGoodPatch T δ).Nonempty := by
  refine ⟨(1 / 2 : ℂ) + (T : ℂ) * I, ?_⟩
  constructor
  · norm_num
  constructor
  · norm_num
  · have him : (((1 / 2 : ℂ) + (T : ℂ) * I).im - T) = 0 := by
      simp
    rw [him]
    simpa using hδ

theorem center_mem_hadamardGoodPatch {T δ : ℝ} (hδ : 0 < δ) :
    ((1 / 2 : ℂ) + (T : ℂ) * I) ∈ hadamardGoodPatch T δ := by
  constructor
  · norm_num
  constructor
  · norm_num
  · have him : (((1 / 2 : ℂ) + (T : ℂ) * I).im - T) = 0 := by
      simp
    rw [him]
    simpa using hδ

/-- If every nontrivial zero has imaginary part at distance at least `δ` from
`T`, then the entire vertical patch `hadamardGoodPatch T δ` is zero-free. -/
theorem hadamardGoodPatch_subset_compl_of_im_separated
    {Z : Set ℂ} {T δ : ℝ}
    (hsep : ∀ ρ ∈ Z, δ ≤ |ρ.im - T|) :
    hadamardGoodPatch T δ ⊆ Zᶜ := by
  intro s hs hsz
  have hs_im : |s.im - T| < δ := hs.2.2
  have hρ_im : δ ≤ |s.im - T| := by
    simpa using hsep s hsz
  linarith

/-- Convenience wrapper bundling the three basic properties needed by the H6
replacement theorem: openness, nonemptiness, and zero-freeness. -/
theorem hadamardGoodPatch_spec
    {Z : Set ℂ} {T δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ ∈ Z, δ ≤ |ρ.im - T|) :
    IsOpen (hadamardGoodPatch T δ) ∧
      (hadamardGoodPatch T δ).Nonempty ∧
      hadamardGoodPatch T δ ⊆ Zᶜ := by
  refine ⟨hadamardGoodPatch_isOpen T δ, hadamardGoodPatch_nonempty hδ, ?_⟩
  exact hadamardGoodPatch_subset_compl_of_im_separated hsep

/-- Specialization of `hadamardGoodPatch_spec` to the canonical set of
nontrivial zeta zeros. This is the geometric input needed by the eventual
local Hadamard partial-fraction theorem. -/
theorem hadamardGoodPatch_spec_nontrivialZeros
    {T δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ ∈ NontrivialZeros, δ ≤ |ρ.im - T|) :
    IsOpen (hadamardGoodPatch T δ) ∧
      (hadamardGoodPatch T δ).Nonempty ∧
      hadamardGoodPatch T δ ⊆ ((NontrivialZeros : Set ℂ)ᶜ) := by
  simpa using hadamardGoodPatch_spec (Z := NontrivialZeros) hδ hsep

-- ═══════════════════════════════════════════════════════════════════════════
-- § Target theorem: partial fraction for ξ'/ξ on a zero-free open patch
-- ═══════════════════════════════════════════════════════════════════════════

/-!
The statement below is the open-patch analogue of the Hadamard log-derivative
partial fraction for ξ.  Its proof is split into two halves:

* A *reduction* step that packages the existing unconditional partial fraction
  for `logDeriv xiProductMult` (available globally off `NontrivialZeros`) with
  any local constancy datum for the difference `ξ'/ξ − logDeriv xiProductMult`.
* The *analytic input* — the local constancy of that difference — which is the
  content the contour/rectangle program is meant to supply.  We expose it here
  as an explicit hypothesis `hDiff` so that the reduction step itself can be
  proved unconditionally in this file and reused elsewhere once the contour
  assembly is complete.

The `hDiff` hypothesis says: there is an open set `U` on which the literal
difference of log-derivatives takes a fixed value `A`.  Combined with
`logDeriv_xiProductMult_partial_fraction`, this immediately yields the target
partial-fraction identity on `U`.
-/

/-- **Reduction step (unconditional).** Given any open patch `U` in the
zero-free set where `ξ'/ξ − logDeriv xiProductMult` is a fixed constant `A`,
the Hadamard log-derivative partial fraction for `ξ` holds on `U` with that
constant.

This is the "packaging" half of the local-patch program: it records that once
the boundary-limit analysis on `hadamardGoodPatch` produces local constancy of
the difference, the partial fraction for `ξ` follows for free from the
unconditional per-factor partial fraction of `xiProductMult`. -/
theorem xi_logDeriv_partial_fraction_of_diff_const_on_open
    {U : Set ℂ} (hU_open : IsOpen U) (hU_nonempty : U.Nonempty)
    (hU_sub : U ⊆ ((NontrivialZeros : Set ℂ)ᶜ))
    {A : ℂ}
    (hDiff : ∀ s ∈ U,
      deriv riemannXi s / riemannXi s - logDeriv xiProductMult s = A) :
    ∃ U : Set ℂ,
      IsOpen U ∧ U.Nonempty ∧ U ⊆ ((NontrivialZeros : Set ℂ)ᶜ) ∧
      ∃ A : ℂ, ∀ s : ℂ, s ∈ U →
        deriv riemannXi s / riemannXi s =
          A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val) := by
  refine ⟨U, hU_open, hU_nonempty, hU_sub, A, ?_⟩
  intro s hsU
  have hs_notMem : s ∉ NontrivialZeros := hU_sub hsU
  have h_pf := logDeriv_xiProductMult_partial_fraction hs_notMem
  have h_diff := hDiff s hsU
  calc
    deriv riemannXi s / riemannXi s
        = (deriv riemannXi s / riemannXi s - logDeriv xiProductMult s)
            + logDeriv xiProductMult s := by ring
    _ = A + logDeriv xiProductMult s := by rw [h_diff]
    _ = A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val) := by
          rw [h_pf]

-- ═══════════════════════════════════════════════════════════════════════════
-- § Reduction: constant log-derivative of `xiOverP` ⇒ partial fraction
-- ═══════════════════════════════════════════════════════════════════════════

/-!
The remaining input to the open-patch partial fraction is the local constancy
of `ξ'/ξ − logDeriv xiProductMult`.  Classically that constancy follows from
the Hadamard factorization of the zero-free entire function `xiOverP`: once
`logDeriv xiOverP` is globally constant, the same constant `A` governs the
log-derivative difference on the whole zero-free complement.

We package that reduction unconditionally here, taking the hypothesis
"`logDeriv xiOverP` is globally constant" explicitly.  Supplying that
hypothesis from growth bounds on `xiOverP` is the job of the downstream
Hadamard factorization assembly (`XiHadamardFactorization.lean`) and is not
duplicated here.
-/

/-- **Unconditional reduction.** If `logDeriv xiOverP` is globally constant
with value `A`, then the partial-fraction identity for `ξ'/ξ` holds on the
entire zero-free complement `(NontrivialZeros)ᶜ` with the same constant `A`.

This is the open-patch Hadamard partial fraction reduced to its essential
input: global constancy of the log-derivative of the entire zero-free
function `ξ / xiProductMult`. -/
theorem xi_logDeriv_partial_fraction_on_open_of_logDeriv_xiOverP_const
    (hA : ∃ A : ℂ, ∀ z : ℂ, logDeriv xiOverP z = A) :
    ∃ U : Set ℂ,
      IsOpen U ∧ U.Nonempty ∧ U ⊆ ((NontrivialZeros : Set ℂ)ᶜ) ∧
      ∃ A : ℂ, ∀ s : ℂ, s ∈ U →
        deriv riemannXi s / riemannXi s =
          A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val) := by
  obtain ⟨A, hA⟩ := hA
  -- Take U = complement of NontrivialZeros (open, nonempty, sub).
  set U : Set ℂ := ((NontrivialZeros : Set ℂ)ᶜ) with hU_def
  have hU_open : IsOpen U := by
    have h_cont : Continuous riemannXi := riemannXi_differentiable.continuous
    have h_closed : IsClosed (riemannXi ⁻¹' ({0} : Set ℂ)) :=
      isClosed_singleton.preimage h_cont
    have hU_eq : U = (riemannXi ⁻¹' ({0} : Set ℂ))ᶜ := by
      ext z
      simp [hU_def, ZD.riemannXi_eq_zero_iff]
    rw [hU_eq]
    exact h_closed.isOpen_compl
  have hU_nonempty : U.Nonempty := by
    refine ⟨0, ?_⟩
    intro h0
    exact ZD.ZeroCount.riemannXi_zero_ne_zero ((ZD.riemannXi_eq_zero_iff 0).mpr h0)
  have hU_sub : U ⊆ ((NontrivialZeros : Set ℂ)ᶜ) := by intro z hz; exact hz
  -- On U = compl NontrivialZeros, the difference ξ'/ξ - logDeriv xiProductMult
  -- equals logDeriv xiOverP = A.
  have hDiff : ∀ s ∈ U,
      deriv riemannXi s / riemannXi s - logDeriv xiProductMult s = A := by
    intro s hs
    have h_s_notMem : s ∉ NontrivialZeros := hs
    have h_xi_ne : riemannXi s ≠ 0 := fun h => h_s_notMem ((ZD.riemannXi_eq_zero_iff s).mp h)
    have h_P_ne : xiProductMult s ≠ 0 :=
      xiProductMult_ne_zero_of_notMem_NontrivialZeros h_s_notMem
    -- Step 1: The literal ratio `ξ/P` equals `xiOverP` on a neighborhood of `s`.
    have h_ratio_ev :
        (fun w => riemannXi w / xiProductMult w) =ᶠ[nhds s] xiOverP := by
      have h_anal_xi : AnalyticAt ℂ riemannXi s :=
        ZD.ZeroCount.riemannXi_analyticOnNhd_univ s (Set.mem_univ s)
      have h_anal_P : AnalyticAt ℂ xiProductMult s :=
        (Complex.analyticOnNhd_univ_iff_differentiable.mpr
          xiProductMult_differentiable) s (Set.mem_univ s)
      have h_ratio_nf :
          MeromorphicNFAt (fun w => riemannXi w / xiProductMult w) s :=
        (h_anal_xi.div h_anal_P h_P_ne).meromorphicNFAt
      have h_punct :
          (fun w => riemannXi w / xiProductMult w) =ᶠ[nhdsWithin s {s}ᶜ] xiOverP := by
        have h_mem :
            {w | (fun w => riemannXi w / xiProductMult w) w = xiOverP w} ∈
              codiscreteWithin (Set.univ : Set ℂ) := xiOverP_eq_ratio_codiscretely
        rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h_mem
        simpa only [Set.compl_univ, Set.union_empty] using h_mem s (Set.mem_univ s)
      exact (h_ratio_nf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
        (xiOverP_analyticAt s).meromorphicNFAt).1 h_punct
    -- Step 2: Therefore logDeriv(ξ/P) s = logDeriv xiOverP s.
    have h_ld_eq :
        logDeriv (fun w => riemannXi w / xiProductMult w) s = logDeriv xiOverP s := by
      rw [logDeriv_apply, logDeriv_apply,
        Filter.EventuallyEq.deriv_eq h_ratio_ev, h_ratio_ev.eq_of_nhds]
    -- Step 3: logDeriv of ξ/P splits as logDeriv ξ - logDeriv P.
    have h_ld_ratio :
        logDeriv (fun w => riemannXi w / xiProductMult w) s =
          logDeriv riemannXi s - logDeriv xiProductMult s := by
      simpa using logDeriv_div (f := riemannXi) (g := xiProductMult) s h_xi_ne h_P_ne
        (riemannXi_differentiable s) (xiProductMult_differentiable s)
    -- Step 4: logDeriv ξ at s is literally deriv ξ / ξ at s.
    have h_ld_riemann : logDeriv riemannXi s = deriv riemannXi s / riemannXi s := rfl
    -- Chain: ξ'/ξ - logDeriv P = logDeriv(ξ/P) = logDeriv xiOverP = A.
    calc
      deriv riemannXi s / riemannXi s - logDeriv xiProductMult s
          = logDeriv riemannXi s - logDeriv xiProductMult s := by rw [h_ld_riemann]
      _ = logDeriv (fun w => riemannXi w / xiProductMult w) s := h_ld_ratio.symm
      _ = logDeriv xiOverP s := h_ld_eq
      _ = A := hA s
  exact xi_logDeriv_partial_fraction_of_diff_const_on_open hU_open hU_nonempty hU_sub hDiff

/-- **Specialization to the canonical patch `hadamardGoodPatch T δ`.** When
the patch is zero-free (im-separation from every nontrivial zero) *and* the
log-derivative difference is locally constant on it, the partial-fraction
identity for `ξ'/ξ` holds on the patch. -/
theorem xi_logDeriv_partial_fraction_on_hadamardGoodPatch
    {T δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ ∈ NontrivialZeros, δ ≤ |ρ.im - T|)
    {A : ℂ}
    (hDiff : ∀ s ∈ hadamardGoodPatch T δ,
      deriv riemannXi s / riemannXi s - logDeriv xiProductMult s = A) :
    ∃ U : Set ℂ,
      IsOpen U ∧ U.Nonempty ∧ U ⊆ ((NontrivialZeros : Set ℂ)ᶜ) ∧
      ∃ A : ℂ, ∀ s : ℂ, s ∈ U →
        deriv riemannXi s / riemannXi s =
          A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val) := by
  obtain ⟨hU_open, hU_nonempty, hU_sub⟩ :=
    hadamardGoodPatch_spec_nontrivialZeros (T := T) (δ := δ) hδ hsep
  exact xi_logDeriv_partial_fraction_of_diff_const_on_open
    hU_open hU_nonempty hU_sub hDiff

-- ═══════════════════════════════════════════════════════════════════════════
-- § Borel–Carathéodory bridge: linear real-part growth ⇒ bounded derivative
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Derivative bound via Borel–Carathéodory.** If `f : ℂ → ℂ` is entire,
vanishes at `0`, and has real part bounded by `A + B * ‖z‖` with `A, B ≥ 0`,
then `deriv f` is globally bounded.

Proof: at each `z₀`, apply `Complex.borelCaratheodory_zero` on `Metric.ball 0 R`
with `R := 2*‖z₀‖ + 4` and `M := A + B*R + 1`, then estimate `‖f‖` on the
sphere `Metric.sphere z₀ r` with `r := (‖z₀‖ + 4)/2` and apply
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`. The resulting bound
`16*M/(‖z₀‖+4)` simplifies (using `r ≥ 2`) to `4*A + 48*B + 4`. -/
private theorem deriv_bound_of_linear_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 = 0)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrowth : ∀ z : ℂ, (f z).re ≤ A + B * ‖z‖) :
    ∃ C : ℝ, ∀ z₀ : ℂ, ‖deriv f z₀‖ ≤ C := by
  refine ⟨4 * A + 48 * B + 4, ?_⟩
  intro z₀
  set nz : ℝ := ‖z₀‖ with hnz_def
  have hnz_nn : 0 ≤ nz := norm_nonneg _
  set r : ℝ := (nz + 4) / 2 with hr_def
  set R : ℝ := 2 * nz + 4 with hR_def
  have hr_pos : 0 < r := by rw [hr_def]; linarith
  have hr_ge_two : 2 ≤ r := by rw [hr_def]; linarith
  have hR_pos : 0 < R := by rw [hR_def]; linarith
  have hz₀_ball : z₀ ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, hR_def]
    linarith
  set M : ℝ := A + B * R + 1 with hM_def
  have hM_pos : 0 < M := by rw [hM_def]; nlinarith [mul_nonneg hB (le_of_lt hR_pos)]
  -- Borel–Carathéodory gives `‖f z‖ ≤ 2*M*‖z‖/(R - ‖z‖)` on ball 0 R.
  have hBC : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) := by
    intro z hz
    have hf_diff_on : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R) :=
      hf.differentiableOn
    have hf_maps : Set.MapsTo f (Metric.ball (0 : ℂ) R) {w : ℂ | w.re ≤ M} := by
      intro w hw
      have hw_norm : ‖w‖ < R := by
        rw [Metric.mem_ball, dist_zero_right] at hw
        exact hw
      have hgw : (f w).re ≤ A + B * ‖w‖ := hgrowth w
      have hB_bound : B * ‖w‖ ≤ B * R := by
        apply mul_le_mul_of_nonneg_left (le_of_lt hw_norm) hB
      show (f w).re ≤ M
      rw [hM_def]
      linarith
    exact Complex.borelCaratheodory_zero hM_pos hf_diff_on hf_maps hR_pos hz hf0
  -- On `sphere z₀ r`, estimate `‖f w‖`.
  have h_sphere_bd : ∀ w ∈ Metric.sphere z₀ r, ‖f w‖ ≤ 8 * M := by
    intro w hw
    have hw_dist : ‖w - z₀‖ = r := by
      rw [← dist_eq_norm]; exact hw
    have hw_norm_le : ‖w‖ ≤ nz + r := by
      have : ‖w‖ = ‖(w - z₀) + z₀‖ := by ring_nf
      rw [this]
      calc ‖(w - z₀) + z₀‖ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ = r + nz := by rw [hw_dist]
        _ = nz + r := by ring
    have hw_norm_nn : 0 ≤ ‖w‖ := norm_nonneg _
    have hw_in_ball : w ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right]
      have h1 : nz + r < R := by
        rw [hr_def, hR_def]; linarith
      linarith
    have hR_sub_w : R - ‖w‖ ≥ r := by
      have h1 : ‖w‖ ≤ nz + r := hw_norm_le
      have h2 : R - (nz + r) = r := by rw [hR_def, hr_def]; ring
      linarith
    have hBCw := hBC w hw_in_ball
    have hR_sub_pos : 0 < R - ‖w‖ := by linarith
    -- `2*M*‖w‖/(R-‖w‖) ≤ 2*M*‖w‖/r ≤ 2*M*R/r`
    have hMM_nn : 0 ≤ 2 * M := by linarith
    have hNum_nn : 0 ≤ 2 * M * ‖w‖ := mul_nonneg hMM_nn hw_norm_nn
    -- `2*M*‖w‖/(R-‖w‖) ≤ 2*M*R/r`
    have step1 : 2 * M * ‖w‖ / (R - ‖w‖) ≤ 2 * M * R / r := by
      apply div_le_div₀ ?_ ?_ hr_pos hR_sub_w
      · exact mul_nonneg hMM_nn (le_of_lt hR_pos)
      · apply mul_le_mul_of_nonneg_left _ hMM_nn
        have hw_lt_R : ‖w‖ ≤ R := by
          rw [Metric.mem_ball, dist_zero_right] at hw_in_ball
          exact le_of_lt hw_in_ball
        exact hw_lt_R
    -- `R ≤ 4r` since `R = 2*nz+4 = 4*((nz+4)/2) - 4 = 4r - 4 ≤ 4r`
    have hR_le_4r : R ≤ 4 * r := by rw [hR_def, hr_def]; linarith
    have step2 : 2 * M * R / r ≤ 8 * M := by
      rw [div_le_iff₀ hr_pos]
      calc 2 * M * R ≤ 2 * M * (4 * r) := by
              apply mul_le_mul_of_nonneg_left hR_le_4r (by linarith)
        _ = 8 * M * r := by ring
    linarith [hBCw.trans (step1.trans step2)]
  -- Apply derivative bound on sphere.
  have h_dcc : DiffContOnCl ℂ f (Metric.ball z₀ r) := hf.diffContOnCl
  have hderiv : ‖deriv f z₀‖ ≤ (8 * M) / r :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr_pos h_dcc h_sphere_bd
  -- `(8*M)/r ≤ 4*A + 48*B + 4`.
  have h_final : (8 * M) / r ≤ 4 * A + 48 * B + 4 := by
    rw [div_le_iff₀ hr_pos]
    -- Goal: 8 * M ≤ (4*A + 48*B + 4) * r
    -- `M = A + B*R + 1 = A + B*(2*nz + 4) + 1 = A + 2B*nz + 4B + 1`
    -- `r = (nz + 4)/2`, so `(4A + 48B + 4) * r = (4A + 48B + 4)*(nz+4)/2 = (2A + 24B + 2)*(nz+4)`
    -- `= 2A*nz + 8A + 24B*nz + 96B + 2*nz + 8`
    -- `8*M = 8A + 16B*nz + 32B + 8`
    -- Difference: `(2A + 24B + 2)*(nz+4) - 8M = 2A*nz - 8B*nz + 2*nz + 64B`
    -- `= (2A + 2)*nz + 8B*nz*? ... ` Let me recompute.
    -- `(2A + 24B + 2)*(nz+4) = 2A*nz + 24B*nz + 2*nz + 8A + 96B + 8`
    -- `- 8M = -8A - 16B*nz - 32B - 8`
    -- Diff = 2A*nz + 8B*nz + 2*nz + 64B ≥ 0 ✓
    have hBnz : 0 ≤ B * nz := mul_nonneg hB hnz_nn
    have hAnz : 0 ≤ A * nz := mul_nonneg hA hnz_nn
    have hBR : 0 ≤ B * R := mul_nonneg hB (le_of_lt hR_pos)
    rw [hM_def, hR_def, hr_def]
    nlinarith [hBnz, hAnz, hnz_nn, hA, hB]
  linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- § Borel–Carathéodory bridge: mean-type real-part growth ⇒ second derivative = 0
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Majorant tendsto:** `32 * (1 + A + B R log (R+2)) / (R - nz)^2 → 0` as `R → ∞`.
Pure real-analysis squeeze using `log R / R → 0` and `1/R^2 → 0`. -/
private theorem tendsto_meanType_ratio_zero {A B nz : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hnz : 0 ≤ nz) :
    Filter.Tendsto
      (fun R : ℝ => 32 * (1 + A + B * R * Real.log (R + 2)) / (R - nz) ^ 2)
      Filter.atTop (nhds 0) := by
  have h_maj_tend : Filter.Tendsto
      (fun R : ℝ => 128 * (1 + A) / R^2 + 256 * B * Real.log R / R)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun R : ℝ => 128 * (1 + A) / R^2)
        Filter.atTop (nhds 0) := by
      have hone : Filter.Tendsto (fun R : ℝ => 1 / R^2) Filter.atTop (nhds 0) := by
        have h := @tendsto_pow_neg_atTop ℝ _ _ _ _ _ 2 (by norm_num)
        refine h.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with R _
        rw [zpow_neg, zpow_natCast, inv_eq_one_div]
      have := hone.const_mul (128 * (1 + A))
      simp at this
      refine this.congr' ?_
      filter_upwards with R; ring
    have h2 : Filter.Tendsto (fun R : ℝ => 256 * B * Real.log R / R)
        Filter.atTop (nhds 0) := by
      have hlog : Filter.Tendsto (fun R : ℝ => Real.log R / R)
          Filter.atTop (nhds 0) := by
        have := Real.tendsto_pow_log_div_mul_add_atTop
          (a := (1:ℝ)) (b := 0) (n := 1) (by norm_num)
        simpa using this
      have := hlog.const_mul (256 * B)
      simp at this
      refine this.congr' ?_
      filter_upwards with R; ring
    simpa using h1.add h2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_maj_tend
  · filter_upwards [Filter.eventually_ge_atTop (max 2 (2*nz+1))] with R hR
    apply div_nonneg _ (sq_nonneg _)
    have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
    have h_log_Rplus : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
    have : 0 ≤ B * R * Real.log (R + 2) :=
      mul_nonneg (mul_nonneg hB (by linarith)) h_log_Rplus
    linarith
  · filter_upwards [Filter.eventually_ge_atTop (max 2 (2*nz+1))] with R hR
    have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
    have hR_nz : 2 * nz + 1 ≤ R := le_trans (le_max_right _ _) hR
    have hR_pos : 0 < R := by linarith
    have hR_gt_nz : R > nz := by linarith
    have hR_sub_pos : 0 < R - nz := by linarith
    have h_log_R : 0 < Real.log R := Real.log_pos (by linarith)
    have h_log_Rplus : 0 < Real.log (R + 2) := Real.log_pos (by linarith)
    have h_rmnz_ge : R - nz ≥ R / 2 := by linarith
    have h_sq_bd : (R - nz) ^ 2 ≥ (R / 2) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h_rmnz_ge 2
    have h_denom_bd : (R - nz) ^ 2 ≥ R^2 / 4 := by nlinarith [h_sq_bd]
    have h_log_bd : Real.log (R + 2) ≤ 2 * Real.log R := by
      have h1 : R + 2 ≤ 2 * R := by linarith
      have h2 : Real.log (R + 2) ≤ Real.log (2 * R) :=
        Real.log_le_log (by linarith) h1
      have h3 : Real.log (2 * R) = Real.log 2 + Real.log R :=
        Real.log_mul (by norm_num) (by linarith)
      have h4 : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR2
      linarith
    have h_num : 1 + A + B * R * Real.log (R + 2) ≤
        1 + A + 2 * B * R * Real.log R := by
      have : B * R * Real.log (R + 2) ≤ B * R * (2 * Real.log R) := by
        apply mul_le_mul_of_nonneg_left h_log_bd
        exact mul_nonneg hB (by linarith)
      linarith
    have h_num'_nn : 0 ≤ 1 + A + 2 * B * R * Real.log R := by
      have : 0 ≤ 2 * B * R * Real.log R :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) (by linarith))
          (le_of_lt h_log_R)
      linarith
    have h_step1 : 32 * (1 + A + B * R * Real.log (R + 2)) / (R - nz) ^ 2 ≤
        32 * (1 + A + 2 * B * R * Real.log R) / (R - nz) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have h_step2 : 32 * (1 + A + 2 * B * R * Real.log R) / (R - nz) ^ 2 ≤
        32 * (1 + A + 2 * B * R * Real.log R) / (R^2/4) := by
      apply div_le_div₀ _ (le_refl _) (by positivity) h_denom_bd
      linarith
    have h_step3 : 32 * (1 + A + 2 * B * R * Real.log R) / (R^2/4) =
        128 * (1 + A) / R^2 + 256 * B * Real.log R / R := by
      have hRne : R ≠ 0 := ne_of_gt hR_pos
      field_simp
      ring
    linarith

/-- **Second-derivative bound on entire function from BC + Cauchy.**  If `f` is
entire, vanishes at `0`, and has real part bounded by `A + B ‖z‖ log(‖z‖+2)`
with `A, B ≥ 0`, then for any `R ≥ 3(‖z₀‖+1)` the iterated second derivative
is bounded by `32 · (1 + A + B R log(R+2)) / (R − ‖z₀‖)²`.  Proof: apply
`Complex.borelCaratheodory_zero` on `Metric.ball 0 R`, restrict to the sphere
`Metric.sphere z₀ r` with `r = (R − ‖z₀‖)/2`, then apply the Cauchy-formula
second-derivative estimate `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`. -/
private theorem iteratedDeriv2_bound_of_meanType
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 = 0)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrowth : ∀ z : ℂ, (f z).re ≤ A + B * ‖z‖ * Real.log (‖z‖ + 2))
    (z₀ : ℂ) (R : ℝ) (hR : 3 * (‖z₀‖ + 1) ≤ R) :
    ‖iteratedDeriv 2 f z₀‖ ≤
      32 * (1 + A + B * R * Real.log (R + 2)) / (R - ‖z₀‖) ^ 2 := by
  set nz : ℝ := ‖z₀‖ with hnz_def
  have hnz_nn : 0 ≤ nz := norm_nonneg _
  have hR_pos : 0 < R := by linarith
  have hR_gt_nz : nz + 1 < R := by linarith
  set r : ℝ := (R - nz) / 2 with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; linarith
  have hr_ge_one : 1 ≤ r := by rw [hr_def]; linarith
  set M : ℝ := 1 + A + B * R * Real.log (R + 2) with hM_def
  have hlog_nn : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hM_pos : 0 < M := by
    rw [hM_def]
    have : 0 ≤ B * R * Real.log (R + 2) :=
      mul_nonneg (mul_nonneg hB hR_pos.le) hlog_nn
    linarith
  have hz₀_in_ball : z₀ ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hf_diff_on : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R) :=
    hf.differentiableOn
  have hf_maps : Set.MapsTo f (Metric.ball (0 : ℂ) R) {w : ℂ | w.re ≤ M} := by
    intro w hw
    have hw_norm : ‖w‖ < R := by
      rw [Metric.mem_ball, dist_zero_right] at hw; exact hw
    have hgw : (f w).re ≤ A + B * ‖w‖ * Real.log (‖w‖ + 2) := hgrowth w
    have h_mono : B * ‖w‖ * Real.log (‖w‖ + 2) ≤ B * R * Real.log (R + 2) := by
      have hwnn : 0 ≤ ‖w‖ := norm_nonneg _
      have h1 : B * ‖w‖ ≤ B * R := mul_le_mul_of_nonneg_left hw_norm.le hB
      have h2 : Real.log (‖w‖ + 2) ≤ Real.log (R + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      have h4 : 0 ≤ Real.log (‖w‖ + 2) := Real.log_nonneg (by linarith)
      calc B * ‖w‖ * Real.log (‖w‖ + 2)
          ≤ B * R * Real.log (‖w‖ + 2) := mul_le_mul_of_nonneg_right h1 h4
        _ ≤ B * R * Real.log (R + 2) :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hB hR_pos.le)
    show (f w).re ≤ M
    rw [hM_def]; linarith
  have hBC : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) :=
    fun z hz => Complex.borelCaratheodory_zero hM_pos hf_diff_on hf_maps hR_pos hz hf0
  have h_sphere_bd : ∀ w ∈ Metric.sphere z₀ r, ‖f w‖ ≤ 4 * M := by
    intro w hw
    have hw_dist : ‖w - z₀‖ = r := by rw [← dist_eq_norm]; exact hw
    have hw_norm_le : ‖w‖ ≤ nz + r := by
      calc ‖w‖ = ‖(w - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ = r + nz := by rw [hw_dist]
        _ = nz + r := by ring
    have hw_in_ball : w ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right]
      have h1 : nz + r = nz + (R - nz) / 2 := by rw [hr_def]
      have h2 : nz + (R - nz) / 2 < R := by linarith
      calc ‖w‖ ≤ nz + r := hw_norm_le
        _ < R := by rw [h1]; exact h2
    have hR_sub_w : r ≤ R - ‖w‖ := by
      have h1 : ‖w‖ ≤ nz + r := hw_norm_le
      have h2 : R - (nz + r) = r := by rw [hr_def]; ring
      linarith
    have hR_sub_pos : 0 < R - ‖w‖ := by linarith
    have hBCw := hBC w hw_in_ball
    have hr_ge_nz : nz ≤ r := by rw [hr_def]; linarith
    have hw_nn : 0 ≤ ‖w‖ := norm_nonneg _
    have h_nzr_nn : 0 ≤ nz + r := by linarith
    have h_step1 : 2 * M * ‖w‖ / (R - ‖w‖) ≤ 2 * M * (nz + r) / r := by
      apply div_le_div₀ _ _ hr_pos hR_sub_w
      · exact mul_nonneg (by linarith [hM_pos]) h_nzr_nn
      · exact mul_le_mul_of_nonneg_left hw_norm_le (by linarith [hM_pos])
    have h_step2 : 2 * M * (nz + r) / r ≤ 4 * M := by
      rw [div_le_iff₀ hr_pos]
      have h : nz + r ≤ 2 * r := by linarith
      calc 2 * M * (nz + r) ≤ 2 * M * (2 * r) :=
            mul_le_mul_of_nonneg_left h (by linarith [hM_pos])
        _ = 4 * M * r := by ring
    linarith [hBCw]
  have h_dcc : DiffContOnCl ℂ f (Metric.ball z₀ r) := hf.diffContOnCl
  have hcauchy : ‖iteratedDeriv 2 f z₀‖ ≤ (2 : ℕ).factorial * (4 * M) / r ^ 2 :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hr_pos h_dcc
      h_sphere_bd
  have h_fact2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num
  rw [h_fact2] at hcauchy
  have hr2 : r ^ 2 = (R - nz) ^ 2 / 4 := by rw [hr_def]; ring
  rw [hr2] at hcauchy
  have hfinal : 2 * (4 * M) / ((R - nz) ^ 2 / 4) = 32 * M / (R - nz) ^ 2 := by
    have hRnz_pos : 0 < R - nz := by linarith
    have : (R - nz) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hfinal] at hcauchy
  show ‖iteratedDeriv 2 f z₀‖ ≤ 32 * M / (R - nz) ^ 2
  exact hcauchy

/-- **Second derivative vanishes for entire mean-type function.**  If `f` is
entire with `f(0) = 0` and real part bounded by `A + B ‖z‖ log(‖z‖+2)`
(with `A, B ≥ 0`), then the iterated second derivative of `f` is identically
zero, so `deriv f` is globally constant. -/
private theorem secondDeriv_zero_of_meanType
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 = 0)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrowth : ∀ z : ℂ, (f z).re ≤ A + B * ‖z‖ * Real.log (‖z‖ + 2)) :
    ∀ z₀ : ℂ, iteratedDeriv 2 f z₀ = 0 := by
  intro z₀
  have hnz_nn : 0 ≤ ‖z₀‖ := norm_nonneg _
  have h_bound : ∀ R : ℝ, 3 * (‖z₀‖ + 1) ≤ R →
      ‖iteratedDeriv 2 f z₀‖ ≤
        32 * (1 + A + B * R * Real.log (R + 2)) / (R - ‖z₀‖) ^ 2 :=
    fun R hR => iteratedDeriv2_bound_of_meanType hf hf0 hA hB hgrowth z₀ R hR
  have h_tend : Filter.Tendsto
      (fun R : ℝ => 32 * (1 + A + B * R * Real.log (R + 2)) / (R - ‖z₀‖) ^ 2)
      Filter.atTop (nhds 0) := tendsto_meanType_ratio_zero hA hB hnz_nn
  have h_le_zero : ‖iteratedDeriv 2 f z₀‖ ≤ 0 :=
    ge_of_tendsto h_tend (Filter.eventually_atTop.mpr ⟨3 * (‖z₀‖ + 1), h_bound⟩)
  exact norm_le_zero_iff.mp h_le_zero

-- ═══════════════════════════════════════════════════════════════════════════
-- § Growth of `xiOverP` ⇒ `logDeriv xiOverP` is constant
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Global constancy from mean-type growth.** If `xiOverP` has order-1
mean-type growth `‖xiOverP z‖ ≤ exp (C ‖z‖ · log(‖z‖+2) + D)`, then
`logDeriv xiOverP` is globally constant.

Proof outline:
1. `logDeriv xiOverP` is entire (`xiOverP` is entire and nowhere zero).
2. Build a global primitive `g` with `deriv g = logDeriv xiOverP` via
   `Differentiable.isExactOn_univ` (Morera's theorem on ℂ), then shift so
   `exp (g 0) = xiOverP 0`.
3. Show `exp ∘ g = xiOverP` by verifying that `φ z := exp (g z) / xiOverP z`
   has zero derivative (hence constant) and equals `1` at `0`.
4. Translate the mean-type growth bound on `‖xiOverP‖` into a mean-type bound
   on `(g z).re`.
5. Apply `secondDeriv_zero_of_meanType` to the shifted primitive
   `h z := g z - g 0` to obtain `iteratedDeriv 2 h ≡ 0`, which gives
   `deriv h = deriv g = logDeriv xiOverP` globally constant.

This weakens the hypothesis from order-1 *finite type* (which is the conclusion
of Hadamard factorization and hence classically too strong) to order-1
*mean type* (which is the correct physical growth order of `ξ/xiProductMult`). -/
theorem logDeriv_xiOverP_const_of_growth
    (hG : ∃ C D : ℝ, ∀ z : ℂ,
      ‖xiOverP z‖ ≤ Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2) + D)) :
    ∃ A : ℂ, ∀ z : ℂ, logDeriv xiOverP z = A := by
  obtain ⟨C, D, hG⟩ := hG
  -- Step 1: `logDeriv xiOverP` is entire.
  have h_xi_ne : ∀ z, xiOverP z ≠ 0 := xiOverP_ne_zero
  have h_log_diff : Differentiable ℂ (logDeriv xiOverP) := by
    intro z
    have h_anal : AnalyticAt ℂ xiOverP z := xiOverP_analyticAt z
    have h_deriv_anal : AnalyticAt ℂ (deriv xiOverP) z := h_anal.deriv
    have h_ld : AnalyticAt ℂ (logDeriv xiOverP) z := by
      simpa [logDeriv] using h_deriv_anal.div h_anal (h_xi_ne z)
    exact h_ld.differentiableAt
  -- Step 2: primitive of `logDeriv xiOverP` on all of `ℂ`.
  obtain ⟨g₀, hg₀⟩ : ∃ g : ℂ → ℂ, ∀ z ∈ (Set.univ : Set ℂ),
      HasDerivAt g (logDeriv xiOverP z) z :=
    h_log_diff.isExactOn_univ
  set g : ℂ → ℂ := fun z => g₀ z + (Complex.log (xiOverP 0) - g₀ 0) with hg_def
  have hg_deriv : ∀ z, HasDerivAt g (logDeriv xiOverP z) z := by
    intro z
    have h₀ := hg₀ z (Set.mem_univ z)
    simpa [hg_def] using h₀.add_const (Complex.log (xiOverP 0) - g₀ 0)
  have hg_diff : Differentiable ℂ g := fun z => (hg_deriv z).differentiableAt
  have hg_deriv_eq : ∀ z, deriv g z = logDeriv xiOverP z :=
    fun z => (hg_deriv z).deriv
  have hg0 : g 0 = Complex.log (xiOverP 0) := by simp [hg_def]
  -- Step 3: `exp ∘ g = xiOverP`.
  set φ : ℂ → ℂ := fun z => Complex.exp (g z) / xiOverP z with hφ_def
  have hφ_deriv_zero : ∀ z, deriv φ z = 0 := by
    intro z
    have h_exp_g_deriv : HasDerivAt (fun w => Complex.exp (g w))
        (Complex.exp (g z) * logDeriv xiOverP z) z := by
      have := (hg_deriv z).cexp
      simpa using this
    have h_xi_deriv : HasDerivAt xiOverP (deriv xiOverP z) z :=
      (xiOverP_differentiable z).hasDerivAt
    have h_div : HasDerivAt φ
        ((Complex.exp (g z) * logDeriv xiOverP z * xiOverP z -
          Complex.exp (g z) * deriv xiOverP z) / (xiOverP z)^2) z :=
      h_exp_g_deriv.div h_xi_deriv (h_xi_ne z)
    have h_num_zero :
        Complex.exp (g z) * logDeriv xiOverP z * xiOverP z -
          Complex.exp (g z) * deriv xiOverP z = 0 := by
      have h_eq : logDeriv xiOverP z * xiOverP z = deriv xiOverP z := by
        rw [logDeriv_apply, div_mul_cancel₀ _ (h_xi_ne z)]
      calc Complex.exp (g z) * logDeriv xiOverP z * xiOverP z -
            Complex.exp (g z) * deriv xiOverP z
          = Complex.exp (g z) * (logDeriv xiOverP z * xiOverP z) -
              Complex.exp (g z) * deriv xiOverP z := by ring
        _ = Complex.exp (g z) * deriv xiOverP z -
              Complex.exp (g z) * deriv xiOverP z := by rw [h_eq]
        _ = 0 := sub_self _
    rw [h_div.deriv, h_num_zero, zero_div]
  have hφ_diff : Differentiable ℂ φ := by
    intro z
    have h_exp_g_diff : DifferentiableAt ℂ (fun w => Complex.exp (g w)) z :=
      (hg_diff z).cexp
    exact h_exp_g_diff.div (xiOverP_differentiable z) (h_xi_ne z)
  have hφ_const : ∀ z, φ z = φ 0 :=
    fun z => is_const_of_deriv_eq_zero hφ_diff hφ_deriv_zero z 0
  have hφ0 : φ 0 = 1 := by
    show Complex.exp (g 0) / xiOverP 0 = 1
    rw [hg0, Complex.exp_log (h_xi_ne 0)]
    exact div_self (h_xi_ne 0)
  have h_exp_g_eq : ∀ z, Complex.exp (g z) = xiOverP z := by
    intro z
    have hφz : Complex.exp (g z) / xiOverP z = 1 := by
      rw [show Complex.exp (g z) / xiOverP z = φ z from rfl, hφ_const z, hφ0]
    have := (div_eq_one_iff_eq (h_xi_ne z)).mp hφz
    exact this
  -- Step 4: mean-type bound on `(g z).re`.
  have h_g_re_bd : ∀ z, (g z).re ≤ C * ‖z‖ * Real.log (‖z‖ + 2) + D := by
    intro z
    have h1 : Real.exp ((g z).re) = ‖xiOverP z‖ := by
      rw [← h_exp_g_eq z, Complex.norm_exp]
    have h2 : Real.exp ((g z).re) ≤ Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2) + D) := by
      rw [h1]; exact hG z
    exact (Real.exp_le_exp.mp h2)
  -- Step 5: shift to `h` with `h 0 = 0`, extract mean-type real-part bound.
  set h : ℂ → ℂ := fun z => g z - g 0 with hh_def
  have hh_diff : Differentiable ℂ h := hg_diff.sub_const _
  have hh_deriv : ∀ z, deriv h z = logDeriv xiOverP z := by
    intro z
    have : deriv h z = deriv g z := by
      simp [hh_def, deriv_sub_const]
    rw [this, hg_deriv_eq]
  have hh0 : h 0 = 0 := by simp [hh_def]
  -- Mean-type real-part bound on `h`: `(h z).re ≤ A' + B' * ‖z‖ * log(‖z‖+2)`
  -- with `A' := max 0 (D - (g 0).re) ≥ 0` and `B' := max C 0 ≥ 0`.
  set A' : ℝ := max 0 (D - (g 0).re) with hA'_def
  set B' : ℝ := max C 0 with hB'_def
  have hA'_nn : 0 ≤ A' := le_max_left _ _
  have hB'_nn : 0 ≤ B' := le_max_right _ _
  have h_h_growth : ∀ z, (h z).re ≤ A' + B' * ‖z‖ * Real.log (‖z‖ + 2) := by
    intro z
    have h_nz : 0 ≤ ‖z‖ := norm_nonneg _
    have h_log_nn : 0 ≤ Real.log (‖z‖ + 2) := Real.log_nonneg (by linarith)
    have h_gz := h_g_re_bd z
    have h_hre : (h z).re = (g z).re - (g 0).re := by
      simp [hh_def, Complex.sub_re]
    have h_C_le : C * ‖z‖ * Real.log (‖z‖ + 2) ≤ B' * ‖z‖ * Real.log (‖z‖ + 2) := by
      apply mul_le_mul_of_nonneg_right _ h_log_nn
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) h_nz
    have h_D_le : D - (g 0).re ≤ A' := le_max_right _ _
    rw [h_hre]
    linarith
  -- Step 6: second iterated derivative of `h` is identically zero.
  have h_iter2_zero : ∀ z₀, iteratedDeriv 2 h z₀ = 0 :=
    secondDeriv_zero_of_meanType hh_diff hh0 hA'_nn hB'_nn h_h_growth
  -- Step 7: `deriv h = logDeriv xiOverP` is globally constant.
  -- `deriv (deriv h) z = iteratedDeriv 2 h z = 0`, and `deriv h` is
  -- differentiable since `deriv h = logDeriv xiOverP`.
  have h_deriv_deriv_zero : ∀ z, deriv (deriv h) z = 0 := by
    intro z
    have := h_iter2_zero z
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  have h_deriv_diff : Differentiable ℂ (deriv h) := by
    have : deriv h = logDeriv xiOverP := funext hh_deriv
    rw [this]; exact h_log_diff
  have h_deriv_const : ∀ z, deriv h z = deriv h 0 := by
    intro z
    exact is_const_of_deriv_eq_zero h_deriv_diff h_deriv_deriv_zero z 0
  refine ⟨logDeriv xiOverP 0, ?_⟩
  intro z
  have := h_deriv_const z
  rw [hh_deriv z, hh_deriv 0] at this
  exact this

/-- **Final chain theorem.** Mean-type growth of `xiOverP` ⇒ partial-fraction
identity for `ξ'/ξ` on a zero-free open patch. -/
theorem xi_logDeriv_partial_fraction_on_open_of_xiOverP_growth
    (hG : ∃ C D : ℝ, ∀ z : ℂ,
      ‖xiOverP z‖ ≤ Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2) + D)) :
    ∃ U : Set ℂ,
      IsOpen U ∧ U.Nonempty ∧ U ⊆ ((NontrivialZeros : Set ℂ)ᶜ) ∧
      ∃ A : ℂ, ∀ s : ℂ, s ∈ U →
        deriv riemannXi s / riemannXi s =
          A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val) :=
  xi_logDeriv_partial_fraction_on_open_of_logDeriv_xiOverP_const
    (logDeriv_xiOverP_const_of_growth hG)

-- ═══════════════════════════════════════════════════════════════════════════
-- § `log²` variant: generalized mean-type helper (Cauchy at order 2 works
--    for any sub-quadratic growth on Re g, in particular `log²`)
-- ═══════════════════════════════════════════════════════════════════════════

/-- `log²` variant of `tendsto_meanType_ratio_zero`.  The `(log R)² / R → 0`
tends to zero even more slowly than `log R / R`; the proof generalizes
trivially by substitution. -/
private theorem tendsto_meanType_ratio_zero_logSq {A B nz : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hnz : 0 ≤ nz) :
    Filter.Tendsto
      (fun R : ℝ =>
        32 * (1 + A + B * R * (Real.log (R + 2)) ^ 2) / (R - nz) ^ 2)
      Filter.atTop (nhds 0) := by
  have h_maj_tend : Filter.Tendsto
      (fun R : ℝ => 128 * (1 + A) / R^2 + 512 * B * (Real.log R) ^ 2 / R)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun R : ℝ => 128 * (1 + A) / R^2)
        Filter.atTop (nhds 0) := by
      have hone : Filter.Tendsto (fun R : ℝ => 1 / R^2) Filter.atTop (nhds 0) := by
        have h := @tendsto_pow_neg_atTop ℝ _ _ _ _ _ 2 (by norm_num)
        refine h.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with R _
        rw [zpow_neg, zpow_natCast, inv_eq_one_div]
      have := hone.const_mul (128 * (1 + A))
      simp at this
      refine this.congr' ?_
      filter_upwards with R; ring
    have h2 : Filter.Tendsto (fun R : ℝ => 512 * B * (Real.log R) ^ 2 / R)
        Filter.atTop (nhds 0) := by
      have hlog : Filter.Tendsto (fun R : ℝ => (Real.log R) ^ 2 / R)
          Filter.atTop (nhds 0) := by
        have := Real.tendsto_pow_log_div_mul_add_atTop
          (a := (1:ℝ)) (b := 0) (n := 2) (by norm_num)
        simpa using this
      have := hlog.const_mul (512 * B)
      simp at this
      refine this.congr' ?_
      filter_upwards with R; ring
    simpa using h1.add h2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_maj_tend
  · filter_upwards [Filter.eventually_ge_atTop (max 2 (2*nz+1))] with R hR
    apply div_nonneg _ (sq_nonneg _)
    have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
    have h_log_Rplus : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
    have h_log_Rplus_sq : 0 ≤ (Real.log (R + 2)) ^ 2 := sq_nonneg _
    have : 0 ≤ B * R * (Real.log (R + 2)) ^ 2 :=
      mul_nonneg (mul_nonneg hB (by linarith)) h_log_Rplus_sq
    linarith
  · filter_upwards [Filter.eventually_ge_atTop (max 2 (2*nz+1))] with R hR
    have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
    have hR_nz : 2 * nz + 1 ≤ R := le_trans (le_max_right _ _) hR
    have hR_pos : 0 < R := by linarith
    have hR_gt_nz : R > nz := by linarith
    have hR_sub_pos : 0 < R - nz := by linarith
    have h_log_R : 0 < Real.log R := Real.log_pos (by linarith)
    have h_log_Rplus : 0 < Real.log (R + 2) := Real.log_pos (by linarith)
    have h_rmnz_ge : R - nz ≥ R / 2 := by linarith
    have h_sq_bd : (R - nz) ^ 2 ≥ (R / 2) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h_rmnz_ge 2
    have h_denom_bd : (R - nz) ^ 2 ≥ R^2 / 4 := by nlinarith [h_sq_bd]
    have h_log_bd : Real.log (R + 2) ≤ 2 * Real.log R := by
      have h1 : R + 2 ≤ 2 * R := by linarith
      have h2 : Real.log (R + 2) ≤ Real.log (2 * R) :=
        Real.log_le_log (by linarith) h1
      have h3 : Real.log (2 * R) = Real.log 2 + Real.log R :=
        Real.log_mul (by norm_num) (by linarith)
      have h4 : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR2
      linarith
    have h_log_sq_bd : (Real.log (R + 2)) ^ 2 ≤ 4 * (Real.log R) ^ 2 := by
      have h_log_plus_nn : 0 ≤ Real.log (R + 2) := le_of_lt h_log_Rplus
      have h_two_log_nn : 0 ≤ 2 * Real.log R := by linarith
      have : (Real.log (R + 2)) ^ 2 ≤ (2 * Real.log R) ^ 2 :=
        pow_le_pow_left₀ h_log_plus_nn h_log_bd 2
      calc (Real.log (R + 2)) ^ 2 ≤ (2 * Real.log R) ^ 2 := this
        _ = 4 * (Real.log R) ^ 2 := by ring
    have h_num : 1 + A + B * R * (Real.log (R + 2)) ^ 2 ≤
        1 + A + 4 * B * R * (Real.log R) ^ 2 := by
      have : B * R * (Real.log (R + 2)) ^ 2 ≤ B * R * (4 * (Real.log R) ^ 2) := by
        apply mul_le_mul_of_nonneg_left h_log_sq_bd
        exact mul_nonneg hB (by linarith)
      linarith
    have h_num'_nn : 0 ≤ 1 + A + 4 * B * R * (Real.log R) ^ 2 := by
      have hlog_sq_nn : 0 ≤ (Real.log R) ^ 2 := sq_nonneg _
      have : 0 ≤ 4 * B * R * (Real.log R) ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) (by linarith))
          hlog_sq_nn
      linarith
    have h_step1 : 32 * (1 + A + B * R * (Real.log (R + 2)) ^ 2) / (R - nz) ^ 2 ≤
        32 * (1 + A + 4 * B * R * (Real.log R) ^ 2) / (R - nz) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have h_step2 : 32 * (1 + A + 4 * B * R * (Real.log R) ^ 2) / (R - nz) ^ 2 ≤
        32 * (1 + A + 4 * B * R * (Real.log R) ^ 2) / (R^2/4) := by
      apply div_le_div₀ _ (le_refl _) (by positivity) h_denom_bd
      linarith
    have h_step3 : 32 * (1 + A + 4 * B * R * (Real.log R) ^ 2) / (R^2/4) =
        128 * (1 + A) / R^2 + 512 * B * (Real.log R) ^ 2 / R := by
      have hRne : R ≠ 0 := ne_of_gt hR_pos
      field_simp
      ring
    linarith [h_step1, h_step2, h_step3]

/-- `log²` variant of `iteratedDeriv2_bound_of_meanType`. -/
private theorem iteratedDeriv2_bound_of_meanType_logSq
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 = 0)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrowth : ∀ z : ℂ, (f z).re ≤ A + B * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2)
    (z₀ : ℂ) (R : ℝ) (hR : 3 * (‖z₀‖ + 1) ≤ R) :
    ‖iteratedDeriv 2 f z₀‖ ≤
      32 * (1 + A + B * R * (Real.log (R + 2)) ^ 2) / (R - ‖z₀‖) ^ 2 := by
  set nz : ℝ := ‖z₀‖ with hnz_def
  have hnz_nn : 0 ≤ nz := norm_nonneg _
  have hR_pos : 0 < R := by linarith
  have hR_gt_nz : nz + 1 < R := by linarith
  set r : ℝ := (R - nz) / 2 with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; linarith
  have hr_ge_one : 1 ≤ r := by rw [hr_def]; linarith
  set M : ℝ := 1 + A + B * R * (Real.log (R + 2)) ^ 2 with hM_def
  have hlog_nn : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hlog_sq_nn : 0 ≤ (Real.log (R + 2)) ^ 2 := sq_nonneg _
  have hM_pos : 0 < M := by
    rw [hM_def]
    have : 0 ≤ B * R * (Real.log (R + 2)) ^ 2 :=
      mul_nonneg (mul_nonneg hB hR_pos.le) hlog_sq_nn
    linarith
  have hz₀_in_ball : z₀ ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hf_diff_on : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R) :=
    hf.differentiableOn
  have hf_maps : Set.MapsTo f (Metric.ball (0 : ℂ) R) {w : ℂ | w.re ≤ M} := by
    intro w hw
    have hw_norm : ‖w‖ < R := by
      rw [Metric.mem_ball, dist_zero_right] at hw; exact hw
    have hgw : (f w).re ≤ A + B * ‖w‖ * (Real.log (‖w‖ + 2)) ^ 2 := hgrowth w
    have h_mono : B * ‖w‖ * (Real.log (‖w‖ + 2)) ^ 2 ≤
        B * R * (Real.log (R + 2)) ^ 2 := by
      have hwnn : 0 ≤ ‖w‖ := norm_nonneg _
      have h1 : B * ‖w‖ ≤ B * R := mul_le_mul_of_nonneg_left hw_norm.le hB
      have h2 : Real.log (‖w‖ + 2) ≤ Real.log (R + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      have h3 : 0 ≤ Real.log (‖w‖ + 2) := Real.log_nonneg (by linarith)
      have h4 : (Real.log (‖w‖ + 2)) ^ 2 ≤ (Real.log (R + 2)) ^ 2 :=
        pow_le_pow_left₀ h3 h2 2
      have h5 : 0 ≤ (Real.log (‖w‖ + 2)) ^ 2 := sq_nonneg _
      calc B * ‖w‖ * (Real.log (‖w‖ + 2)) ^ 2
          ≤ B * R * (Real.log (‖w‖ + 2)) ^ 2 := mul_le_mul_of_nonneg_right h1 h5
        _ ≤ B * R * (Real.log (R + 2)) ^ 2 :=
            mul_le_mul_of_nonneg_left h4 (mul_nonneg hB hR_pos.le)
    show (f w).re ≤ M
    rw [hM_def]; linarith
  have hBC : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) :=
    fun z hz => Complex.borelCaratheodory_zero hM_pos hf_diff_on hf_maps hR_pos hz hf0
  have h_sphere_bd : ∀ w ∈ Metric.sphere z₀ r, ‖f w‖ ≤ 4 * M := by
    intro w hw
    have hw_dist : ‖w - z₀‖ = r := by rw [← dist_eq_norm]; exact hw
    have hw_norm_le : ‖w‖ ≤ nz + r := by
      calc ‖w‖ = ‖(w - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ = r + nz := by rw [hw_dist]
        _ = nz + r := by ring
    have hw_in_ball : w ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right]
      have h1 : nz + r = nz + (R - nz) / 2 := by rw [hr_def]
      have h2 : nz + (R - nz) / 2 < R := by linarith
      calc ‖w‖ ≤ nz + r := hw_norm_le
        _ < R := by rw [h1]; exact h2
    have hR_sub_w : r ≤ R - ‖w‖ := by
      have h1 : ‖w‖ ≤ nz + r := hw_norm_le
      have h2 : R - (nz + r) = r := by rw [hr_def]; ring
      linarith
    have hR_sub_pos : 0 < R - ‖w‖ := by linarith
    have hBCw := hBC w hw_in_ball
    have hr_ge_nz : nz ≤ r := by rw [hr_def]; linarith
    have hw_nn : 0 ≤ ‖w‖ := norm_nonneg _
    have h_nzr_nn : 0 ≤ nz + r := by linarith
    have h_step1 : 2 * M * ‖w‖ / (R - ‖w‖) ≤ 2 * M * (nz + r) / r := by
      apply div_le_div₀ _ _ hr_pos hR_sub_w
      · exact mul_nonneg (by linarith [hM_pos]) h_nzr_nn
      · exact mul_le_mul_of_nonneg_left hw_norm_le (by linarith [hM_pos])
    have h_step2 : 2 * M * (nz + r) / r ≤ 4 * M := by
      rw [div_le_iff₀ hr_pos]
      have h : nz + r ≤ 2 * r := by linarith
      calc 2 * M * (nz + r) ≤ 2 * M * (2 * r) :=
            mul_le_mul_of_nonneg_left h (by linarith [hM_pos])
        _ = 4 * M * r := by ring
    linarith [hBCw]
  have h_dcc : DiffContOnCl ℂ f (Metric.ball z₀ r) := hf.diffContOnCl
  have hcauchy : ‖iteratedDeriv 2 f z₀‖ ≤ (2 : ℕ).factorial * (4 * M) / r ^ 2 :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hr_pos h_dcc
      h_sphere_bd
  have h_fact2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num
  rw [h_fact2] at hcauchy
  have hr2 : r ^ 2 = (R - nz) ^ 2 / 4 := by rw [hr_def]; ring
  rw [hr2] at hcauchy
  have hfinal : 2 * (4 * M) / ((R - nz) ^ 2 / 4) = 32 * M / (R - nz) ^ 2 := by
    have hRnz_pos : 0 < R - nz := by linarith
    have : (R - nz) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hfinal] at hcauchy
  show ‖iteratedDeriv 2 f z₀‖ ≤ 32 * M / (R - nz) ^ 2
  exact hcauchy

/-- `log²` variant of `secondDeriv_zero_of_meanType`. -/
private theorem secondDeriv_zero_of_meanType_logSq
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 = 0)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrowth : ∀ z : ℂ, (f z).re ≤ A + B * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2) :
    ∀ z₀ : ℂ, iteratedDeriv 2 f z₀ = 0 := by
  intro z₀
  have hnz_nn : 0 ≤ ‖z₀‖ := norm_nonneg _
  have h_bound : ∀ R : ℝ, 3 * (‖z₀‖ + 1) ≤ R →
      ‖iteratedDeriv 2 f z₀‖ ≤
        32 * (1 + A + B * R * (Real.log (R + 2)) ^ 2) / (R - ‖z₀‖) ^ 2 :=
    fun R hR => iteratedDeriv2_bound_of_meanType_logSq hf hf0 hA hB hgrowth z₀ R hR
  have h_tend : Filter.Tendsto
      (fun R : ℝ =>
        32 * (1 + A + B * R * (Real.log (R + 2)) ^ 2) / (R - ‖z₀‖) ^ 2)
      Filter.atTop (nhds 0) := tendsto_meanType_ratio_zero_logSq hA hB hnz_nn
  have h_le_zero : ‖iteratedDeriv 2 f z₀‖ ≤ 0 :=
    ge_of_tendsto h_tend (Filter.eventually_atTop.mpr ⟨3 * (‖z₀‖ + 1), h_bound⟩)
  exact norm_le_zero_iff.mp h_le_zero

/-- `log²` variant of `logDeriv_xiOverP_const_of_growth`.  Consumes the weaker
mean-type-2 hypothesis `‖xiOverP z‖ ≤ exp(C ‖z‖ log²(‖z‖+2) + D)` which is
what the `Jensen + Nevanlinna + Poisson` chain in `XiOverPGrowth` naturally
produces.  The proof mirrors the `log`-version; only the growth exponent of
the majorant in `secondDeriv_zero_of_meanType_logSq` changes. -/
theorem logDeriv_xiOverP_const_of_logSqGrowth
    (hG : ∃ C D : ℝ, ∀ z : ℂ,
      ‖xiOverP z‖ ≤ Real.exp (C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D)) :
    ∃ A : ℂ, ∀ z : ℂ, logDeriv xiOverP z = A := by
  obtain ⟨C, D, hG⟩ := hG
  -- Step 1: `logDeriv xiOverP` is entire.
  have h_xi_ne : ∀ z, xiOverP z ≠ 0 := xiOverP_ne_zero
  have h_log_diff : Differentiable ℂ (logDeriv xiOverP) := by
    intro z
    have h_anal : AnalyticAt ℂ xiOverP z := xiOverP_analyticAt z
    have h_deriv_anal : AnalyticAt ℂ (deriv xiOverP) z := h_anal.deriv
    have h_ld : AnalyticAt ℂ (logDeriv xiOverP) z := by
      simpa [logDeriv] using h_deriv_anal.div h_anal (h_xi_ne z)
    exact h_ld.differentiableAt
  -- Step 2: primitive of `logDeriv xiOverP` on all of `ℂ`.
  obtain ⟨g₀, hg₀⟩ : ∃ g : ℂ → ℂ, ∀ z ∈ (Set.univ : Set ℂ),
      HasDerivAt g (logDeriv xiOverP z) z :=
    h_log_diff.isExactOn_univ
  set g : ℂ → ℂ := fun z => g₀ z + (Complex.log (xiOverP 0) - g₀ 0) with hg_def
  have hg_deriv : ∀ z, HasDerivAt g (logDeriv xiOverP z) z := by
    intro z
    have h₀ := hg₀ z (Set.mem_univ z)
    simpa [hg_def] using h₀.add_const (Complex.log (xiOverP 0) - g₀ 0)
  have hg_diff : Differentiable ℂ g := fun z => (hg_deriv z).differentiableAt
  have hg_deriv_eq : ∀ z, deriv g z = logDeriv xiOverP z :=
    fun z => (hg_deriv z).deriv
  have hg0 : g 0 = Complex.log (xiOverP 0) := by simp [hg_def]
  -- Step 3: `exp ∘ g = xiOverP`.
  set φ : ℂ → ℂ := fun z => Complex.exp (g z) / xiOverP z with hφ_def
  have hφ_deriv_zero : ∀ z, deriv φ z = 0 := by
    intro z
    have h_exp_g_deriv : HasDerivAt (fun w => Complex.exp (g w))
        (Complex.exp (g z) * logDeriv xiOverP z) z := by
      have := (hg_deriv z).cexp
      simpa using this
    have h_xi_deriv : HasDerivAt xiOverP (deriv xiOverP z) z :=
      (xiOverP_differentiable z).hasDerivAt
    have h_div : HasDerivAt φ
        ((Complex.exp (g z) * logDeriv xiOverP z * xiOverP z -
          Complex.exp (g z) * deriv xiOverP z) / (xiOverP z)^2) z :=
      h_exp_g_deriv.div h_xi_deriv (h_xi_ne z)
    have h_num_zero :
        Complex.exp (g z) * logDeriv xiOverP z * xiOverP z -
          Complex.exp (g z) * deriv xiOverP z = 0 := by
      have h_eq : logDeriv xiOverP z * xiOverP z = deriv xiOverP z := by
        rw [logDeriv_apply, div_mul_cancel₀ _ (h_xi_ne z)]
      calc Complex.exp (g z) * logDeriv xiOverP z * xiOverP z -
            Complex.exp (g z) * deriv xiOverP z
          = Complex.exp (g z) * (logDeriv xiOverP z * xiOverP z) -
              Complex.exp (g z) * deriv xiOverP z := by ring
        _ = Complex.exp (g z) * deriv xiOverP z -
              Complex.exp (g z) * deriv xiOverP z := by rw [h_eq]
        _ = 0 := sub_self _
    rw [h_div.deriv, h_num_zero, zero_div]
  have hφ_diff : Differentiable ℂ φ := by
    intro z
    have h_exp_g_diff : DifferentiableAt ℂ (fun w => Complex.exp (g w)) z :=
      (hg_diff z).cexp
    exact h_exp_g_diff.div (xiOverP_differentiable z) (h_xi_ne z)
  have hφ_const : ∀ z, φ z = φ 0 :=
    fun z => is_const_of_deriv_eq_zero hφ_diff hφ_deriv_zero z 0
  have hφ0 : φ 0 = 1 := by
    show Complex.exp (g 0) / xiOverP 0 = 1
    rw [hg0, Complex.exp_log (h_xi_ne 0)]
    exact div_self (h_xi_ne 0)
  have h_exp_g_eq : ∀ z, Complex.exp (g z) = xiOverP z := by
    intro z
    have hφz : Complex.exp (g z) / xiOverP z = 1 := by
      rw [show Complex.exp (g z) / xiOverP z = φ z from rfl, hφ_const z, hφ0]
    have := (div_eq_one_iff_eq (h_xi_ne z)).mp hφz
    exact this
  -- Step 4: mean-type-log² bound on `(g z).re`.
  have h_g_re_bd : ∀ z, (g z).re ≤ C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D := by
    intro z
    have h1 : Real.exp ((g z).re) = ‖xiOverP z‖ := by
      rw [← h_exp_g_eq z, Complex.norm_exp]
    have h2 : Real.exp ((g z).re) ≤
        Real.exp (C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 + D) := by
      rw [h1]; exact hG z
    exact (Real.exp_le_exp.mp h2)
  -- Step 5: shift to `h` with `h 0 = 0`, extract mean-type-log² real-part bound.
  set h : ℂ → ℂ := fun z => g z - g 0 with hh_def
  have hh_diff : Differentiable ℂ h := hg_diff.sub_const _
  have hh_deriv : ∀ z, deriv h z = logDeriv xiOverP z := by
    intro z
    have : deriv h z = deriv g z := by
      simp [hh_def, deriv_sub_const]
    rw [this, hg_deriv_eq]
  have hh0 : h 0 = 0 := by simp [hh_def]
  set A' : ℝ := max 0 (D - (g 0).re) with hA'_def
  set B' : ℝ := max C 0 with hB'_def
  have hA'_nn : 0 ≤ A' := le_max_left _ _
  have hB'_nn : 0 ≤ B' := le_max_right _ _
  have h_h_growth : ∀ z, (h z).re ≤ A' + B' * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 := by
    intro z
    have h_nz : 0 ≤ ‖z‖ := norm_nonneg _
    have h_log_nn : 0 ≤ Real.log (‖z‖ + 2) := Real.log_nonneg (by linarith)
    have h_log_sq_nn : 0 ≤ (Real.log (‖z‖ + 2)) ^ 2 := sq_nonneg _
    have h_gz := h_g_re_bd z
    have h_hre : (h z).re = (g z).re - (g 0).re := by
      simp [hh_def, Complex.sub_re]
    have h_C_le : C * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 ≤
        B' * ‖z‖ * (Real.log (‖z‖ + 2)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ h_log_sq_nn
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) h_nz
    have h_D_le : D - (g 0).re ≤ A' := le_max_right _ _
    rw [h_hre]
    linarith
  -- Step 6: second iterated derivative of `h` is identically zero.
  have h_iter2_zero : ∀ z₀, iteratedDeriv 2 h z₀ = 0 :=
    secondDeriv_zero_of_meanType_logSq hh_diff hh0 hA'_nn hB'_nn h_h_growth
  have h_deriv_deriv_zero : ∀ z, deriv (deriv h) z = 0 := by
    intro z
    have := h_iter2_zero z
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using this
  have h_deriv_diff : Differentiable ℂ (deriv h) := by
    have : deriv h = logDeriv xiOverP := funext hh_deriv
    rw [this]; exact h_log_diff
  have h_deriv_const : ∀ z, deriv h z = deriv h 0 := by
    intro z
    exact is_const_of_deriv_eq_zero h_deriv_diff h_deriv_deriv_zero z 0
  refine ⟨logDeriv xiOverP 0, ?_⟩
  intro z
  have := h_deriv_const z
  rw [hh_deriv z, hh_deriv 0] at this
  exact this

-- ═══════════════════════════════════════════════════════════════════════════
-- § UNCONDITIONAL wrappers (consume `XiOverPGrowth.xiOverP_growth_meanType`)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Unconditional** `logDeriv xiOverP` is globally constant.
Direct composition of `XiOverPGrowth.xiOverP_growth_meanType` (the
Jensen + Poisson chain) and `logDeriv_xiOverP_const_of_logSqGrowth`. -/
theorem logDeriv_xiOverP_const :
    ∃ A : ℂ, ∀ z : ℂ, logDeriv xiOverP z = A :=
  logDeriv_xiOverP_const_of_logSqGrowth xiOverP_growth_meanType

/-- **Unconditional** partial-fraction identity for `ξ'/ξ` on the zero-free
open complement. -/
theorem xi_logDeriv_partial_fraction_on_open :
    ∃ U : Set ℂ,
      IsOpen U ∧ U.Nonempty ∧ U ⊆ ((NontrivialZeros : Set ℂ)ᶜ) ∧
      ∃ A : ℂ, ∀ s : ℂ, s ∈ U →
        deriv riemannXi s / riemannXi s =
          A + ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
            (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val) :=
  xi_logDeriv_partial_fraction_on_open_of_logDeriv_xiOverP_const
    logDeriv_xiOverP_const

end ZD
end
