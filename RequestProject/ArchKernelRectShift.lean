import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Complex
import RequestProject.WeilContour
import RequestProject.WeilArchKernelResidues
import RequestProject.WeilPairTestMellinExtend
import RequestProject.WeilArchPrimeIdentity

/-!
# Per-residue computation for the arch-kernel rectangle shift on `pairTestMellin β`

The Form C reduction of H3 (`archEqPrimeSum_target β`) ultimately rests on a
rectangle Cauchy contour shift for the integrand
```
F(s) := archKernel s · pairTestMellin β s
```
applied over `[-1, 2] × [-T, T]` with `T → ∞`. The full closure splits into
four substantive pieces:

1. Analyticity of `F` on the strip `{-1 < Re s < 2}` minus the pole set
   `{0, 1}` (`archKernel` has simple poles at both; `pairTestMellin β` is
   holomorphic on `Re s > -4`).
2. Top/bottom edge vanishing as `T → ∞`.
3. Residue extraction at `s = 0` and `s = 1`.
4. Identification of `F(2 + iy)` with `archIntegrand β 2 y` and of
   `F(-1 + iy)` with `archIntegrand β (-1) y`.

This file delivers pieces (1) and (3) — the analytical infrastructure
the rectangle Cauchy proof consumes. Top/bottom decay via Stirling × IBP-
shifted M[d²] estimates and the assembly into the `2πi · (Res₀ + Res₁)`
identity compose externally.

## Main results

* `pairTestMellin_archKernel_product` — the product `F` as a `noncomputable
  def`.
* `pairTestMellin_archKernel_differentiableAt_off_poles` — `F` is
  differentiable on `{-1 < Re s < 2 ∧ s ≠ 0 ∧ s ≠ 1}`.
* `pairTestMellin_archKernel_residue_at_zero` — `lim_{s → 0, s ≠ 0} s · F(s)
  = -pairTestMellin β 0`.
* `pairTestMellin_archKernel_residue_at_one` — `lim_{s → 1, s ≠ 1}
  (s - 1) · F(s) = pairTestMellin β 1 = gaussianPairDefect β`.
* `pairTestMellin_archKernel_continuousAt_neg_one` — `F` is continuous at
  every point of the line `Re s = -1` (no pole).

All proofs are axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`).
-/

noncomputable section

open Filter Topology Complex MeasureTheory Set
open scoped Real

namespace ZD.ArchKernelRectShift

open ZD.WeilArchKernelResidues ZD.WeilPositivity.Contour

/-! ## The product integrand -/

/-- The IBP-shifted-form arch integrand as a single function of `s`.

By definition this equals `arch_factor(s) · pairTestMellin β s`. Restricted
to `s = σ + iy` it agrees with `archIntegrand β σ y`. -/
def pairTestMellin_archKernel_product (β : ℝ) (s : ℂ) : ℂ :=
  archKernel s * pairTestMellin β s

local notation "F" => pairTestMellin_archKernel_product

/-! ## Differentiability on the strip minus the pole set `{0, 1}` -/

/-- `Γℝ` does not vanish on the open strip `-1 < Re s < 2` away from `s = 0`.
The only zero of `Γℝ` in `Re s > -1` would be a non-positive even integer
`-2k`, and `-1 < -2k` forces `k = 0`, i.e. `s = 0`. -/
private lemma Gammaℝ_ne_zero_on_strip_off_zero
    {s : ℂ} (hs_re : -1 < s.re) (hs_ne : s ≠ 0) : Complex.Gammaℝ s ≠ 0 := by
  intro hzero
  rcases Complex.Gammaℝ_eq_zero_iff.mp hzero with ⟨n, hn⟩
  -- s = -2n in ℂ. Look at real parts.
  have hre : s.re = -(2 * (n : ℝ)) := by
    have h := congrArg Complex.re hn
    simp at h
    linarith
  rw [hre] at hs_re
  -- -1 < -(2n), so 2n < 1. Combined with `(n : ℝ) ≥ 0`, this forces `n = 0`.
  have hn_lt : (2 * (n : ℝ)) < 1 := by linarith
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn_lt_one : (n : ℝ) < 1 := by linarith
  have hn_int_lt : n < 1 := by exact_mod_cast hn_lt_one
  have hn_zero : n = 0 := Nat.lt_one_iff.mp hn_int_lt
  apply hs_ne
  rw [hn]
  simp [hn_zero]

/-- Similarly, `Γℝ(1 - s)` is nonzero on the strip `-1 < Re s < 2` away from
`s = 1`. Reduces to the previous lemma with `s ↦ 1 - s` (re flips: -1 < Re s
becomes Re(1-s) < 2; Re s < 2 becomes -1 < Re(1-s); s = 1 ↔ 1 - s = 0). -/
private lemma Gammaℝ_one_sub_ne_zero_on_strip_off_one
    {s : ℂ} (hs_re_lt : s.re < 2) (hs_ne : s ≠ 1) :
    (1 - s).Gammaℝ ≠ 0 := by
  apply Gammaℝ_ne_zero_on_strip_off_zero
  · -- Re(1 - s) = 1 - Re s > 1 - 2 = -1
    simp; linarith
  · -- 1 - s ≠ 0, since s ≠ 1
    intro h
    apply hs_ne
    have : s = 1 - (1 - s) := by ring
    rw [this, h]; ring

/-- `archKernel` is differentiable at every point of the strip
`-1 < Re s < 2` away from `s = 0` and `s = 1`. -/
theorem archKernel_differentiableAt_on_strip_off_poles
    {s : ℂ} (hs_re_l : -1 < s.re) (hs_re_r : s.re < 2)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ archKernel s := by
  unfold archKernel
  have hΓs_ne : Complex.Gammaℝ s ≠ 0 :=
    Gammaℝ_ne_zero_on_strip_off_zero hs_re_l hs0
  have hΓ1s_ne : (1 - s).Gammaℝ ≠ 0 :=
    Gammaℝ_one_sub_ne_zero_on_strip_off_one hs_re_r hs1
  -- archKernel = Γℝ'/Γℝ + Γℝ'/Γℝ ∘ (1 - ·)
  have hΓ_diff_s : DifferentiableAt ℂ Complex.Gammaℝ s :=
    differentiableAt_Gammaℝ_of_ne_zero hΓs_ne
  have hΓ_diff_1s : DifferentiableAt ℂ Complex.Gammaℝ (1 - s) :=
    differentiableAt_Gammaℝ_of_ne_zero hΓ1s_ne
  -- The derivative `deriv Complex.Gammaℝ` is differentiable on `{Γℝ ≠ 0}`.
  -- Use Gammaℝ_analyticOnNhd from WeilArchKernelResidues style:
  -- `deriv Γℝ` is analytic where `Γℝ ≠ 0`, hence differentiable there.
  have hdΓs_diff : DifferentiableAt ℂ (deriv Complex.Gammaℝ) s := by
    -- Build via AnalyticOnNhd of deriv on the open set {Γℝ ≠ 0}.
    have h_open : IsOpen {z : ℂ | z.Gammaℝ ≠ 0} := by
      have h_cont : Continuous (fun z : ℂ => z.Gammaℝ⁻¹) :=
        Complex.differentiable_Gammaℝ_inv.continuous
      have h_eq : {z : ℂ | z.Gammaℝ ≠ 0} =
          (fun z : ℂ => z.Gammaℝ⁻¹) ⁻¹' {w : ℂ | w ≠ 0} := by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_preimage]
        refine ⟨inv_ne_zero, fun h hs => ?_⟩
        apply h; rw [hs, inv_zero]
      rw [h_eq]
      exact IsOpen.preimage h_cont isOpen_ne
    have hΓ_analytic : AnalyticOnNhd ℂ Complex.Gammaℝ {z : ℂ | z.Gammaℝ ≠ 0} := by
      apply DifferentiableOn.analyticOnNhd
      · intro z hz
        exact (differentiableAt_Gammaℝ_of_ne_zero hz).differentiableWithinAt
      · exact h_open
    exact (hΓ_analytic.deriv s hΓs_ne).differentiableAt
  have hdΓ1s_diff : DifferentiableAt ℂ (deriv Complex.Gammaℝ) (1 - s) := by
    have h_open : IsOpen {z : ℂ | z.Gammaℝ ≠ 0} := by
      have h_cont : Continuous (fun z : ℂ => z.Gammaℝ⁻¹) :=
        Complex.differentiable_Gammaℝ_inv.continuous
      have h_eq : {z : ℂ | z.Gammaℝ ≠ 0} =
          (fun z : ℂ => z.Gammaℝ⁻¹) ⁻¹' {w : ℂ | w ≠ 0} := by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_preimage]
        refine ⟨inv_ne_zero, fun h hs => ?_⟩
        apply h; rw [hs, inv_zero]
      rw [h_eq]
      exact IsOpen.preimage h_cont isOpen_ne
    have hΓ_analytic : AnalyticOnNhd ℂ Complex.Gammaℝ {z : ℂ | z.Gammaℝ ≠ 0} := by
      apply DifferentiableOn.analyticOnNhd
      · intro z hz
        exact (differentiableAt_Gammaℝ_of_ne_zero hz).differentiableWithinAt
      · exact h_open
    exact (hΓ_analytic.deriv (1 - s) hΓ1s_ne).differentiableAt
  -- Composition with `1 - ·` for the second term.
  have h_sub : DifferentiableAt ℂ (fun z : ℂ => (1 : ℂ) - z) s :=
    (differentiableAt_const _).sub differentiableAt_id
  have hdΓ1s_comp :
      DifferentiableAt ℂ (fun z : ℂ => deriv Complex.Gammaℝ (1 - z)) s :=
    hdΓ1s_diff.comp s h_sub
  have hΓ1s_comp :
      DifferentiableAt ℂ (fun z : ℂ => Complex.Gammaℝ (1 - z)) s :=
    hΓ_diff_1s.comp s h_sub
  -- Quotients (denominators nonzero), then sum.
  have hquot1 :
      DifferentiableAt ℂ (fun z : ℂ => deriv Complex.Gammaℝ z / z.Gammaℝ) s :=
    hdΓs_diff.div hΓ_diff_s hΓs_ne
  have hquot2 :
      DifferentiableAt ℂ (fun z : ℂ => deriv Complex.Gammaℝ (1 - z) /
        (1 - z).Gammaℝ) s :=
    hdΓ1s_comp.div hΓ1s_comp hΓ1s_ne
  exact hquot1.add hquot2

/-- `pairTestMellin_archKernel_product β` is differentiable at every `s` in
the punctured strip `-1 < Re s < 2`, `s ≠ 0`, `s ≠ 1`. -/
theorem pairTestMellin_archKernel_differentiableAt_off_poles
    (β : ℝ) {s : ℂ} (hs_re_l : -1 < s.re) (hs_re_r : s.re < 2)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (F β) s := by
  unfold pairTestMellin_archKernel_product
  have hK := archKernel_differentiableAt_on_strip_off_poles hs_re_l hs_re_r hs0 hs1
  have hM : DifferentiableAt ℂ (pairTestMellin β) s := by
    apply pairTestMellin_differentiableAt_re_gt_neg_four
    linarith
  exact hK.mul hM

/-! ## Continuity of `pairTestMellin β` (used at the residue limits) -/

private lemma pairTestMellin_continuousAt (β : ℝ) {s : ℂ} (hs : -4 < s.re) :
    ContinuousAt (pairTestMellin β) s :=
  (pairTestMellin_differentiableAt_re_gt_neg_four β hs).continuousAt

/-! ## Residue at `s = 0` -/

/-- **Residue at `s = 0`**:
```
lim_{s → 0, s ≠ 0} s · F(s) = -pairTestMellin β 0.
```

Proof: `s · F(s) = (s · archKernel s) · pairTestMellin β s`. The first factor
tends to `-1` by `archKernel_residue_at_zero`; the second is continuous at `0`
since `pairTestMellin β` is differentiable on `Re s > -4`. -/
theorem pairTestMellin_archKernel_residue_at_zero (β : ℝ) :
    Filter.Tendsto (fun s : ℂ => s * F β s)
      (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds (-pairTestMellin β 0)) := by
  -- Decompose: s · F(s) = (s · archKernel s) · pairTestMellin β s.
  have h_arch : Filter.Tendsto (fun s : ℂ => s * archKernel s)
      (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds (-1 : ℂ)) :=
    archKernel_residue_at_zero
  -- pairTestMellin β is continuous at 0 (Re 0 = 0 > -4).
  have h_M_cont : ContinuousAt (pairTestMellin β) 0 := by
    apply pairTestMellin_continuousAt; norm_num
  have h_M : Filter.Tendsto (pairTestMellin β)
      (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds (pairTestMellin β 0)) := by
    have h_full : Filter.Tendsto (pairTestMellin β) (𝓝 (0 : ℂ))
        (nhds (pairTestMellin β 0)) := h_M_cont.tendsto
    exact h_full.mono_left nhdsWithin_le_nhds
  have h_mul := h_arch.mul h_M
  -- (-1) * pairTestMellin β 0 = -pairTestMellin β 0
  have h_simp : ((-1 : ℂ) * pairTestMellin β 0) = -pairTestMellin β 0 := by ring
  rw [h_simp] at h_mul
  -- Match shape: s * F β s = (s * archKernel s) * pairTestMellin β s.
  apply h_mul.congr
  intro s
  show (s * archKernel s) * pairTestMellin β s
       = s * F β s
  unfold pairTestMellin_archKernel_product
  ring

/-! ## Residue at `s = 1` -/

/-- **Residue at `s = 1`**:
```
lim_{s → 1, s ≠ 1} (s - 1) · F(s) = pairTestMellin β 1.
```

Combined with `pairTestMellin_at_one : pairTestMellin β 1 = gaussianPairDefect β`,
this identifies the residue with the explicit closed-form value. -/
theorem pairTestMellin_archKernel_residue_at_one (β : ℝ) :
    Filter.Tendsto (fun s : ℂ => (s - 1) * F β s)
      (nhdsWithin (1 : ℂ) {1}ᶜ) (nhds (pairTestMellin β 1)) := by
  have h_arch : Filter.Tendsto (fun s : ℂ => (s - 1) * archKernel s)
      (nhdsWithin (1 : ℂ) {1}ᶜ) (nhds (1 : ℂ)) :=
    archKernel_residue_at_one
  -- pairTestMellin β is continuous at 1.
  have h_M_cont : ContinuousAt (pairTestMellin β) 1 := by
    apply pairTestMellin_continuousAt; norm_num
  have h_M : Filter.Tendsto (pairTestMellin β)
      (nhdsWithin (1 : ℂ) {1}ᶜ) (nhds (pairTestMellin β 1)) := by
    have h_full : Filter.Tendsto (pairTestMellin β) (𝓝 (1 : ℂ))
        (nhds (pairTestMellin β 1)) := h_M_cont.tendsto
    exact h_full.mono_left nhdsWithin_le_nhds
  have h_mul := h_arch.mul h_M
  have h_simp : ((1 : ℂ) * pairTestMellin β 1) = pairTestMellin β 1 := by ring
  rw [h_simp] at h_mul
  apply h_mul.congr
  intro s
  show ((s - 1) * archKernel s) * pairTestMellin β s
       = (s - 1) * F β s
  unfold pairTestMellin_archKernel_product
  ring

/-- **Residue at `s = 1` via `gaussianPairDefect`**: rewriting the previous
limit using `pairTestMellin_at_one`. -/
theorem pairTestMellin_archKernel_residue_at_one_eq_gaussianPairDefect (β : ℝ) :
    Filter.Tendsto (fun s : ℂ => (s - 1) * F β s)
      (nhdsWithin (1 : ℂ) {1}ᶜ)
      (nhds (((gaussianPairDefect β : ℝ) : ℂ))) := by
  have h := pairTestMellin_archKernel_residue_at_one β
  rw [pairTestMellin_at_one β] at h
  exact h

/-! ## Continuity (regularity) at `s = -1` — no pole -/

/-- `archKernel` is continuous at every point of the line `Re s = -1`. The
poles of `archKernel` are at `s ∈ {0, 1}`; for `s` on `Re s = -1`, both
`Γℝ(s)` and `Γℝ(1 - s)` are nonzero. -/
theorem archKernel_continuousAt_on_neg_one_line {y : ℝ} :
    ContinuousAt archKernel ((-1 : ℂ) + (y : ℂ) * I) := by
  set s : ℂ := (-1 : ℂ) + (y : ℂ) * I
  have hs_re : s.re = -1 := by simp [s]
  have hs_ne_0 : s ≠ 0 := by
    intro h
    have hre : s.re = (0 : ℂ).re := by rw [h]
    rw [hs_re] at hre
    exact absurd hre (by norm_num)
  have hs_ne_1 : s ≠ 1 := by
    intro h
    have hre : s.re = (1 : ℂ).re := by rw [h]
    rw [hs_re] at hre
    exact absurd hre (by norm_num)
  have hΓs_ne : Complex.Gammaℝ s ≠ 0 := by
    -- Zeros of Γℝ are at non-positive even integers `s = -2k`. We have Re s = -1,
    -- and `-1 = -2k` has no `k : ℕ` solution.
    intro hzero
    rcases Complex.Gammaℝ_eq_zero_iff.mp hzero with ⟨n, hn⟩
    have hre : s.re = -(2 * (n : ℝ)) := by
      have h := congrArg Complex.re hn
      simp at h
      linarith
    rw [hs_re] at hre
    -- -1 = -(2n), so 2n = 1, but n is a natural so no solution.
    have h1 : (2 * (n : ℝ)) = 1 := by linarith
    have h2 : (n : ℝ) = 1/2 := by linarith
    have h3 : (n : ℝ) ∈ Set.range ((↑) : ℕ → ℝ) := ⟨n, rfl⟩
    -- 1/2 is not a natural number
    rcases n with _ | k
    · simp at h2
    · push_cast at h2; linarith
  have hΓ1s_ne : (1 - s).Gammaℝ ≠ 0 := by
    -- Re(1 - s) = 2 > 0, so Γℝ(1 - s) ≠ 0 directly.
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    show (0 : ℝ) < (1 - s).re
    simp [s]
  -- archKernel is the sum of two quotients, each continuous since
  -- numerators and denominators are continuous and denominators nonzero.
  unfold archKernel
  -- First quotient: Γℝ'(s)/Γℝ(s).
  have hΓ_diff_s : DifferentiableAt ℂ Complex.Gammaℝ s :=
    differentiableAt_Gammaℝ_of_ne_zero hΓs_ne
  have hΓ_diff_1s : DifferentiableAt ℂ Complex.Gammaℝ (1 - s) :=
    differentiableAt_Gammaℝ_of_ne_zero hΓ1s_ne
  have h_open : IsOpen {z : ℂ | z.Gammaℝ ≠ 0} := by
    have h_cont : Continuous (fun z : ℂ => z.Gammaℝ⁻¹) :=
      Complex.differentiable_Gammaℝ_inv.continuous
    have h_eq : {z : ℂ | z.Gammaℝ ≠ 0} =
        (fun z : ℂ => z.Gammaℝ⁻¹) ⁻¹' {w : ℂ | w ≠ 0} := by
      ext z; simp only [Set.mem_setOf_eq, Set.mem_preimage]
      refine ⟨inv_ne_zero, fun h hs => ?_⟩
      apply h; rw [hs, inv_zero]
    rw [h_eq]
    exact IsOpen.preimage h_cont isOpen_ne
  have hΓ_analytic : AnalyticOnNhd ℂ Complex.Gammaℝ {z : ℂ | z.Gammaℝ ≠ 0} := by
    apply DifferentiableOn.analyticOnNhd
    · intro z hz
      exact (differentiableAt_Gammaℝ_of_ne_zero hz).differentiableWithinAt
    · exact h_open
  have hdΓs_cont : ContinuousAt (deriv Complex.Gammaℝ) s :=
    (hΓ_analytic.deriv s hΓs_ne).continuousAt
  have hdΓ1s_cont : ContinuousAt (deriv Complex.Gammaℝ) (1 - s) :=
    (hΓ_analytic.deriv (1 - s) hΓ1s_ne).continuousAt
  have hΓs_cont : ContinuousAt Complex.Gammaℝ s := hΓ_diff_s.continuousAt
  have hΓ1s_cont : ContinuousAt Complex.Gammaℝ (1 - s) := hΓ_diff_1s.continuousAt
  have h_sub_cont : ContinuousAt (fun z : ℂ => (1 : ℂ) - z) s :=
    (continuous_const.sub continuous_id).continuousAt
  have hdΓ1s_comp : ContinuousAt (fun z : ℂ => deriv Complex.Gammaℝ (1 - z)) s :=
    hdΓ1s_cont.comp h_sub_cont
  have hΓ1s_comp : ContinuousAt (fun z : ℂ => Complex.Gammaℝ (1 - z)) s :=
    hΓ1s_cont.comp h_sub_cont
  have hquot1 : ContinuousAt
      (fun z : ℂ => deriv Complex.Gammaℝ z / z.Gammaℝ) s :=
    hdΓs_cont.div hΓs_cont hΓs_ne
  have hquot2 : ContinuousAt
      (fun z : ℂ => deriv Complex.Gammaℝ (1 - z) / (1 - z).Gammaℝ) s :=
    hdΓ1s_comp.div hΓ1s_comp hΓ1s_ne
  exact hquot1.add hquot2

/-- `pairTestMellin_archKernel_product β` is continuous at every point of
the line `Re s = -1` — there is no pole there. -/
theorem pairTestMellin_archKernel_continuousAt_neg_one (β : ℝ) {y : ℝ} :
    ContinuousAt (F β) ((-1 : ℂ) + (y : ℂ) * I) := by
  unfold pairTestMellin_archKernel_product
  have hK := archKernel_continuousAt_on_neg_one_line (y := y)
  have hM : ContinuousAt (pairTestMellin β) ((-1 : ℂ) + (y : ℂ) * I) := by
    apply pairTestMellin_continuousAt
    have : ((-1 : ℂ) + (y : ℂ) * I).re = -1 := by simp
    rw [this]; norm_num
  exact hK.mul hM

/-! ## Identification with `archIntegrand` on the two edges -/

/-- On the right edge `Re s = 2`, the product `F β` agrees with
`archIntegrand β 2` after the parametrisation `s = 2 + iy`. -/
theorem F_eq_archIntegrand_at_two (β : ℝ) (y : ℝ) :
    F β ((2 : ℂ) + (y : ℂ) * I) = archIntegrand β 2 y := by
  unfold pairTestMellin_archKernel_product archKernel archIntegrand
  push_cast
  ring

/-- On the left edge `Re s = -1`, the product `F β` agrees with
`archIntegrand β (-1)` after the parametrisation `s = -1 + iy`. -/
theorem F_eq_archIntegrand_at_neg_one (β : ℝ) (y : ℝ) :
    F β ((-1 : ℂ) + (y : ℂ) * I) = archIntegrand β (-1) y := by
  unfold pairTestMellin_archKernel_product archKernel archIntegrand
  push_cast
  ring

/-! ## Axiom checks -/

#print axioms pairTestMellin_archKernel_differentiableAt_off_poles
#print axioms pairTestMellin_archKernel_residue_at_zero
#print axioms pairTestMellin_archKernel_residue_at_one
#print axioms pairTestMellin_archKernel_residue_at_one_eq_gaussianPairDefect
#print axioms pairTestMellin_archKernel_continuousAt_neg_one
#print axioms F_eq_archIntegrand_at_two
#print axioms F_eq_archIntegrand_at_neg_one

end ZD.ArchKernelRectShift

end
