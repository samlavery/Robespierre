import Mathlib
import RequestProject.ArchKernelRectShift
import RequestProject.ArchKernelCoshGaussRectCauchy
import RequestProject.ArchKernelCoshGaussRectCauchyNegOne

/-!
# Twin removable-singularity remainder for `archKernel · pairTestMellin β`

Let
```
F(s) := archKernel s * pairTestMellin β s
```
be the integrand of the rectangle Cauchy shift used in the H3 / archimedean
transport stack. `F` has simple poles at `s = 0` and `s = 1` coming from the
two `Γℝ`-factors in `archKernel`; the residue limits

* `s · F(s) → -pairTestMellin β 0`   as `s → 0`,
* `(s - 1) · F(s) → gaussianPairDefect β`   as `s → 1`,

are recorded in `ArchKernelRectShift`. After subtracting the two singular
parts
```
S(s) := (-pairTestMellin β 0) / s + gaussianPairDefect β / (s - 1),
```
the remainder `F − S` extends across both poles to a function holomorphic on
the closed rectangle `[-1, 2] × [-T, T]`.

This file constructs that remainder by twice applying the mathlib removable
singularity lemma `Complex.differentiableOn_update_limUnder_of_isLittleO`,
mirroring the structural pattern used in
`WeilHadamardRectangleDecomposition.lean` for `weilIntegrand · hadamardKernel`.

## Main results

* `F_remainder β` — the analytic remainder, defined by patching the two pole
  values to the punctured limits.
* `F_eq_singular_plus_remainder` — off the two poles, `F = S + F_remainder`.
* `F_remainder_differentiableOn` — `F_remainder β` is differentiable on the
  closed rectangle `[-1, 2] ×ℂ [-T, T]` for any `T > 0`.

All proofs are axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`).
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace ZD
namespace PairTestMellinArchKernelRemainder

open ZD.ArchKernelRectShift ZD.WeilArchKernelResidues
open ZD.ArchKernelCoshGaussRectCauchy ZD.ArchKernelCoshGaussRectCauchyNegOne
open ZD.WeilPositivity.Contour

local notation "F" => pairTestMellin_archKernel_product

/-! ## The naive remainder (before patching the two pole values) -/

/-- The naive remainder: subtract both singular parts from `F`. Off the two
poles `{0, 1}` this equals `F − S`; at the poles its value is irrelevant
(blows up) and will be replaced by the punctured-limit value. -/
def F_remainder_naive (β : ℝ) (z : ℂ) : ℂ :=
  F β z - (-pairTestMellin β 0) / z - ((gaussianPairDefect β : ℝ) : ℂ) / (z - 1)

/-! ## The patched remainder -/

/-- The fully patched remainder, with the two simple-pole values replaced by
the punctured limits. The order of the two updates is immaterial (they patch
distinct points). -/
def F_remainder (β : ℝ) : ℂ → ℂ :=
  Function.update
    (Function.update (F_remainder_naive β) 0
      (limUnder (𝓝[≠] (0 : ℂ)) (F_remainder_naive β)))
    1 (limUnder (𝓝[≠] (1 : ℂ)) (F_remainder_naive β))

/-- Off both poles, `F_remainder` equals the naive remainder. -/
theorem F_remainder_eq_naive_off_poles (β : ℝ) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    F_remainder β z = F_remainder_naive β z := by
  unfold F_remainder
  rw [Function.update_of_ne hz1, Function.update_of_ne hz0]

/-! ## Removable singularity at `s = 0`: `s · F_remainder_naive → 0` -/

/-- Multiplied by `s`, the naive remainder tends to `0` at the origin. This
is the residue cancellation: `s · F → -pairTestMellin β 0` exactly cancels
the explicit `(-pairTestMellin β 0)/s` polar part subtracted in the naive
remainder. The other singular part `gaussianPairDefect/(z-1)` is analytic
at `0` and contributes a `0` factor. -/
theorem F_remainder_naive_mul_tendsto_zero_at_zero (β : ℝ) :
    Tendsto (fun s : ℂ => s * F_remainder_naive β s)
      (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
  -- s · F → -pairTestMellin β 0
  have h_sF : Tendsto (fun s : ℂ => s * F β s)
      (𝓝[≠] (0 : ℂ)) (𝓝 (-pairTestMellin β 0)) :=
    pairTestMellin_archKernel_residue_at_zero β
  -- Constant part
  have h_const : Tendsto (fun _ : ℂ => -pairTestMellin β 0)
      (𝓝[≠] (0 : ℂ)) (𝓝 (-pairTestMellin β 0)) := tendsto_const_nhds
  -- Difference → 0
  have h_diff' : Tendsto (fun s : ℂ => s * F β s - (-pairTestMellin β 0))
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have := h_sF.sub h_const
    simpa using this
  -- s · gaussianPairDefect/(s-1) → 0 (continuous quotient × s → 0)
  have h_quot_cont :
      ContinuousAt (fun s : ℂ => ((gaussianPairDefect β : ℝ) : ℂ) / (s - 1)) 0 := by
    have hsub : ContinuousAt (fun s : ℂ => s - 1) 0 :=
      (continuous_id.sub continuous_const).continuousAt
    exact continuousAt_const.div hsub (by norm_num : ((0 : ℂ) - 1) ≠ 0)
  have h_quot_t :
      Tendsto (fun s : ℂ => ((gaussianPairDefect β : ℝ) : ℂ) / (s - 1))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (((gaussianPairDefect β : ℝ) : ℂ) / ((0 : ℂ) - 1))) :=
    h_quot_cont.tendsto.mono_left nhdsWithin_le_nhds
  have h_id : Tendsto (fun s : ℂ => s) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    (continuous_id.continuousAt (x := (0 : ℂ))).tendsto.mono_left nhdsWithin_le_nhds
  have h_S1_zero :
      Tendsto (fun s : ℂ => s * (((gaussianPairDefect β : ℝ) : ℂ) / (s - 1)))
        (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have h_mul := h_id.mul h_quot_t
    have h_zero : (0 : ℂ) * (((gaussianPairDefect β : ℝ) : ℂ) / ((0 : ℂ) - 1)) = 0 := by
      ring
    rw [h_zero] at h_mul
    exact h_mul
  -- Combine and rewrite to s * F_remainder_naive β s.
  have h_combined :
      Tendsto (fun s : ℂ =>
          (s * F β s - (-pairTestMellin β 0)) -
            s * (((gaussianPairDefect β : ℝ) : ℂ) / (s - 1)))
        (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have := h_diff'.sub h_S1_zero
    simpa using this
  apply h_combined.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs_ne
  have hs : s ≠ 0 := hs_ne
  unfold F_remainder_naive
  field_simp

/-! ## Removable singularity at `s = 1`: `(s - 1) · F_remainder_naive → 0` -/

/-- Multiplied by `s - 1`, the naive remainder tends to `0` at `s = 1`. The
`gaussianPairDefect/(s-1)` polar part is exactly cancelled by the residue
limit `(s - 1) · F → gaussianPairDefect`; the other singular part
`(-pairTestMellin β 0)/s` is analytic at `1` and contributes a `0` factor. -/
theorem F_remainder_naive_mul_tendsto_zero_at_one (β : ℝ) :
    Tendsto (fun s : ℂ => (s - 1) * F_remainder_naive β s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (0 : ℂ)) := by
  have h_sF : Tendsto (fun s : ℂ => (s - 1) * F β s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (((gaussianPairDefect β : ℝ) : ℂ))) :=
    pairTestMellin_archKernel_residue_at_one_eq_gaussianPairDefect β
  have h_const : Tendsto (fun _ : ℂ => ((gaussianPairDefect β : ℝ) : ℂ))
      (𝓝[≠] (1 : ℂ)) (𝓝 (((gaussianPairDefect β : ℝ) : ℂ))) := tendsto_const_nhds
  have h_diff' : Tendsto (fun s : ℂ =>
      (s - 1) * F β s - (((gaussianPairDefect β : ℝ) : ℂ)))
      (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have := h_sF.sub h_const
    simpa using this
  -- (s - 1) · (-pairTestMellin β 0)/s → 0 (continuous quotient × (s-1) → 0)
  have h_quot_cont :
      ContinuousAt (fun s : ℂ => (-pairTestMellin β 0) / s) 1 :=
    continuousAt_const.div continuousAt_id (by norm_num : (1 : ℂ) ≠ 0)
  have h_quot_t :
      Tendsto (fun s : ℂ => (-pairTestMellin β 0) / s)
        (𝓝[≠] (1 : ℂ))
        (𝓝 ((-pairTestMellin β 0) / 1)) :=
    h_quot_cont.tendsto.mono_left nhdsWithin_le_nhds
  have h_sub_zero : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have h_full : Tendsto (fun s : ℂ => s - 1) (𝓝 (1 : ℂ)) (𝓝 ((1 : ℂ) - 1)) := by
      have h_cont :
          Continuous (fun s : ℂ => s - 1) :=
        continuous_id.sub continuous_const
      exact h_cont.continuousAt.tendsto
    have hval : ((1 : ℂ) - 1 : ℂ) = 0 := by ring
    rw [hval] at h_full
    exact h_full.mono_left nhdsWithin_le_nhds
  have h_S0_zero :
      Tendsto (fun s : ℂ => (s - 1) * ((-pairTestMellin β 0) / s))
        (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have h_mul := h_sub_zero.mul h_quot_t
    have h_zero : (0 : ℂ) * ((-pairTestMellin β 0) / 1) = 0 := by ring
    rw [h_zero] at h_mul
    exact h_mul
  have h_combined :
      Tendsto (fun s : ℂ =>
          ((s - 1) * F β s - (((gaussianPairDefect β : ℝ) : ℂ))) -
            (s - 1) * ((-pairTestMellin β 0) / s))
        (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have := h_diff'.sub h_S0_zero
    simpa using this
  apply h_combined.congr'
  -- Need s ≠ 0 also (eventually true since 0 ≠ 1).
  have hs_ne_zero : ∀ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), z ≠ 0 :=
    nhdsWithin_le_nhds (isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0))
  filter_upwards [self_mem_nhdsWithin, hs_ne_zero] with s hs_ne hs0
  have hs1 : s ≠ 1 := hs_ne
  have hs1' : s - 1 ≠ 0 := sub_ne_zero_of_ne hs1
  unfold F_remainder_naive
  field_simp
  ring

/-! ## Decomposition equation: `F = singular parts + F_remainder` -/

/-- Off the two simple poles, `F` decomposes as singular parts plus the
analytic remainder. -/
theorem F_eq_singular_plus_remainder (β : ℝ) (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    archKernel s * pairTestMellin β s =
      (-pairTestMellin β 0) / s + ((gaussianPairDefect β : ℝ) : ℂ) / (s - 1) +
        F_remainder β s := by
  rw [F_remainder_eq_naive_off_poles β hs0 hs1]
  unfold F_remainder_naive pairTestMellin_archKernel_product
  ring

/-! ## Naive remainder differentiability at all rectangle points except `{0, 1}` -/

/-- The naive remainder is differentiable at every point of the open punctured
strip `-1 < Re s < 2, s ≠ 0, s ≠ 1`. -/
theorem F_remainder_naive_differentiableAt_open_strip (β : ℝ) {s : ℂ}
    (hs_l : -1 < s.re) (hs_r : s.re < 2) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (F_remainder_naive β) s := by
  unfold F_remainder_naive
  have hF :=
    pairTestMellin_archKernel_differentiableAt_off_poles β hs_l hs_r hs0 hs1
  have hsing0 : DifferentiableAt ℂ (fun z : ℂ => (-pairTestMellin β 0) / z) s :=
    (differentiableAt_const _).div differentiableAt_fun_id hs0
  have hsing1 :
      DifferentiableAt ℂ
        (fun z : ℂ => ((gaussianPairDefect β : ℝ) : ℂ) / (z - 1)) s := by
    have hsub : DifferentiableAt ℂ (fun z : ℂ => z - 1) s :=
      differentiableAt_fun_id.sub_const _
    exact (differentiableAt_const _).div hsub (sub_ne_zero_of_ne hs1)
  exact (hF.sub hsing0).sub hsing1

private lemma F_diffAt_at_neg_one (β : ℝ) (y : ℝ) :
    DifferentiableAt ℂ (F β) ((-1 : ℂ) + (y : ℂ) * I) := by
  set s : ℂ := (-1 : ℂ) + (y : ℂ) * I
  have hK : DifferentiableAt ℂ archKernel s :=
    archKernel_differentiableAt_at_neg_one y
  have hM : DifferentiableAt ℂ (pairTestMellin β) s := by
    apply pairTestMellin_differentiableAt_re_gt_neg_four
    have : s.re = -1 := by simp [s]
    rw [this]; norm_num
  show DifferentiableAt ℂ (fun z => archKernel z * pairTestMellin β z) s
  exact hK.mul hM

private lemma F_diffAt_at_two (β : ℝ) (y : ℝ) :
    DifferentiableAt ℂ (F β) ((2 : ℂ) + (y : ℂ) * I) := by
  set s : ℂ := (2 : ℂ) + (y : ℂ) * I
  have hK : DifferentiableAt ℂ archKernel s :=
    archKernel_differentiableAt_at_two y
  have hM : DifferentiableAt ℂ (pairTestMellin β) s := by
    apply pairTestMellin_differentiableAt_re_gt_neg_four
    have : s.re = 2 := by simp [s]
    rw [this]; norm_num
  show DifferentiableAt ℂ (fun z => archKernel z * pairTestMellin β z) s
  exact hK.mul hM

/-- The naive remainder is differentiable at every point of the line
`Re s = -1` (none of which is a pole). -/
theorem F_remainder_naive_differentiableAt_neg_one (β : ℝ) (y : ℝ) :
    DifferentiableAt ℂ (F_remainder_naive β) ((-1 : ℂ) + (y : ℂ) * I) := by
  set s : ℂ := (-1 : ℂ) + (y : ℂ) * I
  have hs_re : s.re = -1 := by simp [s]
  have hs0 : s ≠ 0 := by
    intro h; have : s.re = 0 := by rw [h]; simp
    rw [hs_re] at this; norm_num at this
  have hs1 : s ≠ 1 := by
    intro h; have : s.re = 1 := by rw [h]; simp
    rw [hs_re] at this; norm_num at this
  unfold F_remainder_naive
  have hF := F_diffAt_at_neg_one β y
  have hsing0 : DifferentiableAt ℂ (fun z : ℂ => (-pairTestMellin β 0) / z) s :=
    (differentiableAt_const _).div differentiableAt_fun_id hs0
  have hsing1 :
      DifferentiableAt ℂ
        (fun z : ℂ => ((gaussianPairDefect β : ℝ) : ℂ) / (z - 1)) s := by
    have hsub : DifferentiableAt ℂ (fun z : ℂ => z - 1) s :=
      differentiableAt_fun_id.sub_const _
    exact (differentiableAt_const _).div hsub (sub_ne_zero_of_ne hs1)
  exact (hF.sub hsing0).sub hsing1

/-- The naive remainder is differentiable at every point of the line
`Re s = 2` (none of which is a pole). -/
theorem F_remainder_naive_differentiableAt_two (β : ℝ) (y : ℝ) :
    DifferentiableAt ℂ (F_remainder_naive β) ((2 : ℂ) + (y : ℂ) * I) := by
  set s : ℂ := (2 : ℂ) + (y : ℂ) * I
  have hs_re : s.re = 2 := by simp [s]
  have hs0 : s ≠ 0 := by
    intro h; have : s.re = 0 := by rw [h]; simp
    rw [hs_re] at this; norm_num at this
  have hs1 : s ≠ 1 := by
    intro h; have : s.re = 1 := by rw [h]; simp
    rw [hs_re] at this; norm_num at this
  unfold F_remainder_naive
  have hF := F_diffAt_at_two β y
  have hsing0 : DifferentiableAt ℂ (fun z : ℂ => (-pairTestMellin β 0) / z) s :=
    (differentiableAt_const _).div differentiableAt_fun_id hs0
  have hsing1 :
      DifferentiableAt ℂ
        (fun z : ℂ => ((gaussianPairDefect β : ℝ) : ℂ) / (z - 1)) s := by
    have hsub : DifferentiableAt ℂ (fun z : ℂ => z - 1) s :=
      differentiableAt_fun_id.sub_const _
    exact (differentiableAt_const _).div hsub (sub_ne_zero_of_ne hs1)
  exact (hF.sub hsing0).sub hsing1

/-! ## Differentiability of `F_remainder` on the rectangle -/

/-- `F_remainder β z = F_remainder_naive β z` on a punctured neighborhood of
`0`. -/
private lemma F_remainder_eq_naive_punct_zero (β : ℝ) :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), F_remainder β z = F_remainder_naive β z := by
  have h_ne_one : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 1 :=
    nhdsWithin_le_nhds (isOpen_ne.mem_nhds (by norm_num : (0 : ℂ) ≠ 1))
  filter_upwards [self_mem_nhdsWithin, h_ne_one] with z hz_ne hz1
  have hz0 : z ≠ 0 := hz_ne
  exact F_remainder_eq_naive_off_poles β hz0 hz1

/-- `F_remainder β z = F_remainder_naive β z` on a punctured neighborhood of
`1`. -/
private lemma F_remainder_eq_naive_punct_one (β : ℝ) :
    ∀ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), F_remainder β z = F_remainder_naive β z := by
  have h_ne_zero : ∀ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), z ≠ 0 :=
    nhdsWithin_le_nhds (isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0))
  filter_upwards [self_mem_nhdsWithin, h_ne_zero] with z hz_ne hz0
  have hz1 : z ≠ 1 := hz_ne
  exact F_remainder_eq_naive_off_poles β hz0 hz1

/-- `IsLittleO` form of the residue cancellation at `0`: the difference
`F_remainder_naive z - F_remainder_naive 0` is `o((z - 0)⁻¹)`. -/
private lemma F_remainder_naive_isLittleO_zero (β : ℝ) :
    (fun z : ℂ => F_remainder_naive β z - F_remainder_naive β 0)
      =o[𝓝[≠] (0 : ℂ)] fun z => (z - 0)⁻¹ := by
  -- (f(z) - f(0)) =o (z - 0)⁻¹ iff (z - 0) · (f(z) - f(0)) → 0.
  -- Reduces to z · f(z) → 0 (constant term `z · f(0)` → 0 separately).
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  -- We will use that (z) * F_remainder_naive z → 0 and z * f(0) → 0.
  have h_target_t : Tendsto
      (fun z : ℂ => z * (F_remainder_naive β z - F_remainder_naive β 0))
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℂ => z * F_remainder_naive β z)
        (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
      F_remainder_naive_mul_tendsto_zero_at_zero β
    have h2 : Tendsto (fun z : ℂ => z * F_remainder_naive β 0)
        (𝓝[≠] (0 : ℂ)) (𝓝 (0 * F_remainder_naive β 0)) := by
      have h_id : Tendsto (fun z : ℂ => z) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
        (continuous_id.continuousAt (x := (0 : ℂ))).tendsto.mono_left
          nhdsWithin_le_nhds
      have := h_id.mul (tendsto_const_nhds (x := F_remainder_naive β 0)
        (f := 𝓝[≠] (0 : ℂ)))
      exact this
    have h2' : Tendsto (fun z : ℂ => z * F_remainder_naive β 0)
        (𝓝[≠] (0 : ℂ)) (𝓝 0) := by simpa using h2
    have h_diff := h1.sub h2'
    have hzero : (0 : ℂ) - 0 = 0 := by ring
    rw [hzero] at h_diff
    apply h_diff.congr'
    filter_upwards with z
    ring
  -- Now turn Tendsto _ _ (𝓝 0) into ‖.‖ ≤ c · ‖(z-0)⁻¹‖ eventually.
  -- ‖z * f‖ = ‖z‖ * ‖f‖ ≤ c · ‖z⁻¹‖^{-1}? Easier: use isBigO directly.
  have h_isBigO : (fun z : ℂ => z * (F_remainder_naive β z - F_remainder_naive β 0))
      =O[𝓝[≠] (0 : ℂ)] (fun _ => (1 : ℂ)) := h_target_t.isBigO_one ℂ
  -- Convert: f =o g ↔ z * f =o z * g (when z is the variable).
  -- Or: `Tendsto (z · f) → 0` ⇒ `f =o (1/z)`.
  -- This is `Asymptotics.IsLittleO.tendsto_inv_smul_nhds_zero` reversed.
  -- Use `Asymptotics.isLittleO_iff_tendsto'` style.
  have h_eq : ∀ z : ℂ, z ≠ 0 →
      F_remainder_naive β z - F_remainder_naive β 0 =
        (z - 0) * (z * (F_remainder_naive β z - F_remainder_naive β 0)) /
          (z * (z - 0)) := by
    intro z hz
    have hz' : z - 0 = z := by ring
    rw [hz']
    field_simp
  -- Easier: bound by Tendsto cast.
  have h_norm_t : Tendsto
      (fun z : ℂ => ‖z * (F_remainder_naive β z - F_remainder_naive β 0)‖)
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have := h_target_t.norm
    simpa using this
  have h_event :
      ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
        ‖z * (F_remainder_naive β z - F_remainder_naive β 0)‖ < c := by
    have := h_norm_t (Iio_mem_nhds hc)
    simpa using this
  filter_upwards [h_event, self_mem_nhdsWithin] with z hz_lt hz_ne
  have hz0 : z ≠ 0 := hz_ne
  have hz_ne_z : (z - 0) ≠ 0 := by
    rw [sub_zero]; exact hz0
  -- ‖f(z) - f(0)‖ ≤ c * ‖(z-0)⁻¹‖
  -- Multiply both sides by ‖z - 0‖ : ‖(z-0)(f(z)-f(0))‖ ≤ c.
  have h_mul_eq : ‖z * (F_remainder_naive β z - F_remainder_naive β 0)‖ =
      ‖(z - 0) * (F_remainder_naive β z - F_remainder_naive β 0)‖ := by
    rw [sub_zero]
  rw [h_mul_eq] at hz_lt
  -- Now `hz_lt : ‖(z - 0) * Δ‖ < c`, want `‖Δ‖ ≤ c * ‖(z - 0)⁻¹‖`.
  rw [norm_mul] at hz_lt
  -- ‖z - 0‖ * ‖Δ‖ < c.
  have hz_norm_pos : 0 < ‖z - 0‖ := by
    rw [norm_pos_iff]; exact hz_ne_z
  have h_norm_inv : ‖(z - 0)⁻¹‖ = ‖z - 0‖⁻¹ := norm_inv (z - 0)
  rw [h_norm_inv]
  have h_div : ‖F_remainder_naive β z - F_remainder_naive β 0‖ < c / ‖z - 0‖ :=
    (lt_div_iff₀ hz_norm_pos).mpr (by rw [mul_comm]; exact hz_lt)
  rw [div_eq_mul_inv] at h_div
  exact h_div.le

/-- `IsLittleO` form of the residue cancellation at `1`: the difference
`F_remainder_naive z - F_remainder_naive 1` is `o((z - 1)⁻¹)`. -/
private lemma F_remainder_naive_isLittleO_one (β : ℝ) :
    (fun z : ℂ => F_remainder_naive β z - F_remainder_naive β 1)
      =o[𝓝[≠] (1 : ℂ)] fun z => (z - 1)⁻¹ := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have h_target_t : Tendsto
      (fun z : ℂ => (z - 1) * (F_remainder_naive β z - F_remainder_naive β 1))
      (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℂ => (z - 1) * F_remainder_naive β z)
        (𝓝[≠] (1 : ℂ)) (𝓝 0) :=
      F_remainder_naive_mul_tendsto_zero_at_one β
    have h_sub_zero : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
      have h_full : Tendsto (fun s : ℂ => s - 1) (𝓝 (1 : ℂ)) (𝓝 ((1 : ℂ) - 1)) :=
        ((continuous_id.sub continuous_const).continuousAt
          (x := (1 : ℂ))).tendsto
      have hval : ((1 : ℂ) - 1 : ℂ) = 0 := by ring
      rw [hval] at h_full
      exact h_full.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun z : ℂ => (z - 1) * F_remainder_naive β 1)
        (𝓝[≠] (1 : ℂ)) (𝓝 (0 * F_remainder_naive β 1)) :=
      h_sub_zero.mul (tendsto_const_nhds (x := F_remainder_naive β 1)
        (f := 𝓝[≠] (1 : ℂ)))
    have h2' : Tendsto (fun z : ℂ => (z - 1) * F_remainder_naive β 1)
        (𝓝[≠] (1 : ℂ)) (𝓝 0) := by simpa using h2
    have h_diff := h1.sub h2'
    have hzero : (0 : ℂ) - 0 = 0 := by ring
    rw [hzero] at h_diff
    apply h_diff.congr'
    filter_upwards with z
    ring
  have h_norm_t : Tendsto
      (fun z : ℂ =>
        ‖(z - 1) * (F_remainder_naive β z - F_remainder_naive β 1)‖)
      (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have := h_target_t.norm
    simpa using this
  have h_event :
      ∀ᶠ z : ℂ in 𝓝[≠] (1 : ℂ),
        ‖(z - 1) * (F_remainder_naive β z - F_remainder_naive β 1)‖ < c := by
    have := h_norm_t (Iio_mem_nhds hc)
    simpa using this
  filter_upwards [h_event, self_mem_nhdsWithin] with z hz_lt hz_ne
  have hz1 : z ≠ 1 := hz_ne
  have hz_ne_z : (z - 1) ≠ 0 := sub_ne_zero_of_ne hz1
  rw [norm_mul] at hz_lt
  have hz_norm_pos : 0 < ‖z - 1‖ := by
    rw [norm_pos_iff]; exact hz_ne_z
  have h_norm_inv : ‖(z - 1)⁻¹‖ = ‖z - 1‖⁻¹ := norm_inv (z - 1)
  rw [h_norm_inv]
  have h_div : ‖F_remainder_naive β z - F_remainder_naive β 1‖ < c / ‖z - 1‖ :=
    (lt_div_iff₀ hz_norm_pos).mpr (by rw [mul_comm]; exact hz_lt)
  rw [div_eq_mul_inv] at h_div
  exact h_div.le

/-- `F_remainder β` is differentiable at `0` (in the complex sense). -/
theorem F_remainder_differentiableAt_zero (β : ℝ) :
    DifferentiableAt ℂ (F_remainder β) (0 : ℂ) := by
  -- Apply `Complex.differentiableOn_update_limUnder_of_isLittleO` to
  -- `F_remainder_naive β` on `Metric.ball 0 (1/2)` (so 1 ∉ ball).
  set ε : ℝ := (1 / 2 : ℝ)
  have hε : (0 : ℝ) < ε := by norm_num
  set U : Set ℂ := Metric.ball 0 ε
  have hU_nhds : U ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 hε
  have h_one_notin : (1 : ℂ) ∉ U := by
    intro h
    have hdist : dist (1 : ℂ) 0 < ε := h
    rw [dist_eq_norm] at hdist
    simp at hdist
    norm_num [ε] at hdist
  -- F_remainder_naive is differentiable on U \ {0}: each z in U has Re z within
  -- (-1/2, 1/2) ⊂ (-1, 2) so the open-strip lemma applies (and z ≠ 1).
  have h_diff : DifferentiableOn ℂ (F_remainder_naive β) (U \ {0}) := by
    intro z hz
    have hz_in : z ∈ U := hz.1
    have hz_ne_zero : z ≠ 0 := by
      intro h; exact hz.2 (h ▸ rfl)
    have hz_ne_one : z ≠ 1 := by
      intro h; rw [h] at hz_in; exact h_one_notin hz_in
    have h_re_lt : ‖z‖ < ε := by
      have hdist : dist z 0 < ε := hz_in
      rw [dist_eq_norm] at hdist; simpa using hdist
    have h_re_l : -1 < z.re := by
      have h_abs := Complex.abs_re_le_norm z
      have : |z.re| < ε := lt_of_le_of_lt h_abs h_re_lt
      have : -ε < z.re := neg_lt_of_abs_lt this
      have hε_lt : -1 < -ε := by norm_num [ε]
      linarith
    have h_re_r : z.re < 2 := by
      have h_abs := Complex.abs_re_le_norm z
      have : |z.re| < ε := lt_of_le_of_lt h_abs h_re_lt
      have : z.re < ε := lt_of_abs_lt this
      have hε_lt : ε < 2 := by norm_num [ε]
      linarith
    exact (F_remainder_naive_differentiableAt_open_strip β h_re_l h_re_r
      hz_ne_zero hz_ne_one).differentiableWithinAt
  -- Apply the removable singularity lemma.
  have h_update : DifferentiableOn ℂ
      (Function.update (F_remainder_naive β) (0 : ℂ)
        (limUnder (𝓝[≠] (0 : ℂ)) (F_remainder_naive β))) U :=
    Complex.differentiableOn_update_limUnder_of_isLittleO hU_nhds h_diff
      (F_remainder_naive_isLittleO_zero β)
  -- The patched function on U equals F_remainder β: the second update at 1 is a
  -- no-op since 1 ∉ U.
  have h_eq_on_U : Set.EqOn (F_remainder β)
      (Function.update (F_remainder_naive β) (0 : ℂ)
        (limUnder (𝓝[≠] (0 : ℂ)) (F_remainder_naive β))) U := by
    intro z hz
    have hz_ne_one : z ≠ 1 := by
      intro h; rw [h] at hz; exact h_one_notin hz
    unfold F_remainder
    rw [Function.update_of_ne hz_ne_one]
  have h_diff_F_remainder : DifferentiableOn ℂ (F_remainder β) U := by
    apply h_update.congr
    intro z hz
    exact h_eq_on_U hz
  exact (h_diff_F_remainder.differentiableAt hU_nhds)

/-- `F_remainder β` is differentiable at `1` (in the complex sense). -/
theorem F_remainder_differentiableAt_one (β : ℝ) :
    DifferentiableAt ℂ (F_remainder β) (1 : ℂ) := by
  set ε : ℝ := (1 / 2 : ℝ)
  have hε : (0 : ℝ) < ε := by norm_num
  set U : Set ℂ := Metric.ball (1 : ℂ) ε
  have hU_nhds : U ∈ 𝓝 (1 : ℂ) := Metric.ball_mem_nhds 1 hε
  have h_zero_notin : (0 : ℂ) ∉ U := by
    intro h
    have hdist : dist (0 : ℂ) 1 < ε := h
    rw [dist_eq_norm] at hdist
    simp at hdist
    norm_num [ε] at hdist
  have h_diff : DifferentiableOn ℂ (F_remainder_naive β) (U \ {1}) := by
    intro z hz
    have hz_in : z ∈ U := hz.1
    have hz_ne_one : z ≠ 1 := by
      intro h; exact hz.2 (h ▸ rfl)
    have hz_ne_zero : z ≠ 0 := by
      intro h; rw [h] at hz_in; exact h_zero_notin hz_in
    -- ‖z - 1‖ < ε, so |Re z - 1| < ε, hence Re z ∈ (1 - ε, 1 + ε) = (1/2, 3/2).
    have h_dist : ‖z - 1‖ < ε := by
      have hd : dist z 1 < ε := hz_in
      rw [dist_eq_norm] at hd; exact hd
    have h_re_diff : |z.re - 1| < ε := by
      have := Complex.abs_re_le_norm (z - 1)
      have h_re_eq : (z - 1).re = z.re - 1 := by simp
      rw [h_re_eq] at this
      exact lt_of_le_of_lt this h_dist
    have h_re_l : -1 < z.re := by
      have : -ε < z.re - 1 := neg_lt_of_abs_lt h_re_diff
      have hε_l : -ε > -2 := by norm_num [ε]
      linarith
    have h_re_r : z.re < 2 := by
      have : z.re - 1 < ε := lt_of_abs_lt h_re_diff
      have hε_r : ε < 1 := by norm_num [ε]
      linarith
    exact (F_remainder_naive_differentiableAt_open_strip β h_re_l h_re_r
      hz_ne_zero hz_ne_one).differentiableWithinAt
  have h_update : DifferentiableOn ℂ
      (Function.update (F_remainder_naive β) (1 : ℂ)
        (limUnder (𝓝[≠] (1 : ℂ)) (F_remainder_naive β))) U :=
    Complex.differentiableOn_update_limUnder_of_isLittleO hU_nhds h_diff
      (F_remainder_naive_isLittleO_one β)
  have h_eq_on_U : Set.EqOn (F_remainder β)
      (Function.update (F_remainder_naive β) (1 : ℂ)
        (limUnder (𝓝[≠] (1 : ℂ)) (F_remainder_naive β))) U := by
    intro z hz
    have hz_ne_zero : z ≠ 0 := by
      intro h; rw [h] at hz; exact h_zero_notin hz
    unfold F_remainder
    by_cases hz1 : z = 1
    · subst hz1
      simp
    · rw [Function.update_of_ne hz1, Function.update_of_ne hz_ne_zero,
          Function.update_of_ne hz1]
  have h_diff_F_remainder : DifferentiableOn ℂ (F_remainder β) U := by
    apply h_update.congr
    intro z hz
    exact h_eq_on_U hz
  exact (h_diff_F_remainder.differentiableAt hU_nhds)

/-- `F_remainder β` is differentiable at every point of the closed strip
`[-1, 2] ×ℂ ℝ` away from the two poles `{0, 1}`. -/
theorem F_remainder_differentiableAt_off_poles (β : ℝ) {z : ℂ}
    (hz_l : -1 ≤ z.re) (hz_r : z.re ≤ 2) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    DifferentiableAt ℂ (F_remainder β) z := by
  -- F_remainder β agrees with F_remainder_naive β on a neighborhood of z
  -- (since z ∉ {0, 1}, the updates are no-ops in a neighborhood).
  have h_ne_pole_nhds : {w : ℂ | w ≠ 0 ∧ w ≠ 1} ∈ 𝓝 z := by
    have h0_open : {w : ℂ | w ≠ 0} ∈ 𝓝 z := isOpen_ne.mem_nhds hz0
    have h1_open : {w : ℂ | w ≠ 1} ∈ 𝓝 z := isOpen_ne.mem_nhds hz1
    exact Filter.inter_mem h0_open h1_open
  have h_eq : F_remainder β =ᶠ[𝓝 z] F_remainder_naive β := by
    filter_upwards [h_ne_pole_nhds] with w hw
    exact F_remainder_eq_naive_off_poles β hw.1 hw.2
  -- Strict-vs-≤ analysis on z.re:
  rcases lt_or_eq_of_le hz_l with hz_l_strict | hz_l_eq
  · rcases lt_or_eq_of_le hz_r with hz_r_strict | hz_r_eq
    · -- Open strip case
      have h_diff_naive :=
        F_remainder_naive_differentiableAt_open_strip β hz_l_strict hz_r_strict hz0 hz1
      exact h_diff_naive.congr_of_eventuallyEq h_eq
    · -- z.re = 2: parametrise z as 2 + i·z.im
      have hz_param : z = (2 : ℂ) + ((z.im : ℂ) * I) := by
        apply Complex.ext
        · simp [hz_r_eq]
        · simp
      have h_diff_naive : DifferentiableAt ℂ (F_remainder_naive β) z := by
        rw [hz_param]
        exact F_remainder_naive_differentiableAt_two β z.im
      exact h_diff_naive.congr_of_eventuallyEq h_eq
  · -- z.re = -1: parametrise z as -1 + i·z.im
    have hz_param : z = (-1 : ℂ) + ((z.im : ℂ) * I) := by
      apply Complex.ext
      · simp [← hz_l_eq]
      · simp
    have h_diff_naive : DifferentiableAt ℂ (F_remainder_naive β) z := by
      rw [hz_param]
      exact F_remainder_naive_differentiableAt_neg_one β z.im
    exact h_diff_naive.congr_of_eventuallyEq h_eq

/-- Main theorem: `F_remainder β` is differentiable on the closed rectangle
`[-1, 2] ×ℂ [-T, T]`. -/
theorem F_remainder_differentiableOn (β : ℝ) (T : ℝ) (_hT : 0 < T) :
    DifferentiableOn ℂ (F_remainder β)
      (Set.uIcc (-1 : ℝ) 2 ×ℂ Set.uIcc (-T) T) := by
  intro z hz
  -- Extract real-part bounds from membership.
  have hz_re_mem : z.re ∈ Set.uIcc (-1 : ℝ) 2 := (Complex.mem_reProdIm.mp hz).1
  have h_uIcc_eq : Set.uIcc (-1 : ℝ) 2 = Set.Icc (-1 : ℝ) 2 := by
    rw [Set.uIcc_of_le]; norm_num
  rw [h_uIcc_eq] at hz_re_mem
  have hz_l : -1 ≤ z.re := hz_re_mem.1
  have hz_r : z.re ≤ 2 := hz_re_mem.2
  by_cases hz0 : z = 0
  · subst hz0
    exact (F_remainder_differentiableAt_zero β).differentiableWithinAt
  · by_cases hz1 : z = 1
    · subst hz1
      exact (F_remainder_differentiableAt_one β).differentiableWithinAt
    · have h := F_remainder_differentiableAt_off_poles β hz_l hz_r hz0 hz1
      exact h.differentiableWithinAt

/-- **Subgoal 3 — Cauchy on the holomorphic remainder.** The rectangle contour
integral of `F_remainder β` over `[-1, 2] × [-T, T]` vanishes by Cauchy-Goursat. -/
theorem F_remainder_rectContourIntegral_zero (β : ℝ) {T : ℝ} (hT : 0 < T) :
    ZD.WeilPositivity.Contour.rectContourIntegral (-1 : ℝ) 2 T (F_remainder β) = 0 :=
  ZD.WeilPositivity.Contour.rectContourIntegral_eq_zero_of_differentiableOn
    (-1 : ℝ) 2 T (F_remainder β) (F_remainder_differentiableOn β T hT)

/-! ## Axiom checks -/

#print axioms F_remainder
#print axioms F_eq_singular_plus_remainder
#print axioms F_remainder_differentiableOn
#print axioms F_remainder_rectContourIntegral_zero

end PairTestMellinArchKernelRemainder
end ZD
