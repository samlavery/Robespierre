import Mathlib
import RequestProject.WeilContour
import RequestProject.ZeroCountJensen

/-!
# Weil Zero Sum — Cycle 46

Goal: sum the circle-integral residue contributions from cycle 32 /
cycle 41 over all nontrivial zeros of `ζ` inside the rectangle, and use
`ZD.ZeroCount.nontrivialZeros_inv_sq_summable` (now axiom-clean!) to justify
convergence.

## Delivered in this file

* `WeilZeroSumTarget` — named target for the Jensen-summed zero-side of the
  Weil formula for the pair test.
* Re-export of `nontrivialZeros_inv_sq_summable` with short docstring.

## Deferred (remaining in cycle 46)

* Enumerate zeros inside rectangle as a finite set parameterized by T.
* Swap sum and limit / integral (Tonelli).
* Extract `Σ_ρ pairTestMellin β ρ` as a convergent series.

Estimated remaining work: 200–400 lines.
-/

open Complex Real MeasureTheory Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- **Re-export of Jensen summability.** `∑ 1/|ρ|² < ∞` over nontrivial zeros.
This is the load-bearing convergence fact for the zero-side sum. -/
theorem nontrivialZeros_inv_sq_summable_reexport :
    ZD.nontrivialZeros_inv_sq_summable_target :=
  ZD.ZeroCount.nontrivialZeros_inv_sq_summable

/-- **Target for cycle 46.** The zero-side of the Weil formula converges:
`∑ pairTestMellin β ρ` over all nontrivial zeros `ρ` is absolutely summable,
given Jensen's bound and `pairTestMellin`'s decay. -/
def WeilZeroSumTarget (β : ℝ) : Prop :=
  Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => pairTestMellin β ρ.val)

#print axioms nontrivialZeros_inv_sq_summable_reexport
#print axioms WeilZeroSumTarget

/-- **Conditional summability.** Given a pointwise bound
`‖pairTestMellin β ρ‖ ≤ C · 1/|ρ·(ρ−1)|²` over nontrivial zeros, summability
follows from Jensen summability (`nontrivialZeros_inv_sq_summable_reexport`). -/
theorem pairTestMellin_summable_of_bound
    (β : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
      ‖pairTestMellin β ρ.val‖ ≤ C * (1 / Complex.normSq (ρ.val * (ρ.val - 1)))) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros} => pairTestMellin β ρ.val) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  exact (nontrivialZeros_inv_sq_summable_reexport).mul_left C

#print axioms pairTestMellin_summable_of_bound

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 46 — Decay bounds for `pairTestMellin β s` on the critical strip
-- ═══════════════════════════════════════════════════════════════════════════

/-- **MellinConvergent of the coerced pair test function on `Re s > 0`.**

Assembles `pair_cosh_gauss_test β t` Mellin integrability from the five-term
cosh expansion (`pair_test_mellin_integrand_expansion`) combined with
`mellinConvergent_coshGauss` at each cosh rate.  The fifth piece comes from
`mellinConvergent_coshGauss 0 _`, whose integrand reduces to the pure
Gaussian `exp (-2 t²)` since `Real.cosh (0 * t) = 1`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem mellinConvergent_pair (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => ((pair_cosh_gauss_test β t : ℝ) : ℂ)) s := by
  unfold MellinConvergent
  have h1 := mellinConvergent_coshGauss (2*β - Real.pi/3) hs
  have h2 := mellinConvergent_coshGauss (2 - Real.pi/3 - 2*β) hs
  have h3 := mellinConvergent_coshGauss (1 - Real.pi/3) hs
  have h4 := mellinConvergent_coshGauss (2*β - 1) hs
  have h5 := mellinConvergent_coshGauss 0 hs
  unfold MellinConvergent at h1 h2 h3 h4 h5
  have h5' : IntegrableOn
      (fun t : ℝ => (t:ℂ)^(s-1) • ((Real.exp (-2*t^2) : ℝ) : ℂ)) (Ioi 0) volume := by
    refine (integrableOn_congr_fun (fun t _ => ?_) measurableSet_Ioi).mp h5
    simp [Real.cosh_zero]
  have h12 : IntegrableOn (fun t : ℝ => (1/2 : ℂ) • ((t:ℂ)^(s-1) •
      ((Real.cosh ((2*β - Real.pi/3) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)) +
      (1/2 : ℂ) • ((t:ℂ)^(s-1) •
      ((Real.cosh ((2 - Real.pi/3 - 2*β) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)))
      (Ioi 0) volume :=
    (h1.smul (1/2 : ℂ)).add (h2.smul (1/2 : ℂ))
  have h34 : IntegrableOn (fun t : ℝ => ((t:ℂ)^(s-1) •
      ((Real.cosh ((1 - Real.pi/3) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)) +
      ((t:ℂ)^(s-1) •
      ((Real.cosh ((2*β - 1) * t) * Real.exp (-2*t^2) : ℝ) : ℂ)))
      (Ioi 0) volume :=
    h3.add h4
  have h_all := (h12.sub h34).add h5'
  refine (integrableOn_congr_fun (fun t _ => ?_) measurableSet_Ioi).mpr h_all
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [pair_test_mellin_integrand_expansion]
  abel

#print axioms mellinConvergent_pair

/-- **Real Mellin integrand of the pair test is integrable on `Ioi 0` for `σ > 0`.**

The real-valued integrand `t^(σ-1) · pair_cosh_gauss_test β t` arises as the
norm of the complex Mellin integrand `(t : ℂ)^((σ:ℂ) - 1) • pair β t`, using
`‖t^c‖ = t^c.re` for `t > 0` and `pair β t ≥ 0`.  Integrability follows from
`mellinConvergent_pair` at `s = (σ : ℂ)`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem pair_mellin_integrand_integrableOn (β : ℝ) (σ : ℝ) (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t^(σ-1) * pair_cosh_gauss_test β t) (Ioi 0) := by
  set s : ℂ := (σ : ℂ)
  have hs_re : (0 : ℝ) < s.re := by simp [s]; exact hσ
  have hConv := mellinConvergent_pair β hs_re
  unfold MellinConvergent at hConv
  have hnorm := hConv.norm
  refine (integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi).mpr hnorm
  simp only [norm_smul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp [Real.norm_of_nonneg (pair_cosh_gauss_test_nonneg β t), s]

#print axioms pair_mellin_integrand_integrableOn

/-- **Pointwise norm bound for `pairTestMellin β s`.**

For every `s : ℂ`, the norm of the complex Mellin transform of the pair test
is bounded by the real Mellin integral of `pair_cosh_gauss_test β` at exponent
`σ = s.re`:

```
‖pairTestMellin β s‖ ≤ ∫_{t > 0} t^(σ-1) · pair_cosh_gauss_test β t dt.
```

Triangle inequality `norm_integral_le_integral_norm` plus
`‖(t:ℂ)^(s-1)‖ = t^(s.re - 1)` (for `t > 0`) and
`|pair_cosh_gauss_test β t| = pair_cosh_gauss_test β t` (nonneg).

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem pairTestMellin_norm_le_real_integral (β : ℝ) (s : ℂ) :
    ‖pairTestMellin β s‖ ≤
      ∫ t in Ioi (0:ℝ), t^(s.re - 1) * pair_cosh_gauss_test β t := by
  unfold pairTestMellin mellin
  calc ‖∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1) • ((pair_cosh_gauss_test β t : ℝ) : ℂ)‖
      ≤ ∫ t in Ioi (0:ℝ), ‖(t:ℂ)^(s-1) • ((pair_cosh_gauss_test β t : ℝ) : ℂ)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t in Ioi (0:ℝ), t^(s.re - 1) * pair_cosh_gauss_test β t := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        simp only [norm_smul]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
        simp [Real.norm_of_nonneg (pair_cosh_gauss_test_nonneg β t)]

#print axioms pairTestMellin_norm_le_real_integral

/-- **Uniform norm bound on the strip `[σL, 1]` (constant in `Im s`).**

For every `σL ∈ (0, 1]`, there is a constant `C ≥ 0` such that

```
‖pairTestMellin β s‖ ≤ C     whenever  σL ≤ s.re ≤ 1.
```

The bound is independent of `Im s`: since the integrand of
`pairTestMellin β s` has norm `t^(s.re - 1) · pair_cosh_gauss_test β t`
(purely real), the norm depends only on `Re s`.

**Dominator.** For `σ ∈ [σL, 1]` and `t > 0`,
`t^(σ-1) ≤ t^(σL-1) + 1`:
- `t ≤ 1`: `t^(σ-1) ≤ t^(σL-1)` since exponents larger when `t ≤ 1` give smaller values.
- `t ≥ 1`: `t^(σ-1) ≤ t^0 = 1` since exponents ≤ 0 applied to `t ≥ 1` give ≤ 1.

Integrability of the dominator follows from
`pair_mellin_integrand_integrableOn β σL hσL` and the `σ = 1` specialization.

This is stronger than Option B of the task description (which allows a
`(1 + |s.im|)` factor): the bound is uniformly constant on the strip.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem pairTestMellin_norm_bound_on_strip
    (β : ℝ) (σL : ℝ) (hσL : 0 < σL) (hσL_le : σL ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σL ≤ s.re → s.re ≤ 1 →
      ‖pairTestMellin β s‖ ≤ C := by
  have h_int_L : IntegrableOn (fun t : ℝ => t^(σL-1) * pair_cosh_gauss_test β t) (Ioi 0) :=
    pair_mellin_integrand_integrableOn β σL hσL
  have h_int_one : IntegrableOn (fun t : ℝ => pair_cosh_gauss_test β t) (Ioi 0) := by
    have h := pair_mellin_integrand_integrableOn β 1 (by norm_num)
    refine (integrableOn_congr_fun (fun t _ => ?_) measurableSet_Ioi).mp h
    simp
  set I_L : ℝ := ∫ t in Ioi (0:ℝ), t^(σL-1) * pair_cosh_gauss_test β t
  set I_0 : ℝ := ∫ t in Ioi (0:ℝ), pair_cosh_gauss_test β t
  set C : ℝ := I_L + I_0
  have hI_L_nonneg : 0 ≤ I_L :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (pair_cosh_gauss_test_nonneg β t))
  have hI_0_nonneg : 0 ≤ I_0 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioi
      (fun t _ => pair_cosh_gauss_test_nonneg β t)
  refine ⟨C, add_nonneg hI_L_nonneg hI_0_nonneg, fun s hσL_le_re hre_le_one => ?_⟩
  have hbound := pairTestMellin_norm_le_real_integral β s
  have h_dom : ∀ t ∈ Ioi (0:ℝ),
      t^(s.re - 1) * pair_cosh_gauss_test β t ≤
        t^(σL - 1) * pair_cosh_gauss_test β t + pair_cosh_gauss_test β t := by
    intro t ht
    have ht_pos : (0:ℝ) < t := ht
    have h_pair_nn := pair_cosh_gauss_test_nonneg β t
    have h_rpow_bd : t^(s.re - 1) ≤ t^(σL-1) + 1 := by
      rcases le_or_gt t 1 with h | h
      · have h1 : t^(s.re - 1) ≤ t^(σL-1) :=
          Real.rpow_le_rpow_of_exponent_ge ht_pos h (by linarith)
        linarith [Real.rpow_nonneg ht_pos.le (σL - 1)]
      · have h1 : t^(s.re - 1) ≤ t^((1:ℝ)-1) :=
          Real.rpow_le_rpow_of_exponent_le (x := t) h.le (by linarith)
        have h2 : t^((1:ℝ)-1) = 1 := by simp
        linarith [Real.rpow_nonneg ht_pos.le (σL - 1)]
    calc t^(s.re - 1) * pair_cosh_gauss_test β t
        ≤ (t^(σL - 1) + 1) * pair_cosh_gauss_test β t :=
          mul_le_mul_of_nonneg_right h_rpow_bd h_pair_nn
      _ = t^(σL - 1) * pair_cosh_gauss_test β t + pair_cosh_gauss_test β t := by ring
  have h_rhs_integrable : IntegrableOn
      (fun t : ℝ => t^(σL - 1) * pair_cosh_gauss_test β t + pair_cosh_gauss_test β t)
      (Ioi 0) := h_int_L.add h_int_one
  have h_lhs_integrable : IntegrableOn
      (fun t : ℝ => t^(s.re - 1) * pair_cosh_gauss_test β t) (Ioi 0) :=
    pair_mellin_integrand_integrableOn β s.re (by linarith)
  have h_integral_le :
      (∫ t in Ioi (0:ℝ), t^(s.re - 1) * pair_cosh_gauss_test β t) ≤
      ∫ t in Ioi (0:ℝ),
        (t^(σL - 1) * pair_cosh_gauss_test β t + pair_cosh_gauss_test β t) :=
    MeasureTheory.setIntegral_mono_on h_lhs_integrable h_rhs_integrable measurableSet_Ioi h_dom
  have h_integral_split :
      (∫ t in Ioi (0:ℝ),
          (t^(σL - 1) * pair_cosh_gauss_test β t + pair_cosh_gauss_test β t)) =
      I_L + I_0 := by
    rw [MeasureTheory.integral_add h_int_L h_int_one]
  linarith

#print axioms pairTestMellin_norm_bound_on_strip

-- ═══════════════════════════════════════════════════════════════════════════
-- § Option C fix — Im-decay target + conditional summability closure
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Im-decay target for pair test Mellin.** States the bound needed to close
`WeilZeroSumTarget` via Jensen's summability. Specifically, a constant `C ≥ 0`
and the bound

```
‖pairTestMellin β ρ‖ ≤ C / |ρ·(ρ−1)|²     for every nontrivial zero ρ.
```

**Why this is needed.** Jensen summability (`nontrivialZeros_inv_sq_summable_reexport`)
gives `∑ 1/|ρ·(ρ−1)|² < ∞`. Combined with this bound, `∑ ‖pairTestMellin β ρ‖`
converges, which is equivalent (via `Summable.of_norm`) to summability of the
complex-valued series.

**Status.** This is a named target (not proved). Discharging it requires showing
`‖pairTestMellin β (σ + iT)‖` decays at least as fast as `|T|^{-4}` uniformly
in `σ ∈ (0, 1)`. From the cosh expansion (cycle 38), each term
`coshGaussMellin c (σ + iT)` is a Mellin transform of `cosh(c·t)·exp(−2t²)`,
which has smooth Gaussian profile — integration by parts gives arbitrary
polynomial decay in `|T|` on any vertical strip. Proving this in Lean requires
the IBP machinery specialized to Mellin transforms, which lives in a separate
analytic infrastructure cycle. -/
def pairTestMellin_decay_target (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
    ‖pairTestMellin β ρ.val‖ ≤ C * (1 / Complex.normSq (ρ.val * (ρ.val - 1)))

/-- **Conditional Option C closure.** Given the Im-decay target, `WeilZeroSumTarget`
follows from Jensen summability via `pairTestMellin_summable_of_bound`.

This is the structural wrapper: the real work is discharging
`pairTestMellin_decay_target` via Stirling-type asymptotics. -/
theorem WeilZeroSumTarget_of_decay (β : ℝ) (h : pairTestMellin_decay_target β) :
    WeilZeroSumTarget β := by
  obtain ⟨C, hC, hbound⟩ := h
  exact pairTestMellin_summable_of_bound β hC hbound

#print axioms pairTestMellin_decay_target
#print axioms WeilZeroSumTarget_of_decay

-- ═══════════════════════════════════════════════════════════════════════════
-- § Cycle 46+ — Strictly stronger Im-quartic decay target and algebraic
-- reduction.  Isolates the analytic content into a clean Im-decay statement.
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Normsq comparison.** For `ρ` with `Re ρ ∈ (0, 1)`,
`normSq (ρ · (ρ − 1)) ≤ (1 + (Im ρ)²)²`.

This is the key algebraic bound that converts an Im-quartic decay statement
`‖pairTestMellin β ρ‖ ≤ C · (1 + (Im ρ)²)^{−2}` into the Jensen-compatible
form `‖pairTestMellin β ρ‖ ≤ C · (1/normSq (ρ · (ρ−1)))` required by
`pairTestMellin_summable_of_bound`.

**Proof sketch.** `normSq (ρ · (ρ−1)) = normSq ρ · normSq (ρ−1)`, and both
factors are bounded by `1 + (Im ρ)²` since `Re ρ ∈ (0, 1)` ⟹
`(Re ρ)² ≤ 1` and `(Re ρ − 1)² ≤ 1`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem normSq_pair_le_im_quartic
    {ρ : ℂ} (hσ_pos : 0 < ρ.re) (hσ_lt : ρ.re < 1) :
    Complex.normSq (ρ * (ρ - 1)) ≤ (1 + ρ.im^2)^2 := by
  have hnormsq : Complex.normSq (ρ * (ρ - 1)) =
      Complex.normSq ρ * Complex.normSq (ρ - 1) :=
    Complex.normSq_mul ρ (ρ - 1)
  rw [hnormsq]
  have hρ : Complex.normSq ρ ≤ 1 + ρ.im^2 := by
    unfold Complex.normSq
    simp
    nlinarith [sq_nonneg ρ.re, sq_nonneg ρ.im, sq_nonneg (1 - ρ.re)]
  have hρm1 : Complex.normSq (ρ - 1) ≤ 1 + ρ.im^2 := by
    have hre_eq : (ρ - 1).re = ρ.re - 1 := by simp
    have him_eq : (ρ - 1).im = ρ.im := by simp
    unfold Complex.normSq
    simp [hre_eq, him_eq]
    nlinarith [sq_nonneg (1 - ρ.re), sq_nonneg ρ.im]
  nlinarith [Complex.normSq_nonneg ρ, Complex.normSq_nonneg (ρ - 1),
    sq_nonneg (1 + ρ.im^2)]

#print axioms normSq_pair_le_im_quartic

/-- **Nontrivial zeros avoid 0 and 1.** Direct from `Re ρ ∈ (0, 1)`. -/
theorem nontrivialZero_ne_zero_and_one {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    ρ ≠ 0 ∧ ρ - 1 ≠ 0 := by
  rcases hρ with ⟨hσ_pos, hσ_lt, _⟩
  refine ⟨?_, ?_⟩
  · intro h
    have : ρ.re = 0 := by rw [h]; simp
    linarith
  · intro h
    have : ρ = 1 := by linear_combination h
    have : ρ.re = 1 := by rw [this]; simp
    linarith

#print axioms nontrivialZero_ne_zero_and_one

/-- **Product `ρ · (ρ − 1)` has positive norm-square on nontrivial zeros.** -/
theorem nontrivialZero_pair_normSq_pos {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    0 < Complex.normSq (ρ * (ρ - 1)) := by
  obtain ⟨hρ0, hρ1⟩ := nontrivialZero_ne_zero_and_one hρ
  exact Complex.normSq_pos.mpr (mul_ne_zero hρ0 hρ1)

#print axioms nontrivialZero_pair_normSq_pos

/-- **Im-quartic decay target (strictly stronger).** States: there is
a constant `C ≥ 0` such that

```
‖pairTestMellin β ρ‖ ≤ C / (1 + (Im ρ)²)²     for every nontrivial zero ρ.
```

This is **strictly stronger** than `pairTestMellin_decay_target β`: an
algebraic bound `(1 + (Im ρ)²)^2 ≥ normSq (ρ · (ρ − 1))` lets us convert
this into the Jensen form.

**Analytic content.** Discharging this requires showing that the Mellin
transform `pairTestMellin β (σ + iT)` decays like `|T|^{−4}` as `|T| → ∞`,
uniformly for `σ` in any compact subset of `(0, 1)`. This follows from
four-step integration by parts: since `pair_cosh_gauss_test β t` is smooth
in `t` with Gaussian decay and vanishes to order 4 at `t = 0` (it equals
`4 · sinh² · sinh² · exp(−2t²)`), each IBP peels off a factor of
`|s|^{−1}` in the Mellin transform.  Four IBPs yield the quartic decay.

The IBP machinery is not yet formalized in Mathlib; this target sits on
top of that analytic infrastructure gap. -/
def pairTestMellin_im_quartic_decay_target (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros},
    ‖pairTestMellin β ρ.val‖ ≤ C / (1 + ρ.val.im^2)^2

#print axioms pairTestMellin_im_quartic_decay_target

/-- **Im-quartic decay implies Jensen-form decay.** The algebraic reduction:
any Im-quartic bound `‖pairTestMellin β ρ‖ ≤ C / (1 + (Im ρ)²)²` implies
the Jensen-compatible bound `‖pairTestMellin β ρ‖ ≤ C / normSq (ρ · (ρ−1))`,
via `normSq_pair_le_im_quartic`.

Combined with `WeilZeroSumTarget_of_decay`, this gives:

```
pairTestMellin_im_quartic_decay_target β → WeilZeroSumTarget β
```

unconditionally.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem pairTestMellin_decay_of_im_quartic (β : ℝ)
    (h : pairTestMellin_im_quartic_decay_target β) :
    pairTestMellin_decay_target β := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, ?_⟩
  intro ρ
  have hρ := ρ.property
  rcases hρ with ⟨hσ_pos, hσ_lt, _⟩
  have hquartic := hbound ρ
  have hNormSq_le : Complex.normSq (ρ.val * (ρ.val - 1)) ≤ (1 + ρ.val.im^2)^2 :=
    normSq_pair_le_im_quartic hσ_pos hσ_lt
  have hNormSq_pos : 0 < Complex.normSq (ρ.val * (ρ.val - 1)) :=
    nontrivialZero_pair_normSq_pos ρ.property
  have hT2_pos : 0 < (1 + ρ.val.im^2)^2 := by positivity
  -- Chain: ‖…‖ ≤ C/(1+T²)² ≤ C/normSq = C · 1/normSq
  have h1 : C / (1 + ρ.val.im^2)^2 ≤ C / Complex.normSq (ρ.val * (ρ.val - 1)) :=
    div_le_div_of_nonneg_left hC hNormSq_pos hNormSq_le
  calc ‖pairTestMellin β ρ.val‖
      ≤ C / (1 + ρ.val.im^2)^2 := hquartic
    _ ≤ C / Complex.normSq (ρ.val * (ρ.val - 1)) := h1
    _ = C * (1 / Complex.normSq (ρ.val * (ρ.val - 1))) := by ring

#print axioms pairTestMellin_decay_of_im_quartic

/-- **Full Im-quartic closure.** Given the Im-quartic decay target,
`WeilZeroSumTarget` follows unconditionally via the algebraic reduction
`pairTestMellin_decay_of_im_quartic` and `WeilZeroSumTarget_of_decay`.

This is the cleanest structural statement: the entire analytic burden is
isolated in `pairTestMellin_im_quartic_decay_target β`, which asks for a
quartic Im-decay rate on vertical lines — a standard consequence of
four-step integration by parts applied to the Gaussian-profile integrand.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem WeilZeroSumTarget_of_im_quartic_decay (β : ℝ)
    (h : pairTestMellin_im_quartic_decay_target β) : WeilZeroSumTarget β :=
  WeilZeroSumTarget_of_decay β (pairTestMellin_decay_of_im_quartic β h)

#print axioms WeilZeroSumTarget_of_im_quartic_decay

end Contour
end WeilPositivity
end ZD

end
