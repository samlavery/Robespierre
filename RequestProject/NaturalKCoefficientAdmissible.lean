import Mathlib
import RequestProject.OfflineDetectorProofUnconditional
import RequestProject.WeilFinalAssemblyUnconditional
import RequestProject.CauchyKExtractionViaBetaTower
import RequestProject.CoshZetaSymmetry
import RequestProject.ZeroCountJensen
import RequestProject.PairTestMellinAnalytic
import RequestProject.PairTestMellinUniformBound

/-!
# Q2: Admissibility of `a = K` for the pair-cosh detector

The natural K-twisted coefficient class for the project's Cauchy/Weil
extraction route is

```
a_K ρ := GaussianDefectCoefficient_local ρ
       = π·√(π/2)·(exp(δ_ρ²/2) − 2 exp(δ_ρ²/8) + 1)   on NTZ, with δ = ρ.re − 1/2
       = 0                                              off NTZ
```

— **no multiplicity weight**.  The project's `CauchyWeilGaussianDefectVanishing_target_local`
states the engineering identity as `Σ_ρ K(ρ) · pairTestMellin β ρ = 0`,
the sum running over distinct nontrivial zeros via the subtype, with no
`xiOrderNat` factor.  The earlier draft of this file mistakenly
introduced `n · K` weighting; that is the wrong target for the K-route.

## Status of each PairCoshDetectorAdmissible field for `a_K`

| Field | Status | Lemma |
|-------|--------|-------|
| `per_beta_summable` | **Proved** | `a_K_per_beta_summable` |
| `locally_uniform_beta_summable` | Open | `a_K_locally_uniform_beta_summable_target` |
| `beta_analytic_tsum` | Open | `a_K_beta_analytic_tsum_target` |
| `symmetry_compatible` | **Proved** | `a_K_symmetry_compatible` |
| `no_detector_blind_spot` | Open | `a_K_no_detector_blind_spot_target` |

Field 4 (`symmetry_compatible`) is **fully proved** here without any
`xiOrderNat` symmetry obligations — the K-route's per-zero coefficient
depends only on `Re ρ` and is FE+conj-symmetric purely from the K closed
form.  Multiplicity does not appear, so the question of `xiOrderNat`
conjugation symmetry never arises.

## Operational consequence for the orbit-vs-zero question

Since `a_K(ρ) = a_K(1 - star ρ)`, the natural coefficient class is
**constant on FE-conj orbits** of NTZ.  Each orbit `{ρ, 1-ρ, ρ̄, 1-ρ̄}`
carries a single value of `a_K`.  The engineering identity therefore
constrains orbit-level aggregates of `pairTestMellin`, not individual
per-zero values.  Field 5 should target ORBIT-LEVEL separation, not
individual-zero separation.

## What this file uses

* `gaussianDefectCoefficientBound` and `norm_gaussianDefectCoefficient_le_bound`
  from `OfflineDetectorProofUnconditional.lean`.
* `weilZeroSumTarget_unconditional` (un-weighted summability) from
  `WeilFinalAssembly.lean`.
* `riemannZeta_conj` from `CoshZetaSymmetry.lean`.
* `riemannZeta_one_sub` from mathlib.
* `gaussianDefectEntireKernel_FE` from `CauchyWeilDefectScratch.lean`
  (implicitly, via the closed-form algebra).

Axiom footprint of all proved theorems: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 800000

open Complex Real Set Filter MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint
namespace BetaTower

/-! ## The natural K-twisted coefficient -/

open Classical in
/-- The natural K-twisted coefficient `a_K ρ := GaussianDefectCoefficient_local ρ`,
extended by zero off `NontrivialZeros`. -/
def a_K : ℂ → ℂ := fun ρ =>
  if ρ ∈ ZD.NontrivialZeros then GaussianDefectCoefficient_local ρ else 0

/-- For `ρ ∈ NontrivialZeros`, `a_K ρ` evaluates to `K(ρ)`. -/
theorem a_K_eq_of_mem
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) :
    a_K ρ.val = GaussianDefectCoefficient_local ρ.val := by
  unfold a_K
  rw [if_pos ρ.property]

/-! ## Field 1 (proved): `per_beta_summable`

For each `β ∈ (0,1)`, `Σ_ρ ‖a_K(ρ) · pairTestMellin β ρ‖` is summable.
Discharge: `‖K(ρ)‖ ≤ K_bound` uniformly + `Σ ‖pairTestMellin β ρ‖`
summable (via `weilZeroSumTarget_unconditional` + quartic decay
+ Jensen). -/

theorem a_K_per_beta_summable :
    ∀ β : ℝ, 0 < β → β < 1 →
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        ‖a_K ρ.val * Contour.pairTestMellin β ρ.val‖) := by
  intro β _hβ_pos _hβ_lt
  -- Bound K · M norm by K_bound · ‖M‖.
  set K_bd : ℝ := gaussianDefectCoefficientBound with hK_bd_def
  have hK_nn : 0 ≤ K_bd := gaussianDefectCoefficientBound_nonneg
  -- ‖pairTestMellin β ρ‖ summable.
  have h_pair_norm_summable :
      Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        ‖Contour.pairTestMellin β ρ.val‖) :=
    (Contour.weilZeroSumTarget_unconditional β).norm
  -- Bound each summand.
  have h_bd : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ‖a_K ρ.val * Contour.pairTestMellin β ρ.val‖ ≤
      K_bd * ‖Contour.pairTestMellin β ρ.val‖ := by
    intro ρ
    rw [a_K_eq_of_mem ρ, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_gaussianDefectCoefficient_le_bound ρ) (norm_nonneg _)
  exact (h_pair_norm_summable.mul_left K_bd).of_nonneg_of_le
    (fun _ => norm_nonneg _) h_bd

/-! ## Field 4 (proved): `symmetry_compatible`

`a_K ρ = a_K (1 - star ρ)`.  Discharged from:
* K-symmetry: `K(1 - star ρ) = K(ρ)`. **Proved**: K depends only on
  `Re ρ`, and the closed form `(exp(δ²/2) - 2·exp(δ²/8) + 1)` with
  `δ = Re ρ - 1/2` is even under `Re ρ ↔ 1 - Re ρ`.
* NTZ closure: `ρ ∈ NTZ ⟹ 1 - star ρ ∈ NTZ`.  **Proved**: combines
  `riemannZeta_conj` + `riemannZeta_one_sub`. -/

/-- K-symmetry on the real axis: `K(1 - star ρ) = K(ρ)`. -/
theorem GaussianDefectCoefficient_FE_conj_sym (ρ : ℂ) :
    GaussianDefectCoefficient_local (1 - (starRingEnd ℂ ρ)) =
      GaussianDefectCoefficient_local ρ := by
  unfold GaussianDefectCoefficient_local
  have h_re : (1 - (starRingEnd ℂ ρ)).re = 1 - ρ.re := by
    simp [Complex.sub_re, Complex.one_re]
  rw [h_re]
  have h_eq : ZD.averageEnergyDefect ZD.gaussianKernel (1 - ρ.re) =
              ZD.averageEnergyDefect ZD.gaussianKernel ρ.re := by
    show ZD.averageEnergyDefect ZD.ψ_gaussian (1 - ρ.re) =
         ZD.averageEnergyDefect ZD.ψ_gaussian ρ.re
    rw [ZD.averageEnergyDefect_gaussian_closed_form (1 - ρ.re)]
    rw [ZD.averageEnergyDefect_gaussian_closed_form ρ.re]
    have hsq : ((1 - ρ.re) - 1/2)^2 = (ρ.re - 1/2)^2 := by ring
    rw [hsq]
  rw [h_eq]

/-- NTZ is closed under `1 - star ·`. -/
theorem NTZ_closed_under_FE_conj
    (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    (1 - (starRingEnd ℂ ρ)) ∈ ZD.NontrivialZeros := by
  obtain ⟨hρ_pos, hρ_lt, hρ_zero⟩ := hρ
  have h_re : (1 - (starRingEnd ℂ) ρ).re = 1 - ρ.re := by
    simp [Complex.sub_re, Complex.one_re]
  refine ⟨?_, ?_, ?_⟩
  · rw [h_re]; linarith
  · rw [h_re]; linarith
  · -- ζ(1 - star ρ) = (prefactor) · ζ(star ρ) = (prefactor) · 0 = 0.
    have hρ_ne_one : ρ ≠ 1 := by
      intro h_eq; rw [h_eq] at hρ_lt; simp at hρ_lt
    have h_zeta_star_zero : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by
      rw [CoshZetaSymmetry.riemannZeta_conj ρ hρ_ne_one]
      rw [hρ_zero, map_zero]
    have h_star_re_eq : ((starRingEnd ℂ) ρ).re = ρ.re := by simp
    have h_star_ne_one : (starRingEnd ℂ) ρ ≠ 1 := by
      intro h_eq
      have : ((starRingEnd ℂ) ρ).re = 1 := by rw [h_eq]; simp
      rw [h_star_re_eq] at this; linarith
    have h_star_ne_neg_n : ∀ n : ℕ, (starRingEnd ℂ) ρ ≠ -(n : ℂ) := by
      intro n h_eq
      have h_re_eq : ((starRingEnd ℂ) ρ).re = (-(n:ℂ)).re := by rw [h_eq]
      simp at h_re_eq
      have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    have h_FE := riemannZeta_one_sub h_star_ne_neg_n h_star_ne_one
    rw [h_FE, h_zeta_star_zero, mul_zero]

/-- **Field 4 — `a_K` is FE+conj-symmetric.** -/
theorem a_K_symmetry_compatible :
    ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      a_K ρ.val = a_K (1 - (starRingEnd ℂ ρ.val)) := by
  intro ρ
  have h_in : (1 - (starRingEnd ℂ ρ.val)) ∈ ZD.NontrivialZeros :=
    NTZ_closed_under_FE_conj ρ.val ρ.property
  rw [a_K_eq_of_mem ρ]
  unfold a_K
  rw [if_pos h_in]
  exact (GaussianDefectCoefficient_FE_conj_sym ρ.val).symm

/-! ## Fields 2, 3, 5 — open obligations -/

/-- **Field 2 — locally uniform β-summability.** -/
def a_K_locally_uniform_beta_summable_target : Prop :=
  ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioo (0 : ℝ) 1 →
    ∃ u : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℝ,
      Summable u ∧ ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, ∀ β ∈ K,
        ‖a_K ρ.val * Contour.pairTestMellin β ρ.val‖ ≤ u ρ

/-- **Field 3 — β-tsum analytic on `Set.univ`.** -/
def a_K_beta_analytic_tsum_target : Prop :=
  AnalyticOnNhd ℝ
    (fun β : ℝ => ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      a_K ρ.val * Contour.pairTestMellin β ρ.val) Set.univ

/-! ### Field 2 reduction to a uniform-in-β quartic decay claim

Field 2 reduces to: for every compact `K ⊆ (0,1)`, there is a uniform
constant `C_K` such that

```
‖pairTestMellin β ρ‖ ≤ C_K · 1/‖ρ·(ρ-1)‖²   for all β ∈ K, ρ ∈ NTZ.
```

The right-hand side `1/‖ρ·(ρ-1)‖²` is summable over NTZ by Jensen's
estimate (`nontrivialZeros_inv_sq_summable`).  Combined with the
universal K-bound `‖K(ρ)‖ ≤ K_bound`, this gives the locally uniform
majorant.

The uniform decay is plausibly derivable from the project's existing
fixed-β quartic decay via continuity of the constant in β + compactness,
but is currently named as the irreducible obligation. -/

/-- **Uniform quartic decay target** — single isolated obligation
underlying Field 2. -/
def pairTestMellin_uniform_quartic_decay_target : Prop :=
  ∀ (K : Set ℝ), IsCompact K → K ⊆ Set.Ioo (0 : ℝ) 1 →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ β ∈ K, ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        ‖Contour.pairTestMellin β ρ.val‖ ≤
          C * (1 / Complex.normSq (ρ.val * (ρ.val - 1)))

/-- **Icc-form uniform quartic decay** — easier-to-prove version (interval
bounds rather than arbitrary compacts).  Compact ⊆ Ioo (0,1) reduces to
some Icc, so this implies the general form. -/
def pairTestMellin_uniform_quartic_decay_on_Icc_target : Prop :=
  ∀ β₀ β₁ : ℝ, 0 < β₀ → β₀ ≤ β₁ → β₁ < 1 →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ β ∈ Set.Icc β₀ β₁, ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        ‖Contour.pairTestMellin β ρ.val‖ ≤
          C * (1 / Complex.normSq (ρ.val * (ρ.val - 1)))

/-- **Reduction: Icc-form ⟹ general-compact form.**  Any compact subset
of `(0,1)` is contained in some `Icc β₀ β₁` with `0 < β₀ ≤ β₁ < 1`
(via `IsCompact.bddBelow`/`bddAbove` + sInf/sSup ∈ K). -/
theorem pairTestMellin_uniform_quartic_decay_target_of_Icc
    (h_Icc : pairTestMellin_uniform_quartic_decay_on_Icc_target) :
    pairTestMellin_uniform_quartic_decay_target := by
  intro K hK_compact hK_sub
  by_cases hK_empty : K = ∅
  · -- Empty K: vacuous bound with C = 0.
    refine ⟨0, le_refl _, ?_⟩
    intro β hβ; rw [hK_empty] at hβ; exact absurd hβ (Set.notMem_empty β)
  -- Nonempty K: extract sInf K, sSup K ∈ K via compactness.
  have hK_nonempty : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  obtain ⟨β₀, hβ₀_in, hβ₀_min⟩ := hK_compact.exists_isLeast hK_nonempty
  obtain ⟨β₁, hβ₁_in, hβ₁_max⟩ := hK_compact.exists_isGreatest hK_nonempty
  -- β₀, β₁ ∈ K ⊂ (0,1).
  have hβ₀_pos : 0 < β₀ := (hK_sub hβ₀_in).1
  have hβ₀_lt : β₀ < 1 := (hK_sub hβ₀_in).2
  have hβ₁_pos : 0 < β₁ := (hK_sub hβ₁_in).1
  have hβ₁_lt : β₁ < 1 := (hK_sub hβ₁_in).2
  have hβ₀_le_β₁ : β₀ ≤ β₁ := hβ₁_max hβ₀_in
  -- Apply Icc version.
  obtain ⟨C, hC_nn, h_bd⟩ := h_Icc β₀ β₁ hβ₀_pos hβ₀_le_β₁ hβ₁_lt
  refine ⟨C, hC_nn, ?_⟩
  intro β hβ ρ
  exact h_bd β ⟨hβ₀_min hβ, hβ₁_max hβ⟩ ρ


/-- **Field 2 (conditional discharge):** locally uniform summability
follows from the uniform quartic decay + the K-bound + Jensen
summability. -/
theorem a_K_locally_uniform_beta_summable_of_uniform_decay
    (h_unif : pairTestMellin_uniform_quartic_decay_target) :
    a_K_locally_uniform_beta_summable_target := by
  intro K hK_compact hK_sub
  obtain ⟨C_M, hC_nn, h_bd⟩ := h_unif K hK_compact hK_sub
  set K_bd : ℝ := gaussianDefectCoefficientBound with hK_bd_def
  have hK_bd_nn : 0 ≤ K_bd := gaussianDefectCoefficientBound_nonneg
  set u : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℝ := fun ρ =>
    K_bd * C_M * (1 / Complex.normSq (ρ.val * (ρ.val - 1)))
    with hu_def
  refine ⟨u, ?_, ?_⟩
  · -- Summability via Jensen.
    have h_jensen :
        Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
          1 / Complex.normSq (ρ.val * (ρ.val - 1))) :=
      Contour.nontrivialZeros_inv_sq_summable_reexport
    have : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
        K_bd * C_M *
          (1 / Complex.normSq (ρ.val * (ρ.val - 1)))) :=
      h_jensen.mul_left (K_bd * C_M)
    exact this
  · intro ρ β hβ
    rw [a_K_eq_of_mem ρ, norm_mul]
    have h_K : ‖GaussianDefectCoefficient_local ρ.val‖ ≤ K_bd :=
      norm_gaussianDefectCoefficient_le_bound ρ
    have h_M : ‖Contour.pairTestMellin β ρ.val‖ ≤
        C_M * (1 / Complex.normSq (ρ.val * (ρ.val - 1))) :=
      h_bd β hβ ρ
    have h_M_rhs_nn : 0 ≤ C_M * (1 / Complex.normSq (ρ.val * (ρ.val - 1))) := by
      apply mul_nonneg hC_nn
      apply div_nonneg (by norm_num)
      exact Complex.normSq_nonneg _
    calc ‖GaussianDefectCoefficient_local ρ.val‖ *
            ‖Contour.pairTestMellin β ρ.val‖
        ≤ K_bd * (C_M * (1 / Complex.normSq (ρ.val * (ρ.val - 1)))) :=
          mul_le_mul h_K h_M (norm_nonneg _) hK_bd_nn
      _ = u ρ := by show _ = K_bd * C_M * (1 / Complex.normSq (ρ.val * (ρ.val - 1))); ring

/-- **Field 2 from Icc form:** convenience wrapper. -/
theorem a_K_locally_uniform_beta_summable_of_Icc
    (h_Icc : pairTestMellin_uniform_quartic_decay_on_Icc_target) :
    a_K_locally_uniform_beta_summable_target :=
  a_K_locally_uniform_beta_summable_of_uniform_decay
    (pairTestMellin_uniform_quartic_decay_target_of_Icc h_Icc)

/-- **Field 2, unconditional discharge.**  The Icc-form uniform quartic
decay `pairTestMellin_uniform_quartic_decay_on_Icc_holds` (proved in
`PairTestMellinUniformBound`) feeds the conditional discharge to give
`a_K`'s locally uniform β-summability outright. -/
theorem a_K_locally_uniform_beta_summable_holds :
    a_K_locally_uniform_beta_summable_target :=
  a_K_locally_uniform_beta_summable_of_Icc
    (h_Icc :=
      (show pairTestMellin_uniform_quartic_decay_on_Icc_target from
        pairTestMellin_uniform_quartic_decay_on_Icc_holds))

/-- **Field 5 — no detector blind spot.**  For every `ρ ∈ NTZ`, there
exists `β ∈ (0,1)` with `pairTestMellin(β, ρ) ≠ 0`. -/
def a_K_no_detector_blind_spot_target : Prop :=
  ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
    ∃ β : ℝ, 0 < β ∧ β < 1 ∧ Contour.pairTestMellin β ρ.val ≠ 0

/-! ### Field 5 reduction to a single computational obligation

The detector-blind-spot condition reduces to: for each `ρ ∈ NTZ`, the
β-function `β ↦ pairTestMellin(β, ρ)` is **not identically zero on ℝ**.

This reduction uses:
* `pairTestMellin_analyticOnNhd_in_beta` — `pairTestMellin(·, ρ)` is
  real-analytic on `Set.univ` for `ρ.re > 0`.
* The identity theorem on `ℝ`
  (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`):
  a real-analytic function on the connected set `ℝ` that vanishes on a
  neighborhood of any point vanishes everywhere. -/

/-- The irreducible computational content for Field 5: for each
`ρ ∈ NTZ`, the β-function is not identically zero on ℝ. -/
def pairTestMellin_not_identically_zero_target : Prop :=
  ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
    ∃ β : ℝ, Contour.pairTestMellin β ρ.val ≠ 0

/-- A stronger (and more uniformly tractable) target: as `β → +∞`, the
norm `‖pairTestMellin(β, ρ)‖` tends to infinity.  The asymptotic is

```
|pairTestMellin(β, ρ)| ~ const(ρ) · (β−1/2)^? · exp((β−1/2)²/2)   as β → ∞
```

via the saddle-point of `sinh²((β−1/2)t)·exp(-2t²)` at `t* = (β−1/2)/2`.
The leading term has nonzero coefficient uniformly for `0 < Re ρ < 1`,
so the asymptotic is robust against complex-Mellin accidental
cancellations (the failure mode of routes (b)/(c)). -/
def pairTestMellin_grows_at_infty_target : Prop :=
  ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
    Filter.Tendsto (fun β : ℝ => ‖Contour.pairTestMellin β ρ.val‖)
      Filter.atTop Filter.atTop

/-- **Reduction step:** growth-at-infinity ⟹ not-identically-zero. -/
theorem pairTestMellin_not_identically_zero_of_grows_at_infty
    (h_grow : pairTestMellin_grows_at_infty_target) :
    pairTestMellin_not_identically_zero_target := by
  intro ρ
  -- ‖pairTestMellin β ρ‖ → ∞, so eventually > 1, in particular > 0,
  -- in particular non-zero.
  have h_tendsto := h_grow ρ
  -- Eventually `‖pairTestMellin β ρ‖ > 0`.
  have h_eventually : ∀ᶠ β : ℝ in Filter.atTop,
      ‖Contour.pairTestMellin β ρ.val‖ > 0 := by
    have h_one : ∀ᶠ β : ℝ in Filter.atTop,
        ‖Contour.pairTestMellin β ρ.val‖ ≥ 1 :=
      h_tendsto (Filter.eventually_ge_atTop 1)
    filter_upwards [h_one] with β hβ; linarith
  -- Pick any β with the property.
  obtain ⟨β, hβ⟩ := h_eventually.exists
  refine ⟨β, ?_⟩
  intro h_eq
  rw [h_eq, norm_zero] at hβ
  linarith

/-- Helper: if a real-analytic function on `ℝ` is non-zero at some
point, it is non-zero at some point in any non-trivial open interval. -/
private lemma exists_nonzero_in_Ioo_of_analytic
    (f : ℝ → ℂ) (h_anal : AnalyticOnNhd ℝ f Set.univ)
    (β₀ : ℝ) (h_nonzero : f β₀ ≠ 0)
    (a b : ℝ) (hab : a < b) :
    ∃ β ∈ Set.Ioo a b, f β ≠ 0 := by
  by_contra h_no
  push_neg at h_no
  -- Pick midpoint of (a, b).
  set m : ℝ := (a + b) / 2 with hm_def
  have hm_in : m ∈ Set.Ioo a b := by
    refine ⟨?_, ?_⟩ <;> · rw [hm_def]; linarith
  -- f =ᶠ[nhds m] 0 because f vanishes on (a, b), an open nbhd of m.
  have h_open : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have h_ev_zero : f =ᶠ[nhds m] 0 := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨Set.Ioo a b, h_open.mem_nhds hm_in, fun β hβ => h_no β hβ⟩
  -- Apply identity theorem on connected ℝ.
  have h_id_zero := h_anal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ m) h_ev_zero
  exact h_nonzero (h_id_zero (Set.mem_univ β₀))

/-- **Field 5 (conditional discharge).**  Given the not-identically-zero
obligation, `a_K_no_detector_blind_spot_target` follows. -/
theorem a_K_no_detector_blind_spot_of_not_id_zero
    (h_obligation : pairTestMellin_not_identically_zero_target) :
    a_K_no_detector_blind_spot_target := by
  intro ρ
  obtain ⟨β₀, hβ₀⟩ := h_obligation ρ
  have hρ_re_pos : 0 < ρ.val.re := ρ.property.1
  have h_anal : AnalyticOnNhd ℝ (fun β : ℝ => Contour.pairTestMellin β ρ.val)
      Set.univ :=
    Contour.pairTestMellin_analyticOnNhd_in_beta hρ_re_pos
  obtain ⟨β, hβ_in, hβ_ne⟩ := exists_nonzero_in_Ioo_of_analytic
    (fun β : ℝ => Contour.pairTestMellin β ρ.val) h_anal β₀ hβ₀ 0 1 (by norm_num)
  exact ⟨β, hβ_in.1, hβ_in.2, hβ_ne⟩

/-- **Composite reduction (Field 5 from growth):** the recommended
discharge route — Field 5 follows from `pairTestMellin_grows_at_infty_target`. -/
theorem a_K_no_detector_blind_spot_of_grows_at_infty
    (h_grow : pairTestMellin_grows_at_infty_target) :
    a_K_no_detector_blind_spot_target :=
  a_K_no_detector_blind_spot_of_not_id_zero
    (pairTestMellin_not_identically_zero_of_grows_at_infty h_grow)

/-! ### Field 3 reduction to a Weierstrass-style claim

Field 3 — `β ↦ Σ' a_K(ρ) · pairTestMellin β ρ` is real-analytic on
`Set.univ` — reduces to a generic tsum-analyticity claim:

> Sum of real-analytic functions, with locally uniform summability on
> compacts, is real-analytic.

This is the Weierstrass theorem in the real-analytic setting.  The
project's individual summands `a_K(ρ) · pairTestMellin(·, ρ)` are
real-analytic via `pairTestMellin_analyticOnNhd_in_beta`.  Locally
uniform summability on compacts in `ℝ` (a Set.univ-strengthening of
Field 2 — currently Field 2 is only on `(0,1)`-compacts) provides the
M-test majorant.

Discharge route: extend Field 2 to all `ℝ`-compacts via the same
quartic-decay argument (the K-bound is uniform; the quartic decay holds
for any β with explicit polynomial constant in β, hence is bounded on
any compact β-set).  Combine with a Weierstrass step. -/

/-- **Generic Weierstrass-style obligation** for the K-route's tsum
analyticity.  The real-analytic tsum theorem: locally uniform
summability + each summand real-analytic ⟹ tsum real-analytic.

Stated specifically for our setting (NTZ subtype + Set.univ).  The
generic version of this should be in mathlib but is currently
referenced as an obligation. -/
def tsum_analytic_pairTestMellin_target : Prop :=
  (∀ K : Set ℝ, IsCompact K →
    ∃ u : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℝ,
      Summable u ∧ ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, ∀ β ∈ K,
        ‖a_K ρ.val * Contour.pairTestMellin β ρ.val‖ ≤ u ρ) →
  a_K_beta_analytic_tsum_target

/-- **Field 3 (conditional discharge):** β-tsum analytic follows from
the Weierstrass step + locally uniform summability on all of `ℝ`. -/
theorem a_K_beta_analytic_tsum_of_obligations
    (h_unif_full :
      ∀ K : Set ℝ, IsCompact K →
        ∃ u : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℝ,
          Summable u ∧ ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, ∀ β ∈ K,
            ‖a_K ρ.val * Contour.pairTestMellin β ρ.val‖ ≤ u ρ)
    (h_weierstrass : tsum_analytic_pairTestMellin_target) :
    a_K_beta_analytic_tsum_target :=
  h_weierstrass h_unif_full

/-- **Field 3 — locally uniform majorant on every real compact** —
the `h_unif_full` half of the Field-3 obligations, proved unconditionally
via `pairTestMellin_uniform_quartic_decay_on_compact_holds` together
with the K-bound and Jensen summability.  Combined with the Weierstrass
step, this fully discharges Field 3. -/
theorem a_K_locally_uniform_majorant_on_real_compact_holds
    (K : Set ℝ) (hK : IsCompact K) :
    ∃ u : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℝ,
      Summable u ∧ ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, ∀ β ∈ K,
        ‖a_K ρ.val * Contour.pairTestMellin β ρ.val‖ ≤ u ρ := by
  obtain ⟨C_M, hC_nn, h_bd⟩ :=
    pairTestMellin_uniform_quartic_decay_on_compact_holds K hK
  set K_bd : ℝ := gaussianDefectCoefficientBound with hK_bd_def
  have hK_bd_nn : 0 ≤ K_bd := gaussianDefectCoefficientBound_nonneg
  set u : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℝ := fun ρ =>
    K_bd * C_M * (1 / Complex.normSq (ρ.val * (ρ.val - 1)))
    with hu_def
  refine ⟨u, ?_, ?_⟩
  · have h_jensen :
        Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
          1 / Complex.normSq (ρ.val * (ρ.val - 1))) :=
      Contour.nontrivialZeros_inv_sq_summable_reexport
    exact h_jensen.mul_left (K_bd * C_M)
  · intro ρ β hβ
    rw [a_K_eq_of_mem ρ, norm_mul]
    have h_K : ‖GaussianDefectCoefficient_local ρ.val‖ ≤ K_bd :=
      norm_gaussianDefectCoefficient_le_bound ρ
    have h_M : ‖Contour.pairTestMellin β ρ.val‖ ≤
        C_M * (1 / Complex.normSq (ρ.val * (ρ.val - 1))) :=
      h_bd β hβ ρ
    calc ‖GaussianDefectCoefficient_local ρ.val‖ *
            ‖Contour.pairTestMellin β ρ.val‖
        ≤ K_bd * (C_M * (1 / Complex.normSq (ρ.val * (ρ.val - 1)))) :=
          mul_le_mul h_K h_M (norm_nonneg _) hK_bd_nn
      _ = u ρ := by show _ = K_bd * C_M * (1 / Complex.normSq (ρ.val * (ρ.val - 1))); ring

/-- **Field 3 from the Weierstrass step alone.**  Once the
real-analytic Weierstrass theorem is provided, Field 3 is fully
discharged — the locally-uniform majorant is now unconditional. -/
theorem a_K_beta_analytic_tsum_of_weierstrass
    (h_weierstrass : tsum_analytic_pairTestMellin_target) :
    a_K_beta_analytic_tsum_target :=
  a_K_beta_analytic_tsum_of_obligations
    a_K_locally_uniform_majorant_on_real_compact_holds h_weierstrass

/-! ## Composite admissibility -/

/-- **Composite admissibility of `a_K`** — assembles the proved fields
(1, 4) with the three open obligations (2, 3, 5). -/
theorem a_K_PairCoshDetectorAdmissible_of_open_obligations
    (h_loc_uniform : a_K_locally_uniform_beta_summable_target)
    (h_beta_analytic : a_K_beta_analytic_tsum_target)
    (h_no_blind : a_K_no_detector_blind_spot_target) :
    PairCoshDetectorAdmissible a_K :=
  { per_beta_summable := a_K_per_beta_summable
    locally_uniform_beta_summable := h_loc_uniform
    beta_analytic_tsum := h_beta_analytic
    symmetry_compatible := a_K_symmetry_compatible
    no_detector_blind_spot := h_no_blind }

/-- **The two remaining open obligations for the K-twisted coefficient
class to discharge `PairCoshDetectorSeparatesKCoeff_target`** (after
Field 2 was discharged via `a_K_locally_uniform_beta_summable_holds`). -/
def a_K_admissibility_open_obligations : Prop :=
  a_K_beta_analytic_tsum_target ∧
  a_K_no_detector_blind_spot_target

/-- **Admissibility of `a_K` from the two remaining open obligations.**
Fields 1, 2, 4 are now unconditional; only Field 3 (`beta_analytic_tsum`)
and Field 5 (`no_detector_blind_spot`) remain. -/
theorem a_K_PairCoshDetectorAdmissible_of_two_open
    (h_beta_analytic : a_K_beta_analytic_tsum_target)
    (h_no_blind : a_K_no_detector_blind_spot_target) :
    PairCoshDetectorAdmissible a_K :=
  a_K_PairCoshDetectorAdmissible_of_open_obligations
    a_K_locally_uniform_beta_summable_holds h_beta_analytic h_no_blind

/-- **Refined admissibility headline:** the only remaining obligations
beyond the unconditional Fields 1, 2, 4 are the **Weierstrass step**
(Field 3's analytic-tsum hypothesis) and the **growth at infinity**
(Field 5's reduction).  All locally-uniform majorant content is now
unconditional. -/
theorem a_K_PairCoshDetectorAdmissible_of_weierstrass_and_growth
    (h_weierstrass : tsum_analytic_pairTestMellin_target)
    (h_grow : pairTestMellin_grows_at_infty_target) :
    PairCoshDetectorAdmissible a_K :=
  a_K_PairCoshDetectorAdmissible_of_two_open
    (a_K_beta_analytic_tsum_of_weierstrass h_weierstrass)
    (a_K_no_detector_blind_spot_of_grows_at_infty h_grow)

#print axioms a_K_per_beta_summable
#print axioms GaussianDefectCoefficient_FE_conj_sym
#print axioms NTZ_closed_under_FE_conj
#print axioms a_K_symmetry_compatible
#print axioms a_K_locally_uniform_beta_summable_of_uniform_decay
#print axioms pairTestMellin_uniform_quartic_decay_target_of_Icc
#print axioms a_K_locally_uniform_beta_summable_of_Icc
#print axioms a_K_beta_analytic_tsum_of_obligations
#print axioms a_K_no_detector_blind_spot_of_not_id_zero
#print axioms pairTestMellin_not_identically_zero_of_grows_at_infty
#print axioms a_K_no_detector_blind_spot_of_grows_at_infty
#print axioms a_K_PairCoshDetectorAdmissible_of_open_obligations
#print axioms a_K_locally_uniform_beta_summable_holds
#print axioms a_K_locally_uniform_majorant_on_real_compact_holds
#print axioms a_K_beta_analytic_tsum_of_weierstrass
#print axioms a_K_PairCoshDetectorAdmissible_of_two_open
#print axioms a_K_PairCoshDetectorAdmissible_of_weierstrass_and_growth

end BetaTower
end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end
