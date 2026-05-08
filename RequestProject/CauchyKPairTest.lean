import Mathlib
import RequestProject.CauchyKPerC
import RequestProject.WeilExplicitFormulaFromPerC

/-!
# K-twisted rectangle Cauchy for `weilIntegrand (pairTestMellin β)`

For any entire `K : ℂ → ℂ`, real `β ∈ Ioo 0 1`, and `goodHeight T` with `1 < T`:
```
∮_{[-1,2]×[-T,T]} K(s) · weilIntegrand (pairTestMellin β) s ds =
  2πi · (K(1) · pairTestMellin β 1 − Σ_{ρ ∈ Z} K(ρ) · n(ρ) · pairTestMellin β ρ)
```

The `negLogDerivZeta0K · K 0` residue at `s = 0` from the per-c result
cancels out: weights `{1/2, 1/2, -1, -1, 1}` sum to 0.

Strategy: weight-sum the K-twisted per-c result over the 5 c-values
of `pairTestMellin_eq_sum_coshGaussMellinExt` and do the same boundary
linearity argument as `rectangleResidueIdentity_from_perC`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

set_option maxHeartbeats 1600000

open Complex Set Filter MeasureTheory BigOperators

noncomputable section

namespace ZD
namespace WeilPositivity
namespace OfflineDetectorEndpoint
namespace Scratch

open ZD.WeilPositivity.Contour
open ZD.WeilPositivity.FinalAssembly
open ZD.CoshGaussMellinContinuation

/-- **K-twisted Weil identity at finite `T` for `pairTestMellin β`.**

For entire `K`, `β ∈ Ioo 0 1`, `1 < T`, and `goodHeight T`,
```
∮_{[-1,2]×[-T,T]} K(s) · weilIntegrand (pairTestMellin β) s ds =
  2πi · (K(1) · pairTestMellin β 1 − Σ_{ρ ∈ Z} ((n ρ : ℕ) : ℂ) · K(ρ) · pairTestMellin β ρ)
```

Sums 5 K-twisted per-c rectangle Cauchy identities (from
`rectContourIntegral_K_neg_logDerivZeta_coshGaussExt_eq_residue_sum`)
with weights `{1/2, 1/2, -1, -1, 1}`.

Axiom footprint: `[propext, Classical.choice, Quot.sound]`. -/
theorem rectContourIntegral_K_neg_logDerivZeta_pairTestMellin_eq_residue_sum
    (K : ℂ → ℂ) (hK : Differentiable ℂ K)
    (β : ℝ) (_hβ : β ∈ Set.Ioo (0:ℝ) 1)
    {T : ℝ} (hT : 1 < T) (hGood : FinalAssembly.goodHeight T)
    (n : ℂ → ℕ) (Z : Finset ℂ)
    (hZ_mem : ∀ ρ ∈ Z,
      ρ ∈ NontrivialZeros ∧ -1 < ρ.re ∧ ρ.re < 2 ∧ -T < ρ.im ∧ ρ.im < T ∧
      analyticOrderAt riemannZeta ρ = (n ρ : ℕ∞))
    (hZ_complete : ∀ ρ : ℂ, ρ ∈ NontrivialZeros → -1 < ρ.re → ρ.re < 2 →
      -T < ρ.im → ρ.im < T → ρ ∈ Z) :
    rectContourIntegral (-1 : ℝ) 2 T
        (fun s => K s * weilIntegrand (Contour.pairTestMellin β) s) =
      2 * ((Real.pi : ℝ) : ℂ) * I *
        (K 1 * Contour.pairTestMellin β 1 -
          ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * K ρ * Contour.pairTestMellin β ρ) := by
  -- Step 1: K-twisted per-c identity at each of 5 c-values.
  have h_c1 := rectContourIntegral_K_neg_logDerivZeta_coshGaussExt_eq_residue_sum
    K hK (2*β - Real.pi/3) hT hGood n Z hZ_mem hZ_complete
  have h_c2 := rectContourIntegral_K_neg_logDerivZeta_coshGaussExt_eq_residue_sum
    K hK (2 - Real.pi/3 - 2*β) hT hGood n Z hZ_mem hZ_complete
  have h_c3 := rectContourIntegral_K_neg_logDerivZeta_coshGaussExt_eq_residue_sum
    K hK (1 - Real.pi/3) hT hGood n Z hZ_mem hZ_complete
  have h_c4 := rectContourIntegral_K_neg_logDerivZeta_coshGaussExt_eq_residue_sum
    K hK (2*β - 1) hT hGood n Z hZ_mem hZ_complete
  have h_c5 := rectContourIntegral_K_neg_logDerivZeta_coshGaussExt_eq_residue_sum
    K hK 0 hT hGood n Z hZ_mem hZ_complete
  -- Step 2: pairTestMellin β at s = 1 and at each ρ ∈ Z.
  have h_at1 : Contour.pairTestMellin β 1 =
      (1/2 : ℂ) * coshGaussMellinExt (2*β - Real.pi/3) 1 +
      (1/2 : ℂ) * coshGaussMellinExt (2 - Real.pi/3 - 2*β) 1 -
      coshGaussMellinExt (1 - Real.pi/3) 1 -
      coshGaussMellinExt (2*β - 1) 1 +
      coshGaussMellinExt 0 1 :=
    pairTestMellin_eq_sum_coshGaussMellinExt β (by norm_num)
  have h_at_rho : ∀ ρ ∈ Z, Contour.pairTestMellin β ρ =
      (1/2 : ℂ) * coshGaussMellinExt (2*β - Real.pi/3) ρ +
      (1/2 : ℂ) * coshGaussMellinExt (2 - Real.pi/3 - 2*β) ρ -
      coshGaussMellinExt (1 - Real.pi/3) ρ -
      coshGaussMellinExt (2*β - 1) ρ +
      coshGaussMellinExt 0 ρ := by
    intro ρ hρ
    obtain ⟨hNZ, _, _, _, _, _⟩ := hZ_mem ρ hρ
    exact pairTestMellin_eq_sum_coshGaussMellinExt β (by linarith [hNZ.1])
  -- Step 3: zero-sum expansion via linearity (K-twisted).
  have h_sum_eq :
      ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * K ρ * Contour.pairTestMellin β ρ =
      (1/2 : ℂ) * ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * K ρ * coshGaussMellinExt (2*β - Real.pi/3) ρ +
      (1/2 : ℂ) * ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * K ρ * coshGaussMellinExt (2 - Real.pi/3 - 2*β) ρ -
      ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * K ρ * coshGaussMellinExt (1 - Real.pi/3) ρ -
      ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * K ρ * coshGaussMellinExt (2*β - 1) ρ +
      ∑ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * K ρ * coshGaussMellinExt 0 ρ := by
    have h_term : ∀ ρ ∈ Z, ((n ρ : ℕ) : ℂ) * K ρ * Contour.pairTestMellin β ρ =
        (1/2:ℂ) * (((n ρ : ℕ) : ℂ) * K ρ * coshGaussMellinExt (2*β - Real.pi/3) ρ) +
        (1/2:ℂ) * (((n ρ : ℕ) : ℂ) * K ρ * coshGaussMellinExt (2 - Real.pi/3 - 2*β) ρ) -
        ((n ρ : ℕ) : ℂ) * K ρ * coshGaussMellinExt (1 - Real.pi/3) ρ -
        ((n ρ : ℕ) : ℂ) * K ρ * coshGaussMellinExt (2*β - 1) ρ +
        ((n ρ : ℕ) : ℂ) * K ρ * coshGaussMellinExt 0 ρ := fun ρ hρ => by
      rw [h_at_rho ρ hρ]; ring
    rw [Finset.sum_congr rfl h_term]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- Step 4: rectContourIntegral of K * weilIntegrand(pairTestMellin) =
  --         linear combination of K * weilIntegrand(coshGaussMellinExt cᵢ).
  -- Pointwise on rectangle (where Re s > -2):
  have h_ptwise_re : ∀ z : ℂ, -2 < z.re →
      K z * weilIntegrand (Contour.pairTestMellin β) z =
        (1/2 : ℂ) * (K z * weilIntegrand (coshGaussMellinExt (2*β - Real.pi/3)) z) +
        (1/2 : ℂ) * (K z * weilIntegrand (coshGaussMellinExt (2 - Real.pi/3 - 2*β)) z) -
        K z * weilIntegrand (coshGaussMellinExt (1 - Real.pi/3)) z -
        K z * weilIntegrand (coshGaussMellinExt (2*β - 1)) z +
        K z * weilIntegrand (coshGaussMellinExt 0) z := by
    intro z hz
    simp only [Contour.weilIntegrand]
    rw [pairTestMellin_eq_sum_coshGaussMellinExt β hz]
    ring
  -- Sketch: linearity over 4 boundary segments × 5 c-values, then ring.
  have h_integ_eq :
      rectContourIntegral (-1) 2 T (fun s => K s * weilIntegrand (Contour.pairTestMellin β) s) =
      (1/2 : ℂ) * rectContourIntegral (-1) 2 T
        (fun s => K s * weilIntegrand (coshGaussMellinExt (2*β - Real.pi/3)) s) +
      (1/2 : ℂ) * rectContourIntegral (-1) 2 T
        (fun s => K s * weilIntegrand (coshGaussMellinExt (2 - Real.pi/3 - 2*β)) s) -
      rectContourIntegral (-1) 2 T
        (fun s => K s * weilIntegrand (coshGaussMellinExt (1 - Real.pi/3)) s) -
      rectContourIntegral (-1) 2 T
        (fun s => K s * weilIntegrand (coshGaussMellinExt (2*β - 1)) s) +
      rectContourIntegral (-1) 2 T
        (fun s => K s * weilIntegrand (coshGaussMellinExt 0) s) := by
    -- Unfold rectContourIntegral and use integral_congr on each of 4 edges.
    unfold rectContourIntegral
    -- Pointwise on each edge: Re z ≥ -1 > -2.
    have h_bot : ∀ x ∈ Set.uIcc (-1:ℝ) 2,
        K ((x : ℂ) + (-T : ℝ) * I) * weilIntegrand (Contour.pairTestMellin β)
              ((x : ℂ) + (-T : ℝ) * I) =
          (1/2 : ℂ) * (K ((x : ℂ) + (-T : ℝ) * I) *
              weilIntegrand (coshGaussMellinExt (2*β - Real.pi/3)) ((x : ℂ) + (-T : ℝ) * I)) +
          (1/2 : ℂ) * (K ((x : ℂ) + (-T : ℝ) * I) *
              weilIntegrand (coshGaussMellinExt (2 - Real.pi/3 - 2*β)) ((x : ℂ) + (-T : ℝ) * I)) -
          K ((x : ℂ) + (-T : ℝ) * I) *
              weilIntegrand (coshGaussMellinExt (1 - Real.pi/3)) ((x : ℂ) + (-T : ℝ) * I) -
          K ((x : ℂ) + (-T : ℝ) * I) *
              weilIntegrand (coshGaussMellinExt (2*β - 1)) ((x : ℂ) + (-T : ℝ) * I) +
          K ((x : ℂ) + (-T : ℝ) * I) *
              weilIntegrand (coshGaussMellinExt 0) ((x : ℂ) + (-T : ℝ) * I) := by
      intro x hx; apply h_ptwise_re
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
      rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 2)] at hx; linarith [hx.1]
    have h_top : ∀ x ∈ Set.uIcc (-1:ℝ) 2,
        K ((x : ℂ) + (T : ℝ) * I) * weilIntegrand (Contour.pairTestMellin β)
              ((x : ℂ) + (T : ℝ) * I) =
          (1/2 : ℂ) * (K ((x : ℂ) + (T : ℝ) * I) *
              weilIntegrand (coshGaussMellinExt (2*β - Real.pi/3)) ((x : ℂ) + (T : ℝ) * I)) +
          (1/2 : ℂ) * (K ((x : ℂ) + (T : ℝ) * I) *
              weilIntegrand (coshGaussMellinExt (2 - Real.pi/3 - 2*β)) ((x : ℂ) + (T : ℝ) * I)) -
          K ((x : ℂ) + (T : ℝ) * I) *
              weilIntegrand (coshGaussMellinExt (1 - Real.pi/3)) ((x : ℂ) + (T : ℝ) * I) -
          K ((x : ℂ) + (T : ℝ) * I) *
              weilIntegrand (coshGaussMellinExt (2*β - 1)) ((x : ℂ) + (T : ℝ) * I) +
          K ((x : ℂ) + (T : ℝ) * I) *
              weilIntegrand (coshGaussMellinExt 0) ((x : ℂ) + (T : ℝ) * I) := by
      intro x hx; apply h_ptwise_re
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
      rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 2)] at hx; linarith [hx.1]
    have h_right : ∀ y ∈ Set.uIcc (-T) T,
        K (((2:ℝ) : ℂ) + (y : ℂ) * I) *
            weilIntegrand (Contour.pairTestMellin β) (((2:ℝ) : ℂ) + (y : ℂ) * I) =
          (1/2 : ℂ) * (K (((2:ℝ) : ℂ) + (y : ℂ) * I) *
              weilIntegrand (coshGaussMellinExt (2*β - Real.pi/3)) (((2:ℝ) : ℂ) + (y : ℂ) * I)) +
          (1/2 : ℂ) * (K (((2:ℝ) : ℂ) + (y : ℂ) * I) *
              weilIntegrand (coshGaussMellinExt (2 - Real.pi/3 - 2*β))
                (((2:ℝ) : ℂ) + (y : ℂ) * I)) -
          K (((2:ℝ) : ℂ) + (y : ℂ) * I) *
              weilIntegrand (coshGaussMellinExt (1 - Real.pi/3)) (((2:ℝ) : ℂ) + (y : ℂ) * I) -
          K (((2:ℝ) : ℂ) + (y : ℂ) * I) *
              weilIntegrand (coshGaussMellinExt (2*β - 1)) (((2:ℝ) : ℂ) + (y : ℂ) * I) +
          K (((2:ℝ) : ℂ) + (y : ℂ) * I) *
              weilIntegrand (coshGaussMellinExt 0) (((2:ℝ) : ℂ) + (y : ℂ) * I) :=
      fun y _ => h_ptwise_re _ (by norm_num)
    have h_left : ∀ y ∈ Set.uIcc (-T) T,
        K (((-1:ℝ) : ℂ) + (y : ℂ) * I) *
            weilIntegrand (Contour.pairTestMellin β) (((-1:ℝ) : ℂ) + (y : ℂ) * I) =
          (1/2 : ℂ) * (K (((-1:ℝ) : ℂ) + (y : ℂ) * I) *
              weilIntegrand (coshGaussMellinExt (2*β - Real.pi/3))
                (((-1:ℝ) : ℂ) + (y : ℂ) * I)) +
          (1/2 : ℂ) * (K (((-1:ℝ) : ℂ) + (y : ℂ) * I) *
              weilIntegrand (coshGaussMellinExt (2 - Real.pi/3 - 2*β))
                (((-1:ℝ) : ℂ) + (y : ℂ) * I)) -
          K (((-1:ℝ) : ℂ) + (y : ℂ) * I) *
              weilIntegrand (coshGaussMellinExt (1 - Real.pi/3)) (((-1:ℝ) : ℂ) + (y : ℂ) * I) -
          K (((-1:ℝ) : ℂ) + (y : ℂ) * I) *
              weilIntegrand (coshGaussMellinExt (2*β - 1)) (((-1:ℝ) : ℂ) + (y : ℂ) * I) +
          K (((-1:ℝ) : ℂ) + (y : ℂ) * I) *
              weilIntegrand (coshGaussMellinExt 0) (((-1:ℝ) : ℂ) + (y : ℂ) * I) :=
      fun y _ => h_ptwise_re _ (by norm_num)
    rw [intervalIntegral.integral_congr h_bot,
        intervalIntegral.integral_congr h_top,
        intervalIntegral.integral_congr h_right,
        intervalIntegral.integral_congr h_left]
    -- Continuity helpers.
    have h_cgm_diff : ∀ (c : ℝ) (s : ℂ), -2 < s.re → s ≠ 0 →
        DifferentiableAt ℂ (coshGaussMellinExt c) s := fun c s hre hs0 => by
      unfold coshGaussMellinExt
      have h_gne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := fun m hm => by
        rcases Nat.eq_zero_or_pos m with rfl | hm_pos
        · simp only [Nat.cast_zero, neg_zero] at hm
          have : s = 0 := by field_simp at hm; simp at hm; exact hm
          exact hs0 this
        · have hre_half : (s / 2).re = -(m : ℝ) := by rw [hm]; simp
          have hdiv : (s / 2).re = s.re / 2 := by simp
          rw [hdiv] at hre_half
          linarith [show (1 : ℝ) ≤ m from by exact_mod_cast hm_pos]
      have h_pow : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ (-(z / 2))) s :=
        (differentiableAt_id.div_const (2 : ℂ)).neg.const_cpow (Or.inl (by norm_num))
      have h_gam : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
        (Complex.differentiableAt_Gamma (s / 2) h_gne).comp s
          (differentiableAt_id.div_const (2 : ℂ))
      have h_gmc : DifferentiableAt ℂ gaussMellinClosed s := by
        unfold gaussMellinClosed
        exact ((differentiableAt_const (1 / 2 : ℂ)).mul h_pow).mul h_gam
      exact h_gmc.add (ZD.CoshGaussMellinResidue.coshDiffMellin_differentiableAt c hre)
    have h_zeta_horiz : ∀ (x t : ℝ), (t = T ∨ t = -T) →
        riemannZeta ((x : ℂ) + (t : ℝ) * I) ≠ 0 := fun x t ht hζ => by
      have h_nt : ∀ n : ℕ, (x : ℂ) + t * I ≠ -2 * (↑n + 1) := fun n hn => by
        have := congr_arg Complex.im hn; push_cast at this; simp at this
        rcases ht with rfl | rfl <;> linarith
      obtain ⟨hlo, hhi⟩ := riemannZeta_nontrivial_zero_re_bounds hζ h_nt
      have hmem : (x : ℂ) + t * I ∈ ZD.NontrivialZeros := ⟨hlo, hhi, hζ⟩
      have him : ((x : ℂ) + (t : ℝ) * I).im = t := by simp
      rcases ht with heq | heq
      · exact (hGood.1 _ hmem).1 (him.trans heq)
      · exact (hGood.1 _ hmem).2 (him.trans heq)
    have h_zeta_left : ∀ (y : ℝ), riemannZeta ((-1 : ℂ) + y * I) ≠ 0 := fun y hζ => by
      have h_nt : ∀ n : ℕ, (-1 : ℂ) + y * I ≠ -2 * (↑n + 1) := fun n hn => by
        have := congr_arg Complex.re hn; push_cast at this; simp at this
        linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      linarith [(riemannZeta_nontrivial_zero_re_bounds hζ h_nt).1,
                show ((-1 : ℂ) + y * I).re = -1 from by simp]
    -- Integrability witnesses for each (c, edge).  Use continuity of K on the
    -- parameterization plus continuity of weilIntegrand(coshGaussMellinExt c).
    have hKcont : Continuous K := hK.continuous
    have h_wii : ∀ (c : ℝ),
        IntervalIntegrable
          (fun x : ℝ => K ((x : ℂ) + (-T : ℝ) * I) *
              weilIntegrand (coshGaussMellinExt c) ((x : ℂ) + (-T : ℝ) * I))
          MeasureTheory.volume (-1 : ℝ) 2 ∧
        IntervalIntegrable
          (fun x : ℝ => K ((x : ℂ) + (T : ℝ) * I) *
              weilIntegrand (coshGaussMellinExt c) ((x : ℂ) + (T : ℝ) * I))
          MeasureTheory.volume (-1 : ℝ) 2 ∧
        IntervalIntegrable
          (fun y : ℝ => K (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
              weilIntegrand (coshGaussMellinExt c) (((2 : ℝ) : ℂ) + (y : ℂ) * I))
          MeasureTheory.volume (-T) T ∧
        IntervalIntegrable
          (fun y : ℝ => K (((-1 : ℝ) : ℂ) + (y : ℂ) * I) *
              weilIntegrand (coshGaussMellinExt c) (((-1 : ℝ) : ℂ) + (y : ℂ) * I))
          MeasureTheory.volume (-T) T := fun c => by
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- bottom edge
        apply ContinuousOn.intervalIntegrable; intro x hx
        rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] at hx
        have hre2 : -2 < ((x : ℂ) + (-T : ℝ) * I).re := by simp; linarith [hx.1]
        have hs0 : (x : ℂ) + (-T : ℝ) * I ≠ 0 := by
          intro h; have := congr_arg Complex.im h; simp at this; linarith
        have hs1 : (x : ℂ) + (-T : ℝ) * I ≠ 1 := by
          intro h; have := congr_arg Complex.im h; simp at this; linarith
        have hζ : riemannZeta ((x : ℂ) + (-T : ℝ) * I) ≠ 0 :=
          h_zeta_horiz x (-T) (Or.inr rfl)
        apply ContinuousAt.continuousWithinAt
        have hparam : Continuous (fun x : ℝ => (x : ℂ) + (-T : ℝ) * I) :=
          Complex.continuous_ofReal.add continuous_const
        have hKx : ContinuousAt (fun x : ℝ => K ((x : ℂ) + (-T : ℝ) * I)) x :=
          (hKcont.comp hparam).continuousAt
        have hWx : ContinuousAt
            (fun x : ℝ => weilIntegrand (coshGaussMellinExt c) ((x : ℂ) + (-T : ℝ) * I)) x :=
          (weilIntegrand_differentiableAt hs1 hζ
            (h_cgm_diff c _ hre2 hs0)).continuousAt.tendsto.comp hparam.continuousAt
        exact hKx.mul hWx
      · -- top edge
        apply ContinuousOn.intervalIntegrable; intro x hx
        rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] at hx
        have hre2 : -2 < ((x : ℂ) + (T : ℝ) * I).re := by simp; linarith [hx.1]
        have hs0 : (x : ℂ) + (T : ℝ) * I ≠ 0 := by
          intro h; have := congr_arg Complex.im h; simp at this; linarith
        have hs1 : (x : ℂ) + (T : ℝ) * I ≠ 1 := by
          intro h; have := congr_arg Complex.im h; simp at this; linarith
        have hζ : riemannZeta ((x : ℂ) + (T : ℝ) * I) ≠ 0 :=
          h_zeta_horiz x T (Or.inl rfl)
        apply ContinuousAt.continuousWithinAt
        have hparam : Continuous (fun x : ℝ => (x : ℂ) + (T : ℝ) * I) :=
          Complex.continuous_ofReal.add continuous_const
        have hKx : ContinuousAt (fun x : ℝ => K ((x : ℂ) + (T : ℝ) * I)) x :=
          (hKcont.comp hparam).continuousAt
        have hWx : ContinuousAt
            (fun x : ℝ => weilIntegrand (coshGaussMellinExt c) ((x : ℂ) + (T : ℝ) * I)) x :=
          (weilIntegrand_differentiableAt hs1 hζ
            (h_cgm_diff c _ hre2 hs0)).continuousAt.tendsto.comp hparam.continuousAt
        exact hKx.mul hWx
      · -- right edge: Re z = 2 > 1, so ζ(z) ≠ 0
        apply ContinuousOn.intervalIntegrable; intro y _hy
        have hre2 : -2 < (((2 : ℝ) : ℂ) + (y : ℂ) * I).re := by simp
        have hs0 : ((2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := by
          intro h; have := congr_arg Complex.re h; simp at this
        have hs1 : ((2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 1 := by
          intro h; have := congr_arg Complex.re h; simp at this
        have hζ : riemannZeta (((2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 :=
          riemannZeta_ne_zero_of_one_lt_re (by simp)
        apply ContinuousAt.continuousWithinAt
        have hparam : Continuous (fun y : ℝ => ((2 : ℝ) : ℂ) + (y : ℂ) * I) :=
          continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
        have hKy : ContinuousAt (fun y : ℝ => K (((2 : ℝ) : ℂ) + (y : ℂ) * I)) y :=
          (hKcont.comp hparam).continuousAt
        have hWy : ContinuousAt
            (fun y : ℝ => weilIntegrand (coshGaussMellinExt c) (((2 : ℝ) : ℂ) + (y : ℂ) * I)) y :=
          (weilIntegrand_differentiableAt hs1 hζ
            (h_cgm_diff c _ hre2 hs0)).continuousAt.tendsto.comp hparam.continuousAt
        exact hKy.mul hWy
      · -- left edge: ζ ≠ 0 since nontrivial zeros have Re ∈ (0,1)
        apply ContinuousOn.intervalIntegrable; intro y _hy
        have hre2 : -2 < (((-1 : ℝ) : ℂ) + (y : ℂ) * I).re := by simp
        have hs0 : ((-1 : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := by
          intro h; have := congr_arg Complex.re h; simp at this
        have hs1 : ((-1 : ℝ) : ℂ) + (y : ℂ) * I ≠ 1 := by
          intro h; have := congr_arg Complex.re h; simp at this; linarith
        have hζ_left' : riemannZeta (((-1 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
          have := h_zeta_left y
          have heq : (((-1 : ℝ) : ℂ) + (y : ℂ) * I) = ((-1 : ℂ) + (y : ℂ) * I) := by
            push_cast; ring
          rw [heq]; exact this
        apply ContinuousAt.continuousWithinAt
        have hparam : Continuous (fun y : ℝ => ((-1 : ℝ) : ℂ) + (y : ℂ) * I) :=
          continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
        have hKy : ContinuousAt (fun y : ℝ => K (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) y :=
          (hKcont.comp hparam).continuousAt
        have hWy : ContinuousAt
            (fun y : ℝ => weilIntegrand (coshGaussMellinExt c) (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) y :=
          (weilIntegrand_differentiableAt hs1 hζ_left'
            (h_cgm_diff c _ hre2 hs0)).continuousAt.tendsto.comp hparam.continuousAt
        exact hKy.mul hWy
    obtain ⟨hwii_b1, hwii_t1, hwii_r1, hwii_l1⟩ := h_wii (2 * β - Real.pi / 3)
    obtain ⟨hwii_b2, hwii_t2, hwii_r2, hwii_l2⟩ := h_wii (2 - Real.pi / 3 - 2 * β)
    obtain ⟨hwii_b3, hwii_t3, hwii_r3, hwii_l3⟩ := h_wii (1 - Real.pi / 3)
    obtain ⟨hwii_b4, hwii_t4, hwii_r4, hwii_l4⟩ := h_wii (2 * β - 1)
    obtain ⟨hwii_b5, hwii_t5, hwii_r5, hwii_l5⟩ := h_wii 0
    -- 5-split helper.
    have h_5split : ∀ (f1 f2 f3 f4 f5 : ℝ → ℂ) (a b : ℝ)
        (h1 : IntervalIntegrable f1 MeasureTheory.volume a b)
        (h2 : IntervalIntegrable f2 MeasureTheory.volume a b)
        (h3 : IntervalIntegrable f3 MeasureTheory.volume a b)
        (h4 : IntervalIntegrable f4 MeasureTheory.volume a b)
        (h5 : IntervalIntegrable f5 MeasureTheory.volume a b),
        ∫ x in a..b, ((1/2 : ℂ) * f1 x + (1/2 : ℂ) * f2 x - f3 x - f4 x + f5 x) =
        (1/2 : ℂ) * (∫ x in a..b, f1 x) + (1/2 : ℂ) * (∫ x in a..b, f2 x)
          - (∫ x in a..b, f3 x) - (∫ x in a..b, f4 x) + (∫ x in a..b, f5 x) :=
      fun f1 f2 f3 f4 f5 a b h1 h2 h3 h4 h5 => by
        have hc1 : IntervalIntegrable (fun x => (1/2 : ℂ) * f1 x) MeasureTheory.volume a b :=
          h1.const_mul (1/2 : ℂ)
        have hc2 : IntervalIntegrable (fun x => (1/2 : ℂ) * f2 x) MeasureTheory.volume a b :=
          h2.const_mul (1/2 : ℂ)
        rw [intervalIntegral.integral_add ((hc1.add hc2).sub h3 |>.sub h4) h5,
            intervalIntegral.integral_sub (hc1.add hc2 |>.sub h3) h4,
            intervalIntegral.integral_sub (hc1.add hc2) h3,
            intervalIntegral.integral_add hc1 hc2]
        have e1 : ∫ x in a..b, (1/2 : ℂ) * f1 x = (1/2 : ℂ) * ∫ x in a..b, f1 x :=
          intervalIntegral.integral_const_mul _ f1
        have e2 : ∫ x in a..b, (1/2 : ℂ) * f2 x = (1/2 : ℂ) * ∫ x in a..b, f2 x :=
          intervalIntegral.integral_const_mul _ f2
        rw [e1, e2]
    rw [h_5split _ _ _ _ _ _ _ hwii_b1 hwii_b2 hwii_b3 hwii_b4 hwii_b5,
        h_5split _ _ _ _ _ _ _ hwii_t1 hwii_t2 hwii_t3 hwii_t4 hwii_t5,
        h_5split _ _ _ _ _ _ _ hwii_r1 hwii_r2 hwii_r3 hwii_r4 hwii_r5,
        h_5split _ _ _ _ _ _ _ hwii_l1 hwii_l2 hwii_l3 hwii_l4 hwii_l5]
    simp only [smul_eq_mul]
    ring
  -- Step 5: Combine.  Constant `negLogDerivZeta0K * K 0` cancels because
  -- weights `1/2 + 1/2 - 1 - 1 + 1 = 0`.
  rw [h_integ_eq, h_c1, h_c2, h_c3, h_c4, h_c5, h_at1, h_sum_eq]
  ring

end Scratch
end OfflineDetectorEndpoint
end WeilPositivity
end ZD

end

#print axioms ZD.WeilPositivity.OfflineDetectorEndpoint.Scratch.rectContourIntegral_K_neg_logDerivZeta_pairTestMellin_eq_residue_sum
