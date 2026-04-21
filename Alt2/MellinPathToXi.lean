import Mathlib
import RequestProject.ThetaTransport

/-!
# Mellin route to `riemannXi` (additive, no changes to existing files)

This file pivots the missing analytic input from "Fourier cosine inversion +
super-exp decay of the FT-inverted ψ_theta" (the original `ThetaTransport`
route) to a Mellin/evenKernel-based route using Mathlib's `WeakFEPair`.

## Why this route

The FT-inversion route (`ThetaTransport.ψ_theta`) needs:
* polynomial growth of `ζ` on the critical line (NOT in Mathlib),
* Fourier cosine inversion adapted to `Ioi 0` (not directly in Mathlib),
* contour-shift super-exp decay (not in Mathlib).

The Mellin/evenKernel route avoids all three by using:
* `HurwitzZeta.evenKernel 0` (in Mathlib) — has known exp decay at +∞,
* `WeakFEPair.hasMellin` and `WeakFEPair.Λ₀` (in Mathlib) — give
  the Mellin/zeta identity for ALL `s` as the entire `Λ₀(s/2)/2 = cRZ₀(s)`,
* a single change-of-variable lemma `u = exp(2τ)` (the only substantial
  remaining work).

## Architecture

* `ψ_mellin t := (evenKernel 0 (e^(2t)) - 1) · e^(t/2)` — well-decayed.
* `I_theta_of ψ_mellin s = completedRiemannZeta₀ s` — the Mellin identity.
* `(s(s-1)/2) · I_theta_of ψ_mellin s + 1/2 = riemannXi s` — algebra.
* Differentiability and vanishing at nontrivial zeros follow from those of
  `riemannXi` (already proved in `ThetaTransport`).

## Honest disclosure

The Mellin identity `I_theta_of ψ_mellin s = completedRiemannZeta₀ s` is
itself a single concrete change-of-variable + FE-symmetrization computation.
Mathlib has the necessary primitives (`mellin_comp_rpow`, `WeakFEPair.Λ₀`,
`hurwitzEvenFEPair_zero` Mellin formulas). The full Lean proof is ~200-400
lines of substitution algebra and is left as one explicit named sorry,
`I_theta_of_ψ_mellin_eq_completedRiemannZeta₀`. That single sorry, when
discharged, closes BOTH original sorries in `ThetaTransport.lean` via this
file's downstream lemmas — so it is strictly less work than the FT route.
-/

open Real Complex MeasureTheory HurwitzZeta Set Filter Topology

noncomputable section

namespace ZD

/-- **Theta-transported density (Mellin form)**: `ψ_mellin(t) := (θ(e^(2t)) − 1)·e^(t/2)`,
where `θ = HurwitzZeta.evenKernel 0` is the Jacobi theta function. -/
def ψ_mellin (t : ℝ) : ℝ :=
  (HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) - 1) * Real.exp (t / 2)

/-! ### Decomposition of the Mellin identity

The proof is decomposed into three steps that match the math:

* `mellinFmodif_eq_symmetric_form` — Mellin of `f_modif (s/2)` collapses,
  via FE on the `(0, 1)` half, to a single integral over `(1, ∞)`.
* `I_theta_of_ψ_mellin_eq_symmetric_form` — substitution `u = e^(2t)` rewrites
  the cosh-kernel integral as the same integral over `(1, ∞)`.
* `I_theta_of_ψ_mellin_eq_completedRiemannZeta₀` — combine.
-/

/-- The "FE-symmetric" integrand on `(1, ∞)` that both `Λ₀(s/2)` and the cosh
observable collapse to: `(evenKernel 0 u − 1) · (u^(s/2−1) + u^(−s/2−1/2))`. -/
def symmetricIntegrand (s : ℂ) (u : ℝ) : ℂ :=
  ((HurwitzZeta.evenKernel 0 u : ℂ) - 1) *
    ((u : ℂ) ^ (s/2 - 1) + (u : ℂ) ^ (-s/2 - (1/2 : ℂ)))

/-! ### Step A: Mellin of `f_modif` at `s/2` equals the symmetric integral over `(1, ∞)`.
Decomposition uses:
1. Split `mellin f_modif (s/2) = ∫_(1,∞) (evenKernel 0 - 1) u^(s/2-1) + ∫_(0,1) (evenKernel 0 - u^(-1/2)) u^(s/2-1)`.
2. On `(0, 1)`, substitute `v = 1/u` (Mathlib `MeasureTheory.integral_comp_inv`-style).
3. Apply `HurwitzZeta.evenKernel_functional_equation` to fold both halves. -/

/-- Half A: integrating `(u:ℂ)^(s/2-1) · (evenKernel 0 u - 1)` against the
`Ioi 1` indicator gives the upper-half integral over `(1,∞)`. -/
private lemma mellinFmodif_upper (s : ℂ) :
    ∫ u in Set.Ioi (0:ℝ),
        (u : ℂ) ^ (s/2 - 1) •
          ((Set.Ioi (1:ℝ)).indicator
            (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) - 1) u) =
      ∫ u in Set.Ioi (1:ℝ),
        ((HurwitzZeta.evenKernel 0 u : ℝ) : ℂ) * (u : ℂ) ^ (s/2 - 1) -
        (u : ℂ) ^ (s/2 - 1) := by
  -- Move the smul inside the indicator
  have h_smul_indicator : ∀ u : ℝ,
      (u : ℂ) ^ (s/2 - 1) •
        ((Set.Ioi (1:ℝ)).indicator
          (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) - 1) u) =
      (Set.Ioi (1:ℝ)).indicator
        (fun x => (x : ℂ) ^ (s/2 - 1) •
          (((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) - 1)) u := by
    intro u
    by_cases hu : u ∈ Set.Ioi (1:ℝ)
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, smul_zero]
  simp_rw [h_smul_indicator]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi]
  rw [show Set.Ioi (0:ℝ) ∩ Set.Ioi 1 = Set.Ioi (1:ℝ) from
    Set.inter_eq_self_of_subset_right (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u _
  show (u : ℂ) ^ (s/2 - 1) • (((HurwitzZeta.evenKernel 0 u : ℝ) : ℂ) - 1) =
      ((HurwitzZeta.evenKernel 0 u : ℝ) : ℂ) * (u : ℂ) ^ (s/2 - 1) -
        (u : ℂ) ^ (s/2 - 1)
  rw [smul_eq_mul]; ring

/-- Half B: the `Ioo 0 1` indicator integral, after substitution `v = 1/u` plus
the evenKernel functional equation, equals the lower-half integral over `(1,∞)`
matching `symmetricIntegrand`'s second term.

Proof: move the smul inside the indicator (so `setIntegral_indicator` localizes to
`Ioo 0 1`), then apply `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`
with the diffeomorphism `t ↦ 1/t : Ioi 1 → Ioo 0 1`. The resulting integrand is
simplified via `evenKernel_functional_equation` and cpow algebra. -/
private lemma mellinFmodif_lower (s : ℂ) :
    ∫ u in Set.Ioi (0:ℝ),
        (u : ℂ) ^ (s/2 - 1) •
          ((Set.Ioo (0:ℝ) 1).indicator
            (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) -
              ((x ^ (-(1/2 : ℝ)) : ℝ) : ℂ)) u) =
      ∫ u in Set.Ioi (1:ℝ),
        ((HurwitzZeta.evenKernel 0 u : ℝ) : ℂ) * (u : ℂ) ^ (-s/2 - (1/2 : ℂ)) -
        (u : ℂ) ^ (-s/2 - (1/2 : ℂ)) := by
  -- Step 1: move smul inside indicator (same trick as upper)
  have h_smul_indicator : ∀ u : ℝ,
      (u : ℂ) ^ (s/2 - 1) •
        ((Set.Ioo (0:ℝ) 1).indicator
          (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) -
            ((x ^ (-(1/2 : ℝ)) : ℝ) : ℂ)) u) =
      (Set.Ioo (0:ℝ) 1).indicator
        (fun x => (x : ℂ) ^ (s/2 - 1) •
          (((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) -
           ((x ^ (-(1/2 : ℝ)) : ℝ) : ℂ))) u := by
    intro u
    by_cases hu : u ∈ Set.Ioo (0:ℝ) 1
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, smul_zero]
  simp_rw [h_smul_indicator]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioo]
  rw [show Set.Ioi (0:ℝ) ∩ Set.Ioo 0 1 = Set.Ioo (0:ℝ) 1 from
    Set.inter_eq_self_of_subset_right Set.Ioo_subset_Ioi_self]
  -- Step 2: apply the change of variables u = 1/t with t in Ioi 1
  -- f t := 1/t, f' t := -1/t², f '' Ioi 1 = Ioo 0 1
  set φ : ℝ → ℝ := fun t => 1/t
  set φ' : ℝ → ℝ := fun t => -1/t^2
  have h_image : φ '' Set.Ioi (1 : ℝ) = Set.Ioo (0:ℝ) 1 := by
    ext u
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Ioo, φ]
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨by positivity, ?_⟩
      rw [div_lt_one (by linarith : (0:ℝ) < t)]; linarith
    · rintro ⟨h0, h1⟩
      refine ⟨1/u, ?_, ?_⟩
      · rw [lt_div_iff₀ h0]; linarith
      · rw [one_div, one_div, inv_inv]
  have h_inj : Set.InjOn φ (Set.Ioi (1 : ℝ)) := by
    intro x hx y hy hxy
    simp only [φ, one_div] at hxy
    have hx_pos : 0 < x := by linarith [Set.mem_Ioi.mp hx]
    have hy_pos : 0 < y := by linarith [Set.mem_Ioi.mp hy]
    exact inv_injective (by rw [hxy])
  have h_deriv : ∀ t ∈ Set.Ioi (1:ℝ), HasDerivWithinAt φ (φ' t) (Set.Ioi (1:ℝ)) t := by
    intro t ht
    have ht_pos : 0 < t := by linarith [Set.mem_Ioi.mp ht]
    have ht_ne : t ≠ 0 := ht_pos.ne'
    have h_one_div : (fun y : ℝ => (1 : ℝ) / y) = (fun y : ℝ => y⁻¹) := by
      funext y; rw [one_div]
    have h_inv_d : HasDerivAt (fun y : ℝ => y⁻¹) (-(t^2)⁻¹) t := hasDerivAt_inv ht_ne
    have h_one_div_d : HasDerivAt φ (-(t^2)⁻¹) t := by
      simp only [φ, h_one_div]; exact h_inv_d
    have h_eq_φ' : φ' t = -(t^2)⁻¹ := by
      simp [φ']; field_simp
    rw [h_eq_φ']
    exact h_one_div_d.hasDerivWithinAt
  rw [← h_image,
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi h_deriv h_inj]
  -- Step 3: integrand simplification using FE
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht_pos : 0 < t := by linarith [Set.mem_Ioi.mp ht]
  have ht_ne : t ≠ 0 := ht_pos.ne'
  have ht_inv_pos : 0 < 1/t := by positivity
  -- |φ' t| = 1/t²
  have h_abs : |φ' t| = 1/t^2 := by
    show |-1/t^2| = 1/t^2
    have h : -1/t^2 = -(1/t^2) := by ring
    rw [h, abs_neg, abs_of_pos]; positivity
  -- evenKernel FE: evenKernel 0 (1/t) = √t · evenKernel 0 t  (using cosKernel 0 = evenKernel 0)
  have h_FE : HurwitzZeta.evenKernel 0 (1/t) = t^(1/2 : ℝ) * HurwitzZeta.evenKernel 0 t := by
    have := HurwitzZeta.evenKernel_functional_equation (0 : UnitAddCircle) t
    -- says: evenKernel 0 t = 1 / t^(1/2) * cosKernel 0 (1/t)
    -- and cosKernel 0 = evenKernel 0
    rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero] at this
    rw [HurwitzZeta.evenKernel_functional_equation]
    rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
    have h_inv : (1:ℝ)/(1/t) = t := by field_simp
    rw [h_inv]
    have h_sqrt_pos : (0:ℝ) < (1/t)^(1/2 : ℝ) := Real.rpow_pos_of_pos ht_inv_pos _
    field_simp
    rw [show ((1:ℝ)/t)^(1/2 : ℝ) = 1 / t^(1/2 : ℝ) by
      rw [Real.div_rpow zero_le_one ht_pos.le, Real.one_rpow]]
    field_simp
  -- (1/t)^(-1/2) = t^(1/2) = √t
  have h_pow_neg_half : (1/t : ℝ)^(-(1/2 : ℝ)) = t^(1/2 : ℝ) := by
    rw [Real.div_rpow zero_le_one ht_pos.le, Real.one_rpow]
    rw [Real.rpow_neg ht_pos.le]
    field_simp
  -- (φ t : ℂ)^(s/2-1) = ((1/t : ℝ) : ℂ)^(s/2-1) = (t : ℂ)^(-(s/2-1)) = (t:ℂ)^(1-s/2)
  -- combined with the (1/t²) prefactor and √t from FE, get t^(-s/2-1/2)
  -- Goal: |φ' t| • (φ t : ℂ)^(s/2-1) • ((evenKernel 0 (φ t)) - (φ t)^(-1/2) : ℂ) =
  --       (evenKernel 0 t : ℂ) * t^(-s/2-1/2) - t^(-s/2-1/2)
  -- via h_FE + h_pow_neg_half: (evenKernel 0 (1/t) - (1/t)^(-1/2)) = √t · (evenKernel 0 t - 1)
  show |φ' t| • ((φ t : ℂ) ^ (s/2 - 1) •
        (((HurwitzZeta.evenKernel 0 (φ t) : ℝ) : ℂ) -
          (((φ t) ^ (-(1/2 : ℝ)) : ℝ) : ℂ))) =
      ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) * (t : ℂ) ^ (-s/2 - (1/2 : ℂ)) -
      (t : ℂ) ^ (-s/2 - (1/2 : ℂ))
  rw [h_abs]
  show ((1/t^2 : ℝ) : ℂ) * (((1/t : ℝ) : ℂ) ^ (s/2 - 1) *
        (((HurwitzZeta.evenKernel 0 (1/t) : ℝ) : ℂ) -
          (((1/t) ^ (-(1/2 : ℝ)) : ℝ) : ℂ))) = _
  rw [h_FE, h_pow_neg_half]
  -- Now: 1/t² * (1/t)^(s/2-1) * (t^(1/2) * evenKernel 0 t - t^(1/2))
  --    = 1/t² * (1/t)^(s/2-1) * t^(1/2) * (evenKernel 0 t - 1)
  -- Goal: evenKernel 0 t * t^(-s/2-1/2) - t^(-s/2-1/2)
  --     = (evenKernel 0 t - 1) * t^(-s/2-1/2)
  -- Need: (1/t²) * (1/t)^(s/2-1) * t^(1/2) = t^(-s/2-1/2)  (as ℂ)
  -- Use (1/t)^(s/2-1) = t^(-(s/2-1)) for t > 0:
  have h_cpow_inv : (((1/t : ℝ)) : ℂ) ^ (s/2 - 1) = (t : ℂ) ^ (-(s/2 - 1)) := by
    rw [show ((1/t : ℝ) : ℂ) = ((t : ℝ) : ℂ)⁻¹ by push_cast; rw [one_div]]
    rw [Complex.inv_cpow_eq_ite]
    have h_arg : (t : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg ht_pos.le]; exact Real.pi_pos.ne
    simp only [h_arg, if_false]
    rw [Complex.cpow_neg]
  rw [h_cpow_inv]
  -- Now everything is in terms of (t : ℂ)^something
  -- (1/t²) and t^(1/2) are real, cast to ℂ
  -- Use: ((t^(1/2) : ℝ) : ℂ) = (t : ℂ)^(1/2 : ℂ)  for t > 0
  have h_real_rpow : ((t^(1/2 : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ ((1/2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow ht_pos.le]
  -- (1/t² : ℝ) = (t^(-2) : ℝ) for t > 0
  have h_inv_sq : ((1/t^2 : ℝ) : ℂ) = (t : ℂ) ^ (-(2:ℂ)) := by
    rw [show (1/t^2 : ℝ) = t^((-2 : ℤ) : ℝ) by
      rw [Real.rpow_intCast]; field_simp]
    rw [show (((t : ℝ)^((-2 : ℤ) : ℝ) : ℝ) : ℂ) = ((t : ℝ) : ℂ)^(((-2 : ℤ) : ℝ) : ℂ) from
      Complex.ofReal_cpow ht_pos.le _]
    push_cast; rfl
  push_cast
  -- After push_cast: 1/↑t^2 (real div), ↑(t^(1/2)) (cast of real rpow)
  -- Convert these to complex cpows of ↑t
  have ht_C_ne : (t : ℂ) ≠ 0 := by exact_mod_cast ht_ne
  have h_inv_sq_cpow : (1 : ℂ) / (t : ℂ)^2 = (t : ℂ)^(-(2:ℂ)) := by
    rw [show ((-2 : ℂ)) = -(2:ℂ) from rfl, Complex.cpow_neg]
    rw [show ((2:ℂ)) = ((2:ℕ) : ℂ) by norm_num]
    rw [Complex.cpow_natCast]; field_simp
  have h_sqrt_cpow : ((t^(1/2 : ℝ) : ℝ) : ℂ) = (t : ℂ)^((1/2 : ℂ)) := by
    rw [Complex.ofReal_cpow ht_pos.le]; push_cast; rfl
  rw [h_inv_sq_cpow, h_sqrt_cpow]
  -- Goal now: ↑t^(-2) * (↑t^(-(s/2-1)) * (↑t^(1/2) * ↑(ev 0 t) - ↑t^(1/2)))
  --        = ↑(ev 0 t) * ↑t^(-s/2-1/2) - ↑t^(-s/2-1/2)
  -- Combine cpow exponents on the LHS:
  have h_exp1 : (t : ℂ)^(-(2:ℂ)) * (t : ℂ)^(-(s/2-1)) * (t : ℂ)^((1/2 : ℂ)) =
      (t : ℂ)^(-s/2 - 1/2) := by
    rw [← Complex.cpow_add _ _ ht_C_ne, ← Complex.cpow_add _ _ ht_C_ne]
    congr 1; ring
  -- Use h_exp1 to rewrite the LHS structure
  calc (t : ℂ)^(-(2:ℂ)) * ((t : ℂ)^(-(s/2-1)) *
          ((t : ℂ)^((1/2 : ℂ)) * ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) -
            (t : ℂ)^((1/2 : ℂ))))
      = ((((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1)) *
          ((t : ℂ)^(-(2:ℂ)) * (t : ℂ)^(-(s/2-1)) * (t : ℂ)^((1/2 : ℂ))) := by ring
    _ = ((((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1)) * (t : ℂ)^(-s/2 - 1/2) := by
          rw [h_exp1]
    _ = ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) * (t : ℂ)^(-s/2 - 1/2) -
          (t : ℂ)^(-s/2 - 1/2) := by ring

theorem mellinFmodif_eq_symmetric_form (s : ℂ) :
    mellin ((hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif) (s / 2) =
      ∫ u in Set.Ioi (1 : ℝ), symmetricIntegrand s u := by
  unfold mellin WeakFEPair.f_modif
  -- The hurwitzEvenFEPair's data: f = ofReal ∘ evenKernel 0, f₀ = 1, g₀ = 1, k = 1/2, ε = 1
  -- Distribute (u^(s/2-1)) • over the indicator sum, then split via integral_add
  have h_eq : ∀ u : ℝ,
      ((u : ℂ) ^ (s/2 - 1) •
        (((Set.Ioi 1).indicator (fun x => (hurwitzEvenFEPair (0 : UnitAddCircle)).f x -
            (hurwitzEvenFEPair (0 : UnitAddCircle)).f₀) +
          (Set.Ioo 0 1).indicator (fun x => (hurwitzEvenFEPair (0 : UnitAddCircle)).f x -
            ((hurwitzEvenFEPair (0 : UnitAddCircle)).ε *
              ↑(x ^ (-(hurwitzEvenFEPair (0 : UnitAddCircle)).k))) •
            (hurwitzEvenFEPair (0 : UnitAddCircle)).g₀)) u)) =
      (u : ℂ) ^ (s/2 - 1) •
        ((Set.Ioi (1:ℝ)).indicator
          (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) - 1) u) +
      (u : ℂ) ^ (s/2 - 1) •
        ((Set.Ioo (0:ℝ) 1).indicator
          (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) -
            ((x ^ (-(1/2 : ℝ)) : ℝ) : ℂ)) u) := by
    intro u
    rw [Pi.add_apply, smul_add]
    congr 1
    · -- Upper indicator: simplifies because hurwitzEvenFEPair 0's f₀ = 1, f = ofReal ∘ evenKernel 0
      show (u : ℂ) ^ (s/2 - 1) •
          ((Set.Ioi (1:ℝ)).indicator
            (fun x => ((hurwitzEvenFEPair (0:UnitAddCircle)).f x -
              (hurwitzEvenFEPair (0:UnitAddCircle)).f₀)) u) = _
      congr 1
      by_cases hu : u ∈ Set.Ioi (1:ℝ)
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
        simp [hurwitzEvenFEPair]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
    · -- Lower indicator: hurwitzEvenFEPair 0's k = 1/2, ε = 1, g₀ = 1
      show (u : ℂ) ^ (s/2 - 1) •
          ((Set.Ioo (0:ℝ) 1).indicator
            (fun x => (hurwitzEvenFEPair (0:UnitAddCircle)).f x -
              ((hurwitzEvenFEPair (0:UnitAddCircle)).ε *
                ↑(x ^ (-(hurwitzEvenFEPair (0:UnitAddCircle)).k))) •
              (hurwitzEvenFEPair (0:UnitAddCircle)).g₀) u) = _
      congr 1
      by_cases hu : u ∈ Set.Ioo (0:ℝ) 1
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
        simp [hurwitzEvenFEPair]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
  simp_rw [h_eq]
  -- Get unconditional Mellin integrability of f_modif from toStrongFEPair.hasMellin
  have h_strong_mellin : IntegrableOn
      (fun t : ℝ => (t : ℂ)^(s/2 - 1) •
        ((hurwitzEvenFEPair (0 : UnitAddCircle)).toStrongFEPair.f t))
      (Set.Ioi 0) :=
    ((hurwitzEvenFEPair (0 : UnitAddCircle)).toStrongFEPair.hasMellin (s/2)).1
  -- The two indicator integrands are non-negative-norm parts of f_modif, hence integrable
  -- Common bound: indicator-restricted integrand has norm ≤ full f_modif integrand
  -- because at each point, only one indicator is nonzero (disjoint supports)
  -- Pointwise norm bound: each indicator part has norm ≤ the f_modif sum
  have h_bound_upper : ∀ t : ℝ,
      ‖(t : ℂ) ^ (s/2 - 1) •
          ((Set.Ioi (1:ℝ)).indicator
            (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) - 1) t)‖ ≤
      ‖(t : ℂ)^(s/2 - 1) •
        ((hurwitzEvenFEPair (0 : UnitAddCircle)).toStrongFEPair.f t)‖ := by
    intro t
    show _ ≤ ‖(t : ℂ)^(s/2 - 1) • ((hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif t)‖
    rw [norm_smul, norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    by_cases ht1 : t ∈ Set.Ioi (1:ℝ)
    · -- f_modif t = (evenKernel 0 t - 1) at t > 1
      have ht_not_lower : t ∉ Set.Ioo (0:ℝ) 1 := fun ⟨_, h2⟩ => by
        rw [Set.mem_Ioi] at ht1; linarith
      rw [Set.indicator_of_mem ht1]
      have h_fmodif : (hurwitzEvenFEPair (0:UnitAddCircle)).f_modif t =
          ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1 := by
        unfold WeakFEPair.f_modif
        rw [Pi.add_apply, Set.indicator_of_mem ht1,
          Set.indicator_of_notMem ht_not_lower, add_zero]
        simp [hurwitzEvenFEPair]
      rw [h_fmodif]
    · rw [Set.indicator_of_notMem ht1, norm_zero]; exact norm_nonneg _
  have h_bound_lower : ∀ t : ℝ,
      ‖(t : ℂ) ^ (s/2 - 1) •
          ((Set.Ioo (0:ℝ) 1).indicator
            (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) -
              ((x ^ (-(1/2 : ℝ)) : ℝ) : ℂ)) t)‖ ≤
      ‖(t : ℂ)^(s/2 - 1) •
        ((hurwitzEvenFEPair (0 : UnitAddCircle)).toStrongFEPair.f t)‖ := by
    intro t
    show _ ≤ ‖(t : ℂ)^(s/2 - 1) • ((hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif t)‖
    rw [norm_smul, norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    by_cases ht2 : t ∈ Set.Ioo (0:ℝ) 1
    · have ht_not_upper : t ∉ Set.Ioi (1:ℝ) := fun h1 =>
        by rw [Set.mem_Ioi] at h1; obtain ⟨_, h⟩ := ht2; linarith
      rw [Set.indicator_of_mem ht2]
      have h_fmodif : (hurwitzEvenFEPair (0:UnitAddCircle)).f_modif t =
          ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - ((t ^ (-(1/2 : ℝ)) : ℝ) : ℂ) := by
        unfold WeakFEPair.f_modif
        rw [Pi.add_apply, Set.indicator_of_notMem ht_not_upper,
          Set.indicator_of_mem ht2, zero_add]
        simp [hurwitzEvenFEPair]
      rw [h_fmodif]
    · rw [Set.indicator_of_notMem ht2, norm_zero]; exact norm_nonneg _
  -- Pointwise eqn: strong integrand = upper indicator integrand + lower indicator integrand
  have h_decomp : ∀ t : ℝ,
      (t : ℂ) ^ (s/2 - 1) •
        ((hurwitzEvenFEPair (0:UnitAddCircle)).toStrongFEPair.f t) =
      (t : ℂ) ^ (s/2 - 1) •
        ((Set.Ioi (1:ℝ)).indicator
          (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) - 1) t) +
      (t : ℂ) ^ (s/2 - 1) •
        ((Set.Ioo (0:ℝ) 1).indicator
          (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) -
            ((x ^ (-(1/2 : ℝ)) : ℝ) : ℂ)) t) := by
    intro t
    rw [← smul_add]
    show (t : ℂ) ^ (s/2 - 1) • (hurwitzEvenFEPair (0:UnitAddCircle)).f_modif t = _
    congr 1
    unfold WeakFEPair.f_modif
    rw [Pi.add_apply]
    by_cases ht1 : t ∈ Set.Ioi (1:ℝ)
    · have ht_not_lower : t ∉ Set.Ioo (0:ℝ) 1 := fun ⟨_, h2⟩ =>
        by rw [Set.mem_Ioi] at ht1; linarith
      rw [Set.indicator_of_mem ht1, Set.indicator_of_notMem ht_not_lower,
        Set.indicator_of_notMem ht_not_lower, Set.indicator_of_mem ht1,
        add_zero, add_zero]
      simp [hurwitzEvenFEPair]
    · rw [Set.indicator_of_notMem ht1, Set.indicator_of_notMem ht1, zero_add]
      by_cases ht2 : t ∈ Set.Ioo (0:ℝ) 1
      · rw [Set.indicator_of_mem ht2, Set.indicator_of_mem ht2, zero_add]
        simp [hurwitzEvenFEPair]
      · rw [Set.indicator_of_notMem ht2, Set.indicator_of_notMem ht2, add_zero]
  -- Construct AEStronglyMeasurable for both indicator integrands using the decomposition
  -- Approach: build them from the Mathlib AEStronglyMeasurable building blocks
  have h_kernel_aestrong : AEStronglyMeasurable
      (fun t : ℝ => ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ))
      (volume.restrict (Set.Ioi 0)) := by
    apply Complex.continuous_ofReal.comp_aestronglyMeasurable
    exact (HurwitzZeta.continuousOn_evenKernel 0).aestronglyMeasurable measurableSet_Ioi
  have h_cpow_aestrong : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (s/2 - 1)) (volume.restrict (Set.Ioi 0)) := by
    apply (ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi)
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const t (s/2 - 1)
      (Or.inr (Set.mem_Ioi.mp ht).ne')).continuousWithinAt
  have h_neg_half_aestrong : AEStronglyMeasurable
      (fun t : ℝ => ((t ^ (-(1/2 : ℝ)) : ℝ) : ℂ)) (volume.restrict (Set.Ioi 0)) := by
    apply Complex.continuous_ofReal.comp_aestronglyMeasurable
    apply (ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi)
    intro t ht
    have : ContinuousAt (fun u : ℝ => u ^ (-(1/2 : ℝ))) t := by
      apply Real.continuousAt_rpow_const
      exact Or.inl (Set.mem_Ioi.mp ht).ne'
    exact this.continuousWithinAt
  -- Now build AEStronglyMeasurable for the two indicator integrands
  have h_aestrong_upper : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (s/2 - 1) •
        ((Set.Ioi (1:ℝ)).indicator
          (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) - 1) t))
      (volume.restrict (Set.Ioi 0)) := by
    apply h_cpow_aestrong.smul
    apply AEStronglyMeasurable.indicator _ measurableSet_Ioi
    exact h_kernel_aestrong.sub aestronglyMeasurable_const
  have h_aestrong_lower : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (s/2 - 1) •
        ((Set.Ioo (0:ℝ) 1).indicator
          (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) -
            ((x ^ (-(1/2 : ℝ)) : ℝ) : ℂ)) t))
      (volume.restrict (Set.Ioi 0)) := by
    apply h_cpow_aestrong.smul
    apply AEStronglyMeasurable.indicator _ measurableSet_Ioo
    exact h_kernel_aestrong.sub h_neg_half_aestrong
  have h_upper_int :
      Integrable (fun t : ℝ => (t : ℂ) ^ (s/2 - 1) •
        ((Set.Ioi (1:ℝ)).indicator
          (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) - 1) t))
        (volume.restrict (Set.Ioi 0)) :=
    MeasureTheory.Integrable.mono h_strong_mellin h_aestrong_upper
      (ae_of_all _ h_bound_upper)
  have h_lower_int :
      Integrable (fun t : ℝ => (t : ℂ) ^ (s/2 - 1) •
        ((Set.Ioo (0:ℝ) 1).indicator
          (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) -
            ((x ^ (-(1/2 : ℝ)) : ℝ) : ℂ)) t))
        (volume.restrict (Set.Ioi 0)) :=
    MeasureTheory.Integrable.mono h_strong_mellin h_aestrong_lower
      (ae_of_all _ h_bound_lower)
  rw [MeasureTheory.integral_add h_upper_int h_lower_int]
  rw [mellinFmodif_upper s, mellinFmodif_lower s]
  unfold symmetricIntegrand
  -- Integrability of each half on Ioi 1 (for the inner integral_add)
  -- Derive integrability of the two halves on Ioi 1 from h_upper_int/h_lower_int
  -- via indicator localization (the same technique as in mellinFmodif_upper/_lower).
  have h_int1 : Integrable (fun u : ℝ =>
      ((HurwitzZeta.evenKernel 0 u : ℝ) : ℂ) * (u : ℂ)^(s/2 - 1) -
        (u : ℂ)^(s/2 - 1)) (volume.restrict (Set.Ioi 1)) := by
    -- h_upper_int is integrability on Ioi 0 of cpow • (Ioi 1).indicator (evenKernel - 1)
    -- Move smul inside indicator, then use integrable_indicator_iff
    have h_upper_eq : ∀ u : ℝ,
        (u : ℂ) ^ (s/2 - 1) •
          ((Set.Ioi (1:ℝ)).indicator
            (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) - 1) u) =
        (Set.Ioi (1:ℝ)).indicator
          (fun x => (x : ℂ) ^ (s/2 - 1) •
            (((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) - 1)) u := by
      intro u
      by_cases hu : u ∈ Set.Ioi (1:ℝ)
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, smul_zero]
    have h_upper_ind : Integrable (fun u : ℝ =>
        (Set.Ioi (1:ℝ)).indicator
          (fun x => (x : ℂ) ^ (s/2 - 1) •
            (((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) - 1)) u)
        (volume.restrict (Set.Ioi 0)) := by
      have : (fun u : ℝ => (u : ℂ) ^ (s/2 - 1) •
          ((Set.Ioi (1:ℝ)).indicator
            (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) - 1) u)) =
        (fun u : ℝ =>
          (Set.Ioi (1:ℝ)).indicator
            (fun x => (x : ℂ) ^ (s/2 - 1) •
              (((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) - 1)) u) := funext h_upper_eq
      rw [this] at h_upper_int; exact h_upper_int
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioi] at h_upper_ind
    -- h_upper_ind : IntegrableOn ... (Ioi 1) (volume.restrict (Ioi 0))
    --             = Integrable ... ((volume.restrict (Ioi 0)).restrict (Ioi 1))
    have h_restrict_eq : ((volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi 0)).restrict
        (Set.Ioi 1) = volume.restrict (Set.Ioi 1) := by
      rw [MeasureTheory.Measure.restrict_restrict measurableSet_Ioi]
      congr 1
      exact Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
    rw [MeasureTheory.IntegrableOn, h_restrict_eq] at h_upper_ind
    apply h_upper_ind.congr
    refine ae_of_all _ (fun u => ?_)
    simp only [smul_eq_mul]
    ring
  have h_int2 : Integrable (fun u : ℝ =>
      ((HurwitzZeta.evenKernel 0 u : ℝ) : ℂ) * (u : ℂ)^(-s/2 - (1/2 : ℂ)) -
        (u : ℂ)^(-s/2 - (1/2 : ℂ))) (volume.restrict (Set.Ioi 1)) := by
    -- Step 1: Move cpow inside the (Ioo 0 1) indicator
    have h_lower_eq : ∀ u : ℝ,
        (u : ℂ) ^ (s/2 - 1) •
          ((Set.Ioo (0:ℝ) 1).indicator
            (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) -
              ((x ^ (-(1/2 : ℝ)) : ℝ) : ℂ)) u) =
        (Set.Ioo (0:ℝ) 1).indicator
          (fun x => (x : ℂ) ^ (s/2 - 1) •
            (((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) -
             ((x ^ (-(1/2 : ℝ)) : ℝ) : ℂ))) u := by
      intro u
      by_cases hu : u ∈ Set.Ioo (0:ℝ) 1
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, smul_zero]
    have h_lower_ind : Integrable (fun u : ℝ =>
        (Set.Ioo (0:ℝ) 1).indicator
          (fun x => (x : ℂ) ^ (s/2 - 1) •
            (((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) -
             ((x ^ (-(1/2 : ℝ)) : ℝ) : ℂ))) u)
        (volume.restrict (Set.Ioi 0)) := by
      have heq : (fun u : ℝ => (u : ℂ) ^ (s/2 - 1) •
          ((Set.Ioo (0:ℝ) 1).indicator
            (fun x => ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) -
              ((x ^ (-(1/2 : ℝ)) : ℝ) : ℂ)) u)) =
        (fun u : ℝ =>
          (Set.Ioo (0:ℝ) 1).indicator
            (fun x => (x : ℂ) ^ (s/2 - 1) •
              (((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) -
               ((x ^ (-(1/2 : ℝ)) : ℝ) : ℂ))) u) := funext h_lower_eq
      rw [heq] at h_lower_int; exact h_lower_int
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioo] at h_lower_ind
    -- Step 2: Rewrite to `Integrable ... (volume.restrict (Ioo 0 1))`
    have h_restrict_Ioo : ((volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi 0)).restrict
        (Set.Ioo 0 1) = volume.restrict (Set.Ioo 0 1) := by
      rw [MeasureTheory.Measure.restrict_restrict measurableSet_Ioo]
      congr 1
      exact Set.inter_eq_left.mpr Set.Ioo_subset_Ioi_self
    rw [MeasureTheory.IntegrableOn, h_restrict_Ioo] at h_lower_ind
    -- Step 3: Apply change of variables u = 1/t, Ioi 1 → Ioo 0 1
    -- h_lower_ind : IntegrableOn g (Ioo 0 1) where g x = cpow x • (evenKernel 0 x - x^(-1/2))
    set φ : ℝ → ℝ := fun t => 1/t
    set φ' : ℝ → ℝ := fun t => -1/t^2
    have h_image : φ '' Set.Ioi (1 : ℝ) = Set.Ioo (0:ℝ) 1 := by
      ext u
      simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Ioo, φ]
      refine ⟨?_, ?_⟩
      · rintro ⟨t, ht, rfl⟩; exact ⟨by positivity,
          by rw [div_lt_one (by linarith : (0:ℝ) < t)]; linarith⟩
      · rintro ⟨h0, h1⟩; exact ⟨1/u, by rw [lt_div_iff₀ h0]; linarith,
          by rw [one_div, one_div, inv_inv]⟩
    have h_inj : Set.InjOn φ (Set.Ioi (1 : ℝ)) := by
      intro x hx y _ hxy
      simp only [φ, one_div] at hxy
      have hx_pos : 0 < x := by linarith [Set.mem_Ioi.mp hx]
      exact inv_injective (by rw [hxy])
    have h_deriv : ∀ t ∈ Set.Ioi (1:ℝ), HasDerivWithinAt φ (φ' t) (Set.Ioi (1:ℝ)) t := by
      intro t ht
      have ht_pos : 0 < t := by linarith [Set.mem_Ioi.mp ht]
      have ht_ne : t ≠ 0 := ht_pos.ne'
      have h_one_div : (fun y : ℝ => (1 : ℝ) / y) = (fun y : ℝ => y⁻¹) := by
        funext y; rw [one_div]
      have h_inv_d : HasDerivAt (fun y : ℝ => y⁻¹) (-(t^2)⁻¹) t := hasDerivAt_inv ht_ne
      have h_one_div_d : HasDerivAt φ (-(t^2)⁻¹) t := by
        simp only [φ, h_one_div]; exact h_inv_d
      have h_eq_φ' : φ' t = -(t^2)⁻¹ := by simp [φ']; field_simp
      rw [h_eq_φ']
      exact h_one_div_d.hasDerivWithinAt
    rw [← h_image] at h_lower_ind
    have h_lower_ind' : IntegrableOn
        (fun x : ℝ => (x : ℂ) ^ (s/2 - 1) • (((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ) -
          ((x ^ (-(1/2 : ℝ)) : ℝ) : ℂ))) (φ '' Set.Ioi 1) volume := h_lower_ind
    rw [MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi h_deriv h_inj] at h_lower_ind'
    -- Step 4: simplify |φ'| • g(φ t) = target integrand
    apply h_lower_ind'.congr
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    -- Now ht : t ∈ Ioi 1
    -- Need to show: |φ' t| • (φ t:ℂ)^(s/2-1) • (...) = target
    -- This is the exact same algebra as in mellinFmodif_lower
    · have ht_pos : 0 < t := by linarith [Set.mem_Ioi.mp ht]
      have ht_ne : t ≠ 0 := ht_pos.ne'
      have ht_inv_pos : 0 < 1/t := by positivity
      have h_abs : |φ' t| = 1/t^2 := by
        show |-1/t^2| = 1/t^2
        have h : -1/t^2 = -(1/t^2) := by ring
        rw [h, abs_neg, abs_of_pos]; positivity
      have h_FE : HurwitzZeta.evenKernel 0 (1/t) = t^(1/2 : ℝ) * HurwitzZeta.evenKernel 0 t := by
        have := HurwitzZeta.evenKernel_functional_equation (0 : UnitAddCircle) t
        rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero] at this
        rw [HurwitzZeta.evenKernel_functional_equation]
        rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
        have h_inv : (1:ℝ)/(1/t) = t := by field_simp
        rw [h_inv]
        have h_sqrt_pos : (0:ℝ) < (1/t)^(1/2 : ℝ) := Real.rpow_pos_of_pos ht_inv_pos _
        field_simp
        rw [show ((1:ℝ)/t)^(1/2 : ℝ) = 1 / t^(1/2 : ℝ) by
          rw [Real.div_rpow zero_le_one ht_pos.le, Real.one_rpow]]
        field_simp
      have h_pow_neg_half : (1/t : ℝ)^(-(1/2 : ℝ)) = t^(1/2 : ℝ) := by
        rw [Real.div_rpow zero_le_one ht_pos.le, Real.one_rpow]
        rw [Real.rpow_neg ht_pos.le]
        field_simp
      show |φ' t| • ((φ t : ℂ) ^ (s/2 - 1) •
          (((HurwitzZeta.evenKernel 0 (φ t) : ℝ) : ℂ) -
            (((φ t) ^ (-(1/2 : ℝ)) : ℝ) : ℂ))) =
        ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) * (t : ℂ) ^ (-s/2 - (1/2 : ℂ)) -
          (t : ℂ) ^ (-s/2 - (1/2 : ℂ))
      rw [h_abs]
      show ((1/t^2 : ℝ) : ℂ) * (((1/t : ℝ) : ℂ) ^ (s/2 - 1) *
            (((HurwitzZeta.evenKernel 0 (1/t) : ℝ) : ℂ) -
              (((1/t) ^ (-(1/2 : ℝ)) : ℝ) : ℂ))) = _
      rw [h_FE, h_pow_neg_half]
      have h_cpow_inv : (((1/t : ℝ)) : ℂ) ^ (s/2 - 1) = (t : ℂ) ^ (-(s/2 - 1)) := by
        rw [show ((1/t : ℝ) : ℂ) = ((t : ℝ) : ℂ)⁻¹ by push_cast; rw [one_div]]
        rw [Complex.inv_cpow_eq_ite]
        have h_arg : (t : ℂ).arg ≠ Real.pi := by
          rw [Complex.arg_ofReal_of_nonneg ht_pos.le]; exact Real.pi_pos.ne
        simp only [h_arg, if_false]
        rw [Complex.cpow_neg]
      rw [h_cpow_inv]
      push_cast
      have ht_C_ne : (t : ℂ) ≠ 0 := by exact_mod_cast ht_ne
      have h_inv_sq_cpow : (1 : ℂ) / (t : ℂ)^2 = (t : ℂ)^(-(2:ℂ)) := by
        rw [show ((-2 : ℂ)) = -(2:ℂ) from rfl, Complex.cpow_neg]
        rw [show ((2:ℂ)) = ((2:ℕ) : ℂ) by norm_num]
        rw [Complex.cpow_natCast]; field_simp
      have h_sqrt_cpow : ((t^(1/2 : ℝ) : ℝ) : ℂ) = (t : ℂ)^((1/2 : ℂ)) := by
        rw [Complex.ofReal_cpow ht_pos.le]; push_cast; rfl
      rw [h_inv_sq_cpow, h_sqrt_cpow]
      have h_exp1 : (t : ℂ)^(-(2:ℂ)) * (t : ℂ)^(-(s/2-1)) * (t : ℂ)^((1/2 : ℂ)) =
          (t : ℂ)^(-s/2 - 1/2) := by
        rw [← Complex.cpow_add _ _ ht_C_ne, ← Complex.cpow_add _ _ ht_C_ne]
        congr 1; ring
      calc (t : ℂ)^(-(2:ℂ)) * ((t : ℂ)^(-(s/2-1)) *
              ((t : ℂ)^((1/2 : ℂ)) * ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) -
                (t : ℂ)^((1/2 : ℂ))))
          = ((((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1)) *
              ((t : ℂ)^(-(2:ℂ)) * (t : ℂ)^(-(s/2-1)) * (t : ℂ)^((1/2 : ℂ))) := by ring
        _ = ((((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1)) * (t : ℂ)^(-s/2 - 1/2) := by
              rw [h_exp1]
        _ = ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) * (t : ℂ)^(-s/2 - 1/2) -
              (t : ℂ)^(-s/2 - 1/2) := by ring
  rw [← MeasureTheory.integral_add h_int1 h_int2]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u _
  ring

/-- Helper: `(Real.exp t : ℂ) ^ z = Complex.exp (t · z)`. -/
private lemma cpow_real_exp (t : ℝ) (z : ℂ) :
    (Real.exp t : ℂ) ^ z = Complex.exp ((t : ℂ) * z) := by
  rw [Complex.ofReal_exp]
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _)]
  congr 1
  rw [Complex.log_exp]
  · simp [Complex.ofReal_im, Real.pi_pos]
  · simp [Complex.ofReal_im, Real.pi_pos.le]

/-- Helper: `(Complex.exp z) ^ w = Complex.exp (z * w)` when `z.im ∈ (-π, π]`. -/
private lemma cexp_cpow (z w : ℂ) (h_im_lt : z.im ≤ Real.pi) (h_im_gt : -Real.pi < z.im) :
    (Complex.exp z) ^ w = Complex.exp (z * w) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _)]
  congr 1
  rw [Complex.log_exp h_im_gt h_im_lt]

/-- Pointwise integrand identity: substituting `u = exp(2t)` rewrites the
cosh-kernel integrand as `(2·exp(2t)) · ((1/2) · symmetricIntegrand s (exp(2t)))`. -/
private lemma integrand_substitution (s : ℂ) (t : ℝ) :
    (2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)) * ((ψ_mellin t : ℂ)) =
      ((2 * Real.exp (2 * t) : ℝ) : ℂ) *
        ((1/2 : ℂ) * symmetricIntegrand s (Real.exp (2 * t))) := by
  unfold ψ_mellin symmetricIntegrand
  push_cast
  -- After push_cast, ↑(Real.exp(2t)) becomes cexp(2 * ↑t). Use cexp_cpow.
  have h_im2 : ((2 * (t : ℂ))).im = 0 := by simp
  rw [cexp_cpow (2 * (t : ℂ)) (s/2 - 1) (by rw [h_im2]; positivity) (by rw [h_im2]; linarith [Real.pi_pos])]
  rw [cexp_cpow (2 * (t : ℂ)) (-s/2 - 1/2) (by rw [h_im2]; positivity) (by rw [h_im2]; linarith [Real.pi_pos])]
  -- Use 2 * cosh = exp + exp(-·)
  have h_cosh : (2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)) =
      Complex.exp ((s - 1/2) * (t : ℂ)) + Complex.exp (-((s - 1/2) * (t : ℂ))) :=
    Complex.two_cosh _
  -- Now everything is in terms of Complex.exp; use exp_add to combine
  have h1 : Complex.exp ((s - 1/2) * (t : ℂ)) * Complex.exp ((t : ℂ)/2) =
      Complex.exp ((s : ℂ) * t) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h2 : Complex.exp (-((s - 1/2) * (t : ℂ))) * Complex.exp ((t : ℂ)/2) =
      Complex.exp (((1 : ℂ) - s) * t) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h5 : Complex.exp (2 * (t : ℂ)) * Complex.exp (2 * (t : ℂ) * (s/2 - 1)) =
      Complex.exp ((s : ℂ) * t) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h6 : Complex.exp (2 * (t : ℂ)) * Complex.exp (2 * (t : ℂ) * (-s/2 - 1/2)) =
      Complex.exp (((1 : ℂ) - s) * t) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  set Z : ℂ := ((HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) : ℝ) : ℂ)
  -- Both sides equal (Z - 1) · (cexp(s·t) + cexp((1-s)·t))
  have lhs_collapse : (2 * Complex.cosh ((s - 1/2) * (t : ℂ))) * Complex.exp ((t : ℂ)/2) =
      Complex.exp ((s : ℂ) * t) + Complex.exp (((1 : ℂ) - s) * t) := by
    rw [h_cosh, add_mul, h1, h2]
  have rhs_collapse : Complex.exp (2 * (t : ℂ)) *
      (Complex.exp (2 * (t : ℂ) * (s/2 - 1)) +
       Complex.exp (2 * (t : ℂ) * (-s/2 - 1/2))) =
      Complex.exp ((s : ℂ) * t) + Complex.exp (((1 : ℂ) - s) * t) := by
    rw [mul_add, h5, h6]
  -- Now both sides reduce to the same expression
  linear_combination (Z - 1) * lhs_collapse - (Z - 1) * rhs_collapse

/-! ### Integrability hypotheses (still needed) -/

/-- The cosh-kernel integrand for `ψ_mellin` at parameter `s` is integrable on `Ioi 0`.

Proof: continuity on `Ici 0` (for local integrability) + big-O bound at `+∞` of
the form `O(exp(-t/4))`, then `LocallyIntegrableOn.integrableOn_of_isBigO_atTop`.
The big-O bound is built from:
* `‖2·cosh((s-1/2)·t)‖ ≤ 2·exp(α·|t|)` with `α := ‖s − 1/2‖`
* `evenKernel 0 (exp 2t) − 1 =O[atTop] exp(-(α+1)·t)`, which uses the doubly-
  exponential decay of `evenKernel 0 - 1` (Mathlib's `isBigO_atTop_evenKernel_sub`
  composed with `Tendsto exp(2·) atTop atTop`), and then dominates `exp(-(α+1)·t)`
  via `Real.tendsto_exp_div_pow_atTop 1`. -/
theorem integrable_I_theta_integrand (s : ℂ) :
    IntegrableOn (fun t : ℝ =>
      (2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)) * ((ψ_mellin t : ℂ)))
      (Set.Ioi 0) := by
  have h_cont : ContinuousOn (fun t : ℝ =>
      (2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)) * ((ψ_mellin t : ℂ)))
      (Set.Ici (0 : ℝ)) := by
    have h_cosh : Continuous fun t : ℝ =>
        (2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)) := by
      apply Continuous.mul continuous_const
      apply Complex.continuous_cosh.comp
      exact (continuous_const.mul Complex.continuous_ofReal)
    have h_evk : ContinuousOn (fun t : ℝ =>
        ((HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) - 1) * Real.exp (t/2) : ℂ))
        (Set.Ici (0 : ℝ)) := by
      have h_kernel : ContinuousOn
          (fun t : ℝ => (HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) - 1)) (Set.Ici (0 : ℝ)) := by
        have h_inner : Continuous (fun t : ℝ => Real.exp (2 * t)) :=
          Real.continuous_exp.comp (continuous_const.mul continuous_id)
        have h_pos : ∀ t : ℝ, Real.exp (2 * t) ∈ Set.Ioi (0 : ℝ) :=
          fun t => Real.exp_pos _
        have h_kev : ContinuousOn (fun u : ℝ => HurwitzZeta.evenKernel 0 u) (Set.Ioi (0:ℝ)) :=
          HurwitzZeta.continuousOn_evenKernel 0
        exact (h_kev.comp h_inner.continuousOn (fun t _ => h_pos t)).sub continuousOn_const
      have h_R : Continuous (fun t : ℝ => Real.exp (t/2)) :=
        Real.continuous_exp.comp (continuous_id.mul continuous_const)
      have h_prod : ContinuousOn
          (fun t : ℝ => (HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) - 1) * Real.exp (t/2))
          (Set.Ici (0 : ℝ)) := h_kernel.mul h_R.continuousOn
      have h_C : ContinuousOn
          (fun t : ℝ => (((HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) - 1) *
            Real.exp (t/2) : ℝ) : ℂ)) (Set.Ici (0 : ℝ)) :=
        Complex.continuous_ofReal.comp_continuousOn h_prod
      have h_eq : (fun t : ℝ => (((HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) - 1) *
            Real.exp (t/2) : ℝ) : ℂ)) =
          (fun t : ℝ => ((HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) - 1) *
            Real.exp (t/2) : ℂ)) := by
        funext t; push_cast; ring
      rw [← h_eq]; exact h_C
    have h_psi : ContinuousOn (fun t : ℝ => ((ψ_mellin t : ℝ) : ℂ)) (Set.Ici (0 : ℝ)) := by
      unfold ψ_mellin
      have : (fun t : ℝ => (((HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) - 1) *
          Real.exp (t / 2) : ℝ) : ℂ)) =
          (fun t : ℝ => ((HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) - 1) *
            Real.exp (t/2) : ℂ)) := by
        funext t; push_cast; ring
      rw [this]
      exact h_evk
    exact h_cosh.continuousOn.mul h_psi
  have h_loc : LocallyIntegrableOn (fun t : ℝ =>
      (2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)) * ((ψ_mellin t : ℂ)))
      (Set.Ici (0 : ℝ)) volume :=
    h_cont.locallyIntegrableOn measurableSet_Ici
  -- Get evenKernel decay
  obtain ⟨p, hp_pos, hp_decay⟩ :=
    HurwitzZeta.isBigO_atTop_evenKernel_sub (0 : UnitAddCircle)
  simp only [if_pos rfl] at hp_decay
  -- Big-O at infinity for the integrand:
  -- |2 cosh((s-1/2)t)| ≤ 2 exp(α · |t|) where α = |Re(s-1/2)| + 1
  -- |ψ_mellin t| = |evenKernel 0 (exp 2t) - 1| · exp(t/2)
  -- |evenKernel 0 (exp 2t) - 1| =O[t→∞] exp(-p · exp 2t) (via composition)
  -- exp(-p · exp 2t) =o[t→∞] exp(-K · t) for any K > 0 (super-exp dominates exp)
  -- Net: integrand =O[t→∞] exp(-K · t) for any K > 0
  set α : ℝ := ‖s - 1/2‖
  -- Bound on cosh
  have h_cosh_bound : ∀ t : ℝ, ‖(2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ))‖ ≤
      2 * Real.exp (α * |t|) := by
    intro t
    rw [norm_mul, Complex.norm_two]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
    have h_arg : ‖(s - 1/2) * (t : ℂ)‖ ≤ α * |t| := by
      rw [norm_mul]
      show ‖s - 1/2‖ * ‖(t : ℂ)‖ ≤ ‖s - 1/2‖ * |t|
      rw [Complex.norm_real, Real.norm_eq_abs]
    have h_cosh_le : ‖Complex.cosh ((s - 1/2) * (t : ℂ))‖ ≤
        Real.exp (‖(s - 1/2) * (t : ℂ)‖) := by
      set z : ℂ := (s - 1/2) * (t : ℂ)
      rw [Complex.cosh]
      rw [show (Complex.exp z + Complex.exp (-z)) / 2 =
          (1/2 : ℂ) * (Complex.exp z + Complex.exp (-z)) from by ring]
      rw [norm_mul]
      have hnz : ‖(1/2 : ℂ)‖ = 1/2 := by simp [norm_div]
      rw [hnz]
      have h_add : ‖Complex.exp z + Complex.exp (-z)‖ ≤ 2 * Real.exp ‖z‖ := by
        calc ‖Complex.exp z + Complex.exp (-z)‖
            ≤ ‖Complex.exp z‖ + ‖Complex.exp (-z)‖ := norm_add_le _ _
          _ ≤ Real.exp ‖z‖ + Real.exp ‖-z‖ := by
              gcongr <;> exact Complex.norm_exp_le_exp_norm _
          _ = 2 * Real.exp ‖z‖ := by rw [norm_neg]; ring
      linarith [h_add, Real.exp_pos ‖z‖]
    exact h_cosh_le.trans (Real.exp_le_exp.mpr h_arg)
  -- Decay of evenKernel 0 (exp 2·) - 1 dominates exp(-(α+1)·t)
  have h_kernel_decay : (fun t : ℝ => HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) - 1)
      =O[Filter.atTop] (fun t : ℝ => Real.exp (-(α + 1) * t)) := by
    have h_comp : (fun t : ℝ => HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) - 1)
        =O[Filter.atTop] (fun t : ℝ => Real.exp (-p * Real.exp (2 * t))) := by
      have h_tendsto : Filter.Tendsto (fun t : ℝ => Real.exp (2 * t))
          Filter.atTop Filter.atTop :=
        Real.tendsto_exp_atTop.comp (Filter.tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))
      exact hp_decay.comp_tendsto h_tendsto
    -- Direct bound: eventually exp(-p·exp(2t)) ≤ exp(-(α+1)·t)
    have h_dom : (fun t : ℝ => Real.exp (-p * Real.exp (2 * t)))
        =O[Filter.atTop] (fun t : ℝ => Real.exp (-(α + 1) * t)) := by
      refine Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩
      -- Eventually p · exp(2t) ≥ (α+1)·t  ⇒  -p·exp(2t) ≤ -(α+1)·t  ⇒  exp(...) ≤ exp(...)
      -- We use that exp(2t) / t → ∞, hence exp(2t) ≥ ((α+1)/p) · t eventually
      have h_grow : Filter.Tendsto (fun t : ℝ => Real.exp (2 * t) / t)
          Filter.atTop Filter.atTop := by
        have h1 : Filter.Tendsto (fun u : ℝ => Real.exp u / u ^ (1 : ℕ))
            Filter.atTop Filter.atTop := Real.tendsto_exp_div_pow_atTop 1
        have h2 : Filter.Tendsto (fun t : ℝ => 2 * t) Filter.atTop Filter.atTop :=
          Filter.tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2)
        have h3 : Filter.Tendsto (fun t : ℝ => Real.exp (2 * t) / (2 * t))
            Filter.atTop Filter.atTop := by
          simpa using h1.comp h2
        -- exp(2t)/t = 2 · (exp(2t)/(2t))
        have h_eq : (fun t : ℝ => Real.exp (2 * t) / t) =ᶠ[Filter.atTop]
            (fun t : ℝ => 2 * (Real.exp (2 * t) / (2 * t))) := by
          filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
          field_simp
        exact (h3.const_mul_atTop (by norm_num : (0:ℝ) < 2)).congr' h_eq.symm
      -- Get t large enough that exp(2t) / t ≥ (α+1)/p
      have h_key : ∀ᶠ t : ℝ in Filter.atTop, p * Real.exp (2 * t) ≥ (α + 1) * t := by
        have hαp_pos : 0 < (α + 1) / p := div_pos (by
          have : 0 ≤ α := norm_nonneg _
          linarith) hp_pos
        have h_event := h_grow.eventually_ge_atTop ((α + 1) / p)
        filter_upwards [h_event, Filter.eventually_gt_atTop (0:ℝ)] with t ht htp
        have h1 : Real.exp (2 * t) / t ≥ (α + 1) / p := ht
        have h2 : Real.exp (2 * t) ≥ ((α + 1) / p) * t := by
          have := mul_le_mul_of_nonneg_right h1 htp.le
          rwa [div_mul_cancel₀ _ htp.ne'] at this
        have h3 : p * Real.exp (2 * t) ≥ p * (((α + 1) / p) * t) :=
          mul_le_mul_of_nonneg_left h2 hp_pos.le
        rw [show p * (((α + 1) / p) * t) = (α + 1) * t from by
          field_simp] at h3
        exact h3
      filter_upwards [h_key] with t ht
      have h_neg : -p * Real.exp (2 * t) ≤ -(α + 1) * t := by linarith
      have h_le : Real.exp (-p * Real.exp (2 * t)) ≤ Real.exp (-(α + 1) * t) :=
        Real.exp_le_exp.mpr h_neg
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
      exact h_le
    exact h_comp.trans h_dom
  -- Combine: integrand =O[atTop] exp(-t/4) via the bounds above
  have h_main_BigO : (fun t : ℝ =>
      (2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)) * ((ψ_mellin t : ℂ)))
      =O[Filter.atTop] (fun t : ℝ => Real.exp (-t / 4)) := by
    -- ψ_mellin as ℂ: |.| = |evenKernel 0 (exp 2t) - 1| * exp(t/2)
    have h_psi_norm : ∀ t : ℝ, ‖((ψ_mellin t : ℝ) : ℂ)‖ =
        |HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) - 1| * Real.exp (t/2) := by
      intro t
      rw [Complex.norm_real, Real.norm_eq_abs]
      unfold ψ_mellin
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    -- ψ_mellin =O[atTop] exp(-(α + 1/2) · t)
    have h_psi_BigO : (fun t : ℝ => ((ψ_mellin t : ℝ) : ℂ)) =O[Filter.atTop]
        (fun t : ℝ => Real.exp (-(α + 1/2) * t)) := by
      refine Asymptotics.isBigO_iff.mpr ?_
      obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp h_kernel_decay
      refine ⟨C, ?_⟩
      filter_upwards [hC, Filter.eventually_ge_atTop (0:ℝ)] with t hkt _
      rw [h_psi_norm]
      have h_pos : 0 < Real.exp (t/2) := Real.exp_pos _
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at *
      have h_split : Real.exp (-(α + 1/2) * t) =
          Real.exp (-(α + 1) * t) * Real.exp (t/2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h_split]
      calc |HurwitzZeta.evenKernel 0 (Real.exp (2 * t)) - 1| * Real.exp (t/2)
          ≤ (C * Real.exp (-(α + 1) * t)) * Real.exp (t/2) :=
            mul_le_mul_of_nonneg_right hkt h_pos.le
        _ = C * (Real.exp (-(α + 1) * t) * Real.exp (t/2)) := by ring
    -- 2 cosh =O[atTop] exp(α · t) (since for t ≥ 0, |t| = t)
    have h_cosh_BigO : (fun t : ℝ => (2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)))
        =O[Filter.atTop] (fun t : ℝ => Real.exp (α * t)) := by
      refine Asymptotics.isBigO_iff.mpr ⟨2, ?_⟩
      filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with t ht
      have h_abs : |t| = t := abs_of_nonneg ht
      have := h_cosh_bound t
      rw [h_abs] at this
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      linarith
    -- Product BigO
    have h_prod_BigO :
        (fun t : ℝ => (2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)) * ((ψ_mellin t : ℂ)))
        =O[Filter.atTop]
        (fun t : ℝ => Real.exp (α * t) * Real.exp (-(α + 1/2) * t)) :=
      h_cosh_BigO.mul h_psi_BigO
    -- exp(α t) · exp(-(α+1/2) t) = exp(-t/2)
    have h_simplify : (fun t : ℝ => Real.exp (α * t) * Real.exp (-(α + 1/2) * t)) =
        (fun t : ℝ => Real.exp (-t/2)) := by
      funext t
      rw [← Real.exp_add]; congr 1; ring
    rw [h_simplify] at h_prod_BigO
    -- exp(-t/2) =O exp(-t/4)
    have h_final : (fun t : ℝ => Real.exp (-t/2)) =O[Filter.atTop]
        (fun t : ℝ => Real.exp (-t/4)) := by
      refine Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩
      filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with t ht
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
      apply Real.exp_le_exp.mpr; linarith
    exact h_prod_BigO.trans h_final
  have h_g_int : IntegrableAtFilter (fun t : ℝ => Real.exp (-t / 4)) Filter.atTop volume := by
    refine ⟨Set.Ioi (0:ℝ), Filter.Ioi_mem_atTop _, ?_⟩
    have : (fun t : ℝ => Real.exp (-t/4)) = (fun t : ℝ => Real.exp (-(1/4 : ℝ) * t)) := by
      funext t; ring_nf
    rw [this]
    exact exp_neg_integrableOn_Ioi 0 (by norm_num)
  have h_int_Ici := h_loc.integrableOn_of_isBigO_atTop h_main_BigO h_g_int
  exact h_int_Ici.mono_set Set.Ioi_subset_Ici_self

/-- The symmetric integrand is integrable on `Ioi 1`. Required for the substitution
lemma's RHS integrability hypothesis.

Proof: `evenKernel 0 - 1` decays exponentially at +∞ (`isBigO_atTop_evenKernel_sub`).
Multiplied by polynomial cpow factors, the result is still O(exp(-q·u)) for some
`q > 0`. Continuous on `Ici 1` by `evenKernel` continuous + cpow continuity at
`u ≠ 0`. Then `LocallyIntegrableOn.integrableOn_of_isBigO_atTop`. -/
theorem integrable_symmetricIntegrand (s : ℂ) :
    IntegrableOn (symmetricIntegrand s) (Set.Ioi 1) := by
  -- Step 1: continuity of symmetricIntegrand on Ici 1 (for local integrability)
  have h_cont_Ici : ContinuousOn (symmetricIntegrand s) (Set.Ici 1) := by
    have h_kernel : ContinuousOn (fun u : ℝ => ((HurwitzZeta.evenKernel 0 u : ℝ) : ℂ) - 1)
        (Set.Ici (1 : ℝ)) := by
      have hev : ContinuousOn (fun u : ℝ => (HurwitzZeta.evenKernel 0 u : ℝ))
          (Set.Ici (1 : ℝ)) :=
        (HurwitzZeta.continuousOn_evenKernel 0).mono
          (fun u hu => lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hu)
      exact (Complex.continuous_ofReal.comp_continuousOn hev).sub continuousOn_const
    have h_cpow1 : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (s/2 - 1)) (Set.Ici (1 : ℝ)) := by
      intro u hu
      apply (Complex.continuousAt_ofReal_cpow_const u (s/2 - 1) (Or.inr ?_)).continuousWithinAt
      linarith [Set.mem_Ici.mp hu]
    have h_cpow2 : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s/2 - (1/2 : ℂ))) (Set.Ici (1 : ℝ)) := by
      intro u hu
      apply (Complex.continuousAt_ofReal_cpow_const u (-s/2 - 1/2) (Or.inr ?_)).continuousWithinAt
      linarith [Set.mem_Ici.mp hu]
    unfold symmetricIntegrand
    exact h_kernel.mul (h_cpow1.add h_cpow2)
  -- Step 2: local integrability
  have h_loc : LocallyIntegrableOn (symmetricIntegrand s) (Set.Ici 1) volume :=
    h_cont_Ici.locallyIntegrableOn measurableSet_Ici
  -- Step 3: get the evenKernel decay rate p
  obtain ⟨p, hp_pos, hp_decay⟩ :=
    HurwitzZeta.isBigO_atTop_evenKernel_sub (0 : UnitAddCircle)
  simp only [if_pos rfl] at hp_decay
  -- Step 4: big-O bound on symmetricIntegrand
  -- |symmetricIntegrand s u| ≤ |evenKernel 0 u - 1| · (u^Re(s/2-1) + u^Re(-s/2-1/2))
  -- = O(exp(-p u)) · poly = O(exp(-p/2 · u))
  set A : ℝ := (s/2 - 1).re
  set B : ℝ := (-s/2 - (1/2 : ℂ)).re
  have h_polyA_BigO : (fun u : ℝ => u ^ A) =O[Filter.atTop]
      (fun u : ℝ => Real.exp (p / 4 * u)) := by
    have : (fun u : ℝ => u ^ A) =o[Filter.atTop] (fun u : ℝ => Real.exp (p / 4 * u)) :=
      isLittleO_rpow_exp_pos_mul_atTop A (by linarith)
    exact this.isBigO
  have h_polyB_BigO : (fun u : ℝ => u ^ B) =O[Filter.atTop]
      (fun u : ℝ => Real.exp (p / 4 * u)) := by
    have : (fun u : ℝ => u ^ B) =o[Filter.atTop] (fun u : ℝ => Real.exp (p / 4 * u)) :=
      isLittleO_rpow_exp_pos_mul_atTop B (by linarith)
    exact this.isBigO
  have h_sum_BigO : (fun u : ℝ => u ^ A + u ^ B) =O[Filter.atTop]
      (fun u : ℝ => Real.exp (p / 4 * u)) :=
    h_polyA_BigO.add h_polyB_BigO
  -- Bound on cpow: |u^z| = u^Re(z) for u > 0
  have h_cpow_bound : ∀ᶠ u : ℝ in Filter.atTop,
      ‖(u : ℂ) ^ (s/2 - 1) + (u : ℂ) ^ (-s/2 - (1/2 : ℂ))‖ ≤ u ^ A + u ^ B := by
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with u hu
    refine le_trans (norm_add_le _ _) ?_
    have hAeq : ‖(u : ℂ) ^ (s/2 - 1)‖ = u ^ A := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
    have hBeq : ‖(u : ℂ) ^ (-s/2 - (1/2 : ℂ))‖ = u ^ B := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
    rw [hAeq, hBeq]
  -- symmetricIntegrand =O[atTop] exp(-p/2 · ·)
  have h_main_BigO : (symmetricIntegrand s) =O[Filter.atTop]
      (fun u : ℝ => Real.exp (-(p / 2) * u)) := by
    have h_fact : (symmetricIntegrand s) =O[Filter.atTop]
        (fun u : ℝ => Real.exp (-p * u) * Real.exp (p / 4 * u)) := by
      unfold symmetricIntegrand
      have h_kernel_norm : (fun u : ℝ => ‖((HurwitzZeta.evenKernel 0 u : ℝ) : ℂ) - 1‖) =O[Filter.atTop]
          (fun u : ℝ => Real.exp (-p * u)) := by
        have hp_decay' : (fun u => HurwitzZeta.evenKernel 0 u - 1) =O[Filter.atTop]
            (fun u => Real.exp (-p * u)) := hp_decay
        have h_norm_eq : (fun u : ℝ => ‖((HurwitzZeta.evenKernel 0 u : ℝ) : ℂ) - 1‖) =
            (fun u : ℝ => |HurwitzZeta.evenKernel 0 u - 1|) := by
          funext u
          rw [show ((HurwitzZeta.evenKernel 0 u : ℝ) : ℂ) - 1 =
              ((HurwitzZeta.evenKernel 0 u - 1 : ℝ) : ℂ) by push_cast; ring]
          rw [Complex.norm_real]
          rfl
        rw [h_norm_eq]
        exact hp_decay'.norm_left
      have h_kernel_BigO : (fun u : ℝ => ((HurwitzZeta.evenKernel 0 u : ℝ) : ℂ) - 1) =O[Filter.atTop]
          (fun u : ℝ => Real.exp (-p * u)) :=
        Asymptotics.isBigO_norm_left.mp h_kernel_norm
      have h_step : (fun u : ℝ => (u : ℂ) ^ (s/2 - 1) + (u : ℂ) ^ (-s/2 - (1/2 : ℂ))) =O[Filter.atTop]
          (fun u : ℝ => u ^ A + u ^ B) := by
        refine Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩
        filter_upwards [Filter.eventually_gt_atTop (0:ℝ), h_cpow_bound] with u hu hbnd
        have h_sum_pos : 0 ≤ u ^ A + u ^ B :=
          add_nonneg (Real.rpow_nonneg hu.le A) (Real.rpow_nonneg hu.le B)
        calc ‖(u : ℂ) ^ (s/2 - 1) + (u : ℂ) ^ (-s/2 - (1/2 : ℂ))‖
            ≤ u ^ A + u ^ B := hbnd
          _ = ‖u ^ A + u ^ B‖ := by rw [Real.norm_eq_abs, abs_of_nonneg h_sum_pos]
          _ = 1 * ‖u ^ A + u ^ B‖ := (one_mul _).symm
      have h_sum_cpow_BigO :
          (fun u : ℝ => (u : ℂ) ^ (s/2 - 1) + (u : ℂ) ^ (-s/2 - (1/2 : ℂ))) =O[Filter.atTop]
          (fun u : ℝ => Real.exp (p / 4 * u)) :=
        h_step.trans h_sum_BigO
      exact h_kernel_BigO.mul h_sum_cpow_BigO
    -- exp(-p u) · exp(p/4 u) = exp(-3p/4 u) ≤ exp(-p/2 u) for u ≥ 0
    have h_simplify : (fun u : ℝ => Real.exp (-p * u) * Real.exp (p / 4 * u)) =
        (fun u : ℝ => Real.exp (-(3 * p / 4) * u)) := by
      funext u
      rw [← Real.exp_add]
      congr 1; ring
    rw [h_simplify] at h_fact
    -- exp(-(3p/4) u) =O[atTop] exp(-(p/2) u)
    have : (fun u : ℝ => Real.exp (-(3 * p / 4) * u)) =O[Filter.atTop]
        (fun u : ℝ => Real.exp (-(p / 2) * u)) := by
      apply Asymptotics.isBigO_iff.mpr
      refine ⟨1, ?_⟩
      filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with u hu
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [show (1 : ℝ) * Real.exp (-(p/2) * u) = Real.exp (-(p/2) * u) from one_mul _]
      apply Real.exp_le_exp.mpr
      nlinarith
    exact h_fact.trans this
  -- Step 5: apply LocallyIntegrableOn.integrableOn_of_isBigO_atTop
  have h_g_int : IntegrableAtFilter (fun u : ℝ => Real.exp (-(p / 2) * u)) Filter.atTop volume :=
    ⟨Set.Ioi (0 : ℝ), Filter.Ioi_mem_atTop _,
      exp_neg_integrableOn_Ioi 0 (by linarith)⟩
  have h_int_Ici := h_loc.integrableOn_of_isBigO_atTop h_main_BigO h_g_int
  exact h_int_Ici.mono_set Set.Ioi_subset_Ici_self

/-- Step B: the cosh-kernel integral, by substitution `u = exp(2t)`, equals
`(1/2)` times the same symmetric integral on `(1, ∞)`. Uses Mathlib's
`MeasureTheory.integral_comp_smul_deriv_Ioi` with `f(t) = exp(2t)`,
`f'(t) = 2·exp(2t)`, plus the pointwise `integrand_substitution`. -/
theorem I_theta_of_ψ_mellin_eq_symmetric_form (s : ℂ) :
    I_theta_of ψ_mellin s = (1 / 2 : ℂ) * ∫ u in Set.Ioi (1 : ℝ), symmetricIntegrand s u := by
  unfold I_theta_of
  -- Step 1: rewrite the integrand using integrand_substitution
  have h_cong : ∀ t ∈ Set.Ioi (0 : ℝ),
      (2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)) * ((ψ_mellin t : ℂ)) =
      ((2 * Real.exp (2 * t) : ℝ) : ℂ) *
        ((1/2 : ℂ) * symmetricIntegrand s (Real.exp (2 * t))) := fun t _ =>
    integrand_substitution s t
  rw [setIntegral_congr_fun measurableSet_Ioi h_cong]
  -- Step 2: factor as f' • (g ∘ f) where f(t) = exp(2t), f'(t) = 2 exp(2t),
  -- g(u) = (1/2) symmetricIntegrand s u
  set f : ℝ → ℝ := fun t => Real.exp (2 * t)
  set f' : ℝ → ℝ := fun t => 2 * Real.exp (2 * t)
  set g : ℝ → ℂ := fun u => (1/2 : ℂ) * symmetricIntegrand s u
  have h_factor : ∀ t ∈ Set.Ioi (0 : ℝ),
      ((2 * Real.exp (2 * t) : ℝ) : ℂ) *
        ((1/2 : ℂ) * symmetricIntegrand s (Real.exp (2 * t))) =
      (f' t : ℂ) * g (f t) := fun t _ => by
    simp [f, f', g]
  rw [setIntegral_congr_fun measurableSet_Ioi h_factor]
  -- Step 3: convert (f' t : ℂ) * g (f t) to (f' t) • g(f t) and apply substitution
  have h_smul : ∀ t : ℝ, (f' t : ℂ) * g (f t) = f' t • g (f t) := fun t => by
    simp [Complex.real_smul]
  rw [show (∫ t in Set.Ioi 0, (↑(f' t) : ℂ) * g (f t)) =
        ∫ t in Set.Ioi 0, f' t • g (f t) from
    setIntegral_congr_fun measurableSet_Ioi (fun t _ => h_smul t)]
  -- Step 4: apply integral_comp_smul_deriv_Ioi
  have hf_cont : ContinuousOn f (Set.Ici 0) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hft : Filter.Tendsto f Filter.atTop Filter.atTop := by
    show Filter.Tendsto (fun t => Real.exp (2 * t)) Filter.atTop Filter.atTop
    exact Real.tendsto_exp_atTop.comp
      (Filter.tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))
  have hff' : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivWithinAt f (f' x) (Set.Ioi x) x := fun x _ => by
    show HasDerivWithinAt (fun t => Real.exp (2 * t)) (2 * Real.exp (2 * x)) (Set.Ioi x) x
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
      simpa using (hasDerivAt_id x).const_mul 2
    have h2 : HasDerivAt (fun t => Real.exp (2 * t)) (Real.exp (2 * x) * 2) x :=
      (Real.hasDerivAt_exp (2 * x)).comp x h1
    have h3 : HasDerivAt (fun t => Real.exp (2 * t)) (2 * Real.exp (2 * x)) x := by
      convert h2 using 1; ring
    exact h3.hasDerivWithinAt
  have h_image : f '' Set.Ici (0 : ℝ) = Set.Ici 1 := by
    ext u
    simp only [Set.mem_image, Set.mem_Ici, f]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact Real.one_le_exp (by linarith)
    · intro hu
      refine ⟨Real.log u / 2, ?_, ?_⟩
      · exact div_nonneg (Real.log_nonneg hu) (by norm_num)
      · rw [show 2 * (Real.log u / 2) = Real.log u from by ring,
            Real.exp_log (by linarith)]
  have h_image_Ioi : f '' Set.Ioi (0 : ℝ) = Set.Ioi 1 := by
    ext u
    simp only [Set.mem_image, Set.mem_Ioi, f]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact Real.one_lt_exp_iff.mpr (by linarith)
    · intro hu
      refine ⟨Real.log u / 2, ?_, ?_⟩
      · apply div_pos _ (by norm_num)
        exact Real.log_pos hu
      · rw [show 2 * (Real.log u / 2) = Real.log u from by ring,
            Real.exp_log (by linarith)]
  have hg_cont : ContinuousOn g (f '' Set.Ioi (0 : ℝ)) := by
    rw [h_image_Ioi]
    show ContinuousOn (fun u => (1/2 : ℂ) * symmetricIntegrand s u) (Set.Ioi 1)
    -- evenKernel continuous on Ioi 0 ⊆ Ioi 1; cpow continuous away from 0
    have h_kernel : ContinuousOn (fun u : ℝ => ((HurwitzZeta.evenKernel 0 u : ℝ) : ℂ) - 1)
        (Set.Ioi (1 : ℝ)) := by
      have hev : ContinuousOn (fun u : ℝ => (HurwitzZeta.evenKernel 0 u : ℝ))
          (Set.Ioi (1 : ℝ)) :=
        (HurwitzZeta.continuousOn_evenKernel 0).mono
          (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
      have hev_C : ContinuousOn (fun u : ℝ => ((HurwitzZeta.evenKernel 0 u : ℝ) : ℂ))
          (Set.Ioi (1 : ℝ)) :=
        Complex.continuous_ofReal.comp_continuousOn hev
      exact hev_C.sub continuousOn_const
    have h_cpow1 : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (s/2 - 1)) (Set.Ioi (1 : ℝ)) := by
      intro u hu
      apply (Complex.continuousAt_ofReal_cpow_const u (s/2 - 1) (Or.inr ?_)).continuousWithinAt
      linarith [Set.mem_Ioi.mp hu]
    have h_cpow2 : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s/2 - (1/2 : ℂ))) (Set.Ioi (1 : ℝ)) := by
      intro u hu
      apply (Complex.continuousAt_ofReal_cpow_const u (-s/2 - 1/2) (Or.inr ?_)).continuousWithinAt
      linarith [Set.mem_Ioi.mp hu]
    unfold symmetricIntegrand
    exact continuousOn_const.mul (h_kernel.mul (h_cpow1.add h_cpow2))
  have hg1 : IntegrableOn g (f '' Set.Ici (0 : ℝ)) := by
    rw [h_image]
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    show IntegrableOn (fun u => (1/2 : ℂ) * symmetricIntegrand s u) (Set.Ioi 1)
    exact (integrable_symmetricIntegrand s).const_mul _
  have hg2 : IntegrableOn (fun x => f' x • (g ∘ f) x) (Set.Ici (0 : ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    -- The substituted integrand equals the I_theta integrand on Ioi 0 (by integrand_substitution)
    have h_eq : ∀ t ∈ Set.Ioi (0 : ℝ),
        ((2 : ℂ) * Complex.cosh ((s - 1/2) * (t : ℂ)) * ((ψ_mellin t : ℂ))) =
          f' t • (g ∘ f) t := by
      intro t _
      simp only [Function.comp_apply, f, f', g]
      rw [integrand_substitution s t]
      rw [Complex.real_smul]
    exact (integrable_I_theta_integrand s).congr_fun
      (fun t ht => h_eq t ht) measurableSet_Ioi
  have h_subst :=
    MeasureTheory.integral_comp_smul_deriv_Ioi hf_cont hft hff' hg_cont hg1 hg2
  rw [show (f 0 : ℝ) = 1 from by simp [f]] at h_subst
  show ∫ t in Set.Ioi 0, f' t • g (f t) = (1 / 2 : ℂ) * ∫ u in Set.Ioi 1, symmetricIntegrand s u
  -- h_subst has (g ∘ f) form, ours has g (f t) form — unfold Function.comp.
  simp only [Function.comp] at h_subst
  calc ∫ t in Set.Ioi 0, f' t • g (f t)
      = ∫ u in Set.Ioi 1, g u := h_subst
    _ = (1 / 2 : ℂ) * ∫ u in Set.Ioi 1, symmetricIntegrand s u := ?_
  -- Pull out the (1/2) constant
  show ∫ u in Set.Ioi 1, g u = (1 / 2 : ℂ) * ∫ u in Set.Ioi 1, symmetricIntegrand s u
  simp only [g]
  exact MeasureTheory.integral_const_mul _ _

/-- **The Mellin identity** — combines steps A and B with the definitional
unfolding of `completedRiemannZeta₀ = (hurwitzEvenFEPair 0).Λ₀(s/2)/2`. -/
theorem I_theta_of_ψ_mellin_eq_completedRiemannZeta₀ (s : ℂ) :
    I_theta_of ψ_mellin s = completedRiemannZeta₀ s := by
  rw [I_theta_of_ψ_mellin_eq_symmetric_form,
      ← mellinFmodif_eq_symmetric_form]
  -- completedRiemannZeta₀ s = completedHurwitzZetaEven₀ 0 s = Λ₀(s/2)/2 = mellin f_modif (s/2)/2
  show (1 / 2 : ℂ) * mellin ((hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif) (s / 2) =
       completedRiemannZeta₀ s
  unfold completedRiemannZeta₀ completedHurwitzZetaEven₀ WeakFEPair.Λ₀
  ring

/-- **The Riemann ξ identity** — `(s(s-1)/2) · I_theta_of ψ_mellin s + 1/2 = ξ(s)`.

Pure algebra from `I_theta_of_ψ_mellin_eq_completedRiemannZeta₀` and the
definition `riemannXi s := (s(s-1)/2) · cRZ₀(s) + 1/2`. -/
theorem riemannXi_eq_observable (s : ℂ) :
    ZD.riemannXi s = (s * (s - 1) / 2) * I_theta_of ψ_mellin s + 1/2 := by
  rw [I_theta_of_ψ_mellin_eq_completedRiemannZeta₀]
  unfold ZD.riemannXi
  ring

/-- **Pointwise vanishing at nontrivial zeros**: from `riemannXi(ρ) = 0`,
get `(ρ(ρ-1)/2) · I_theta_of ψ_mellin ρ + 1/2 = 0`. -/
theorem observable_vanishes_at_zeros (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    (ρ * (ρ - 1) / 2) * I_theta_of ψ_mellin ρ + 1/2 = 0 := by
  rw [← riemannXi_eq_observable]
  exact ZD.riemannXi_eq_zero_of_mem_NontrivialZeros ρ hρ

/-- **Equivalent form of vanishing**: `I_theta_of ψ_mellin ρ = -1/(ρ(ρ-1))`.
This holds because `ρ(ρ-1) ≠ 0` for any nontrivial zero (since `0 < ρ.re < 1`,
so `ρ ≠ 0` and `ρ ≠ 1`). -/
theorem observable_value_at_zero (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    I_theta_of ψ_mellin ρ = -1 / (ρ * (ρ - 1)) := by
  have h := observable_vanishes_at_zeros ρ hρ
  have hρ_re_pos : 0 < ρ.re := hρ.1
  have hρ_re_lt_one : ρ.re < 1 := hρ.2.1
  have hρ_ne_zero : ρ ≠ 0 := by
    intro h0; rw [h0, Complex.zero_re] at hρ_re_pos; linarith
  have hρ_ne_one : ρ ≠ 1 := by
    intro h1; rw [h1, Complex.one_re] at hρ_re_lt_one; linarith
  have hρ_sub_one_ne_zero : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ_ne_one
  have hprod_ne_zero : ρ * (ρ - 1) ≠ 0 := mul_ne_zero hρ_ne_zero hρ_sub_one_ne_zero
  have htwo_ne_zero : (2 : ℂ) ≠ 0 := two_ne_zero
  -- (ρ(ρ-1)/2) · I + 1/2 = 0 ⟹ I = -1 / (ρ(ρ-1))
  have h_eq' : (ρ * (ρ - 1)) * I_theta_of ψ_mellin ρ = -1 := by
    have h2 : 2 * ((ρ * (ρ - 1) / 2) * I_theta_of ψ_mellin ρ + 1/2) = 0 := by
      rw [h]; ring
    have h3 : (ρ * (ρ - 1)) * I_theta_of ψ_mellin ρ + 1 =
              2 * ((ρ * (ρ - 1) / 2) * I_theta_of ψ_mellin ρ + 1/2) := by ring
    have h4 : (ρ * (ρ - 1)) * I_theta_of ψ_mellin ρ + 1 = 0 := h3.trans h2
    linear_combination h4
  field_simp [hprod_ne_zero]
  linear_combination h_eq'

/-- **Norm at a nontrivial zero** — from `observable_value_at_zero`,
`‖I_theta_of ψ_mellin ρ‖ = 1 / ‖ρ·(ρ−1)‖`. This is the unconditional
amplitude-identity handle: every nontrivial zero pins the observable's
norm to the explicit geometric quantity `1/|ρ(ρ−1)|`, which behaves like
`1/|ρ.im|²` for large `|ρ.im|`. -/
theorem I_theta_mellin_norm_at_zero (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    ‖I_theta_of ψ_mellin ρ‖ = 1 / ‖ρ * (ρ - 1)‖ := by
  rw [observable_value_at_zero ρ hρ]
  rw [norm_div, norm_neg, norm_one]

/-- **Differentiability of the observable** — derived from `riemannXi`'s
differentiability via the identity. -/
theorem differentiable_observable :
    Differentiable ℂ
      (fun s => (s * (s - 1) / 2) * I_theta_of ψ_mellin s + 1/2) := by
  have h_eq : (fun s => (s * (s - 1) / 2) * I_theta_of ψ_mellin s + 1/2) =
              ZD.riemannXi := by
    funext s
    exact (riemannXi_eq_observable s).symm
  rw [h_eq]
  exact ZD.riemannXi_differentiable

/-! ### Axiom hygiene

Once `I_theta_of_ψ_mellin_eq_completedRiemannZeta₀` is discharged, every
theorem in this file depends only on `[propext, Classical.choice, Quot.sound]`
plus standard Mathlib axioms. -/

#print axioms riemannXi_eq_observable
#print axioms observable_vanishes_at_zeros
#print axioms I_theta_mellin_norm_at_zero
#print axioms differentiable_observable

end ZD

end
