import Mathlib

/-!
# Archimedean Transport Scaffold

Archimedean kernel scaffold with native-chart algebra and a separated
conjectural coefficient package. Three layers, cleanly separated:

1. **Exact Archimedean kernel** (`ASym`): no fitted constants.
2. **Native-chart algebra** (`cArch`, `deltaC`, `cShadow`): abstract
   real-valued families with the exact structural sum rule.
3. **Conjectural pinned coefficient package** (`ArchTransport.Conjectural`):
   the fitted model — `k_S, k_T, k_A, α, τ₀, c₀` — segregated from the
   exact theorems. The intercept relation `c₀ = τ₀ + α` and curvature
   relation `k_A = k_S + k_T` are proved as algebraic identities; no
   fitted constant is asserted as an unconditional analytic truth.

### Theorem-grade now
- exact definition of `ASym`
- reflection symmetry `ASym(-a,γ) = ASym(a,γ)` (proved)
- vanishing first derivative at `a = 0` (proved)
- second derivative formula in terms of `ψ'' = ψ_2` (stub, conditional on `γ ≠ 0`)
- native sum rule from `c₀ = τ₀ + α` and `k_A = k_S + k_T`

### Conjectural now (no truth claim)
- `α = ζ(-1)` as the effective Archimedean intercept
- `c₀ ≈ π + log 2`
- the amplitude bridge ansatz `shadowAnsatz`
- that the `t = π a` chart is native beyond the measured regime
-/

open Real Complex

noncomputable section

namespace ArchTransport

-- ═══════════════════════════════════════════════════════════════════════════
-- § Layer 1 — Exact Archimedean kernel
-- ═══════════════════════════════════════════════════════════════════════════

/-- `z_+(a,γ) = ¼ + a/2 + iγ/2`. -/
def zPlus  (a γ : ℝ) : ℂ := (1 / 4 + a / 2 : ℝ) + (γ / 2 : ℝ) * Complex.I

/-- `z_-(a,γ) = ¼ − a/2 + iγ/2`. -/
def zMinus (a γ : ℝ) : ℂ := (1 / 4 - a / 2 : ℝ) + (γ / 2 : ℝ) * Complex.I

/-- **Exact symmetric Archimedean kernel.**
  `A_sym(a,γ) = ½ Re( ψ(z_-(a,γ)) + ψ(z_+(a,γ)) ) − log π`
with `ψ = Complex.digamma`. No fitted constants. -/
def ASym (a γ : ℝ) : ℝ :=
  (1 / 2) * (Complex.digamma (zMinus a γ) + Complex.digamma (zPlus a γ)).re
  - Real.log Real.pi

/-- Argument swap under `a ↦ -a`. -/
@[simp] theorem zPlus_neg (a γ : ℝ) : zPlus (-a) γ = zMinus a γ := by
  unfold zPlus zMinus
  push_cast
  ring

/-- Argument swap under `a ↦ -a`. -/
@[simp] theorem zMinus_neg (a γ : ℝ) : zMinus (-a) γ = zPlus a γ := by
  unfold zPlus zMinus
  push_cast
  ring

/-- **Reflection symmetry** — `A_sym` is even in `a`. -/
theorem ASym_even (a γ : ℝ) : ASym (-a) γ = ASym a γ := by
  unfold ASym
  simp [zPlus_neg, zMinus_neg, add_comm]

/-- **Vanishing first derivative at `a = 0`.**

Purely from evenness. `ASym_even` gives `ASym(-·, γ) = ASym(·, γ)`; the
chain-rule identity `deriv (f ∘ Neg.neg) x = -deriv f (-x)` applied at
`x = 0` forces `deriv g 0 = -deriv g 0`, hence `= 0`. No
differentiability hypothesis is needed because `deriv` returns `0`
outside the differentiability locus in both branches. -/
theorem archSym_d_da_at_zero (γ : ℝ) :
    deriv (fun a => ASym a γ) 0 = 0 := by
  set g : ℝ → ℝ := fun a => ASym a γ with hg_def
  have heven : (fun a => g (-a)) = g := by
    funext a
    simp [hg_def, ASym_even]
  have hneg : deriv (fun a => g (-a)) 0 = -deriv g 0 := by
    have h := deriv_comp_neg g 0
    rw [neg_zero] at h
    exact h
  rw [heven] at hneg
  linarith

/-
**Second-derivative formula** — `∂_a² A_sym(a,γ) = ⅛ Re( ψ''(z_+) + ψ''(z_-) )`,
where `ψ = Complex.digamma` and `ψ'' = deriv (deriv ψ) = ψ_2`.

Conditional on `γ ≠ 0`, which forces `Im z_±(a,γ) = γ/2 ≠ 0`, placing both
digamma arguments off the pole locus `{-n : n ∈ ℕ} ⊂ ℝ`. At poles the
unconditional statement is false, so the hypothesis is not cosmetic.

**Proof sketch** (deferred):
  1. `Complex.digamma = logDeriv Complex.Gamma` (`Complex.digamma_def`);
     `Complex.meromorphic_digamma` gives analyticity off the pole set.
  2. Differentiability at `zPlus a γ`, `zMinus a γ` from `γ ≠ 0`
     (imaginary part `γ/2 ≠ 0`, arguments land off `ℝ`).
  3. Chain rule through the real-affine maps `a ↦ 1/4 ± a/2` composed
     with `ofReal` and `+ (γ/2) • I`, giving derivatives `±1/2`.
  4. `HasDerivAt` transport through `Complex.re` (continuous ℝ-linear).
  5. First derivative: `(1/4) Re(ψ'(z_+) - ψ'(z_-))`.
  6. Differentiate again; sign from `z_-` flips yielding
     `(1/8) Re(ψ''(z_+) + ψ''(z_-))`.
-/
theorem archSym_d2_da2_formula
    (a γ : ℝ) (hγ : γ ≠ 0) :
    deriv (deriv fun a => ASym a γ) a =
      (1 / 8) * ((deriv (deriv Complex.digamma)) (zPlus a γ) +
                 (deriv (deriv Complex.digamma)) (zMinus a γ)).re := by
  convert ( HasDerivAt.deriv ( _ ) ) using 1;
  convert HasDerivAt.congr_of_eventuallyEq _ ?_ using 1;
  exact fun a => 1 / 4 * ( Complex.re ( deriv digamma ( zPlus a γ ) - deriv digamma ( zMinus a γ ) ) );
  · -- Apply the chain rule to compute the derivative.
    have h_chain : HasDerivAt (fun a => deriv digamma (zPlus a γ)) (deriv (deriv digamma) (zPlus a γ) * (1 / 2)) a ∧ HasDerivAt (fun a => deriv digamma (zMinus a γ)) (deriv (deriv digamma) (zMinus a γ) * (-1 / 2)) a := by
      have h_chain : DifferentiableAt ℂ (deriv digamma) (zPlus a γ) ∧ DifferentiableAt ℂ (deriv digamma) (zMinus a γ) := by
        have h_analytic : ∀ z : ℂ, z.im ≠ 0 → AnalyticAt ℂ Complex.digamma z := by
          intro z hz
          have h_analytic : AnalyticAt ℂ Complex.Gamma z ∧ Complex.Gamma z ≠ 0 := by
            constructor;
            · refine' DifferentiableOn.analyticAt _ _;
              exact { w : ℂ | w.im ≠ 0 };
              · intro w hw; exact Complex.differentiableAt_Gamma _ ( by intro m; exact fun h => hw <| by simp_all +decide [ Complex.ext_iff ] ) |> DifferentiableAt.differentiableWithinAt;
              · exact IsOpen.mem_nhds ( isOpen_compl_singleton.preimage Complex.continuous_im ) hz;
            · rw [ Ne.eq_def, Complex.Gamma_eq_zero_iff ] ; aesop;
          have h_analytic : AnalyticAt ℂ (deriv Complex.Gamma) z := by
            exact h_analytic.1.deriv;
          exact h_analytic.div ( by tauto ) ( by tauto )
        generalize_proofs at *; (
        exact ⟨ ( h_analytic _ ( by unfold zPlus; norm_num; positivity ) ) |> AnalyticAt.deriv |> AnalyticAt.differentiableAt, ( h_analytic _ ( by unfold zMinus; norm_num; positivity ) ) |> AnalyticAt.deriv |> AnalyticAt.differentiableAt ⟩);
      -- Build zPlus/zMinus derivatives directly via HasDerivAt.comp.
      have h_zPlus : HasDerivAt (fun a : ℝ => zPlus a γ) (1/2 : ℂ) a := by
        unfold zPlus
        have h1 : HasDerivAt (fun a : ℝ => (1/4 + a/2 : ℝ)) (1/2 : ℝ) a :=
          ((hasDerivAt_id a).div_const 2).const_add _
        have h2 : HasDerivAt (fun a : ℝ => ((1/4 + a/2 : ℝ) : ℂ)) ((1/2 : ℝ) : ℂ) a :=
          h1.ofReal_comp
        have h3 := h2.add_const (((γ/2 : ℝ) : ℂ) * I)
        convert h3 using 1
        push_cast; ring
      have h_zMinus : HasDerivAt (fun a : ℝ => zMinus a γ) (-1/2 : ℂ) a := by
        unfold zMinus
        have h1 : HasDerivAt (fun a : ℝ => (1/4 - a/2 : ℝ)) (-1/2 : ℝ) a := by
          have := ((hasDerivAt_id a).div_const 2).const_sub (1/4 : ℝ)
          convert this using 1; ring
        have h2 : HasDerivAt (fun a : ℝ => ((1/4 - a/2 : ℝ) : ℂ)) ((-1/2 : ℝ) : ℂ) a :=
          h1.ofReal_comp
        have h3 := h2.add_const (((γ/2 : ℝ) : ℂ) * I)
        convert h3 using 1
        push_cast; ring
      refine ⟨?_, ?_⟩
      · have h_outer : HasDerivAt (deriv digamma)
            (deriv (deriv digamma) (zPlus a γ)) (zPlus a γ) :=
          h_chain.1.hasDerivAt
        exact h_outer.comp a h_zPlus
      · have h_outer : HasDerivAt (deriv digamma)
            (deriv (deriv digamma) (zMinus a γ)) (zMinus a γ) :=
          h_chain.2.hasDerivAt
        have := h_outer.comp a h_zMinus
        convert this using 1
    -- Build HasDerivAt directly from h_chain via subtraction, then .re, then const_mul.
    have h_sub : HasDerivAt (fun a => deriv digamma (zPlus a γ) - deriv digamma (zMinus a γ))
        (deriv (deriv digamma) (zPlus a γ) * (1/2) -
          deriv (deriv digamma) (zMinus a γ) * (-1/2)) a :=
      h_chain.1.sub h_chain.2
    have h_re : HasDerivAt
        (fun a => (deriv digamma (zPlus a γ) - deriv digamma (zMinus a γ)).re)
        (deriv (deriv digamma) (zPlus a γ) * (1/2) -
          deriv (deriv digamma) (zMinus a γ) * (-1/2)).re a := by
      have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt a h_sub
      simpa using this
    have h_final := h_re.const_mul (1/4 : ℝ)
    convert h_final using 1
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.neg_re, Complex.neg_im,
      Complex.div_re, Complex.div_im, Complex.normSq_ofNat, Complex.one_re,
      Complex.one_im]
    ring
  · filter_upwards [ ] with a;
    -- Applying the chain rule to find the derivative:
    have h_chain : HasDerivAt (fun a => Complex.digamma (zPlus a γ) + Complex.digamma (zMinus a γ)) ((deriv digamma (zPlus a γ)) * (1 / 2) + (deriv digamma (zMinus a γ)) * (-1 / 2)) a := by
      have h_chain : HasDerivAt (fun a => Complex.digamma (zPlus a γ)) (deriv digamma (zPlus a γ) * (1 / 2)) a ∧ HasDerivAt (fun a => Complex.digamma (zMinus a γ)) (deriv digamma (zMinus a γ) * (-1 / 2)) a := by
        constructor <;> apply_rules [ HasDerivAt.comp, hasDerivAt_id, hasDerivAt_const ];
        · convert hasDerivAt_deriv_iff.mpr _ using 1;
          refine' DifferentiableAt.div _ _ _ <;> norm_num [ Complex.Gamma_ne_zero ];
          · have h_diff : AnalyticAt ℂ Complex.Gamma (zPlus a γ) := by
              refine' DifferentiableOn.analyticAt _ _;
              exact { z : ℂ | z.im ≠ 0 };
              · intro z hz; exact Complex.differentiableAt_Gamma _ ( by intro m; exact fun h => hz <| by simp_all +decide [ Complex.ext_iff ] ) |> DifferentiableAt.differentiableWithinAt;
              · exact IsOpen.mem_nhds ( isOpen_compl_singleton.preimage Complex.continuous_im ) ( show ( zPlus a γ |> Complex.im ) ≠ 0 from by norm_num [ zPlus ] ; positivity );
            exact h_diff.deriv.differentiableAt;
          · refine' Complex.differentiableAt_Gamma _ _;
            intro m hm; norm_num [ Complex.ext_iff, zPlus ] at hm; cases lt_or_gt_of_ne hγ <;> nlinarith [ Real.pi_pos ] ;
          · refine' Complex.Gamma_ne_zero _;
            intro m; rw [ Ne.eq_def, Complex.ext_iff ] ; norm_num [ zPlus ] ; ring_nf; aesop;
        · -- HasDerivAt (fun a => zPlus a γ) (1/2) a
          have h1 : HasDerivAt (fun a : ℝ => (1/4 + a/2 : ℝ)) (1/2 : ℝ) a :=
            ((hasDerivAt_id a).div_const 2).const_add _
          have h2 : HasDerivAt (fun a : ℝ => ((1/4 + a/2 : ℝ) : ℂ)) ((1/2 : ℝ) : ℂ) a :=
            h1.ofReal_comp
          have h3 := h2.add_const (((γ/2 : ℝ) : ℂ) * I)
          convert h3 using 1
          push_cast; ring
        · convert hasDerivAt_deriv_iff.mpr _ using 1;
          refine' DifferentiableAt.div _ _ _ <;> norm_num [ Complex.Gamma_ne_zero ];
          · -- The Gamma function is analytic at $zMinus a γ$ since $γ ≠ 0$.
            have h_gamma_analytic : AnalyticAt ℂ Complex.Gamma (zMinus a γ) := by
              apply_rules [ DifferentiableOn.analyticAt, Complex.differentiableAt_Gamma ];
              refine' fun z hz => Complex.differentiableAt_Gamma _ _ |> DifferentiableAt.differentiableWithinAt;
              exact { z : ℂ | z.im ≠ 0 };
              · exact fun m => ne_of_apply_ne Complex.im <| by aesop;
              · exact IsOpen.mem_nhds ( isOpen_compl_singleton.preimage Complex.continuous_im ) ( show ( zMinus a γ |> Complex.im ) ≠ 0 from by norm_num [ zMinus ] ; positivity );
            exact h_gamma_analytic.deriv.differentiableAt;
          · refine' Complex.differentiableAt_Gamma _ _ ; norm_num [ zMinus ] ; ring ; norm_num [ hγ ];
            intro m; norm_num [ Complex.ext_iff ] ; contrapose! hγ; linarith;
          · rw [ Complex.Gamma_eq_zero_iff ] ; norm_num [ Complex.ext_iff, zMinus ] ; aesop;
        · -- HasDerivAt (fun a => zMinus a γ) (-1/2) a
          have h1 : HasDerivAt (fun a : ℝ => (1/4 - a/2 : ℝ)) (-1/2 : ℝ) a := by
            have := ((hasDerivAt_id a).div_const 2).const_sub (1/4 : ℝ)
            convert this using 1; ring
          have h2 : HasDerivAt (fun a : ℝ => ((1/4 - a/2 : ℝ) : ℂ)) ((-1/2 : ℝ) : ℂ) a :=
            h1.ofReal_comp
          have h3 := h2.add_const (((γ/2 : ℝ) : ℂ) * I)
          convert h3 using 1
          push_cast; ring
      exact h_chain.1.add h_chain.2;
    convert HasDerivAt.deriv ( HasDerivAt.sub ( HasDerivAt.const_mul ( 1 / 2 : ℝ ) ( Complex.reCLM.hasFDerivAt.comp_hasDerivAt a h_chain ) ) ( hasDerivAt_const _ _ ) ) using 1 ; norm_num ; ring;
    rotate_right;
    exact Real.log Real.pi;
    · congr ; ext ; unfold ASym ; norm_num ; ring;
    · norm_num [ Complex.ext_iff ] ; ring

-- ═══════════════════════════════════════════════════════════════════════════
-- § Layer 2 — Native-chart algebra
-- ═══════════════════════════════════════════════════════════════════════════

/-- Archimedean component along the native chart `t = π a`. Left abstract
at this layer; a pinned form lives in `Conjectural.cArchModel`. -/
def cArch   : ℝ → ℝ := fun _ => 0

/-- Offset component. Abstract; pinned form in `Conjectural.deltaCModel`. -/
def deltaC  : ℝ → ℝ := fun _ => 0

/-- Shadow component defined as the exact sum. -/
def cShadow (t : ℝ) : ℝ := cArch t + deltaC t

/-- **Exact native-chart split.** Theorem-grade by definition. -/
theorem cShadow_split (t : ℝ) : cShadow t = cArch t + deltaC t := rfl

end ArchTransport

-- ═══════════════════════════════════════════════════════════════════════════
-- § Layer 3 — Conjectural pinned coefficient package
--
-- Everything below is the *fitted* model. Nothing here is an unconditional
-- analytic theorem about ζ, ψ, or the Weil bridge — only algebraic
-- relationships between the pinned symbols themselves.
-- ═══════════════════════════════════════════════════════════════════════════

namespace ArchTransport.Conjectural

/-- Native-chart parameters: `c₀` is the shadow intercept, `τ₀` is the
offset intercept. The relation `c₀ = τ₀ + α` is the intercept sum rule. -/
structure NativeChartParams where
  c0   : ℝ
  tau0 : ℝ

/-- Shadow curvature coefficient: `k_S = 1 / (6π)`. -/
def kS : ℝ := 1 / (6 * Real.pi)

/-- Offset curvature coefficient: `k_T = (1 − π/6) / π²`. -/
def kT : ℝ := (1 - Real.pi / 6) / (Real.pi ^ 2)

/-- Archimedean curvature coefficient: `k_A = k_S + k_T`. -/
def kA : ℝ := kS + kT

/-- Effective Archimedean intercept. Conjecturally equal to `ζ(-1) = -1/12`. -/
def alpha : ℝ := -(1 / 12)

/-- Pinned Archimedean component: `c_arch(t) ≈ α + k_A t²`. -/
def cArchModel (t : ℝ) : ℝ := alpha + kA * t ^ 2

/-- Pinned offset component: `Δc(t) ≈ τ₀ − t − k_T t²`. -/
def deltaCModel (P : NativeChartParams) (t : ℝ) : ℝ :=
  P.tau0 - t - kT * t ^ 2

/-- Pinned shadow component: `c_shadow(t) ≈ c₀ − t + k_S t²`. -/
def cShadowModel (P : NativeChartParams) (t : ℝ) : ℝ :=
  P.c0 - t + kS * t ^ 2

/-- **Curvature sum rule**: `k_A = k_S + k_T`. Definitional. -/
theorem kA_split : kA = kS + kT := rfl

/-- **Exact algebraic sum rule for the pinned model.**

Given the intercept relation `c₀ = τ₀ + α`, the pinned shadow equals the
pinned Archimedean plus the pinned offset identically in `t`. Purely
algebraic — no empirical content is assumed. -/
theorem native_sum_rule
    (P : NativeChartParams)
    (h : P.c0 = P.tau0 + alpha) :
    ∀ t, cShadowModel P t = cArchModel t + deltaCModel P t := by
  intro t
  unfold cShadowModel cArchModel deltaCModel kA
  rw [h]
  ring

/-- **Conjectural amplitude bridge ansatz.**

`S(t,β,γ) ≈ λ(t) · exp(−A_sym(t/π, γ)/2) + μ(t) + η(t) · log(γ² + c_arch(t))`.

Defined as a symbolic form only. No truth claim. -/
def shadowAnsatz
    (lam mu eta : ℝ → ℝ) (t _β γ : ℝ) : ℝ :=
  lam t * Real.exp (-(ArchTransport.ASym (t / Real.pi) γ) / 2)
  + mu t
  + eta t * Real.log (γ ^ 2 + cArchModel t)

end ArchTransport.Conjectural