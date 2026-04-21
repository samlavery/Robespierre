import Mathlib

/-!
# Half-Line Parseval — discharging the project axioms from Mathlib Plancherel

Goal: prove the half-line cosine and sine Parseval identities as
theorems (currently axioms in `EnergyDefect.lean`).

Strategy: derive from Mathlib's `MeasureTheory.Lp.norm_fourier_eq`
(L² Plancherel for complex-valued functions on ℝ) via even (resp.
odd) extension of the half-line function to the full line.

Since this derivation is substantial (extension + Plancherel + change
of variables + symmetry), the file is built up incrementally.
-/

open Real MeasureTheory Set Complex

noncomputable section

namespace HalfLineParseval

/-- Even extension of a real half-line function to all of ℝ. -/
def evenExt (f : ℝ → ℝ) : ℝ → ℝ := fun t => f (|t|)

/-- Even extension as complex-valued, for use with Mathlib's L² Fourier. -/
def evenExtC (f : ℝ → ℝ) : ℝ → ℂ := fun t => ((f (|t|) : ℝ) : ℂ)

@[simp] theorem evenExt_neg (f : ℝ → ℝ) (t : ℝ) :
    evenExt f (-t) = evenExt f t := by
  unfold evenExt; rw [abs_neg]

@[simp] theorem evenExtC_neg (f : ℝ → ℝ) (t : ℝ) :
    evenExtC f (-t) = evenExtC f t := by
  unfold evenExtC; rw [abs_neg]

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step 1: L² norm of even extension equals twice the half-line L² norm
-- ═══════════════════════════════════════════════════════════════════════════

/-- **L² norm of the even extension.**
`∫_ℝ (f |t|)² dt = 2 ∫_{Ioi 0} f(t)² dt`. -/
theorem integral_sq_evenExt (f : ℝ → ℝ) :
    ∫ t : ℝ, (evenExt f t) ^ 2 = 2 * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
  unfold evenExt
  -- ∫ (f |t|)² dt = ∫ ((·)² ∘ f)(|t|) dt
  --            = 2 * ∫_{Ioi 0} f x ^ 2 dx  (by integral_comp_abs)
  have h := integral_comp_abs (f := fun x => f x ^ 2)
  simpa using h

/-- **L² norm of the complex-valued even extension.**
`∫_ℝ ‖evenExtC f t‖² dt = 2 ∫_{Ioi 0} f(t)² dt`. -/
theorem integral_normSq_evenExtC (f : ℝ → ℝ) :
    ∫ t : ℝ, ‖evenExtC f t‖ ^ 2 = 2 * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
  unfold evenExtC
  have h : ∀ t : ℝ, ‖((f (|t|) : ℝ) : ℂ)‖ ^ 2 = (f (|t|)) ^ 2 := by
    intro t
    rw [Complex.norm_real]
    exact sq_abs (f (|t|))
  simp_rw [h]
  exact integral_sq_evenExt f

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step 2: Measurability of the even extension
-- ═══════════════════════════════════════════════════════════════════════════

/-- The real even extension is measurable if `f` is. -/
theorem evenExt_measurable {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (evenExt f) :=
  hf.comp measurable_id.abs

/-- The complex even extension is measurable if `f` is. -/
theorem evenExtC_measurable {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (evenExtC f) :=
  Complex.measurable_ofReal.comp (evenExt_measurable hf)

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step 3: L² membership of the even extension
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Integrability of (evenExt f)².** Follows from integrability of f²
on Ioi 0 via change-of-variables on the Iic 0 half. -/
theorem integrable_sq_evenExt {f : ℝ → ℝ} (_hf_meas : Measurable f)
    (hf : Integrable (fun t => f t ^ 2) (volume.restrict (Ioi (0 : ℝ)))) :
    Integrable (fun t => (evenExt f t) ^ 2) volume := by
  have hf_Ioi : IntegrableOn (fun t => f t ^ 2) (Ioi (0 : ℝ)) volume := hf
  -- Extend to Ici 0 (boundary is null)
  have hf_Ici : IntegrableOn (fun t => f t ^ 2) (Ici (0 : ℝ)) volume := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]; exact hf_Ioi
  -- On Ioi 0, (evenExt f)² = f².
  have h_Ioi : IntegrableOn (fun t => (evenExt f t) ^ 2) (Ioi (0 : ℝ)) volume := by
    apply hf_Ioi.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    unfold evenExt; rw [abs_of_pos ht]
  -- On Iic 0: use `IntegrableOn.comp_neg_Iic` applied to f² on Ici 0.
  -- Gives IntegrableOn (fun t => (f(-t))²) (Iic 0).
  have h_neg : IntegrableOn (fun t => (f (-t)) ^ 2) (Iic (0 : ℝ)) volume := by
    have h := MeasureTheory.IntegrableOn.comp_neg_Iic (f := fun t => f t ^ 2)
      (c := (0 : ℝ)) (μ := volume) (by rw [neg_zero]; exact hf_Ici)
    exact h
  -- On Iic 0, (evenExt f t)² = (f(-t))².
  have h_Iic : IntegrableOn (fun t => (evenExt f t) ^ 2) (Iic (0 : ℝ)) volume := by
    apply h_neg.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Iic] with t ht
    unfold evenExt
    rw [abs_of_nonpos ht]
  -- Combine via union of Iic 0 and Ioi 0.
  have hUnion : IntegrableOn (fun t => (evenExt f t) ^ 2) (Iic 0 ∪ Ioi 0) volume :=
    h_Iic.union h_Ioi
  rw [Iic_union_Ioi] at hUnion
  rwa [integrableOn_univ] at hUnion

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step 4: MemLp 2 of the complex even extension
-- ═══════════════════════════════════════════════════════════════════════════

/-- **L² membership of (evenExtC f).** -/
theorem memLp_evenExtC {f : ℝ → ℝ} (hf_meas : Measurable f)
    (hf : Integrable (fun t => f t ^ 2) (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (evenExtC f) 2 volume := by
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm
      (evenExtC_measurable hf_meas).aestronglyMeasurable]
  -- Goal: Integrable (fun t => ‖evenExtC f t‖ ^ 2) volume
  have h_eq : ∀ t, ‖evenExtC f t‖ ^ 2 = (evenExt f t) ^ 2 := by
    intro t
    unfold evenExtC evenExt
    rw [Complex.norm_real]
    exact sq_abs _
  apply (integrable_sq_evenExt hf_meas hf).congr
  filter_upwards with t using (h_eq t).symm

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step 5: Plancherel for the complex even extension
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Plancherel on Lp**: `‖F(fLp)‖ = ‖fLp‖` in L² norm (Mathlib). -/
private theorem plancherel_norm_Lp {f : ℝ → ℝ} (hf_meas : Measurable f)
    (hf : Integrable (fun t => f t ^ 2) (volume.restrict (Ioi (0 : ℝ)))) :
    ‖FourierTransform.fourier
        ((memLp_evenExtC hf_meas hf).toLp : Lp ℂ 2 (volume : Measure ℝ))‖
      = ‖((memLp_evenExtC hf_meas hf).toLp : Lp ℂ 2 (volume : Measure ℝ))‖ :=
  MeasureTheory.Lp.norm_fourier_eq _

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step 6: Concrete integral form of ‖·‖² on Lp ℂ 2
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Squared Lp 2 norm as concrete integral.** For any element of `Lp ℂ 2 μ`,
`‖f‖² = ∫ ‖f t‖² dμ`. This is the bridge from the abstract `Lp` norm (which
appears in Mathlib's `Lp.norm_fourier_eq`) to a concrete Bochner integral.

Derivation: `‖f‖² = re ⟪f, f⟫` (InnerProductSpace defining equation);
`⟪f, f⟫ = ∫ ⟪f t, f t⟫ dμ` (`L2.inner_def`);
`⟪f t, f t⟫ = ((‖f t‖² : ℝ) : ℂ)` (`inner_self_eq_norm_sq_to_K`);
`re (∫ ((g t : ℝ) : ℂ) dμ) = ∫ g t dμ` (`integral_re`). -/
theorem Lp_two_sq_norm_eq_integral_sq_norm
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂μ := by
  have hInner : ‖f‖ ^ 2 =
      RCLike.re (inner ℂ (f : Lp ℂ 2 μ) f) :=
    InnerProductSpace.norm_sq_eq_re_inner f
  rw [hInner, L2.inner_def]
  rw [← integral_re (L2.integrable_inner f f)]
  apply integral_congr_ae
  filter_upwards with t
  rw [inner_self_eq_norm_sq_to_K]; norm_cast

/-- **Plancherel in concrete integral form (Lp 2 level).** For `f : ℝ → ℝ`
measurable and `f² ∈ L¹` on `(0,∞)`, the integral of the squared norm of
the Fourier transform of the complex even extension equals the integral
of the squared norm of the even extension itself. -/
theorem integral_normSq_fourier_Lp {f : ℝ → ℝ}
    (hf_meas : Measurable f)
    (hf : Integrable (fun t => f t ^ 2) (volume.restrict (Ioi (0 : ℝ)))) :
    ∫ ξ : ℝ, ‖(FourierTransform.fourier
        ((memLp_evenExtC hf_meas hf).toLp : Lp ℂ 2 (volume : Measure ℝ))) ξ‖ ^ 2
      = 2 * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
  -- LHS: ∫ ‖(𝓕 fLp) ξ‖² = ‖𝓕 fLp‖² (Step 6 helper)
  rw [← Lp_two_sq_norm_eq_integral_sq_norm volume
      (FourierTransform.fourier ((memLp_evenExtC hf_meas hf).toLp :
        Lp ℂ 2 (volume : Measure ℝ)))]
  -- Plancherel: ‖𝓕 fLp‖ = ‖fLp‖
  rw [MeasureTheory.Lp.norm_fourier_eq]
  -- Back to integral form for ‖fLp‖²
  rw [Lp_two_sq_norm_eq_integral_sq_norm volume
      ((memLp_evenExtC hf_meas hf).toLp : Lp ℂ 2 (volume : Measure ℝ))]
  -- toLp coincides a.e. with evenExtC f
  have h_ae :
      ((memLp_evenExtC hf_meas hf).toLp : ℝ → ℂ) =ᵐ[volume] evenExtC f :=
    (memLp_evenExtC hf_meas hf).coeFn_toLp
  rw [integral_congr_ae (h_ae.mono (fun t ht => by rw [ht]))]
  exact integral_normSq_evenExtC f

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step 7: Fourier of even extension = 2·cosine integral  (BRIDGE NEEDED)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Bridge (missing in Mathlib).** For an integrable complex-valued function
`g : ℝ → ℂ` that is also in `L²`, the Lp Fourier transform of its `toLp 2`
image coincides almost everywhere with the classical Bochner Fourier integral
`𝓕 g`.

Mathlib has `SchwartzMap.toLp_fourier_eq` (for Schwartz), and defines
`Lp.fourierTransformₗᵢ` by density extension from Schwartz, but does not
expose a direct `L¹ ∩ L²` bridge. This lemma is what the half-line Parseval
derivation requires, and is the cleanest natural addition.

Proof sketch (deferred): approximate `g` in both `L¹` and `L²` simultaneously
by Schwartz functions `gₙ`; use `SchwartzMap.toLp_fourier_eq` for each; pass
to the limit using continuity of the classical Fourier integral in `L¹` and
continuity of `Lp.fourierTransformₗᵢ` in `Lp 2`; `L²` limits extract an a.e.
convergent subsequence giving the pointwise a.e. identity. -/
theorem fourier_Lp_eq_fourierIntegral_ae
    {g : ℝ → ℂ} (hg_meas : AEStronglyMeasurable g (volume : Measure ℝ))
    (hg_int : Integrable g (volume : Measure ℝ))
    (hg_memLp : MemLp g 2 (volume : Measure ℝ)) :
    (FourierTransform.fourier (hg_memLp.toLp : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] FourierTransform.fourier g := by
  -- Outline: apply `ae_eq_of_integral_contDiff_smul_eq` to reduce to testing
  -- against smooth compactly-supported `h : ℝ → ℝ`, then use the TD-Fourier
  -- identity plus `VectorFourier.integral_bilin_fourierIntegral_eq_flip` for
  -- the Fubini swap.
  set gLp : Lp ℂ 2 (volume : Measure ℝ) := hg_memLp.toLp with hgLp_def
  set F : ℝ → ℂ := ((FourierTransform.fourier gLp : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
    with hF_def
  set F' : ℝ → ℂ := FourierTransform.fourier g with hF'_def
  -- F is locally integrable: Lp 2 ⇒ locally integrable.
  have hF_locInt : LocallyIntegrable F (volume : Measure ℝ) :=
    (Lp.memLp (FourierTransform.fourier gLp)).locallyIntegrable (by norm_num)
  -- F' = classical Fourier integral of integrable g is continuous bounded,
  -- hence locally integrable.
  have hF'_continuous : Continuous F' := by
    rw [hF'_def]
    exact VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop) hg_int
  have hF'_locInt : LocallyIntegrable F' (volume : Measure ℝ) :=
    hF'_continuous.locallyIntegrable
  -- Reduce to: ∫ h x • F x = ∫ h x • F' x for all smooth cpt-supported h.
  apply ae_eq_of_integral_contDiff_smul_eq hF_locInt hF'_locInt
  intro h h_smooth h_supp
  -- Cast h to ℂ-valued Schwartz
  have hh_smooth_ℂ := Complex.ofRealCLM.contDiff.comp h_smooth
  have hh_supp_ℂ : HasCompactSupport (fun x : ℝ => (h x : ℂ)) :=
    h_supp.comp_left (g := fun r : ℝ => (r : ℂ)) (by norm_cast)
  set hC : SchwartzMap ℝ ℂ := hh_supp_ℂ.toSchwartzMap hh_smooth_ℂ with hhC_def
  have hC_apply : ∀ x : ℝ, hC x = (h x : ℂ) := fun _ => rfl
  -- h x • F x = hC x • F x (real smul rewrites through ofReal)
  have h_smul_eq : ∀ x : ℝ, h x • F x = hC x • F x := fun x => by
    simp [hC_apply, Complex.real_smul, smul_eq_mul]
  have h'_smul_eq : ∀ x : ℝ, h x • F' x = hC x • F' x := fun x => by
    simp [hC_apply, Complex.real_smul, smul_eq_mul]
  calc ∫ x : ℝ, h x • F x
      = ∫ x : ℝ, hC x • F x := by
        apply integral_congr_ae
        filter_upwards with x using h_smul_eq x
    _ = Lp.toTemperedDistribution
          (FourierTransform.fourier gLp : Lp ℂ 2 (volume : Measure ℝ)) hC :=
        (Lp.toTemperedDistribution_apply _ _).symm
    _ = FourierTransform.fourier (Lp.toTemperedDistribution gLp) hC := by
        rw [← Lp.fourier_toTemperedDistribution_eq gLp]
    _ = Lp.toTemperedDistribution gLp (FourierTransform.fourier hC) :=
        TemperedDistribution.fourier_apply _ _
    _ = ∫ x : ℝ, (FourierTransform.fourier hC) x • (gLp : ℝ → ℂ) x :=
        Lp.toTemperedDistribution_apply _ _
    _ = ∫ x : ℝ, (FourierTransform.fourier hC) x • g x := by
        apply integral_congr_ae
        filter_upwards [hg_memLp.coeFn_toLp] with x hx
        rw [show (gLp : ℝ → ℂ) x = (hg_memLp.toLp : ℝ → ℂ) x from rfl, hx]
    _ = ∫ x : ℝ, hC x • F' x := by
        have key := VectorFourier.integral_fourierIntegral_smul_eq_flip
          (L := innerₗ ℝ) (ν := (volume : Measure ℝ)) (μ := (volume : Measure ℝ))
          Real.continuous_fourierChar continuous_inner hC.integrable hg_int
        rw [flip_innerₗ] at key
        exact key
    _ = ∫ x : ℝ, h x • F' x := by
        apply integral_congr_ae
        filter_upwards with x using (h'_smul_eq x).symm

/-- Integrability of `evenExtC f` on ℝ, given `f` integrable on `Ioi 0`. -/
theorem integrable_evenExtC {f : ℝ → ℝ} (hf_meas : Measurable f)
    (hf : Integrable f (volume.restrict (Ioi (0 : ℝ)))) :
    Integrable (evenExtC f) (volume : Measure ℝ) := by
  -- Reduce to integrability of `fun t => |f(|t|)|`, then to `∫_ℝ |f(|t|)| dt = 2 ∫_{t>0} |f t| dt`.
  have h_abs : Integrable (fun t : ℝ => f |t|) (volume : Measure ℝ) := by
    -- Copy structure of integrable_sq_evenExt (Step 3) with `f` in place of `f^2`.
    have hf_Ioi : IntegrableOn (fun t => f t) (Ioi (0 : ℝ)) volume := hf
    have hf_Ici : IntegrableOn (fun t => f t) (Ici (0 : ℝ)) volume := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]; exact hf_Ioi
    have h_Ioi : IntegrableOn (fun t => f |t|) (Ioi (0 : ℝ)) volume := by
      apply hf_Ioi.congr
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      rw [abs_of_pos ht]
    have h_neg : IntegrableOn (fun t => f (-t)) (Iic (0 : ℝ)) volume := by
      have h := MeasureTheory.IntegrableOn.comp_neg_Iic (f := fun t => f t)
        (c := (0 : ℝ)) (μ := volume) (by rw [neg_zero]; exact hf_Ici)
      exact h
    have h_Iic : IntegrableOn (fun t => f |t|) (Iic (0 : ℝ)) volume := by
      apply h_neg.congr
      filter_upwards [self_mem_ae_restrict measurableSet_Iic] with t ht
      rw [abs_of_nonpos ht]
    have hUnion : IntegrableOn (fun t => f |t|) (Iic 0 ∪ Ioi 0) volume :=
      h_Iic.union h_Ioi
    rw [Iic_union_Ioi] at hUnion
    rwa [integrableOn_univ] at hUnion
  -- Now evenExtC f t = ((f |t| : ℝ) : ℂ); `Complex.ofReal` is an L∞-bounded isometry on norms.
  have hmeas : AEStronglyMeasurable (evenExtC f) (volume : Measure ℝ) :=
    (evenExtC_measurable hf_meas).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  have h_eq : ∀ t, ‖evenExtC f t‖ = ‖f |t|‖ := by
    intro t; unfold evenExtC; rw [Complex.norm_real]
  exact h_abs.2.congr'
    (Filter.Eventually.of_forall (fun t => (h_eq t).symm))

-- The Fourier-transform-of-even-extension theorem appears after Step 8 below,
-- because its proof uses Step 8's even/odd integral helpers.

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step 8: Change of variables γ = 2πξ on the ξ-integral
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Change of variables γ = 2πξ.** For a real function `h`,
`∫_ℝ h(2πξ) dξ = (1/(2π)) · ∫_ℝ h(γ) dγ`. No integrability hypothesis
is needed: both sides are `0` if `h` isn't integrable (Bochner convention). -/
theorem integral_comp_two_pi_smul (h : ℝ → ℝ) :
    ∫ ξ : ℝ, h (2 * Real.pi * ξ) = (1 / (2 * Real.pi)) * ∫ γ : ℝ, h γ := by
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2πne : (2 * Real.pi) ≠ 0 := ne_of_gt h2π
  rw [MeasureTheory.Measure.integral_comp_mul_left h (2 * Real.pi), smul_eq_mul,
      abs_of_pos (inv_pos.mpr h2π), inv_eq_one_div]

/-- **Full-line integral of an odd function = 0.** Integrable or not, both
sides are `0` (Bochner convention for non-integrable ⇒ zero). -/
theorem integral_eq_zero_of_odd (h : ℝ → ℝ)
    (h_odd : ∀ γ, h (-γ) = -h γ) :
    ∫ γ : ℝ, h γ = 0 := by
  by_cases hint : Integrable h (volume : Measure ℝ)
  · have int_Iic : IntegrableOn h (Iic (0 : ℝ)) volume := hint.integrableOn
    have int_Ioi : IntegrableOn h (Ioi (0 : ℝ)) volume := hint.integrableOn
    have split : ∫ x : ℝ, h x =
        (∫ x in Iic (0 : ℝ), h x) + ∫ x in Ioi (0 : ℝ), h x := by
      rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi int_Iic int_Ioi,
          Iic_union_Ioi, Measure.restrict_univ]
    have h_eq : ∀ x, h x = -(h (-x)) := fun x => by rw [h_odd x]; ring
    have int_Iic_reflect :
        (∫ x in Iic (0 : ℝ), h x) = -∫ x in Ioi (0 : ℝ), h x := by
      calc (∫ x in Iic (0 : ℝ), h x)
          = ∫ x in Iic (0 : ℝ), -(h (-x)) := by
              refine setIntegral_congr_fun measurableSet_Iic (fun x _ => ?_)
              exact h_eq x
        _ = -(∫ x in Iic (0 : ℝ), h (-x)) := by rw [integral_neg]
        _ = -(∫ x in Ioi (0 : ℝ), h x) := by
              rw [← neg_zero, integral_comp_neg_Iic]; simp
    rw [split, int_Iic_reflect]; ring
  · exact integral_undef hint

/-- **AE version of odd-integral-zero.** If `h(-γ) = -h γ` holds a.e., then
`∫_ℝ h γ = 0`. Needed because definitions like `oddExt` fail pointwise
oddness at γ = 0 only. -/
theorem integral_eq_zero_of_odd_ae (h : ℝ → ℝ)
    (h_odd : ∀ᵐ γ ∂(volume : Measure ℝ), h (-γ) = -h γ) :
    ∫ γ : ℝ, h γ = 0 := by
  by_cases hint : Integrable h (volume : Measure ℝ)
  · -- Use the odd-symmetrisation `g γ := (h γ - h (-γ))/2`.
    set g : ℝ → ℝ := fun γ => (h γ - h (-γ)) / 2 with hg
    have hg_eq : h =ᵐ[volume] g := by
      filter_upwards [h_odd] with γ hγ
      show h γ = (h γ - h (-γ)) / 2
      rw [hγ]; ring
    have hg_odd : ∀ γ, g (-γ) = -g γ := by
      intro γ
      show (h (-γ) - h (-(-γ))) / 2 = -((h γ - h (-γ)) / 2)
      rw [neg_neg]; ring
    rw [integral_congr_ae hg_eq]
    exact integral_eq_zero_of_odd g hg_odd
  · exact integral_undef hint

/-- **Full-line integral of an even function = twice half-line integral.** -/
theorem integral_eq_two_integral_Ioi_of_even (h : ℝ → ℝ)
    (h_even : ∀ γ, h (-γ) = h γ) :
    ∫ γ : ℝ, h γ = 2 * ∫ γ in Ioi (0 : ℝ), h γ := by
  have h_abs : ∀ γ, h γ = h |γ| := fun γ => by
    rcases le_or_gt (0 : ℝ) γ with hγ | hγ
    · rw [abs_of_nonneg hγ]
    · rw [abs_of_neg hγ, h_even γ]
  have step1 : ∫ γ : ℝ, h γ = ∫ γ : ℝ, h |γ| := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro γ; exact h_abs γ
  rw [step1]
  exact integral_comp_abs

/-- **Cosine integrand is even in γ.** For `f` integrable on `Ioi 0`,
the γ-integrand `γ ↦ (∫_{Ioi 0} f(t) cos(γt) dt)²` is even in γ, hence
`∫_ℝ (...)² dγ = 2 ∫_{Ioi 0} (...)² dγ`. -/
theorem integral_cosine_sq_eq_two_Ioi (f : ℝ → ℝ) :
    ∫ γ : ℝ, (∫ t in Ioi (0 : ℝ), f t * Real.cos (γ * t)) ^ 2 =
      2 * ∫ γ in Ioi (0 : ℝ), (∫ t in Ioi (0 : ℝ), f t * Real.cos (γ * t)) ^ 2 := by
  apply integral_eq_two_integral_Ioi_of_even
  intro γ
  -- goal: (∫ t in Ioi 0, f t * cos(-γ*t))² = (∫ t in Ioi 0, f t * cos(γ*t))²
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [show -γ * t = -(γ * t) from by ring, Real.cos_neg]

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step 7b: Fourier transform of the even extension
-- (placed here so the Step-8 even/odd integral helpers are available)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Fourier transform of the even extension.** For f : ℝ → ℝ with f ∈ L¹
on Ioi 0, `𝓕 (evenExtC f)(ξ) = 2 ∫_{t > 0} cos(2πξt) f(t) dt` (real,
imaginary part is zero because the integrand of the full-line Fourier
integral is an even function in `t` for the real part and odd for the
imaginary part).

This is a plain integral-level computation. The hypotheses `hf_meas`,
`hf_int` guarantee convergence of all the Bochner integrals involved. -/
theorem fourier_evenExtC_eq_cosine {f : ℝ → ℝ}
    (hf_meas : Measurable f)
    (hf_int : Integrable f (volume.restrict (Ioi (0 : ℝ)))) (ξ : ℝ) :
    FourierTransform.fourier (evenExtC f) ξ =
      ((2 * ∫ t in Ioi (0 : ℝ), f t * Real.cos (2 * Real.pi * ξ * t) : ℝ) : ℂ) := by
  have h_int : Integrable (evenExtC f) (volume : Measure ℝ) :=
    integrable_evenExtC hf_meas hf_int
  rw [fourier_real_eq_integral_exp_smul]
  -- Rewrite the integrand as ((A v : ℝ) : ℂ) + I · ((B v : ℝ) : ℂ) with
  -- A v := cos(2πξv) · f|v|,  B v := -sin(2πξv) · f|v|.
  have h_integrand : ∀ v : ℝ,
      Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) • evenExtC f v =
      ((Real.cos (2 * Real.pi * ξ * v) * f |v| : ℝ) : ℂ) +
        Complex.I * ((-(Real.sin (2 * Real.pi * ξ * v) * f |v|) : ℝ) : ℂ) := by
    intro v
    unfold evenExtC
    show Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) * _ = _
    rw [Complex.exp_mul_I]
    have h_reorder : (↑(-2 * Real.pi * v * ξ) : ℂ) =
        -((2 * Real.pi * ξ * v : ℝ) : ℂ) := by push_cast; ring
    rw [h_reorder, Complex.cos_neg, Complex.sin_neg]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  have h_absf_int : Integrable (fun v : ℝ => f |v|) (volume : Measure ℝ) := by
    have h_norm_eq : ∀ v, ‖evenExtC f v‖ = ‖f |v|‖ := by
      intro v; unfold evenExtC; rw [Complex.norm_real]
    refine ⟨(hf_meas.comp measurable_id.abs).aestronglyMeasurable, ?_⟩
    refine h_int.2.congr' (Filter.Eventually.of_forall (fun v => ?_))
    exact h_norm_eq v
  have hA_int : Integrable
      (fun v : ℝ => Real.cos (2 * Real.pi * ξ * v) * f |v|) (volume : Measure ℝ) := by
    refine h_absf_int.bdd_mul (c := 1) ?_ ?_
    · exact (Real.continuous_cos.comp (by continuity)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  have hB_int : Integrable
      (fun v : ℝ => -(Real.sin (2 * Real.pi * ξ * v) * f |v|)) (volume : Measure ℝ) := by
    refine (h_absf_int.bdd_mul (c := 1) ?_ ?_).neg
    · exact (Real.continuous_sin.comp (by continuity)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _
  have hA_intC : Integrable (fun v : ℝ =>
      ((Real.cos (2 * Real.pi * ξ * v) * f |v| : ℝ) : ℂ)) (volume : Measure ℝ) :=
    hA_int.ofReal
  have hB_intC : Integrable (fun v : ℝ =>
      Complex.I * ((-(Real.sin (2 * Real.pi * ξ * v) * f |v|) : ℝ) : ℂ))
      (volume : Measure ℝ) :=
    hB_int.ofReal.const_mul Complex.I
  rw [integral_congr_ae (Filter.Eventually.of_forall h_integrand)]
  rw [integral_add hA_intC hB_intC,
      show (∫ (a : ℝ), I * ((-(Real.sin (2 * Real.pi * ξ * a) * f |a|) : ℝ) : ℂ))
        = I * ∫ (a : ℝ), ((-(Real.sin (2 * Real.pi * ξ * a) * f |a|) : ℝ) : ℂ)
        from MeasureTheory.integral_const_mul I _,
      integral_complex_ofReal, integral_complex_ofReal]
  have hA_even : ∀ γ, Real.cos (2 * Real.pi * ξ * -γ) * f |-γ| =
      Real.cos (2 * Real.pi * ξ * γ) * f |γ| := by
    intro γ
    rw [abs_neg, show (2 : ℝ) * Real.pi * ξ * (-γ) = -(2 * Real.pi * ξ * γ) from by ring,
        Real.cos_neg]
  have hA_val : ∫ v : ℝ, Real.cos (2 * Real.pi * ξ * v) * f |v| =
      2 * ∫ v in Ioi (0 : ℝ), f v * Real.cos (2 * Real.pi * ξ * v) := by
    rw [integral_eq_two_integral_Ioi_of_even _ hA_even]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
    rw [abs_of_pos hv]; ring
  have hB_odd : ∀ γ, -Real.sin (2 * Real.pi * ξ * -γ) * f |-γ| =
      -(-Real.sin (2 * Real.pi * ξ * γ) * f |γ|) := by
    intro γ
    rw [abs_neg, show (2 : ℝ) * Real.pi * ξ * (-γ) = -(2 * Real.pi * ξ * γ) from by ring,
        Real.sin_neg]; ring
  have hB_val : ∫ v : ℝ, -(Real.sin (2 * Real.pi * ξ * v) * f |v|) = 0 := by
    rw [show (fun v : ℝ => -(Real.sin (2 * Real.pi * ξ * v) * f |v|)) =
        (fun v => -Real.sin (2 * Real.pi * ξ * v) * f |v|) from by funext v; ring]
    exact integral_eq_zero_of_odd _ hB_odd
  rw [hA_val, hB_val]
  push_cast; ring

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step 9: Assembled halfLine cosine Parseval (target)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Half-line cosine Parseval — theorem form.** Matches the signature of
`ZD.halfLine_cosine_parseval` in `EnergyDefect.lean`, *modulo strengthening
the hypothesis from `f² ∈ L¹(Ioi 0)` alone to `f ∈ L¹ ∩ L²(Ioi 0)`*.

The stronger hypothesis lets us use the classical Bochner Fourier integral
for the even extension `evenExtC f`. The L¹ piece guarantees that
`fourierIntegral (evenExtC f)` is a well-defined pointwise continuous
function; the L² piece gives access to Plancherel via `Lp.norm_fourier_eq`.

Under the hypothesis `f ∈ L¹` (alongside `f² ∈ L¹`), this theorem could be
used to discharge the axiom `ZD.halfLine_cosine_parseval` **at the call
site by providing the extra L¹ witness**. The downstream test function `ψ`
is expected to decay super-exponentially, hence L¹ is automatic. -/
theorem halfLine_cosine_parseval_strong {f : ℝ → ℝ} (hf_meas : Measurable f)
    (hf_int : Integrable f (volume.restrict (Ioi (0 : ℝ))))
    (hf_sq  : Integrable (fun t => f t ^ 2) (volume.restrict (Ioi (0 : ℝ)))) :
    Integrable
        (fun γ => (∫ t in Ioi (0 : ℝ), f t * Real.cos (γ * t)) ^ 2)
        (volume.restrict (Ioi (0 : ℝ))) ∧
    ∫ γ in Ioi (0 : ℝ),
        (∫ t in Ioi (0 : ℝ), f t * Real.cos (γ * t)) ^ 2 =
      (Real.pi / 2) * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
  -- ———— Setup ————
  have hg_int : Integrable (evenExtC f) (volume : Measure ℝ) :=
    integrable_evenExtC hf_meas hf_int
  have hg_memLp : MemLp (evenExtC f) 2 (volume : Measure ℝ) :=
    memLp_evenExtC hf_meas hf_sq
  -- ———— Step A: Plancherel gives ∫ ‖𝓕 fLp‖² = 2 ∫_{Ioi 0} f² ————
  have hPl : ∫ ξ : ℝ, ‖(FourierTransform.fourier
        ((memLp_evenExtC hf_meas hf_sq).toLp :
          Lp ℂ 2 (volume : Measure ℝ))) ξ‖ ^ 2
      = 2 * ∫ t in Ioi (0 : ℝ), f t ^ 2 :=
    integral_normSq_fourier_Lp hf_meas hf_sq
  -- ———— Step B: bridge Lp Fourier → classical Fourier, then → cosine integral ————
  have hBridge :
      ((FourierTransform.fourier ((memLp_evenExtC hf_meas hf_sq).toLp :
          Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) =ᵐ[volume]
        FourierTransform.fourier (evenExtC f) :=
    fourier_Lp_eq_fourierIntegral_ae hg_memLp.1 hg_int hg_memLp
  have hFour : ∀ ξ, FourierTransform.fourier (evenExtC f) ξ =
      ((2 * ∫ t in Ioi (0 : ℝ), f t * Real.cos (2 * Real.pi * ξ * t) : ℝ) : ℂ) :=
    fun ξ => fourier_evenExtC_eq_cosine hf_meas hf_int ξ
  -- ———— Step C: ‖𝓕 fLp ξ‖² = 4 · (∫_{Ioi 0} f cos(2πξt))² a.e. ————
  have hAE :
      (fun ξ => ‖(FourierTransform.fourier
          ((memLp_evenExtC hf_meas hf_sq).toLp :
            Lp ℂ 2 (volume : Measure ℝ))) ξ‖ ^ 2) =ᵐ[volume]
      (fun ξ =>
        4 * (∫ t in Ioi (0 : ℝ), f t * Real.cos (2 * Real.pi * ξ * t)) ^ 2) := by
    filter_upwards [hBridge] with ξ hξ
    rw [hξ, hFour, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  -- ———— Step D: integrate both sides of hAE, substitute into hPl ————
  have hPl2 : ∫ ξ : ℝ,
      4 * (∫ t in Ioi (0 : ℝ), f t * Real.cos (2 * Real.pi * ξ * t)) ^ 2 =
      2 * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
    rw [← hPl]; exact (integral_congr_ae hAE).symm
  -- ———— Step E: pull constant, then divide by 4 ————
  have hPl3 : ∫ ξ : ℝ,
      (∫ t in Ioi (0 : ℝ), f t * Real.cos (2 * Real.pi * ξ * t)) ^ 2 =
      (1/2) * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
    have : (4 : ℝ) * ∫ ξ : ℝ,
        (∫ t in Ioi (0 : ℝ), f t * Real.cos (2 * Real.pi * ξ * t)) ^ 2 =
        2 * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
      rw [← integral_const_mul]; exact hPl2
    linarith
  -- ———— Step F: change of variables γ = 2π ξ (Step 8 lemma) ————
  -- After β-reduction, `h(2π·ξ) = (∫ t, f t · cos((2π·ξ)·t))²`, which matches our
  -- LHS's `cos(2·π·ξ·t)` up to default left-associativity of `*`.
  have hCoV : ∫ ξ : ℝ,
      (∫ t in Ioi (0 : ℝ), f t * Real.cos (2 * Real.pi * ξ * t)) ^ 2 =
      (1 / (2 * Real.pi)) *
        ∫ γ : ℝ, (∫ t in Ioi (0 : ℝ), f t * Real.cos (γ * t)) ^ 2 :=
    integral_comp_two_pi_smul
      (fun γ => (∫ t in Ioi (0 : ℝ), f t * Real.cos (γ * t)) ^ 2)
  -- ———— Step G: evenness in γ → half-line ————
  have hEv : ∫ γ : ℝ, (∫ t in Ioi (0 : ℝ), f t * Real.cos (γ * t)) ^ 2 =
      2 * ∫ γ in Ioi (0 : ℝ),
        (∫ t in Ioi (0 : ℝ), f t * Real.cos (γ * t)) ^ 2 :=
    integral_cosine_sq_eq_two_Ioi f
  -- ———— Step H: combine into final equation ————
  have hFinal : ∫ γ in Ioi (0 : ℝ),
      (∫ t in Ioi (0 : ℝ), f t * Real.cos (γ * t)) ^ 2 =
      (Real.pi / 2) * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    have hπne : (2 * Real.pi) ≠ 0 := ne_of_gt hπ
    -- From hPl3: ∫ ξ, (...)² = (1/2) · ∫ f²
    -- From hCoV: ∫ ξ, (...)² = (1/(2π)) · ∫ γ, (...)²
    -- Combining: (1/(2π)) · ∫ γ, (...)² = (1/2) · ∫ f²
    --         ⇒ ∫ γ, (...)² = π · ∫ f²
    have step1 : ∫ γ : ℝ, (∫ t in Ioi (0 : ℝ), f t * Real.cos (γ * t)) ^ 2 =
        Real.pi * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
      have eq := hCoV.symm.trans hPl3
      -- eq : (1/(2π)) · ∫ γ,(...)² = (1/2) · ∫ f²
      field_simp at eq
      linarith
    rw [hEv] at step1
    linarith
  -- ———— Integrability part ————
  refine ⟨?_, hFinal⟩
  -- (a) 𝓕 fLp ∈ Lp 2 ⇒ ‖𝓕 fLp‖² ∈ L¹ on ℝ.
  have hFourierLp_sq_int :
      Integrable (fun ξ => ‖(FourierTransform.fourier
          ((memLp_evenExtC hf_meas hf_sq).toLp :
            Lp ℂ 2 (volume : Measure ℝ))) ξ‖ ^ 2) (volume : Measure ℝ) := by
    have hmem := Lp.memLp (FourierTransform.fourier
      ((memLp_evenExtC hf_meas hf_sq).toLp :
        Lp ℂ 2 (volume : Measure ℝ)))
    exact (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem
  -- (b) Transfer via hAE to the cosine expression.
  have hCosSq4_int : Integrable
      (fun ξ => 4 * (∫ t in Ioi (0 : ℝ), f t * Real.cos (2 * Real.pi * ξ * t)) ^ 2)
      (volume : Measure ℝ) :=
    hFourierLp_sq_int.congr hAE
  -- (c) Factor out the constant 4.
  have hCosSq_int : Integrable
      (fun ξ => (∫ t in Ioi (0 : ℝ), f t * Real.cos (2 * Real.pi * ξ * t)) ^ 2)
      (volume : Measure ℝ) := by
    have := hCosSq4_int.const_mul (1/4)
    refine this.congr ?_
    filter_upwards with ξ
    ring
  -- (d) Change of variables γ = 2π·ξ preserves integrability.
  have h2πne : (2 * Real.pi) ≠ 0 := by positivity
  have hGammaSq_int : Integrable
      (fun γ => (∫ t in Ioi (0 : ℝ), f t * Real.cos (γ * t)) ^ 2)
      (volume : Measure ℝ) :=
    (integrable_comp_mul_left_iff
      (g := fun γ => (∫ t in Ioi (0 : ℝ), f t * Real.cos (γ * t)) ^ 2)
      h2πne).mp hCosSq_int
  -- (e) Restrict to Ioi 0.
  exact hGammaSq_int.restrict

-- ═══════════════════════════════════════════════════════════════════════════
-- § Step 10: Odd extension and sine Parseval (symmetric to Steps 1–9)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Odd extension of a real half-line function to all of ℝ. -/
def oddExt (f : ℝ → ℝ) : ℝ → ℝ := fun t => if 0 < t then f t else -(f (-t))

/-- Odd extension as complex-valued. -/
def oddExtC (f : ℝ → ℝ) : ℝ → ℂ := fun t => ((oddExt f t : ℝ) : ℂ)

/-- **(oddExt f)² = (evenExt f)²** pointwise: they differ only by sign. -/
theorem oddExt_sq_eq_evenExt_sq (f : ℝ → ℝ) (t : ℝ) :
    (oddExt f t) ^ 2 = (evenExt f t) ^ 2 := by
  unfold oddExt evenExt
  by_cases ht : 0 < t
  · simp [ht, abs_of_pos ht]
  · push_neg at ht
    simp [not_lt.mpr ht, abs_of_nonpos ht]

theorem oddExt_measurable {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (oddExt f) := by
  unfold oddExt
  refine Measurable.ite measurableSet_Ioi hf ?_
  exact (hf.comp measurable_id.neg).neg

theorem oddExtC_measurable {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (oddExtC f) :=
  Complex.measurable_ofReal.comp (oddExt_measurable hf)

theorem integral_sq_oddExt (f : ℝ → ℝ) :
    ∫ t : ℝ, (oddExt f t) ^ 2 = 2 * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
  rw [show (fun t => (oddExt f t) ^ 2) = (fun t => (evenExt f t) ^ 2) from
    funext (fun t => oddExt_sq_eq_evenExt_sq f t)]
  exact integral_sq_evenExt f

theorem integral_normSq_oddExtC (f : ℝ → ℝ) :
    ∫ t : ℝ, ‖oddExtC f t‖ ^ 2 = 2 * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
  unfold oddExtC
  have h : ∀ t : ℝ, ‖((oddExt f t : ℝ) : ℂ)‖ ^ 2 = (oddExt f t) ^ 2 := by
    intro t; rw [Complex.norm_real]; exact sq_abs _
  simp_rw [h]
  exact integral_sq_oddExt f

theorem integrable_sq_oddExt {f : ℝ → ℝ} (hf_meas : Measurable f)
    (hf : Integrable (fun t => f t ^ 2) (volume.restrict (Ioi (0 : ℝ)))) :
    Integrable (fun t => (oddExt f t) ^ 2) volume := by
  refine (integrable_sq_evenExt hf_meas hf).congr ?_
  filter_upwards with t using (oddExt_sq_eq_evenExt_sq f t).symm

theorem memLp_oddExtC {f : ℝ → ℝ} (hf_meas : Measurable f)
    (hf : Integrable (fun t => f t ^ 2) (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (oddExtC f) 2 volume := by
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm
      (oddExtC_measurable hf_meas).aestronglyMeasurable]
  have h_eq : ∀ t, ‖oddExtC f t‖ ^ 2 = (oddExt f t) ^ 2 := by
    intro t; unfold oddExtC
    rw [Complex.norm_real]; exact sq_abs _
  apply (integrable_sq_oddExt hf_meas hf).congr
  filter_upwards with t using (h_eq t).symm

theorem integrable_oddExtC {f : ℝ → ℝ} (hf_meas : Measurable f)
    (hf : Integrable f (volume.restrict (Ioi (0 : ℝ)))) :
    Integrable (oddExtC f) (volume : Measure ℝ) := by
  -- Paralleled to integrable_evenExtC; uses the fact that |oddExt f t| = |f|t||
  -- almost everywhere (equality holds pointwise away from t = 0, which is null).
  have h_evenC : Integrable (evenExtC f) (volume : Measure ℝ) :=
    integrable_evenExtC hf_meas hf
  have hmeas : AEStronglyMeasurable (oddExtC f) (volume : Measure ℝ) :=
    (oddExtC_measurable hf_meas).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  have h_norm_eq : ∀ t, ‖oddExtC f t‖ = ‖evenExtC f t‖ := by
    intro t; unfold oddExtC evenExtC
    rw [Complex.norm_real, Complex.norm_real]
    unfold oddExt
    by_cases ht : 0 < t
    · simp [ht, abs_of_pos ht]
    · push_neg at ht
      simp [not_lt.mpr ht, abs_of_nonpos ht, abs_neg]
  exact h_evenC.2.congr' (Filter.Eventually.of_forall (fun v => (h_norm_eq v).symm))

/-- **Fourier of the odd extension.** For `f : ℝ → ℝ` with `f ∈ L¹` on `Ioi 0`,
`𝓕 (oddExtC f)(ξ) = -2i · ∫_{t>0} sin(2πξt) f(t) dt`. Real part vanishes by
oddness; imag part is nonzero via the sin integrand. -/
theorem fourier_oddExtC_eq_sine {f : ℝ → ℝ}
    (hf_meas : Measurable f)
    (hf_int : Integrable f (volume.restrict (Ioi (0 : ℝ)))) (ξ : ℝ) :
    FourierTransform.fourier (oddExtC f) ξ =
      ((-(2 * ∫ t in Ioi (0 : ℝ), f t * Real.sin (2 * Real.pi * ξ * t)) : ℝ) : ℂ) *
        Complex.I := by
  have h_int : Integrable (oddExtC f) (volume : Measure ℝ) :=
    integrable_oddExtC hf_meas hf_int
  rw [fourier_real_eq_integral_exp_smul]
  -- Rewrite integrand analogously to cos case.
  have h_integrand : ∀ v : ℝ,
      Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) • oddExtC f v =
      ((Real.cos (2 * Real.pi * ξ * v) * oddExt f v : ℝ) : ℂ) +
        Complex.I * ((-(Real.sin (2 * Real.pi * ξ * v) * oddExt f v) : ℝ) : ℂ) := by
    intro v
    unfold oddExtC
    show Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) * _ = _
    rw [Complex.exp_mul_I]
    have h_reorder : (↑(-2 * Real.pi * v * ξ) : ℂ) =
        -((2 * Real.pi * ξ * v : ℝ) : ℂ) := by push_cast; ring
    rw [h_reorder, Complex.cos_neg, Complex.sin_neg]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  have h_oddf_int : Integrable (oddExt f) (volume : Measure ℝ) := by
    have h_norm_eq : ∀ v, ‖oddExtC f v‖ = ‖oddExt f v‖ := by
      intro v; unfold oddExtC; rw [Complex.norm_real]
    refine ⟨(oddExt_measurable hf_meas).aestronglyMeasurable, ?_⟩
    refine h_int.2.congr' (Filter.Eventually.of_forall (fun v => ?_))
    exact h_norm_eq v
  have hA_int : Integrable
      (fun v : ℝ => Real.cos (2 * Real.pi * ξ * v) * oddExt f v)
      (volume : Measure ℝ) := by
    refine h_oddf_int.bdd_mul (c := 1) ?_ ?_
    · exact (Real.continuous_cos.comp (by continuity)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  have hB_int : Integrable
      (fun v : ℝ => -(Real.sin (2 * Real.pi * ξ * v) * oddExt f v))
      (volume : Measure ℝ) := by
    refine (h_oddf_int.bdd_mul (c := 1) ?_ ?_).neg
    · exact (Real.continuous_sin.comp (by continuity)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _
  have hA_intC : Integrable (fun v : ℝ =>
      ((Real.cos (2 * Real.pi * ξ * v) * oddExt f v : ℝ) : ℂ))
      (volume : Measure ℝ) :=
    hA_int.ofReal
  have hB_intC : Integrable (fun v : ℝ =>
      Complex.I * ((-(Real.sin (2 * Real.pi * ξ * v) * oddExt f v) : ℝ) : ℂ))
      (volume : Measure ℝ) :=
    hB_int.ofReal.const_mul Complex.I
  rw [integral_congr_ae (Filter.Eventually.of_forall h_integrand)]
  rw [integral_add hA_intC hB_intC,
      show (∫ (a : ℝ), I * ((-(Real.sin (2 * Real.pi * ξ * a) * oddExt f a) : ℝ) : ℂ))
        = I * ∫ (a : ℝ), ((-(Real.sin (2 * Real.pi * ξ * a) * oddExt f a) : ℝ) : ℂ)
        from MeasureTheory.integral_const_mul I _,
      integral_complex_ofReal, integral_complex_ofReal]
  -- Real part integrates to 0 (ae-odd: oddExt f(-γ) = -oddExt f γ for γ ≠ 0).
  have hA_val : ∫ v : ℝ, Real.cos (2 * Real.pi * ξ * v) * oddExt f v = 0 := by
    apply integral_eq_zero_of_odd_ae
    -- ae-odd: show on {γ ≠ 0} (complement is {0}, null)
    have h_ae : ∀ᵐ γ ∂(volume : Measure ℝ), γ ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [h_ae] with γ hγ
    -- γ ≠ 0 ⇒ oddExt f (-γ) = -oddExt f γ
    have h_oddExt : oddExt f (-γ) = -oddExt f γ := by
      unfold oddExt
      rcases lt_trichotomy γ 0 with hγ' | hγ' | hγ'
      · simp [not_lt.mpr hγ'.le, show (0 : ℝ) < -γ from by linarith]
      · exact absurd hγ' hγ
      · simp [hγ', not_lt.mpr (show -γ ≤ 0 from by linarith)]
    rw [show (2 : ℝ) * Real.pi * ξ * (-γ) = -(2 * Real.pi * ξ * γ) from by ring,
        Real.cos_neg, h_oddExt]
    ring
  -- Imag part integrates to -2·∫_{Ioi 0} f·sin.
  have h_even_sinodd : ∀ γ, -Real.sin (2 * Real.pi * ξ * -γ) * oddExt f (-γ) =
      -Real.sin (2 * Real.pi * ξ * γ) * oddExt f γ := by
    intro γ
    rcases eq_or_ne γ 0 with rfl | hγ
    · simp
    · rw [show (2 : ℝ) * Real.pi * ξ * (-γ) = -(2 * Real.pi * ξ * γ) from by ring,
          Real.sin_neg]
      have h_oddExt : oddExt f (-γ) = -oddExt f γ := by
        unfold oddExt
        rcases lt_trichotomy γ 0 with hγ' | hγ' | hγ'
        · simp [not_lt.mpr hγ'.le, show (0 : ℝ) < -γ from by linarith]
        · exact absurd hγ' hγ
        · simp [hγ', not_lt.mpr (show -γ ≤ 0 from by linarith)]
      rw [h_oddExt]; ring
  have hB_val : ∫ v : ℝ, -(Real.sin (2 * Real.pi * ξ * v) * oddExt f v) =
      -(2 * ∫ v in Ioi (0 : ℝ), f v * Real.sin (2 * Real.pi * ξ * v)) := by
    rw [show (fun v : ℝ => -(Real.sin (2 * Real.pi * ξ * v) * oddExt f v)) =
        (fun v => -Real.sin (2 * Real.pi * ξ * v) * oddExt f v) from by funext v; ring]
    rw [integral_eq_two_integral_Ioi_of_even _ h_even_sinodd]
    have h_on_Ioi :
        (fun γ : ℝ => -Real.sin (2 * Real.pi * ξ * γ) * oddExt f γ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun γ => -(f γ * Real.sin (2 * Real.pi * ξ * γ))) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with γ hγ
      have hγ' : (0 : ℝ) < γ := hγ
      have h_odd_pos : oddExt f γ = f γ := by
        unfold oddExt; exact if_pos hγ'
      rw [h_odd_pos]; ring
    rw [integral_congr_ae h_on_Ioi, integral_neg]
    ring
  rw [hA_val, hB_val]
  push_cast; ring

theorem integral_normSq_fourier_Lp_odd {f : ℝ → ℝ}
    (hf_meas : Measurable f)
    (hf : Integrable (fun t => f t ^ 2) (volume.restrict (Ioi (0 : ℝ)))) :
    ∫ ξ : ℝ, ‖(FourierTransform.fourier
        ((memLp_oddExtC hf_meas hf).toLp : Lp ℂ 2 (volume : Measure ℝ))) ξ‖ ^ 2
      = 2 * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
  rw [← Lp_two_sq_norm_eq_integral_sq_norm volume
      (FourierTransform.fourier ((memLp_oddExtC hf_meas hf).toLp :
        Lp ℂ 2 (volume : Measure ℝ)))]
  rw [MeasureTheory.Lp.norm_fourier_eq]
  rw [Lp_two_sq_norm_eq_integral_sq_norm volume
      ((memLp_oddExtC hf_meas hf).toLp : Lp ℂ 2 (volume : Measure ℝ))]
  have h_ae :
      ((memLp_oddExtC hf_meas hf).toLp : ℝ → ℂ) =ᵐ[volume] oddExtC f :=
    (memLp_oddExtC hf_meas hf).coeFn_toLp
  rw [integral_congr_ae (h_ae.mono (fun t ht => by rw [ht]))]
  exact integral_normSq_oddExtC f

/-- **Sine integrand is even in γ.** `sin(-γt) = -sin(γt)`, but squaring
preserves evenness. -/
theorem integral_sine_sq_eq_two_Ioi (f : ℝ → ℝ) :
    ∫ γ : ℝ, (∫ t in Ioi (0 : ℝ), f t * Real.sin (γ * t)) ^ 2 =
      2 * ∫ γ in Ioi (0 : ℝ), (∫ t in Ioi (0 : ℝ), f t * Real.sin (γ * t)) ^ 2 := by
  apply integral_eq_two_integral_Ioi_of_even
  intro γ
  have h_sin : (fun t : ℝ => f t * Real.sin (-γ * t)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => -(f t * Real.sin (γ * t))) := by
    filter_upwards with t
    rw [show -γ * t = -(γ * t) from by ring, Real.sin_neg]
    ring
  rw [integral_congr_ae h_sin, integral_neg, neg_sq]

/-- **Half-line sine Parseval — theorem form.** Parallels Step 9 with `sin`
replacing `cos` and `oddExtC` replacing `evenExtC`. The `π/2` constant is
identical. -/
theorem halfLine_sine_parseval_strong {f : ℝ → ℝ} (hf_meas : Measurable f)
    (hf_int : Integrable f (volume.restrict (Ioi (0 : ℝ))))
    (hf_sq  : Integrable (fun t => f t ^ 2) (volume.restrict (Ioi (0 : ℝ)))) :
    Integrable
        (fun γ => (∫ t in Ioi (0 : ℝ), f t * Real.sin (γ * t)) ^ 2)
        (volume.restrict (Ioi (0 : ℝ))) ∧
    ∫ γ in Ioi (0 : ℝ),
        (∫ t in Ioi (0 : ℝ), f t * Real.sin (γ * t)) ^ 2 =
      (Real.pi / 2) * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
  -- ———— Setup ————
  have hg_int : Integrable (oddExtC f) (volume : Measure ℝ) :=
    integrable_oddExtC hf_meas hf_int
  have hg_memLp : MemLp (oddExtC f) 2 (volume : Measure ℝ) :=
    memLp_oddExtC hf_meas hf_sq
  -- ———— Step A: Plancherel ————
  have hPl : ∫ ξ : ℝ, ‖(FourierTransform.fourier
        ((memLp_oddExtC hf_meas hf_sq).toLp :
          Lp ℂ 2 (volume : Measure ℝ))) ξ‖ ^ 2
      = 2 * ∫ t in Ioi (0 : ℝ), f t ^ 2 :=
    integral_normSq_fourier_Lp_odd hf_meas hf_sq
  -- ———— Step B: bridge → classical Fourier → -2i·∫sin ————
  have hBridge :
      ((FourierTransform.fourier ((memLp_oddExtC hf_meas hf_sq).toLp :
          Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) =ᵐ[volume]
        FourierTransform.fourier (oddExtC f) :=
    fourier_Lp_eq_fourierIntegral_ae hg_memLp.1 hg_int hg_memLp
  have hFour : ∀ ξ, FourierTransform.fourier (oddExtC f) ξ =
      ((-(2 * ∫ t in Ioi (0 : ℝ), f t * Real.sin (2 * Real.pi * ξ * t)) : ℝ) : ℂ) *
        Complex.I :=
    fun ξ => fourier_oddExtC_eq_sine hf_meas hf_int ξ
  -- ———— Step C: ‖𝓕 fLp ξ‖² = 4·(∫sin)² a.e. ————
  have hAE :
      (fun ξ => ‖(FourierTransform.fourier
          ((memLp_oddExtC hf_meas hf_sq).toLp :
            Lp ℂ 2 (volume : Measure ℝ))) ξ‖ ^ 2) =ᵐ[volume]
      (fun ξ =>
        4 * (∫ t in Ioi (0 : ℝ), f t * Real.sin (2 * Real.pi * ξ * t)) ^ 2) := by
    filter_upwards [hBridge] with ξ hξ
    rw [hξ, hFour, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
    ring
  -- ———— Step D: integrate the AE equality ————
  have hPl2 : ∫ ξ : ℝ,
      4 * (∫ t in Ioi (0 : ℝ), f t * Real.sin (2 * Real.pi * ξ * t)) ^ 2 =
      2 * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
    rw [← hPl]; exact (integral_congr_ae hAE).symm
  -- ———— Step E: factor 4 ————
  have hPl3 : ∫ ξ : ℝ,
      (∫ t in Ioi (0 : ℝ), f t * Real.sin (2 * Real.pi * ξ * t)) ^ 2 =
      (1/2) * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
    have : (4 : ℝ) * ∫ ξ : ℝ,
        (∫ t in Ioi (0 : ℝ), f t * Real.sin (2 * Real.pi * ξ * t)) ^ 2 =
        2 * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
      rw [← integral_const_mul]; exact hPl2
    linarith
  -- ———— Step F: change of variables γ = 2π ξ ————
  have hCoV : ∫ ξ : ℝ,
      (∫ t in Ioi (0 : ℝ), f t * Real.sin (2 * Real.pi * ξ * t)) ^ 2 =
      (1 / (2 * Real.pi)) *
        ∫ γ : ℝ, (∫ t in Ioi (0 : ℝ), f t * Real.sin (γ * t)) ^ 2 :=
    integral_comp_two_pi_smul
      (fun γ => (∫ t in Ioi (0 : ℝ), f t * Real.sin (γ * t)) ^ 2)
  -- ———— Step G: evenness in γ → half-line ————
  have hEv : ∫ γ : ℝ, (∫ t in Ioi (0 : ℝ), f t * Real.sin (γ * t)) ^ 2 =
      2 * ∫ γ in Ioi (0 : ℝ),
        (∫ t in Ioi (0 : ℝ), f t * Real.sin (γ * t)) ^ 2 :=
    integral_sine_sq_eq_two_Ioi f
  -- ———— Step H: combine ————
  have hFinal : ∫ γ in Ioi (0 : ℝ),
      (∫ t in Ioi (0 : ℝ), f t * Real.sin (γ * t)) ^ 2 =
      (Real.pi / 2) * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    have hπne : (2 * Real.pi) ≠ 0 := ne_of_gt hπ
    have step1 : ∫ γ : ℝ, (∫ t in Ioi (0 : ℝ), f t * Real.sin (γ * t)) ^ 2 =
        Real.pi * ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
      have eq := hCoV.symm.trans hPl3
      field_simp at eq
      linarith
    rw [hEv] at step1
    linarith
  -- ———— Integrability part ————
  refine ⟨?_, hFinal⟩
  have hFourierLp_sq_int :
      Integrable (fun ξ => ‖(FourierTransform.fourier
          ((memLp_oddExtC hf_meas hf_sq).toLp :
            Lp ℂ 2 (volume : Measure ℝ))) ξ‖ ^ 2) (volume : Measure ℝ) := by
    have hmem := Lp.memLp (FourierTransform.fourier
      ((memLp_oddExtC hf_meas hf_sq).toLp :
        Lp ℂ 2 (volume : Measure ℝ)))
    exact (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem
  have hSinSq4_int : Integrable
      (fun ξ => 4 * (∫ t in Ioi (0 : ℝ), f t * Real.sin (2 * Real.pi * ξ * t)) ^ 2)
      (volume : Measure ℝ) :=
    hFourierLp_sq_int.congr hAE
  have hSinSq_int : Integrable
      (fun ξ => (∫ t in Ioi (0 : ℝ), f t * Real.sin (2 * Real.pi * ξ * t)) ^ 2)
      (volume : Measure ℝ) := by
    have := hSinSq4_int.const_mul (1/4)
    refine this.congr ?_
    filter_upwards with ξ; ring
  have h2πne : (2 * Real.pi) ≠ 0 := by positivity
  have hGammaSq_int : Integrable
      (fun γ => (∫ t in Ioi (0 : ℝ), f t * Real.sin (γ * t)) ^ 2)
      (volume : Measure ℝ) :=
    (integrable_comp_mul_left_iff
      (g := fun γ => (∫ t in Ioi (0 : ℝ), f t * Real.sin (γ * t)) ^ 2)
      h2πne).mp hSinSq_int
  exact hGammaSq_int.restrict
  -- replacing `cos` in the Fourier computation. Imag part becomes active,
  -- real part vanishes by evenness. Same Plancherel + Step 6 bridge, same
  -- change of variables. The π/2 constant comes out identically.

end HalfLineParseval
