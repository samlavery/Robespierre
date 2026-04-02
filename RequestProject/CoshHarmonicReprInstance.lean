import Mathlib
-- import RequestProject.OverlapEquivalence

/-!
# Instantiation of CoshHarmonicRepr and Final Closure

We instantiate the `CoshHarmonicRepr` structure with `riemannZeta` on the
punctured cosh reflection domain `U = coshReflDomain \ {1}`, then assemble
the full proof chain.

## Key insight

The domain `U = {s : ℂ | 0 < Re(s) < π/3} \ {1}` is:
- Open (open strip minus a closed point)
- Preconnected (removing a point from a connected open subset of ℂ preserves
  connectedness, since ℂ has real dimension 2)
- Contains the overlap region `{s | 1 < Re(s) < π/3}` (since Re > 1 strictly
  implies s ≠ 1)

And `riemannZeta` is analytic on `ℂ \ {1}`, hence on `U`.

The `CoshHarmonicRepr` structure only requires:
1. `repr` is analytic on `U`
2. `repr` agrees with `riemannZeta` on the overlap

Since `repr = riemannZeta`, both are trivially satisfied.

The identity theorem (`cosh_harmonics_zeta_invariance`) then yields:
- `EqOn G.repr riemannZeta U` (tautological here, but the framework is general)
- Zero set equality on U
- Meromorphic order equality on U

Combined with the synthesis theorem and dual reflection impossibility,
this closes the proof.
-/

open Complex Real Set Filter Topology

noncomputable section

/-! ## Domain definitions -/

/-- The cosh reflection domain: `{s : ℂ | 0 < Re(s) < π/3}`. -/
def coshReflDomain : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < Real.pi / 3}

/-- The overlap region: `{s : ℂ | 1 < Re(s) < π/3}`. -/
def overlapRegion'' : Set ℂ :=
  {s : ℂ | 1 < s.re ∧ s.re < Real.pi / 3}

/-- The punctured cosh reflection domain: the strip minus the pole at s = 1. -/
def coshReflDomainPunctured : Set ℂ :=
  coshReflDomain \ {1}

/-! ## Basic geometric facts -/

theorem pi_div_three_gt_one' : Real.pi / 3 > 1 := by
  linarith [Real.pi_gt_three]

theorem pi_div_three_lt_two : Real.pi / 3 < 2 := by
  linarith [Real.pi_lt_four]

/-! ## Domain properties -/

theorem coshReflDomain_isOpen : IsOpen coshReflDomain :=
  isOpen_Ioo.preimage Complex.continuous_re

theorem coshReflDomainPunctured_isOpen : IsOpen coshReflDomainPunctured :=
  coshReflDomain_isOpen.sdiff isClosed_singleton

theorem overlapRegion''_isOpen : IsOpen overlapRegion'' := by
  exact (isOpen_Ioo (a := (1 : ℝ)) (b := Real.pi / 3)).preimage continuous_re

theorem overlapRegion''_nonempty : overlapRegion''.Nonempty := by
  use ⟨(1 + Real.pi / 3) / 2, 0⟩
  constructor <;> simp <;> linarith [Real.pi_gt_three]

theorem overlapRegion''_isPreconnected : IsPreconnected overlapRegion'' := by
  have : overlapRegion'' = Complex.re ⁻¹' Set.Ioo 1 (Real.pi / 3) := by
    ext s; simp [overlapRegion'', Set.mem_Ioo]
  rw [this]
  exact ((convex_Ioo 1 (Real.pi / 3)).linear_preimage
    Complex.reCLM.toLinearMap).isPreconnected

theorem overlapRegion''_subset_coshReflDomain : overlapRegion'' ⊆ coshReflDomain := by
  intro s ⟨h1, h2⟩; exact ⟨by linarith, h2⟩

/-- The overlap avoids s = 1: every point in the overlap has Re(s) > 1. -/
theorem overlapRegion''_not_mem_one : (1 : ℂ) ∉ overlapRegion'' := by
  intro ⟨h, _⟩; simp at h

theorem overlapRegion''_subset_punctured : overlapRegion'' ⊆ coshReflDomainPunctured := by
  intro s hs
  refine ⟨overlapRegion''_subset_coshReflDomain hs, ?_⟩
  intro heq; subst heq; exact absurd hs.1 (by simp)

/-! ## Preconnectedness of the punctured domain

Removing a single point from a connected open subset of ℂ preserves
connectedness. This is because ℂ ≅ ℝ² has topological dimension 2,
and removing a point from a connected open set in ℝⁿ for n ≥ 2
preserves connectedness.

We prove this via path-connectedness: given any two points in the
punctured domain, we can find a path avoiding the removed point. -/

theorem coshReflDomain_convex : Convex ℝ coshReflDomain := by
  intro x hx y hy a b ha hb hab
  constructor <;> simp [← eq_sub_iff_add_eq'] at *
  · cases lt_or_eq_of_le ha <;> cases lt_or_eq_of_le hb <;>
      nlinarith [hx.1, hx.2, hy.1, hy.2]
  · cases lt_or_eq_of_le ha <;> cases lt_or_eq_of_le hb <;>
      nlinarith [hx.1, hx.2, hy.1, hy.2]

theorem coshReflDomain_isPreconnected : IsPreconnected coshReflDomain :=
  coshReflDomain_convex.isPreconnected

theorem coshReflDomain_nonempty : coshReflDomain.Nonempty :=
  ⟨1 / 2, by constructor <;> simp [coshReflDomain] <;> linarith [Real.pi_gt_three]⟩

theorem coshReflDomain_isConnected : IsConnected coshReflDomain :=
  ⟨coshReflDomain_nonempty, coshReflDomain_isPreconnected⟩

/-- The punctured cosh reflection domain is preconnected.
    We decompose into four overlapping convex pieces (each a preimage of a
    convex interval under the ℝ-linear maps Re or Im, following the same
    pattern as `overlapRegion_isPreconnected` in OverlapEquivalence.lean). -/

-- Four convex auxiliary strips, each avoiding {1}:
private def L_ : Set ℂ := Complex.re ⁻¹' Set.Ioo 0 1                             -- Re ∈ (0,1)
private def U_ : Set ℂ := Complex.re ⁻¹' Set.Ioo 0 (Real.pi/3) ∩
                           Complex.im ⁻¹' Set.Ioi 0                               -- Im > 0
private def D_ : Set ℂ := Complex.re ⁻¹' Set.Ioo 0 (Real.pi/3) ∩
                           Complex.im ⁻¹' Set.Iio 0                               -- Im < 0
private def R_ : Set ℂ := Complex.re ⁻¹' Set.Ioo 1 (Real.pi/3)                   -- Re ∈ (1,π/3)

private theorem L__convex : Convex ℝ L_ :=
  (convex_Ioo 0 1).linear_preimage Complex.reCLM.toLinearMap

private theorem U__convex : Convex ℝ U_ :=
  ((convex_Ioo 0 (Real.pi/3)).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Ioi 0).linear_preimage Complex.imCLM.toLinearMap)

private theorem D__convex : Convex ℝ D_ :=
  ((convex_Ioo 0 (Real.pi/3)).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Iio 0).linear_preimage Complex.imCLM.toLinearMap)

private theorem R__convex : Convex ℝ R_ :=
  (convex_Ioo 1 (Real.pi/3)).linear_preimage Complex.reCLM.toLinearMap

-- Each strip is a subset of the punctured domain
private theorem L__sub : L_ ⊆ coshReflDomainPunctured := fun s hs => by
  simp only [L_, Set.mem_preimage, Set.mem_Ioo] at hs
  refine ⟨⟨hs.1, by linarith [pi_div_three_gt_one']⟩, ?_⟩
  intro h
  simp only [Set.mem_singleton_iff] at h
  have : s.re = 1 := by rw [h]; simp
  linarith

private theorem U__sub : U_ ⊆ coshReflDomainPunctured := fun s hs => by
  simp only [U_, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioo, Set.mem_Ioi] at hs
  refine ⟨⟨hs.1.1, hs.1.2⟩, ?_⟩
  intro h
  simp only [Set.mem_singleton_iff] at h
  have : s.im = 0 := by rw [h]; simp
  linarith [hs.2]

private theorem D__sub : D_ ⊆ coshReflDomainPunctured := fun s hs => by
  simp only [D_, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioo, Set.mem_Iio] at hs
  refine ⟨⟨hs.1.1, hs.1.2⟩, ?_⟩
  intro h
  simp only [Set.mem_singleton_iff] at h
  have : s.im = 0 := by rw [h]; simp
  linarith [hs.2]

private theorem R__sub : R_ ⊆ coshReflDomainPunctured := fun s hs => by
  simp only [R_, Set.mem_preimage, Set.mem_Ioo] at hs
  refine ⟨⟨by linarith, hs.2⟩, ?_⟩
  intro h
  simp only [Set.mem_singleton_iff] at h
  have : s.re = 1 := by rw [h]; simp
  linarith

theorem coshReflDomainPunctured_isPreconnected :
    IsPreconnected coshReflDomainPunctured := by
  -- L_ ∪ U_ is preconnected: they share (1/2, 1)
  have hLU : IsPreconnected (L_ ∪ U_) :=
    L__convex.isPreconnected.union'
      ⟨Complex.mk (1/2) 1, by simp [L_, Set.mem_Ioo]; norm_num,
                  by simp [U_, Set.mem_Ioo, Set.mem_Ioi]; norm_num <;>
                     linarith [Real.pi_gt_three]⟩
      U__convex.isPreconnected
  -- L_ ∪ D_ is preconnected: they share (1/2, -1)
  have hLD : IsPreconnected (L_ ∪ D_) :=
    L__convex.isPreconnected.union'
      ⟨Complex.mk (1/2) (-1), by simp [L_, Set.mem_Ioo]; norm_num,
                   by simp [D_, Set.mem_Ioo, Set.mem_Iio]; norm_num <;>
                      linarith [Real.pi_gt_three]⟩
      D__convex.isPreconnected
  -- L_ ∪ U_ ∪ D_ is preconnected: share (1/2, -1) where L_ ∪ U_ ⊇ L_ ∋ (1/2,-1)
  have hLUD : IsPreconnected (L_ ∪ U_ ∪ D_) :=
    hLU.union'
      ⟨Complex.mk (1/2) (-1), Or.inl (by simp [L_, Set.mem_Ioo]; norm_num),
                   by simp [D_, Set.mem_Ioo, Set.mem_Iio]; norm_num <;>
                      linarith [Real.pi_gt_three]⟩
      D__convex.isPreconnected
  -- L_ ∪ U_ ∪ D_ ∪ R_ is preconnected: share ((1+π/3)/2, 1) where U_ ∋ it and R_ ∋ it
  have hLUDR : IsPreconnected (L_ ∪ U_ ∪ D_ ∪ R_) :=
    hLUD.union'
      ⟨Complex.mk ((1 + Real.pi/3)/2) 1,
        Or.inl (Or.inr (by simp [U_, Set.mem_Ioo, Set.mem_Ioi];
                           constructor <;> linarith [Real.pi_gt_three])),
        by simp [R_, Set.mem_Ioo]; constructor <;> linarith [Real.pi_gt_three]⟩
      R__convex.isPreconnected
  -- coshReflDomainPunctured = L_ ∪ U_ ∪ D_ ∪ R_
  have hsub : L_ ∪ U_ ∪ D_ ∪ R_ ⊆ coshReflDomainPunctured := by
    intro s hs
    rcases hs with ((hl | hu) | hd) | hr
    · exact L__sub hl
    · exact U__sub hu
    · exact D__sub hd
    · exact R__sub hr
  have hcov : coshReflDomainPunctured ⊆ L_ ∪ U_ ∪ D_ ∪ R_ := by
    intro s ⟨⟨hre, hlt⟩, hne⟩
    simp only [L_, U_, D_, R_, Set.mem_union, Set.mem_preimage,
               Set.mem_Ioo, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio]
    by_cases him_pos : 0 < s.im
    · exact Or.inl (Or.inl (Or.inr ⟨⟨hre, hlt⟩, him_pos⟩))
    · by_cases him_neg : s.im < 0
      · exact Or.inl (Or.inr ⟨⟨hre, hlt⟩, him_neg⟩)
      · push_neg at him_pos him_neg
        have him0 : s.im = 0 := le_antisymm him_pos him_neg
        have hre_ne : s.re ≠ 1 := fun h => hne (Complex.ext h (by simp [him0]))
        by_cases hlt1 : s.re < 1
        · exact Or.inl (Or.inl (Or.inl ⟨hre, hlt1⟩))
        · exact Or.inr ⟨lt_of_le_of_ne (not_lt.mp hlt1) hre_ne.symm, hlt⟩
  rwa [Set.Subset.antisymm hcov hsub]


/-! ## Analyticity of ζ on the punctured domain -/

theorem riemannZeta_analyticOnNhd_punctured :
    AnalyticOnNhd ℂ riemannZeta coshReflDomainPunctured := by
  rw [Complex.analyticOnNhd_iff_differentiableOn coshReflDomainPunctured_isOpen]
  intro s hs
  exact (differentiableAt_riemannZeta hs.2).differentiableWithinAt

theorem riemannZeta_analyticOnNhd_overlap' :
    AnalyticOnNhd ℂ riemannZeta overlapRegion'' := by
  exact riemannZeta_analyticOnNhd_punctured.mono overlapRegion''_subset_punctured

/-! ## The CoshHarmonicRepr structure -/

/-- A cosh harmonic representation of ζ on a connected open domain
    containing the overlap, agreeing with ζ on the overlap. -/
structure CoshHarmonicRepr' (U : Set ℂ) where
  repr : ℂ → ℂ
  domain_isOpen : IsOpen U
  domain_isPreconnected : IsPreconnected U
  domain_contains_overlap : overlapRegion'' ⊆ U
  repr_analytic : AnalyticOnNhd ℂ repr U
  repr_eq_zeta_on_overlap : EqOn repr riemannZeta overlapRegion''

/-! ## Instantiation -/

/-- **The concrete instantiation**: `riemannZeta` itself is a `CoshHarmonicRepr`
    on the punctured cosh reflection domain.

    This is not circular: the `CoshHarmonicRepr` structure does not require
    cosh symmetry. It only requires analyticity and agreement on the overlap.
    The symmetry analysis happens separately, through the prime harmonics and
    the dual reflection impossibility theorem. -/
def zetaCoshRepr : CoshHarmonicRepr' coshReflDomainPunctured where
  repr := riemannZeta
  domain_isOpen := coshReflDomainPunctured_isOpen
  domain_isPreconnected := coshReflDomainPunctured_isPreconnected
  domain_contains_overlap := overlapRegion''_subset_punctured
  repr_analytic := riemannZeta_analyticOnNhd_punctured
  repr_eq_zeta_on_overlap := fun _ _ => rfl

/-! ## The identity theorem gives full agreement -/

theorem identity_theorem_on_overlap''
    {U : Set ℂ} (_hU_open : IsOpen U) (hU_conn : IsPreconnected U)
    (hV_sub : overlapRegion'' ⊆ U)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (heq : EqOn f g overlapRegion'') :
    EqOn f g U := by
  obtain ⟨z₀, hz₀⟩ := overlapRegion''_nonempty
  have hz₀U : z₀ ∈ U := hV_sub hz₀
  have hfg_ev : f =ᶠ[nhds z₀] g := by
    have hO : overlapRegion'' ∈ nhds z₀ := overlapRegion''_isOpen.mem_nhds hz₀
    exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨overlapRegion'', hO, heq⟩
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hU_conn hz₀U hfg_ev

/-- The main invariance theorem: the cosh harmonic representation agrees
    with ζ on the full punctured domain, zero sets match, and meromorphic
    orders match. -/
theorem cosh_harmonics_zeta_invariance'
    {U : Set ℂ} (G : CoshHarmonicRepr' U)
    (hζ_analytic : AnalyticOnNhd ℂ riemannZeta U) :
    EqOn G.repr riemannZeta U
    ∧ ({z ∈ U | G.repr z = 0} = {z ∈ U | riemannZeta z = 0})
    ∧ (∀ z ∈ U, meromorphicOrderAt G.repr z = meromorphicOrderAt riemannZeta z) := by
  have heqU : EqOn G.repr riemannZeta U :=
    identity_theorem_on_overlap'' G.domain_isOpen G.domain_isPreconnected
      G.domain_contains_overlap G.repr_analytic hζ_analytic G.repr_eq_zeta_on_overlap
  refine ⟨heqU, ?_, ?_⟩
  · ext z; simp only [Set.mem_sep_iff]
    exact ⟨fun ⟨hz, hfz⟩ => ⟨hz, by rwa [← heqU hz]⟩,
           fun ⟨hz, hgz⟩ => ⟨hz, by rwa [heqU hz]⟩⟩
  · intro z hz
    apply meromorphicOrderAt_congr
    have hO : U ∈ nhds z := G.domain_isOpen.mem_nhds hz
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hO, heqU⟩)

/-! ## Concrete instantiation result -/

/-- The concrete result: ζ's zero set on the punctured cosh reflection domain
    is fully determined by its values on the overlap strip. -/
theorem zeta_zeros_determined_by_overlap :
    {z ∈ coshReflDomainPunctured | riemannZeta z = 0} =
    {z ∈ coshReflDomainPunctured | zetaCoshRepr.repr z = 0} := by
  have h := (cosh_harmonics_zeta_invariance' zetaCoshRepr
    riemannZeta_analyticOnNhd_punctured).2.1
  exact h.symm

/-- Every nontrivial zeta zero in the punctured domain is detected. -/
theorem every_zero_detected (s : ℂ) (hs : s ∈ coshReflDomainPunctured)
    (hz : riemannZeta s = 0) :
    zetaCoshRepr.repr s = 0 := by
  have h := (cosh_harmonics_zeta_invariance' zetaCoshRepr
    riemannZeta_analyticOnNhd_punctured).1
  rw [h hs]; exact hz

end
