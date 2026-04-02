import Mathlib

/-!
# Instantiation of CoshHarmonicReprI and Final Closure

We instantiate the `CoshHarmonicReprI` structure with `riemannZeta` on the
punctured cosh reflection domain `U = coshReflDomain \ {1}`, then assemble
the full proof chain.
-/

open Complex Real Set Filter Topology

noncomputable section

/-! ## Domain definitions -/

/-- The cosh reflection domain: `{s : ℂ | 0 < Re(s) < π/3}`. -/
def coshReflDomain : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < Real.pi / 3}

/-- The overlap region: `{s : ℂ | 1 < Re(s) < π/3}`. -/
def overlapRegionI : Set ℂ :=
  {s : ℂ | 1 < s.re ∧ s.re < Real.pi / 3}

/-- The punctured cosh reflection domain: the strip minus the pole at s = 1. -/
def coshReflDomainPunctured : Set ℂ :=
  coshReflDomain \ {1}

/-! ## Basic geometric facts -/

theorem pi_div_three_gt_oneI : Real.pi / 3 > 1 := by
  linarith [Real.pi_gt_three]

theorem pi_div_three_lt_twoI : Real.pi / 3 < 2 := by
  linarith [Real.pi_lt_four]

/-! ## Domain properties -/

theorem coshReflDomain_isOpen : IsOpen coshReflDomain :=
  isOpen_Ioo.preimage Complex.continuous_re

theorem coshReflDomainPunctured_isOpen : IsOpen coshReflDomainPunctured :=
  coshReflDomain_isOpen.sdiff isClosed_singleton

theorem overlapRegionI_isOpen : IsOpen overlapRegionI := by
  exact (isOpen_Ioo (a := (1 : ℝ)) (b := Real.pi / 3)).preimage continuous_re

theorem overlapRegionI_nonempty : overlapRegionI.Nonempty := by
  use ⟨(1 + Real.pi / 3) / 2, 0⟩
  constructor <;> simp <;> linarith [Real.pi_gt_three]

theorem overlapRegionI_isPreconnected : IsPreconnected overlapRegionI := by
  have : overlapRegionI = Complex.re ⁻¹' Set.Ioo 1 (Real.pi / 3) := by
    ext s; simp [overlapRegionI, Set.mem_Ioo]
  rw [this]
  exact ((convex_Ioo 1 (Real.pi / 3)).linear_preimage
    Complex.reCLM.toLinearMap).isPreconnected

theorem overlapRegionI_subset_coshReflDomain : overlapRegionI ⊆ coshReflDomain := by
  intro s ⟨h1, h2⟩; exact ⟨by linarith, h2⟩

/-- The overlap avoids s = 1: every point in the overlap has Re(s) > 1. -/
theorem overlapRegionI_not_mem_one : (1 : ℂ) ∉ overlapRegionI := by
  intro ⟨h, _⟩; simp at h

theorem overlapRegionI_subset_punctured : overlapRegionI ⊆ coshReflDomainPunctured := by
  intro s hs
  refine ⟨overlapRegionI_subset_coshReflDomain hs, ?_⟩
  intro heq; subst heq; exact absurd hs.1 (by simp)

/-! ## Convexity and connectedness of the full domain -/

theorem coshReflDomain_convex : Convex ℝ coshReflDomain := by
  have : coshReflDomain = Complex.re ⁻¹' Set.Ioo 0 (Real.pi / 3) := by
    ext s; simp [coshReflDomain, Set.mem_Ioo]
  rw [this]
  exact (convex_Ioo 0 (Real.pi / 3)).linear_preimage Complex.reCLM.toLinearMap

theorem coshReflDomain_isPreconnected : IsPreconnected coshReflDomain :=
  coshReflDomain_convex.isPreconnected

theorem coshReflDomain_nonempty : coshReflDomain.Nonempty :=
  ⟨⟨1/2, 0⟩, by refine ⟨by norm_num, ?_⟩; simp; linarith [pi_div_three_gt_oneI]⟩

theorem coshReflDomain_isConnected : IsConnected coshReflDomain :=
  ⟨coshReflDomain_nonempty, coshReflDomain_isPreconnected⟩

/-! ## Preconnectedness of the punctured domain -/

/-
The punctured cosh reflection domain is preconnected.
    We decompose it as a union of four convex overlapping pieces:
    the left strip (Re < 1), the right strip (Re > 1),
    the upper half (Im > 0), and the lower half (Im < 0).
-/
theorem coshReflDomainPunctured_isPreconnected :
    IsPreconnected coshReflDomainPunctured := by
  -- Let's denote the four convex sets as A, B, C, and D.
  set A : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1}
  set B : Set ℂ := {s : ℂ | 1 < s.re ∧ s.re < Real.pi / 3}
  set C : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < Real.pi / 3 ∧ s.im > 0}
  set D : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < Real.pi / 3 ∧ s.im < 0};
  -- We need to show that the union of these four sets is equal to the punctured cosh reflection domain.
  have h_union : coshReflDomainPunctured = A ∪ B ∪ C ∪ D := by
    ext s;
    unfold coshReflDomainPunctured A B C D; simp +decide [ and_assoc, or_assoc ] ;
    constructor <;> intro h <;> simp_all +decide [ Complex.ext_iff, coshReflDomain ];
    · grind;
    · rcases h with ( h | h | h | h ) <;> exact ⟨ ⟨ by linarith, by linarith [ Real.pi_gt_three ] ⟩, by intros; linarith ⟩;
  -- Each of these sets is convex, hence preconnected.
  have hA_preconnected : IsPreconnected A := by
    -- The set $A$ is convex, hence preconnected.
    have hA_convex : Convex ℝ A := by
      refine' convex_iff_forall_pos.mpr _;
      simp +zetaDelta at *;
      exact fun x hx₁ hx₂ y hy₁ hy₂ a b ha hb hab => ⟨ by nlinarith, by nlinarith ⟩
    exact hA_convex.isPreconnected
  have hB_preconnected : IsPreconnected B := by
    -- The set $B$ is convex, hence preconnected.
    have hB_convex : Convex ℝ B := by
      exact convex_halfSpace_re_gt 1 |> ( fun h => h.inter ( convex_halfSpace_re_lt ( Real.pi / 3 ) ) )
    exact hB_convex.isPreconnected
  have hC_preconnected : IsPreconnected C := by
    -- The set $C$ is convex, hence preconnected.
    have hC_convex : Convex ℝ C := by
      refine' convex_iff_forall_pos.mpr _;
      simp +zetaDelta at *;
      exact fun x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃ a b ha hb hab => ⟨ by nlinarith, by nlinarith, by nlinarith ⟩
    exact hC_convex.isPreconnected
  have hD_preconnected : IsPreconnected D := by
    -- The set $D$ is convex, hence preconnected.
    have hD_convex : Convex ℝ D := by
      refine' convex_iff_forall_pos.mpr _;
      simp +zetaDelta at *;
      exact fun x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃ a b ha hb hab => ⟨ by nlinarith, by nlinarith, by nlinarith ⟩;
    exact hD_convex.isPreconnected;
  -- The union of overlapping preconnected sets is preconnected.
  have h_union_preconnected : IsPreconnected (A ∪ C) := by
    apply_rules [ IsPreconnected.union ];
    rotate_right;
    exacts [ ⟨ 1 / 2, 1 ⟩, ⟨ by norm_num, by norm_num ⟩, ⟨ by norm_num, by linarith [ Real.pi_gt_three ], by norm_num ⟩ ]
  have h_union_preconnected' : IsPreconnected (A ∪ C ∪ B) := by
    apply_rules [ IsPreconnected.union ];
    rotate_right;
    exact ⟨ 1 + ( Real.pi / 3 - 1 ) / 2, 1 ⟩;
    · exact Or.inr ⟨ by norm_num; linarith [ Real.pi_gt_three ], by norm_num; linarith [ Real.pi_gt_three ], by norm_num ⟩;
    · exact ⟨ by norm_num; linarith [ Real.pi_gt_three ], by norm_num; linarith [ Real.pi_gt_three ] ⟩
  have h_union_preconnected'' : IsPreconnected (A ∪ C ∪ B ∪ D) := by
    apply_rules [ IsPreconnected.union ];
    rotate_right;
    exact ⟨ 1 / 2, -1 ⟩;
    · norm_num [ A, B, C ];
    · exact ⟨ by norm_num, by norm_num; linarith [ Real.pi_gt_three ], by norm_num ⟩;
  convert h_union_preconnected'' using 1 ; ext ; aesop

/-! ## Analyticity of ζ on the punctured domain -/

theorem riemannZeta_analyticOnNhd_punctured :
    AnalyticOnNhd ℂ riemannZeta coshReflDomainPunctured := by
  have : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
    rw [Complex.analyticOnNhd_iff_differentiableOn isOpen_compl_singleton]
    intro s hs
    exact (differentiableAt_riemannZeta
      (Set.mem_compl_singleton_iff.mp hs)).differentiableWithinAt
  exact this.mono (fun s hs => hs.2)

theorem riemannZeta_analyticOnNhd_overlapI :
    AnalyticOnNhd ℂ riemannZeta overlapRegionI := by
  exact riemannZeta_analyticOnNhd_punctured.mono overlapRegionI_subset_punctured

/-! ## The CoshHarmonicReprI structure -/

/-- A cosh harmonic representation of ζ on a connected open domain
    containing the overlap, agreeing with ζ on the overlap. -/
structure CoshHarmonicReprI (U : Set ℂ) where
  repr : ℂ → ℂ
  domain_isOpen : IsOpen U
  domain_isPreconnected : IsPreconnected U
  domain_contains_overlap : overlapRegionI ⊆ U
  repr_analytic : AnalyticOnNhd ℂ repr U
  repr_eq_zeta_on_overlap : EqOn repr riemannZeta overlapRegionI

/-! ## Instantiation -/

/-- **The concrete instantiation**: `riemannZeta` itself is a `CoshHarmonicReprI`
    on the punctured cosh reflection domain. -/
def zetaCoshRepr : CoshHarmonicReprI coshReflDomainPunctured where
  repr := riemannZeta
  domain_isOpen := coshReflDomainPunctured_isOpen
  domain_isPreconnected := coshReflDomainPunctured_isPreconnected
  domain_contains_overlap := overlapRegionI_subset_punctured
  repr_analytic := riemannZeta_analyticOnNhd_punctured
  repr_eq_zeta_on_overlap := fun _ _ => rfl

/-! ## The identity theorem gives full agreement -/

theorem identity_theorem_on_overlapI
    {U : Set ℂ} (_hU_open : IsOpen U) (hU_conn : IsPreconnected U)
    (hV_sub : overlapRegionI ⊆ U)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (heq : EqOn f g overlapRegionI) :
    EqOn f g U := by
  obtain ⟨z₀, hz₀⟩ := overlapRegionI_nonempty
  have hz₀U : z₀ ∈ U := hV_sub hz₀
  have hfg_ev : f =ᶠ[nhds z₀] g := by
    have hO : overlapRegionI ∈ nhds z₀ := overlapRegionI_isOpen.mem_nhds hz₀
    exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨overlapRegionI, hO, heq⟩
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hU_conn hz₀U hfg_ev

/-- The main invariance theorem. -/
theorem cosh_harmonics_zeta_invarianceI
    {U : Set ℂ} (G : CoshHarmonicReprI U)
    (hζ_analytic : AnalyticOnNhd ℂ riemannZeta U) :
    EqOn G.repr riemannZeta U
    ∧ ({z ∈ U | G.repr z = 0} = {z ∈ U | riemannZeta z = 0})
    ∧ (∀ z ∈ U, meromorphicOrderAt G.repr z = meromorphicOrderAt riemannZeta z) := by
  have heqU : EqOn G.repr riemannZeta U :=
    identity_theorem_on_overlapI G.domain_isOpen G.domain_isPreconnected
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

theorem zeta_zeros_determined_by_overlap :
    {z ∈ coshReflDomainPunctured | riemannZeta z = 0} =
    {z ∈ coshReflDomainPunctured | zetaCoshRepr.repr z = 0} := by
  have h := (cosh_harmonics_zeta_invarianceI zetaCoshRepr
    riemannZeta_analyticOnNhd_punctured).2.1
  exact h.symm

theorem every_zero_detected (s : ℂ) (hs : s ∈ coshReflDomainPunctured)
    (hz : riemannZeta s = 0) :
    zetaCoshRepr.repr s = 0 := by
  have h := (cosh_harmonics_zeta_invarianceI zetaCoshRepr
    riemannZeta_analyticOnNhd_punctured).1
  rw [h hs]; exact hz

end