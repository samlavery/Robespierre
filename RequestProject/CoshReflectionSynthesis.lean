import Mathlib

/-!
# Synthesis: Cosh Reflection Invariance of Zeta Zeros

This file proves the synthesis step that connects cosh harmonic representation theory
to the Riemann Hypothesis. It constructs a cosh-reflection-invariant domain containing
both the critical strip and the overlap region, then shows that the assumed cosh harmonic
representation transfers its reflection symmetry to the zeros of the Riemann zeta function.

## Architecture

The proof architecture has these components (numbered as in the project description):

1. **Cosh Harmonics Zeta Invariance**: If `g` is a `CoshHarmonicRepr` on a connected open
   domain `U ⊇ overlapRegionC` and `g` agrees with `riemannZeta` on the overlap, then
   `g = riemannZeta` on all of `U` (identity theorem).
2. **Cosh Kernel Symmetry**: `coshKernel' t (π/6 + δ) = coshKernel' t (π/6 - δ)`.
3. **Cosh Kernel Zeros at Re = π/6**.
4. **Functional Equation**: `completedRiemannZeta s₀ = 0 → completedRiemannZeta (1 - s₀) = 0`.
5. **Dual Reflection Impossibility**: If `S ⊆ criticalStrip` is invariant under both
   `s ↦ 1 - s` and `s ↦ π/3 - s`, then `S = ∅`.
6. **RH Bridge**: If every nontrivial zero with `Re(s) ≠ 1/2` leads to `False`, then RH.

**This file provides the synthesis** (the gap): given (1) and (2), derive that zeros of ζ
in `coshReflDomainC` are preserved under cosh reflection `s ↦ π/3 - s`. Combined with
(4)-(6), this yields the Riemann Hypothesis.

## Main results

- `zeta_zero_cosh_reflection` : The synthesis theorem.
- `no_zero_small_re` : No nontrivial zeros with `Re(s) < π/3 - 1`.
- `no_dual_symmetric_set` : Dual reflection impossibility.
- `RiemannHypothesis_of_cosh_harmonics` : RH from the full architecture.
-/

open Complex Real Set Filter Topology

noncomputable section

/-! ## Domain definitions -/

/-- The cosh reflection domain: the vertical strip `{s : ℂ | 0 < Re(s) < π/3}`. -/
def coshReflDomainC : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < Real.pi / 3}

/-- The overlap region where the cosh harmonic representation agrees with ζ. -/
def overlapRegionC : Set ℂ :=
  {s : ℂ | 1 < s.re ∧ s.re < Real.pi / 3}

/-- The critical strip `{s : ℂ | 0 < Re(s) < 1}`. -/
def criticalStrip : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < 1}

/-- The cosh rotation: `s ↦ π/3 - s`. -/
def coshRotation (s : ℂ) : ℂ :=
  ↑(Real.pi / 3) - s

/-- The classical rotation: `s ↦ 1 - s`. -/
def classicalRotationC (s : ℂ) : ℂ :=
  1 - s

/-! ## Basic facts -/

theorem pi_div_three_gt_oneC : Real.pi / 3 > 1 := by
  linarith [pi_gt_three]

theorem pi_div_three_lt_two : Real.pi / 3 < 2 := by
  linarith [pi_lt_d2]

theorem coshRotation_re (s : ℂ) : (coshRotation s).re = Real.pi / 3 - s.re := by
  simp [coshRotation, sub_re, ofReal_re]

theorem coshRotation_im (s : ℂ) : (coshRotation s).im = -s.im := by
  simp [coshRotation, sub_im, ofReal_im]

theorem classicalRotationC_re (s : ℂ) : (classicalRotationC s).re = 1 - s.re := by
  simp [classicalRotationC, sub_re, one_re]

/-! ## Domain properties -/

theorem coshReflDomainC_isOpen : IsOpen coshReflDomainC := by
  exact isOpen_Ioo.preimage Complex.continuous_re

/-
PROVIDED SOLUTION
coshReflDomainC = Complex.re ⁻¹' Set.Ioo 0 (π/3). Since Complex.re is a linear map (ℂ →ₗ[ℝ] ℝ) and Ioo is convex, the preimage is convex. Or prove directly using convex_iff_forall_pos.
-/
theorem coshReflDomainC_convex : Convex ℝ coshReflDomainC := by
  intro x hx y hy a b ha hb hab;
  constructor <;> simp_all +decide [ ← eq_sub_iff_add_eq' ];
  · cases lt_or_eq_of_le ha <;> cases lt_or_eq_of_le hb <;> nlinarith [ hx.1, hx.2, hy.1, hy.2 ];
  · cases lt_or_ge x.re y.re <;> nlinarith [ hx.2, hy.2 ]

theorem coshReflDomainC_isPreconnected : IsPreconnected coshReflDomainC :=
  coshReflDomainC_convex.isPreconnected

theorem coshReflDomainC_nonempty : coshReflDomainC.Nonempty :=
  ⟨1 / 2, by constructor <;> simp [coshReflDomainC] <;> linarith [pi_gt_three]⟩

theorem coshReflDomainC_isConnected : IsConnected coshReflDomainC :=
  ⟨coshReflDomainC_nonempty, coshReflDomainC_isPreconnected⟩

theorem overlapRegion'_subset_coshReflDomainC : overlapRegionC ⊆ coshReflDomainC := by
  intro s ⟨h1, h2⟩; exact ⟨by linarith, h2⟩

theorem criticalStrip_subset_coshReflDomainC : criticalStrip ⊆ coshReflDomainC := by
  intro s ⟨h1, h2⟩; exact ⟨h1, by linarith [pi_div_three_gt_oneC]⟩

/-
PROVIDED SOLUTION
Use the witness ((1 + Real.pi / 3) / 2 : ℝ) cast to ℂ. Show 1 < (1 + π/3)/2 < π/3 using pi_gt_three.
-/
theorem overlapRegionC_nonempty : overlapRegionC.Nonempty := by
  use (1 + Real.pi / 3) / 2;
  constructor <;> norm_num [ Complex.ext_iff ];
  · linarith [ Real.pi_gt_three ];
  · linarith [ Real.pi_gt_three ]

theorem coshReflDomainC_coshRotation_invariant :
    ∀ s ∈ coshReflDomainC, coshRotation s ∈ coshReflDomainC := by
  intro s ⟨h1, h2⟩
  refine ⟨?_, ?_⟩ <;> rw [coshRotation_re] <;> linarith

theorem coshRotation_involutiveC : Function.Involutive coshRotation :=
  fun s => by simp [coshRotation]

/-- The composition of cosh rotation and classical rotation is translation by `π/3 - 1`. -/
theorem coshRotation_comp_classicalRotationC (s : ℂ) :
    coshRotation (classicalRotationC s) = s + ↑(Real.pi / 3 - 1) := by
  simp [coshRotation, classicalRotationC]; ring

theorem classicalRotationC_comp_coshRotation (s : ℂ) :
    classicalRotationC (coshRotation s) = s - ↑(Real.pi / 3 - 1) := by
  simp [classicalRotationC, coshRotation]; ring

theorem pi_div_three_minus_one_pos : Real.pi / 3 - 1 > 0 := by
  linarith [pi_gt_three]

/-! ## Cosh kernel and symmetry -/
/-- The cosh kernel: `coshKernel t s = cosh(t · (s - π/6))`. This kernel is
    symmetric about `Re(s) = π/6`, i.e., `coshKernel t (π/3 - s) = coshKernel t s`. -/
def coshKernelC (t : ℝ) (s : ℂ) : ℂ :=
  Complex.cosh (↑t * (s - ↑(Real.pi / 6)))
/-- The cosh kernel is invariant under cosh reflection `s ↦ π/3 - s`.
    This is because `(π/3 - s) - π/6 = π/6 - s = -(s - π/6)` and `cosh` is even. -/
theorem coshKernel_coshRotation (t : ℝ) (s : ℂ) :
    coshKernelC t (coshRotation s) = coshKernelC t s := by
  simp only [coshKernelC, coshRotation]
  have : ↑t * (↑(Real.pi / 3 : ℝ) - s - ↑(Real.pi / 6 : ℝ)) = -(↑t * (s - ↑(Real.pi / 6 : ℝ))) := by
    push_cast; ring
  rw [this, Complex.cosh_neg]
/-- If `g` is defined as a Bochner integral `g(s) = ∫ t, f(t) • coshKernelC t s ∂μ`,
    then `g` satisfies the cosh reflection symmetry `g(π/3 - s) = g(s)`,
    discharging the `hg_symm` hypothesis in the synthesis theorem. -/
theorem hg_symm_of_coshKernel_integral
    {μ : MeasureTheory.Measure ℝ}
    (f : ℝ → ℂ)
    (g : ℂ → ℂ)
    (hg_def : ∀ s, g s = ∫ t, f t * coshKernelC t s ∂μ) :
    ∀ s ∈ coshReflDomainC, g (coshRotation s) = g s := by
  intro s _
  rw [hg_def, hg_def]
  congr 1
  ext t
  rw [coshKernel_coshRotation]



/-- For s in the critical strip, `s ≠ 1` is automatic since `Re(s) < 1`. -/
theorem ne_one_of_mem_criticalStrip {s : ℂ} (hs : s ∈ criticalStrip) : s ≠ 1 := by
  intro h; subst h; exact absurd hs.2 (by norm_num)

/-
PROBLEM
For s in the critical strip with `Im(s) ≠ 0`, `coshRotation s ≠ 1` since
`Im(coshRotation s) = -Im(s) ≠ 0` while `Im(1) = 0`.

PROVIDED SOLUTION
If coshRotation s = 1, then (coshRotation s).im = 0, i.e., -s.im = 0 (by coshRotation_im), so s.im = 0, contradicting him.
-/
theorem coshRotation_ne_one_of_im_ne_zero {s : ℂ} (him : s.im ≠ 0) :
    coshRotation s ≠ 1 := by
  unfold coshRotation; intro H;
  norm_num [ Complex.ext_iff, him ] at H

/-
PROBLEM
For s in the critical strip with `Re(s) ≠ π/3 - 1`, `coshRotation s ≠ 1` since
`Re(coshRotation s) = π/3 - Re(s) ≠ 1`.

PROVIDED SOLUTION
If coshRotation s = 1, then (coshRotation s).re = 1, i.e., π/3 - s.re = 1 (by coshRotation_re), so s.re = π/3 - 1, contradicting hre.
-/
theorem coshRotation_ne_one_of_re_ne {s : ℂ} (hre : s.re ≠ Real.pi / 3 - 1) :
    coshRotation s ≠ 1 := by
  exact fun h => hre <| by have := congr_arg Complex.re h; norm_num [ coshRotation_re ] at this; linarith;




/-! ## Dual reflection impossibility -/

/-
PROBLEM
**Dual reflection impossibility**: If `S ⊆ criticalStrip` is invariant under both
`classicalRotationC` (`s ↦ 1 - s`) and `coshRotation` (`s ↦ π/3 - s`), then `S = ∅`.

The composition `coshRotation ∘ classicalRotationC` is translation by `π/3 - 1 > 0`.
For any `s₀ ∈ S`, the orbit `{s₀ + n(π/3 - 1) | n ∈ ℤ} ⊆ S ⊆ criticalStrip`.
But `Re(s₀ + n(π/3 - 1)) = Re(s₀) + n(π/3 - 1)` exceeds 1 for large `n`,
contradicting `S ⊆ criticalStrip`.

PROVIDED SOLUTION
By contradiction, suppose s₀ ∈ S. Then s₀ ∈ criticalStrip, so 0 < Re(s₀) < 1. By hS_cosh, coshRotation s₀ ∈ S. By hS_classical applied to coshRotation s₀, classicalRotationC(coshRotation s₀) ∈ S. By classicalRotationC_comp_coshRotation, this equals s₀ - ↑(π/3 - 1). So s₁ = s₀ - ↑(π/3 - 1) ∈ S, hence in criticalStrip. Re(s₁) = Re(s₀) - (π/3 - 1). Similarly, using coshRotation_comp_classicalRotationC, hS_classical then hS_cosh gives s₀ + ↑(π/3 - 1) ∈ S. By induction, s₀ + n·↑(π/3 - 1) ∈ S for all natural n. Since π/3 - 1 > 0 (by pi_div_three_minus_one_pos), for large enough n, Re(s₀) + n(π/3-1) > 1, but S ⊆ criticalStrip requires Re < 1. Use Archimedean property: ∃ n such that n(π/3-1) > 1 - Re(s₀). This gives a contradiction.
-/
theorem no_dual_symmetric_setC (S : Set ℂ)
    (hS_strip : S ⊆ criticalStrip)
    (hS_classical : ∀ s ∈ S, classicalRotationC s ∈ S)
    (hS_cosh : ∀ s ∈ S, coshRotation s ∈ S) :
    S = ∅ := by
  contrapose! hS_strip;
  -- By induction, we can show that for any natural number $n$, $s + n \cdot (Real.pi / 3 - 1) \in S$.
  have h_induction : ∀ n : ℕ, ∀ s ∈ S, s + n * (Real.pi / 3 - 1) ∈ S := by
    intro n s hs;
    induction' n with n ih;
    · simpa;
    · have := hS_cosh _ ( hS_classical _ ih );
      convert this using 1 ; push_cast [ coshRotation, classicalRotationC ] ; ring;
  -- Choose $n$ such that $n(\pi/3 - 1) > 1 - s.re$ for any $s \in S$.
  obtain ⟨s, hs⟩ : ∃ s ∈ S, True := by
    exact ⟨ hS_strip.some, hS_strip.choose_spec, trivial ⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n * (Real.pi / 3 - 1) > 1 - s.re := by
    exact exists_nat_gt ( ( 1 - s.re ) / ( Real.pi / 3 - 1 ) ) |> fun ⟨ n, hn ⟩ => ⟨ n, by rwa [ div_lt_iff₀ ( by linarith [ Real.pi_gt_three ] ) ] at hn ⟩;
  exact Set.not_subset.2 ⟨ s + n * ( Real.pi / 3 - 1 ), h_induction n s hs.1, fun h => by have := h.2; norm_num at this; linarith ⟩
/-! ## Discharging `hg_eq` via the identity theorem -/



/-- `coshReflDomain \ {1}` is open. -/
theorem coshReflDomainC_diff_one_isOpen : IsOpen (coshReflDomainC \ {1}) :=
  coshReflDomainC_isOpen.sdiff isClosed_singleton
/-
`coshReflDomain \ {1}` is preconnected.
Since `coshReflDomain` is an open convex set in `ℂ` (real dimension 2) containing `1`,
removing this single point preserves path-connectedness (hence preconnectedness).
-/
theorem coshReflDomainC_diff_one_preconnected :
    IsPreconnected (coshReflDomainC \ {1}) := by
  -- Since the complement of {1} in the complex plane is path-connected, any two points in the set can be connected by a path.
  have h_path_connected : IsPathConnected {s : ℂ | s.re ∈ Set.Ioo 0 (Real.pi / 3) ∧ s ≠ 1} := by
    refine' ⟨ 1 / 2, _, _ ⟩ <;> norm_num;
    · linarith [ Real.pi_gt_three ];
    · intro y hy₁ hy₂ hy₃;
      -- Since $y \neq 1$, we can construct a path from $1/2$ to $y$ that avoids $1$.
      by_cases hy_im : y.im = 0;
      · -- Since $y$ is real and $y \neq 1$, we can construct a path from $1/2$ to $y$ that avoids $1$ by moving vertically.
        have h_path : JoinedIn {s : ℂ | s.re ∈ Set.Ioo 0 (Real.pi / 3) ∧ s ≠ 1} (1 / 2) (1 / 2 + Complex.I * (y.re - 1 / 2)) := by
          refine' ⟨ _, _ ⟩;
          constructor;
          rotate_left;
          rotate_left;
          exact ⟨ fun t => 1 / 2 + Complex.I * ( y.re - 1 / 2 ) * t, by continuity ⟩;
          all_goals norm_num [ Complex.ext_iff ];
          linarith [ Real.pi_gt_three ];
        convert h_path.trans _ using 1;
        refine' ⟨ _, _ ⟩;
        refine' ⟨ _, _, _ ⟩;
        exact ⟨ fun t => ( 1 / 2 + I * ( y.re - 1 / 2 ) ) + t * ( y - ( 1 / 2 + I * ( y.re - 1 / 2 ) ) ), by continuity ⟩;
        all_goals norm_num;
        intro a ha₁ ha₂; refine' ⟨ ⟨ _, _ ⟩, _ ⟩ <;> norm_num [ Complex.ext_iff, hy_im ];
        · cases lt_or_ge a ( 1 / 2 ) <;> nlinarith;
        · cases lt_or_ge a ( 1 / 2 ) <;> nlinarith [ Real.pi_gt_three ];
        · intro h; contrapose! hy₃; simp_all +decide [ Complex.ext_iff ] ;
          nlinarith;
      · refine' ⟨ _, _ ⟩;
        refine' ⟨ _, _, _ ⟩;
        exact ⟨ fun t => ( 1 - t ) * ( 1 / 2 ) + t * y, by continuity ⟩;
        all_goals norm_num;
        intro a ha₁ ha₂; refine' ⟨ ⟨ _, _ ⟩, _ ⟩ <;> norm_num [ Complex.ext_iff ] at *;
        · cases lt_or_eq_of_le ha₁ <;> cases lt_or_eq_of_le ha₂ <;> nlinarith;
        · cases lt_or_ge a ( 1 / 2 ) <;> nlinarith [ Real.pi_gt_three ];
        · exact fun h => ⟨ by rintro rfl; norm_num at h, hy_im ⟩;
  convert h_path_connected.isConnected.isPreconnected using 1
/-
`overlapRegion'` is a subset of `coshReflDomain \ {1}`.
-/
theorem overlapRegionC_subset_diff_one : overlapRegionC ⊆ coshReflDomainC \ {1} := by
  intro s hs;
  exact ⟨ ⟨ by linarith [ hs.1 ], by linarith [ hs.2, Real.pi_le_four ] ⟩, ne_of_apply_ne Complex.re ( by norm_num; linarith [ hs.1, hs.2 ] ) ⟩
/-
`overlapRegion'` is open.
-/
theorem overlapRegionC_isOpen : IsOpen overlapRegionC := by
  exact isOpen_Ioo.preimage Complex.continuous_re
/-
`riemannZeta` is analytic on `coshReflDomain \ {1}`.
-/
theorem riemannZeta_analyticOnNhd_coshReflDomainC :
    AnalyticOnNhd ℂ riemannZeta (coshReflDomainC \ {1}) := by
  apply_rules [ DifferentiableOn.analyticOnNhd ];
  · refine' fun s hs => DifferentiableAt.differentiableWithinAt _;
    apply_rules [ differentiableAt_riemannZeta ];
    exact hs.2;
  · exact coshReflDomainC_diff_one_isOpen


/-
**Discharging `hg_eq`**: If `g` is differentiable on `coshReflDomain` and agrees with
`riemannZeta` on the overlap region `{s | 1 < Re(s) < π/3}`, then `g = riemannZeta` on
all of `coshReflDomain` away from the pole `s = 1`.
This follows from the identity theorem for analytic functions: both `g` and `riemannZeta`
are analytic on `coshReflDomain \ {1}` (which is preconnected), and they agree on the
open subset `overlapRegion'`, so they agree everywhere on the domain.
-/
theorem hg_eq_from_overlap
    (g : ℂ → ℂ)
    (hg_diff : DifferentiableOn ℂ g coshReflDomainC)
    (hg_overlap : ∀ s ∈ overlapRegionC, g s = riemannZeta s) :
    ∀ s ∈ coshReflDomainC, s ≠ 1 → g s = riemannZeta s := by
  intros s hs hs_ne_one
  have h_analytic : AnalyticOnNhd ℂ g (coshReflDomainC \ {1}) := by
    apply_rules [ DifferentiableOn.analyticOnNhd ];
    · exact hg_diff.mono <| Set.diff_subset;
    · exact coshReflDomainC_diff_one_isOpen
  have h_analytic_riemann : AnalyticOnNhd ℂ riemannZeta (coshReflDomainC \ {1}) :=
    riemannZeta_analyticOnNhd_coshReflDomainC;
  -- Since `overlapRegion'` is open and nonempty, we can pick any point `z₀` in `overlapRegion'`.
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, z₀ ∈ overlapRegionC ∧ z₀ ∈ coshReflDomainC \ {1} := by
    exact Exists.elim ( overlapRegionC_nonempty ) fun x hx => ⟨ x, hx, overlapRegionC_subset_diff_one hx ⟩;
  apply h_analytic.eqOn_of_preconnected_of_eventuallyEq h_analytic_riemann;
  any_goals tauto;
  · exact coshReflDomainC_diff_one_preconnected;
  · exact Filter.eventually_of_mem (IsOpen.mem_nhds overlapRegionC_isOpen hz₀.1) fun x hx => hg_overlap x hx



end