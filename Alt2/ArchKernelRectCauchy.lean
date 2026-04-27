import RequestProject.ArchKernelRectCauchyTransport
import RequestProject.WeilWindingIntegral
import RequestProject.WeilRectangleViaSubtraction
import RequestProject.PairTestMellinArchKernelRemainder
import RequestProject.WeilRectangleResidueSum

/-!
# Rectangle Cauchy for `F = archKernel · pairTestMellin β` (finite `T`)

This file specialises the unconditional multi-pole rectangle residue theorem
`ZD.WeilPositivity.Contour.rectResidueTheorem_multi_pole_unconditional`
to the integrand

```
F(s) := archKernel s · pairTestMellin β s
```

over the rectangle `[-1, 2] × [-T, T]` with two interior poles at `s = 0` and
`s = 1`, with residues identified as `-pairTestMellin β 0` and
`gaussianPairDefect β` respectively.

## Status of the rectangle Cauchy step

The unconditional theorem `rectResidueTheorem_multi_pole_unconditional` does
the heavy lifting: it discharges the winding integral and the Cauchy-Goursat
step on the holomorphic remainder. Specialising it here gives a clean,
named, axiom-clean theorem that produces the residue sum

```
2π i · ((-pairTestMellin β 0) + gaussianPairDefect β)
```

once the caller supplies a holomorphic remainder `g` and the integral
linearity hypothesis (these are concrete hypotheses, not new conditional
targets).

## Main results (axiom-clean)

* `pairTestMellin_archKernel_rectContour_residueSum_value` — the value
  `(-pairTestMellin β 0) + gaussianPairDefect β` appearing on the right of the
  rectangle Cauchy identity, packaged as `∑ poleResidue β`.
* `pairTestMellin_archKernel_rectContour_eq_residue_sum_finiteT` — the
  rectangle Cauchy identity at finite `T`, granted the holomorphic remainder
  `g` and the integral linearity hypothesis (both concrete proof obligations,
  not conditional `Prop` placeholders).
* `rectContour_F_right_edge_eq_archIntegrand` — pointwise re-write of the
  right edge as `archIntegrand β 2`.
* `rectContour_F_left_edge_eq_archIntegrand` — pointwise re-write of the
  left edge as `archIntegrand β (-1)`.
-/

noncomputable section

open Filter Topology Complex MeasureTheory Set
open scoped Real

namespace ZD.ArchKernelRectCauchy

open ZD.WeilArchKernelResidues
open ZD.WeilPositivity.Contour
open ZD.ArchKernelRectShift

/-! ## Pole index and per-pole data -/

/-- Pole index for the `F = archKernel · pairTestMellin β` decomposition:
two interior poles at `s = 0` and `s = 1`. -/
abbrev PoleIndex : Type := Fin 2

/-- Location of each pole. -/
def polePoint : PoleIndex → ℂ
  | 0 => 0
  | 1 => 1

/-- Residue value at each pole, exactly the named values from
`pairTestMellin_archKernel_residue_at_zero` and
`pairTestMellin_archKernel_residue_at_one_eq_gaussianPairDefect`. -/
def poleResidue (β : ℝ) : PoleIndex → ℂ
  | 0 => -pairTestMellin β 0
  | 1 => ((gaussianPairDefect β : ℝ) : ℂ)

/-- The sum of pole residues equals the named value
`(-pairTestMellin β 0) + gaussianPairDefect β`. -/
theorem pairTestMellin_archKernel_rectContour_residueSum_value (β : ℝ) :
    (∑ i : PoleIndex, poleResidue β i)
      = (-pairTestMellin β 0) + ((gaussianPairDefect β : ℝ) : ℂ) := by
  rw [Fin.sum_univ_two]
  simp [poleResidue]

/-! ## Rectangle Cauchy identity at finite `T` -/

/-- **Rectangle Cauchy identity for `F = archKernel · pairTestMellin β`
at finite `T`, specialised form.**

Direct application of the unconditional multi-pole residue theorem
`rectResidueTheorem_multi_pole_unconditional` with `poles = {0, 1}`,
`p = polePoint`, `r = poleResidue β`. The right-hand side is the named
value `2π i · ((-pairTestMellin β 0) + gaussianPairDefect β)`.

The hypotheses `g`, `hg_diff`, `h_integral_eq` are concrete proof obligations
required by the underlying `rectResidueTheorem_multi_pole_unconditional`,
not new conditional `Prop` placeholders. -/
theorem pairTestMellin_archKernel_rectContour_eq_residue_sum_finiteT
    (β : ℝ) {T : ℝ} (hT : 0 < T)
    (g : ℂ → ℂ)
    (hg_diff :
      DifferentiableOn ℂ g (Set.uIcc (-1 : ℝ) 2 ×ℂ Set.uIcc (-T) T))
    (h_integral_eq :
      rectContourIntegral (-1 : ℝ) 2 T
          (fun z => ∑ i : PoleIndex, poleResidue β i / (z - polePoint i) + g z) =
        (∑ i : PoleIndex,
          rectContourIntegral (-1 : ℝ) 2 T
            (fun z => poleResidue β i / (z - polePoint i))) +
          rectContourIntegral (-1 : ℝ) 2 T g) :
    rectContourIntegral (-1 : ℝ) 2 T
        (fun z => ∑ i : PoleIndex, poleResidue β i / (z - polePoint i) + g z) =
      2 * ((Real.pi : ℝ) : ℂ) * I *
        ((-pairTestMellin β 0) + ((gaussianPairDefect β : ℝ) : ℂ)) := by
  have hσ : (-1 : ℝ) < 2 := by norm_num
  have hp_re : ∀ i ∈ (Finset.univ : Finset PoleIndex),
      (-1 : ℝ) < (polePoint i).re ∧ (polePoint i).re < 2 := by
    intro i _hi
    fin_cases i
    · refine ⟨?_, ?_⟩ <;> simp [polePoint]
    · refine ⟨?_, ?_⟩ <;> simp [polePoint]
  have hp_im : ∀ i ∈ (Finset.univ : Finset PoleIndex),
      -T < (polePoint i).im ∧ (polePoint i).im < T := by
    intro i _hi
    fin_cases i
    · refine ⟨?_, ?_⟩ <;> simp [polePoint] <;> linarith
    · refine ⟨?_, ?_⟩ <;> simp [polePoint] <;> linarith
  have hmain := rectResidueTheorem_multi_pole_unconditional hσ hT
    (poles := (Finset.univ : Finset PoleIndex))
    (p := polePoint) (r := poleResidue β) (g := g)
    hp_re hp_im hg_diff h_integral_eq
  rw [pairTestMellin_archKernel_rectContour_residueSum_value β] at hmain
  exact hmain

/-! ## Edge identification (axiom-clean) -/

/-- The right edge of the rectangle, integrated against the parameter `y`,
agrees with the integral of `archIntegrand β 2`. -/
theorem rectContour_F_right_edge_eq_archIntegrand (β : ℝ) (T : ℝ) :
    (∫ y : ℝ in (-T : ℝ)..T,
        pairTestMellin_archKernel_product β ((2 : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ in (-T : ℝ)..T, archIntegrand β 2 y := by
  apply intervalIntegral.integral_congr
  intro y _hy
  exact F_eq_archIntegrand_at_two β y

/-- The left edge of the rectangle, integrated against the parameter `y`,
agrees with the integral of `archIntegrand β (-1)`. -/
theorem rectContour_F_left_edge_eq_archIntegrand (β : ℝ) (T : ℝ) :
    (∫ y : ℝ in (-T : ℝ)..T,
        pairTestMellin_archKernel_product β ((-1 : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ in (-T : ℝ)..T, archIntegrand β (-1) y := by
  apply intervalIntegral.integral_congr
  intro y _hy
  exact F_eq_archIntegrand_at_neg_one β y

/-! ## Cycle 2a — Singular part at `s = 0` integrates to `(-M(0)) · 2πi` -/

/-- Helper: rectContourIntegral pulls out a constant scalar. -/
private theorem rectContourIntegral_const_mul (σL σR T : ℝ) (c : ℂ) (f : ℂ → ℂ) :
    rectContourIntegral σL σR T (fun z => c * f z) =
    c * rectContourIntegral σL σR T f := by
  have h1 : (∫ x : ℝ in σL..σR, (fun z => c * f z) (↑x + (-T : ℝ) * I)) =
      c * ∫ x : ℝ in σL..σR, f (↑x + (-T : ℝ) * I) :=
    intervalIntegral.integral_const_mul c (fun x : ℝ => f (↑x + (-T : ℝ) * I))
  have h2 : (∫ x : ℝ in σL..σR, (fun z => c * f z) (↑x + (T : ℝ) * I)) =
      c * ∫ x : ℝ in σL..σR, f (↑x + (T : ℝ) * I) :=
    intervalIntegral.integral_const_mul c (fun x : ℝ => f (↑x + (T : ℝ) * I))
  have h3 : (∫ y : ℝ in (-T : ℝ)..T, (fun z => c * f z) (↑σR + ↑y * I)) =
      c * ∫ y : ℝ in (-T : ℝ)..T, f (↑σR + ↑y * I) :=
    intervalIntegral.integral_const_mul c (fun y : ℝ => f (↑σR + ↑y * I))
  have h4 : (∫ y : ℝ in (-T : ℝ)..T, (fun z => c * f z) (↑σL + ↑y * I)) =
      c * ∫ y : ℝ in (-T : ℝ)..T, f (↑σL + ↑y * I) :=
    intervalIntegral.integral_const_mul c (fun y : ℝ => f (↑σL + ↑y * I))
  unfold rectContourIntegral
  rw [h1, h2, h3, h4]
  simp only [smul_eq_mul]; ring

/-- Helper: closed-form value of `∮ (-M(0))/z` over the rectangle `[-1,2]×[-T,T]`. -/
theorem rectContourIntegral_singular_at_zero (β : ℝ) {T : ℝ} (hT : 0 < T) :
    rectContourIntegral (-1 : ℝ) 2 T
        (fun z => (-ZD.WeilPositivity.Contour.pairTestMellin β 0) / z) =
      (-ZD.WeilPositivity.Contour.pairTestMellin β 0) * (2 * (Real.pi : ℂ) * I) := by
  set c : ℂ := -ZD.WeilPositivity.Contour.pairTestMellin β 0 with hc_def
  have h_eq : (fun z : ℂ => c / z) = fun z => c * (z - 0)⁻¹ := by
    ext z; rw [sub_zero, div_eq_mul_inv]
  rw [h_eq]
  rw [rectContourIntegral_const_mul]
  have h_p_re : (-1 : ℝ) < (0 : ℂ).re ∧ (0 : ℂ).re < 2 := by
    rw [Complex.zero_re]; exact ⟨by norm_num, by norm_num⟩
  have h_p_im : -T < (0 : ℂ).im ∧ (0 : ℂ).im < T := by
    rw [Complex.zero_im]; exact ⟨by linarith, hT⟩
  rw [rectContourIntegral_inv_center_eq_twoPiI_holds (-1 : ℝ) 2 T
    (by norm_num : (-1 : ℝ) < 2) hT (0 : ℂ) h_p_re h_p_im]

/-! ## Cycle 2b — Singular part at `s = 1` integrates to `M(1) · 2πi` -/

/-- Helper: closed-form value of `∮ M(1)/(z-1)` over the rectangle `[-1,2]×[-T,T]`,
where `M(1) = pairTestMellin β 1 = gaussianPairDefect β`. -/
theorem rectContourIntegral_singular_at_one (β : ℝ) {T : ℝ} (hT : 0 < T) :
    rectContourIntegral (-1 : ℝ) 2 T
        (fun z => ((ZD.gaussianPairDefect β : ℝ) : ℂ) / (z - 1)) =
      ((ZD.gaussianPairDefect β : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
  set c : ℂ := ((ZD.gaussianPairDefect β : ℝ) : ℂ) with hc_def
  have h_eq : (fun z : ℂ => c / (z - 1)) = fun z => c * (z - 1)⁻¹ := by
    ext z; rw [div_eq_mul_inv]
  rw [h_eq]
  rw [rectContourIntegral_const_mul]
  have h_p_re : (-1 : ℝ) < (1 : ℂ).re ∧ (1 : ℂ).re < 2 := by
    rw [Complex.one_re]; exact ⟨by norm_num, by norm_num⟩
  have h_p_im : -T < (1 : ℂ).im ∧ (1 : ℂ).im < T := by
    rw [Complex.one_im]; exact ⟨by linarith, hT⟩
  rw [rectContourIntegral_inv_center_eq_twoPiI_holds (-1 : ℝ) 2 T
    (by norm_num : (-1 : ℝ) < 2) hT (1 : ℂ) h_p_re h_p_im]

/-! ## Cycle 2c — Combined singular part `S = S₀ + S₁` -/

/-- The combined singular part of `F = archKernel · pairTestMellin β` at the two
poles `s = 0` and `s = 1`. -/
noncomputable def singularPart (β : ℝ) (z : ℂ) : ℂ :=
  (-ZD.WeilPositivity.Contour.pairTestMellin β 0) / z +
  ((ZD.gaussianPairDefect β : ℝ) : ℂ) / (z - 1)

/-- `singularPart β` is integrable on every edge of the rectangle `[-1,2]×[-T,T]`
provided `T > 0`. Helper: produce edge-wise interval integrability via continuity. -/
private theorem singularPart_pieces_integrable (β : ℝ) {T : ℝ} (hT : 0 < T) :
    True := trivial  -- placeholder; we work integrability inline below.

/-- `∮ singularPart = ∮ S₀ + ∮ S₁` via `rectContourIntegral_add` plus continuity-based
integrability of each summand on each edge of the rectangle. -/
theorem rectContourIntegral_singularPart_split (β : ℝ) {T : ℝ} (hT : 0 < T) :
    rectContourIntegral (-1 : ℝ) 2 T (singularPart β) =
      rectContourIntegral (-1 : ℝ) 2 T
        (fun z => (-ZD.WeilPositivity.Contour.pairTestMellin β 0) / z) +
      rectContourIntegral (-1 : ℝ) 2 T
        (fun z => ((ZD.gaussianPairDefect β : ℝ) : ℂ) / (z - 1)) := by
  have h_unfold : (fun z : ℂ => singularPart β z) =
      fun z => (-ZD.WeilPositivity.Contour.pairTestMellin β 0) / z +
               ((ZD.gaussianPairDefect β : ℝ) : ℂ) / (z - 1) := rfl
  -- Build integrability witnesses for each piece on each edge.
  set f₁ : ℂ → ℂ := fun z => (-ZD.WeilPositivity.Contour.pairTestMellin β 0) / z
    with hf₁_def
  set f₂ : ℂ → ℂ := fun z => ((ZD.gaussianPairDefect β : ℝ) : ℂ) / (z - 1)
    with hf₂_def
  -- f₁ continuous on {z ≠ 0}, f₂ continuous on {z ≠ 1}.
  have hf₁_contOn : ContinuousOn f₁ {z : ℂ | z ≠ 0} :=
    continuousOn_const.div continuousOn_id (fun z hz => hz)
  have hf₂_contOn : ContinuousOn f₂ {z : ℂ | z ≠ 1} :=
    continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      (fun z hz => sub_ne_zero.mpr hz)
  -- Edges avoid both poles when T > 0.
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT
  have hT_neg_ne : (-T : ℝ) ≠ 0 := by linarith
  have h_im_ne_zero_z_ne_zero : ∀ x y : ℝ, y ≠ 0 →
      (((x : ℂ) + (y : ℂ) * I) ≠ 0 ∧ ((x : ℂ) + (y : ℂ) * I) ≠ 1) := by
    intro x y hy
    constructor
    · intro h
      have him : ((x : ℂ) + (y : ℂ) * I).im = 0 := by rw [h]; simp
      simp at him; exact hy him
    · intro h
      have him : ((x : ℂ) + (y : ℂ) * I).im = 0 := by rw [h]; simp
      simp at him; exact hy him
  have h_re_neg_one_z_ne : ∀ y : ℝ,
      ((-1 : ℂ) + (y : ℂ) * I) ≠ 0 ∧ ((-1 : ℂ) + (y : ℂ) * I) ≠ 1 := by
    intro y
    constructor
    · intro h
      have hre : ((-1 : ℂ) + (y : ℂ) * I).re = 0 := by rw [h]; simp
      simp at hre
    · intro h
      have hre : ((-1 : ℂ) + (y : ℂ) * I).re = 1 := by rw [h]; simp
      simp at hre; linarith
  have h_re_two_z_ne : ∀ y : ℝ,
      ((2 : ℂ) + (y : ℂ) * I) ≠ 0 ∧ ((2 : ℂ) + (y : ℂ) * I) ≠ 1 := by
    intro y
    constructor
    · intro h
      have hre : ((2 : ℂ) + (y : ℂ) * I).re = 0 := by rw [h]; simp
      simp at hre
    · intro h
      have hre : ((2 : ℂ) + (y : ℂ) * I).re = 1 := by rw [h]; simp
      simp at hre
  -- Per-edge integrability for f₁.
  have hf₁_b : IntervalIntegrable (fun x : ℝ => f₁ ((x : ℂ) + (-T : ℝ) * I))
      MeasureTheory.volume (-1) 2 :=
    (hf₁_contOn.comp' (by fun_prop) fun x _hx => by
      simp only [Set.mem_setOf_eq]
      exact (h_im_ne_zero_z_ne_zero x (-T) hT_neg_ne).1).intervalIntegrable
  have hf₁_t : IntervalIntegrable (fun x : ℝ => f₁ ((x : ℂ) + (T : ℝ) * I))
      MeasureTheory.volume (-1) 2 :=
    (hf₁_contOn.comp' (by fun_prop) fun x _hx => by
      simp only [Set.mem_setOf_eq]
      exact (h_im_ne_zero_z_ne_zero x T hT_ne).1).intervalIntegrable
  have hf₁_r : IntervalIntegrable (fun y : ℝ => f₁ ((2 : ℝ) + (y : ℝ) * I))
      MeasureTheory.volume (-T) T :=
    (hf₁_contOn.comp' (by fun_prop) fun y _hy => by
      simp only [Set.mem_setOf_eq]
      exact (h_re_two_z_ne y).1).intervalIntegrable
  have hf₁_l : IntervalIntegrable (fun y : ℝ => f₁ ((-1 : ℝ) + (y : ℝ) * I))
      MeasureTheory.volume (-T) T :=
    (hf₁_contOn.comp' (by fun_prop) fun y _hy => by
      simp only [Set.mem_setOf_eq]
      have := (h_re_neg_one_z_ne y).1; push_cast at this ⊢; exact this).intervalIntegrable
  -- Per-edge integrability for f₂.
  have hf₂_b : IntervalIntegrable (fun x : ℝ => f₂ ((x : ℂ) + (-T : ℝ) * I))
      MeasureTheory.volume (-1) 2 :=
    (hf₂_contOn.comp' (by fun_prop) fun x _hx => by
      simp only [Set.mem_setOf_eq]
      exact (h_im_ne_zero_z_ne_zero x (-T) hT_neg_ne).2).intervalIntegrable
  have hf₂_t : IntervalIntegrable (fun x : ℝ => f₂ ((x : ℂ) + (T : ℝ) * I))
      MeasureTheory.volume (-1) 2 :=
    (hf₂_contOn.comp' (by fun_prop) fun x _hx => by
      simp only [Set.mem_setOf_eq]
      exact (h_im_ne_zero_z_ne_zero x T hT_ne).2).intervalIntegrable
  have hf₂_r : IntervalIntegrable (fun y : ℝ => f₂ ((2 : ℝ) + (y : ℝ) * I))
      MeasureTheory.volume (-T) T :=
    (hf₂_contOn.comp' (by fun_prop) fun y _hy => by
      simp only [Set.mem_setOf_eq]
      exact (h_re_two_z_ne y).2).intervalIntegrable
  have hf₂_l : IntervalIntegrable (fun y : ℝ => f₂ ((-1 : ℝ) + (y : ℝ) * I))
      MeasureTheory.volume (-T) T :=
    (hf₂_contOn.comp' (by fun_prop) fun y _hy => by
      simp only [Set.mem_setOf_eq]
      have := (h_re_neg_one_z_ne y).2; push_cast at this ⊢; exact this).intervalIntegrable
  -- Apply rectContourIntegral_add.
  have h_add := ZD.WeilPositivity.Contour.rectContourIntegral_add (-1 : ℝ) 2 T f₁ f₂
    hf₁_b hf₂_b hf₁_t hf₂_t hf₁_r hf₂_r hf₁_l hf₂_l
  exact h_add

/-- **Cycle 2c result.** `∮ singularPart β = 2πi · ((-M(0)) + M(1))`. -/
theorem rectContourIntegral_singularPart_value (β : ℝ) {T : ℝ} (hT : 0 < T) :
    rectContourIntegral (-1 : ℝ) 2 T (singularPart β) =
      2 * (Real.pi : ℂ) * I *
        ((-ZD.WeilPositivity.Contour.pairTestMellin β 0) +
          ((ZD.gaussianPairDefect β : ℝ) : ℂ)) := by
  rw [rectContourIntegral_singularPart_split β hT,
    rectContourIntegral_singular_at_zero β hT,
    rectContourIntegral_singular_at_one β hT]
  ring

/-! ## Cycle 2d — `∮ F = ∮ singularPart + ∮ F_remainder` -/

/-- Helper: edge-wise congruence for rectangle contour integrals. -/
private theorem rectContourIntegral_congr_edges
    {σL σR T : ℝ} {f g : ℂ → ℂ}
    (h_b : ∀ x ∈ Set.uIcc σL σR, f (↑x + (-T : ℝ) * I) = g (↑x + (-T : ℝ) * I))
    (h_t : ∀ x ∈ Set.uIcc σL σR, f (↑x + (T : ℝ) * I) = g (↑x + (T : ℝ) * I))
    (h_r : ∀ y ∈ Set.uIcc (-T) T, f (↑σR + ↑y * I) = g (↑σR + ↑y * I))
    (h_l : ∀ y ∈ Set.uIcc (-T) T, f (↑σL + ↑y * I) = g (↑σL + ↑y * I)) :
    rectContourIntegral σL σR T f = rectContourIntegral σL σR T g := by
  unfold rectContourIntegral
  rw [intervalIntegral.integral_congr fun x hx => h_b x hx]
  rw [intervalIntegral.integral_congr fun x hx => h_t x hx]
  rw [intervalIntegral.integral_congr fun y hy => h_r y hy]
  rw [intervalIntegral.integral_congr fun y hy => h_l y hy]

/-- **Cycle 2d.**  The rectangle contour integral of `F = archKernel · pairTestMellin β`
splits as `∮ singularPart β + ∮ F_remainder β`. -/
theorem F_rectContourIntegral_eq_singularPart_plus_remainder
    (β : ℝ) {T : ℝ} (hT : 0 < T) :
    rectContourIntegral (-1 : ℝ) 2 T
        (ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β) =
      rectContourIntegral (-1 : ℝ) 2 T (singularPart β) +
      rectContourIntegral (-1 : ℝ) 2 T
        (ZD.PairTestMellinArchKernelRemainder.F_remainder β) := by
  -- Helper: pointwise F(z) = singularPart β z + F_remainder β z for z off the poles.
  have h_pt_eq : ∀ z : ℂ, z ≠ 0 → z ≠ 1 →
      ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β z =
      singularPart β z + ZD.PairTestMellinArchKernelRemainder.F_remainder β z := by
    intro z hz0 hz1
    have h_decomp :=
      ZD.PairTestMellinArchKernelRemainder.F_eq_singular_plus_remainder β z hz0 hz1
    unfold ZD.ArchKernelRectShift.pairTestMellin_archKernel_product
    rw [h_decomp]; unfold singularPart; ring
  -- Edge points avoid {0, 1}: adapt the exact patterns from rectContourIntegral_singularPart_split.
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT
  have hTn_ne : (-T : ℝ) ≠ 0 := by linarith
  -- Horizontal edges: imaginary part ≠ 0 excludes both poles.
  have h_im_ne_aux : ∀ (x t : ℝ), t ≠ 0 →
      ((x : ℂ) + (t : ℂ) * I) ≠ 0 ∧ ((x : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro x t ht
    have him : ((x : ℂ) + (t : ℂ) * I).im = t := by simp
    constructor
    · intro h; have := congrArg Complex.im h; simp at this; exact ht this
    · intro h; have := congrArg Complex.im h; simp at this; exact ht this
  -- Right vertical edge (re = 2 ≠ 0, 1).
  have h_re_two_ne : ∀ (y : ℝ),
      ((2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 ∧ ((2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 1 := by
    intro y
    constructor
    · intro h
      have hre : (((2 : ℝ) : ℂ) + (y : ℂ) * I).re = 0 := by rw [h]; simp
      simp at hre
    · intro h
      have hre : (((2 : ℝ) : ℂ) + (y : ℂ) * I).re = 1 := by rw [h]; simp
      simp at hre
  -- Left vertical edge (re = -1 ≠ 0, 1).
  have h_re_neg_one_ne : ∀ (y : ℝ),
      ((-1 : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 ∧ ((-1 : ℝ) : ℂ) + (y : ℂ) * I ≠ 1 := by
    intro y
    constructor
    · intro h
      have hre : (((-1 : ℝ) : ℂ) + (y : ℂ) * I).re = 0 := by rw [h]; simp
      simp at hre
    · intro h
      have hre : (((-1 : ℝ) : ℂ) + (y : ℂ) * I).re = 1 := by rw [h]; simp
      simp at hre; linarith
  -- Congr rewrite: F agrees with singularPart + F_remainder on all four edges.
  rw [rectContourIntegral_congr_edges
    (f := ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β)
    (g := fun z => singularPart β z + ZD.PairTestMellinArchKernelRemainder.F_remainder β z)]
  · -- After the rw, prove the sum splits.
    -- Build integrability of singularPart on each edge (copied from rectContourIntegral_singularPart_split).
    have hf_sp_contOn : ContinuousOn (singularPart β) {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
      unfold singularPart
      apply ContinuousOn.add
      · exact continuousOn_const.div continuousOn_id (fun z hz => hz.1)
      · exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
          (fun z hz => sub_ne_zero.mpr hz.2)
    have hf_sp_b : IntervalIntegrable
        (fun x : ℝ => singularPart β ((x : ℂ) + (-T : ℝ) * I))
        MeasureTheory.volume (-1) 2 :=
      (hf_sp_contOn.comp' (by fun_prop) fun x _hx => by
        simp only [Set.mem_setOf_eq]
        exact h_im_ne_aux x (-T) hTn_ne).intervalIntegrable
    have hf_sp_t : IntervalIntegrable
        (fun x : ℝ => singularPart β ((x : ℂ) + (T : ℝ) * I))
        MeasureTheory.volume (-1) 2 :=
      (hf_sp_contOn.comp' (by fun_prop) fun x _hx => by
        simp only [Set.mem_setOf_eq]
        exact h_im_ne_aux x T hT_ne).intervalIntegrable
    have hf_sp_r : IntervalIntegrable
        (fun y : ℝ => singularPart β ((2 : ℝ) + (y : ℂ) * I))
        MeasureTheory.volume (-T) T :=
      (hf_sp_contOn.comp' (by fun_prop) fun y _hy => by
        simp only [Set.mem_setOf_eq]; exact h_re_two_ne y).intervalIntegrable
    have hf_sp_l : IntervalIntegrable
        (fun y : ℝ => singularPart β ((-1 : ℝ) + (y : ℂ) * I))
        MeasureTheory.volume (-T) T :=
      (hf_sp_contOn.comp' (by fun_prop) fun y _hy => by
        simp only [Set.mem_setOf_eq]; exact h_re_neg_one_ne y).intervalIntegrable
    -- Build integrability of F_remainder on each edge via continuity on the closed rectangle.
    have hFr_contOn : ContinuousOn (ZD.PairTestMellinArchKernelRemainder.F_remainder β)
        (Set.uIcc (-1 : ℝ) 2 ×ℂ Set.uIcc (-T) T) :=
      (ZD.PairTestMellinArchKernelRemainder.F_remainder_differentiableOn β T hT).continuousOn
    have hFr_b : IntervalIntegrable
        (fun x : ℝ => ZD.PairTestMellinArchKernelRemainder.F_remainder β
            ((x : ℂ) + (-T : ℝ) * I))
        MeasureTheory.volume (-1) 2 :=
      (hFr_contOn.comp' (by fun_prop) fun x hx => by
        simp only [Complex.mem_reProdIm]
        refine ⟨by simpa using hx, ?_⟩
        simp [Set.uIcc_comm]).intervalIntegrable
    have hFr_t : IntervalIntegrable
        (fun x : ℝ => ZD.PairTestMellinArchKernelRemainder.F_remainder β
            ((x : ℂ) + (T : ℝ) * I))
        MeasureTheory.volume (-1) 2 :=
      (hFr_contOn.comp' (by fun_prop) fun x hx => by
        simp only [Complex.mem_reProdIm]
        refine ⟨by simpa using hx, ?_⟩
        simp [Set.right_mem_uIcc]).intervalIntegrable
    have hFr_r : IntervalIntegrable
        (fun y : ℝ => ZD.PairTestMellinArchKernelRemainder.F_remainder β
            ((2 : ℝ) + (y : ℂ) * I))
        MeasureTheory.volume (-T) T :=
      (hFr_contOn.comp' (by fun_prop) fun y hy => by
        simp only [Complex.mem_reProdIm]
        refine ⟨?_, by simpa using hy⟩
        simp [Set.right_mem_uIcc]).intervalIntegrable
    have hFr_l : IntervalIntegrable
        (fun y : ℝ => ZD.PairTestMellinArchKernelRemainder.F_remainder β
            ((-1 : ℝ) + (y : ℂ) * I))
        MeasureTheory.volume (-T) T :=
      (hFr_contOn.comp' (by fun_prop) fun y hy => by
        simp only [Complex.mem_reProdIm]
        refine ⟨?_, by simpa using hy⟩
        simp [Set.left_mem_uIcc]).intervalIntegrable
    exact ZD.WeilPositivity.Contour.rectContourIntegral_add (-1 : ℝ) 2 T
      (singularPart β) (ZD.PairTestMellinArchKernelRemainder.F_remainder β)
      hf_sp_b hFr_b hf_sp_t hFr_t hf_sp_r hFr_r hf_sp_l hFr_l
  · -- Bottom edge congr.
    intro x _; exact h_pt_eq _ (h_im_ne_aux x (-T) hTn_ne).1 (h_im_ne_aux x (-T) hTn_ne).2
  · -- Top edge congr.
    intro x _; exact h_pt_eq _ (h_im_ne_aux x T hT_ne).1 (h_im_ne_aux x T hT_ne).2
  · -- Right edge congr.
    intro y _; exact h_pt_eq _ (h_re_two_ne y).1 (h_re_two_ne y).2
  · -- Left edge congr.
    intro y _; exact h_pt_eq _ (h_re_neg_one_ne y).1 (h_re_neg_one_ne y).2

/-! ## Cycle 2e — Final value theorem -/

/-- **Cycle 2e.**  The rectangle contour integral of `F = archKernel · pairTestMellin β`
equals `2πi · ((-pairTestMellin β 0) + gaussianPairDefect β)`. -/
theorem F_rectContourIntegral_value (β : ℝ) {T : ℝ} (hT : 0 < T) :
    rectContourIntegral (-1 : ℝ) 2 T
        (ZD.ArchKernelRectShift.pairTestMellin_archKernel_product β) =
      2 * (Real.pi : ℂ) * I *
        ((-ZD.WeilPositivity.Contour.pairTestMellin β 0) +
          ((ZD.gaussianPairDefect β : ℝ) : ℂ)) := by
  rw [F_rectContourIntegral_eq_singularPart_plus_remainder β hT,
    rectContourIntegral_singularPart_value β hT,
    ZD.PairTestMellinArchKernelRemainder.F_remainder_rectContourIntegral_zero β hT]
  ring

end ZD.ArchKernelRectCauchy

/-! ## Axiom checks -/

#print axioms ZD.ArchKernelRectCauchy.pairTestMellin_archKernel_rectContour_residueSum_value
#print axioms ZD.ArchKernelRectCauchy.pairTestMellin_archKernel_rectContour_eq_residue_sum_finiteT
#print axioms ZD.ArchKernelRectCauchy.rectContour_F_right_edge_eq_archIntegrand
#print axioms ZD.ArchKernelRectCauchy.rectContour_F_left_edge_eq_archIntegrand
#print axioms ZD.ArchKernelRectCauchy.rectContourIntegral_singularPart_split
#print axioms ZD.ArchKernelRectCauchy.rectContourIntegral_singularPart_value
#print axioms ZD.ArchKernelRectCauchy.F_rectContourIntegral_eq_singularPart_plus_remainder
#print axioms ZD.ArchKernelRectCauchy.F_rectContourIntegral_value

end
