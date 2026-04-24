import Mathlib
import RequestProject.WeilHadamardRectangleDecomposition
import RequestProject.WeilRectangleResidueSum
import RequestProject.WeilWindingIntegral

/-!
# Hadamard-kernel rectangle residue sum

This file packages the finite-pole residue theorem for the decomposition built
in `WeilHadamardRectangleDecomposition.lean`.
-/

open Complex Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

/-- Pole index for the hadamard-kernel decomposition:
nontrivial zeros from `Z`, plus the pole at `1`, plus the self-pole at `s`. -/
abbrev HadamardPoleIndex (Z : Finset ℂ) :=
  Sum {ρ : ℂ // ρ ∈ Z} (Fin 2)

/-- Location of each pole in the hadamard-kernel decomposition. -/
def hadamardPolePoint {Z : Finset ℂ} (s : ℂ) : HadamardPoleIndex Z → ℂ
  | Sum.inl ρ => ρ.1
  | Sum.inr i => if i = 0 then 1 else s

/-- Residue coefficient of each pole in the hadamard-kernel decomposition. -/
def hadamardPoleResidue {Z : Finset ℂ} (s : ℂ) : HadamardPoleIndex Z → ℂ
  | Sum.inl ρ => -hadamardZeroCoeff s ρ.1
  | Sum.inr i => if i = 0 then hadamardOneCoeff s else hadamardSelfCoeff s

/-- The explicit polar sum appearing in the hadamard-kernel rectangle
decomposition. -/
def hadamardPoleSum (s : ℂ) (Z : Finset ℂ) (z : ℂ) : ℂ :=
  ∑ i : HadamardPoleIndex Z, hadamardPoleResidue s i / (z - hadamardPolePoint s i)

private theorem hadamardPoleSum_eq_explicit {s z : ℂ} {Z : Finset ℂ} :
    hadamardPoleSum s Z z =
      (∑ ρ ∈ Z, -hadamardZeroCoeff s ρ / (z - ρ)) +
        hadamardOneCoeff s / (z - 1) +
        hadamardSelfCoeff s / (z - s) := by
  unfold hadamardPoleSum hadamardPoleResidue hadamardPolePoint
  rw [Fintype.sum_sum_type]
  change (∑ a₁ : {ρ : ℂ // ρ ∈ Z}, -hadamardZeroCoeff s a₁.1 / (z - a₁.1)) +
      ∑ a₂ : Fin 2, (if a₂ = 0 then hadamardOneCoeff s else hadamardSelfCoeff s) /
        (z - if a₂ = 0 then 1 else s) =
    (∑ ρ ∈ Z, -hadamardZeroCoeff s ρ / (z - ρ)) +
      hadamardOneCoeff s / (z - 1) +
      hadamardSelfCoeff s / (z - s)
  rw [← Z.sum_attach (fun ρ => -hadamardZeroCoeff s ρ / (z - ρ))]
  rw [Fin.sum_univ_two]
  simp [Fin.isValue]
  ring

private theorem hadamardPoleResidue_sum_eq_explicit {s : ℂ} {Z : Finset ℂ} :
    (∑ i : HadamardPoleIndex Z, hadamardPoleResidue s i) =
      (∑ ρ ∈ Z, -hadamardZeroCoeff s ρ) + hadamardOneCoeff s + hadamardSelfCoeff s := by
  unfold hadamardPoleResidue
  rw [Fintype.sum_sum_type]
  change (∑ a₁ : {ρ : ℂ // ρ ∈ Z}, -hadamardZeroCoeff s a₁.1) +
      ∑ a₂ : Fin 2, (if a₂ = 0 then hadamardOneCoeff s else hadamardSelfCoeff s) =
    (∑ ρ ∈ Z, -hadamardZeroCoeff s ρ) + hadamardOneCoeff s + hadamardSelfCoeff s
  rw [← Z.sum_attach (fun ρ => -hadamardZeroCoeff s ρ)]
  rw [Fin.sum_univ_two]
  simp [Fin.isValue]
  ring

private theorem hadamardOneCoeff_eq (s : ℂ) :
    hadamardOneCoeff s = 1 / (s - 1) + 1 := by
  simp [hadamardOneCoeff, hadamardKernel]

private theorem rectContourIntegral_congr
    {σL σR T : ℝ} {f g : ℂ → ℂ}
    (h_bottom : ∀ x ∈ Set.uIcc σL σR, f (↑x + (-T : ℝ) * I) = g (↑x + (-T : ℝ) * I))
    (h_top : ∀ x ∈ Set.uIcc σL σR, f (↑x + (T : ℝ) * I) = g (↑x + (T : ℝ) * I))
    (h_right : ∀ y ∈ Set.uIcc (-T) T, f (↑σR + ↑y * I) = g (↑σR + ↑y * I))
    (h_left : ∀ y ∈ Set.uIcc (-T) T, f (↑σL + ↑y * I) = g (↑σL + ↑y * I)) :
    rectContourIntegral σL σR T f = rectContourIntegral σL σR T g := by
  unfold rectContourIntegral
  rw [intervalIntegral.integral_congr fun x hx => h_bottom x hx]
  rw [intervalIntegral.integral_congr fun x hx => h_top x hx]
  rw [intervalIntegral.integral_congr fun y hy => h_right y hy]
  rw [intervalIntegral.integral_congr fun y hy => h_left y hy]

private theorem bottom_edge_intervalIntegrable_of_continuousOn_rect
    {σL σR T : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)) :
    IntervalIntegrable (fun x : ℝ => f (↑x + (-T : ℝ) * I)) MeasureTheory.volume σL σR := by
  apply ContinuousOn.intervalIntegrable
  refine hf.comp ?_ ?_
  · fun_prop
  · intro x hx
    constructor
    · simpa using hx
    · simp

private theorem top_edge_intervalIntegrable_of_continuousOn_rect
    {σL σR T : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)) :
    IntervalIntegrable (fun x : ℝ => f (↑x + (T : ℝ) * I)) MeasureTheory.volume σL σR := by
  apply ContinuousOn.intervalIntegrable
  refine hf.comp ?_ ?_
  · fun_prop
  · intro x hx
    constructor
    · simpa using hx
    · simp

private theorem right_edge_intervalIntegrable_of_continuousOn_rect
    {σL σR T : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)) :
    IntervalIntegrable (fun y : ℝ => f (↑σR + ↑y * I)) MeasureTheory.volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  refine hf.comp ?_ ?_
  · fun_prop
  · intro y hy
    constructor
    · simp
    · simpa using hy

private theorem left_edge_intervalIntegrable_of_continuousOn_rect
    {σL σR T : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T)) :
    IntervalIntegrable (fun y : ℝ => f (↑σL + ↑y * I)) MeasureTheory.volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  refine hf.comp ?_ ?_
  · fun_prop
  · intro y hy
    constructor
    · simp
    · simpa using hy

private theorem bottom_edge_intervalIntegrable_pole
    {σL σR T : ℝ} (r p : ℂ) (hp_im : -T < p.im) :
    IntervalIntegrable (fun x : ℝ => r / ((x : ℂ) + (-T : ℝ) * I - p))
      MeasureTheory.volume σL σR := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
  · fun_prop
  · intro x _ hx0
    have him : (((x : ℂ) + (-T : ℝ) * I - p).im : ℝ) = -T - p.im := by simp
    rw [hx0] at him
    simp at him
    linarith

private theorem top_edge_intervalIntegrable_pole
    {σL σR T : ℝ} (r p : ℂ) (hp_im : p.im < T) :
    IntervalIntegrable (fun x : ℝ => r / ((x : ℂ) + (T : ℝ) * I - p))
      MeasureTheory.volume σL σR := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
  · fun_prop
  · intro x _ hx0
    have him : (((x : ℂ) + (T : ℝ) * I - p).im : ℝ) = T - p.im := by simp
    rw [hx0] at him
    simp at him
    linarith

private theorem right_edge_intervalIntegrable_pole
    {σR T : ℝ} (r p : ℂ) (hp_re : p.re < σR) :
    IntervalIntegrable (fun y : ℝ => r / ((σR : ℂ) + (y : ℂ) * I - p))
      MeasureTheory.volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
  · fun_prop
  · intro y _ hy0
    have hre : (((σR : ℂ) + (y : ℂ) * I - p).re : ℝ) = σR - p.re := by simp
    rw [hy0] at hre
    simp at hre
    linarith

private theorem left_edge_intervalIntegrable_pole
    {σL T : ℝ} (r p : ℂ) (hp_re : σL < p.re) :
    IntervalIntegrable (fun y : ℝ => r / ((σL : ℂ) + (y : ℂ) * I - p))
      MeasureTheory.volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
  · fun_prop
  · intro y _ hy0
    have hre : (((σL : ℂ) + (y : ℂ) * I - p).re : ℝ) = σL - p.re := by simp
    rw [hy0] at hre
    simp at hre
    linarith

private theorem hadamard_decomp_eq_at_point
    {s z : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    (hzZ : z ∉ Z) (hz1 : z ≠ 1) (hzs : z ≠ s) :
    weilIntegrand (hadamardKernel s) z =
      hadamardPoleSum s Z z + hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ z := by
  rw [weilIntegrand_hadamardKernel_eq_polar_plus_global hs0 hs1 hsζ hZ hzZ hz1 hzs]
  rw [← hadamardPoleSum_eq_explicit]

/-- Rectangle residue sum for the hadamard-kernel pole decomposition. This is a
thin wrapper around `rectResidueTheorem_multi_pole_unconditional`. -/
theorem rectContourIntegral_hadamardPoleSum_eq_residue_sum
    {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    {σL σR T : ℝ} (hσ : σL < σR) (hT : 0 < T) (hσL : 0 < σL)
    (h_one_re : σL < 1 ∧ (1 : ℂ).re < σR)
    (hs_re : σL < s.re ∧ s.re < σR)
    (hs_im : -T < s.im ∧ s.im < T)
    (hρ_re : ∀ ρ ∈ Z, σL < ρ.re ∧ ρ.re < σR)
    (hρ_im : ∀ ρ ∈ Z, -T < ρ.im ∧ ρ.im < T)
    (hζ_ne_off_Z :
      ∀ z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T),
        z ≠ 1 → z ∉ Z → riemannZeta z ≠ 0)
    (h_integral_eq :
      rectContourIntegral σL σR T
          (fun z => hadamardPoleSum s Z z + hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ z) =
        (∑ i : HadamardPoleIndex Z,
          rectContourIntegral σL σR T
            (fun z => hadamardPoleResidue s i / (z - hadamardPolePoint s i))) +
          rectContourIntegral σL σR T (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ)) :
    rectContourIntegral σL σR T
        (fun z => hadamardPoleSum s Z z + hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ z) =
      2 * ↑Real.pi * I *
        ((∑ ρ ∈ Z, -hadamardZeroCoeff s ρ) + hadamardOneCoeff s + hadamardSelfCoeff s) := by
  have hg_diff :
      DifferentiableOn ℂ (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ)
        (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) :=
    hadamardRemainderGlobal_differentiableOn_rect hs0 hs1 hsζ hZ σL σR T hσ.le hσL hζ_ne_off_Z
  have hp_re :
      ∀ i ∈ (Finset.univ : Finset (HadamardPoleIndex Z)),
        σL < (hadamardPolePoint s i).re ∧ (hadamardPolePoint s i).re < σR := by
    intro i _hi
    cases i with
    | inl ρ =>
        simpa [hadamardPolePoint] using hρ_re ρ.1 ρ.2
    | inr i =>
        fin_cases i
        · simpa [hadamardPolePoint] using h_one_re
        · simpa [hadamardPolePoint] using hs_re
  have hp_im :
      ∀ i ∈ (Finset.univ : Finset (HadamardPoleIndex Z)),
        -T < (hadamardPolePoint s i).im ∧ (hadamardPolePoint s i).im < T := by
    intro i _hi
    cases i with
    | inl ρ =>
        simpa [hadamardPolePoint] using hρ_im ρ.1 ρ.2
    | inr i =>
        fin_cases i
        · have h_one_im : -T < (1 : ℂ).im ∧ (1 : ℂ).im < T := by
            simp
            linarith [hT]
          simpa [hadamardPolePoint] using h_one_im
        · simpa [hadamardPolePoint] using hs_im
  have hmain := rectResidueTheorem_multi_pole_unconditional hσ hT
    (poles := (Finset.univ : Finset (HadamardPoleIndex Z)))
    (p := hadamardPolePoint s) (r := hadamardPoleResidue s)
    (g := hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ)
    hp_re hp_im hg_diff h_integral_eq
  rw [hadamardPoleResidue_sum_eq_explicit] at hmain
  exact hmain

/-- Rectangle contour of `weilIntegrand (hadamardKernel s)` equals the residue
sum, once the decomposition equality on the boundary is supplied. -/
theorem rectContourIntegral_weilIntegrand_hadamardKernel_eq_residue_sum
    {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    {σL σR T : ℝ} (hσ : σL < σR) (hT : 0 < T) (hσL : 0 < σL)
    (h_one_re : σL < 1 ∧ (1 : ℂ).re < σR)
    (hs_re : σL < s.re ∧ s.re < σR)
    (hs_im : -T < s.im ∧ s.im < T)
    (hρ_re : ∀ ρ ∈ Z, σL < ρ.re ∧ ρ.re < σR)
    (hρ_im : ∀ ρ ∈ Z, -T < ρ.im ∧ ρ.im < T)
    (hζ_ne_off_Z :
      ∀ z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T),
        z ≠ 1 → z ∉ Z → riemannZeta z ≠ 0)
    (h_f_eq_decomp :
      rectContourIntegral σL σR T (weilIntegrand (hadamardKernel s)) =
        rectContourIntegral σL σR T
          (fun z => hadamardPoleSum s Z z + hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ z))
    (h_integral_eq :
      rectContourIntegral σL σR T
          (fun z => hadamardPoleSum s Z z + hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ z) =
        (∑ i : HadamardPoleIndex Z,
          rectContourIntegral σL σR T
            (fun z => hadamardPoleResidue s i / (z - hadamardPolePoint s i))) +
          rectContourIntegral σL σR T (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ)) :
    rectContourIntegral σL σR T (weilIntegrand (hadamardKernel s)) =
      2 * ↑Real.pi * I *
        ((∑ ρ ∈ Z, -hadamardZeroCoeff s ρ) + hadamardOneCoeff s + hadamardSelfCoeff s) := by
  rw [h_f_eq_decomp]
  exact rectContourIntegral_hadamardPoleSum_eq_residue_sum hs0 hs1 hsζ hZ
    hσ hT hσL h_one_re hs_re hs_im hρ_re hρ_im hζ_ne_off_Z h_integral_eq

/-- Rectangle contour of `weilIntegrand (hadamardKernel s)` equals the residue
sum once every pole is strictly interior, with no extra boundary or linearity
hypotheses. -/
theorem rectContourIntegral_weilIntegrand_hadamardKernel_eq_residue_sum_of_interior_poles
    {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    {σL σR T : ℝ} (hσ : σL < σR) (hT : 0 < T) (hσL : 0 < σL)
    (h_one_re : σL < 1 ∧ (1 : ℂ).re < σR)
    (hs_re : σL < s.re ∧ s.re < σR)
    (hs_im : -T < s.im ∧ s.im < T)
    (hρ_re : ∀ ρ ∈ Z, σL < ρ.re ∧ ρ.re < σR)
    (hρ_im : ∀ ρ ∈ Z, -T < ρ.im ∧ ρ.im < T)
    (hζ_ne_off_Z :
      ∀ z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T),
        z ≠ 1 → z ∉ Z → riemannZeta z ≠ 0) :
    rectContourIntegral σL σR T (weilIntegrand (hadamardKernel s)) =
      2 * ↑Real.pi * I *
        ((∑ ρ ∈ Z, -hadamardZeroCoeff s ρ) + hadamardOneCoeff s + hadamardSelfCoeff s) := by
  have hrem_diff :
      DifferentiableOn ℂ (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ)
        (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) :=
    hadamardRemainderGlobal_differentiableOn_rect hs0 hs1 hsζ hZ σL σR T hσ.le hσL hζ_ne_off_Z
  have hrem_cont :
      ContinuousOn (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ)
        (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) :=
    hrem_diff.continuousOn
  have hp_re :
      ∀ i ∈ (Finset.univ : Finset (HadamardPoleIndex Z)),
        σL < (hadamardPolePoint s i).re ∧ (hadamardPolePoint s i).re < σR := by
    intro i _hi
    cases i with
    | inl ρ =>
        simpa [hadamardPolePoint] using hρ_re ρ.1 ρ.2
    | inr i =>
        fin_cases i
        · simpa [hadamardPolePoint] using h_one_re
        · simpa [hadamardPolePoint] using hs_re
  have hp_im :
      ∀ i ∈ (Finset.univ : Finset (HadamardPoleIndex Z)),
        -T < (hadamardPolePoint s i).im ∧ (hadamardPolePoint s i).im < T := by
    intro i _hi
    cases i with
    | inl ρ =>
        simpa [hadamardPolePoint] using hρ_im ρ.1 ρ.2
    | inr i =>
        fin_cases i
        · have h_one_im : -T < (1 : ℂ).im ∧ (1 : ℂ).im < T := by
            simp
            linarith [hT]
          simpa [hadamardPolePoint] using h_one_im
        · simpa [hadamardPolePoint] using hs_im
  have hrem_b :
      IntervalIntegrable (fun x : ℝ =>
        hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ (↑x + (-T : ℝ) * I))
        MeasureTheory.volume σL σR :=
    bottom_edge_intervalIntegrable_of_continuousOn_rect hrem_cont
  have hrem_t :
      IntervalIntegrable (fun x : ℝ =>
        hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ (↑x + (T : ℝ) * I))
        MeasureTheory.volume σL σR :=
    top_edge_intervalIntegrable_of_continuousOn_rect hrem_cont
  have hrem_r :
      IntervalIntegrable (fun y : ℝ =>
        hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ (↑σR + ↑y * I))
        MeasureTheory.volume (-T) T :=
    right_edge_intervalIntegrable_of_continuousOn_rect hrem_cont
  have hrem_l :
      IntervalIntegrable (fun y : ℝ =>
        hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ (↑σL + ↑y * I))
        MeasureTheory.volume (-T) T :=
    left_edge_intervalIntegrable_of_continuousOn_rect hrem_cont
  have h_pole_b :
      ∀ i ∈ (Finset.univ : Finset (HadamardPoleIndex Z)),
        IntervalIntegrable
          (fun x : ℝ =>
            hadamardPoleResidue s i / ((x : ℂ) + (-T : ℝ) * I - hadamardPolePoint s i))
          MeasureTheory.volume σL σR := by
    intro i hi
    exact bottom_edge_intervalIntegrable_pole (hadamardPoleResidue s i) (hadamardPolePoint s i)
      (hp_im i hi).1
  have h_pole_t :
      ∀ i ∈ (Finset.univ : Finset (HadamardPoleIndex Z)),
        IntervalIntegrable
          (fun x : ℝ =>
            hadamardPoleResidue s i / ((x : ℂ) + (T : ℝ) * I - hadamardPolePoint s i))
          MeasureTheory.volume σL σR := by
    intro i hi
    exact top_edge_intervalIntegrable_pole (hadamardPoleResidue s i) (hadamardPolePoint s i)
      (hp_im i hi).2
  have h_pole_r :
      ∀ i ∈ (Finset.univ : Finset (HadamardPoleIndex Z)),
        IntervalIntegrable
          (fun y : ℝ =>
            hadamardPoleResidue s i / ((σR : ℂ) + (y : ℂ) * I - hadamardPolePoint s i))
          MeasureTheory.volume (-T) T := by
    intro i hi
    exact right_edge_intervalIntegrable_pole (hadamardPoleResidue s i) (hadamardPolePoint s i)
      (hp_re i hi).2
  have h_pole_l :
      ∀ i ∈ (Finset.univ : Finset (HadamardPoleIndex Z)),
        IntervalIntegrable
          (fun y : ℝ =>
            hadamardPoleResidue s i / ((σL : ℂ) + (y : ℂ) * I - hadamardPolePoint s i))
          MeasureTheory.volume (-T) T := by
    intro i hi
    exact left_edge_intervalIntegrable_pole (hadamardPoleResidue s i) (hadamardPolePoint s i)
      (hp_re i hi).1
  have hsum_b :
      IntervalIntegrable (fun x : ℝ => hadamardPoleSum s Z (↑x + (-T : ℝ) * I))
        MeasureTheory.volume σL σR := by
    classical
    let F : HadamardPoleIndex Z → ℝ → ℂ := fun i x =>
      hadamardPoleResidue s i / ((x : ℂ) + (-T : ℝ) * I - hadamardPolePoint s i)
    have hsum :
        ∀ t : Finset (HadamardPoleIndex Z),
          IntervalIntegrable (fun x : ℝ => Finset.sum t (fun i => F i x))
            MeasureTheory.volume σL σR := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · simp [F]
      · intro i t hi ih
        simpa [F, hi, Finset.sum_insert] using IntervalIntegrable.add (h_pole_b i (by simp)) ih
    simpa [hadamardPoleSum, F] using hsum (Finset.univ : Finset (HadamardPoleIndex Z))
  have hsum_t :
      IntervalIntegrable (fun x : ℝ => hadamardPoleSum s Z (↑x + (T : ℝ) * I))
        MeasureTheory.volume σL σR := by
    classical
    let F : HadamardPoleIndex Z → ℝ → ℂ := fun i x =>
      hadamardPoleResidue s i / ((x : ℂ) + (T : ℝ) * I - hadamardPolePoint s i)
    have hsum :
        ∀ t : Finset (HadamardPoleIndex Z),
          IntervalIntegrable (fun x : ℝ => Finset.sum t (fun i => F i x))
            MeasureTheory.volume σL σR := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · simp [F]
      · intro i t hi ih
        simpa [F, hi, Finset.sum_insert] using IntervalIntegrable.add (h_pole_t i (by simp)) ih
    simpa [hadamardPoleSum, F] using hsum (Finset.univ : Finset (HadamardPoleIndex Z))
  have hsum_r :
      IntervalIntegrable (fun y : ℝ => hadamardPoleSum s Z (↑σR + ↑y * I))
        MeasureTheory.volume (-T) T := by
    classical
    let F : HadamardPoleIndex Z → ℝ → ℂ := fun i y =>
      hadamardPoleResidue s i / ((σR : ℂ) + (y : ℂ) * I - hadamardPolePoint s i)
    have hsum :
        ∀ t : Finset (HadamardPoleIndex Z),
          IntervalIntegrable (fun y : ℝ => Finset.sum t (fun i => F i y))
            MeasureTheory.volume (-T) T := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · simp [F]
      · intro i t hi ih
        simpa [F, hi, Finset.sum_insert] using IntervalIntegrable.add (h_pole_r i (by simp)) ih
    simpa [hadamardPoleSum, F] using hsum (Finset.univ : Finset (HadamardPoleIndex Z))
  have hsum_l :
      IntervalIntegrable (fun y : ℝ => hadamardPoleSum s Z (↑σL + ↑y * I))
        MeasureTheory.volume (-T) T := by
    classical
    let F : HadamardPoleIndex Z → ℝ → ℂ := fun i y =>
      hadamardPoleResidue s i / ((σL : ℂ) + (y : ℂ) * I - hadamardPolePoint s i)
    have hsum :
        ∀ t : Finset (HadamardPoleIndex Z),
          IntervalIntegrable (fun y : ℝ => Finset.sum t (fun i => F i y))
            MeasureTheory.volume (-T) T := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · simp [F]
      · intro i t hi ih
        simpa [F, hi, Finset.sum_insert] using IntervalIntegrable.add (h_pole_l i (by simp)) ih
    simpa [hadamardPoleSum, F] using hsum (Finset.univ : Finset (HadamardPoleIndex Z))
  have h_pole_sum_eq :
      rectContourIntegral σL σR T (hadamardPoleSum s Z) =
        ∑ i : HadamardPoleIndex Z,
          rectContourIntegral σL σR T
            (fun z => hadamardPoleResidue s i / (z - hadamardPolePoint s i)) := by
    unfold hadamardPoleSum
    simpa using rectContourIntegral_finset_sum σL σR T (Finset.univ : Finset (HadamardPoleIndex Z))
      (fun i z => hadamardPoleResidue s i / (z - hadamardPolePoint s i))
      h_pole_b h_pole_t h_pole_r h_pole_l
  have h_integral_eq :
      rectContourIntegral σL σR T
          (fun z => hadamardPoleSum s Z z + hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ z) =
        (∑ i : HadamardPoleIndex Z,
          rectContourIntegral σL σR T
            (fun z => hadamardPoleResidue s i / (z - hadamardPolePoint s i))) +
          rectContourIntegral σL σR T (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ) := by
    calc
      rectContourIntegral σL σR T
          (fun z => hadamardPoleSum s Z z + hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ z) =
          rectContourIntegral σL σR T (hadamardPoleSum s Z) +
            rectContourIntegral σL σR T (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ) := by
              exact rectContourIntegral_add σL σR T (hadamardPoleSum s Z)
                (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ)
                hsum_b hrem_b hsum_t hrem_t hsum_r hrem_r hsum_l hrem_l
      _ =
          (∑ i : HadamardPoleIndex Z,
            rectContourIntegral σL σR T
              (fun z => hadamardPoleResidue s i / (z - hadamardPolePoint s i))) +
            rectContourIntegral σL σR T (hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ) := by
              rw [h_pole_sum_eq]
  have h_f_eq_decomp :
      rectContourIntegral σL σR T (weilIntegrand (hadamardKernel s)) =
        rectContourIntegral σL σR T
          (fun z => hadamardPoleSum s Z z + hadamardRemainderGlobal s Z hs0 hs1 hsζ hZ z) := by
    apply rectContourIntegral_congr
    · intro x hx
      have hzZ : ((x : ℂ) + (-T : ℝ) * I) ∉ Z := by
        intro hzZ
        have hρ := hρ_im ((x : ℂ) + (-T : ℝ) * I) hzZ
        simp at hρ
      have hz1 : ((x : ℂ) + (-T : ℝ) * I) ≠ 1 := by
        intro hz1
        have him : (-T : ℝ) = 0 := by simpa using congrArg Complex.im hz1
        linarith [hT]
      have hzs : ((x : ℂ) + (-T : ℝ) * I) ≠ s := by
        intro hxs
        have him : (-T : ℝ) = s.im := by simpa using congrArg Complex.im hxs
        linarith [hs_im.1]
      exact hadamard_decomp_eq_at_point hs0 hs1 hsζ hZ hzZ hz1 hzs
    · intro x hx
      have hzZ : ((x : ℂ) + (T : ℝ) * I) ∉ Z := by
        intro hzZ
        have hρ := hρ_im ((x : ℂ) + (T : ℝ) * I) hzZ
        simp at hρ
      have hz1 : ((x : ℂ) + (T : ℝ) * I) ≠ 1 := by
        intro hz1
        have him : (T : ℝ) = 0 := by simpa using congrArg Complex.im hz1
        linarith [hT]
      have hzs : ((x : ℂ) + (T : ℝ) * I) ≠ s := by
        intro hxs
        have him : (T : ℝ) = s.im := by simpa using congrArg Complex.im hxs
        linarith [hs_im.2]
      exact hadamard_decomp_eq_at_point hs0 hs1 hsζ hZ hzZ hz1 hzs
    · intro y hy
      have hzZ : ((σR : ℂ) + (y : ℂ) * I) ∉ Z := by
        intro hzZ
        have hρ := hρ_re ((σR : ℂ) + (y : ℂ) * I) hzZ
        simp at hρ
      have hz1 : ((σR : ℂ) + (y : ℂ) * I) ≠ 1 := by
        intro hz1
        have hre : (σR : ℝ) = 1 := by simpa using congrArg Complex.re hz1
        have hσR1 : (1 : ℝ) < σR := by simpa using h_one_re.2
        linarith
      have hzs : ((σR : ℂ) + (y : ℂ) * I) ≠ s := by
        intro hys
        have hre : (σR : ℝ) = s.re := by simpa using congrArg Complex.re hys
        linarith [hs_re.2]
      exact hadamard_decomp_eq_at_point hs0 hs1 hsζ hZ hzZ hz1 hzs
    · intro y hy
      have hzZ : ((σL : ℂ) + (y : ℂ) * I) ∉ Z := by
        intro hzZ
        have hρ := hρ_re ((σL : ℂ) + (y : ℂ) * I) hzZ
        simp at hρ
      have hz1 : ((σL : ℂ) + (y : ℂ) * I) ≠ 1 := by
        intro hz1
        have hre : (σL : ℝ) = 1 := by simpa using congrArg Complex.re hz1
        have hσL1 : σL < (1 : ℝ) := by simpa using h_one_re.1
        linarith
      have hzs : ((σL : ℂ) + (y : ℂ) * I) ≠ s := by
        intro hys
        have hre : (σL : ℝ) = s.re := by simpa using congrArg Complex.re hys
        linarith [hs_re.1]
      exact hadamard_decomp_eq_at_point hs0 hs1 hsζ hZ hzZ hz1 hzs
  exact rectContourIntegral_weilIntegrand_hadamardKernel_eq_residue_sum hs0 hs1 hsζ hZ
    hσ hT hσL h_one_re hs_re hs_im hρ_re hρ_im hζ_ne_off_Z h_f_eq_decomp h_integral_eq

/-- Zero-free rectangle specialization of the Hadamard-kernel residue sum. -/
theorem rectContourIntegral_weilIntegrand_hadamardKernel_eq_residue_sum_zero_free
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    {σL σR T : ℝ} (hσ : σL < σR) (hT : 0 < T) (hσL : 0 < σL)
    (h_one_re : σL < 1 ∧ (1 : ℂ).re < σR)
    (hs_re : σL < s.re ∧ s.re < σR)
    (hs_im : -T < s.im ∧ s.im < T)
    (hζ_ne_rect :
      ∀ z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T), z ≠ 1 → riemannZeta z ≠ 0) :
    rectContourIntegral σL σR T (weilIntegrand (hadamardKernel s)) =
      2 * ↑Real.pi * I * (hadamardOneCoeff s + hadamardSelfCoeff s) := by
  have hζ_ne_off_empty :
      ∀ z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T),
        z ≠ 1 → z ∉ (∅ : Finset ℂ) → riemannZeta z ≠ 0 := by
    intro z hz hz1 _hz
    exact hζ_ne_rect z hz hz1
  simpa using
    (rectContourIntegral_weilIntegrand_hadamardKernel_eq_residue_sum_of_interior_poles
      (Z := ∅) hs0 hs1 hsζ
      (by intro ρ hρ; simp at hρ) hσ hT hσL h_one_re hs_re hs_im
      (by intro ρ hρ; simp at hρ)
      (by intro ρ hρ; simp at hρ)
      hζ_ne_off_empty)

/-- Explicit zero-free rectangle specialization, with the pole-at-one term
expanded as `1 / (s - 1) + 1`. -/
theorem rectContourIntegral_weilIntegrand_hadamardKernel_eq_residue_sum_zero_free_explicit
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    {σL σR T : ℝ} (hσ : σL < σR) (hT : 0 < T) (hσL : 0 < σL)
    (h_one_re : σL < 1 ∧ (1 : ℂ).re < σR)
    (hs_re : σL < s.re ∧ s.re < σR)
    (hs_im : -T < s.im ∧ s.im < T)
    (hζ_ne_rect :
      ∀ z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T), z ≠ 1 → riemannZeta z ≠ 0) :
    rectContourIntegral σL σR T (weilIntegrand (hadamardKernel s)) =
      2 * ↑Real.pi * I * (deriv riemannZeta s / riemannZeta s + 1 / (s - 1) + 1) := by
  rw [rectContourIntegral_weilIntegrand_hadamardKernel_eq_residue_sum_zero_free hs0 hs1 hsζ
    hσ hT hσL h_one_re hs_re hs_im hζ_ne_rect]
  rw [hadamardOneCoeff_eq, hadamardSelfCoeff]
  ring

/-- Pole index for the Hadamard-kernel decomposition when the rectangle also
contains the kernel pole at `z = 0`. -/
abbrev HadamardPoleIndexWithOrigin (Z : Finset ℂ) :=
  Sum {ρ : ℂ // ρ ∈ Z} (Fin 3)

/-- Location of each pole when the rectangle contains `0`, `1`, and `s`. -/
def hadamardPolePointWithOrigin {Z : Finset ℂ} (s : ℂ) :
    HadamardPoleIndexWithOrigin Z → ℂ
  | Sum.inl ρ => ρ.1
  | Sum.inr i => if i = 0 then 0 else if i = 1 then 1 else s

/-- Residue coefficient of each pole when the rectangle contains `0`, `1`, and
`s`. -/
def hadamardPoleResidueWithOrigin {Z : Finset ℂ} (s : ℂ) :
    HadamardPoleIndexWithOrigin Z → ℂ
  | Sum.inl ρ => -hadamardZeroCoeff s ρ.1
  | Sum.inr i =>
      if i = 0 then hadamardOriginCoeff else if i = 1 then hadamardOneCoeff s else hadamardSelfCoeff s

/-- The explicit polar sum for the origin-containing rectangle decomposition. -/
def hadamardPoleSumWithOrigin (s : ℂ) (Z : Finset ℂ) (z : ℂ) : ℂ :=
  ∑ i : HadamardPoleIndexWithOrigin Z,
    hadamardPoleResidueWithOrigin s i / (z - hadamardPolePointWithOrigin s i)

private theorem hadamardPoleSumWithOrigin_eq_explicit {s z : ℂ} {Z : Finset ℂ} :
    hadamardPoleSumWithOrigin s Z z =
      hadamardOriginCoeff / z +
        (∑ ρ ∈ Z, -hadamardZeroCoeff s ρ / (z - ρ)) +
        hadamardOneCoeff s / (z - 1) +
        hadamardSelfCoeff s / (z - s) := by
  unfold hadamardPoleSumWithOrigin hadamardPoleResidueWithOrigin hadamardPolePointWithOrigin
  rw [Fintype.sum_sum_type]
  change (∑ a₁ : {ρ : ℂ // ρ ∈ Z}, -hadamardZeroCoeff s a₁.1 / (z - a₁.1)) +
      ∑ a₂ : Fin 3,
        (if a₂ = 0 then hadamardOriginCoeff else if a₂ = 1 then hadamardOneCoeff s
          else hadamardSelfCoeff s) /
          (z - if a₂ = 0 then 0 else if a₂ = 1 then 1 else s) =
    hadamardOriginCoeff / z +
      (∑ ρ ∈ Z, -hadamardZeroCoeff s ρ / (z - ρ)) +
      hadamardOneCoeff s / (z - 1) +
      hadamardSelfCoeff s / (z - s)
  rw [← Z.sum_attach (fun ρ => -hadamardZeroCoeff s ρ / (z - ρ))]
  rw [Fin.sum_univ_three]
  simp [Fin.isValue]
  ring

private theorem hadamardPoleResidueWithOrigin_sum_eq_explicit {s : ℂ} {Z : Finset ℂ} :
    (∑ i : HadamardPoleIndexWithOrigin Z, hadamardPoleResidueWithOrigin s i) =
      hadamardOriginCoeff + (∑ ρ ∈ Z, -hadamardZeroCoeff s ρ) +
        hadamardOneCoeff s + hadamardSelfCoeff s := by
  unfold hadamardPoleResidueWithOrigin
  rw [Fintype.sum_sum_type]
  change (∑ a₁ : {ρ : ℂ // ρ ∈ Z}, -hadamardZeroCoeff s a₁.1) +
      ∑ a₂ : Fin 3,
        (if a₂ = 0 then hadamardOriginCoeff else if a₂ = 1 then hadamardOneCoeff s
          else hadamardSelfCoeff s) =
    hadamardOriginCoeff + (∑ ρ ∈ Z, -hadamardZeroCoeff s ρ) +
      hadamardOneCoeff s + hadamardSelfCoeff s
  rw [← Z.sum_attach (fun ρ => -hadamardZeroCoeff s ρ)]
  rw [Fin.sum_univ_three]
  simp [Fin.isValue]
  ring

private theorem hadamard_decomp_with_origin_eq_at_point
    {s z : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    (hz0 : z ≠ 0) (hzZ : z ∉ Z) (hz1 : z ≠ 1) (hzs : z ≠ s) :
    weilIntegrand (hadamardKernel s) z =
      hadamardPoleSumWithOrigin s Z z +
        hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ z := by
  rw [weilIntegrand_hadamardKernel_eq_polar_plus_origin_global hs0 hs1 hsζ hZ hz0 hzZ hz1 hzs]
  rw [← hadamardPoleSumWithOrigin_eq_explicit]

/-- Rectangle contour of `weilIntegrand (hadamardKernel s)` when the rectangle
contains the additional pole at `z = 0`. -/
theorem rectContourIntegral_weilIntegrand_hadamardKernel_eq_residue_sum_with_origin_of_interior_poles
    {s : ℂ} {Z : Finset ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ NontrivialZeros)
    {σL σR T : ℝ} (hσ : σL < σR) (hT : 0 < T)
    (h_zero_re : σL < (0 : ℂ).re ∧ (0 : ℂ).re < σR)
    (h_one_re : σL < 1 ∧ (1 : ℂ).re < σR)
    (hs_re : σL < s.re ∧ s.re < σR)
    (hs_im : -T < s.im ∧ s.im < T)
    (hρ_re : ∀ ρ ∈ Z, σL < ρ.re ∧ ρ.re < σR)
    (hρ_im : ∀ ρ ∈ Z, -T < ρ.im ∧ ρ.im < T)
    (hζ_ne_off_Z :
      ∀ z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T),
        z ≠ 1 → z ∉ Z → riemannZeta z ≠ 0) :
    rectContourIntegral σL σR T (weilIntegrand (hadamardKernel s)) =
      2 * ↑Real.pi * I *
        (hadamardOriginCoeff + (∑ ρ ∈ Z, -hadamardZeroCoeff s ρ) +
          hadamardOneCoeff s + hadamardSelfCoeff s) := by
  have hrem_diff :
      DifferentiableOn ℂ (hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ)
        (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) :=
    hadamardRemainderWithOriginGlobal_differentiableOn_rect hs0 hs1 hsζ hZ σL σR T hσ.le
      hζ_ne_off_Z
  have hrem_cont :
      ContinuousOn (hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ)
        (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) :=
    hrem_diff.continuousOn
  have hp_re :
      ∀ i ∈ (Finset.univ : Finset (HadamardPoleIndexWithOrigin Z)),
        σL < (hadamardPolePointWithOrigin s i).re ∧ (hadamardPolePointWithOrigin s i).re < σR := by
    intro i _hi
    cases i with
    | inl ρ =>
        simpa [hadamardPolePointWithOrigin] using hρ_re ρ.1 ρ.2
    | inr i =>
        fin_cases i
        · simpa [hadamardPolePointWithOrigin] using h_zero_re
        · simpa [hadamardPolePointWithOrigin] using h_one_re
        · simpa [hadamardPolePointWithOrigin] using hs_re
  have hp_im :
      ∀ i ∈ (Finset.univ : Finset (HadamardPoleIndexWithOrigin Z)),
        -T < (hadamardPolePointWithOrigin s i).im ∧ (hadamardPolePointWithOrigin s i).im < T := by
    intro i _hi
    cases i with
    | inl ρ =>
        simpa [hadamardPolePointWithOrigin] using hρ_im ρ.1 ρ.2
    | inr i =>
        fin_cases i
        · have h_zero_im : -T < (0 : ℂ).im ∧ (0 : ℂ).im < T := by
            simp
            linarith [hT]
          simpa [hadamardPolePointWithOrigin] using h_zero_im
        · have h_one_im : -T < (1 : ℂ).im ∧ (1 : ℂ).im < T := by
            simp
            linarith [hT]
          simpa [hadamardPolePointWithOrigin] using h_one_im
        · simpa [hadamardPolePointWithOrigin] using hs_im
  have hrem_b :
      IntervalIntegrable (fun x : ℝ =>
        hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ (↑x + (-T : ℝ) * I))
        MeasureTheory.volume σL σR :=
    bottom_edge_intervalIntegrable_of_continuousOn_rect hrem_cont
  have hrem_t :
      IntervalIntegrable (fun x : ℝ =>
        hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ (↑x + (T : ℝ) * I))
        MeasureTheory.volume σL σR :=
    top_edge_intervalIntegrable_of_continuousOn_rect hrem_cont
  have hrem_r :
      IntervalIntegrable (fun y : ℝ =>
        hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ (↑σR + ↑y * I))
        MeasureTheory.volume (-T) T :=
    right_edge_intervalIntegrable_of_continuousOn_rect hrem_cont
  have hrem_l :
      IntervalIntegrable (fun y : ℝ =>
        hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ (↑σL + ↑y * I))
        MeasureTheory.volume (-T) T :=
    left_edge_intervalIntegrable_of_continuousOn_rect hrem_cont
  have h_pole_b :
      ∀ i ∈ (Finset.univ : Finset (HadamardPoleIndexWithOrigin Z)),
        IntervalIntegrable
          (fun x : ℝ =>
            hadamardPoleResidueWithOrigin s i /
              ((x : ℂ) + (-T : ℝ) * I - hadamardPolePointWithOrigin s i))
          MeasureTheory.volume σL σR := by
    intro i hi
    exact bottom_edge_intervalIntegrable_pole (hadamardPoleResidueWithOrigin s i)
      (hadamardPolePointWithOrigin s i) (hp_im i hi).1
  have h_pole_t :
      ∀ i ∈ (Finset.univ : Finset (HadamardPoleIndexWithOrigin Z)),
        IntervalIntegrable
          (fun x : ℝ =>
            hadamardPoleResidueWithOrigin s i /
              ((x : ℂ) + (T : ℝ) * I - hadamardPolePointWithOrigin s i))
          MeasureTheory.volume σL σR := by
    intro i hi
    exact top_edge_intervalIntegrable_pole (hadamardPoleResidueWithOrigin s i)
      (hadamardPolePointWithOrigin s i) (hp_im i hi).2
  have h_pole_r :
      ∀ i ∈ (Finset.univ : Finset (HadamardPoleIndexWithOrigin Z)),
        IntervalIntegrable
          (fun y : ℝ =>
            hadamardPoleResidueWithOrigin s i /
              ((σR : ℂ) + (y : ℂ) * I - hadamardPolePointWithOrigin s i))
          MeasureTheory.volume (-T) T := by
    intro i hi
    exact right_edge_intervalIntegrable_pole (hadamardPoleResidueWithOrigin s i)
      (hadamardPolePointWithOrigin s i) (hp_re i hi).2
  have h_pole_l :
      ∀ i ∈ (Finset.univ : Finset (HadamardPoleIndexWithOrigin Z)),
        IntervalIntegrable
          (fun y : ℝ =>
            hadamardPoleResidueWithOrigin s i /
              ((σL : ℂ) + (y : ℂ) * I - hadamardPolePointWithOrigin s i))
          MeasureTheory.volume (-T) T := by
    intro i hi
    exact left_edge_intervalIntegrable_pole (hadamardPoleResidueWithOrigin s i)
      (hadamardPolePointWithOrigin s i) (hp_re i hi).1
  have hsum_b :
      IntervalIntegrable (fun x : ℝ => hadamardPoleSumWithOrigin s Z (↑x + (-T : ℝ) * I))
        MeasureTheory.volume σL σR := by
    classical
    let F : HadamardPoleIndexWithOrigin Z → ℝ → ℂ := fun i x =>
      hadamardPoleResidueWithOrigin s i /
        ((x : ℂ) + (-T : ℝ) * I - hadamardPolePointWithOrigin s i)
    have hsum :
        ∀ t : Finset (HadamardPoleIndexWithOrigin Z),
          IntervalIntegrable (fun x : ℝ => Finset.sum t (fun i => F i x))
            MeasureTheory.volume σL σR := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · simp [F]
      · intro i t hi ih
        simpa [F, hi, Finset.sum_insert] using IntervalIntegrable.add (h_pole_b i (by simp)) ih
    simpa [hadamardPoleSumWithOrigin, F] using
      hsum (Finset.univ : Finset (HadamardPoleIndexWithOrigin Z))
  have hsum_t :
      IntervalIntegrable (fun x : ℝ => hadamardPoleSumWithOrigin s Z (↑x + (T : ℝ) * I))
        MeasureTheory.volume σL σR := by
    classical
    let F : HadamardPoleIndexWithOrigin Z → ℝ → ℂ := fun i x =>
      hadamardPoleResidueWithOrigin s i /
        ((x : ℂ) + (T : ℝ) * I - hadamardPolePointWithOrigin s i)
    have hsum :
        ∀ t : Finset (HadamardPoleIndexWithOrigin Z),
          IntervalIntegrable (fun x : ℝ => Finset.sum t (fun i => F i x))
            MeasureTheory.volume σL σR := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · simp [F]
      · intro i t hi ih
        simpa [F, hi, Finset.sum_insert] using IntervalIntegrable.add (h_pole_t i (by simp)) ih
    simpa [hadamardPoleSumWithOrigin, F] using
      hsum (Finset.univ : Finset (HadamardPoleIndexWithOrigin Z))
  have hsum_r :
      IntervalIntegrable (fun y : ℝ => hadamardPoleSumWithOrigin s Z (↑σR + ↑y * I))
        MeasureTheory.volume (-T) T := by
    classical
    let F : HadamardPoleIndexWithOrigin Z → ℝ → ℂ := fun i y =>
      hadamardPoleResidueWithOrigin s i /
        ((σR : ℂ) + (y : ℂ) * I - hadamardPolePointWithOrigin s i)
    have hsum :
        ∀ t : Finset (HadamardPoleIndexWithOrigin Z),
          IntervalIntegrable (fun y : ℝ => Finset.sum t (fun i => F i y))
            MeasureTheory.volume (-T) T := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · simp [F]
      · intro i t hi ih
        simpa [F, hi, Finset.sum_insert] using IntervalIntegrable.add (h_pole_r i (by simp)) ih
    simpa [hadamardPoleSumWithOrigin, F] using
      hsum (Finset.univ : Finset (HadamardPoleIndexWithOrigin Z))
  have hsum_l :
      IntervalIntegrable (fun y : ℝ => hadamardPoleSumWithOrigin s Z (↑σL + ↑y * I))
        MeasureTheory.volume (-T) T := by
    classical
    let F : HadamardPoleIndexWithOrigin Z → ℝ → ℂ := fun i y =>
      hadamardPoleResidueWithOrigin s i /
        ((σL : ℂ) + (y : ℂ) * I - hadamardPolePointWithOrigin s i)
    have hsum :
        ∀ t : Finset (HadamardPoleIndexWithOrigin Z),
          IntervalIntegrable (fun y : ℝ => Finset.sum t (fun i => F i y))
            MeasureTheory.volume (-T) T := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · simp [F]
      · intro i t hi ih
        simpa [F, hi, Finset.sum_insert] using IntervalIntegrable.add (h_pole_l i (by simp)) ih
    simpa [hadamardPoleSumWithOrigin, F] using
      hsum (Finset.univ : Finset (HadamardPoleIndexWithOrigin Z))
  have h_pole_sum_eq :
      rectContourIntegral σL σR T (hadamardPoleSumWithOrigin s Z) =
        ∑ i : HadamardPoleIndexWithOrigin Z,
          rectContourIntegral σL σR T
            (fun z => hadamardPoleResidueWithOrigin s i /
              (z - hadamardPolePointWithOrigin s i)) := by
    unfold hadamardPoleSumWithOrigin
    simpa using rectContourIntegral_finset_sum σL σR T
      (Finset.univ : Finset (HadamardPoleIndexWithOrigin Z))
      (fun i z => hadamardPoleResidueWithOrigin s i / (z - hadamardPolePointWithOrigin s i))
      h_pole_b h_pole_t h_pole_r h_pole_l
  have h_integral_eq :
      rectContourIntegral σL σR T
          (fun z =>
            hadamardPoleSumWithOrigin s Z z +
              hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ z) =
        (∑ i : HadamardPoleIndexWithOrigin Z,
          rectContourIntegral σL σR T
            (fun z => hadamardPoleResidueWithOrigin s i /
              (z - hadamardPolePointWithOrigin s i))) +
          rectContourIntegral σL σR T
            (hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ) := by
    calc
      rectContourIntegral σL σR T
          (fun z =>
            hadamardPoleSumWithOrigin s Z z +
              hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ z) =
          rectContourIntegral σL σR T (hadamardPoleSumWithOrigin s Z) +
            rectContourIntegral σL σR T (hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ) := by
              exact rectContourIntegral_add σL σR T (hadamardPoleSumWithOrigin s Z)
                (hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ)
                hsum_b hrem_b hsum_t hrem_t hsum_r hrem_r hsum_l hrem_l
      _ =
          (∑ i : HadamardPoleIndexWithOrigin Z,
            rectContourIntegral σL σR T
              (fun z => hadamardPoleResidueWithOrigin s i /
                (z - hadamardPolePointWithOrigin s i))) +
            rectContourIntegral σL σR T
              (hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ) := by
              rw [h_pole_sum_eq]
  have h_f_eq_decomp :
      rectContourIntegral σL σR T (weilIntegrand (hadamardKernel s)) =
        rectContourIntegral σL σR T
          (fun z =>
            hadamardPoleSumWithOrigin s Z z +
              hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ z) := by
    apply rectContourIntegral_congr
    · intro x hx
      have hz0 : ((x : ℂ) + (-T : ℝ) * I) ≠ 0 := by
        intro hx0
        have him : (-T : ℝ) = 0 := by simpa using congrArg Complex.im hx0
        linarith [hT]
      have hzZ : ((x : ℂ) + (-T : ℝ) * I) ∉ Z := by
        intro hzZ
        have hρ := hρ_im ((x : ℂ) + (-T : ℝ) * I) hzZ
        simp at hρ
      have hz1 : ((x : ℂ) + (-T : ℝ) * I) ≠ 1 := by
        intro hz1
        have him : (-T : ℝ) = 0 := by simpa using congrArg Complex.im hz1
        linarith [hT]
      have hzs : ((x : ℂ) + (-T : ℝ) * I) ≠ s := by
        intro hxs
        have him : (-T : ℝ) = s.im := by simpa using congrArg Complex.im hxs
        linarith [hs_im.1]
      exact hadamard_decomp_with_origin_eq_at_point hs0 hs1 hsζ hZ hz0 hzZ hz1 hzs
    · intro x hx
      have hz0 : ((x : ℂ) + (T : ℝ) * I) ≠ 0 := by
        intro hx0
        have him : (T : ℝ) = 0 := by simpa using congrArg Complex.im hx0
        linarith [hT]
      have hzZ : ((x : ℂ) + (T : ℝ) * I) ∉ Z := by
        intro hzZ
        have hρ := hρ_im ((x : ℂ) + (T : ℝ) * I) hzZ
        simp at hρ
      have hz1 : ((x : ℂ) + (T : ℝ) * I) ≠ 1 := by
        intro hz1
        have him : (T : ℝ) = 0 := by simpa using congrArg Complex.im hz1
        linarith [hT]
      have hzs : ((x : ℂ) + (T : ℝ) * I) ≠ s := by
        intro hxs
        have him : (T : ℝ) = s.im := by simpa using congrArg Complex.im hxs
        linarith [hs_im.2]
      exact hadamard_decomp_with_origin_eq_at_point hs0 hs1 hsζ hZ hz0 hzZ hz1 hzs
    · intro y hy
      have hz0 : ((σR : ℂ) + (y : ℂ) * I) ≠ 0 := by
        intro hz0
        have hre : (σR : ℝ) = 0 := by simpa using congrArg Complex.re hz0
        have hσR_pos : (0 : ℝ) < σR := by simpa using h_zero_re.2
        linarith
      have hzZ : ((σR : ℂ) + (y : ℂ) * I) ∉ Z := by
        intro hzZ
        have hρ := hρ_re ((σR : ℂ) + (y : ℂ) * I) hzZ
        simp at hρ
      have hz1 : ((σR : ℂ) + (y : ℂ) * I) ≠ 1 := by
        intro hz1
        have hre : (σR : ℝ) = 1 := by simpa using congrArg Complex.re hz1
        have hσR1 : (1 : ℝ) < σR := by simpa using h_one_re.2
        linarith
      have hzs : ((σR : ℂ) + (y : ℂ) * I) ≠ s := by
        intro hys
        have hre : (σR : ℝ) = s.re := by simpa using congrArg Complex.re hys
        linarith [hs_re.2]
      exact hadamard_decomp_with_origin_eq_at_point hs0 hs1 hsζ hZ hz0 hzZ hz1 hzs
    · intro y hy
      have hz0 : ((σL : ℂ) + (y : ℂ) * I) ≠ 0 := by
        intro hz0
        have hre : (σL : ℝ) = 0 := by simpa using congrArg Complex.re hz0
        have hσL_neg : σL < (0 : ℝ) := by simpa using h_zero_re.1
        linarith
      have hzZ : ((σL : ℂ) + (y : ℂ) * I) ∉ Z := by
        intro hzZ
        have hρ := hρ_re ((σL : ℂ) + (y : ℂ) * I) hzZ
        simp at hρ
      have hz1 : ((σL : ℂ) + (y : ℂ) * I) ≠ 1 := by
        intro hz1
        have hre : (σL : ℝ) = 1 := by simpa using congrArg Complex.re hz1
        have hσL1 : σL < (1 : ℝ) := by simpa using h_one_re.1
        linarith
      have hzs : ((σL : ℂ) + (y : ℂ) * I) ≠ s := by
        intro hys
        have hre : (σL : ℝ) = s.re := by simpa using congrArg Complex.re hys
        linarith [hs_re.1]
      exact hadamard_decomp_with_origin_eq_at_point hs0 hs1 hsζ hZ hz0 hzZ hz1 hzs
  have hmain := rectResidueTheorem_multi_pole_unconditional hσ hT
    (poles := (Finset.univ : Finset (HadamardPoleIndexWithOrigin Z)))
    (p := hadamardPolePointWithOrigin s) (r := hadamardPoleResidueWithOrigin s)
    (g := hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ)
    hp_re hp_im hrem_diff h_integral_eq
  have h_f_eq_decomp_sum :
      rectContourIntegral σL σR T (weilIntegrand (hadamardKernel s)) =
        rectContourIntegral σL σR T
          (fun z =>
            (∑ i : HadamardPoleIndexWithOrigin Z,
              hadamardPoleResidueWithOrigin s i / (z - hadamardPolePointWithOrigin s i)) +
              hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ z) := by
    calc
      rectContourIntegral σL σR T (weilIntegrand (hadamardKernel s)) =
          rectContourIntegral σL σR T
            (fun z =>
              hadamardPoleSumWithOrigin s Z z +
                hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ z) := h_f_eq_decomp
      _ =
          rectContourIntegral σL σR T
            (fun z =>
              (∑ i : HadamardPoleIndexWithOrigin Z,
                hadamardPoleResidueWithOrigin s i / (z - hadamardPolePointWithOrigin s i)) +
                hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ z) := by
              apply rectContourIntegral_congr <;> intro t ht <;> simp [hadamardPoleSumWithOrigin]
  calc
    rectContourIntegral σL σR T (weilIntegrand (hadamardKernel s)) =
        rectContourIntegral σL σR T
          (fun z =>
            (∑ i : HadamardPoleIndexWithOrigin Z,
              hadamardPoleResidueWithOrigin s i / (z - hadamardPolePointWithOrigin s i)) +
              hadamardRemainderWithOriginGlobal s Z hs0 hs1 hsζ hZ z) := h_f_eq_decomp_sum
    _ = 2 * ↑Real.pi * I * ∑ i : HadamardPoleIndexWithOrigin Z, hadamardPoleResidueWithOrigin s i :=
        hmain
    _ =
        2 * ↑Real.pi * I *
          (hadamardOriginCoeff + (∑ ρ ∈ Z, -hadamardZeroCoeff s ρ) +
            hadamardOneCoeff s + hadamardSelfCoeff s) := by
              rw [hadamardPoleResidueWithOrigin_sum_eq_explicit]

/-- Zero-free specialization of the origin-containing Hadamard rectangle residue
sum. -/
theorem rectContourIntegral_weilIntegrand_hadamardKernel_eq_residue_sum_with_origin_zero_free
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    {σL σR T : ℝ} (hσ : σL < σR) (hT : 0 < T)
    (h_zero_re : σL < (0 : ℂ).re ∧ (0 : ℂ).re < σR)
    (h_one_re : σL < 1 ∧ (1 : ℂ).re < σR)
    (hs_re : σL < s.re ∧ s.re < σR)
    (hs_im : -T < s.im ∧ s.im < T)
    (hζ_ne_rect :
      ∀ z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T), z ≠ 1 → riemannZeta z ≠ 0) :
    rectContourIntegral σL σR T (weilIntegrand (hadamardKernel s)) =
      2 * ↑Real.pi * I * (hadamardOriginCoeff + hadamardOneCoeff s + hadamardSelfCoeff s) := by
  have hζ_ne_off_empty :
      ∀ z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T),
        z ≠ 1 → z ∉ (∅ : Finset ℂ) → riemannZeta z ≠ 0 := by
    intro z hz hz1 _hz
    exact hζ_ne_rect z hz hz1
  simpa using
    (rectContourIntegral_weilIntegrand_hadamardKernel_eq_residue_sum_with_origin_of_interior_poles
      (Z := ∅) hs0 hs1 hsζ
      (by intro ρ hρ; simp at hρ) hσ hT h_zero_re h_one_re hs_re hs_im
      (by intro ρ hρ; simp at hρ)
      (by intro ρ hρ; simp at hρ)
      hζ_ne_off_empty)

/-- Explicit zero-free specialization of the origin-containing Hadamard
rectangle residue sum. -/
theorem rectContourIntegral_weilIntegrand_hadamardKernel_eq_residue_sum_with_origin_zero_free_explicit
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsζ : riemannZeta s ≠ 0)
    {σL σR T : ℝ} (hσ : σL < σR) (hT : 0 < T)
    (h_zero_re : σL < (0 : ℂ).re ∧ (0 : ℂ).re < σR)
    (h_one_re : σL < 1 ∧ (1 : ℂ).re < σR)
    (hs_re : σL < s.re ∧ s.re < σR)
    (hs_im : -T < s.im ∧ s.im < T)
    (hζ_ne_rect :
      ∀ z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T), z ≠ 1 → riemannZeta z ≠ 0) :
    rectContourIntegral σL σR T (weilIntegrand (hadamardKernel s)) =
      2 * ↑Real.pi * I *
        (hadamardOriginCoeff + deriv riemannZeta s / riemannZeta s + 1 / (s - 1) + 1) := by
  rw [rectContourIntegral_weilIntegrand_hadamardKernel_eq_residue_sum_with_origin_zero_free
    hs0 hs1 hsζ hσ hT h_zero_re h_one_re hs_re hs_im hζ_ne_rect]
  rw [hadamardOneCoeff_eq, hadamardSelfCoeff]
  ring

end Contour
end WeilPositivity
end ZD

end
