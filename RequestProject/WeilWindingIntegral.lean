import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilRectangleViaSubtraction

/-!
# Rectangle Winding Integral — `∮_∂R (z - p)⁻¹ dz = 2πi`

Closes `rectContourIntegral_inv_center_eq_twoPiI_target` from
`WeilRectangleViaSubtraction.lean` unconditionally.

## Strategy
Edge-by-edge FTC. Let a := σL - p.re < 0, b := σR - p.re > 0,
c := T + p.im > 0, d := T - p.im > 0.

* Bottom (y = -T): z - p = x - c·I, Im < 0, in slitPlane. Antideriv log(z - p).
* Right  (x = σR): z - p has Re = b > 0, in slitPlane.   Antideriv log(z - p).
* Top    (y = T):  z - p = x + d·I, Im > 0, in slitPlane. Antideriv log(z - p).
* Left   (x = σL): z - p has Re = a < 0, crosses branch cut; use log(p - z).

Sum reduces to (log x - log(-x)) + (log(-y) - log y) with x.im > 0, y.im < 0,
each bracket equal to π·I by Complex.arg_neg_eq_arg_{sub,add}_pi_of_im_{pos,neg}.
-/

open Complex Real MeasureTheory Set Filter

noncomputable section

namespace ZD
namespace WeilPositivity
namespace Contour

private lemma bottom_edge_integral (σL σR T : ℝ) (p : ℂ) (hc : -T - p.im < 0) :
    ∫ x : ℝ in σL..σR, ((x : ℂ) + (-T : ℝ) * I - p)⁻¹ =
    Complex.log ((σR : ℂ) + (-T : ℝ) * I - p) -
    Complex.log ((σL : ℂ) + (-T : ℝ) * I - p) := by
  have hderiv : ∀ x : ℝ, HasDerivAt
      (fun t : ℝ => Complex.log ((t : ℂ) + (-T : ℝ) * I - p))
      (((x : ℂ) + (-T : ℝ) * I - p)⁻¹) x := by
    intro x
    have hslit : ((x : ℂ) + (-T : ℝ) * I - p) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; right
      intro heq
      have him : ((x : ℂ) + (-T : ℝ) * I - p).im = -T - p.im := by simp
      rw [heq] at him; linarith
    have hlog : HasDerivAt Complex.log (((x : ℂ) + (-T : ℝ) * I - p))⁻¹
        ((x : ℂ) + (-T : ℝ) * I - p) := Complex.hasDerivAt_log hslit
    have hinner : HasDerivAt (fun t : ℝ => (t : ℂ) + (-T : ℝ) * I - p) (1 : ℂ) x := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) x := Complex.ofRealCLM.hasDerivAt
      simpa using h1.add_const ((-T : ℝ) * I : ℂ) |>.sub_const p
    simpa using hlog.comp x hinner
  have hint : IntervalIntegrable
      (fun x : ℝ => ((x : ℂ) + (-T : ℝ) * I - p)⁻¹) volume σL σR := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x _ heq
      have him : ((x : ℂ) + (-T : ℝ) * I - p).im = -T - p.im := by simp
      rw [heq] at him; simp at him; linarith
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint

private lemma top_edge_integral (σL σR T : ℝ) (p : ℂ) (hd : 0 < T - p.im) :
    ∫ x : ℝ in σL..σR, ((x : ℂ) + (T : ℝ) * I - p)⁻¹ =
    Complex.log ((σR : ℂ) + (T : ℝ) * I - p) -
    Complex.log ((σL : ℂ) + (T : ℝ) * I - p) := by
  have hderiv : ∀ x : ℝ, HasDerivAt
      (fun t : ℝ => Complex.log ((t : ℂ) + (T : ℝ) * I - p))
      (((x : ℂ) + (T : ℝ) * I - p)⁻¹) x := by
    intro x
    have hslit : ((x : ℂ) + (T : ℝ) * I - p) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; right
      intro heq
      have him : ((x : ℂ) + (T : ℝ) * I - p).im = T - p.im := by simp
      rw [heq] at him; linarith
    have hlog : HasDerivAt Complex.log (((x : ℂ) + (T : ℝ) * I - p))⁻¹
        ((x : ℂ) + (T : ℝ) * I - p) := Complex.hasDerivAt_log hslit
    have hinner : HasDerivAt (fun t : ℝ => (t : ℂ) + (T : ℝ) * I - p) (1 : ℂ) x := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) x := Complex.ofRealCLM.hasDerivAt
      simpa using h1.add_const ((T : ℝ) * I : ℂ) |>.sub_const p
    simpa using hlog.comp x hinner
  have hint : IntervalIntegrable
      (fun x : ℝ => ((x : ℂ) + (T : ℝ) * I - p)⁻¹) volume σL σR := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x _ heq
      have him : ((x : ℂ) + (T : ℝ) * I - p).im = T - p.im := by simp
      rw [heq] at him; simp at him; linarith
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint

private lemma right_edge_integral (σR T : ℝ) (p : ℂ) (hb : 0 < σR - p.re) :
    ∫ y : ℝ in (-T : ℝ)..T, ((σR : ℂ) + (y : ℝ) * I - p)⁻¹ =
    -Complex.I * (Complex.log ((σR : ℂ) + (T : ℝ) * I - p) -
                  Complex.log ((σR : ℂ) + (-T : ℝ) * I - p)) := by
  have hderiv : ∀ y : ℝ, HasDerivAt
      (fun t : ℝ => Complex.log ((σR : ℂ) + (t : ℝ) * I - p))
      (Complex.I * ((σR : ℂ) + (y : ℝ) * I - p)⁻¹) y := by
    intro y
    have hslit : ((σR : ℂ) + (y : ℝ) * I - p) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left
      show 0 < ((σR : ℂ) + (y : ℝ) * I - p).re
      simp; linarith
    have hlog : HasDerivAt Complex.log (((σR : ℂ) + (y : ℝ) * I - p))⁻¹
        ((σR : ℂ) + (y : ℝ) * I - p) := Complex.hasDerivAt_log hslit
    have hinner : HasDerivAt (fun t : ℝ => (σR : ℂ) + (t : ℝ) * I - p) Complex.I y := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) y := Complex.ofRealCLM.hasDerivAt
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) Complex.I y := by
        simpa using h1.mul_const I
      have h3 : HasDerivAt (fun t : ℝ => (σR : ℂ) + (t : ℝ) * I) Complex.I y := by
        simpa using h2.const_add (σR : ℂ)
      simpa using h3.sub_const p
    have hcomp := hlog.comp y hinner
    have heq : (((σR : ℂ) + (y : ℝ) * I - p))⁻¹ * Complex.I =
               Complex.I * ((σR : ℂ) + (y : ℝ) * I - p)⁻¹ := by ring
    rw [heq] at hcomp; exact hcomp
  have hint : IntervalIntegrable
      (fun y : ℝ => ((σR : ℂ) + (y : ℝ) * I - p)⁻¹) volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · fun_prop
    · intro y _ heq
      have hre : ((σR : ℂ) + (y : ℝ) * I - p).re = σR - p.re := by simp
      rw [heq] at hre; simp at hre; linarith
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => Complex.log ((σR : ℂ) + (t : ℝ) * I - p))
      (f' := fun y => Complex.I * ((σR : ℂ) + (y : ℝ) * I - p)⁻¹)
      (a := -T) (b := T)
      (fun y _ => hderiv y)
      (hint.const_mul Complex.I)
  rw [show (∫ (y : ℝ) in -T..T, (fun y => I * ((σR : ℂ) + (y : ℝ) * I - p)⁻¹) y)
      = I * ∫ (y : ℝ) in -T..T, ((σR : ℂ) + (y : ℝ) * I - p)⁻¹
      from intervalIntegral.integral_const_mul I _] at hftc
  have hftc' : Complex.I * ∫ y : ℝ in (-T : ℝ)..T, ((σR : ℂ) + (y : ℝ) * I - p)⁻¹ =
               Complex.log ((σR : ℂ) + (T : ℝ) * I - p) -
               Complex.log ((σR : ℂ) + (-T : ℝ) * I - p) := by
    convert hftc using 2
  have hres := congrArg (fun z => -Complex.I * z) hftc'
  simp only [← mul_assoc] at hres
  have hcancel : (-Complex.I) * Complex.I = 1 := by
    have : (-Complex.I) * Complex.I = -(Complex.I * Complex.I) := by ring
    rw [this, Complex.I_mul_I]; ring
  rw [hcancel, one_mul] at hres
  exact hres

private lemma left_edge_integral (σL T : ℝ) (p : ℂ) (ha : σL - p.re < 0) :
    ∫ y : ℝ in (-T : ℝ)..T, ((σL : ℂ) + (y : ℝ) * I - p)⁻¹ =
    -Complex.I * (Complex.log (p - ((σL : ℂ) + (T : ℝ) * I)) -
                  Complex.log (p - ((σL : ℂ) + (-T : ℝ) * I))) := by
  have hderiv : ∀ y : ℝ, HasDerivAt
      (fun t : ℝ => Complex.log (p - ((σL : ℂ) + (t : ℝ) * I)))
      (Complex.I * ((σL : ℂ) + (y : ℝ) * I - p)⁻¹) y := by
    intro y
    have hslit : (p - ((σL : ℂ) + (y : ℝ) * I)) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left
      show 0 < (p - ((σL : ℂ) + (y : ℝ) * I)).re
      simp; linarith
    have hlog : HasDerivAt Complex.log ((p - ((σL : ℂ) + (y : ℝ) * I)))⁻¹
        (p - ((σL : ℂ) + (y : ℝ) * I)) := Complex.hasDerivAt_log hslit
    have hinner : HasDerivAt (fun t : ℝ => p - ((σL : ℂ) + (t : ℝ) * I)) (-Complex.I) y := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) y := Complex.ofRealCLM.hasDerivAt
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) Complex.I y := by
        simpa using h1.mul_const I
      have h3 : HasDerivAt (fun t : ℝ => (σL : ℂ) + (t : ℝ) * I) Complex.I y := by
        simpa using h2.const_add (σL : ℂ)
      simpa using h3.const_sub p
    have hcomp := hlog.comp y hinner
    have heq : (p - ((σL : ℂ) + (y : ℝ) * I))⁻¹ * (-Complex.I) =
               Complex.I * ((σL : ℂ) + (y : ℝ) * I - p)⁻¹ := by
      have hne : (p - ((σL : ℂ) + (y : ℝ) * I)) ≠ 0 := Complex.slitPlane_ne_zero hslit
      have hsym : ((σL : ℂ) + (y : ℝ) * I - p) = -(p - ((σL : ℂ) + (y : ℝ) * I)) := by ring
      rw [hsym, inv_neg]; ring
    rw [heq] at hcomp; exact hcomp
  have hint : IntervalIntegrable
      (fun y : ℝ => ((σL : ℂ) + (y : ℝ) * I - p)⁻¹) volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · fun_prop
    · intro y _ heq
      have hre : ((σL : ℂ) + (y : ℝ) * I - p).re = σL - p.re := by simp
      rw [heq] at hre; simp at hre; linarith
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => Complex.log (p - ((σL : ℂ) + (t : ℝ) * I)))
      (f' := fun y => Complex.I * ((σL : ℂ) + (y : ℝ) * I - p)⁻¹)
      (a := -T) (b := T)
      (fun y _ => hderiv y)
      (hint.const_mul Complex.I)
  rw [show (∫ (y : ℝ) in -T..T, (fun y => I * ((σL : ℂ) + (y : ℝ) * I - p)⁻¹) y)
      = I * ∫ (y : ℝ) in -T..T, ((σL : ℂ) + (y : ℝ) * I - p)⁻¹
      from intervalIntegral.integral_const_mul I _] at hftc
  have hftc' : Complex.I * ∫ y : ℝ in (-T : ℝ)..T, ((σL : ℂ) + (y : ℝ) * I - p)⁻¹ =
               Complex.log (p - ((σL : ℂ) + (T : ℝ) * I)) -
               Complex.log (p - ((σL : ℂ) + (-T : ℝ) * I)) := by
    convert hftc using 2
  have hres := congrArg (fun z => -Complex.I * z) hftc'
  simp only [← mul_assoc] at hres
  have hcancel : (-Complex.I) * Complex.I = 1 := by
    have : (-Complex.I) * Complex.I = -(Complex.I * Complex.I) := by ring
    rw [this, Complex.I_mul_I]; ring
  rw [hcancel, one_mul] at hres
  exact hres

private lemma log_sub_log_neg_of_im_pos {x : ℂ} (hx : 0 < x.im) :
    Complex.log x - Complex.log (-x) = (Real.pi : ℂ) * Complex.I := by
  have step : Complex.log (-x) = Complex.log x - (Real.pi : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.log_re]
    · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hx]
  rw [step]; ring

private lemma log_neg_sub_log_of_im_neg {x : ℂ} (hx : x.im < 0) :
    Complex.log (-x) - Complex.log x = (Real.pi : ℂ) * Complex.I := by
  have step : Complex.log (-x) = Complex.log x + (Real.pi : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.log_re]
    · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hx]
  rw [step]; ring

theorem rectContourIntegral_inv_center_eq_twoPiI
    (σL σR T : ℝ) (hσ : σL < σR) (hT : 0 < T) (p : ℂ)
    (hp_re : σL < p.re ∧ p.re < σR) (hp_im : -T < p.im ∧ p.im < T) :
    rectContourIntegral σL σR T (fun z => (z - p)⁻¹) = 2 * ↑π * I := by
  obtain ⟨hLre, hRre⟩ := hp_re
  obtain ⟨hLim, hRim⟩ := hp_im
  have ha : σL - p.re < 0 := by linarith
  have hb : 0 < σR - p.re := by linarith
  have hc : -T - p.im < 0 := by linarith
  have hd : 0 < T - p.im := by linarith
  unfold rectContourIntegral
  rw [bottom_edge_integral σL σR T p hc]
  rw [top_edge_integral σL σR T p hd]
  rw [right_edge_integral σR T p hb]
  rw [left_edge_integral σL T p ha]
  set A : ℂ := Complex.log ((σR : ℂ) + (-T : ℝ) * I - p) with hA_def
  set B : ℂ := Complex.log ((σL : ℂ) + (-T : ℝ) * I - p) with hB_def
  set C : ℂ := Complex.log ((σR : ℂ) + (T : ℝ) * I - p) with hC_def
  set D : ℂ := Complex.log ((σL : ℂ) + (T : ℝ) * I - p) with hD_def
  set E : ℂ := Complex.log (p - ((σL : ℂ) + (T : ℝ) * I)) with hE_def
  set F : ℂ := Complex.log (p - ((σL : ℂ) + (-T : ℝ) * I)) with hF_def
  set Gr : ℂ := Complex.log ((σR : ℂ) + (T : ℝ) * I - p) with hGr_def
  set Gl : ℂ := Complex.log ((σR : ℂ) + (-T : ℝ) * I - p) with hGl_def
  have hA_Gl : A = Gl := rfl
  have hC_Gr : C = Gr := rfl
  set x : ℂ := (σL : ℂ) + (T : ℝ) * I - p with hx_def
  set y : ℂ := (σL : ℂ) + (-T : ℝ) * I - p with hy_def
  have hx_im : x.im = T - p.im := by simp [hx_def]
  have hy_im : y.im = -T - p.im := by simp [hy_def]
  have hx_pos : 0 < x.im := by rw [hx_im]; linarith
  have hy_neg : y.im < 0 := by rw [hy_im]; linarith
  have hD_eq_logx : D = Complex.log x := by simp [hD_def, hx_def]
  have hB_eq_logy : B = Complex.log y := by simp [hB_def, hy_def]
  have hE_eq : E = Complex.log (-x) := by
    have : p - ((σL : ℂ) + (T : ℝ) * I) = -x := by rw [hx_def]; ring
    rw [hE_def, this]
  have hF_eq : F = Complex.log (-y) := by
    have : p - ((σL : ℂ) + (-T : ℝ) * I) = -y := by rw [hy_def]; ring
    rw [hF_def, this]
  have hDB : D - B = Complex.log x - Complex.log y := by rw [hD_eq_logx, hB_eq_logy]
  have hEF : E - F = Complex.log (-x) - Complex.log (-y) := by rw [hE_eq, hF_eq]
  have hxpi : Complex.log x - Complex.log (-x) = (Real.pi : ℂ) * Complex.I :=
    log_sub_log_neg_of_im_pos hx_pos
  have hypi : Complex.log (-y) - Complex.log y = (Real.pi : ℂ) * Complex.I :=
    log_neg_sub_log_of_im_neg hy_neg
  have hI_neg_I : Complex.I * (-Complex.I) = 1 := by
    have : Complex.I * (-Complex.I) = -(Complex.I * Complex.I) := by ring
    rw [this, Complex.I_mul_I]; ring
  have hsmul1 : Complex.I • (-Complex.I * (Gr - Gl)) = Gr - Gl := by
    show Complex.I * (-Complex.I * (Gr - Gl)) = Gr - Gl
    rw [← mul_assoc, hI_neg_I, one_mul]
  have hsmul2 : Complex.I • (-Complex.I * (E - F)) = E - F := by
    show Complex.I * (-Complex.I * (E - F)) = E - F
    rw [← mul_assoc, hI_neg_I, one_mul]
  rw [hsmul1, hsmul2]
  show (A - B) - (C - D) + (Gr - Gl) - (E - F) = 2 * (Real.pi : ℂ) * Complex.I
  have hreduce : (A - B) - (C - D) + (Gr - Gl) - (E - F) = (D - B) - (E - F) := by
    rw [hA_Gl, hC_Gr]; ring
  rw [hreduce, hDB, hEF]
  have hdist : Complex.log x - Complex.log y - (Complex.log (-x) - Complex.log (-y)) =
               (Complex.log x - Complex.log (-x)) + (Complex.log (-y) - Complex.log y) := by
    ring
  rw [hdist, hxpi, hypi]
  ring

theorem rectContourIntegral_inv_center_eq_twoPiI_holds :
    rectContourIntegral_inv_center_eq_twoPiI_target := by
  intro σL σR T hσ hT p hp_re hp_im
  exact rectContourIntegral_inv_center_eq_twoPiI σL σR T hσ hT p hp_re hp_im

#print axioms rectContourIntegral_inv_center_eq_twoPiI
#print axioms rectContourIntegral_inv_center_eq_twoPiI_holds

-- ═══════════════════════════════════════════════════════════════════════════
-- § Unconditional wrappers for residue theorems
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Unconditional single-pole residue theorem.** Drops the `hwind` hypothesis
from `rectResidueTheorem_via_subtraction` by supplying
`rectContourIntegral_inv_center_eq_twoPiI_holds` internally. -/
theorem rectResidueTheorem_via_subtraction_unconditional
    {σL σR T : ℝ} (hσ : σL < σR) (hT : 0 < T)
    (f g : ℂ → ℂ) (p : ℂ) (r : ℂ)
    (hp_re : σL < p.re ∧ p.re < σR) (hp_im : -T < p.im ∧ p.im < T)
    (hg_diff : DifferentiableOn ℂ g (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T))
    (hf_eq_on_rect_minus_p : ∀ z ∈ (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T) \ ({p} : Set ℂ),
        f z = r / (z - p) + g z)
    (hf_integral_eq : rectContourIntegral σL σR T f =
        rectContourIntegral σL σR T (fun z => r / (z - p)) +
        rectContourIntegral σL σR T g) :
    rectContourIntegral σL σR T f = 2 * ↑π * I * r :=
  rectResidueTheorem_via_subtraction hσ hT f g p r hp_re hp_im
    rectContourIntegral_inv_center_eq_twoPiI_holds hg_diff
    hf_eq_on_rect_minus_p hf_integral_eq

#print axioms rectResidueTheorem_via_subtraction_unconditional

/-- **Unconditional multi-pole residue theorem.** Drops the `hwind` hypothesis
from `rectResidueTheorem_multi_pole`. -/
theorem rectResidueTheorem_multi_pole_unconditional
    {σL σR T : ℝ} (hσ : σL < σR) (hT : 0 < T)
    {ι : Type*} (poles : Finset ι) (p : ι → ℂ) (r : ι → ℂ) (g : ℂ → ℂ)
    (hp_re : ∀ i ∈ poles, σL < (p i).re ∧ (p i).re < σR)
    (hp_im : ∀ i ∈ poles, -T < (p i).im ∧ (p i).im < T)
    (hg_diff : DifferentiableOn ℂ g (Set.uIcc σL σR ×ℂ Set.uIcc (-T) T))
    (h_integral_eq : rectContourIntegral σL σR T
        (fun z => ∑ i ∈ poles, r i / (z - p i) + g z) =
      (∑ i ∈ poles, rectContourIntegral σL σR T (fun z => r i / (z - p i))) +
      rectContourIntegral σL σR T g) :
    rectContourIntegral σL σR T
      (fun z => ∑ i ∈ poles, r i / (z - p i) + g z) = 2 * ↑π * I * ∑ i ∈ poles, r i :=
  rectResidueTheorem_multi_pole hσ hT poles p r g hp_re hp_im hg_diff
    rectContourIntegral_inv_center_eq_twoPiI_holds h_integral_eq

#print axioms rectResidueTheorem_multi_pole_unconditional

end Contour
end WeilPositivity
end ZD

end
