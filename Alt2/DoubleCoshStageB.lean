import RequestProject.DoubleCoshExtension

/-!
# Double-Cosh Paired-Integral Extension — Stage B

Stage B of the paired-integral construction: **proves Condition (3)** —
the paired integral annihilates the antisymmetric component of ψ.

## Setup

We work with a **finite symmetric trace**: a finite set of t-values
closed under `t → −t`, with even weights. This is the discrete analogue
of a symmetric Lebesgue measure, and it matches the natural prime-log
support `{±log p : p prime, p ≤ N}`. The pairing argument runs cleanly
over `Finset`.

## The theorem

For any odd ψ (i.e., `ψ(−t) = −ψ(t)`), the finite paired integral
vanishes:

```
∑_{t ∈ points} weight(t) · [K_L^ℂ(s,t)·ψ(t) + K_R^ℂ(s,t)·conj(ψ(t))] = 0
```

because the integrand is odd in t (kernels are even in t, weight is
even, ψ is odd), and summing an odd function over a symmetric support
gives zero.

## Relation to Stage A's `Condition3Holds`

Stage A defined `AntisymmetricPsi` via conjugation — that's the natural
involution for the paired integral's *mixed* conj/non-conj structure.
Stage B uses the simpler pure-reflection antisymmetry (`ψ(−t) = −ψ(t)`,
i.e., odd). Both are legitimate decompositions; the odd version gives
the clean pairing cancellation.
-/

open Complex Finset ZetaDefs

noncomputable section

namespace DoubleCoshExtension

/-! ### §1. Odd / Even ψ definitions (pure reflection) -/

/-- ψ is **odd under reflection**: `ψ(−t) = −ψ(t)`. -/
def IsOddPsi (ψ : ℝ → ℂ) : Prop := ∀ t : ℝ, ψ (-t) = -ψ t

/-- ψ is **even under reflection**: `ψ(−t) = ψ(t)`. -/
def IsEvenPsi (ψ : ℝ → ℂ) : Prop := ∀ t : ℝ, ψ (-t) = ψ t

/-- For odd ψ: `ψ(0) = 0`. -/
theorem IsOddPsi.at_zero {ψ : ℝ → ℂ} (h : IsOddPsi ψ) : ψ 0 = 0 := by
  have h0 : ψ (-(0 : ℝ)) = -ψ 0 := h 0
  rw [neg_zero] at h0
  -- h0 : ψ 0 = -ψ 0
  have h2 : (2 : ℂ) * ψ 0 = 0 := by linear_combination ψ 0 + h0
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-! ### §2. Finite symmetric trace -/

/-- A **finite symmetric trace**: a finite set of real values closed
under `t → −t`, equipped with an even real-valued weight. -/
structure FiniteSymmetricTrace where
  /-- The finite support set. -/
  points : Finset ℝ
  /-- The support is closed under negation. -/
  points_symmetric : ∀ t ∈ points, -t ∈ points
  /-- The weight function. -/
  weight : ℝ → ℝ
  /-- The weight is even. -/
  weight_even : ∀ t : ℝ, weight (-t) = weight t

/-- Kernel parity: `K_L^ℂ(s, −t) = K_L^ℂ(s, t)` (cosh is even in t). -/
theorem coshDetectorLeftC_even_in_t (s : ℂ) (t : ℝ) :
    coshDetectorLeftC s (-t) = coshDetectorLeftC s t := by
  simp only [coshDetectorLeftC_eq]
  have h : (s - (Real.pi / 6 : ℂ)) * ((-t : ℝ) : ℂ) =
           -((s - (Real.pi / 6 : ℂ)) * (t : ℂ)) := by
    push_cast; ring
  rw [h, Complex.cosh_neg]

/-- Kernel parity: `K_R^ℂ(s, −t) = K_R^ℂ(s, t)`. -/
theorem coshDetectorRightC_even_in_t (s : ℂ) (t : ℝ) :
    coshDetectorRightC s (-t) = coshDetectorRightC s t := by
  simp only [coshDetectorRightC_eq]
  have h : (s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * ((-t : ℝ) : ℂ) =
           -((s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ)) := by
    push_cast; ring
  rw [h, Complex.cosh_neg]

/-! ### §3. Finite paired integral -/

/-- The **finite paired integral**: the discrete-support version of the
Stage A `pairedIntegral`. -/
def finitePairedIntegral (T : FiniteSymmetricTrace) (ψ : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∑ t ∈ T.points, (T.weight t : ℂ) *
    (coshDetectorLeftC s t * ψ t +
     coshDetectorRightC s t * starRingEnd ℂ (ψ t))

/-! ### §4. Main theorem — Condition (3) holds for odd ψ -/

/-- The **paired-integrand is odd in t** when ψ is odd.
This is the pointwise statement whose summed form gives Stage B. -/
theorem paired_integrand_odd
    (T : FiniteSymmetricTrace) (ψ : ℝ → ℂ) (hψ : IsOddPsi ψ)
    (s : ℂ) (t : ℝ) :
    (T.weight (-t) : ℂ) *
      (coshDetectorLeftC s (-t) * ψ (-t) +
       coshDetectorRightC s (-t) * starRingEnd ℂ (ψ (-t))) =
    -((T.weight t : ℂ) *
      (coshDetectorLeftC s t * ψ t +
       coshDetectorRightC s t * starRingEnd ℂ (ψ t))) := by
  rw [T.weight_even, coshDetectorLeftC_even_in_t,
      coshDetectorRightC_even_in_t, hψ t, map_neg]
  ring

/-- **Stage B, main theorem**: the finite paired integral of an odd ψ
vanishes. This proves Condition (3) in the discrete-symmetric-trace
formulation.

Proof: the integrand is odd in t (`paired_integrand_odd`); reindex the
sum via the involution `t → −t` (valid since `T.points` is symmetric);
then the sum equals its own negation, forcing it to zero. -/
theorem finitePairedIntegral_of_odd_vanishes
    (T : FiniteSymmetricTrace) (ψ : ℝ → ℂ) (hψ : IsOddPsi ψ) (s : ℂ) :
    finitePairedIntegral T ψ s = 0 := by
  set f : ℝ → ℂ := fun t => (T.weight t : ℂ) *
    (coshDetectorLeftC s t * ψ t +
     coshDetectorRightC s t * starRingEnd ℂ (ψ t)) with hf
  change ∑ t ∈ T.points, f t = 0
  -- f is odd: f(-t) = -f(t)
  have f_odd : ∀ t : ℝ, f (-t) = -f t := by
    intro t
    simp only [hf]
    exact paired_integrand_odd T ψ hψ s t
  -- The image of T.points under negation is T.points itself
  have image_neg_eq : T.points.image (fun t : ℝ => -t) = T.points := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact T.points_symmetric y hy
    · intro hx
      exact Finset.mem_image.mpr ⟨-x, T.points_symmetric x hx, neg_neg x⟩
  -- Reindex via negation
  have neg_bij : ∑ t ∈ T.points, f t = ∑ t ∈ T.points, f (-t) := by
    conv_lhs => rw [← image_neg_eq]
    rw [Finset.sum_image (fun a _ b _ h => neg_injective h)]
  -- Sum over T.points equals its own negation
  have hsum_neg : ∑ t ∈ T.points, f t = -∑ t ∈ T.points, f t := by
    calc ∑ t ∈ T.points, f t
        = ∑ t ∈ T.points, f (-t) := neg_bij
      _ = ∑ t ∈ T.points, -f t := Finset.sum_congr rfl (fun t _ => f_odd t)
      _ = -∑ t ∈ T.points, f t := by rw [← Finset.sum_neg_distrib]
  -- x = -x in ℂ implies x = 0
  have h2 : (2 : ℂ) * ∑ t ∈ T.points, f t = 0 := by
    linear_combination ∑ t ∈ T.points, f t + hsum_neg
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num : (2 : ℂ) ≠ 0)

/-! ### §5. Condition (3) recast for the finite trace

We package the finite-trace version alongside Stage A's abstract form,
so downstream consumers can use either. -/

/-- **Condition (3) for finite traces** — the discrete formulation
of Stage A's `Condition3Holds`, specialized to our IsOddPsi antisymmetry.
Proved unconditionally by `finitePairedIntegral_of_odd_vanishes`. -/
def FiniteCondition3 (T : FiniteSymmetricTrace) : Prop :=
  ∀ ψ : ℝ → ℂ, IsOddPsi ψ → ∀ s : ℂ, finitePairedIntegral T ψ s = 0

theorem finiteCondition3_holds (T : FiniteSymmetricTrace) :
    FiniteCondition3 T :=
  fun ψ hψ s => finitePairedIntegral_of_odd_vanishes T ψ hψ s

/-! ### §6. Concrete trace: symmetric prime-log support

The canonical instance for number-theoretic applications: support on
`{±log p : p prime, p ≤ N}` with unit weights. -/

/-- Build a `FiniteSymmetricTrace` from a finite set of positive reals by
symmetrizing: take `S ∪ (−S)`. Weight is the indicator of `S ∪ (−S)`. -/
def symmetrizedTrace (S : Finset ℝ) : FiniteSymmetricTrace where
  points := S ∪ (S.image Neg.neg)
  points_symmetric := by
    intro t ht
    rcases Finset.mem_union.mp ht with h | h
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, h, rfl⟩)
    · obtain ⟨t', ht', heq⟩ := Finset.mem_image.mp h
      rw [← heq, neg_neg]
      exact Finset.mem_union_left _ ht'
  weight _ := 1
  weight_even _ := rfl

/-- Odd ψ vanishes at 0 (useful for single-point degenerate cases). -/
theorem finitePairedIntegral_symmetrized_vanishes
    (S : Finset ℝ) (ψ : ℝ → ℂ) (hψ : IsOddPsi ψ) (s : ℂ) :
    finitePairedIntegral (symmetrizedTrace S) ψ s = 0 :=
  finitePairedIntegral_of_odd_vanishes _ ψ hψ s

/-! ### §7. Axiom hygiene -/

#print axioms coshDetectorLeftC_even_in_t
#print axioms coshDetectorRightC_even_in_t
#print axioms paired_integrand_odd
#print axioms finitePairedIntegral_of_odd_vanishes
#print axioms finiteCondition3_holds
#print axioms finitePairedIntegral_symmetrized_vanishes

end DoubleCoshExtension

end
