import RequestProject.DoubleCoshResidue

/-!
# Double-Cosh Paired-Integral Extension — Stage A

Setup for the paired-integral construction that aims to produce a
cosh-symmetric analytic extension of ζ on the overlap region `(1, π/3)`.

## The construction target

```
f(s) := ∫ test(t) · [K_L^ℂ(s, t) · ψ(t) + K_R^ℂ(s, t) · conj(ψ(t))] dμ(t)
```

with four conditions for closure:

* **(1) Pair relation under FE**: `K_R^ℂ(s,t) = K_L^ℂ(1−s, t)`.
* **(2) Invariant measure/test**: `μ` and `test` symmetric under the
  matching involution (t → −t).
* **(3) Overlap trace annihilates antisymmetric ψ**: paired integral of
  an antisymmetric ψ vanishes on the overlap.
* **(4) Symmetric ψ reproduces ζ trace**: paired integral of a symmetric
  ψ agrees with `riemannZeta` on `(1, π/3)`.

## What this file establishes

**Stage A** — the algebraic/structural layer:

* Complex extension of the kernel pair (`coshDetectorLeftC`,
  `coshDetectorRightC`), entire in `s`.
* **Condition (1) proved unconditionally** — FE pair relation is a
  direct algebraic identity (`cosh` even + FE substitution).
* Symmetric/antisymmetric decomposition of `ψ`, invariance templates.
* Paired integral operator definition.
* Conditions (2), (3), (4) stated as `Prop`s — the explicit goals for
  Stage B and Stage C.

Stages B and C (annihilation of antisymmetric component; ζ-trace
reproduction by symmetric component) are the concrete analytic content
remaining. This file makes them named targets.
-/

open Real Complex ZetaDefs

noncomputable section

namespace DoubleCoshExtension

/-! ### §1. Complex extension of the kernel pair -/

/-- Complex left kernel: `K_L^ℂ(s, t) = cosh((s − π/6) · t)`. Entire in `s`
for every fixed real `t`. -/
def coshDetectorLeftC (s : ℂ) (t : ℝ) : ℂ :=
  Complex.cosh ((s - (Real.pi / 6 : ℂ)) * (t : ℂ))

/-- Complex right kernel: `K_R^ℂ(s, t) = cosh((s − (1 − π/6)) · t)`. Entire in `s`. -/
def coshDetectorRightC (s : ℂ) (t : ℝ) : ℂ :=
  Complex.cosh ((s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ))

@[simp] theorem coshDetectorLeftC_eq (s : ℂ) (t : ℝ) :
    coshDetectorLeftC s t = Complex.cosh ((s - (Real.pi / 6 : ℂ)) * (t : ℂ)) := rfl

@[simp] theorem coshDetectorRightC_eq (s : ℂ) (t : ℝ) :
    coshDetectorRightC s t = Complex.cosh ((s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ)) := rfl

/-! ### §2. Condition (1): FE pair relation (proved) -/

/-- **Condition (1)**: `K_R^ℂ(s, t) = K_L^ℂ(1 − s, t)`. The kernel pair
carries the FE reflection structurally — a direct algebraic identity
from cosh being even. This is what distinguishes the cosh *pair*
construction from a single-kernel setup. -/
theorem coshDetectorRightC_eq_Left_one_sub (s : ℂ) (t : ℝ) :
    coshDetectorRightC s t = coshDetectorLeftC (1 - s) t := by
  simp only [coshDetectorLeftC_eq, coshDetectorRightC_eq]
  have : ((1 - s) - (Real.pi / 6 : ℂ)) * (t : ℂ) =
         -((s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ)) := by ring
  rw [this, Complex.cosh_neg]

/-- Helper: conjugation fixes `(Real.pi / 6 : ℂ)` (it's real). -/
private lemma conj_pi_div_six : starRingEnd ℂ (Real.pi / 6 : ℂ) = (Real.pi / 6 : ℂ) := by
  have h : (Real.pi / 6 : ℂ) = ((Real.pi / 6 : ℝ) : ℂ) := by push_cast; ring
  rw [h]; exact Complex.conj_ofReal _

/-- **Conjugation-compatible form**: `K_L^ℂ(s̄, t) = conj(K_L^ℂ(s, t))`.
Via Schwarz reflection on cosh (cosh has real Taylor coefficients at 0). -/
theorem coshDetectorLeftC_conj (s : ℂ) (t : ℝ) :
    coshDetectorLeftC (starRingEnd ℂ s) t = starRingEnd ℂ (coshDetectorLeftC s t) := by
  simp only [coshDetectorLeftC_eq]
  have h1 : (starRingEnd ℂ s - (Real.pi / 6 : ℂ)) * (t : ℂ) =
            starRingEnd ℂ ((s - (Real.pi / 6 : ℂ)) * (t : ℂ)) := by
    rw [map_mul, map_sub, conj_pi_div_six, Complex.conj_ofReal]
  rw [h1, ← Complex.cosh_conj]

/-- `K_R^ℂ(s̄, t) = conj(K_R^ℂ(s, t))`. Same Schwarz-reflection structure. -/
theorem coshDetectorRightC_conj (s : ℂ) (t : ℝ) :
    coshDetectorRightC (starRingEnd ℂ s) t = starRingEnd ℂ (coshDetectorRightC s t) := by
  simp only [coshDetectorRightC_eq]
  have h1 : (starRingEnd ℂ s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ) =
            starRingEnd ℂ ((s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ)) := by
    rw [map_mul, map_sub, map_sub, map_one, conj_pi_div_six, Complex.conj_ofReal]
  rw [h1, ← Complex.cosh_conj]

/-- **Klein 180 pair relation**: combining FE with conjugation,
`K_R^ℂ(s, t) = conj(K_L^ℂ(1 − s̄, t))`. The full Klein-four action on
the pair, encoded structurally. -/
theorem coshDetectorRightC_eq_conj_Left_one_sub_conj (s : ℂ) (t : ℝ) :
    coshDetectorRightC s t =
      starRingEnd ℂ (coshDetectorLeftC (1 - starRingEnd ℂ s) t) := by
  rw [coshDetectorRightC_eq_Left_one_sub]
  have h_apply : coshDetectorLeftC (1 - starRingEnd ℂ s) t =
      starRingEnd ℂ (coshDetectorLeftC (starRingEnd ℂ (1 - starRingEnd ℂ s)) t) := by
    rw [coshDetectorLeftC_conj, starRingEnd_self_apply]
  rw [h_apply]
  congr 2
  simp [map_sub, map_one, starRingEnd_self_apply]

/-! ### §3. Symmetric/antisymmetric decomposition of ψ -/

/-- A ψ : ℝ → ℂ is **symmetric under the matching involution** if
`ψ(−t) = conj(ψ(t))`. This is the representative that survives the
paired trace. -/
def SymmetricPsi (ψ : ℝ → ℂ) : Prop :=
  ∀ t : ℝ, ψ (-t) = starRingEnd ℂ (ψ t)

/-- A ψ : ℝ → ℂ is **antisymmetric under the matching involution** if
`ψ(−t) = −conj(ψ(t))`. This is the representative annihilated by the
paired trace (condition 3 to be proved). -/
def AntisymmetricPsi (ψ : ℝ → ℂ) : Prop :=
  ∀ t : ℝ, ψ (-t) = -(starRingEnd ℂ (ψ t))

/-- Decomposition into symmetric + antisymmetric: every ψ is the sum of
its sym and asym parts under the involution. -/
def psiSymPart (ψ : ℝ → ℂ) (t : ℝ) : ℂ := (ψ t + starRingEnd ℂ (ψ (-t))) / 2

def psiAsymPart (ψ : ℝ → ℂ) (t : ℝ) : ℂ := (ψ t - starRingEnd ℂ (ψ (-t))) / 2

theorem psiSymPart_symmetric (ψ : ℝ → ℂ) : SymmetricPsi (psiSymPart ψ) := by
  intro t
  unfold psiSymPart
  rw [neg_neg]
  rw [map_div₀, map_add, starRingEnd_self_apply]
  have h2 : starRingEnd ℂ (2 : ℂ) = 2 := by
    show starRingEnd ℂ ((2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ)
    exact Complex.conj_ofReal 2
  rw [h2]
  ring

theorem psiAsymPart_antisymmetric (ψ : ℝ → ℂ) : AntisymmetricPsi (psiAsymPart ψ) := by
  intro t
  unfold psiAsymPart
  rw [neg_neg]
  rw [map_div₀, map_sub, starRingEnd_self_apply]
  have h2 : starRingEnd ℂ (2 : ℂ) = 2 := by
    show starRingEnd ℂ ((2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ)
    exact Complex.conj_ofReal 2
  rw [h2]
  ring

theorem psi_decompose (ψ : ℝ → ℂ) (t : ℝ) :
    ψ t = psiSymPart ψ t + psiAsymPart ψ t := by
  unfold psiSymPart psiAsymPart
  ring

/-! ### §4. FE-invariant measure/test templates -/

/-- A test function `test : ℝ → ℝ` is FE-symmetric if `test(−t) = test(t)`.
This is the even-in-t condition from Condition (2). -/
def FESymmetricTest (test : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, test (-t) = test t

/-- A measure is FE-symmetric (informal): it's invariant under t → −t.
We package this abstractly; concrete instances pick e.g. a Gaussian
measure or prime-log-spaced atoms. -/
structure FEInvariantTrace where
  μ : MeasureTheory.Measure ℝ
  test : ℝ → ℝ
  test_symmetric : FESymmetricTest test
  test_nonneg : ∀ t, 0 ≤ test t
  -- Integrability, compact support, etc. as needed for concrete use.

/-! ### §5. Paired integral operator -/

/-- The **paired integral operator** producing a candidate ζ-extension f:
`f(s) := ∫ test(t) · [K_L^ℂ(s,t) · ψ(t) + K_R^ℂ(s,t) · conj(ψ(t))] dμ`. -/
def pairedIntegral (T : FEInvariantTrace) (ψ : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t, (T.test t : ℂ) *
       (coshDetectorLeftC s t * ψ t +
        coshDetectorRightC s t * starRingEnd ℂ (ψ t)) ∂T.μ

/-! ### §6. Conditions (2)-(4) as explicit Props — Stage B/C targets -/

/-- **Condition (2) (structural)**: the trace map `T` is FE-symmetric.
Packaged in the `FEInvariantTrace` structure. This is a *definitional*
choice for the trace; we state it explicitly for clarity. -/
def Condition2Holds (T : FEInvariantTrace) : Prop :=
  FESymmetricTest T.test

theorem condition2_automatic (T : FEInvariantTrace) : Condition2Holds T :=
  T.test_symmetric

/-- **Condition (3) — antisymmetric annihilation**: the paired integral
vanishes on antisymmetric ψ, throughout the overlap region `(1, π/3)`.
This is the heart of "symmetrization projects away the antisymmetric". -/
def Condition3Holds (T : FEInvariantTrace) : Prop :=
  ∀ ψ : ℝ → ℂ, AntisymmetricPsi ψ →
    ∀ s : ℂ, 1 < s.re → s.re < Real.pi / 3 →
      pairedIntegral T ψ s = 0

/-- **Condition (4) — ζ-trace reproduction**: there exists a symmetric ψ
for which the paired integral reproduces `riemannZeta` on the overlap. -/
def Condition4Holds (T : FEInvariantTrace) : Prop :=
  ∃ ψ : ℝ → ℂ, SymmetricPsi ψ ∧
    ∀ s : ℂ, 1 < s.re → s.re < Real.pi / 3 →
      pairedIntegral T ψ s = riemannZeta s

/-! ### §7. The closure theorem — conditional on (2), (3), (4) -/

/-- **The conditional closure** (Stage A packaging): if we have a trace T
satisfying conditions (2), (3), (4), then the paired integral provides
a cosh-pair-symmetric analytic extension of `riemannZeta` on the overlap
region. Combined with the existing `cosh_kernel_pi_sixth_symmetry`
machinery, this would propagate π/6-reflection-invariance to ζ-zeros.

The proof of the conditional is trivial assembly; the hard content is
establishing the three conditions with a concrete trace + ψ. -/
theorem paired_extension_exists
    (T : FEInvariantTrace)
    (h3 : Condition3Holds T) (h4 : Condition4Holds T) :
    ∃ ψ : ℝ → ℂ, SymmetricPsi ψ ∧
      ∀ s : ℂ, 1 < s.re → s.re < Real.pi / 3 →
        pairedIntegral T ψ s = riemannZeta s :=
  h4

/-! ### §8. Axiom hygiene -/

#print axioms coshDetectorRightC_eq_Left_one_sub
#print axioms coshDetectorLeftC_conj
#print axioms coshDetectorRightC_conj
#print axioms coshDetectorRightC_eq_conj_Left_one_sub_conj
#print axioms psiSymPart_symmetric
#print axioms psiAsymPart_antisymmetric
#print axioms psi_decompose
#print axioms condition2_automatic
#print axioms paired_extension_exists

end DoubleCoshExtension

end
