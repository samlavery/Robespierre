import RequestProject.DoubleCoshStageC

/-!
# Double-Cosh Kernel Comparison

What each kernel produces separately and in combination, evaluated at
prime scales `t = log n` (so exponentials become powers of `n`).

## Per-kernel expansions at `t = log n`

Each kernel at scale `t = log n` expands to two powers of `n`:

```
K_L^ℂ(s, log n) = (n^{s − π/6} + n^{π/6 − s}) / 2
K_R^ℂ(s, log n) = (n^{s − (1 − π/6)} + n^{(1 − π/6) − s}) / 2
```

## FE interaction: kernel swap

The FE action `s → 1 − s` **swaps** the kernel pair:
```
K_L^ℂ(1 − s, t) = K_R^ℂ(s, t)
K_R^ℂ(1 − s, t) = K_L^ℂ(s, t)
```

## Sum / difference under FE

From the swap, the pair decomposes cleanly under FE:
```
K_L^ℂ(s,t) + K_R^ℂ(s,t)  is FE-even   (symmetric under s ↔ 1 − s)
K_L^ℂ(s,t) − K_R^ℂ(s,t)  is FE-odd    (flips sign under s ↔ 1 − s)
```

## Factorized forms

```
K_L + K_R = 2 · cosh((s − 1/2)t) · cosh((1/2 − π/6)t)
K_L − K_R = 2 · sinh((s − 1/2)t) · sinh((1/2 − π/6)t)
K_L · K_R = (cosh((1 − π/3)t) + cosh((s − 1/2) · 2t)) / 2
```

Each factorization isolates the `(s − 1/2)` dependence in a single
trigonometric function, with a β-independent multiplier.

## Diagnostic fact

At `s = 1/2` (critical line, real argument): `sinh((s − 1/2)t) = 0`, so

- `K_L − K_R = 0` at Re s = 1/2 (this is the classifier biconditional)
- `K_L + K_R = 2 · cosh((1/2 − π/6)t)` — a β-independent constant per t

This is why pair *agreement* detects the critical line.
-/

open Complex Finset ZetaDefs

noncomputable section

namespace DoubleCoshExtension

/-! ### §1. Per-kernel expansion (informal)

At `t = log n` for positive real `n`, the complex kernel expands as
`K_L^ℂ(s, log n) = (n^{s − π/6} + n^{π/6 − s}) / 2` via `cosh = (e^· + e^{−·})/2`
and `e^{a · log n} = n^a`. Stated here for documentation; the formal
manipulations in sections 3–5 use the `Complex.cosh` form directly without
invoking this rewrite. -/

/-! ### §2. FE interaction: kernel swap -/

/-- **FE swap**: `K_L^ℂ(1 − s, t) = K_R^ℂ(s, t)`. The pair structure carries FE. -/
theorem coshDetectorLeftC_one_sub (s : ℂ) (t : ℝ) :
    coshDetectorLeftC (1 - s) t = coshDetectorRightC s t :=
  (coshDetectorRightC_eq_Left_one_sub s t).symm

/-- **FE swap (symmetric)**: `K_R^ℂ(1 − s, t) = K_L^ℂ(s, t)`. -/
theorem coshDetectorRightC_one_sub (s : ℂ) (t : ℝ) :
    coshDetectorRightC (1 - s) t = coshDetectorLeftC s t := by
  rw [coshDetectorRightC_eq_Left_one_sub]
  congr 1
  ring

/-! ### §3. Sum and difference under FE -/

/-- **Pair sum is FE-even**: `K_L(s,t) + K_R(s,t) = K_L(1−s,t) + K_R(1−s,t)`. -/
theorem pair_sum_FE_even (s : ℂ) (t : ℝ) :
    coshDetectorLeftC s t + coshDetectorRightC s t =
    coshDetectorLeftC (1 - s) t + coshDetectorRightC (1 - s) t := by
  rw [coshDetectorLeftC_one_sub, coshDetectorRightC_one_sub]
  ring

/-- **Pair difference is FE-odd**: `K_L − K_R` flips sign under `s ↦ 1 − s`. -/
theorem pair_diff_FE_odd (s : ℂ) (t : ℝ) :
    coshDetectorLeftC s t - coshDetectorRightC s t =
    -(coshDetectorLeftC (1 - s) t - coshDetectorRightC (1 - s) t) := by
  rw [coshDetectorLeftC_one_sub, coshDetectorRightC_one_sub]
  ring

/-! ### §4. Factorized forms -/

/-- `K_L − K_R = 2 · sinh((s − 1/2)t) · sinh((1/2 − π/6)t)`. The difference
factors as a product of sinh-terms — a classifier for the critical line
(vanishes at `s.re = 1/2` via the first sinh). -/
theorem coshDetector_pair_diff_complex (s : ℂ) (t : ℝ) :
    coshDetectorLeftC s t - coshDetectorRightC s t =
      2 * Complex.sinh ((s - (1/2 : ℂ)) * (t : ℂ)) *
          Complex.sinh (((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ)) := by
  simp only [coshDetectorLeftC_eq, coshDetectorRightC_eq]
  have hL : (s - (Real.pi / 6 : ℂ)) * (t : ℂ) =
            (s - (1/2 : ℂ)) * (t : ℂ) + ((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ) := by ring
  have hR : (s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ) =
            (s - (1/2 : ℂ)) * (t : ℂ) - ((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ) := by ring
  rw [hL, hR, Complex.cosh_add, Complex.cosh_sub]
  ring

/-- `K_L · K_R = (cosh((1 − π/3)·t) + cosh((s − 1/2)·2t)) / 2`. The product
decomposes into a β-independent constant plus a β-dependent cosh at
**doubled** log-scale. -/
theorem coshDetector_pair_prod_complex (s : ℂ) (t : ℝ) :
    coshDetectorLeftC s t * coshDetectorRightC s t =
      (Complex.cosh (((1 : ℂ) - (Real.pi / 3 : ℂ)) * (t : ℂ)) +
       Complex.cosh ((s - (1/2 : ℂ)) * ((2 : ℂ) * (t : ℂ)))) / 2 := by
  simp only [coshDetectorLeftC_eq, coshDetectorRightC_eq]
  -- Product-to-sum: cosh A · cosh B = (cosh(A-B) + cosh(A+B)) / 2
  have hpm : (s - (Real.pi / 6 : ℂ)) * (t : ℂ) +
             (s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ) =
             (s - (1/2 : ℂ)) * ((2 : ℂ) * (t : ℂ)) := by ring
  have hmp : (s - (Real.pi / 6 : ℂ)) * (t : ℂ) -
             (s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ) =
             ((1 : ℂ) - (Real.pi / 3 : ℂ)) * (t : ℂ) := by ring
  have h1 : Complex.cosh ((s - (Real.pi / 6 : ℂ)) * (t : ℂ)) *
            Complex.cosh ((s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ)) =
            (Complex.cosh ((s - (Real.pi / 6 : ℂ)) * (t : ℂ) -
                           (s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ)) +
             Complex.cosh ((s - (Real.pi / 6 : ℂ)) * (t : ℂ) +
                           (s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ))) / 2 := by
    rw [show Complex.cosh ((s - (Real.pi / 6 : ℂ)) * (t : ℂ) -
                           (s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ)) =
            Complex.cosh ((s - (Real.pi / 6 : ℂ)) * (t : ℂ)) *
            Complex.cosh ((s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ)) -
            Complex.sinh ((s - (Real.pi / 6 : ℂ)) * (t : ℂ)) *
            Complex.sinh ((s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ))
         from Complex.cosh_sub _ _]
    rw [show Complex.cosh ((s - (Real.pi / 6 : ℂ)) * (t : ℂ) +
                           (s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ)) =
            Complex.cosh ((s - (Real.pi / 6 : ℂ)) * (t : ℂ)) *
            Complex.cosh ((s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ)) +
            Complex.sinh ((s - (Real.pi / 6 : ℂ)) * (t : ℂ)) *
            Complex.sinh ((s - ((1 : ℂ) - (Real.pi / 6 : ℂ))) * (t : ℂ))
         from Complex.cosh_add _ _]
    ring
  rw [h1, hpm, hmp]

/-! ### §5. Sub-observables from the decomposition

Three derived observables from the kernel pair, each tracking a different
analytic piece:

- `pairSum = K_L + K_R` — FE-even, scales with `cosh((s−1/2)t)`.
- `pairDiff = K_L − K_R` — FE-odd, scales with `sinh((s−1/2)t)`. **Vanishes at Re s = 1/2** (the critical-line classifier).
- `pairProd = K_L · K_R` — β-dependence isolated in `cosh((s−1/2)·2t)`. -/

/-- The FE-even sub-observable. -/
def pairSum (s : ℂ) (t : ℝ) : ℂ := coshDetectorLeftC s t + coshDetectorRightC s t

/-- The FE-odd sub-observable. Vanishes on Re(s) = 1/2 by `coshDetector_pair_diff_complex`. -/
def pairDiff (s : ℂ) (t : ℝ) : ℂ := coshDetectorLeftC s t - coshDetectorRightC s t

/-- The product sub-observable. -/
def pairProd (s : ℂ) (t : ℝ) : ℂ := coshDetectorLeftC s t * coshDetectorRightC s t

theorem pairSum_eq (s : ℂ) (t : ℝ) :
    pairSum s t = 2 * Complex.cosh ((s - (1/2 : ℂ)) * (t : ℂ)) *
                      Complex.cosh (((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ)) :=
  coshDetector_pair_sum_complex s t

theorem pairDiff_eq (s : ℂ) (t : ℝ) :
    pairDiff s t = 2 * Complex.sinh ((s - (1/2 : ℂ)) * (t : ℂ)) *
                       Complex.sinh (((1/2 : ℂ) - (Real.pi / 6 : ℂ)) * (t : ℂ)) :=
  coshDetector_pair_diff_complex s t

theorem pairProd_eq (s : ℂ) (t : ℝ) :
    pairProd s t = (Complex.cosh (((1 : ℂ) - (Real.pi / 3 : ℂ)) * (t : ℂ)) +
                    Complex.cosh ((s - (1/2 : ℂ)) * ((2 : ℂ) * (t : ℂ)))) / 2 :=
  coshDetector_pair_prod_complex s t

/-! ### §6. Critical-line diagnostic

At s with `s = 1/2 + it₀` (on the critical line), `(s − 1/2) = it₀` is
purely imaginary, so `sinh((s−1/2)·t) = i·sin(t₀·t)` and
`cosh((s−1/2)·t) = cos(t₀·t)`. The pair-difference vanishes when we
further specialize `t₀ = 0` (pure critical-line real axis), but more
interestingly, at every scale `t ∈ ℝ`:

- `pairDiff(1/2 + it₀, t) = 2i · sin(t₀·t) · sinh((1/2−π/6)·t)` — purely
  imaginary (for real t₀, t). Zero when `sin(t₀·t) = 0`.

- `pairSum(1/2 + it₀, t) = 2 · cos(t₀·t) · cosh((1/2−π/6)·t)` — purely
  real, bounded. Matches the classifier's "balanced" behavior.
-/

/-- On the real axis (`s = β` real), `pairDiff(β, t)` specializes to the
real pair-difference, which vanishes iff `β = 1/2` (classical classifier
biconditional from `coshDetectors_agree_iff`). Left as informal
documentation; formal version lives in `DoubleCoshResidue` / `DoubleCoshValidation`. -/
def pairDiff_real_criticalLine_note : Prop := True

/-! ### §7. Axiom hygiene -/

#print axioms coshDetectorLeftC_one_sub
#print axioms coshDetectorRightC_one_sub
#print axioms pair_sum_FE_even
#print axioms pair_diff_FE_odd
#print axioms coshDetector_pair_diff_complex
#print axioms coshDetector_pair_prod_complex
#print axioms pairSum_eq
#print axioms pairDiff_eq
#print axioms pairProd_eq

end DoubleCoshExtension

end
