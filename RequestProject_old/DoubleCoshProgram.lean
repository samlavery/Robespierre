import RequestProject.DoubleCoshRiemannBridge
import RequestProject.RiemannHypothesisBridge

/-!
# Double-Cosh Program — Top-Level Integration

This file integrates the full double-cosh chain, from pair algebra through
Riemann's integral bridge to Mathlib's `RiemannHypothesis`. It exposes the
unconditional infrastructure as named theorems and states the single
remaining open content — **no-offline** — as a clean hypothesis that, when
proved (by any route, including the parallel `no_offline` proof effort),
closes `RiemannHypothesis`.

## The chain

```
                   [no-offline]                 (open, target)
                        |
                        ↓
 ∀ ρ ∈ NontrivialZeros, ρ.re = 1/2              (our internal RH form)
                        |
                        ↓  no_offline_zeros_implies_rh  (unconditional)
                        |
                 RiemannHypothesis              (Mathlib, def)
```

and dually, via the classifier:

```
 R_double(ρ.re, r) = 0 on NontrivialZeros       (classifier balance)
                        ↕  classifier_iff_online  (unconditional biconditional)
 ∀ ρ ∈ NontrivialZeros, ρ.re = 1/2
```

## Infrastructure files

1. **`DoubleCoshResidue`** — classifier factorization:
   `R_double(β, r) = 4·sinh²((β−1/2)·log r)·sinh²((1/2−π/6)·log r)`
2. **`DoubleCoshValidation`** — soundness/completeness against
   `riemannZeta`'s nontrivial zeros. Bidirectional reformulation of RH.
3. **`CoshZetaIntertwiner`** — Klein-180 intertwiner with FE + conjugation.
4. **`RiemannHypothesisBridge`** — bridges our internal `∀ ρ, ρ.re = 1/2`
   to Mathlib's `RiemannHypothesis` predicate.
5. **`DoubleCoshExtension`** — Stage A: complex pair kernel, FE pair
   relation, Schwarz lifts, ψ decomposition.
6. **`DoubleCoshStageB`** — Stage B proved: `finitePairedIntegral_of_odd_vanishes`
   (paired integral annihilates odd ψ).
7. **`DoubleCoshStageC`** — Stage C structural: real-ψ factored form,
   target stated.
8. **`DoubleCoshKernelComparison`** — per-kernel and pair-sum/difference/
   product decompositions; FE-even/odd structure.
9. **`DoubleCoshRiemannBridge`** — the near-collinearity pointer: any
   `cosh((s−1/2)·t)` integral rewrites as paired-cosh integral.

## What's unconditional (no sorry, no custom axioms)

All 9 files above build with axiom footprint `[propext, Classical.choice, Quot.sound]` only.
Specific capstones:

* `classifier_iff_online`: `pairAgreementDefect r ρ.re = 0 ↔ ρ.re = 1/2`
  for `r > 1` on nontrivial zeros.
* `rho_online_iff_residue_zero`: `ρ ∈ OnLineZeros ↔ pairAgreementDefect r ρ.re = 0`.
* `no_offline_zeros_implies_rh`: `(∀ ρ ∈ NontrivialZeros, ρ.re = 1/2) → RiemannHypothesis`.
* `RiemannHypothesis_iff_classifier_balance`: full biconditional.
* `finitePairedIntegral_of_odd_vanishes`: Stage B Condition (3).
* `cosh_shift_half_via_pair`: algebraic inversion for Riemann-style bridge.

## What closes the chain

Any proof of

```
∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2
```

-- via any route (classifier, Riemann bridge, independent no-offline
analysis, parallel GPT proof effort) -- closes `RiemannHypothesis` via
`no_offline_zeros_implies_rh`.
-/

open Complex ZetaDefs DoubleCoshResidue DoubleCoshValidation RHBridge

noncomputable section

namespace DoubleCoshProgram

/-! ### §1. The no-offline hypothesis and its consequence -/

/-- **The open target**: no nontrivial zero is offline. Named hypothesis
so parallel proof efforts can plug in. -/
def NoOfflineZeros : Prop :=
  ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1/2

/-- **Capstone**: `NoOfflineZeros` closes `RiemannHypothesis` unconditionally. -/
theorem RiemannHypothesis_of_no_offline (h : NoOfflineZeros) : RiemannHypothesis :=
  no_offline_zeros_implies_rh h

/-- **Capstone (biconditional)**: `NoOfflineZeros` is equivalent to
`RiemannHypothesis`. -/
theorem NoOfflineZeros_iff_RiemannHypothesis :
    NoOfflineZeros ↔ RiemannHypothesis := by
  constructor
  · exact RiemannHypothesis_of_no_offline
  · intro hRH ρ hρ
    have hne1 : ρ ≠ 1 := by
      intro h
      have := hρ.2.1
      rw [h, Complex.one_re] at this
      linarith
    have hnt : ¬ ∃ n : ℕ, ρ = -2 * (↑n + 1) := by
      rintro ⟨n, hn⟩
      have hre := congr_arg Complex.re hn
      have hcalc : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
        simp [Complex.mul_re]
      rw [hcalc] at hre
      have hpos : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
      linarith [hρ.1]
    exact hRH ρ hρ.2.2 hnt hne1

/-! ### §2. Classifier equivalence — internal RH form ↔ pair-agreement balance -/

/-- **NoOffline ↔ Universal classifier-balance at any single admissible scale**.
The classifier provides a pair-observable restatement of RH. -/
theorem NoOfflineZeros_iff_classifier_balance {r : ℝ} (hr : 1 < r) :
    NoOfflineZeros ↔
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → pairAgreementDefect r ρ.re = 0 := by
  unfold NoOfflineZeros
  constructor
  · intro h ρ hρ
    rw [h ρ hρ]; exact residue_balanced r
  · intro h ρ hρ
    exact (classifier_iff_online ρ hρ hr).mp (h ρ hρ)

/-- **Triple equivalence**: RH, NoOffline, classifier-balance. -/
theorem RH_iff_NoOffline_iff_classifier {r : ℝ} (hr : 1 < r) :
    (RiemannHypothesis ↔ NoOfflineZeros) ∧
    (NoOfflineZeros ↔
      ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → pairAgreementDefect r ρ.re = 0) :=
  ⟨NoOfflineZeros_iff_RiemannHypothesis.symm,
   NoOfflineZeros_iff_classifier_balance hr⟩

/-! ### §3. FE-reflected no-offline form

If no-offline is proved for a zero set, the FE-reflected zero set also
satisfies no-offline — automatic via the classifier's FE-invariance. -/

/-- **FE-closure of no-offline**: if no nontrivial zero is offline, then
no FE-reflected zero is offline either. Automatic via the FE-invariance
of `ZD.NontrivialZeros` (provable from Mathlib's `riemannZeta_one_sub`). -/
theorem NoOffline_fe_stable (h : NoOfflineZeros) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → (1 - ρ).re = 1/2 := by
  intro ρ hρ
  have hre : ρ.re = 1/2 := h ρ hρ
  simp only [Complex.sub_re, Complex.one_re, hre]; norm_num

/-! ### §4. Consumer interface — a single theorem any `no_offline` proof can
hit -/

/-- **The single theorem any proof route should target**: `NoOfflineZeros`.
If you can prove it, this file + `RiemannHypothesisBridge` gives you
`RiemannHypothesis`, no additional work needed.

Parallel proof efforts (GPT working on no-offline, classical analytic
approaches, the paired-cosh bridge when Riemann's ξ-integral is
formalized) all land here. -/
theorem target_theorem : NoOfflineZeros ↔ RiemannHypothesis :=
  NoOfflineZeros_iff_RiemannHypothesis

/-! ### §5. Axiom hygiene -/

#print axioms NoOfflineZeros_iff_RiemannHypothesis
#print axioms NoOfflineZeros_iff_classifier_balance
#print axioms RH_iff_NoOffline_iff_classifier
#print axioms NoOffline_fe_stable
#print axioms target_theorem

end DoubleCoshProgram

end
