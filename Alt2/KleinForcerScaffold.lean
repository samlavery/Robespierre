import Mathlib
import RequestProject.HarmonicDiagnostics
import RequestProject.EnergyDefect
import RequestProject.ZetaZeroDefs
import RequestProject.OfflineAmplitudeMethods
import RequestProject.PairCoshGaussTest
import RequestProject.GaussianDetectorPair
import RequestProject.WeilContour
import RequestProject.WeilRightEdgePrimeSum
import RequestProject.WeilCoshPairPositivity
import RequestProject.WeilFinalAssembly
import RequestProject.WeilExplicitFormulaFromPerC
import RequestProject.ExplicitFormulaBridgeOfRH
import RequestProject.GaussianClosedForm

/-!
# Klein-4 cosh-side primitives

Cosh has 1/2 as a topological midpoint. Cosh by itself **knows nothing about
RH** — it cannot witness which `β` values appear as `ρ.re` for nontrivial
zeros, nor whether any specific reading vanishes. Every theorem of the form
"vanishing of cosh-quantity ⟹ ρ.re = 1/2" is just cosh-midpoint geometry
(`amplitudeDefect r β = 0 ⟺ β = 1/2`), with no number-theoretic content.

This file therefore retains only:

1. **Klein-4-orbit closed form** (`kleinOrbitContribution_excess`) —
   algebraic identity expressing the orbit-summed offline excess at prime `p`
   in terms of `amplitudeDefect p ρ.re` and `cos(ρ.im · log p)`.
2. **Per-prime AM-GM lower bound** (`perZeroEnvelope_ge_noDefect`) —
   envelope `p^β + p^{1-β} ≥ 2 p^{1/2}` at every prime, AM-GM unconditional.
3. **Positive-cone primitive** (`totalAmplitudeDefectAtPrime_nonneg`) —
   un-cosined sum of nonneg defects is nonneg.
4. **Transcendence primitives** (`log_two_three_lin_indep`,
   `not_cos_log_two_three_zero`) — number-theoretic facts about primes 2, 3
   that are independent of cosh's midpoint structure.

The trap-shaped forcer wrappers (any `(cosh-quantity = 0) → ρ.re = 1/2`
package, with or without `NontrivialZeros` decoration) have been removed
because cosh's midpoint geometry doesn't see ζ. RH closure requires
analytic content beyond cosh — Weil-side identity content that defeats
per-test conspiracy.

The closed forms and primitives above are useful as building blocks for
any future Weil-side construction.
-/

open ZD ZD.WeilPositivity ZetaDefs

noncomputable section

namespace ZD
namespace WeilPositivity
namespace KleinForcer

/-! ## §1. Definitions -/

/-- The "no-defect" prime harmonic at `p`: the AM-GM lower bound `2·p^{1/2}`. -/
def noDefectHarmonic (p : ℕ) : ℝ := 2 * (p : ℝ) ^ ((1 : ℝ) / 2)

/-- Per-zero envelope at prime `p`: `p^{ρ.re} + p^{1-ρ.re}` (FE-symmetric). -/
def perZeroEnvelope (p : ℕ) (ρ : ℂ) : ℝ :=
  (p : ℝ) ^ (ρ.re) + (p : ℝ) ^ (1 - ρ.re)

/-- Klein-4-orbit-summed spectral contribution at prime `p` for zero `ρ`.
For `ρ = β + iγ` the orbit `{ρ, ρ̄, 1-ρ, 1-ρ̄}` summed gives
`2 (p^β + p^{1-β}) · cos(γ · log p)`. -/
def kleinOrbitContribution (p : ℕ) (ρ : ℂ) : ℝ :=
  2 * perZeroEnvelope p ρ * Real.cos (ρ.im * Real.log p)

/-- Un-cosined per-prime defect summed over a finite zero set. -/
def totalAmplitudeDefectAtPrime (p : ℕ) (Z : Finset ℂ) : ℝ :=
  ∑ ρ ∈ Z, amplitudeDefect (p : ℝ) ρ.re


/-- **Per-prime amplitude bridge.**  At any scale `r > 0`, the
amplitude defect equals the balanced envelope times the cosh excess
`coshDetector β (log r) − 1`. -/
theorem amplitudeDefect_eq_balanced_mul_coshExcess
    {r : ℝ} (hr : 0 < r) (β : ℝ) :
    amplitudeDefect r β =
      balancedEnvelope r * (coshDetector β (Real.log r) - 1) := by
  have h := defect_eq_balanced_mul_diff hr β
  unfold harmonicDiffPiThird at h
  exact h


/-! ## §2. AM-GM lower bound (cosh-midpoint geometry, unconditional) -/

/-- **AM-GM lower bound**: at every prime `p > 0`,
`noDefectHarmonic p ≤ perZeroEnvelope p ρ`. Pure cosh-geometry. -/
theorem perZeroEnvelope_ge_noDefect {p : ℕ} (hp : 0 < p) (ρ : ℂ) :
    noDefectHarmonic p ≤ perZeroEnvelope p ρ := by
  unfold noDefectHarmonic perZeroEnvelope
  have hp' : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  have hAD := amplitudeDefect_nonneg hp' ρ.re
  unfold amplitudeDefect zeroPairEnvelope balancedEnvelope at hAD
  linarith

/-! ## §3. Klein-4 orbit closed form -/

/-- **Closed-form per-prime offline excess (Klein-4-orbit).** The orbit-summed
contribution minus the balanced contribution is
`2 · amplitudeDefect p ρ.re · cos(ρ.im · log p)`. Algebraic identity. -/
theorem kleinOrbitContribution_excess (p : ℕ) (ρ : ℂ) :
    kleinOrbitContribution p ρ -
        2 * noDefectHarmonic p * Real.cos (ρ.im * Real.log p) =
      2 * amplitudeDefect (p : ℝ) ρ.re * Real.cos (ρ.im * Real.log p) := by
  unfold kleinOrbitContribution noDefectHarmonic perZeroEnvelope
    amplitudeDefect zeroPairEnvelope balancedEnvelope
  ring

/-! ## §4. Positive-cone primitive (un-cosined, ≥ 0 always) -/

theorem totalAmplitudeDefectAtPrime_nonneg {p : ℕ} (hp : 0 < p) (Z : Finset ℂ) :
    0 ≤ totalAmplitudeDefectAtPrime p Z := by
  unfold totalAmplitudeDefectAtPrime
  refine Finset.sum_nonneg (fun ρ _ => ?_)
  exact amplitudeDefect_nonneg (Nat.cast_pos.mpr hp) ρ.re

/-! ## §5. Transcendence primitives (number theory of primes 2, 3)

These are **genuinely number-theoretic** — independent of cosh's midpoint
geometry. They follow from unique factorization (no transcendence theory
beyond `2^a ≠ 3^b` for nonzero integers). -/

/-- **Linear independence of `log 2` and `log 3` over `ℤ`.**
If integers `a`, `b` satisfy `a · log 2 = b · log 3`, then `a = b = 0`. -/
lemma log_two_three_lin_indep (a b : ℤ) (h : (a : ℝ) * Real.log 2 = (b : ℝ) * Real.log 3) :
    a = 0 ∧ b = 0 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  by_cases ha : a = 0
  · subst ha
    have h0 : (b : ℝ) * Real.log 3 = 0 := by
      have : (0 : ℝ) * Real.log 2 = (b : ℝ) * Real.log 3 := by exact_mod_cast h
      linarith
    have : (b : ℝ) = 0 := (mul_eq_zero.mp h0).resolve_right (ne_of_gt hlog3)
    have : b = 0 := by exact_mod_cast this
    exact ⟨rfl, this⟩
  by_cases hb : b = 0
  · subst hb
    have h0 : (a : ℝ) * Real.log 2 = 0 := by
      have : (a : ℝ) * Real.log 2 = (0 : ℝ) * Real.log 3 := by exact_mod_cast h
      linarith
    have : (a : ℝ) = 0 := (mul_eq_zero.mp h0).resolve_right (ne_of_gt hlog2)
    have : a = 0 := by exact_mod_cast this
    exact ⟨this, rfl⟩
  exfalso
  have hab_pos : (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by
    rcases lt_or_gt_of_ne ha with ha_neg | ha_pos
    · rcases lt_or_gt_of_ne hb with hb_neg | hb_pos
      · exact Or.inr ⟨ha_neg, hb_neg⟩
      · exfalso
        have h1 : (a : ℝ) * Real.log 2 < 0 :=
          mul_neg_of_neg_of_pos (by exact_mod_cast ha_neg) hlog2
        have h2 : 0 < (b : ℝ) * Real.log 3 :=
          mul_pos (by exact_mod_cast hb_pos) hlog3
        linarith
    · rcases lt_or_gt_of_ne hb with hb_neg | hb_pos
      · exfalso
        have h1 : 0 < (a : ℝ) * Real.log 2 :=
          mul_pos (by exact_mod_cast ha_pos) hlog2
        have h2 : (b : ℝ) * Real.log 3 < 0 :=
          mul_neg_of_neg_of_pos (by exact_mod_cast hb_neg) hlog3
        linarith
      · exact Or.inl ⟨ha_pos, hb_pos⟩
  have h_pos_pos : ∃ (m n : ℕ), 0 < m ∧ 0 < n ∧ (m : ℝ) * Real.log 2 = (n : ℝ) * Real.log 3 := by
    rcases hab_pos with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · refine ⟨a.toNat, b.toNat, by omega, by omega, ?_⟩
      have ha_eq : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by
        have : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha'.le
        exact_mod_cast this
      have hb_eq : ((b.toNat : ℕ) : ℝ) = (b : ℝ) := by
        have : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb'.le
        exact_mod_cast this
      rw [ha_eq, hb_eq]; exact h
    · refine ⟨(-a).toNat, (-b).toNat, by omega, by omega, ?_⟩
      have ha_eq : (((-a).toNat : ℕ) : ℝ) = (-a : ℝ) := by
        have : ((-a).toNat : ℤ) = -a := Int.toNat_of_nonneg (by linarith)
        exact_mod_cast this
      have hb_eq : (((-b).toNat : ℕ) : ℝ) = (-b : ℝ) := by
        have : ((-b).toNat : ℤ) = -b := Int.toNat_of_nonneg (by linarith)
        exact_mod_cast this
      rw [ha_eq, hb_eq]; linarith
  obtain ⟨m, n, hm, hn, heq⟩ := h_pos_pos
  have e2 : ((m : ℝ) * Real.log 2) = Real.log ((2 : ℝ)^m) := by rw [Real.log_pow]
  have e3 : ((n : ℝ) * Real.log 3) = Real.log ((3 : ℝ)^n) := by rw [Real.log_pow]
  have hexp : (2 : ℝ)^m = (3 : ℝ)^n := by
    have h2pos : (0 : ℝ) < (2 : ℝ)^m := by positivity
    have h3pos : (0 : ℝ) < (3 : ℝ)^n := by positivity
    have heq' : Real.log ((2 : ℝ)^m) = Real.log ((3 : ℝ)^n) := by rw [← e2, ← e3]; exact heq
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr h2pos) (Set.mem_Ioi.mpr h3pos) heq'
  have hnat : (2 : ℕ)^m = (3 : ℕ)^n := by exact_mod_cast hexp
  have hdvd : (2 : ℕ) ∣ (3 : ℕ)^n := by
    rw [← hnat]; exact dvd_pow_self _ (Nat.pos_iff_ne_zero.mp hm)
  have : (2 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
  omega

/-- **No real `γ` simultaneously zeros `cos(γ · log 2)` and `cos(γ · log 3)`.**
Cosine vanishing at both `log 2` and `log 3` would force `γ` to satisfy
incompatible rational relations to `π`, ruling out by linear independence
of `{log 2, log 3}` over `ℤ`. -/
lemma not_cos_log_two_three_zero (γ : ℝ) :
    ¬ (Real.cos (γ * Real.log 2) = 0 ∧ Real.cos (γ * Real.log 3) = 0) := by
  rintro ⟨h2, h3⟩
  rw [Real.cos_eq_zero_iff] at h2 h3
  obtain ⟨k, hk⟩ := h2
  obtain ⟨k', hk'⟩ := h3
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hcross : (2 * (k' : ℝ) + 1) * (2 * γ * Real.log 2) =
                (2 * (k : ℝ) + 1) * (2 * γ * Real.log 3) := by
    have h2γ2 : 2 * γ * Real.log 2 = (2 * (k : ℝ) + 1) * Real.pi := by linarith
    have h2γ3 : 2 * γ * Real.log 3 = (2 * (k' : ℝ) + 1) * Real.pi := by linarith
    rw [h2γ2, h2γ3]; ring
  have hγ_factor : 2 * γ * ((2 * (k' : ℝ) + 1) * Real.log 2 -
                            (2 * (k : ℝ) + 1) * Real.log 3) = 0 := by
    have : (2 * (k' : ℝ) + 1) * (2 * γ * Real.log 2) -
           (2 * (k : ℝ) + 1) * (2 * γ * Real.log 3) = 0 := by linarith
    linarith
  have hγ_ne : γ ≠ 0 := by
    intro hγ0
    rw [hγ0] at hk
    have h0 : (2 * (k : ℝ) + 1) * Real.pi / 2 = 0 := by linarith
    have h1 : (2 * (k : ℝ) + 1) * Real.pi = 0 := by linarith
    have h2 : 2 * (k : ℝ) + 1 = 0 := by
      rcases mul_eq_zero.mp h1 with hcase | hcase
      · exact hcase
      · exact absurd hcase hπ
    have : (2 * k + 1 : ℤ) = 0 := by exact_mod_cast h2
    omega
  have hlinrel : (2 * (k' : ℝ) + 1) * Real.log 2 - (2 * (k : ℝ) + 1) * Real.log 3 = 0 := by
    have h2γ_ne : (2 * γ : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hγ_ne
    rcases mul_eq_zero.mp hγ_factor with hcase | hcase
    · exact absurd hcase h2γ_ne
    · exact hcase
  have hrel : ((2 * k' + 1 : ℤ) : ℝ) * Real.log 2 = ((2 * k + 1 : ℤ) : ℝ) * Real.log 3 := by
    push_cast; linarith
  obtain ⟨_, hkeq⟩ := log_two_three_lin_indep _ _ hrel
  omega

end KleinForcer
end WeilPositivity
end ZD

end
