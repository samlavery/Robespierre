/-
# RH-Assumption Methods

Definitions and theorems that rely on RH or GRH.
-/

import Mathlib

open Real BigOperators

noncomputable section
namespace RHOFFRHAssumptionMethods
/-! ## Nontrivial zeta zeros -/

def NontrivialZetaZeros : Set ℂ :=
  { s : ℂ | 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 }

/-! ## RH implies critical line -/

theorem rh_implies_critical_line (hRH : RiemannHypothesis) (ρ : ℂ)
    (hρ : ρ ∈ NontrivialZetaZeros) : ρ.re = 1 / 2 := by
  have h0 := hρ.1
  have h1 := hρ.2.1
  have hζ := hρ.2.2
  apply hRH ρ hζ
  · -- ρ is not a trivial zero: trivial zeros have Re ≤ 0, but Re(ρ) > 0
    intro ⟨n, hn⟩
    rw [hn] at h0
    simp at h0
    have := n.cast_nonneg (α := ℝ)
    linarith
  · -- ρ ≠ 1: since Re(ρ) < 1
    intro heq; rw [heq] at h1; simp at h1

/-! ## Envelope sides -/

def envelopeSideLeft (r β : ℝ) : ℝ := r ^ β
def envelopeSideRight (r β : ℝ) : ℝ := r ^ (1 - β)

theorem envelopeSideLeft_under_RH (r : ℝ) :
    envelopeSideLeft r (1/2) = r ^ (1/2 : ℝ) := rfl

theorem envelopeSideRight_under_RH (r : ℝ) :
    envelopeSideRight r (1/2) = r ^ (1/2 : ℝ) := by
  unfold envelopeSideRight; congr 1; ring

/-! ## Excess amplitude -/

def excessAmplitude (r β : ℝ) : ℝ := r ^ β + r ^ (1 - β) - 2 * r ^ (1/2 : ℝ)

theorem excessAmplitude_zero_for_RH_zero (hRH : RiemannHypothesis) (ρ : ℂ)
    (hρ : ρ ∈ NontrivialZetaZeros) (r : ℝ) :
    excessAmplitude r ρ.re = 0 := by
  have hβ := rh_implies_critical_line hRH ρ hρ
  unfold excessAmplitude; rw [hβ]; ring

/-! ## RH-faithful amplitude pipeline -/

def rhFaithfulAmplitude (p : ℕ) (β r : ℝ) : ℝ :=
  Real.cos (↑p * Real.pi / 3) + excessAmplitude r β

theorem rhFaithfulAmplitude_val (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (r : ℝ) :
    rhFaithfulAmplitude p (1/2) r = 1 / 2 := by
  unfold rhFaithfulAmplitude excessAmplitude
  have hcos : Real.cos (↑p * Real.pi / 3) = 1 / 2 := by
    -- Since $p \geq 5$ and prime, $p$ must be congruent to $1$ or $5$ modulo $6$.
    have h_mod : p % 6 = 1 ∨ p % 6 = 5 := by
      by_contra h_contra; have := Nat.Prime.eq_two_or_odd hp; ( have := Nat.dvd_of_mod_eq_zero ( show p % 3 = 0 from by omega ) ; ( rw [ hp.dvd_iff_eq ] at this <;> linarith; ) );
    rw [ ← Nat.mod_add_div p 6 ] ; rcases h_mod with ( h | h ) <;> norm_num [ h, add_mul, mul_assoc, mul_div_assoc, Real.cos_add ];
    · rw [ ← Real.cos_pi_div_three ] ; convert Real.cos_periodic.int_mul ( p / 6 ) _ using 2 ; ring;
      norm_cast;
    · convert Real.cos_pi_div_three using 1 ; ring;
      norm_num [ mul_assoc, mul_comm Real.pi, mul_div ];
      rw [ ← Real.cos_two_pi_sub ] ; ring
  rw [hcos]; ring

/-! ## GRH mod-6 balance -/

def GRH_mod6_balance : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
    |((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => Real.sin (↑p * Real.pi / 3))| ≤ C * Real.sqrt N * Real.log N

theorem grh_implies_imaginary_bound (hGRH : GRH_mod6_balance) :
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
      |((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
        (fun p => Real.sin (↑p * Real.pi / 3))| ≤ C * Real.sqrt N * Real.log N :=
  hGRH

end  RHOFFRHAssumptionMethods
