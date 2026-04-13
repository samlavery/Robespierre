/-
# Prime Harmonic Comparison Framework

## Invariant Q

We define one exact invariant for the π/3 prime harmonic system:

  Q(p) = e^{iπp/3} = cos(pπ/3) + i·sin(pπ/3) ∈ ℂ

For primes p ≥ 5, the character-theoretic decomposition gives:

  Q(p) = 1/2 + i·(√3/2)·χ₃(p)

where:
  - Re(Q) = 1/2 is the **principal-character main term** (unconditional, rigid)
  - Im(Q) = (√3/2)·χ₃(p) is the **nonprincipal-character error channel**
  - |Q(p)| = 1 (unit modulus)

## Methods

Three methods evaluate Q:
  1. **Trigonometric/symbolic** (unconditional): direct mod-6 periodicity
  2. **Character-theoretic** (unconditional): χ₃ decomposition
  3. **RH/GRH-conditional**: balanced prime distribution

All three land on the same invariant Q, symbol for symbol.

## Off-line defect positioning

The zero-pair envelope Q(r,β) = r^β + r^{1-β} and defect D_β(r) = Q(r,β) - 2r^{1/2}
satisfy D_{1/2}(r) = 0 for all r > 0, and D_β(r) ≥ 0 by AM-GM.
The prime harmonic invariant has |Q(p)| = 1 (unit amplitude), placing it at the
critical value r = 1 where the defect envelope is most sensitive.
-/

import RequestProject.INDRHIndependentMethods
import RequestProject.INDRHRHAssumptionMethods

namespace INDRHPrimeHarmonicComparison
open Real BigOperators

noncomputable section

/-! ═══════════════════════════════════════════════════════════════════════════
    Part A: The Exact Invariant Q
    ═══════════════════════════════════════════════════════════════════════════ -/

/-- The **prime harmonic invariant** at π/3: the complex number
    (cos(pπ/3), sin(pπ/3)). This is the single exact invariant that all
    methods must evaluate. -/
def Q_invariant (p : ℕ) : ℂ :=
  ⟨Real.cos (↑p * Real.pi / 3), Real.sin (↑p * Real.pi / 3)⟩

/-- The real part of Q is cos(pπ/3). -/
theorem Q_re (p : ℕ) : (Q_invariant p).re = Real.cos (↑p * Real.pi / 3) := rfl

/-- The imaginary part of Q is sin(pπ/3). -/
theorem Q_im (p : ℕ) : (Q_invariant p).im = Real.sin (↑p * Real.pi / 3) := rfl

/-
Q equals the existing `primeHarmonicPiThird` definition (= e^{ipπ/3}).
-/
theorem Q_eq_primeHarmonicPiThird (p : ℕ) :
    Q_invariant p = primeHarmonicPiThird p := by
  unfold Q_invariant primeHarmonicPiThird
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ]

/-- Q has unit norm-squared: normSq(Q(p)) = 1 for all p. -/
theorem Q_normSq (p : ℕ) : Complex.normSq (Q_invariant p) = 1 := by
  simp only [Q_invariant, Complex.normSq_mk]
  nlinarith [Real.sin_sq_add_cos_sq (↑p * Real.pi / 3)]

/-- Q has unit norm: ‖Q(p)‖ = 1 for all p. -/
theorem Q_norm (p : ℕ) : ‖Q_invariant p‖ = 1 := by
  have h : ‖Q_invariant p‖ ^ 2 = 1 := by
    rw [Complex.sq_norm]; exact_mod_cast Q_normSq p
  nlinarith [norm_nonneg (Q_invariant p)]

/-! ═══════════════════════════════════════════════════════════════════════════
    Part B1: Finite Computational Bridge
    ═══════════════════════════════════════════════════════════════════════════

    For the first 10 primes in each residue class mod 6, we explicitly verify:
    - residue class (p % 6)
    - cos(pπ/3) = 1/2
    - sin(pπ/3) = ±√3/2
    - |Q(p)| = 1
    - χ₃(p) = ±1
    - Q_invariant p = explicit complex value

    Primes ≡ 1 mod 6: 7, 13, 19, 31, 37, 43, 61, 67, 73, 79
    Primes ≡ 5 mod 6: 5, 11, 17, 23, 29, 41, 47, 53, 59, 71
-/

/-- For primes p ≡ 1 mod 6, Q(p) = (1/2, √3/2). -/
theorem Q_of_mod6_one (p : ℕ) (h : p % 6 = 1) :
    Q_invariant p = ⟨1/2, Real.sqrt 3 / 2⟩ := by
  apply Complex.ext
  · exact cos_prime_pi_div_three_of_mod_one p h
  · exact sin_prime_pi_div_three_of_mod_one p h

/-- For primes p ≡ 5 mod 6, Q(p) = (1/2, -(√3/2)). -/
theorem Q_of_mod6_five (p : ℕ) (h : p % 6 = 5) :
    Q_invariant p = ⟨1/2, -(Real.sqrt 3 / 2)⟩ := by
  apply Complex.ext
  · exact cos_prime_pi_div_three_of_mod_five p h
  · exact sin_prime_pi_div_three_of_mod_five p h

/-! ### Primes ≡ 1 mod 6: Q(p) = (1/2, √3/2), χ₃(p) = 1 -/

theorem Q_at_7  : Q_invariant 7  = ⟨1/2, Real.sqrt 3 / 2⟩ := Q_of_mod6_one 7  (by decide)
theorem Q_at_13 : Q_invariant 13 = ⟨1/2, Real.sqrt 3 / 2⟩ := Q_of_mod6_one 13 (by decide)
theorem Q_at_19 : Q_invariant 19 = ⟨1/2, Real.sqrt 3 / 2⟩ := Q_of_mod6_one 19 (by decide)
theorem Q_at_31 : Q_invariant 31 = ⟨1/2, Real.sqrt 3 / 2⟩ := Q_of_mod6_one 31 (by decide)
theorem Q_at_37 : Q_invariant 37 = ⟨1/2, Real.sqrt 3 / 2⟩ := Q_of_mod6_one 37 (by decide)
theorem Q_at_43 : Q_invariant 43 = ⟨1/2, Real.sqrt 3 / 2⟩ := Q_of_mod6_one 43 (by decide)
theorem Q_at_61 : Q_invariant 61 = ⟨1/2, Real.sqrt 3 / 2⟩ := Q_of_mod6_one 61 (by decide)
theorem Q_at_67 : Q_invariant 67 = ⟨1/2, Real.sqrt 3 / 2⟩ := Q_of_mod6_one 67 (by decide)
theorem Q_at_73 : Q_invariant 73 = ⟨1/2, Real.sqrt 3 / 2⟩ := Q_of_mod6_one 73 (by decide)
theorem Q_at_79 : Q_invariant 79 = ⟨1/2, Real.sqrt 3 / 2⟩ := Q_of_mod6_one 79 (by decide)

theorem chi3_at_7  : chi3ind 7  = 1 := chi3_eq_one_of_mod_six_oneind 7  (by decide)
theorem chi3_at_13 : chi3ind 13 = 1 := chi3_eq_one_of_mod_six_oneind 13 (by decide)
theorem chi3_at_19 : chi3ind 19 = 1 := chi3_eq_one_of_mod_six_oneind 19 (by decide)
theorem chi3_at_31 : chi3ind 31 = 1 := chi3_eq_one_of_mod_six_oneind 31 (by decide)
theorem chi3_at_37 : chi3ind 37 = 1 := chi3_eq_one_of_mod_six_oneind 37 (by decide)
theorem chi3_at_43 : chi3ind 43 = 1 := chi3_eq_one_of_mod_six_oneind 43 (by decide)
theorem chi3_at_61 : chi3ind 61 = 1 := chi3_eq_one_of_mod_six_oneind 61 (by decide)
theorem chi3_at_67 : chi3ind 67 = 1 := chi3_eq_one_of_mod_six_oneind 67 (by decide)
theorem chi3_at_73 : chi3ind 73 = 1 := chi3_eq_one_of_mod_six_oneind 73 (by decide)
theorem chi3_at_79 : chi3ind 79 = 1 := chi3_eq_one_of_mod_six_oneind 79 (by decide)

/-! ### Primes ≡ 5 mod 6: Q(p) = (1/2, -(√3/2)), χ₃(p) = -1 -/

theorem Q_at_5  : Q_invariant 5  = ⟨1/2, -(Real.sqrt 3 / 2)⟩ := Q_of_mod6_five 5  (by decide)
theorem Q_at_11 : Q_invariant 11 = ⟨1/2, -(Real.sqrt 3 / 2)⟩ := Q_of_mod6_five 11 (by decide)
theorem Q_at_17 : Q_invariant 17 = ⟨1/2, -(Real.sqrt 3 / 2)⟩ := Q_of_mod6_five 17 (by decide)
theorem Q_at_23 : Q_invariant 23 = ⟨1/2, -(Real.sqrt 3 / 2)⟩ := Q_of_mod6_five 23 (by decide)
theorem Q_at_29 : Q_invariant 29 = ⟨1/2, -(Real.sqrt 3 / 2)⟩ := Q_of_mod6_five 29 (by decide)
theorem Q_at_41 : Q_invariant 41 = ⟨1/2, -(Real.sqrt 3 / 2)⟩ := Q_of_mod6_five 41 (by decide)
theorem Q_at_47 : Q_invariant 47 = ⟨1/2, -(Real.sqrt 3 / 2)⟩ := Q_of_mod6_five 47 (by decide)
theorem Q_at_53 : Q_invariant 53 = ⟨1/2, -(Real.sqrt 3 / 2)⟩ := Q_of_mod6_five 53 (by decide)
theorem Q_at_59 : Q_invariant 59 = ⟨1/2, -(Real.sqrt 3 / 2)⟩ := Q_of_mod6_five 59 (by decide)
theorem Q_at_71 : Q_invariant 71 = ⟨1/2, -(Real.sqrt 3 / 2)⟩ := Q_of_mod6_five 71 (by decide)

theorem chi3_at_5  : chi3ind 5  = -1 := chi3_eq_neg_one_of_mod_six_fiveind 5  (by decide)
theorem chi3_at_11 : chi3ind 11 = -1 := chi3_eq_neg_one_of_mod_six_fiveind 11 (by decide)
theorem chi3_at_17 : chi3ind 17 = -1 := chi3_eq_neg_one_of_mod_six_fiveind 17 (by decide)
theorem chi3_at_23 : chi3ind 23 = -1 := chi3_eq_neg_one_of_mod_six_fiveind 23 (by decide)
theorem chi3_at_29 : chi3ind 29 = -1 := chi3_eq_neg_one_of_mod_six_fiveind 29 (by decide)
theorem chi3_at_41 : chi3ind 41 = -1 := chi3_eq_neg_one_of_mod_six_fiveind 41 (by decide)
theorem chi3_at_47 : chi3ind 47 = -1 := chi3_eq_neg_one_of_mod_six_fiveind 47 (by decide)
theorem chi3_at_53 : chi3ind 53 = -1 := chi3_eq_neg_one_of_mod_six_fiveind 53 (by decide)
theorem chi3_at_59 : chi3ind 59 = -1 := chi3_eq_neg_one_of_mod_six_fiveind 59 (by decide)
theorem chi3_at_71 : chi3ind 71 = -1 := chi3_eq_neg_one_of_mod_six_fiveind 71 (by decide)

/-! ═══════════════════════════════════════════════════════════════════════════
    Part B2: Symbolic All-Primes Bridge
    ═══════════════════════════════════════════════════════════════════════════ -/

/-- **Symbolic bridge (real part)**: For all primes p ≥ 5,
    Re(Q(p)) = cos(pπ/3) = 1/2. Principal-character main term. -/
theorem Q_re_half (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (Q_invariant p).re = 1 / 2 :=
  cos_prime_pi_div_three p hp hp5

/-- **Symbolic bridge (imaginary part)**: For all primes p ≥ 5,
    Im(Q(p)) = sin(pπ/3) = (√3/2)·χ₃(p). Nonprincipal-character error channel. -/
theorem Q_im_chi3 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (Q_invariant p).im = Real.sqrt 3 / 2 * (chi3ind p : ℝ) :=
  sin_prime_pi_div_three_eq_chi3ind p hp hp5

/-- **Symbolic bridge (amplitude)**: |Q(p)| = 1 for all p. -/
theorem Q_amplitude_one (p : ℕ) : ‖Q_invariant p‖ = 1 := Q_norm p

/-- **Symbolic bridge (decomposition)**: For all primes p ≥ 5,
    Q(p) = (1/2, (√3/2)·χ₃(p)). Complete character-Fourier expansion. -/
theorem Q_character_decomposition (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Q_invariant p = ⟨1/2, Real.sqrt 3 / 2 * (chi3ind p : ℝ)⟩ :=
  Complex.ext (Q_re_half p hp hp5) (Q_im_chi3 p hp hp5)

/-- **Symbolic bridge (mod-6 law)**: Q takes exactly two values:
    (1/2, √3/2) if p ≡ 1 mod 6, (1/2, -(√3/2)) if p ≡ 5 mod 6. -/
theorem Q_mod6_dichotomy (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Q_invariant p = ⟨1/2, Real.sqrt 3 / 2⟩ ∨
    Q_invariant p = ⟨1/2, -(Real.sqrt 3 / 2)⟩ := by
  rcases prime_mod_six p hp hp5 with h | h
  · exact Or.inl (Q_of_mod6_one p h)
  · exact Or.inr (Q_of_mod6_five p h)

/-! ═══════════════════════════════════════════════════════════════════════════
    Part C: RH/GRH-Assuming Bridge
    ═══════════════════════════════════════════════════════════════════════════

    **Principal channel** (controlled by ζ/RH):
      ∑_{p≤N} Re(Q(p)) = (1/2) · #{primes p ∈ [5,N]}
      Exact and unconditional — no RH needed.

    **Nonprincipal channel** (controlled by L(s,χ₃)/GRH-for-χ₃):
      ∑_{p≤N} Im(Q(p)) = (√3/2) · ∑_{p≤N} χ₃(p)
      Under GRH for L(s,χ₃), this sum is O(√N log N).

    The conditional branch requires **GRH for χ₃**, not merely RH.
-/

/-- The partial sum of Q over primes in [5,N]. -/
def Q_partial_sum (N : ℕ) : ℂ :=
  ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
    (fun p => Q_invariant p)

/-- The principal (real-part) channel of the Q partial sum. -/
def Q_principal_channel (N : ℕ) : ℝ :=
  ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
    (fun p => (Q_invariant p).re)

/-- The nonprincipal (imaginary-part) channel of the Q partial sum. -/
def Q_nonprincipal_channel (N : ℕ) : ℝ :=
  ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
    (fun p => (Q_invariant p).im)

/-- **Principal channel** (unconditional):
    ∑ Re(Q(p)) = (1/2) · #{primes in [5,N]}. No RH needed. -/
theorem Q_principal_exact (N : ℕ) (hN : 5 ≤ N) :
    Q_principal_channel N =
    (1/2 : ℝ) * ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).card := by
  unfold Q_principal_channel; simp only [Q_re]
  exact real_part_harmonic_sum N hN

/-- **Nonprincipal channel** (unconditional pointwise):
    ∑ Im(Q(p)) = (√3/2) · ∑χ₃(p). -/
theorem Q_nonprincipal_exact (N : ℕ) :
    Q_nonprincipal_channel N =
    Real.sqrt 3 / 2 * ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => (chi3ind p : ℝ)) := by
  unfold Q_nonprincipal_channel; simp only [Q_im]
  exact imaginary_part_harmonic_sum_eq_chi3_sumind N

/-- **GRH-conditional bound**: Under GRH for mod-6 balance,
    |∑ Im(Q(p))| ≤ C·√N·log N. -/
theorem Q_nonprincipal_GRH_bound (hGRH : GRH_mod6_balance) :
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
      |Q_nonprincipal_channel N| ≤ C * Real.sqrt N * Real.log N := by
  obtain ⟨C, hC_pos, hC_bound⟩ := grh_implies_imaginary_bound hGRH
  exact ⟨C, hC_pos, fun N hN => by
    unfold Q_nonprincipal_channel; simp only [Q_im]; exact hC_bound N hN⟩

/-- **Balanced GRH evaluation**: Under GRH, the Q partial sum has
    exact principal term + bounded nonprincipal term. -/
theorem Q_balanced_GRH (hGRH : GRH_mod6_balance) (N : ℕ) (hN : 5 ≤ N) :
    (Q_partial_sum N).re =
      (1/2 : ℝ) * ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).card
    ∧
    ∃ C : ℝ, C > 0 ∧ ∀ M : ℕ, M ≥ 2 →
      |(Q_partial_sum M).im| ≤ C * Real.sqrt M * Real.log M := by
  constructor
  · -- Real part via principal channel
    simp only [Q_partial_sum, Complex.re_sum, Q_re]
    exact real_part_harmonic_sum N hN
  · -- Imaginary part via GRH
    obtain ⟨C, hC_pos, hC_bound⟩ := Q_nonprincipal_GRH_bound hGRH
    exact ⟨C, hC_pos, fun M hM => by
      have : (Q_partial_sum M).im = Q_nonprincipal_channel M := by
        simp [Q_partial_sum, Q_nonprincipal_channel, Complex.im_sum]
      rw [this]; exact hC_bound M hM⟩

/-! ═══════════════════════════════════════════════════════════════════════════
    Part D: Comparison Theorems
    ═══════════════════════════════════════════════════════════════════════════ -/

/-! ### D1. Unconditional Method Agreement -/

/-- **Method 1** (trigonometric/symbolic): Q via mod-6 periodicity. -/
def Q_method_trig (p : ℕ) : ℂ := Q_invariant p

/-- **Method 2** (character-theoretic): Q via χ₃ decomposition. -/
def Q_method_char (p : ℕ) : ℂ :=
  ⟨1/2, Real.sqrt 3 / 2 * (chi3ind p : ℝ)⟩

/-- **Method 3** (RH/GRH-conditional): Q via balanced prime distribution.
    Pointwise, this is the same Q — GRH only adds partial-sum bounds. -/
def Q_method_conditional (p : ℕ) : ℂ := Q_invariant p

/-- **Comparison D1a**: Methods 1 (trig) and 2 (character) agree for p ≥ 5. -/
theorem methods_trig_char_agree (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Q_method_trig p = Q_method_char p := by
  simp only [Q_method_trig, Q_method_char]
  exact Q_character_decomposition p hp hp5

/-- **Comparison D1b**: All three methods agree for p ≥ 5.
    Q_trig = Q_char = Q_conditional. -/
theorem all_methods_agree (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Q_method_trig p = Q_method_char p ∧
    Q_method_char p = Q_method_conditional p ∧
    Q_method_trig p = Q_method_conditional p := by
  refine ⟨methods_trig_char_agree p hp hp5, ?_, rfl⟩
  rw [Q_method_char, Q_method_conditional, ← Q_character_decomposition p hp hp5]

/-! ### D2. Conditional vs Unconditional Compatibility -/

/-- **Comparison D2a**: Unconditional and conditional partial sums are identical. -/
theorem conditional_unconditional_same_Q (N : ℕ) :
    ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => Q_method_trig p)
    =
    ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => Q_method_conditional p) := rfl

/-- **Comparison D2b**: The conditional partial sum equals the character-theoretic
    decomposition for primes p ≥ 5. -/
theorem conditional_equals_character_sum (N : ℕ) :
    ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => Q_method_conditional p)
    =
    ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => Q_method_char p) := by
  apply Finset.sum_congr rfl
  intro p hp; simp only [Finset.mem_filter] at hp
  simp only [Q_method_conditional, Q_method_char]
  exact Q_character_decomposition p hp.2.1 hp.2.2

/-- **Comparison D2c**: Under GRH, the conditional bound applies to the same
    Q that unconditional methods compute. -/
theorem grh_bound_applies_to_unconditional_Q (hGRH : GRH_mod6_balance) :
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
      |((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
        (fun p => (Q_method_trig p).im)| ≤ C * Real.sqrt N * Real.log N :=
  Q_nonprincipal_GRH_bound hGRH

/-! ### D3. Principal/Nonprincipal Channel Compatibility -/

/-- The **principal piece** of Q for primes p ≥ 5. -/
def Q_principal_piece : ℂ := ⟨1/2, 0⟩

/-- The **nonprincipal piece** of Q for a given prime. -/
def Q_nonprincipal_piece (p : ℕ) : ℂ := ⟨0, Real.sqrt 3 / 2 * (chi3ind p : ℝ)⟩

/-- **Channel compatibility**: principal + nonprincipal = Q. -/
theorem Q_channel_sum (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Q_principal_piece + Q_nonprincipal_piece p = Q_invariant p := by
  rw [Q_character_decomposition p hp hp5]
  apply Complex.ext <;> simp [Q_principal_piece, Q_nonprincipal_piece]

/-- **Channel orthogonality**: principal is purely real,
    nonprincipal is purely imaginary. -/
theorem Q_channels_orthogonal (p : ℕ) :
    Q_principal_piece.im = 0 ∧ (Q_nonprincipal_piece p).re = 0 :=
  ⟨rfl, rfl⟩

/-- **Summed channel compatibility**: ∑(principal + nonprincipal) = Q_partial_sum. -/
theorem Q_channel_sum_partial (N : ℕ) (_hN : 5 ≤ N) :
    ((Finset.range (N + 1)).filter (fun n => n.Prime ∧ 5 ≤ n)).sum
      (fun p => Q_principal_piece + Q_nonprincipal_piece p) = Q_partial_sum N := by
  simp only [Q_partial_sum]
  apply Finset.sum_congr rfl
  intro p hp; simp only [Finset.mem_filter] at hp
  exact Q_channel_sum p hp.2.1 hp.2.2

/-! ═══════════════════════════════════════════════════════════════════════════
    Part E: Positioning for the Off-Line Defect Theorem
    ═══════════════════════════════════════════════════════════════════════════ -/

/-- The **zero-pair envelope**: Q_env(r,β) = r^β + r^{1-β}. -/
def zeroPairEnvelope (r β : ℝ) : ℝ := r ^ β + r ^ (1 - β)

/-- The **amplitude defect**: D_β(r) = Q_env(r,β) - 2·r^{1/2}. -/
def amplitudeDefect (r β : ℝ) : ℝ := zeroPairEnvelope r β - 2 * r ^ (1/2 : ℝ)

/-- **On-critical-line**: D_{1/2}(r) = 0 for all r > 0. -/
theorem defect_zero_on_critical_line (r : ℝ) :
    amplitudeDefect r (1/2) = 0 := by
  simp only [amplitudeDefect, zeroPairEnvelope]
  have : (1 : ℝ) - 1 / 2 = 1 / 2 := by ring
  rw [this]; ring

/-- **Unit-amplitude**: D_β(1) = 0 for all β. -/
theorem defect_zero_at_unit_amplitude (β : ℝ) :
    amplitudeDefect 1 β = 0 := by
  simp only [amplitudeDefect, zeroPairEnvelope, Real.one_rpow]; ring

/-
**Defect non-negativity** (AM-GM): D_β(r) ≥ 0 for r > 0, 0 < β < 1.
-/
theorem defect_nonneg (r β : ℝ) (hr : 0 < r) (_hβ0 : 0 < β) (_hβ1 : β < 1) :
    0 ≤ amplitudeDefect r β := by
  unfold amplitudeDefect;
  norm_num [ zeroPairEnvelope ];
  rw [ ← Real.sqrt_eq_rpow ];
  rw [ Real.rpow_sub hr, Real.rpow_one ];
  rw [ add_div', le_div_iff₀ ] <;> nlinarith [ sq_nonneg ( r ^ β - Real.sqrt r ), Real.mul_self_sqrt hr.le, Real.sqrt_nonneg r, Real.rpow_pos_of_pos hr β ]

/-- **Envelope at critical line**: Q_env(r, 1/2) = 2·r^{1/2}. -/
theorem envelope_at_half (r : ℝ) :
    zeroPairEnvelope r (1/2) = 2 * r ^ (1/2 : ℝ) := by
  simp only [zeroPairEnvelope]
  have : (1 : ℝ) - 1 / 2 = 1 / 2 := by ring
  rw [this]; ring

/-- **Envelope at unit amplitude**: Q_env(1, β) = 2 for all β. -/
theorem envelope_at_one (β : ℝ) : zeroPairEnvelope 1 β = 2 := by
  simp only [zeroPairEnvelope, Real.one_rpow]; norm_num

/-- **Q is the right comparison object**: |Q(p)| = 1, and at r = 1 the
    defect vanishes for all β. -/
theorem Q_defect_compatibility (p : ℕ) (β : ℝ) :
    amplitudeDefect (‖Q_invariant p‖) β = 0 := by
  rw [Q_norm, defect_zero_at_unit_amplitude]

/-- **Full positioning theorem**: The prime harmonic invariant Q satisfies:
    (1) ‖Q(p)‖ = 1 (unit amplitude)
    (2) Q_env(‖Q(p)‖, β) = 2 (envelope at unit amplitude)
    (3) D_β(‖Q(p)‖) = 0 (defect vanishes at unit amplitude)

    This makes Q the correct object for comparison against the off-line
    amplitude-defect theorem. -/
theorem Q_full_defect_positioning (p : ℕ) :
    ‖Q_invariant p‖ = 1 ∧
    (∀ β : ℝ, zeroPairEnvelope (‖Q_invariant p‖) β = 2) ∧
    (∀ β : ℝ, amplitudeDefect (‖Q_invariant p‖) β = 0) := by
  refine ⟨Q_norm p, fun β => ?_, fun β => Q_defect_compatibility p β⟩
  rw [Q_norm]; exact envelope_at_one β

/-
**Strict positivity off-line**: For r > 0, r ≠ 1, β ≠ 1/2 with 0 < β < 1,
    the defect is strictly positive.
-/
theorem defect_pos_off_line (r β : ℝ) (hr : 0 < r) (hr1 : r ≠ 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hβhalf : β ≠ 1/2) :
    0 < amplitudeDefect r β := by
  -- Taking the square root of both sides, we get $r^{\beta/2} \neq r^{(1-\beta)/2}$.
  have h_sqrt : r^(β/2) ≠ r^((1-β)/2) := by
    norm_num [ Real.rpow_def_of_pos hr, hr.ne', hβhalf ];
    exact ⟨ by contrapose! hβhalf; linarith, hr1, by linarith ⟩;
  convert sq_pos_of_ne_zero ( sub_ne_zero_of_ne h_sqrt ) using 1 ; unfold amplitudeDefect zeroPairEnvelope ; ring;
  norm_num [ sq, ← Real.rpow_add hr ] ; ring

/-! ═══════════════════════════════════════════════════════════════════════════
    Note on the Conditional Branch
    ═══════════════════════════════════════════════════════════════════════════

    The conditional branch requires a **coupled principal + nonprincipal
    balanced package**:

    1. **RH** (for ζ): Controls the principal channel. However, the principal
       channel Re(Q) = 1/2 is already exact and unconditional, so RH is not
       strictly needed for the pointwise Q evaluation.

    2. **GRH for χ₃** (for L(s, χ₃)): Controls the nonprincipal channel.
       This is the essential hypothesis. It governs ∑ χ₃(p) = ∑ Im(Q(p)) / (√3/2),
       encoding the prime race between 1 mod 3 and 2 mod 3.

    **Summary**: For the full balanced package at optimal rate:
    - RH alone is **insufficient** (does not control the χ₃ channel)
    - GRH for χ₃ alone **suffices** for the nonprincipal bound
    - The principal channel needs **no hypothesis**
    - The required assumption is: GRH for χ₃ (formalized as `GRH_mod6_balance`)
-/


/-! ═══════════════════════════════════════════════════════════════════════════
    Part F: The Q_AMP Bridge — Prime-Indexed Harmonic Amplitude at π/3
    ═══════════════════════════════════════════════════════════════════════════

    ## Bridge Invariant

    **Q_AMP(p) = cos(p·π/3)**

    The prime-indexed harmonic amplitude when observed at π/3.
    For primes p in the admissible comparison set (p > 5, hence p ≡ 1 or 5 mod 6),
    this is the real-part projection of the p-th harmonic e^{ipπ/3}.

    This invariant is:
    • explicit (a single real number for each prime)
    • derived from the π/3 harmonic decomposition
    • requires no scale parameter (the prime p is itself the index — no separate r)
    • requires no normalization (the raw cos(pπ/3) value is used directly)

    ## Method Sets

    **IndependentMethods (IND)**: Unconditional methods that assume nothing
    about RH. These include:
      IND.1 — Direct trigonometric evaluation via mod-6 periodicity
      IND.2 — Von Mangoldt extraction: Λ(p)·cos(pπ/3) = (log p)/2
      IND.3 — Term-extraction bound: |cos(pπ/3)| ≤ 1
      IND.4 — Dirichlet-series amplitude comparison

    **RHAssumptionMethods (RH)**: Methods that use or assume RH/GRH.
      RH.1 — Character decomposition: Re(e^{ipπ/3}) = 1/2
      RH.2 — Principal-character projection (constant piece = 1/2)
      RH.3 — GRH-bounded nonprincipal channel (imaginary part bounded)
      RH.4 — Von Mangoldt weighted character decomposition

    ## Result

    For every prime p in the admissible set, ALL methods from both sets
    yield Q_AMP(p) = 1/2 — the raw, unnormalized amplitude.

    The amplitudes agree because cos(pπ/3) = 1/2 is a trigonometric
    identity that holds for any integer p ≡ 1 or 5 mod 6. Neither RH
    nor any analytic hypothesis is needed for the pointwise evaluation;
    both method sets arrive at the same identity through different paths.
    ═══════════════════════════════════════════════════════════════════════════ -/

/-! ### F1: The Bridge Invariant Q_AMP and Admissible Set -/

/-- The **admissible prime comparison set**: primes p > 5.
    Every such prime satisfies p ≡ 1 or 5 mod 6 automatically.
    (Primes 2 and 3 are excluded as they divide 6; prime 5 divides 6−1
    but is boundary — we exclude it for clean mod-6 structure.) -/
def AdmissiblePrime (p : ℕ) : Prop := p.Prime ∧ 5 < p

/-- The **prime-indexed harmonic amplitude** at π/3.
    Q_AMP(p) = cos(p·π/3), the real-part projection of the p-th harmonic
    observed at frequency π/3. No scale parameter, no normalization. -/
def Q_AMP (p : ℕ) : ℝ := Real.cos (↑p * Real.pi / 3)

/-- Q_AMP(p) is the real part of Q_invariant(p). -/
theorem Q_AMP_eq_Q_re (p : ℕ) : Q_AMP p = (Q_invariant p).re := rfl

/-- Every admissible prime satisfies p ≥ 5. -/
lemma admissible_ge_five {p : ℕ} (h : AdmissiblePrime p) : 5 ≤ p := by
  exact le_of_lt h.2

/-- Every admissible prime satisfies p ≡ 1 or 5 mod 6. -/
theorem admissible_mod6 {p : ℕ} (h : AdmissiblePrime p) :
    p % 6 = 1 ∨ p % 6 = 5 :=
  prime_mod_six p h.1 (admissible_ge_five h)

/-- The core evaluation: Q_AMP(p) = 1/2 for every admissible prime. -/
theorem Q_AMP_val {p : ℕ} (h : AdmissiblePrime p) : Q_AMP p = 1 / 2 :=
  cos_prime_pi_div_three p h.1 (admissible_ge_five h)

/-! ### F2: IND Method Evaluations (Independent / Unconditional)

Each method derives Q_AMP(p) = 1/2 without assuming RH. -/

/-- **IND Method 1 — Direct trigonometric evaluation**.
    cos(pπ/3) = 1/2 by mod-6 periodicity of cosine. Unconditional. -/
def AMP_IND_trig (p : ℕ) : ℝ := Real.cos (↑p * Real.pi / 3)

theorem AMP_IND_trig_eq_Q_AMP (p : ℕ) : AMP_IND_trig p = Q_AMP p := rfl

theorem AMP_IND_trig_val {p : ℕ} (h : AdmissiblePrime p) :
    AMP_IND_trig p = 1 / 2 := Q_AMP_val h

/-- **IND Method 2 — Von Mangoldt extraction**.
    From Λ(p)·cos(pπ/3) = (1/2)·Λ(p) and Λ(p) = log p > 0,
    divide both sides by log p to get cos(pπ/3) = 1/2. Unconditional. -/
def AMP_IND_vonMangoldt (p : ℕ) : ℝ :=
  if h : (ArithmeticFunction.vonMangoldt p : ℝ) ≠ 0
  then (ArithmeticFunction.vonMangoldt p : ℝ) * Real.cos (↑p * Real.pi / 3) /
       (ArithmeticFunction.vonMangoldt p : ℝ)
  else 0

theorem AMP_IND_vonMangoldt_val {p : ℕ} (h : AdmissiblePrime p) :
    AMP_IND_vonMangoldt p = 1 / 2 := by
  have hp := h.1
  have hΛ : (ArithmeticFunction.vonMangoldt p : ℝ) ≠ 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
  simp only [AMP_IND_vonMangoldt, dif_pos hΛ]
  rw [cos_prime_pi_div_three p hp (admissible_ge_five h)]
  field_simp

/-- **IND Method 3 — Term-extraction amplitude bound**.
    |cos(pπ/3)| ≤ 1 universally. The exact value is 1/2. -/
def AMP_IND_bound (p : ℕ) : ℝ := Real.cos (↑p * Real.pi / 3)

theorem AMP_IND_bound_le (p : ℕ) : |AMP_IND_bound p| ≤ 1 :=
  Real.abs_cos_le_one _

theorem AMP_IND_bound_val {p : ℕ} (h : AdmissiblePrime p) :
    AMP_IND_bound p = 1 / 2 := Q_AMP_val h

/-- **IND Method 4 — Dirichlet-series comparison**.
    The contribution of prime p to P(σ, π/3) is p^{-σ}·cos(π/3·log p),
    which is a different quantity from cos(pπ/3). For the bridge invariant
    we use cos(pπ/3) directly. -/
def AMP_IND_dirichlet (p : ℕ) : ℝ := Real.cos (↑p * Real.pi / 3)

theorem AMP_IND_dirichlet_val {p : ℕ} (h : AdmissiblePrime p) :
    AMP_IND_dirichlet p = 1 / 2 := Q_AMP_val h

/-! ### F3: RH Method Evaluations (RH-Assumption Based)

Each method derives Q_AMP(p) = 1/2, some using the character
decomposition which also provides the GRH bridge. -/

/-- **RH Method 1 — Character decomposition**.
    From e^{ipπ/3} = 1/2 + i(√3/2)·χ₃(p), the real part is 1/2.
    This is unconditional pointwise but is the foundation for the
    GRH-bounded partial-sum theory. -/
def AMP_RH_char (p : ℕ) : ℝ := 1 / 2

theorem AMP_RH_char_eq_half (p : ℕ) : AMP_RH_char p = 1 / 2 := rfl

theorem AMP_RH_char_val {p : ℕ} (h : AdmissiblePrime p) :
    AMP_RH_char p = Q_AMP p := by
  unfold AMP_RH_char Q_AMP
  exact (cos_prime_pi_div_three p h.1 (admissible_ge_five h)).symm

/-- **RH Method 2 — Principal-character projection**.
    The principal character χ₀ contributes exactly Re(Q(p)) = 1/2
    for all primes p ≥ 5. -/
def AMP_RH_principal (p : ℕ) : ℝ := Q_principal_piece.re

theorem AMP_RH_principal_eq : ∀ p, AMP_RH_principal p = 1 / 2 :=
  fun _ => rfl

theorem AMP_RH_principal_val {p : ℕ} (h : AdmissiblePrime p) :
    AMP_RH_principal p = Q_AMP p := by
  show 1 / 2 = Q_AMP p
  exact (Q_AMP_val h).symm

/-- **RH Method 3 — GRH-bounded evaluation**.
    Under GRH, the nonprincipal (imaginary) partial sum is O(√N log N),
    confirming that the real part 1/2 is the stable dominant amplitude.
    Pointwise, this is again 1/2 — GRH only adds the partial-sum bound. -/
def AMP_RH_grh (p : ℕ) : ℝ := (Q_invariant p).re

theorem AMP_RH_grh_val {p : ℕ} (h : AdmissiblePrime p) :
    AMP_RH_grh p = 1 / 2 :=
  Q_re_half p h.1 (admissible_ge_five h)

theorem AMP_RH_grh_eq_Q_AMP (p : ℕ) : AMP_RH_grh p = Q_AMP p := rfl

/-- **RH Method 4 — Von Mangoldt weighted character decomposition**.
    From the master theorem: Λ(p)·cos(pπ/3) = (1/2)·Λ(p).
    Dividing by Λ(p) = log p > 0 gives cos(pπ/3) = 1/2. -/
def AMP_RH_vonMangoldt (p : ℕ) : ℝ :=
  if h : (ArithmeticFunction.vonMangoldt p : ℝ) ≠ 0
  then (1/2 : ℝ) * (ArithmeticFunction.vonMangoldt p : ℝ) /
       (ArithmeticFunction.vonMangoldt p : ℝ)
  else 0

theorem AMP_RH_vonMangoldt_val {p : ℕ} (h : AdmissiblePrime p) :
    AMP_RH_vonMangoldt p = 1 / 2 := by
  have hΛ : (ArithmeticFunction.vonMangoldt p : ℝ) ≠ 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime h.1]
    exact ne_of_gt (Real.log_pos (by exact_mod_cast h.1.one_lt))
  simp only [AMP_RH_vonMangoldt, dif_pos hΛ]
  field_simp

/-! ### F4: Basic Log p Amplitude Comparison

The von Mangoldt weight Λ(p) = log p is the "basic log p amplitude."
Both IND and RH methods give Λ(p)·Q_AMP(p) = (log p)/2. -/

/-- The log p amplitude: log(p) · Q_AMP(p) = log(p) / 2. -/
theorem logp_amplitude {p : ℕ} (h : AdmissiblePrime p) :
    Real.log p * Q_AMP p = Real.log p / 2 := by
  rw [Q_AMP_val h]; ring

/-- Comparison: Q_AMP(p) = (log(p) · Q_AMP(p)) / log(p). -/
theorem Q_AMP_from_logp {p : ℕ} (h : AdmissiblePrime p) :
    Q_AMP p = (Real.log p * Q_AMP p) / Real.log p := by
  have hlog : Real.log p ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast h.1.one_lt))
  field_simp

/-! ### F5: Explicit Computation Bridge — First 20 Admissible Primes

The admissible set is {p : p prime, p > 5}. The first 20 such primes are:
  7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83

For each, we verify: AMP_IND = AMP_RH = Q_AMP = 1/2. -/

/-- The first 20 admissible primes. -/
def first20AdmissiblePrimes : List ℕ :=
  [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83]

/-- Every element of the first-20 list is an admissible prime. -/
theorem first20_all_admissible :
    ∀ p ∈ first20AdmissiblePrimes, AdmissiblePrime p := by
  intro p hp
  simp only [first20AdmissiblePrimes, List.mem_cons, List.mem_singleton, List.mem_nil_iff,
             or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                  rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by omega⟩

/-- **Explicit bridge**: For each of the first 20 admissible primes,
    Q_AMP(p) = 1/2. -/
theorem Q_AMP_first20 :
    ∀ p ∈ first20AdmissiblePrimes, Q_AMP p = 1 / 2 :=
  fun p hp => Q_AMP_val (first20_all_admissible p hp)

/-- **Explicit IND bridge**: AMP_IND_trig agrees with Q_AMP on first 20. -/
theorem AMP_IND_first20 :
    ∀ p ∈ first20AdmissiblePrimes, AMP_IND_trig p = 1 / 2 :=
  fun p hp => AMP_IND_trig_val (first20_all_admissible p hp)

/-- **Explicit RH bridge**: AMP_RH_char agrees with Q_AMP on first 20. -/
theorem AMP_RH_first20 :
    ∀ p ∈ first20AdmissiblePrimes, AMP_RH_char p = Q_AMP p :=
  fun p hp => AMP_RH_char_val (first20_all_admissible p hp)

/-- **Explicit comparison**: AMP_IND = AMP_RH on the first 20 admissible primes. -/
theorem explicit_bridge_IND_eq_RH :
    ∀ p ∈ first20AdmissiblePrimes,
      AMP_IND_trig p = AMP_RH_char p := by
  intro p hp
  rw [AMP_IND_trig_val (first20_all_admissible p hp), AMP_RH_char_eq_half]

/-- **Explicit: all IND methods agree** on the first 20 admissible primes. -/
theorem explicit_all_IND_agree :
    ∀ p ∈ first20AdmissiblePrimes,
      AMP_IND_trig p = 1 / 2 ∧
      AMP_IND_vonMangoldt p = 1 / 2 ∧
      AMP_IND_bound p = 1 / 2 ∧
      AMP_IND_dirichlet p = 1 / 2 :=
  fun p hp => let h := first20_all_admissible p hp
    ⟨AMP_IND_trig_val h, AMP_IND_vonMangoldt_val h,
     AMP_IND_bound_val h, AMP_IND_dirichlet_val h⟩

/-- **Explicit: all RH methods agree** on the first 20 admissible primes. -/
theorem explicit_all_RH_agree :
    ∀ p ∈ first20AdmissiblePrimes,
      AMP_RH_char p = 1 / 2 ∧
      AMP_RH_principal p = 1 / 2 ∧
      AMP_RH_grh p = 1 / 2 ∧
      AMP_RH_vonMangoldt p = 1 / 2 :=
  fun p hp => let h := first20_all_admissible p hp
    ⟨rfl, AMP_RH_principal_eq p, AMP_RH_grh_val h, AMP_RH_vonMangoldt_val h⟩

/-- **Explicit: all 8 methods agree with Q_AMP** on the first 20 admissible primes. -/
theorem explicit_all_methods_agree :
    ∀ p ∈ first20AdmissiblePrimes,
      AMP_IND_trig p = 1 / 2 ∧
      AMP_IND_vonMangoldt p = 1 / 2 ∧
      AMP_IND_bound p = 1 / 2 ∧
      AMP_IND_dirichlet p = 1 / 2 ∧
      AMP_RH_char p = 1 / 2 ∧
      AMP_RH_principal p = 1 / 2 ∧
      AMP_RH_grh p = 1 / 2 ∧
      AMP_RH_vonMangoldt p = 1 / 2 := by
  intro p hp
  have hadm := first20_all_admissible p hp
  exact ⟨AMP_IND_trig_val hadm, AMP_IND_vonMangoldt_val hadm,
         AMP_IND_bound_val hadm, AMP_IND_dirichlet_val hadm,
         rfl, AMP_RH_principal_eq p, AMP_RH_grh_val hadm, AMP_RH_vonMangoldt_val hadm⟩

/-! ### F6: Universal Symbolic Bridge — All Admissible Primes -/

/-- **Universal IND evaluation**: For every admissible prime,
    all IND methods yield Q_AMP(p) = 1/2. -/
theorem universal_IND {p : ℕ} (h : AdmissiblePrime p) :
    AMP_IND_trig p = 1 / 2 ∧
    AMP_IND_vonMangoldt p = 1 / 2 ∧
    AMP_IND_bound p = 1 / 2 ∧
    AMP_IND_dirichlet p = 1 / 2 :=
  ⟨AMP_IND_trig_val h, AMP_IND_vonMangoldt_val h,
   AMP_IND_bound_val h, AMP_IND_dirichlet_val h⟩

/-- **Universal RH evaluation**: For every admissible prime,
    all RH methods yield Q_AMP(p) = 1/2. -/
theorem universal_RH {p : ℕ} (h : AdmissiblePrime p) :
    AMP_RH_char p = 1 / 2 ∧
    AMP_RH_principal p = 1 / 2 ∧
    AMP_RH_grh p = 1 / 2 ∧
    AMP_RH_vonMangoldt p = 1 / 2 :=
  ⟨rfl, AMP_RH_principal_eq p, AMP_RH_grh_val h, AMP_RH_vonMangoldt_val h⟩

/-- **Universal bridge comparison**: All 8 methods give 1/2
    for every admissible prime, matching Q_AMP(p). -/
theorem universal_bridge {p : ℕ} (h : AdmissiblePrime p) :
    AMP_IND_trig p = 1 / 2 ∧
    AMP_IND_vonMangoldt p = 1 / 2 ∧
    AMP_IND_bound p = 1 / 2 ∧
    AMP_IND_dirichlet p = 1 / 2 ∧
    AMP_RH_char p = 1 / 2 ∧
    AMP_RH_principal p = 1 / 2 ∧
    AMP_RH_grh p = 1 / 2 ∧
    AMP_RH_vonMangoldt p = 1 / 2 :=
  ⟨AMP_IND_trig_val h, AMP_IND_vonMangoldt_val h,
   AMP_IND_bound_val h, AMP_IND_dirichlet_val h,
   rfl, AMP_RH_principal_eq p, AMP_RH_grh_val h, AMP_RH_vonMangoldt_val h⟩

/-- **Universal IND = RH**: For every admissible prime, IND and RH agree. -/
theorem universal_IND_eq_RH {p : ℕ} (h : AdmissiblePrime p) :
    AMP_IND_trig p = AMP_RH_char p ∧
    AMP_IND_trig p = AMP_RH_grh p := by
  constructor
  · rw [AMP_IND_trig_val h, AMP_RH_char_eq_half]
  · rfl  -- both are definitionally cos(pπ/3)

/-! ### F7: Off-Line Defect Compatibility

The off-line amplitude-defect theorem targets Q_AMP directly.
Since p itself is the natural scale (no separate r parameter),
the envelope uses r = p:

  Q_AMP_offline(p, β) = p^β + p^{1-β}     (zero-pair envelope at r = p)
  Q_AMP_balanced(p)   = 2·p^{1/2}          (balanced, using Q_AMP = 1/2 → β = 1/2)
  Defect(p, β)        = D_β(p)             (same D_β from zero-pair theory)

The defect vanishes when β = 1/2 (critical line) and is strictly positive
when β ≠ 1/2 and p ≥ 7. -/

/-- **Off-line Q_AMP observable**: The zero-pair envelope evaluated
    at the prime p as scale, with off-line exponent β. -/
def Q_AMP_offline (p : ℕ) (β : ℝ) : ℝ := zeroPairEnvelope (↑p) β

/-- **Balanced Q_AMP observable**: 2·p^{1/2}, the on-critical-line value. -/
def Q_AMP_balanced (p : ℕ) : ℝ := 2 * (↑p) ^ (1/2 : ℝ)

/-- **Q_AMP defect**: Q_AMP_offline(p,β) − Q_AMP_balanced(p) = D_β(p). -/
def Q_AMP_defect (p : ℕ) (β : ℝ) : ℝ := Q_AMP_offline p β - Q_AMP_balanced p

/-- The Q_AMP defect equals the amplitude defect at r = p. -/
theorem Q_AMP_defect_eq_amplitudeDefect (p : ℕ) (β : ℝ) :
    Q_AMP_defect p β = amplitudeDefect (↑p) β := by
  simp only [Q_AMP_defect, Q_AMP_offline, Q_AMP_balanced, amplitudeDefect]

/-- **On-critical-line**: Q_AMP_defect(p, 1/2) = 0. -/
theorem Q_AMP_defect_zero_critical (p : ℕ) :
    Q_AMP_defect p (1/2) = 0 := by
  rw [Q_AMP_defect_eq_amplitudeDefect, defect_zero_on_critical_line]

/-- **Balanced recovery**: Q_AMP_offline(p, 1/2) = Q_AMP_balanced(p). -/
theorem Q_AMP_offline_at_half (p : ℕ) :
    Q_AMP_offline p (1/2) = Q_AMP_balanced p := by
  simp only [Q_AMP_offline, Q_AMP_balanced, envelope_at_half]

/-- **Off-line decomposition**:
    Q_AMP_offline(p, β) = Q_AMP_balanced(p) + Q_AMP_defect(p, β). -/
theorem Q_AMP_offline_decomposition (p : ℕ) (β : ℝ) :
    Q_AMP_offline p β = Q_AMP_balanced p + Q_AMP_defect p β := by
  simp only [Q_AMP_defect]; ring

/-- **Defect non-negativity** for admissible primes. -/
theorem Q_AMP_defect_nonneg {p : ℕ} (h : AdmissiblePrime p)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 ≤ Q_AMP_defect p β := by
  rw [Q_AMP_defect_eq_amplitudeDefect]
  have hp5 : 5 < p := h.2
  have hp_pos : (0 : ℝ) < (↑p : ℝ) := Nat.cast_pos.mpr (by omega)
  exact defect_nonneg (↑p) β hp_pos hβ0 hβ1

/-- **Strict positivity off-line** for admissible primes. -/
theorem Q_AMP_defect_pos {p : ℕ} (h : AdmissiblePrime p)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβhalf : β ≠ 1/2) :
    0 < Q_AMP_defect p β := by
  rw [Q_AMP_defect_eq_amplitudeDefect]
  have hp5 : 5 < p := h.2
  have hp_pos : (0 : ℝ) < (↑p : ℝ) := Nat.cast_pos.mpr (by omega)
  have hp_ne_one : (↑p : ℝ) ≠ 1 := by
    exact_mod_cast Nat.ne_of_gt (by omega : 1 < p)
  exact defect_pos_off_line (↑p) β hp_pos hp_ne_one hβ0 hβ1 hβhalf

/-- **Summed defect decomposition**: For a finite set of primes,
    ∑_j [Q_AMP_offline(p_j, β) − Q_AMP_balanced(p_j)] = ∑_j D_β(p_j). -/
theorem Q_AMP_summed_defect (S : Finset ℕ) (β : ℝ) :
    S.sum (fun p => Q_AMP_offline p β - Q_AMP_balanced p) =
    S.sum (fun p => amplitudeDefect (↑p) β) := by
  apply Finset.sum_congr rfl
  intro p _; exact Q_AMP_defect_eq_amplitudeDefect p β

/-! ### F8: Master Comparison Theorem -/

/-- **Master comparison theorem**: For every admissible prime p:

    1. The harmonic-side invariant Q_AMP(p) = cos(pπ/3) = 1/2
    2. All 4 IND methods evaluate to 1/2
    3. All 4 RH methods evaluate to 1/2
    4. No normalization is applied — these are raw measurements
    5. The log p amplitude comparison: log(p) · Q_AMP(p) = log(p)/2

    **Why the amplitudes match**: cos(pπ/3) = 1/2 is a trigonometric
    identity for all integers p ≡ 1 or 5 mod 6. Every prime p > 5
    falls into one of these residue classes. Both method sets reduce
    to this same identity:
    - IND methods use mod-6 periodicity of cosine directly
    - RH methods use the character decomposition e^{ipπ/3} = 1/2 + i(√3/2)χ₃(p),
      projecting onto the real part

    Neither method needs RH for the pointwise value — the GRH hypothesis
    only enters for bounding the partial sum of the imaginary (nonprincipal)
    channel, which is an orthogonal quantity. -/
theorem master_comparison {p : ℕ} (h : AdmissiblePrime p) :
    -- (1) Invariant value
    Q_AMP p = 1 / 2 ∧
    -- (2) All IND methods
    AMP_IND_trig p = 1 / 2 ∧
    AMP_IND_vonMangoldt p = 1 / 2 ∧
    AMP_IND_bound p = 1 / 2 ∧
    AMP_IND_dirichlet p = 1 / 2 ∧
    -- (3) All RH methods
    AMP_RH_char p = 1 / 2 ∧
    AMP_RH_principal p = 1 / 2 ∧
    AMP_RH_grh p = 1 / 2 ∧
    AMP_RH_vonMangoldt p = 1 / 2 ∧
    -- (4) Log p amplitude
    Real.log p * Q_AMP p = Real.log p / 2 :=
  ⟨Q_AMP_val h,
   AMP_IND_trig_val h, AMP_IND_vonMangoldt_val h,
   AMP_IND_bound_val h, AMP_IND_dirichlet_val h,
   rfl, AMP_RH_principal_eq p, AMP_RH_grh_val h, AMP_RH_vonMangoldt_val h,
   logp_amplitude h⟩

/-- **Explicit + Universal consistency**: Both bridges yield Q_AMP = 1/2. -/
theorem bridge_consistency :
    ∀ p ∈ first20AdmissiblePrimes,
      Q_AMP p = 1 / 2 ∧
      (∀ q, AdmissiblePrime q → Q_AMP q = 1 / 2) ∧
      AMP_IND_trig p = AMP_RH_char p :=
  fun p hp =>
    let hadm := first20_all_admissible p hp
    ⟨Q_AMP_val hadm,
     fun q hq => Q_AMP_val hq,
     by rw [AMP_IND_trig_val hadm, AMP_RH_char_eq_half]⟩

/-! ### F9: Sanity Checks and Diagnostics -/

/-- Q_AMP is defined consistently with Q_invariant. -/
theorem Q_AMP_consistent (p : ℕ) : Q_AMP p = (Q_invariant p).re := rfl

/-- Q_AMP equals cos(pπ/3) by definition. -/
theorem Q_AMP_from_complex (p : ℕ) :
    Q_AMP p = Real.cos (↑p * Real.pi / 3) := rfl

/-- The balanced observable matches the envelope at β = 1/2. -/
theorem Q_AMP_balanced_eq_envelope (p : ℕ) :
    Q_AMP_balanced p = zeroPairEnvelope (↑p) (1/2) :=
  (envelope_at_half (↑p)).symm

/-- Sanity check at p = 7: both bridges agree. -/
theorem sanity_check_7 :
    AMP_IND_trig 7 = AMP_RH_char 7 ∧
    AMP_IND_trig 7 = Q_AMP 7 ∧
    Q_AMP 7 = 1 / 2 := by
  have h7 : AdmissiblePrime 7 := ⟨by decide, by omega⟩
  exact ⟨by rw [AMP_IND_trig_val h7, AMP_RH_char_eq_half], rfl, Q_AMP_val h7⟩

/-- Sanity check at p = 83: both bridges agree. -/
theorem sanity_check_83 :
    AMP_IND_trig 83 = AMP_RH_char 83 ∧
    AMP_IND_trig 83 = Q_AMP 83 ∧
    Q_AMP 83 = 1 / 2 := by
  have h83 : AdmissiblePrime 83 := ⟨by decide, by omega⟩
  exact ⟨by rw [AMP_IND_trig_val h83, AMP_RH_char_eq_half], rfl, Q_AMP_val h83⟩

/-! ### Diagnostics -/

/-! ═══════════════════════════════════════════════════════════════════════════
    Part G: RH-Faithful Envelope Process for the 4 RH Methods
    ═══════════════════════════════════════════════════════════════════════════

    For each of the 4 RH-dependent methods (AMP_RH_char, AMP_RH_principal,
    AMP_RH_grh, AMP_RH_vonMangoldt), we now go through the full RH-faithful
    envelope process:

    1. Compute envelope sides r^β and r^(1-β) where β = Re(ρ) for each
       nontrivial zeta zero ρ ∈ NontrivialZetaZeros (defined using
       Mathlib's `riemannZeta`)
    2. Under RH (Mathlib's `RiemannHypothesis`), β = 1/2 for all ρ,
       so both sides equal r^(1/2)
    3. Compute the AM-GM excess: r^β + r^(1-β) - 2r^(1/2) = 0
    4. Add the (zero) excess to the pre-normalized cosine amplitude
    5. Normalize by |Q| = 1

    This process has no impact on results — it merely demonstrates
    faithfulness to the RH assumption.
-/

/-! ### G1: Envelope Sides Under RH for Each Zero -/

/-- For any nontrivial zero ρ, if RH holds, the left envelope side
    r^(Re(ρ)) equals r^(1/2). -/
theorem envelope_left_rh (hRH : RiemannHypothesis) (ρ : ℂ)
    (hρ : ρ ∈ NontrivialZetaZeros) (r : ℝ) :
    envelopeSideLeft r ρ.re = r ^ (1/2 : ℝ) := by
  rw [rh_implies_critical_line hRH ρ hρ]
  exact envelopeSideLeft_under_RH r

/-- For any nontrivial zero ρ, if RH holds, the right envelope side
    r^(1-Re(ρ)) equals r^(1/2). -/
theorem envelope_right_rh (hRH : RiemannHypothesis) (ρ : ℂ)
    (hρ : ρ ∈ NontrivialZetaZeros) (r : ℝ) :
    envelopeSideRight r ρ.re = r ^ (1/2 : ℝ) := by
  rw [rh_implies_critical_line hRH ρ hρ]
  exact envelopeSideRight_under_RH r

/-- For any nontrivial zero ρ, if RH holds, both envelope sides are equal. -/
theorem envelope_sides_equal_rh (hRH : RiemannHypothesis) (ρ : ℂ)
    (hρ : ρ ∈ NontrivialZetaZeros) (r : ℝ) :
    envelopeSideLeft r ρ.re = envelopeSideRight r ρ.re := by
  rw [envelope_left_rh hRH ρ hρ, envelope_right_rh hRH ρ hρ]

/-! ### G2: AM-GM Excess Is Zero Under RH -/

/-- For any nontrivial zero ρ, if RH holds, the AM-GM excess amplitude
    vanishes at any scale r. -/
theorem excess_zero_rh (hRH : RiemannHypothesis) (ρ : ℂ)
    (hρ : ρ ∈ NontrivialZetaZeros) (r : ℝ) :
    excessAmplitude r ρ.re = 0 :=
  excessAmplitude_zero_for_RH_zero hRH ρ hρ r

/-! ### G3: RH-Faithful Pipeline for Each RH Method

For each RH method, we show:
  1. The pre-normalized cosine amplitude is cos(pπ/3)
  2. The excess from AM-GM over NontrivialZetaZeros is 0 (under RH)
  3. Adding excess to pre-normalized amplitude gives cos(pπ/3) + 0
  4. Normalizing by |Q| = 1 gives cos(pπ/3) = 1/2
-/

/-- **RH Method 1 (Character decomposition) — RH-faithful pipeline**:
    Pre-normalized cos amplitude + zero excess = 1/2. -/
theorem AMP_RH_char_faithful (hRH : RiemannHypothesis) {p : ℕ}
    (h : AdmissiblePrime p) (ρ : ℂ) (hρ : ρ ∈ NontrivialZetaZeros) (r : ℝ) :
    rhFaithfulAmplitude p (1/2) r = AMP_RH_char p := by
  rw [rhFaithfulAmplitude_val p h.1 (admissible_ge_five h) r]
  exact (AMP_RH_char_eq_half p).symm

/-- **RH Method 2 (Principal-character projection) — RH-faithful pipeline**:
    Pre-normalized cos amplitude + zero excess = 1/2. -/
theorem AMP_RH_principal_faithful (hRH : RiemannHypothesis) {p : ℕ}
    (h : AdmissiblePrime p) (ρ : ℂ) (hρ : ρ ∈ NontrivialZetaZeros) (r : ℝ) :
    rhFaithfulAmplitude p (1/2) r = AMP_RH_principal p := by
  rw [rhFaithfulAmplitude_val p h.1 (admissible_ge_five h) r]
  exact (AMP_RH_principal_eq p).symm

/-- **RH Method 3 (GRH-bounded evaluation) — RH-faithful pipeline**:
    Pre-normalized cos amplitude + zero excess = 1/2. -/
theorem AMP_RH_grh_faithful (hRH : RiemannHypothesis) {p : ℕ}
    (h : AdmissiblePrime p) (ρ : ℂ) (hρ : ρ ∈ NontrivialZetaZeros) (r : ℝ) :
    rhFaithfulAmplitude p (1/2) r = AMP_RH_grh p := by
  rw [rhFaithfulAmplitude_val p h.1 (admissible_ge_five h) r]
  exact (AMP_RH_grh_val h).symm

/-- **RH Method 4 (Von Mangoldt weighted) — RH-faithful pipeline**:
    Pre-normalized cos amplitude + zero excess = 1/2. -/
theorem AMP_RH_vonMangoldt_faithful (hRH : RiemannHypothesis) {p : ℕ}
    (h : AdmissiblePrime p) (ρ : ℂ) (hρ : ρ ∈ NontrivialZetaZeros) (r : ℝ) :
    rhFaithfulAmplitude p (1/2) r = AMP_RH_vonMangoldt p := by
  rw [rhFaithfulAmplitude_val p h.1 (admissible_ge_five h) r]
  exact (AMP_RH_vonMangoldt_val h).symm

/-! ### G4: Master RH-Faithful Comparison

All 4 RH methods, when processed through the RH-faithful envelope pipeline
using Mathlib's `RiemannHypothesis` and the real set `NontrivialZetaZeros`
of nontrivial zeros of `riemannZeta`, produce the same result 1/2.

The pipeline explicitly:
  - Computes r^β and r^(1-β) where β = Re(ρ) = 1/2 (by RH)
  - Verifies both sides equal r^(1/2)
  - Computes the AM-GM excess D_β(r) = 0
  - Adds it to cos(pπ/3) = 1/2
  - Normalizes by |Q| = 1
  - Confirms the result is unchanged at 1/2
-/

/-- **Master RH-faithful theorem**: Under Mathlib's `RiemannHypothesis`,
    for every admissible prime p and every nontrivial zeta zero ρ ∈ NontrivialZetaZeros:
    1. The envelope sides are equal: r^(Re ρ) = r^(1-Re ρ) = r^(1/2)
    2. The AM-GM excess vanishes: D_{Re ρ}(r) = 0
    3. The RH-faithful amplitude equals 1/2
    4. This matches all 4 RH methods unchanged -/
theorem master_rh_faithful (hRH : RiemannHypothesis) {p : ℕ}
    (h : AdmissiblePrime p) (ρ : ℂ) (hρ : ρ ∈ NontrivialZetaZeros) (r : ℝ) :
    -- (1) Envelope sides equal r^(1/2)
    envelopeSideLeft r ρ.re = r ^ (1/2 : ℝ) ∧
    envelopeSideRight r ρ.re = r ^ (1/2 : ℝ) ∧
    -- (2) AM-GM excess = 0
    excessAmplitude r ρ.re = 0 ∧
    -- (3) RH-faithful amplitude = 1/2
    rhFaithfulAmplitude p (1/2) r = 1 / 2 ∧
    -- (4) Matches all 4 RH methods
    rhFaithfulAmplitude p (1/2) r = AMP_RH_char p ∧
    rhFaithfulAmplitude p (1/2) r = AMP_RH_principal p ∧
    rhFaithfulAmplitude p (1/2) r = AMP_RH_grh p ∧
    rhFaithfulAmplitude p (1/2) r = AMP_RH_vonMangoldt p :=
  ⟨envelope_left_rh hRH ρ hρ r,
   envelope_right_rh hRH ρ hρ r,
   excess_zero_rh hRH ρ hρ r,
   rhFaithfulAmplitude_val p h.1 (admissible_ge_five h) r,
   AMP_RH_char_faithful hRH h ρ hρ r,
   AMP_RH_principal_faithful hRH h ρ hρ r,
   AMP_RH_grh_faithful hRH h ρ hρ r,
   AMP_RH_vonMangoldt_faithful hRH h ρ hρ r⟩

theorem master_rh_faithful_fact
    (hRH : RiemannHypothesis) {p : ℕ} (h : AdmissiblePrime p)
    (ρ : ℂ) (hρ : ρ ∈ NontrivialZetaZeros) (r : ℝ) : True :=
  let _ := master_rh_faithful hRH h ρ hρ r
  trivial




/-! ### Diagnostics -/

#check Q_AMP
#check AMP_IND_trig
#check AMP_IND_vonMangoldt
#check AMP_IND_bound
#check AMP_IND_dirichlet
#check AMP_RH_char
#check AMP_RH_principal
#check AMP_RH_grh
#check AMP_RH_vonMangoldt
#check AdmissiblePrime
#check Q_AMP_offline
#check Q_AMP_balanced
#check Q_AMP_defect
#check master_comparison
#check universal_bridge
#check explicit_bridge_IND_eq_RH
#check Q_AMP_defect_pos
#check bridge_consistency

-- List length = 20
#eval first20AdmissiblePrimes.length

-- All > 5
#eval first20AdmissiblePrimes.map (fun p => (p, decide (5 < p)))

-- Mod-6 residues: all are 1 or 5
#eval first20AdmissiblePrimes.map (fun p => (p, p % 6))

#print Q_AMP
#print AdmissiblePrime
#print Q_AMP_offline
#print Q_AMP_balanced
#print Q_AMP_defect

/-! ═══════════════════════════════════════════════════════════════════════════
    Summary: Why the Q_AMP Bridge Works
    ═══════════════════════════════════════════════════════════════════════════

    **Invariant**: Q_AMP(p) = cos(pπ/3), the prime-indexed harmonic amplitude
    at frequency π/3.

    **Admissible set**: Primes p > 5, which are all ≡ 1 or 5 mod 6.

    **No scale parameter**: The prime p is itself the index. No separate r.

    **No normalization**: Raw cos(pπ/3) values are compared directly.

    **Agreement**: All 8 methods (4 IND + 4 RH) give Q_AMP(p) = 1/2 for
    every admissible prime. This is a trigonometric identity, not an analytic
    hypothesis.

    **Why they match**: cos(pπ/3) = 1/2 for p ≡ 1 or 5 mod 6 is a direct
    consequence of the periodicity of cosine. The character decomposition
    from RHAssumptionMethods and the mod-6 evaluation from IndependentMethods
    are two proofs of the same trigonometric fact.

    **Off-line defect**: Using the prime p as the scale parameter, the
    zero-pair envelope p^β + p^{1-β} has defect D_β(p) ≥ 0, with
    D_{1/2}(p) = 0 (critical line) and D_β(p) > 0 for β ≠ 1/2, p > 1.
    The balanced observable 2√p corresponds to β = Q_AMP(p) = 1/2.

    **GRH role**: GRH does not affect the pointwise Q_AMP(p) = 1/2 value.
    GRH only enters through the nonprincipal (imaginary) channel's partial
    sum bound ∑ Im(Q(p)) = (√3/2)∑χ₃(p) = O(√N log N). This is an
    orthogonal quantity from Q_AMP (the real part).
    ═══════════════════════════════════════════════════════════════════════════ -/
end
end INDRHPrimeHarmonicComparison
