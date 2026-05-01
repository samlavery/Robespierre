import Mathlib
/-!
# Balance and Symmetry of Harmonics at π/3
We formalize properties of the harmonics derived from Euler's product at π/3.
The harmonics are the 6th roots of unity ω^n where ω = exp(iπ/3), equivalently
the values exp(inπ/3) for n = 0, 1, ..., 5.
## Main Results
1. **Balance (Cancellation)**: The sum of all harmonics vanishes:
   ∑_{n=0}^{5} ω^n = 0, which implies both ∑ cos(nπ/3) = 0 and ∑ sin(nπ/3) = 0.
2. **Schwarz Reflection around π/6**: The set of harmonics is invariant under the
   reflection z ↦ exp(iπ/3)·conj(z), which geometrically reflects across the line
   at angle π/6 from the real axis.
3. **Klein Four-Group Symmetry**: The set of harmonics is invariant under both
   complex conjugation (z ↦ conj(z)) and negation (z ↦ -z). These two involutions
   commute and generate a Klein four-group V₄ ≅ ℤ/2 × ℤ/2 acting on the harmonics.
   Under the 180° rotation (negation), the two "halves" of the harmonic set are
   mapped bijectively onto each other.
-/
open Complex Finset
set_option maxHeartbeats 800000
noncomputable section
/-- The primitive 6th root of unity ω = exp(iπ/3). -/
def omega : ℂ := Complex.exp (↑Real.pi * Complex.I / 3)
/-- The set of harmonics: {ω^n | n = 0, 1, ..., 5}. -/
def harmonicSet : Finset ℂ := (Finset.range 6).image (fun n => omega ^ n)
/-! ## Part 1: Balance — The sum of all harmonics vanishes -/
/-
The sixth power of ω equals 1, i.e., ω is a 6th root of unity.
-/
lemma omega_pow_six : omega ^ 6 = 1 := by
  rw [ show omega = Complex.exp ( Real.pi * Complex.I / 3 ) from rfl ];
  rw [ ← Complex.exp_nat_mul, mul_comm, Complex.exp_eq_one_iff ] ; use 1 ; ring
/-
**Balance Theorem**: The sum of all harmonics ω^n for n = 0,...,5 is zero.
This is the "unconditional balance" of the harmonic set.
-/
theorem harmonic_sum_vanishes :
    ∑ n ∈ Finset.range 6, omega ^ n = 0 := by
      erw [ geom_sum_eq ] <;> norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, ← Complex.exp_nat_mul ];
      · exact Or.inl ( by rw [ omega_pow_six ] ; norm_num );
      · unfold omega; norm_num [ Complex.exp_re, Complex.exp_im ] ;
/-
The real parts (cosines) of the harmonics sum to zero.
-/
theorem cos_harmonic_sum_vanishes :
    ∑ n ∈ Finset.range 6, (omega ^ n).re = 0 := by
      convert congr_arg Complex.re harmonic_sum_vanishes
/-
The imaginary parts (sines) of the harmonics sum to zero.
-/
theorem sin_harmonic_sum_vanishes :
    ∑ n ∈ Finset.range 6, (omega ^ n).im = 0 := by
      convert congr_arg Complex.im ( harmonic_sum_vanishes ) using 1
/-! ## Part 2: Schwarz Reflection around π/6
The Schwarz reflection across the line at angle π/6 from the real axis
maps z ↦ exp(iπ/3)·conj(z). We show the harmonic set is invariant. -/
/-- Schwarz reflection around π/6: z ↦ ω · conj(z). -/
def schwarzReflect (z : ℂ) : ℂ := omega * starRingEnd ℂ z
/-
For each harmonic ω^n, its Schwarz reflection ω·conj(ω^n) is also a harmonic ω^m
for some m. Specifically, ω·conj(ω^n) = ω^((1 + 6 - n) mod 6).
-/
theorem schwarz_reflects_harmonics (n : ℕ) (hn : n < 6) :
    ∃ m : ℕ, m < 6 ∧ schwarzReflect (omega ^ n) = omega ^ m := by
      -- By definition of $schwarzReflect$, we know that
      set z := omega ^ n
      have h_schwarz : schwarzReflect z = omega^(1 + (6 - n) % 6) := by
        -- By definition of $schwarzReflect$, we know that $schwarzReflect z = omega \cdot conj(z)$.
        have h_schwarz : schwarzReflect z = omega * starRingEnd ℂ z := by
          rfl;
        -- By definition of $omega$, we know that $starRingEnd ℂ (omega ^ n) = omega ^ (6 - n)$.
        have h_conj : starRingEnd ℂ (omega ^ n) = omega ^ (6 - n) := by
          interval_cases n <;> norm_num [ omega, pow_succ, Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
          all_goals constructor <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), pow_pos ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) 3, pow_pos ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) 4 ] ;
        rw [ h_schwarz, h_conj, ← pow_succ' ];
        interval_cases n <;> norm_num [ pow_succ' ];
        grind;
      interval_cases n <;> norm_num [ h_schwarz ];
      exacts [ ⟨ 1, by norm_num ⟩, ⟨ 0, by norm_num, by norm_num [ omega_pow_six ] ⟩, ⟨ 5, by norm_num ⟩, ⟨ 4, by norm_num ⟩, ⟨ 3, by norm_num ⟩, ⟨ 2, by norm_num ⟩ ]
/-
The conjugate values vanish under Schwarz reflection: for each harmonic,
    the harmonic plus its Schwarz-reflected conjugate telescope within the full set,
    giving the overall zero sum (balance).
-/
theorem schwarz_conjugates_cancel :
    ∑ n ∈ Finset.range 6, (omega ^ n + schwarzReflect (omega ^ n)) = 0 := by
      unfold schwarzReflect;
      -- We know ∑ω^n = 0 by harmonic_sum_vanishes. Also ∑conj(ω^n) = conj(∑ω^n) = conj(0) = 0.
      have h_sum_conj : ∑ n ∈ Finset.range 6, (starRingEnd ℂ (omega ^ n)) = 0 := by
        rw [ ← map_sum, harmonic_sum_vanishes ] ; norm_num;
      simp_all +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _ ]
      exact harmonic_sum_vanishes
/-! ## Part 3: Klein Four-Group Symmetry
The Klein four-group V₄ = {id, conj, neg, conj∘neg} acts on the harmonics.
Under negation (180° rotation), the "upper" harmonics {ω^1, ω^2} and
"lower" harmonics {ω^4, ω^5} are exchanged, while {1, -1} = {ω^0, ω^3} are fixed. -/
/-
Complex conjugation maps ω^n to ω^(6-n), preserving the harmonic set.
-/
theorem conj_preserves_harmonics (n : ℕ) (hn : n < 6) :
    ∃ m : ℕ, m < 6 ∧ starRingEnd ℂ (omega ^ n) = omega ^ m := by
      -- We can choose m = 6 - n, which is less than 6 since n < 6.
      use (6 - n) % 6;
      interval_cases n <;> simp_all +decide [ Complex.ext_iff, pow_succ' ];
      · unfold omega; norm_num [ Complex.exp_re, Complex.exp_im ] ; ring_nf ; norm_num;
        grind;
      · unfold omega; norm_num [ Complex.exp_re, Complex.exp_im, pow_succ' ] ; ring_nf; norm_num;
        constructor <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ];
      · unfold omega; norm_num [ Complex.exp_re, Complex.exp_im ] ; ring_nf; norm_num;
        norm_num [ pow_three ] ; ring;
      · norm_num [ Complex.normSq, Complex.div_re, Complex.div_im, Complex.exp_re, Complex.exp_im, omega ] ; ring ; norm_num;
        grind;
      · unfold omega; norm_num [ Complex.exp_re, Complex.exp_im ] ; ring_nf ; norm_num;
        grind
/-
Negation (180° rotation) maps ω^n to ω^(n+3), preserving the harmonic set.
-/
theorem neg_preserves_harmonics (n : ℕ) (hn : n < 6) :
    ∃ m : ℕ, m < 6 ∧ -(omega ^ n) = omega ^ m := by
      use (n + 3) % 6;
      unfold omega;
      interval_cases n <;> norm_num [ ← Complex.exp_nat_mul, Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
      all_goals norm_num [ show 2 * ( Real.pi / 3 ) = Real.pi - Real.pi / 3 by ring, show 3 * ( Real.pi / 3 ) = Real.pi by ring, show 4 * ( Real.pi / 3 ) = Real.pi + Real.pi / 3 by ring, show 5 * ( Real.pi / 3 ) = 2 * Real.pi - Real.pi / 3 by ring, Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub ]
/-
Negation maps ω^n to ω^(n+3 mod 6), giving a perfect pairing.
-/
theorem neg_harmonic_eq (n : ℕ) (hn : n < 6) :
    -(omega ^ n) = omega ^ ((n + 3) % 6) := by
      interval_cases n <;> norm_num [ pow_succ ];
      all_goals unfold omega; norm_num [ ← Complex.exp_nat_mul, Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ;
      all_goals constructor <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ), pow_pos ( Real.sqrt_pos.mpr ( show 0 < 3 by norm_num ) ) 3 ]
/-
The composition conj ∘ neg also preserves the harmonic set.
-/
theorem conj_neg_preserves_harmonics (n : ℕ) (hn : n < 6) :
    ∃ m : ℕ, m < 6 ∧ starRingEnd ℂ (-(omega ^ n)) = omega ^ m := by
      -- By definition of composition, we have $\star(-\omega^n) = \star(\omega^((n + 3) % 6))$.
      obtain ⟨m, hm₁, hm₂⟩ : ∃ m < 6, starRingEnd ℂ (omega ^ ((n + 3) % 6)) = omega ^ m := by
        exact conj_preserves_harmonics _ ( Nat.mod_lt _ ( by decide ) );
      have h_conj_neg : starRingEnd ℂ (-omega ^ n) = starRingEnd ℂ (omega ^ ((n + 3) % 6)) := by
        rw [ neg_harmonic_eq n hn ];
      aesop
/-
The Klein four-group operations {id, conj, neg, conj∘neg} each preserve the
harmonic set and satisfy V₄ relations: each is an involution and they commute.
-/
theorem klein_four_involutions (z : ℂ) :
    starRingEnd ℂ (starRingEnd ℂ z) = z ∧
    -(-z) = z ∧
    starRingEnd ℂ (-(starRingEnd ℂ (-(z)))) = z := by
      aesop
/-
Under 180° rotation (negation), the two halves {ω^0, ω^1, ω^2} and
{ω^3, ω^4, ω^5} are mapped bijectively onto each other, demonstrating
unconditional symmetry of the two sets of harmonics.
-/
theorem rotation_symmetry (n : ℕ) (_hn : n < 3) :
    -(omega ^ n) = omega ^ (n + 3) ∧ -(omega ^ (n + 3)) = omega ^ n := by
      norm_num [ omega, Complex.ext_iff, Complex.exp_re, Complex.exp_im, pow_succ ];
      grind
end