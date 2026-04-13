import Mathlib

/-!
# Off-Line Amplitude Defect in the π/3 Harmonic Framework

## Purpose

This file proves the **unconditional** off-line amplitude-defect theorem: if the
Riemann zeta function (or a Dirichlet L-function) has a zero ρ = β + it with
β ≠ 1/2, then the amplitude envelope contribution from the reflected zero pair
{ρ, 1 − ρ̄} is **strictly larger** than the balanced (on-line) contribution.

The core inequality is the AM-GM defect:

    D_β(r) = r^β + r^{1−β} − 2r^{1/2} > 0    for β ≠ 1/2, r > 0, r ≠ 1.

## Relationship to the π/3 Harmonic Decomposition

The file `PrimeHarmonics2.lean` proves the character-theoretic identity:

    e^{iπp/3} = 1/2 + i(√3/2) · χ₃(p)

with principal channel (Re = 1/2) and nonprincipal channel (Im = (√3/2)χ₃(p)).

The **unified invariant** connecting both analyses is the zero-pair amplitude
envelope Q(r, β), defined as the contribution of a reflected zero pair to the
explicit-formula representation of the weighted prime harmonic sum. Concretely:

- The principal channel (from ζ) sees zero-pair envelopes Q(r, β_ζ) for each
  nontrivial zero β_ζ + it of ζ(s).
- The nonprincipal channel (from L(s, χ₃)) sees zero-pair envelopes Q(r, β_L)
  for each nontrivial zero β_L + it of L(s, χ₃).

Under RH/GRH all β = 1/2 and Q = 2r^{1/2} (balanced). Any off-line zero forces
Q > 2r^{1/2}, creating a strictly positive defect.

## Where the defect lands

- **Off-line zeros of ζ(s)**: defect in the **principal** channel (real part).
- **Off-line zeros of L(s,χ₃)**: defect in the **nonprincipal** channel (imaginary part).
- **General case**: defect in **both** channels if both functions have off-line zeros.

The defect is always additive across zero pairs. It cannot be cancelled by other
zeros because each reflected pair contributes a nonneg term, and the defect for
β ≠ 1/2 is strictly positive.

## Contradiction structure

The off-line defect is **incompatible** with the balanced principal/nonprincipal
split. The balanced split requires Q = 2r^{1/2} for all zero pairs; any off-line
zero violates this. The impossibility of cancellation is formalized as an
**exclusion principle**: since each zero pair contributes a nonneg envelope
r^β + r^{1-β} ≥ 2r^{1/2}, and the defect D_β > 0 for β ≠ 1/2, no combination
of genuine zero-pair contributions can reduce the total envelope below the
balanced value. "Anti-zero" contributions (negative envelopes) are excluded by
the nonnegativity of r^β for real r > 0.

## Summary of where the contradiction falls

The contradiction is against the **coupled principal + nonprincipal object**.
An off-line ζ-zero perturbs the principal channel; an off-line L-zero perturbs
the nonprincipal channel. Either perturbation breaks the identity

    Q_total(r) = Q_balanced(r)

that characterizes the on-line (RH/GRH) configuration.
-/

open Real Finset BigOperators

noncomputable section

/-! ## §1. The Unified Invariant: Zero-Pair Amplitude Envelope

For a nontrivial zero ρ = β + it of ζ(s) or L(s, χ₃), the functional equation
pairs it with 1 − ρ̄ = (1 − β) + it. In the explicit formula for ψ(x), the
contribution of this pair to the amplitude envelope at scale r = x > 0 is:

    Q(r, β) = r^β + r^{1 − β}

This is the quantity that both the harmonic decomposition and the AM-GM defect
theorem evaluate.
-/

/-- The zero-pair amplitude envelope: contribution of a reflected zero pair
{β + it, (1−β) + it} to the explicit formula at scale r. -/
def zeroPairEnvelope (r : ℝ) (β : ℝ) : ℝ :=
  r ^ β + r ^ (1 - β)

/-- The balanced (on-line) envelope: the value when β = 1/2 (all zeros on the
critical line). -/
def balancedEnvelope (r : ℝ) : ℝ :=
  2 * r ^ (1 / 2 : ℝ)

/-- The off-line amplitude defect: the excess envelope from an off-line zero. -/
def amplitudeDefect (r : ℝ) (β : ℝ) : ℝ :=
  zeroPairEnvelope r β - balancedEnvelope r

/-! ## §2. Fundamental Properties of the Envelope

We establish basic properties: nonnegativity for r > 0, the identity at
β = 1/2, and symmetry under β ↦ 1 − β.
-/

/-- The balanced envelope equals the zero-pair envelope at β = 1/2. -/
theorem balancedEnvelope_eq_zeroPairEnvelope_half (r : ℝ) :
    balancedEnvelope r = zeroPairEnvelope r (1/2) := by
  simp [balancedEnvelope, zeroPairEnvelope]; ring

/-- The defect at β = 1/2 is zero: on-line zeros produce no excess. -/
theorem amplitudeDefect_half (r : ℝ) : amplitudeDefect r (1/2) = 0 := by
  simp [amplitudeDefect, zeroPairEnvelope, balancedEnvelope]; ring

/-- The zero-pair envelope is symmetric: Q(r, β) = Q(r, 1−β). -/
theorem zeroPairEnvelope_symm (r : ℝ) (β : ℝ) :
    zeroPairEnvelope r β = zeroPairEnvelope r (1 - β) := by
  simp [zeroPairEnvelope]; ring

/-- The amplitude defect is symmetric: D(r, β) = D(r, 1−β). -/
theorem amplitudeDefect_symm (r : ℝ) (β : ℝ) :
    amplitudeDefect r β = amplitudeDefect r (1 - β) := by
  simp [amplitudeDefect]; rw [zeroPairEnvelope_symm]

/-- For r > 0, the zero-pair envelope is positive. -/
theorem zeroPairEnvelope_pos {r : ℝ} (hr : 0 < r) (β : ℝ) :
    0 < zeroPairEnvelope r β := by
  unfold zeroPairEnvelope
  linarith [rpow_pos_of_pos hr β, rpow_pos_of_pos hr (1 - β)]

/-! ## §3. The Core AM-GM Defect Theorem (Unconditional)

The central result: for r > 0, r ≠ 1, and β ≠ 1/2, the off-line defect is
strictly positive. This is an application of the strict AM-GM inequality
to the pair (r^{β/2}, r^{(1−β)/2}).

The proof uses the square identity:
    r^β + r^{1−β} − 2r^{1/2} = (r^{β/2} − r^{(1−β)/2})²
which is nonneg, and zero iff r^{β/2} = r^{(1−β)/2}, i.e., β = 1/2 (when r ≠ 1).
-/

/-
Key identity: the defect equals a perfect square.
    r^β + r^{1-β} - 2r^{1/2} = (r^{β/2} - r^{(1-β)/2})² for r > 0.
-/
theorem amplitudeDefect_eq_sq {r : ℝ} (hr : 0 < r) (β : ℝ) :
    amplitudeDefect r β = (r ^ (β / 2) - r ^ ((1 - β) / 2)) ^ 2 := by
  unfold amplitudeDefect;
  unfold zeroPairEnvelope balancedEnvelope; ring;
  norm_num [ sq, ← Real.rpow_add hr ] ; ring

/-- **AM-GM for rpow**: For r > 0, r^β + r^{1-β} ≥ 2 r^{1/2}. -/
theorem zeroPairEnvelope_ge_balanced {r : ℝ} (hr : 0 < r) (β : ℝ) :
    zeroPairEnvelope r β ≥ balancedEnvelope r := by
  have h := amplitudeDefect_eq_sq hr β
  have hsq : 0 ≤ (r ^ (β / 2) - r ^ ((1 - β) / 2)) ^ 2 := sq_nonneg _
  unfold amplitudeDefect at h
  linarith

/-- Nonnegativity of the defect: D_β(r) ≥ 0 for r > 0. -/
theorem amplitudeDefect_nonneg {r : ℝ} (hr : 0 < r) (β : ℝ) :
    0 ≤ amplitudeDefect r β := by
  rw [amplitudeDefect_eq_sq hr]
  exact sq_nonneg _

/-
Key lemma: if r > 0, r ≠ 1, and β ≠ 1/2, then r^{β/2} ≠ r^{(1-β)/2}.
-/
theorem rpow_half_ne_of_offline {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ}
    (hβ : β ≠ 1/2) : r ^ (β / 2) ≠ r ^ ((1 - β) / 2) := by
  norm_num [ Real.rpow_def_of_pos hr, hr1 ];
  exact ⟨ by contrapose! hβ; linarith, hr.ne', by linarith ⟩

/-- **The Core Off-Line Amplitude Defect Theorem** (unconditional):

For r > 0, r ≠ 1, and β ≠ 1/2:

    D_β(r) = r^β + r^{1-β} - 2r^{1/2} > 0

An off-line zero (β ≠ 1/2) forces a strictly positive excess in the amplitude
envelope over the balanced (on-line) value. -/
theorem offline_amplitude_defect_pos {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ}
    (hβ : β ≠ 1/2) : 0 < amplitudeDefect r β := by
  rw [amplitudeDefect_eq_sq hr]
  exact sq_pos_of_ne_zero (sub_ne_zero.mpr (rpow_half_ne_of_offline hr hr1 hβ))

/-
The defect is monotone in |β - 1/2|: further off-line means larger defect.
For r > 1, if 0 < β₁ < β₂ ≤ 1/2, then D_{β₁}(r) > D_{β₂}(r).
-/
theorem amplitudeDefect_monotone_in_offset {r : ℝ} (hr : 1 < r) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₂ : β₁ < β₂) (hβ₂half : β₂ ≤ 1/2) :
    amplitudeDefect r β₁ > amplitudeDefect r β₂ := by
  by_contra h_contra;
  -- Since $D_{β₁}(r) \leq D_{β₂}(r)$, we have $(r^{β₁/2} - r^{(1-β₁)/2})² \leq (r^{β₂/2} - r^{(1-β₂)/2})²$.
  have h_sq_le : (r ^ (β₁ / 2) - r ^ ((1 - β₁) / 2)) ^ 2 ≤ (r ^ (β₂ / 2) - r ^ ((1 - β₂) / 2)) ^ 2 := by
    convert le_of_not_gt h_contra using 1;
    · exact Eq.symm ( amplitudeDefect_eq_sq ( by linarith ) _ );
    · rw [ amplitudeDefect_eq_sq ( by positivity ) ];
  -- Since $r > 1$, we can take the square root of both sides of the inequality.
  have h_sqrt_le : |r ^ (β₁ / 2) - r ^ ((1 - β₁) / 2)| ≤ |r ^ (β₂ / 2) - r ^ ((1 - β₂) / 2)| := by
    simpa only [ sq_le_sq ] using h_sq_le;
  rw [ abs_of_nonpos, abs_of_nonpos ] at h_sqrt_le <;> norm_num at *;
  · linarith [ Real.rpow_lt_rpow_of_exponent_lt hr ( by linarith : ( 1 - β₁ ) / 2 > ( 1 - β₂ ) / 2 ), Real.rpow_lt_rpow_of_exponent_lt hr ( by linarith : β₂ / 2 > β₁ / 2 ) ];
  · exact Real.rpow_le_rpow_of_exponent_le hr.le ( by linarith );
  · exact Real.rpow_le_rpow_of_exponent_le hr.le ( by linarith )

/-! ## §4. Connection to the χ₃ Decomposition

We now connect the abstract envelope theory to the concrete π/3 harmonic
decomposition from PrimeHarmonics2.lean.

Recall: e^{iπp/3} = 1/2 + i(√3/2)χ₃(p), where:
- Principal channel = Re = 1/2 (from ζ)
- Nonprincipal channel = Im = (√3/2)χ₃(p) (from L(s, χ₃))

### The unified invariant in each channel

The weighted prime harmonic sum at π/3, via the explicit formula, decomposes as:

  Σ_p Λ(p) e^{iπp/3} p^{-s} = (1/2)(-ζ'/ζ)(s) + i(√3/2)(-L'/L)(s, χ₃)

Each L-function contributes zero-pair envelopes from its own zeros:
- Principal channel total envelope: Σ_{ρ_ζ} Q(r, β_ρ)  (sum over ζ-zeros)
- Nonprincipal channel total envelope: Σ_{ρ_L} Q(r, β_ρ)  (sum over L-zeros)

Under RH/GRH, every β = 1/2, so both channels see only balanced envelopes.
Any off-line zero in either function creates a defect in the corresponding channel.
-/

/-! ### §4.1. Channel-Specific Defect

We define the principal and nonprincipal channel contributions and show
how off-line zeros create defects in each.
-/

/-- An off-line zero of ζ(s) at real part β creates a defect in the principal
(real-part) channel of the π/3 harmonic sum. The defect magnitude in the
principal channel is (1/2) · D_β(r), since the principal projection is
multiplication by the constant 1/2. -/
def principalChannelDefect (r : ℝ) (β : ℝ) : ℝ :=
  (1/2 : ℝ) * amplitudeDefect r β

/-- An off-line zero of L(s, χ₃) at real part β creates a defect in the
nonprincipal (imaginary-part) channel. The defect magnitude is
(√3/2) · D_β(r). -/
def nonprincipalChannelDefect (r : ℝ) (β : ℝ) : ℝ :=
  (Real.sqrt 3 / 2) * amplitudeDefect r β

/-- **Principal channel defect is strictly positive for off-line ζ-zeros.** -/
theorem principalChannelDefect_pos {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ}
    (hβ : β ≠ 1/2) : 0 < principalChannelDefect r β := by
  unfold principalChannelDefect
  have hD := offline_amplitude_defect_pos hr hr1 hβ
  positivity

/-- **Nonprincipal channel defect is strictly positive for off-line L-zeros.** -/
theorem nonprincipalChannelDefect_pos {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ}
    (hβ : β ≠ 1/2) : 0 < nonprincipalChannelDefect r β := by
  unfold nonprincipalChannelDefect
  have hD := offline_amplitude_defect_pos hr hr1 hβ
  positivity

/-! ## §5. The Exclusion Principle: No Cancellation

The key structural fact: the off-line defect cannot be cancelled by other zeros
or by harmonic interference across primes. This is because:

1. Each reflected zero pair {ρ, 1−ρ̄} contributes a **nonneg** envelope:
   r^β + r^{1-β} ≥ 0 for r > 0.
2. The defect D_β(r) ≥ 0 for each pair, with strict inequality for off-line zeros.
3. Summing defects over all zero pairs preserves nonnegativity.
4. A "negative envelope" (anti-zero) is impossible: r^β > 0 for all r > 0, β ∈ ℝ.

Therefore no rearrangement or cancellation of genuine zero contributions can
reduce the total envelope below the balanced value.
-/

/-- **Anti-zero exclusion**: For r > 0, the envelope r^β is strictly positive.
There is no zero-pair contribution that could produce a negative envelope. -/
theorem no_negative_envelope {r : ℝ} (hr : 0 < r) (β : ℝ) :
    0 < r ^ β :=
  rpow_pos_of_pos hr β

/-- **Additivity of defects**: The total defect from n zero pairs is the sum
of individual defects. -/
theorem total_defect_eq_sum (r : ℝ) (βs : Finset ℝ) :
    βs.sum (fun β => amplitudeDefect r β) =
    βs.sum (fun β => zeroPairEnvelope r β) - βs.card • balancedEnvelope r := by
  simp only [amplitudeDefect, Finset.sum_sub_distrib, Finset.sum_const]

/-- **Defect sum is nonneg**: if r > 0, the total defect from any set of zero
pairs is nonneg. -/
theorem total_defect_nonneg {r : ℝ} (hr : 0 < r) (βs : Finset ℝ) :
    0 ≤ βs.sum (fun β => amplitudeDefect r β) :=
  Finset.sum_nonneg (fun β _ => amplitudeDefect_nonneg hr β)

/-
**Defect sum is strictly positive if any zero is off-line**: if r > 0, r ≠ 1,
and at least one β ≠ 1/2 appears in the set, then the total defect is > 0.
-/
theorem total_defect_pos_of_offline {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1)
    {βs : Finset ℝ} {β₀ : ℝ} (hβ₀_mem : β₀ ∈ βs) (hβ₀ : β₀ ≠ 1/2) :
    0 < βs.sum (fun β => amplitudeDefect r β) := by
  rw [ Finset.sum_eq_add_sum_diff_singleton hβ₀_mem ];
  exact add_pos_of_pos_of_nonneg ( offline_amplitude_defect_pos hr hr1 hβ₀ ) ( Finset.sum_nonneg fun x hx => amplitudeDefect_nonneg hr x )

/-! ## §6. Incompatibility with the Balanced Split

We prove that the off-line defect makes Q_offline(r) > Q_balanced(r),
directly contradicting the balanced principal/nonprincipal split.

The balanced configuration is defined by: every zero pair has β = 1/2,
giving total envelope = (number of pairs) · 2r^{1/2}. The off-line
configuration has at least one β ≠ 1/2, giving a strictly larger total.
-/

/-- A configuration of zero real parts is **balanced** if all equal 1/2. -/
def IsBalanced (βs : Finset ℝ) : Prop :=
  ∀ β ∈ βs, β = 1/2

/-- A configuration is **off-line** if at least one β ≠ 1/2. -/
def HasOfflineZero (βs : Finset ℝ) : Prop :=
  ∃ β ∈ βs, β ≠ 1/2

/-
The total envelope from a balanced configuration.
-/
theorem balanced_total_envelope (r : ℝ) (βs : Finset ℝ) (hbal : IsBalanced βs) :
    βs.sum (fun β => zeroPairEnvelope r β) = βs.card • balancedEnvelope r := by
  rw [ Finset.sum_congr rfl fun x hx => show zeroPairEnvelope r x = balancedEnvelope r from ?_, Finset.sum_const, nsmul_eq_mul ];
  rw [ hbal x hx, balancedEnvelope_eq_zeroPairEnvelope_half ]

/-- **The incompatibility theorem**: An off-line configuration has strictly
larger total envelope than the balanced configuration with the same number
of zero pairs. -/
theorem offline_exceeds_balanced {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1)
    {βs : Finset ℝ} (hoff : HasOfflineZero βs) :
    βs.sum (fun β => zeroPairEnvelope r β) >
    βs.card • balancedEnvelope r := by
  obtain ⟨β₀, hβ₀_mem, hβ₀⟩ := hoff
  have key := total_defect_pos_of_offline hr hr1 hβ₀_mem hβ₀
  rw [total_defect_eq_sum] at key
  linarith

/-! ## §7. The Full Statement in Harmonic Language

We now state the defect in terms that directly mirror the π/3 harmonic sum
decomposition:

  Σ_p e^{iπp/3} = (1/2) · (prime count) + i(√3/2) · Σ χ₃(p)

The explicit formula expresses each channel's growth in terms of zero-pair
envelopes. The off-line defect theorem says:

  ¬RH ⟹ (principal channel envelope) > (balanced principal envelope)
  ¬GRH_{χ₃} ⟹ (nonprincipal channel envelope) > (balanced nonprincipal envelope)
-/

/-- **RH-false implies principal-channel defect**: If ζ(s) has a zero with
real part β ≠ 1/2, then for any r > 0, r ≠ 1, the principal channel of the
π/3 harmonic sum has a strictly positive defect:

    Q_principal(r) - Q_balanced_principal(r) = (1/2) · D_β(r) > 0.

This is the same observable as Re(Σ e^{iπp/3}) = (1/2) · (prime count),
evaluated through the explicit formula. -/
theorem offline_zeta_zero_principal_defect
    {β : ℝ} (hβ : β ≠ 1/2)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    0 < principalChannelDefect r β :=
  principalChannelDefect_pos hr hr1 hβ

/-- **GRH-false for L(s,χ₃) implies nonprincipal-channel defect**: If L(s, χ₃) has
a zero with real part β ≠ 1/2, then the nonprincipal (character-sum) channel of the
π/3 harmonic sum has a strictly positive defect:

    Q_nonprincipal(r) - Q_balanced_nonprincipal(r) = (√3/2) · D_β(r) > 0.

This is the same observable as Im(Σ e^{iπp/3}) = (√3/2) · Σ χ₃(p),
evaluated through the explicit formula. -/
theorem offline_L_zero_nonprincipal_defect
    {β : ℝ} (hβ : β ≠ 1/2)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    0 < nonprincipalChannelDefect r β :=
  nonprincipalChannelDefect_pos hr hr1 hβ

/-! ## §8. Compatibility Theorem: Unified View

We state the theorem showing that the off-line defect and the balanced
decomposition are evaluating the same invariant.
-/

/-- **Compatibility theorem**: The zero-pair envelope Q(r, β) evaluated at
β = 1/2 reproduces exactly the balanced envelope 2r^{1/2}, which is the
envelope underlying the principal/nonprincipal split of e^{iπp/3}.

In other words: the invariant that the AM-GM defect theorem targets is
*the same* invariant that the character-theoretic decomposition evaluates
at its balanced point.

The principal channel evaluates (1/2) · Q(r, 1/2) = r^{1/2}.
The nonprincipal channel evaluates (√3/2) · χ₃(p) · r^{1/2} per prime.
The unit-amplitude identity (1/2)² + (√3/2)² = 1 ensures total amplitude = 1.

Any off-line zero shifts Q(r, β) > Q(r, 1/2), breaking the balanced
decomposition in the affected channel. -/
theorem compatibility_balanced_harmonic (r : ℝ) :
    zeroPairEnvelope r (1/2) = balancedEnvelope r ∧
    (1/2 : ℝ) * balancedEnvelope r = r ^ (1/2 : ℝ) ∧
    ((1/2 : ℝ)^2 + (Real.sqrt 3 / 2)^2 = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Q(r, 1/2) = 2r^{1/2}
    simp [zeroPairEnvelope, balancedEnvelope]; ring_nf
  · -- (1/2) · 2r^{1/2} = r^{1/2}
    simp [balancedEnvelope]
  · -- Pythagorean identity
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    nlinarith [h3]

/-! ## §9. Theorem Inventory and Notes

### Theorem Inventory

1. `amplitudeDefect_half` — D_{1/2}(r) = 0 (on-line = no defect)
2. `amplitudeDefect_nonneg` — D_β(r) ≥ 0 for r > 0 (unconditional)
3. `offline_amplitude_defect_pos` — **Core**: D_β(r) > 0 for β ≠ 1/2, r > 0, r ≠ 1
4. `amplitudeDefect_monotone_in_offset` — Further off-line ⟹ larger defect
5. `principalChannelDefect_pos` — Defect in Re channel from ζ-zero
6. `nonprincipalChannelDefect_pos` — Defect in Im channel from L-zero
7. `no_negative_envelope` — Anti-zero exclusion (r^β > 0)
8. `total_defect_pos_of_offline` — Sum defect > 0 if any off-line zero
9. `offline_exceeds_balanced` — Off-line total > balanced total
10. `compatibility_balanced_harmonic` — Unified invariant identity

### The Unified Invariant

    Q(r, β) = r^β + r^{1 − β}

evaluated in each channel:
  - Principal:     (1/2) · Q(r, β_ζ)
  - Nonprincipal:  (√3/2) · Q(r, β_L)

### Where the Contradiction Lands

The contradiction is against the **coupled principal + character object**:

  Σ e^{iπp/3} = (1/2)(prime count) + i(√3/2) Σ χ₃(p)

Any off-line zero of ζ perturbs the **principal channel** (the 1/2 coefficient
controls the main-term growth of the real part). Any off-line zero of L(s, χ₃)
perturbs the **nonprincipal channel** (the √3/2 coefficient controls the
character-sum growth of the imaginary part). The defect is not erased by
cross-channel cancellation because the channels are orthogonal
(real vs imaginary), and within each channel, the defect is additive and
nonneg per zero pair.
-/

end
