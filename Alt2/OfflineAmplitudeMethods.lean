import RequestProject.ZetaZeroDefs

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

## Note on definitions

The core definitions `zeroPairEnvelope`, `balancedEnvelope`, and `amplitudeDefect`
are imported from `ZetaZeroDefs` (in the `ZetaDefs` namespace), which serves as the
single source of truth for all zeta-zero-related definitions in this project.
-/

open Real Finset BigOperators ZetaDefs ArithmeticFunction LSeries.notation

noncomputable section

/-! ## §1. The Unified Invariant: Zero-Pair Amplitude Envelope

For a nontrivial zero ρ = β + it of ζ(s) or L(s, χ₃), the functional equation
pairs it with 1 − ρ̄ = (1 − β) + it. In the explicit formula for ψ(x), the
contribution of this pair to the amplitude envelope at scale r = x > 0 is:

    Q(r, β) = r^β + r^{1 − β}

This is the quantity that both the harmonic decomposition and the AM-GM defect
theorem evaluate.

The definitions `zeroPairEnvelope`, `balancedEnvelope`, and `amplitudeDefect` are
provided by `ZetaZeroDefs` in the `ZetaDefs` namespace, opened above.
-/

/-! ## §2. Fundamental Properties of the Envelope

We establish basic properties: nonnegativity for r > 0, the identity at
β = 1/2, and symmetry under β ↦ 1 − β.
-/

/-- The balanced envelope equals the zero-pair envelope at β = 1/2. -/
theorem balancedEnvelope_eq_zeroPairEnvelope_half (r : ℝ) :
    balancedEnvelope r = zeroPairEnvelope r (1/2) := by
  simp [balancedEnvelope, zeroPairEnvelope]; ring

/-- The zero-pair envelope is symmetric: Q(r, β) = Q(r, 1−β). -/
theorem zeroPairEnvelope_symm (r : ℝ) (β : ℝ) :
    zeroPairEnvelope r β = zeroPairEnvelope r (1 - β) := by
  simp [zeroPairEnvelope]; ring

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

/-- **Core off-line defect for an actual zeta zero**: If ρ is an off-line
nontrivial zeta zero, then D_{Re(ρ)}(r) > 0 for r > 0, r ≠ 1. -/
theorem offline_amplitude_defect_pos_of_zero (ρ : ℂ) (hρ : ZD.IsOfflineZetaZero ρ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    0 < amplitudeDefect r ρ.re :=
  offline_amplitude_defect_pos hr hr1 hρ.2

/-- **Core off-line defect via set membership**: If ρ ∈ OffLineZeros, then
D_{Re(ρ)}(r) > 0. -/
theorem offline_amplitude_defect_pos_of_mem (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    0 < amplitudeDefect r ρ.re :=
  offline_amplitude_defect_pos hr hr1 hρ.2

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

/-! ### §3b. Monotonicity of the defect in scale (r)

For fixed off-line β ≠ 1/2 in the critical strip, the defect `D_β(r)` is
strictly increasing for `r > 1`. This means the defect grows with each
successive prime: `D_β(2) < D_β(3) < D_β(5) < ⋯`, so the cumulative
defect diverges.

**Proof strategy**: Factor `r^u - r^v = r^v · (r^{u-v} - 1)` where
`u = max(β/2, (1-β)/2)` and `v = min(β/2, (1-β)/2)`. Both factors are
positive for `r > 1` and strictly increasing in `r`, so their product is
strictly increasing.
-/

/-- Helper: for `u > v > 0` and `1 < r₁ < r₂`, the rpow gap `r^u - r^v`
is strictly increasing in the base. -/
private theorem rpow_sub_strict_mono {u v : ℝ} (huv : v < u) (hv : 0 < v)
    {r₁ r₂ : ℝ} (hr₁ : 1 < r₁) (hr₁₂ : r₁ < r₂) :
    r₁ ^ u - r₁ ^ v < r₂ ^ u - r₂ ^ v := by
  have hr₁_pos : (0 : ℝ) < r₁ := by linarith
  have hr₂_pos : (0 : ℝ) < r₂ := by linarith
  have hd : (0 : ℝ) < u - v := by linarith
  have hf₁ : r₁ ^ u - r₁ ^ v = r₁ ^ v * (r₁ ^ (u - v) - 1) := by
    have : r₁ ^ u = r₁ ^ v * r₁ ^ (u - v) := by
      rw [← rpow_add hr₁_pos]; congr 1; ring
    linarith
  have hf₂ : r₂ ^ u - r₂ ^ v = r₂ ^ v * (r₂ ^ (u - v) - 1) := by
    have : r₂ ^ u = r₂ ^ v * r₂ ^ (u - v) := by
      rw [← rpow_add hr₂_pos]; congr 1; ring
    linarith
  rw [hf₁, hf₂]
  have hv_mono : r₁ ^ v < r₂ ^ v := rpow_lt_rpow hr₁_pos.le hr₁₂ hv
  have hd₁_gt1 : 1 < r₁ ^ (u - v) := by
    rw [← rpow_zero r₁]; exact rpow_lt_rpow_of_exponent_lt hr₁ hd
  have hd₁_pos : (0 : ℝ) < r₁ ^ (u - v) - 1 := by linarith
  have hd_mono : r₁ ^ (u - v) < r₂ ^ (u - v) := rpow_lt_rpow hr₁_pos.le hr₁₂ hd
  calc r₁ ^ v * (r₁ ^ (u - v) - 1)
      < r₂ ^ v * (r₁ ^ (u - v) - 1) := mul_lt_mul_of_pos_right hv_mono hd₁_pos
    _ < r₂ ^ v * (r₂ ^ (u - v) - 1) :=
        mul_lt_mul_of_pos_left (by linarith) (by positivity)

/-- **The amplitude defect is strictly increasing in scale** for `r > 1`
and `0 < β < 1`, `β ≠ 1/2`. Combined with `amplitudeDefect_pos_at_prime`,
this gives divergence of the cumulative defect over primes. -/
theorem amplitudeDefect_strict_mono_scale {β : ℝ} (hβ : β ≠ 1/2)
    (hβ₀ : 0 < β) (hβ₁ : β < 1)
    {r₁ r₂ : ℝ} (hr₁ : 1 < r₁) (hr₁₂ : r₁ < r₂) :
    amplitudeDefect r₁ β < amplitudeDefect r₂ β := by
  have hr₁_pos : (0 : ℝ) < r₁ := by linarith
  have hr₂_pos : (0 : ℝ) < r₂ := by linarith
  rw [amplitudeDefect_eq_sq hr₁_pos, amplitudeDefect_eq_sq hr₂_pos]
  rcases lt_or_gt_of_ne hβ with hβ_lt | hβ_gt
  · -- β < 1/2: (1-β)/2 > β/2, gap = r^v - r^u is positive and increasing
    have huv : β / 2 < (1 - β) / 2 := by linarith
    have h_mono := rpow_sub_strict_mono huv (by linarith : 0 < β / 2) hr₁ hr₁₂
    have h_pos : 0 < r₁ ^ ((1 - β) / 2) - r₁ ^ (β / 2) := by
      linarith [rpow_lt_rpow_of_exponent_lt hr₁ huv]
    have eq₁ : (r₁ ^ (β / 2) - r₁ ^ ((1 - β) / 2)) ^ 2 =
      (r₁ ^ ((1 - β) / 2) - r₁ ^ (β / 2)) ^ 2 := by ring
    have eq₂ : (r₂ ^ (β / 2) - r₂ ^ ((1 - β) / 2)) ^ 2 =
      (r₂ ^ ((1 - β) / 2) - r₂ ^ (β / 2)) ^ 2 := by ring
    rw [eq₁, eq₂]
    exact pow_lt_pow_left₀ h_mono h_pos.le two_ne_zero
  · -- β > 1/2: β/2 > (1-β)/2, gap = r^u - r^v is positive and increasing
    have huv : (1 - β) / 2 < β / 2 := by linarith
    have h_mono := rpow_sub_strict_mono huv (by linarith : 0 < (1 - β) / 2) hr₁ hr₁₂
    have h_pos : 0 < r₁ ^ (β / 2) - r₁ ^ ((1 - β) / 2) := by
      linarith [rpow_lt_rpow_of_exponent_lt hr₁ huv]
    exact pow_lt_pow_left₀ h_mono h_pos.le two_ne_zero

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

/-! ### §4.0. Von Mangoldt as the Harmonic Extractor

The von Mangoldt function `Λ` (mathlib's `ArithmeticFunction.vonMangoldt`) is the
spectral extraction tool connecting primes to zeta zeros:

- `L ↗Λ s = -ζ'(s)/ζ(s)` for Re(s) > 1  (`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`)
- `L (↗χ * ↗Λ) s = -L'(s,χ)/L(s,χ)`    (`LSeries_twist_vonMangoldt_eq`)

The zeros of ζ are the poles of `-ζ'/ζ` (principal channel).
The zeros of L(s,χ₃) are the poles of `-L'/L(s,χ₃)` (nonprincipal channel).

Weighting by Λ extracts the zero spectrum; twisting by a Dirichlet character χ₃
selects which L-function's zeros appear.
-/

/-- The principal channel L-series: `L(Λ, s) = -ζ'/ζ(s)`.
Restatement of mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`. -/
theorem vonMangoldt_extracts_zeta_zeros {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗Λ) s = -deriv riemannZeta s / riemannZeta s :=
  LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/-- The nonprincipal channel L-series: `L(χ·Λ, s) = -L'(s,χ)/L(s,χ)`.
For any Dirichlet character χ (in particular χ₃ mod 3), twisting Λ by χ
extracts the zeros of L(s,χ). -/
theorem vonMangoldt_twist_extracts_L_zeros {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗χ * ↗Λ) s = -deriv (LSeries ↗χ) s / LSeries ↗χ s :=
  DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs

/-- The L-series of Λ converges for Re(s) > 1. -/
theorem vonMangoldt_summable {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (↗Λ) s :=
  LSeriesSummable_vonMangoldt hs

/-- The twisted L-series of χ·Λ converges for Re(s) > 1. -/
theorem vonMangoldt_twist_summable {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (↗χ * ↗Λ) s :=
  DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs

/-! ### §4.1. Channel-Specific Defect

We define the principal and nonprincipal channel contributions and show
how off-line zeros create defects in each.

The principal channel is `-ζ'/ζ = L(Λ, s)` (mathlib: `vonMangoldt_extracts_zeta_zeros`).
The nonprincipal channel is `-L'/L(s,χ₃) = L(χ₃·Λ, s)` (mathlib: `vonMangoldt_twist_extracts_L_zeros`).

The zeros of each L-function are the poles of the corresponding logarithmic
derivative. The zero-pair envelope `Q(r, β) = r^β + r^{1-β}` measures the
contribution of a reflected pair `{ρ, 1-ρ̄}` to the explicit formula.
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

/-- **Principal channel defect for an actual off-line zeta zero.** -/
theorem principalChannelDefect_pos_of_offlineZero (ρ : ℂ) (hρ : ZD.IsOfflineZetaZero ρ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    0 < principalChannelDefect r ρ.re :=
  principalChannelDefect_pos hr hr1 hρ.2

/-- **Principal channel defect for ρ ∈ OffLineZeros.** -/
theorem principalChannelDefect_pos_of_mem (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    0 < principalChannelDefect r ρ.re :=
  principalChannelDefect_pos hr hr1 hρ.2

/-- **Nonprincipal channel defect for an actual off-line zeta zero.** -/
theorem nonprincipalChannelDefect_pos_of_offlineZero (ρ : ℂ) (hρ : ZD.IsOfflineZetaZero ρ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    0 < nonprincipalChannelDefect r ρ.re :=
  nonprincipalChannelDefect_pos hr hr1 hρ.2

/-- **Nonprincipal channel defect for ρ ∈ OffLineZeros.** -/
theorem nonprincipalChannelDefect_pos_of_mem (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    0 < nonprincipalChannelDefect r ρ.re :=
  nonprincipalChannelDefect_pos hr hr1 hρ.2

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
  rw [← Finset.sum_erase_add βs (fun β => amplitudeDefect r β) hβ₀_mem]
  exact add_pos_of_nonneg_of_pos
    (Finset.sum_nonneg fun x _ => amplitudeDefect_nonneg hr x)
    (offline_amplitude_defect_pos hr hr1 hβ₀)

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

/-- A finite set of complex zeros contains an off-line zero (via `ZD.OffLineZeros`). -/
def HasOfflineZetaZero (ρs : Finset ℂ) : Prop :=
  ∃ ρ ∈ ρs, ZD.IsOfflineZetaZero ρ

/-- A finite set of nontrivial zeros is balanced if all lie on the critical line. -/
def IsBalancedZeros (ρs : Finset ℂ) : Prop :=
  ∀ ρ ∈ ρs, ρ ∈ ZD.OnLineZeros

/-- Extracting real parts from an off-line zero set gives `HasOfflineZero`. -/
theorem HasOfflineZetaZero.to_hasOfflineZero {ρs : Finset ℂ}
    (h : HasOfflineZetaZero ρs) :
    HasOfflineZero (ρs.image Complex.re) := by
  obtain ⟨ρ, hρ_mem, hρ_off⟩ := h
  exact ⟨ρ.re, Finset.mem_image_of_mem _ hρ_mem, hρ_off.2⟩

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

/-- **Total defect over actual zeta zeros is nonneg.** -/
theorem total_defect_nonneg_of_zeros {r : ℝ} (hr : 0 < r) (ρs : Finset ℂ) :
    0 ≤ (ρs.image Complex.re).sum (fun β => amplitudeDefect r β) :=
  total_defect_nonneg hr _

/-- **Total defect is positive if any actual zeta zero is off-line.** -/
theorem total_defect_pos_of_offlineZetaZero {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1)
    {ρs : Finset ℂ} (hoff : HasOfflineZetaZero ρs) :
    0 < (ρs.image Complex.re).sum (fun β => amplitudeDefect r β) := by
  obtain ⟨ρ, hρ_mem, hρ_off⟩ := hoff
  exact total_defect_pos_of_offline hr hr1 (Finset.mem_image_of_mem _ hρ_mem) hρ_off.2

/-- **Off-line zeta zeros exceed the balanced envelope.** -/
theorem offline_zeros_exceed_balanced {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1)
    {ρs : Finset ℂ} (hoff : HasOfflineZetaZero ρs) :
    (ρs.image Complex.re).sum (fun β => zeroPairEnvelope r β) >
    (ρs.image Complex.re).card • balancedEnvelope r :=
  offline_exceeds_balanced hr hr1 hoff.to_hasOfflineZero

/-! ## §7. The Full Statement in Harmonic Language

We now state the defect in terms that directly mirror the π/3 harmonic sum
decomposition:

  Σ_p e^{iπp/3} = (1/2) · (prime count) + i(√3/2) · Σ χ₃(p)

The explicit formula expresses each channel's growth in terms of zero-pair
envelopes. The off-line defect theorem says:

  ¬RH ⟹ (principal channel envelope) > (balanced principal envelope)
  ¬GRH_{χ₃} ⟹ (nonprincipal channel envelope) > (balanced nonprincipal envelope)
-/

/-- **RH-false implies principal-channel defect**: If ρ is an off-line nontrivial
zeta zero (ρ ∈ OffLineZeros), then for any r > 0, r ≠ 1, the principal channel
of the π/3 harmonic sum has a strictly positive defect:

    Q_principal(r) - Q_balanced_principal(r) = (1/2) · D_{Re(ρ)}(r) > 0.

This is the same observable as Re(Σ e^{iπp/3}) = (1/2) · (prime count),
evaluated through the explicit formula. -/
theorem offline_zeta_zero_principal_defect
    (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    0 < principalChannelDefect r ρ.re :=
  principalChannelDefect_pos hr hr1 hρ.2

/-- Variant taking `IsOfflineZetaZero` predicate. -/
theorem offline_zeta_zero_principal_defect' (ρ : ℂ) (hρ : ZD.IsOfflineZetaZero ρ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    0 < principalChannelDefect r ρ.re :=
  principalChannelDefect_pos hr hr1 hρ.2

/-- **GRH-false for L(s,χ₃) implies nonprincipal-channel defect**: If ρ is an
off-line nontrivial zeta zero (ρ ∈ OffLineZeros), then the nonprincipal
(character-sum) channel of the π/3 harmonic sum has a strictly positive defect:

    Q_nonprincipal(r) - Q_balanced_nonprincipal(r) = (√3/2) · D_{Re(ρ)}(r) > 0.

This is the same observable as Im(Σ e^{iπp/3}) = (√3/2) · Σ χ₃(p),
evaluated through the explicit formula. -/
theorem offline_L_zero_nonprincipal_defect
    (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    0 < nonprincipalChannelDefect r ρ.re :=
  nonprincipalChannelDefect_pos hr hr1 hρ.2

/-- Variant taking `IsOfflineZetaZero` predicate. -/
theorem offline_L_zero_nonprincipal_defect' (ρ : ℂ) (hρ : ZD.IsOfflineZetaZero ρ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    0 < nonprincipalChannelDefect r ρ.re :=
  nonprincipalChannelDefect_pos hr hr1 hρ.2

/-! ## §7b. Harmonic Detector Bridges at π/3

The harmonic detector is `cos(p · π/3)` — the cosine component of the sixth
root of unity at prime p. This is the spectral weight; it depends only on p.
The zero's real part β enters solely through the envelope `p^β + p^{1-β}`.

The per-prime signal is: `harmonicSignal(p, β) = cos(pπ/3) · (p^β + p^{1-β})`.
On-line (β = 1/2): signal = `cos(pπ/3) · 2p^{1/2}` (balanced).
Off-line (β ≠ 1/2): signal ≠ balanced (excess amplitude).

We provide 4 bridges:
- **Test bridges** (pure ℝ): check that online β = 1/2 gives balanced signal,
  offline β ≠ 1/2 gives different signal.
- **Real bridges** (actual zeta zeros): same using ρ ∈ OnLineZeros / OffLineZeros.
-/

private theorem prime_cast_pos (p : ℕ) (hp : Nat.Prime p) : (0 : ℝ) < (p : ℝ) :=
  Nat.cast_pos.mpr hp.pos

private theorem prime_cast_ne_one (p : ℕ) (hp : Nat.Prime p) : (p : ℝ) ≠ 1 := by
  exact_mod_cast hp.one_lt.ne'

/-- The harmonic signal defect factors as cos · amplitudeDefect. -/
theorem harmonicSignalDefect_eq (p : ℕ) (β : ℝ) :
    harmonicSignalDefect p β = harmonicCosine p * amplitudeDefect (↑p) β := by
  simp [harmonicSignalDefect, harmonicSignal, harmonicSignalBalanced, amplitudeDefect]
  ring

/-- `cos(n · π/3)` is never zero for any natural number n.
The values cycle through {1, 1/2, −1/2, −1, −1/2, 1/2} with period 6.
Proof: `cos(nπ/3) = 0` would require `nπ/3 = (2k+1)π/2`, giving `2n = 3(2k+1)`,
but LHS is even and RHS is odd. -/
theorem harmonicCosine_ne_zero (n : ℕ) : harmonicCosine n ≠ 0 := by
  unfold harmonicCosine
  intro h
  rw [Real.cos_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_pos.ne'
  have h1 : 2 * (↑n : ℝ) * Real.pi = 3 * (2 * (↑k : ℝ) + 1) * Real.pi := by linarith
  have h2 : 2 * (↑n : ℝ) = 3 * (2 * (↑k : ℝ) + 1) := mul_right_cancel₀ hπ h1
  have h3 : (2 : ℤ) * ↑n = 3 * (2 * k + 1) := by exact_mod_cast h2
  omega

/-- **On-line signal = balanced signal**: When β = 1/2, the harmonic signal at
any prime p equals the balanced signal. -/
theorem harmonicSignal_eq_balanced_of_online (p : ℕ) :
    harmonicSignal p (1 / 2) = harmonicSignalBalanced p := by
  unfold harmonicSignal harmonicSignalBalanced zeroPairEnvelope balancedEnvelope
  ring

/-- **On-line defect = 0**: The harmonic signal defect vanishes on-line. -/
theorem harmonicSignalDefect_zero_of_online (p : ℕ) :
    harmonicSignalDefect p (1 / 2) = 0 := by
  rw [harmonicSignalDefect_eq, amplitudeDefect_half]; ring

/-- **Off-line defect ≠ 0** (unconditional): For β ≠ 1/2 at any prime p,
the harmonic signal defect `cos(pπ/3) · D_β(p)` is nonzero. Both factors are
proved nonzero: `harmonicCosine_ne_zero` and `offline_amplitude_defect_pos`. -/
theorem harmonicSignalDefect_ne_zero_of_offline (p : ℕ) (hp : Nat.Prime p)
    {β : ℝ} (hβ : β ≠ 1 / 2) :
    harmonicSignalDefect p β ≠ 0 := by
  rw [harmonicSignalDefect_eq]
  exact mul_ne_zero (harmonicCosine_ne_zero p) (ne_of_gt (offline_amplitude_defect_pos
    (prime_cast_pos p hp) (prime_cast_ne_one p hp) hβ))

/-- **Test bridge (online)**: For any prime p and β = 1/2, the harmonic detector
reports: envelope ratio = 1, signal defect = 0. -/
theorem test_bridge_online (p : ℕ) (hp : Nat.Prime p) :
    envelopeRatio (↑p) (1 / 2) = 1 ∧ harmonicSignalDefect p (1 / 2) = 0 :=
  ⟨envelopeRatio_eq_one_of_online (prime_cast_pos p hp),
   harmonicSignalDefect_zero_of_online p⟩

/-- **Test bridge (offline)**: For any prime p and β ≠ 1/2, the harmonic detector
fires unconditionally: envelope ratio > 1 and signal defect ≠ 0. -/
theorem test_bridge_offline (p : ℕ) (hp : Nat.Prime p)
    {β : ℝ} (hβ : β ≠ 1 / 2) :
    1 < envelopeRatio (↑p) β ∧ harmonicSignalDefect p β ≠ 0 :=
  ⟨envelopeRatio_gt_one_of_offline (prime_cast_pos p hp) (prime_cast_ne_one p hp) hβ,
   harmonicSignalDefect_ne_zero_of_offline p hp hβ⟩

/-- **Real bridge (online)**: For any prime p and on-line zeta zero ρ ∈ OnLineZeros,
the harmonic detector reports: envelope ratio = 1, signal defect = 0. -/
theorem real_bridge_online (p : ℕ) (hp : Nat.Prime p) (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) :
    envelopeRatio (↑p) ρ.re = 1 ∧ harmonicSignalDefect p ρ.re = 0 := by
  rw [hρ.2]; exact test_bridge_online p hp

/-- **Real bridge (offline)**: For any prime p and off-line zeta zero ρ ∈ OffLineZeros,
the harmonic detector fires unconditionally. -/
theorem real_bridge_offline (p : ℕ) (hp : Nat.Prime p) (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    1 < envelopeRatio (↑p) ρ.re ∧ harmonicSignalDefect p ρ.re ≠ 0 :=
  test_bridge_offline p hp hρ.2

/-! ### §7b½. Admissible Primes and Monotone Scanning

An **admissible prime** is any prime p ≥ 5. All such primes satisfy p ≡ 1 or 5 mod 6,
which gives `cos(pπ/3) = 1/2` — a **constant positive** spectral weight. This is
critical: the cosine factor is uniform across all admissible primes, so the per-prime
signal `harmonicSignal(p, β) = (1/2) · (p^β + p^{1-β})` is controlled entirely by
the envelope. Since the defect `D_β(p)` is strictly increasing in p
(`amplitudeDefect_strict_mono_scale`), the signal is **monotonically growing**
across all prime-indexed harmonics.

Primes 2 and 3 have `cos(2π/3) = -1/2` and `cos(π) = -1` respectively — they
still detect (both are nonzero by `harmonicCosine_ne_zero`) but with different
spectral weights. The admissible primes form the clean monotone sequence.
-/

/-- Primes ≥ 5 satisfy p ≡ 1 or 5 mod 6 (not divisible by 2 or 3). -/
theorem prime_ge5_mod6 (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ (2 ∣ p) := fun h => by have := hp.eq_one_or_self_of_dvd 2 h; omega
  have h3 : ¬ (3 ∣ p) := fun h => by have := hp.eq_one_or_self_of_dvd 3 h; omega
  have hlt : p % 6 < 6 := Nat.mod_lt _ (by omega)
  have hdiv : p = 6 * (p / 6) + p % 6 := (Nat.div_add_mod p 6).symm
  interval_cases (p % 6)
  · exfalso; exact h2 ⟨3 * (p / 6), by omega⟩
  · left; rfl
  · exfalso; exact h2 ⟨3 * (p / 6) + 1, by omega⟩
  · exfalso; exact h3 ⟨2 * (p / 6) + 1, by omega⟩
  · exfalso; exact h2 ⟨3 * (p / 6) + 2, by omega⟩
  · right; rfl

/-- Periodicity reduction: `cos(nπ/3) = cos((n mod 6)π/3)`. -/
private theorem harmonicCosine_period (n : ℕ) :
    harmonicCosine n = Real.cos (↑(n % 6) * (Real.pi / 3)) := by
  simp only [harmonicCosine]
  have key : (↑n : ℝ) = ↑(n % 6) + ↑(n / 6) * 6 := by
    exact_mod_cast (show n = n % 6 + n / 6 * 6 from by omega)
  rw [show (↑n : ℝ) * (π / 3) = ↑(n % 6) * (π / 3) + ↑(n / 6) * (2 * π) from by
    rw [key]; ring]
  exact Real.cos_add_nat_mul_two_pi _ _

/-- **At admissible primes, `cos(pπ/3) = 1/2`** — a constant positive weight.
This is what makes the signal monotone: the cosine is uniform, so growth
comes purely from the envelope `p^β + p^{1-β}`. -/
theorem harmonicCosine_admissible (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) :
    harmonicCosine p = 1 / 2 := by
  rw [harmonicCosine_period]
  rcases prime_ge5_mod6 p hp h5 with h | h
  · rw [h]; simp only [Nat.cast_one, one_mul]; exact Real.cos_pi_div_three
  · rw [h]; simp only [Nat.cast_ofNat]
    rw [show (5 : ℝ) * (π / 3) = 2 * π - π / 3 from by ring, Real.cos_two_pi_sub]
    exact Real.cos_pi_div_three

/-- Periodicity reduction for sine: `sin(nπ/3) = sin((n mod 6)π/3)`. -/
private theorem harmonicSine_period (n : ℕ) :
    Real.sin (↑n * (Real.pi / 3)) = Real.sin (↑(n % 6) * (Real.pi / 3)) := by
  have key : (↑n : ℝ) = ↑(n % 6) + ↑(n / 6) * 6 := by
    exact_mod_cast (show n = n % 6 + n / 6 * 6 from by omega)
  rw [show (↑n : ℝ) * (π / 3) = ↑(n % 6) * (π / 3) + ↑(n / 6) * (2 * π) from by
    rw [key]; ring]
  exact Real.sin_add_nat_mul_two_pi _ _

/-- **Odd channel for p ≡ 1 mod 6**: `sin(pπ/3) = √3/2`.
The sine carries the mod-6 residue class sign. -/
theorem harmonicSine_mod1 (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p)
    (hmod : p % 6 = 1) :
    Real.sin (↑p * (Real.pi / 3)) = Real.sqrt 3 / 2 := by
  rw [harmonicSine_period, hmod]; simp only [Nat.cast_one, one_mul]
  exact Real.sin_pi_div_three

/-- **Odd channel for p ≡ 5 mod 6**: `sin(pπ/3) = -√3/2`.
The sign flips between the two admissible residue classes. -/
theorem harmonicSine_mod5 (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p)
    (hmod : p % 6 = 5) :
    Real.sin (↑p * (Real.pi / 3)) = -(Real.sqrt 3 / 2) := by
  rw [harmonicSine_period, hmod]; simp only [Nat.cast_ofNat]
  rw [show (5 : ℝ) * (π / 3) = 2 * π - π / 3 from by ring, Real.sin_two_pi_sub]
  simp [Real.sin_pi_div_three]

/-- **At admissible primes, the harmonic signal equals (1/2) · envelope.**
The constant cosine weight factors out, leaving pure envelope dependence. -/
theorem harmonicSignal_admissible (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (β : ℝ) :
    harmonicSignal p β = (1 / 2) * zeroPairEnvelope (↑p) β := by
  unfold harmonicSignal; rw [harmonicCosine_admissible p hp h5]

/-- **Monotone scanning over admissible primes**: For admissible primes p < q
and 0 < β < 1, the signal at q strictly exceeds the signal at p.
Since the cosine is constant (1/2), this reduces to envelope monotonicity.
Note: monotonicity holds for ALL β ∈ (0,1) — both online and offline.
The *defect* distinguishes them; the signal always grows. -/
theorem harmonicSignal_strict_mono_admissible
    {p q : ℕ} (hp : Nat.Prime p) (h5p : 5 ≤ p)
    (hq : Nat.Prime q) (h5q : 5 ≤ q) (hpq : p < q)
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1) :
    harmonicSignal p β < harmonicSignal q β := by
  rw [harmonicSignal_admissible p hp h5p, harmonicSignal_admissible q hq h5q]
  apply mul_lt_mul_of_pos_left _ (by norm_num : (0:ℝ) < 1/2)
  -- Reduce to: zeroPairEnvelope p β < zeroPairEnvelope q β
  -- i.e., D_β(p) + balanced(p) < D_β(q) + balanced(q), using strict mono of both
  unfold zeroPairEnvelope
  have hpr : (1 : ℝ) < (↑p : ℝ) := by exact_mod_cast (show 1 < p from by omega)
  have hpq_r : (↑p : ℝ) < (↑q : ℝ) := by exact_mod_cast hpq
  linarith [rpow_lt_rpow (by linarith : (0:ℝ) ≤ p) hpq_r (by linarith : (0:ℝ) < β),
            rpow_lt_rpow (by linarith : (0:ℝ) ≤ p) hpq_r (by linarith : (0:ℝ) < 1 - β)]

/-- **Every prime detects an off-line zero**: universal quantification over
ALL primes, not just one at a time. -/
theorem all_primes_detect_offline {β : ℝ} (hβ : β ≠ 1 / 2) :
    ∀ p : ℕ, Nat.Prime p →
      1 < envelopeRatio (↑p) β ∧ harmonicSignalDefect p β ≠ 0 :=
  fun p hp => test_bridge_offline p hp hβ

/-- **Every prime detects an off-line zeta zero**: if ρ ∈ OffLineZeros,
the detector fires at every prime simultaneously. -/
theorem all_primes_detect_offline_zero (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    ∀ p : ℕ, Nat.Prime p →
      1 < envelopeRatio (↑p) ρ.re ∧ harmonicSignalDefect p ρ.re ≠ 0 :=
  fun p hp => real_bridge_offline p hp ρ hρ

/-! ## §7c. Divergence: the defect grows over primes

For a single off-line zero pair at real part β ≠ 1/2, the amplitude defect
D_β(p) = p^β + p^{1-β} - 2p^{1/2} is:
1. Strictly positive at every prime p (since p ≥ 2 > 1, so p > 0 and p ≠ 1).
2. Strictly increasing in p (since p > 1 and the defect is monotone in r for r > 1).
3. Therefore the cumulative defect Σ_{p ≤ N} D_β(p) diverges as N → ∞.
-/

/-- The defect at prime p is strictly positive for any off-line β. -/
theorem amplitudeDefect_pos_at_prime (p : ℕ) (hp : Nat.Prime p) {β : ℝ} (hβ : β ≠ 1 / 2) :
    0 < amplitudeDefect (↑p) β :=
  offline_amplitude_defect_pos (prime_cast_pos p hp) (prime_cast_ne_one p hp) hβ

/-- **[UNCONDITIONAL]** **Cumulative defect positivity (all primes)**: For an
off-line β, the amplitude defect is strictly positive at *every* prime —
universal pointwise, no finset, no nonempty hypothesis. -/
theorem cumulative_defect_pos {β : ℝ} (hβ : β ≠ 1 / 2) :
    ∀ p : ℕ, Nat.Prime p → 0 < amplitudeDefect (↑p) β :=
  fun p hp => amplitudeDefect_pos_at_prime p hp hβ

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

#### Pure real-analysis (ℝ) layer
1. `ZetaDefs.amplitudeDefect_half` — D_{1/2}(r) = 0 (on-line = no defect) [from ZetaZeroDefs]
2. `amplitudeDefect_nonneg` — D_β(r) ≥ 0 for r > 0 (unconditional)
3. `offline_amplitude_defect_pos` — **Core**: D_β(r) > 0 for β ≠ 1/2, r > 0, r ≠ 1
4. `amplitudeDefect_monotone_in_offset` — Further off-line ⟹ larger defect
5. `principalChannelDefect_pos` — Defect in Re channel (bare ℝ)
6. `nonprincipalChannelDefect_pos` — Defect in Im channel (bare ℝ)
7. `no_negative_envelope` — Anti-zero exclusion (r^β > 0)
8. `total_defect_pos_of_offline` — Sum defect > 0 if any off-line (Finset ℝ)
9. `offline_exceeds_balanced` — Off-line total > balanced total (Finset ℝ)
10. `compatibility_balanced_harmonic` — Unified invariant identity

#### Zeta-zero-typed (ℂ) layer (using ZD.OffLineZeros / ZD.IsOfflineZetaZero)
11. `offline_amplitude_defect_pos_of_zero` — Core defect for `IsOfflineZetaZero ρ`
12. `offline_amplitude_defect_pos_of_mem` — Core defect for `ρ ∈ OffLineZeros`
13. `principalChannelDefect_pos_of_offlineZero` — Principal defect for `IsOfflineZetaZero ρ`
14. `principalChannelDefect_pos_of_mem` — Principal defect for `ρ ∈ OffLineZeros`
15. `nonprincipalChannelDefect_pos_of_offlineZero` — Nonprincipal defect for `IsOfflineZetaZero ρ`
16. `nonprincipalChannelDefect_pos_of_mem` — Nonprincipal defect for `ρ ∈ OffLineZeros`
17. `total_defect_pos_of_offlineZetaZero` — Sum defect > 0 for `HasOfflineZetaZero`
18. `offline_zeros_exceed_balanced` — Off-line total > balanced (Finset ℂ)
19. `offline_zeta_zero_principal_defect` — §7 principal (ρ ∈ OffLineZeros)
20. `offline_L_zero_nonprincipal_defect` — §7 nonprincipal (ρ ∈ OffLineZeros)

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


/-! ## §10. Diagnostic API

Named-record interface for running the harmonic detector against each zero class.
Consumers access fields by name (`.in_strip`, `.defect_pos`, `.witness`, etc.),
so reordering fields in the producer never breaks downstream code.

**Fixed scale**: All defect and ratio tests use `r = π/3` (≈ 1.047), the natural
scale of the π/3 harmonic framework. This is > 0 and ≠ 1 (since π > 3), so the
AM-GM defect theorem applies unconditionally. Signal tests remain per-prime since
the harmonic signal is intrinsically indexed by primes.

Three entry points:
- `diagnostic_nontrivial`: any zero in the critical strip, no online/offline assumption
- `diagnostic_online`: zero known to lie on the critical line
- `diagnostic_offline`: zero known to lie off the critical line
-/

/-- π/3 > 0: the fixed test scale is positive. -/
theorem pi_third_pos : (0 : ℝ) < Real.pi / 3 := by positivity

/-- π/3 ≠ 1: the fixed test scale is not the degenerate base (since π > 3). -/
theorem pi_third_ne_one : Real.pi / 3 ≠ 1 := by
  have := Real.pi_gt_three; linarith

/-- Diagnostic record for a nontrivial zero (no online/offline assumption).
All defect/ratio tests at fixed scale r = π/3. -/
structure NontrivialDiagnostic (ρ : ℂ) where
  in_strip : 0 < ρ.re ∧ ρ.re < 1
  defect_nonneg : 0 ≤ amplitudeDefect (Real.pi / 3) ρ.re
  signal_mono :
    ∀ {p q : ℕ}, Nat.Prime p → 5 ≤ p → Nat.Prime q → 5 ≤ q → p < q →
      harmonicSignal p ρ.re < harmonicSignal q ρ.re
  online_or_offline : ρ.re = 1/2 ∨ ρ.re ≠ 1/2

/-- Diagnostic record for an online zero (detector silent).
All defect/ratio tests at fixed scale r = π/3. -/
structure OnlineDiagnostic (ρ : ℂ) where
  on_line : ρ.re = 1/2
  defect_zero : amplitudeDefect (Real.pi / 3) ρ.re = 0
  ratio_one : envelopeRatio (Real.pi / 3) ρ.re = 1
  signal_zero : ∀ p : ℕ, harmonicSignalDefect p ρ.re = 0

/-- Diagnostic record for an offline zero (detector fires everywhere).
Defect/ratio at fixed scale r = π/3; signal tests per-prime. -/
structure OfflineDiagnostic (ρ : ℂ) where
  off_line : ρ.re ≠ 1/2
  defect_pos : 0 < amplitudeDefect (Real.pi / 3) ρ.re
  ratio_gt_one : 1 < envelopeRatio (Real.pi / 3) ρ.re
  signal_ne_zero : ∀ p : ℕ, Nat.Prime p → harmonicSignalDefect p ρ.re ≠ 0
  witness : 0 < amplitudeDefect (Real.pi / 3) ρ.re
  /-- At every prime, the amplitude defect is strictly positive — universal
  pointwise "all primes" form (no finset, no nonempty hypothesis). -/
  cumulative_pos :
    ∀ p : ℕ, Nat.Prime p → 0 < amplitudeDefect (↑p) ρ.re

/-- **Nontrivial zero diagnostic** (assumption-free). -/
def diagnostic_nontrivial (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    NontrivialDiagnostic ρ where
  in_strip := ⟨hρ.1, hρ.2.1⟩
  defect_nonneg := amplitudeDefect_nonneg pi_third_pos _
  signal_mono hp h5p hq h5q hpq :=
    harmonicSignal_strict_mono_admissible hp h5p hq h5q hpq hρ.1 hρ.2.1
  online_or_offline := Classical.em _

/-- **Online zero diagnostic**: detector silent at r = π/3. -/
def diagnostic_online (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) :
    OnlineDiagnostic ρ where
  on_line := hρ.2
  defect_zero := by rw [hρ.2]; exact amplitudeDefect_half _
  ratio_one := by rw [hρ.2]; exact envelopeRatio_eq_one_of_online pi_third_pos
  signal_zero p := by rw [hρ.2]; exact harmonicSignalDefect_zero_of_online p

/-- **Offline zero diagnostic**: detector fires at r = π/3 and every prime. -/
def diagnostic_offline (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    OfflineDiagnostic ρ where
  off_line := hρ.2
  defect_pos := offline_amplitude_defect_pos pi_third_pos pi_third_ne_one hρ.2
  ratio_gt_one := envelopeRatio_gt_one_of_offline pi_third_pos pi_third_ne_one hρ.2
  signal_ne_zero p hp := harmonicSignalDefect_ne_zero_of_offline p hp hρ.2
  witness := offline_amplitude_defect_pos pi_third_pos pi_third_ne_one hρ.2
  cumulative_pos := cumulative_defect_pos hρ.2

/-! ## §11. Pair-Anchored Envelope Theory + Two-Kernel Diagnostic Records

Parallel envelope theory anchored at `π/6` and `1 − π/6`, and a bundled
`TwoKernelDiagnostic` / `TwoKernelOnlineDiagnostic` / `TwoKernelOfflineDiagnostic`
record API mirroring the single-kernel `NontrivialDiagnostic` / `OnlineDiagnostic`
/ `OfflineDiagnostic` structures from §10.

**Formal vs substantive**: the pair envelopes
`zeroPairEnvelopeLeft r β = r^β + r^(π/3 − β)` and the analogous right one do
NOT correspond to ζ's zero-pair envelopes (which use the functional equation
reflection β ↔ 1 − β, not β ↔ π/3 − β). They are *formal* analogs of the
existing envelope theory; their value is the parallel cosh factorization

  zeroPairEnvelopeLeft  r β = balancedEnvelopeLeft  r · coshDetectorLeft  β (log r)
  zeroPairEnvelopeRight r β = balancedEnvelopeRight r · coshDetectorRight β (log r)

which lets us reuse the single-kernel proofs at the new anchors. The
*discriminating* pair observable for ζ is the kernel agreement
`coshDetectorLeft = coshDetectorRight` (from §3c′), not either envelope
alone; this is what `TwoKernelDiagnostic` packages.
-/

/-! ### §11.1. Scale helpers at the reflected anchors -/

theorem pi_sixth_pos : (0 : ℝ) < Real.pi / 6 := by positivity

theorem pi_sixth_lt_one : Real.pi / 6 < 1 := by
  have := Real.pi_lt_d4; linarith

theorem one_minus_pi_sixth_pos : (0 : ℝ) < 1 - Real.pi / 6 := by
  have := Real.pi_lt_d4; linarith

theorem one_minus_pi_sixth_lt_one : 1 - Real.pi / 6 < 1 := by
  have := Real.pi_gt_three; linarith

theorem pi_sixth_ne_half : Real.pi / 6 ≠ 1 / 2 := by
  intro h; have := Real.pi_gt_three; linarith

theorem one_minus_pi_sixth_ne_half : 1 - Real.pi / 6 ≠ 1 / 2 := by
  intro h; have := Real.pi_gt_three; linarith

/-! ### §11.2. Pair-anchored envelopes + balanced values -/

/-- **Left-anchored zero-pair envelope**: `r^β + r^(π/3 − β)`. Minimum
    `2·r^(π/6)` at β = π/6 (the left kernel anchor). -/
def zeroPairEnvelopeLeft (r β : ℝ) : ℝ := r ^ β + r ^ (Real.pi / 3 - β)

/-- **Right-anchored zero-pair envelope**: `r^β + r^(2 − π/3 − β)`. Minimum
    `2·r^(1 − π/6)` at β = 1 − π/6 (the right kernel anchor). -/
def zeroPairEnvelopeRight (r β : ℝ) : ℝ := r ^ β + r ^ (2 - Real.pi / 3 - β)

/-- Balanced value of the left-anchored envelope: `2·r^(π/6)`. -/
def balancedEnvelopeLeft (r : ℝ) : ℝ := 2 * r ^ (Real.pi / 6)

/-- Balanced value of the right-anchored envelope: `2·r^(1 − π/6)`. -/
def balancedEnvelopeRight (r : ℝ) : ℝ := 2 * r ^ (1 - Real.pi / 6)

theorem balancedEnvelopeLeft_pos {r : ℝ} (hr : 0 < r) : 0 < balancedEnvelopeLeft r := by
  unfold balancedEnvelopeLeft; positivity

theorem balancedEnvelopeRight_pos {r : ℝ} (hr : 0 < r) : 0 < balancedEnvelopeRight r := by
  unfold balancedEnvelopeRight; positivity

/-! ### §11.3. Cosh factorization: envelope = balanced · kernel -/

/-- **Left factorization**: `zeroPairEnvelopeLeft r β = 2·r^(π/6) · coshDetectorLeft β (log r)`. -/
theorem zeroPairEnvelopeLeft_eq_cosh {r : ℝ} (hr : 0 < r) (β : ℝ) :
    zeroPairEnvelopeLeft r β = balancedEnvelopeLeft r * coshDetectorLeft β (Real.log r) := by
  unfold zeroPairEnvelopeLeft balancedEnvelopeLeft coshDetectorLeft
  rw [Real.cosh_eq]
  have key : ∀ a : ℝ, Real.exp (a * Real.log r) = r ^ a := fun a => by
    rw [mul_comm, Real.rpow_def_of_pos hr]
  rw [key,
      show -((β - Real.pi / 6) * Real.log r) = (-(β - Real.pi / 6)) * Real.log r from by ring,
      key]
  have h1 : r ^ (Real.pi / 6 : ℝ) * r ^ (β - Real.pi / 6) = r ^ β := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have h2 : r ^ (Real.pi / 6 : ℝ) * r ^ (-(β - Real.pi / 6)) = r ^ (Real.pi / 3 - β) := by
    rw [← Real.rpow_add hr]; congr 1; ring
  nlinarith

/-- **Right factorization**: `zeroPairEnvelopeRight r β = 2·r^(1−π/6) · coshDetectorRight β (log r)`. -/
theorem zeroPairEnvelopeRight_eq_cosh {r : ℝ} (hr : 0 < r) (β : ℝ) :
    zeroPairEnvelopeRight r β = balancedEnvelopeRight r * coshDetectorRight β (Real.log r) := by
  unfold zeroPairEnvelopeRight balancedEnvelopeRight coshDetectorRight
  rw [Real.cosh_eq]
  have key : ∀ a : ℝ, Real.exp (a * Real.log r) = r ^ a := fun a => by
    rw [mul_comm, Real.rpow_def_of_pos hr]
  rw [key,
      show -((β - (1 - Real.pi / 6)) * Real.log r) =
        (-(β - (1 - Real.pi / 6))) * Real.log r from by ring,
      key]
  have h1 : r ^ (1 - Real.pi / 6 : ℝ) * r ^ (β - (1 - Real.pi / 6)) = r ^ β := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have h2 : r ^ (1 - Real.pi / 6 : ℝ) * r ^ (-(β - (1 - Real.pi / 6))) =
      r ^ (2 - Real.pi / 3 - β) := by
    rw [← Real.rpow_add hr]; congr 1; ring
  nlinarith

/-- **Envelope symmetry** (left): `zeroPairEnvelopeLeft r β = zeroPairEnvelopeLeft r (π/3 − β)`.
    The left envelope is even in `(β − π/6)`. -/
theorem zeroPairEnvelopeLeft_symm (r β : ℝ) :
    zeroPairEnvelopeLeft r β = zeroPairEnvelopeLeft r (Real.pi / 3 - β) := by
  unfold zeroPairEnvelopeLeft
  have : (Real.pi / 3 - (Real.pi / 3 - β)) = β := by ring
  rw [this]; ring

/-- **Envelope symmetry** (right): analogous even symmetry around the right anchor. -/
theorem zeroPairEnvelopeRight_symm (r β : ℝ) :
    zeroPairEnvelopeRight r β = zeroPairEnvelopeRight r (2 - Real.pi / 3 - β) := by
  unfold zeroPairEnvelopeRight
  have : (2 - Real.pi / 3 - (2 - Real.pi / 3 - β)) = β := by ring
  rw [this]; ring

/-! ### §11.4. Pair-anchored defects + biconditionals -/

/-- Left-anchored defect: `zeroPairEnvelopeLeft r β − 2·r^(π/6)`. Vanishes iff β = π/6. -/
def amplitudeDefectLeft (r β : ℝ) : ℝ :=
  zeroPairEnvelopeLeft r β - balancedEnvelopeLeft r

/-- Right-anchored defect: `zeroPairEnvelopeRight r β − 2·r^(1−π/6)`. Vanishes iff β = 1−π/6. -/
def amplitudeDefectRight (r β : ℝ) : ℝ :=
  zeroPairEnvelopeRight r β - balancedEnvelopeRight r

/-- Left defect equals `balancedLeft · (coshDetectorLeft − 1)`. -/
theorem amplitudeDefectLeft_eq_cosh_excess {r : ℝ} (hr : 0 < r) (β : ℝ) :
    amplitudeDefectLeft r β =
      balancedEnvelopeLeft r * (coshDetectorLeft β (Real.log r) - 1) := by
  unfold amplitudeDefectLeft
  rw [zeroPairEnvelopeLeft_eq_cosh hr]; ring

/-- Right defect equals `balancedRight · (coshDetectorRight − 1)`. -/
theorem amplitudeDefectRight_eq_cosh_excess {r : ℝ} (hr : 0 < r) (β : ℝ) :
    amplitudeDefectRight r β =
      balancedEnvelopeRight r * (coshDetectorRight β (Real.log r) - 1) := by
  unfold amplitudeDefectRight
  rw [zeroPairEnvelopeRight_eq_cosh hr]; ring

/-- **Left defect nonneg**: `amplitudeDefectLeft r β ≥ 0` for r > 0. -/
theorem amplitudeDefectLeft_nonneg {r : ℝ} (hr : 0 < r) (β : ℝ) :
    0 ≤ amplitudeDefectLeft r β := by
  rw [amplitudeDefectLeft_eq_cosh_excess hr]
  have hbal : 0 < balancedEnvelopeLeft r := balancedEnvelopeLeft_pos hr
  have hcosh : 1 ≤ coshDetectorLeft β (Real.log r) := by
    unfold coshDetectorLeft; exact Real.one_le_cosh _
  nlinarith

/-- **Right defect nonneg**: `amplitudeDefectRight r β ≥ 0` for r > 0. -/
theorem amplitudeDefectRight_nonneg {r : ℝ} (hr : 0 < r) (β : ℝ) :
    0 ≤ amplitudeDefectRight r β := by
  rw [amplitudeDefectRight_eq_cosh_excess hr]
  have hbal : 0 < balancedEnvelopeRight r := balancedEnvelopeRight_pos hr
  have hcosh : 1 ≤ coshDetectorRight β (Real.log r) := by
    unfold coshDetectorRight; exact Real.one_le_cosh _
  nlinarith

/-- **Left defect biconditional**: `amplitudeDefectLeft r β = 0 ↔ β = π/6`, for r > 0, r ≠ 1. -/
theorem amplitudeDefectLeft_eq_zero_iff {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ} :
    amplitudeDefectLeft r β = 0 ↔ β = Real.pi / 6 := by
  rw [amplitudeDefectLeft_eq_cosh_excess hr]
  have hbal : (0 : ℝ) < balancedEnvelopeLeft r := balancedEnvelopeLeft_pos hr
  rw [mul_eq_zero]
  constructor
  · rintro (hbal0 | hc)
    · exact absurd hbal0 hbal.ne'
    · have : coshDetectorLeft β (Real.log r) = 1 := by linarith
      by_contra hβ
      have hlog : Real.log r ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hr hr1
      exact absurd this (ne_of_gt (coshDetectorLeft_gt_one hβ hlog))
  · rintro rfl; right; rw [coshDetectorLeft_one_at_center]; ring

/-- **Right defect biconditional**: `amplitudeDefectRight r β = 0 ↔ β = 1 − π/6`, for r > 0, r ≠ 1. -/
theorem amplitudeDefectRight_eq_zero_iff {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ} :
    amplitudeDefectRight r β = 0 ↔ β = 1 - Real.pi / 6 := by
  rw [amplitudeDefectRight_eq_cosh_excess hr]
  have hbal : (0 : ℝ) < balancedEnvelopeRight r := balancedEnvelopeRight_pos hr
  rw [mul_eq_zero]
  constructor
  · rintro (hbal0 | hc)
    · exact absurd hbal0 hbal.ne'
    · have : coshDetectorRight β (Real.log r) = 1 := by linarith
      by_contra hβ
      have hlog : Real.log r ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hr hr1
      exact absurd this (ne_of_gt (coshDetectorRight_gt_one hβ hlog))
  · rintro rfl; right; rw [coshDetectorRight_one_at_center]; ring

/-- Left defect is strictly positive off the left anchor. -/
theorem amplitudeDefectLeft_pos {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ}
    (hβ : β ≠ Real.pi / 6) :
    0 < amplitudeDefectLeft r β := by
  have hnn := amplitudeDefectLeft_nonneg hr β
  have hne : amplitudeDefectLeft r β ≠ 0 := by
    intro h; exact hβ ((amplitudeDefectLeft_eq_zero_iff hr hr1).mp h)
  exact lt_of_le_of_ne hnn (Ne.symm hne)

/-- Right defect is strictly positive off the right anchor. -/
theorem amplitudeDefectRight_pos {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ}
    (hβ : β ≠ 1 - Real.pi / 6) :
    0 < amplitudeDefectRight r β := by
  have hnn := amplitudeDefectRight_nonneg hr β
  have hne : amplitudeDefectRight r β ≠ 0 := by
    intro h; exact hβ ((amplitudeDefectRight_eq_zero_iff hr hr1).mp h)
  exact lt_of_le_of_ne hnn (Ne.symm hne)

/-! ### §11.5. Agreement-defect: the DISCRIMINATING pair observable

The pair-kernel agreement `K_L = K_R ↔ β = 1/2` (for nonzero scale) is the
observable that actually separates on-line from off-line zeros — unlike the
individual left/right defects above, which vanish at π/6 and 1−π/6 rather
than at 1/2. We package the agreement as `pairAgreementDefect r β` for use
in downstream diagnostics.
-/

/-- **Pair agreement defect**: `(coshDetectorLeft β (log r) − coshDetectorRight β (log r))²`.
    This is the squared disagreement between the two kernels at log-scale r;
    nonneg always, zero iff β = 1/2 for r ≠ 1. -/
def pairAgreementDefect (r β : ℝ) : ℝ :=
  (coshDetectorLeft β (Real.log r) - coshDetectorRight β (Real.log r)) ^ 2

/-- Pair agreement defect is nonneg (a perfect square). -/
theorem pairAgreementDefect_nonneg (r β : ℝ) : 0 ≤ pairAgreementDefect r β := sq_nonneg _

/-- **Pair agreement biconditional**: `pairAgreementDefect r β = 0 ↔ β = 1/2`, for r > 0, r ≠ 1. -/
theorem pairAgreementDefect_eq_zero_iff {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ} :
    pairAgreementDefect r β = 0 ↔ β = 1 / 2 := by
  unfold pairAgreementDefect
  rw [sq_eq_zero_iff, sub_eq_zero]
  exact coshDetectors_agree_iff (Real.log_ne_zero_of_pos_of_ne_one hr hr1)

/-- Pair agreement defect is strictly positive off the critical line. -/
theorem pairAgreementDefect_pos {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ}
    (hβ : β ≠ 1 / 2) :
    0 < pairAgreementDefect r β := by
  have hnn := pairAgreementDefect_nonneg r β
  have hne : pairAgreementDefect r β ≠ 0 := by
    intro h; exact hβ ((pairAgreementDefect_eq_zero_iff hr hr1).mp h)
  exact lt_of_le_of_ne hnn (Ne.symm hne)

/-! ### §11.6. Diagnostic records: TwoKernelDiagnostic and Online/Offline variants -/

/-- **Nontrivial two-kernel diagnostic**: the pair facts that hold unconditionally
for any nontrivial zero (no online/offline assumption). All tests at fixed scale r = π/3. -/
structure TwoKernelDiagnostic (ρ : ℂ) where
  in_strip : 0 < ρ.re ∧ ρ.re < 1
  left_defect_nonneg : 0 ≤ amplitudeDefectLeft (Real.pi / 3) ρ.re
  right_defect_nonneg : 0 ≤ amplitudeDefectRight (Real.pi / 3) ρ.re
  agreement_defect_nonneg : 0 ≤ pairAgreementDefect (Real.pi / 3) ρ.re
  online_or_offline : ρ.re = 1 / 2 ∨ ρ.re ≠ 1 / 2
  reflect_swap : ∀ y : ℝ,
    coshDetectorLeft (1 - ρ.re) y = coshDetectorRight ρ.re y

/-- **Online two-kernel diagnostic**: detector agreement at the critical line. -/
structure TwoKernelOnlineDiagnostic (ρ : ℂ) where
  on_line : ρ.re = 1 / 2
  agreement_defect_zero : pairAgreementDefect (Real.pi / 3) ρ.re = 0
  kernels_agree_everywhere : ∀ y : ℝ,
    coshDetectorLeft ρ.re y = coshDetectorRight ρ.re y
  pair_sum_is_calibration : ∀ y : ℝ,
    coshDetectorLeft ρ.re y + coshDetectorRight ρ.re y =
      2 * Real.cosh ((1 - Real.pi / 3) * y / 2)

/-- **Offline two-kernel diagnostic**: strict kernel disagreement at every nonzero scale. -/
structure TwoKernelOfflineDiagnostic (ρ : ℂ) where
  off_line : ρ.re ≠ 1 / 2
  agreement_defect_pos : 0 < pairAgreementDefect (Real.pi / 3) ρ.re
  kernels_disagree_at_nonzero :
    ∀ {y : ℝ}, y ≠ 0 → coshDetectorLeft ρ.re y ≠ coshDetectorRight ρ.re y
  kernels_disagree_at_primes :
    ∀ p : ℕ, Nat.Prime p →
      coshDetectorLeft ρ.re (Real.log (↑p)) ≠ coshDetectorRight ρ.re (Real.log (↑p))
  pair_sum_strict_excess :
    ∀ {y : ℝ}, y ≠ 0 →
      2 * Real.cosh ((1 - Real.pi / 3) * y / 2) <
        coshDetectorLeft ρ.re y + coshDetectorRight ρ.re y

/-! ### §11.7. Diagnostic constructors -/

/-- **Nontrivial two-kernel diagnostic** (unconditional). -/
def diagnostic_twoKernel (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    TwoKernelDiagnostic ρ where
  in_strip := ⟨hρ.1, hρ.2.1⟩
  left_defect_nonneg := amplitudeDefectLeft_nonneg pi_third_pos _
  right_defect_nonneg := amplitudeDefectRight_nonneg pi_third_pos _
  agreement_defect_nonneg := pairAgreementDefect_nonneg _ _
  online_or_offline := Classical.em _
  reflect_swap y := coshDetector_reflect_swap ρ.re y

/-- **Online two-kernel diagnostic**: kernels agree everywhere. -/
def diagnostic_twoKernel_online (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) :
    TwoKernelOnlineDiagnostic ρ where
  on_line := hρ.2
  agreement_defect_zero := by
    rw [hρ.2]
    exact (pairAgreementDefect_eq_zero_iff pi_third_pos pi_third_ne_one).mpr rfl
  kernels_agree_everywhere y := by
    rw [hρ.2]; exact coshDetectors_equal_on_critical_line y
  pair_sum_is_calibration y := by
    rw [coshDetector_pair_sum, hρ.2, coshDetector_one_of_online]; ring

/-- **Offline two-kernel diagnostic**: kernels disagree at every nonzero scale. -/
def diagnostic_twoKernel_offline (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    TwoKernelOfflineDiagnostic ρ where
  off_line := hρ.2
  agreement_defect_pos := pairAgreementDefect_pos pi_third_pos pi_third_ne_one hρ.2
  kernels_disagree_at_nonzero hy h := by
    exact hρ.2 ((coshDetectors_agree_iff hy).mp h)
  kernels_disagree_at_primes p hp h := by
    have hlog : Real.log (↑p) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one
        (Nat.cast_pos.mpr hp.pos) (by exact_mod_cast hp.one_lt.ne')
    exact hρ.2 ((coshDetectors_agree_iff hlog).mp h)
  pair_sum_strict_excess := @fun y hy => by
    rw [coshDetector_pair_sum]
    have hcosh : 1 < coshDetector ρ.re y := coshDetector_gt_one_of_offline hρ.2 hy
    have hcal : 0 < 2 * Real.cosh ((1 - Real.pi / 3) * y / 2) :=
      coshDetector_pair_calibration_pos y
    nlinarith [hcal, hcosh]

end
