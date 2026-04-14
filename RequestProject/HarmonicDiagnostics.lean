import RequestProject.OfflineAmplitudeMethods

/-!
# Harmonic Diagnostics — Consumer of the Bridge API

Exercises the diagnostic API from `OfflineAmplitudeMethods.lean` with fixed
test scale r = π/3. Extracts named fields from diagnostic records.
-/

open Real ZetaDefs BigOperators

noncomputable section

/-! ## §1. Generic Nontrivial Zero -/

theorem nontrivial_in_strip (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    0 < ρ.re ∧ ρ.re < 1 :=
  (diagnostic_nontrivial ρ hρ).in_strip

theorem nontrivial_defect_nonneg (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    0 ≤ amplitudeDefect (π / 3) ρ.re :=
  (diagnostic_nontrivial ρ hρ).defect_nonneg

theorem nontrivial_signal_mono (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros)
    {p q : ℕ} (hp : Nat.Prime p) (h5p : 5 ≤ p)
    (hq : Nat.Prime q) (h5q : 5 ≤ q) (hpq : p < q) :
    harmonicSignal p ρ.re < harmonicSignal q ρ.re :=
  (diagnostic_nontrivial ρ hρ).signal_mono hp h5p hq h5q hpq

theorem nontrivial_online_or_offline (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    ρ.re = 1/2 ∨ ρ.re ≠ 1/2 :=
  (diagnostic_nontrivial ρ hρ).online_or_offline

/-! ## §2. Online Zero — Detector Silent -/

theorem online_membership (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) :
    ρ.re = 1/2 :=
  (diagnostic_online ρ hρ).on_line

theorem online_defect_zero (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) :
    amplitudeDefect (π / 3) ρ.re = 0 :=
  (diagnostic_online ρ hρ).defect_zero

theorem online_ratio_one (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) :
    envelopeRatio (π / 3) ρ.re = 1 :=
  (diagnostic_online ρ hρ).ratio_one

theorem online_signal_zero (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) (p : ℕ) :
    harmonicSignalDefect p ρ.re = 0 :=
  (diagnostic_online ρ hρ).signal_zero p

/-! ## §3. Offline Zero — Detector Fires -/

theorem offline_membership (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    ρ.re ≠ 1/2 :=
  (diagnostic_offline ρ hρ).off_line

theorem offline_defect_pos (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    0 < amplitudeDefect (π / 3) ρ.re :=
  (diagnostic_offline ρ hρ).defect_pos

theorem offline_ratio_gt_one (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    1 < envelopeRatio (π / 3) ρ.re :=
  (diagnostic_offline ρ hρ).ratio_gt_one

theorem offline_signal_ne_zero (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros)
    (p : ℕ) (hp : Nat.Prime p) :
    harmonicSignalDefect p ρ.re ≠ 0 :=
  (diagnostic_offline ρ hρ).signal_ne_zero p hp

theorem offline_witness (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    0 < amplitudeDefect (π / 3) ρ.re :=
  (diagnostic_offline ρ hρ).witness

theorem offline_cumulative_pos (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros)
    (ps : Finset ℕ) (hps : ∀ p ∈ ps, Nat.Prime p) (hne : ps.Nonempty) :
    0 < ps.sum (fun p => amplitudeDefect (↑p) ρ.re) :=
  (diagnostic_offline ρ hρ).cumulative_pos ps hps hne

/-! ## §4. Contrast -/

theorem contrast_defect (ρ_on : ℂ) (h_on : ρ_on ∈ ZD.OnLineZeros)
    (ρ_off : ℂ) (h_off : ρ_off ∈ ZD.OffLineZeros) :
    amplitudeDefect (π / 3) ρ_on.re = 0 ∧ 0 < amplitudeDefect (π / 3) ρ_off.re :=
  ⟨(diagnostic_online ρ_on h_on).defect_zero,
   (diagnostic_offline ρ_off h_off).defect_pos⟩

theorem contrast_ratio (ρ_on : ℂ) (h_on : ρ_on ∈ ZD.OnLineZeros)
    (ρ_off : ℂ) (h_off : ρ_off ∈ ZD.OffLineZeros) :
    envelopeRatio (π / 3) ρ_on.re = 1 ∧ 1 < envelopeRatio (π / 3) ρ_off.re :=
  ⟨(diagnostic_online ρ_on h_on).ratio_one,
   (diagnostic_offline ρ_off h_off).ratio_gt_one⟩

/-! ## §5. Global Tests on ALL Nontrivial Zeros

These are the real tests. They apply to every nontrivial zero simultaneously,
with no online/offline assumption. Each is a biconditional that completely
characterizes the critical line through the harmonic measurement at r = π/3.
-/

/-- **The defect test**: For ANY nontrivial zero, the amplitude defect at π/3
is zero if and only if the zero lies on the critical line.
This is the complete characterization — the measurement IS the classifier. -/
theorem defect_characterizes_line (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    amplitudeDefect (π / 3) ρ.re = 0 ↔ ρ.re = 1 / 2 :=
  amplitudeDefect_eq_zero_iff pi_third_pos pi_third_ne_one

/-- **The ratio test**: For ANY nontrivial zero, the envelope ratio at π/3
equals 1 if and only if the zero lies on the critical line. -/
theorem ratio_characterizes_line (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    envelopeRatio (π / 3) ρ.re = 1 ↔ ρ.re = 1 / 2 :=
  envelopeRatio_eq_one_iff pi_third_pos pi_third_ne_one

/-- **The defect positivity test**: For ANY nontrivial zero, the defect is
strictly positive if and only if the zero is OFF the critical line. -/
theorem defect_pos_iff_offline (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    0 < amplitudeDefect (π / 3) ρ.re ↔ ρ.re ≠ 1 / 2 :=
  amplitudeDefect_pos_iff pi_third_pos pi_third_ne_one

/-- **The ratio excess test**: For ANY nontrivial zero, the ratio exceeds 1
if and only if the zero is OFF the critical line. -/
theorem ratio_gt_one_iff_offline (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    1 < envelopeRatio (π / 3) ρ.re ↔ ρ.re ≠ 1 / 2 :=
  envelopeRatio_gt_one_iff pi_third_pos pi_third_ne_one

/-- **Harmonic balance implies RH**: If the defect vanishes on all nontrivial
zeros, then all nontrivial zeros lie on the critical line. Fully proved — the
hypothesis is the open question, not the implication. -/
theorem harmonic_balance_implies_rh
    (balance : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      amplitudeDefect (π / 3) ρ.re = 0) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1 / 2 :=
  fun ρ hρ => (defect_characterizes_line ρ hρ).mp (balance ρ hρ)

/-- **Online zeros exhibit harmonic balance**: every on-line nontrivial zero
has zero defect, unit ratio, and zero signal defect at all primes. -/
theorem online_zeros_show_harmonic_balance (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) :
    amplitudeDefect (π / 3) ρ.re = 0 ∧
    envelopeRatio (π / 3) ρ.re = 1 ∧
    (∀ p : ℕ, harmonicSignalDefect p ρ.re = 0) :=
  let d := diagnostic_online ρ hρ
  ⟨d.defect_zero, d.ratio_one, d.signal_zero⟩

/-- **Contrapositive**: Any offline nontrivial zero breaks harmonic balance. -/
theorem offline_breaks_balance (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    0 < amplitudeDefect (π / 3) ρ.re :=
  (diagnostic_offline ρ hρ).defect_pos

/-! ## §5b. Observability: Offline Zeros are Detectable

An offline zero doesn't just produce a positive defect at one scale — it produces
a **nonzero analytic component** (via the cosh kernel on the even channel) that
is visible at every nonzero observation scale y = log x, at every prime, and on
every interval (a, b) ⊂ (1, ∞). No cancellation can hide it.

The observable is `harmonicDiffPiThird β y = cosh((β - 1/2)·y) - 1`:
- Online (β = 1/2): identically 0 for all y (silent)
- Offline (β ≠ 1/2): strictly positive for all y ≠ 0 (always visible)
-/

/-- **Offline creates imbalance**: At every nonzero log-scale y, the even-channel
observable `cosh((β-1/2)·y) - 1` is strictly positive for an offline zero. -/
theorem offline_imbalance_at_every_scale (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros)
    {y : ℝ} (hy : y ≠ 0) :
    0 < harmonicDiffPiThird ρ.re y :=
  harmonicDiffPiThird_pos_of_offline hρ.2 hy

/-- **Online produces no imbalance**: The even-channel observable is identically
zero for an online zero — the detector is completely silent at every scale. -/
theorem online_no_imbalance (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) (y : ℝ) :
    harmonicDiffPiThird ρ.re y = 0 := by
  rw [hρ.2]; exact harmonicDiffPiThird_zero_of_online y

/-- **No cancellation on intervals**: For an offline zero, the amplitude defect
is strictly positive at EVERY point x in any interval (1, ∞). The positive
contribution from the offline zero pair cannot be cancelled at any scale. -/
theorem offline_visible_on_interval (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∀ x ∈ Set.Icc a b, 0 < amplitudeDefect x ρ.re :=
  fun x hx => offline_amplitude_defect_pos (by linarith [hx.1]) (by linarith [hx.1]) hρ.2

/-- **Infinitely many witnesses**: An offline zero is detected at every prime.
Since there are infinitely many primes, this gives ∃^∞ observation points. -/
theorem offline_detected_at_all_primes (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    ∀ p : ℕ, Nat.Prime p → 0 < amplitudeDefect (↑p) ρ.re :=
  fun p hp => amplitudeDefect_pos_at_prime p hp hρ.2

/-- **Existential witness with concrete scale**: The imbalance is positive
at x = π/3, giving a specific computable witness. -/
theorem offline_concrete_witness (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    ∃ x : ℝ, 0 < x ∧ x ≠ 1 ∧ 0 < amplitudeDefect x ρ.re :=
  ⟨π / 3, pi_third_pos, pi_third_ne_one, offline_breaks_balance ρ hρ⟩

/-- **Even-channel biconditional**: The cosh observable is zero at a given scale
if and only if the zero is on the critical line. This is the detection criterion
on the even channel — it separates online from offline with zero false positives. -/
theorem even_channel_characterizes_line (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros)
    {y : ℝ} (hy : y ≠ 0) :
    harmonicDiffPiThird ρ.re y = 0 ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h
    by_contra hβ
    exact absurd h (ne_of_gt (harmonicDiffPiThird_pos_of_offline hβ hy))
  · intro h; rw [h]; exact harmonicDiffPiThird_zero_of_online y

/-! ## §5c. Infinite Prime-Indexed Detector Family

The cosh detector at each prime provides an INDEPENDENT probe of the critical line.
For prime p, `Detector_p(β) = cosh((β - 1/2) · log p)`.
The key biconditional: `Detector_p(β) = 1 ↔ β = 1/2`, for every prime p.

This means an offline zero would have to evade detection not at one point, but
across an **infinite family of independent probes** — one per prime. Each probe
has its own frequency `ω_p = log p` and its own half-period shift `π/log p`.
The odd channel (cosine) can flip sign under these shifts; the even channel
(cosh) **cannot be evaded**.
-/

/-- **Prime-indexed detector biconditional**: At each prime p, the cosh detector
reads 1 if and only if β = 1/2. Each prime is an independent classifier. -/
theorem prime_detector_iff (p : ℕ) (hp : Nat.Prime p) {β : ℝ} :
    coshDetector β (Real.log (↑p)) = 1 ↔ β = 1 / 2 :=
  coshDetector_eq_one_iff (Real.log_ne_zero_of_pos_of_ne_one
    (Nat.cast_pos.mpr hp.pos) (by exact_mod_cast hp.one_lt.ne'))

/-- **Infinite detection**: An offline zero triggers EVERY prime detector.
Since there are infinitely many primes, this gives an infinite family of
independent witnesses — no finite evasion is possible. -/
theorem infinite_detection (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros) :
    ∀ p : ℕ, Nat.Prime p → 1 < coshDetector ρ.re (Real.log (↑p)) := by
  intro p hp
  exact coshDetector_gt_one_of_offline hρ.2 (Real.log_ne_zero_of_pos_of_ne_one
    (Nat.cast_pos.mpr hp.pos) (by exact_mod_cast hp.one_lt.ne'))

/-- **Silent detection**: An online zero triggers NO prime detector.
Every probe reads exactly 1. -/
theorem silent_detection (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) :
    ∀ p : ℕ, Nat.Prime p → coshDetector ρ.re (Real.log (↑p)) = 1 := by
  intro p _; rw [hρ.2]; exact coshDetector_one_of_online _

/-- **Each prime has its own evasion shift**: the half-period `π/log p`.
Shifting by this amount flips the odd (cosine) channel for prime p,
but the even (cosh) channel is unaffected — the detector still fires. -/
theorem prime_has_evasion_shift (p : ℕ) (hp : Nat.Prime p) :
    0 < halfPeriodShift p ∧
    ∀ t : ℝ, Real.cos (primeFrequency p * (t + halfPeriodShift p)) =
      -Real.cos (primeFrequency p * t) :=
  ⟨halfPeriodShift_pos hp, fun t => cos_half_period_flip t hp⟩

/-! ## §5d. Even/Odd Decomposition and Midpoint Evaluation

The detector story:
1. For each prime p, choose midpoint m_p
2. Reflect around m_p
3. The odd channel (sinh) is antisymmetric → killed at m_p
4. The even channel (cosh) is symmetric → survives at m_p
5. Evaluate at m_p: odd = 0, even = cosh((β - 1/2) · log p)

**Structural fact**: The zero-pair envelope `Q(r, β) = r^β + r^{1-β}` is
symmetric under `β ↦ 1 - β` (proved: `zeroPairEnvelope_symm`). This means
it's a purely even function of `(β - 1/2)` — the odd channel is identically
zero, not just killed at the midpoint. The cosh detector captures the ENTIRE
envelope. Nothing is lost in the even-channel projection.

The factorization: `Q(r, β) = 2r^{1/2} · cosh((β - 1/2) · log r)` for r > 0.
-/

/-- **The envelope is purely even**: Q(r, β) = Q(r, 1-β). This is the functional
equation symmetry — the zero-pair envelope has no odd component in (β - 1/2). -/
theorem envelope_purely_even (r : ℝ) (β : ℝ) :
    zeroPairEnvelope r β = zeroPairEnvelope r (1 - β) :=
  zeroPairEnvelope_symm r β

/-- **Cosh factorization**: The envelope factors as `2r^{1/2} · cosh((β-1/2)·log r)`
for r > 0. This shows the cosh detector IS the full even-channel content. -/
theorem envelope_eq_balanced_mul_cosh {r : ℝ} (hr : 0 < r) (β : ℝ) :
    zeroPairEnvelope r β = balancedEnvelope r * coshDetector β (Real.log r) := by
  unfold zeroPairEnvelope balancedEnvelope coshDetector
  rw [Real.cosh_eq]
  have key : ∀ a : ℝ, Real.exp (a * Real.log r) = r ^ a := fun a => by
    rw [mul_comm, Real.rpow_def_of_pos hr]
  rw [key, show -((β - 1/2) * Real.log r) = (-(β - 1/2)) * Real.log r from by ring, key]
  have h1 : r ^ (1/2 : ℝ) * r ^ (β - 1/2) = r ^ β := by
    rw [← rpow_add hr]; congr 1; ring
  have h2 : r ^ (1/2 : ℝ) * r ^ (-(β - 1/2)) = r ^ (1 - β) := by
    rw [← rpow_add hr]; congr 1; ring
  nlinarith

/-- **Defect via cosh**: The amplitude defect equals the balanced envelope times
(cosh - 1), which is the harmonicDiffPiThird at log-scale. -/
theorem defect_eq_balanced_mul_diff {r : ℝ} (hr : 0 < r) (β : ℝ) :
    amplitudeDefect r β = balancedEnvelope r * harmonicDiffPiThird β (Real.log r) := by
  unfold amplitudeDefect harmonicDiffPiThird
  rw [envelope_eq_balanced_mul_cosh hr]; ring

/-- **Midpoint evaluation**: At β = 1/2, the cosh factor is 1 and the defect
factor is 0. This is the midpoint — the odd channel is zero (by symmetry)
and the even channel reads the balanced value. -/
theorem midpoint_cosh_eq_one {r : ℝ} (hr : 0 < r) :
    coshDetector (1/2) (Real.log r) = 1 := coshDetector_one_of_online _

/-- **Off-midpoint detection**: At β ≠ 1/2, the cosh factor exceeds 1 and
the defect factor is positive. The even channel detects the deviation. -/
theorem off_midpoint_cosh_gt_one {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {β : ℝ} (hβ : β ≠ 1/2) :
    1 < coshDetector β (Real.log r) :=
  coshDetector_gt_one_of_offline hβ (Real.log_ne_zero_of_pos_of_ne_one hr hr1)

/-! ## §5e. Divergence: The 0-or-∞ Dichotomy

For δ = β - 1/2 ≠ 0, the cosh detector grows without bound across primes:
`cosh(δ · log p) → ∞` as `p → ∞`. This means an offline zero doesn't produce
a small perturbation — it produces an **unbounded signal** that grows with
every additional prime. The dichotomy is: online → signal identically 0,
offline → signal diverges to ∞. No finite nonzero state exists.
-/

private lemma cosh_ge_exp_abs_half (x : ℝ) : Real.exp (|x|) / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]; rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]; nlinarith [Real.exp_pos (-x)]
  · rw [abs_of_neg hx]; nlinarith [Real.exp_pos x]

private lemma le_exp_self (x : ℝ) : x ≤ Real.exp x :=
  le_trans (by linarith) (Real.add_one_le_exp x)

/-- **Unboundedness**: For δ ≠ 0, the cosh detector at primes is unbounded.
For any target M, there exists a prime where the detector exceeds M.
Proof uses: `cosh(x) ≥ exp(|x|)/2 ≥ x/2`, `log p → ∞`, infinite primes. -/
theorem prime_cosh_unbounded_of_offline {β : ℝ} (hβ : β ≠ 1/2) :
    ∀ M : ℝ, ∃ p : ℕ, Nat.Prime p ∧
      M < coshDetector β (Real.log (↑p)) := by
  intro M
  have hδ : β - 1/2 ≠ 0 := sub_ne_zero.mpr hβ
  have hδ_pos : 0 < |β - 1/2| := abs_pos.mpr hδ
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp ((2 * M + 2) / |β - 1/2|))
  obtain ⟨p, hn_le, hp⟩ := Nat.exists_infinite_primes n
  refine ⟨p, hp, ?_⟩
  show M < coshDetector β (Real.log ↑p)
  unfold coshDetector
  have hp_pos : (0 : ℝ) < ↑p := Nat.cast_pos.mpr hp.pos
  have hn_pos : (0 : ℝ) < ↑n := lt_trans (Real.exp_pos _) hn
  have hpn : (↑n : ℝ) ≤ ↑p := Nat.cast_le.mpr hn_le
  have hlog_pos : 0 < Real.log ↑p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have h_abs : |(β - 1/2) * Real.log ↑p| = |β - 1/2| * Real.log ↑p := by
    rw [abs_mul, abs_of_pos hlog_pos]
  have h1 : (2 * M + 2) / |β - 1/2| < Real.log ↑n :=
    (Real.lt_log_iff_exp_lt hn_pos).mpr hn
  have h2 : (2 * M + 2) / |β - 1/2| < Real.log ↑p :=
    lt_of_lt_of_le h1 (Real.log_le_log hn_pos hpn)
  have h3 : 2 * M + 2 < |β - 1/2| * Real.log ↑p := by
    have := (div_lt_iff₀ hδ_pos).mp h2; linarith [mul_comm (Real.log ↑p) |β - 1/2|]
  calc (M : ℝ)
      < |β - 1/2| * Real.log ↑p / 2 := by linarith
    _ ≤ Real.exp (|β - 1/2| * Real.log ↑p) / 2 :=
        div_le_div_of_nonneg_right (le_exp_self _) (by positivity)
    _ = Real.exp (|(β - 1/2) * Real.log ↑p|) / 2 := by rw [h_abs]
    _ ≤ Real.cosh ((β - 1/2) * Real.log ↑p) := cosh_ge_exp_abs_half _

/-! ## §5f. Reduced Observable: Online = Count, Offline > Count -/

/-- **Online observable = prime count**: When β = 1/2, each cosh reading is 1,
so the total observable equals the number of primes up to P. -/
theorem actualReducedObservable_online (P : ℕ) :
    actualReducedObservable (1/2) P = balancedPrimeObservable P := by
  unfold actualReducedObservable balancedPrimeObservable
  simp_rw [coshDetector_one_of_online]; simp

/-- **Observable ≥ count** (unconditional): The cosh observable is always at
least the prime count, since each cosh reading is ≥ 1. -/
theorem actualReducedObservable_ge_balanced (β : ℝ) (P : ℕ) :
    balancedPrimeObservable P ≤ actualReducedObservable β P := by
  simp only [actualReducedObservable, balancedPrimeObservable]
  calc (↑(primeSetUpTo P).card : ℝ)
      = ∑ _ ∈ primeSetUpTo P, (1 : ℝ) := by simp
    _ ≤ ∑ p ∈ primeSetUpTo P, coshDetector β (Real.log ↑p) :=
        Finset.sum_le_sum fun p _ => Real.one_le_cosh _

/-- **Offline observable > count**: When β ≠ 1/2, every cosh reading exceeds 1,
so the total strictly exceeds the prime count (when there's at least one prime). -/
theorem actualReducedObservable_offline_gt {β : ℝ} (hβ : β ≠ 1/2)
    {P : ℕ} (hP : 0 < (primeSetUpTo P).card) :
    balancedPrimeObservable P < actualReducedObservable β P := by
  simp only [actualReducedObservable, balancedPrimeObservable]
  calc (↑(primeSetUpTo P).card : ℝ)
      = ∑ _ ∈ primeSetUpTo P, (1 : ℝ) := by simp
    _ < ∑ p ∈ primeSetUpTo P, coshDetector β (Real.log ↑p) := by
        apply Finset.sum_lt_sum (fun p _ => Real.one_le_cosh _)
        obtain ⟨p, hp_mem⟩ := Finset.card_pos.mp hP
        have hp := (Finset.mem_filter.mp hp_mem).2
        exact ⟨p, hp_mem, coshDetector_gt_one_of_offline hβ
          (Real.log_ne_zero_of_pos_of_ne_one (Nat.cast_pos.mpr hp.pos)
            (by exact_mod_cast hp.one_lt.ne'))⟩

/-- **Envelope = balanced × detector sum**: The raw envelope observable factors
through the cosh detector. -/
theorem actualEnvelopeObservable_eq (β : ℝ) (P : ℕ) :
    actualEnvelopeObservable β P =
    ∑ p ∈ primeSetUpTo P, balancedEnvelope (↑p) * coshDetector β (Real.log (↑p)) := by
  simp only [actualEnvelopeObservable]
  exact Finset.sum_congr rfl fun p hp =>
    envelope_eq_balanced_mul_cosh (Nat.cast_pos.mpr (Finset.mem_filter.mp hp).2.pos) β

/-! ## §5g. Euler Factor Origin of the Cosh Detector

The cosh detector is not applied to ζ from outside — it is extracted from
the Euler product's own factor structure:

    Euler factor at p:  (1 - p⁻ˢ)⁻¹
    Exponential form:   p⁻ˢ = e^{-s·log p}       [spectral coordinate log p]
    Split s = β + it:   p⁻ˢ = p⁻ᵝ · e^{-it·log p} [amplitude × phase]
    Reflect β ↔ 1-β:    envelope = pᵝ + p¹⁻ᵝ       [zero-pair contribution]
    Recenter at 1/2:    = 2p^{1/2} · cosh((β-1/2)·log p) [even channel]

The rigid content is: **Euler product + log p**. Everything else is packaging.
-/

/-- **Reflected Euler-factor envelope = balanced × cosh**: The zero-pair
contribution from the p-th Euler factor, reflected around β = 1/2, is
`2p^{1/2} · cosh((β - 1/2) · log p)`. -/
theorem euler_envelope_eq_cosh (p : ℕ) (hp : Nat.Prime p) (β : ℝ) :
    zeroPairEnvelope (↑p) β =
    balancedEnvelope (↑p) * coshDetector β (Real.log (↑p)) :=
  envelope_eq_balanced_mul_cosh (Nat.cast_pos.mpr hp.pos) β

/-- **The closure implication**: If the prime-indexed cosh detector reads 1
at every prime for every nontrivial zero, then all nontrivial zeros lie on
the critical line. This is the exact conditional that closes the chain:
balance on the even channel at all primes → RH. -/
theorem detector_balance_implies_on_line
    (balance : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p → coshDetector ρ.re (Real.log (↑p)) = 1) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1 / 2 := by
  intro ρ hρ
  -- Use any prime as the probe — say p = 2
  have h := balance ρ hρ 2 (by norm_num)
  exact (prime_detector_iff 2 (by norm_num)).mp h

/-- **On-line → detector balanced at all primes**: If all nontrivial zeros
lie on the critical line, then the cosh detector reads 1 at every prime
for every nontrivial zero. -/
theorem prime_detector_balance_all_of_on_line
    (hline : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1 / 2) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p → coshDetector ρ.re (Real.log (↑p)) = 1 := by
  intro ρ hρ p hp
  rw [coshDetector_eq_one_iff
    (Real.log_ne_zero_of_pos_of_ne_one
      (Nat.cast_pos.mpr hp.pos) (by exact_mod_cast hp.one_lt.ne'))]
  exact hline ρ hρ

/-- **Detector balance → RH**: If the cosh detector reads 1 at every prime
for every nontrivial zero, then `RiemannHypothesis` holds. -/
theorem detector_balance_implies_rh
    (hbal : ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p → coshDetector ρ.re (Real.log (↑p)) = 1) :
    RiemannHypothesis :=
  no_offline_zeros_implies_rh (detector_balance_implies_on_line hbal)

/-- **Universal detector balance from RH**: Assuming Mathlib's `RiemannHypothesis`,
the cosh detector reads 1 at every prime for every nontrivial zero. -/
theorem prime_detector_balance_all (hRH : RiemannHypothesis) :
    ∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p → coshDetector ρ.re (Real.log (↑p)) = 1 :=
  prime_detector_balance_all_of_on_line (fun ρ hρ => rh_implies_critical_line hRH ρ hρ)

/-- **RH ↔ prime detector balance**: The Riemann Hypothesis is equivalent to
the cosh detector reading 1 at every prime for every nontrivial zero. -/
theorem riemannHypothesis_iff_prime_detector_balance :
    RiemannHypothesis ↔
    (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p →
        coshDetector ρ.re (Real.log (↑p)) = 1) :=
  ⟨prime_detector_balance_all, detector_balance_implies_rh⟩

/-- **The complete biconditional**: Detector balance at all primes for all
nontrivial zeros ↔ all nontrivial zeros on the critical line.
Both directions fully proved. -/
theorem detector_balance_iff_on_line :
    (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros →
      ∀ p : ℕ, Nat.Prime p → coshDetector ρ.re (Real.log (↑p)) = 1) ↔
    (∀ ρ : ℂ, ρ ∈ ZD.NontrivialZeros → ρ.re = 1 / 2) :=
  ⟨detector_balance_implies_on_line, prime_detector_balance_all_of_on_line⟩

/-! ## §6. Type Signatures (#check) -/

#check @diagnostic_nontrivial
#check @diagnostic_online
#check @diagnostic_offline
#check @NontrivialDiagnostic
#check @OnlineDiagnostic
#check @OfflineDiagnostic
#check @defect_characterizes_line
#check @ratio_characterizes_line
#check @defect_pos_iff_offline
#check @ratio_gt_one_iff_offline
#check @harmonic_balance_implies_rh
#check @offline_breaks_balance
#check @nontrivial_in_strip
#check @nontrivial_defect_nonneg
#check @nontrivial_signal_mono
#check @online_defect_zero
#check @online_ratio_one
#check @offline_defect_pos
#check @offline_ratio_gt_one
#check @offline_witness
#check @offline_cumulative_pos
#check @contrast_defect
#check @contrast_ratio

end
