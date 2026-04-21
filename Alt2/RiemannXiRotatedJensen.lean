import Mathlib
import RequestProject.RiemannXiRotated
import RequestProject.JensenZerosBound
import RequestProject.ZeroCountJensen

/-!
# Rotated-ξ Jensen zero-count over short height windows

Hadamard-Jensen short-window zero count for the rotated Riemann ξ-function:
given a radius-4 uniform bound `‖Ξ(z)‖ ≤ B · ‖Ξ(c)‖` on the ball of radius 4
around the safe base point `c = 2 + iT`, the number of nontrivial zeros of
ζ with ordinates in `[T-1, T+1]` is bounded by `log B / log (4/3)`.

Combined with an order-1 growth bound on ξ (⟹ `log B = O(log T)`), this
yields the classical `N(T+1) − N(T-1) = O(log T)` short-window count used
in the critical-strip Landau `‖ζ'/ζ(σ+iT)‖ = O((log T)²)` bound.

Ported from Aristotle's Hadamard-Jensen package (codex2). Axiom footprint:
`[propext, Classical.choice, Quot.sound]`.
-/

open Filter Topology Complex Real Set

noncomputable section

namespace ZD

/-- Nontrivial zeros whose ordinates lie within `H` of height `T`. -/
def nontrivialZerosNearHeight (T H : ℝ) : Set ℂ :=
  {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - T| ≤ H}

/-- Explicit affine coordinates for the rotated variable `z = (ρ - 1/2) / i`. -/
theorem sub_half_div_I_eq (ρ : ℂ) :
    ((ρ - (1 / 2 : ℂ)) / Complex.I) =
      (ρ.im : ℂ) + ((1 / 2 - ρ.re : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [Complex.sub_re, Complex.sub_im]

/-- Rotated-coordinate center corresponding to the real point `σ` under
`z ↦ 1/2 + i z`. For `σ > 1`, this is a safe Jensen center because
`ξ(σ) ≠ 0`. -/
def riemannXiRotatedCenter (σ : ℝ) : ℂ :=
  ((σ : ℂ) - (1 / 2 : ℂ)) / Complex.I

/-- Height-`T` translate of the safe Jensen center corresponding to `σ`. Under
`z ↦ 1/2 + i z`, this is exactly the point `σ + iT`. -/
def riemannXiRotatedCenterAt (σ T : ℝ) : ℂ :=
  (T : ℂ) + riemannXiRotatedCenter σ

theorem riemannXiRotatedCenterAt_eq (σ T : ℝ) :
    riemannXiRotatedCenterAt σ T =
      (T : ℂ) + ((1 / 2 - σ : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [riemannXiRotatedCenterAt, riemannXiRotatedCenter]

theorem one_half_add_I_mul_riemannXiRotatedCenter (σ : ℝ) :
    (1 / 2 : ℂ) + Complex.I * riemannXiRotatedCenter σ = σ := by
  unfold riemannXiRotatedCenter
  field_simp [Complex.I_ne_zero]
  ring

theorem riemannXiRotated_at_center (σ : ℝ) :
    riemannXiRotated (riemannXiRotatedCenter σ) = riemannXi σ := by
  unfold riemannXiRotated
  rw [one_half_add_I_mul_riemannXiRotatedCenter]

theorem one_half_add_I_mul_riemannXiRotatedCenterAt (σ T : ℝ) :
    (1 / 2 : ℂ) + Complex.I * riemannXiRotatedCenterAt σ T =
      (σ : ℂ) + (T : ℂ) * Complex.I := by
  calc
    (1 / 2 : ℂ) + Complex.I * riemannXiRotatedCenterAt σ T
      = ((1 / 2 : ℂ) + Complex.I * riemannXiRotatedCenter σ) + (T : ℂ) * Complex.I := by
          unfold riemannXiRotatedCenterAt
          ring
    _ = (σ : ℂ) + (T : ℂ) * Complex.I := by
          rw [one_half_add_I_mul_riemannXiRotatedCenter]

theorem riemannXiRotated_at_centerAt (σ T : ℝ) :
    riemannXiRotated (riemannXiRotatedCenterAt σ T) =
      riemannXi ((σ : ℂ) + (T : ℂ) * Complex.I) := by
  unfold riemannXiRotated
  rw [one_half_add_I_mul_riemannXiRotatedCenterAt]

theorem completedRiemannZeta_ne_zero_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    completedRiemannZeta s ≠ 0 := by
  have hs_ne0 : s ≠ 0 := by
    intro hs0
    have hre := congrArg Complex.re hs0
    simp at hre
    linarith
  intro hΛ
  have hζ0 : riemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs_ne0, hΛ, zero_div]
  exact (riemannZeta_ne_zero_of_one_lt_re hs) hζ0

theorem riemannXi_ne_zero_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    riemannXi s ≠ 0 := by
  have hs_ne0 : s ≠ 0 := by
    intro hs0
    have hre := congrArg Complex.re hs0
    simp at hre
    linarith
  have hs_ne1 : s ≠ 1 := by
    intro hs1
    have hre := congrArg Complex.re hs1
    simp at hre
    linarith
  rw [riemannXi_eq_classical_of_ne_zero_of_ne_one s hs_ne0 hs_ne1]
  refine mul_ne_zero ?_ (completedRiemannZeta_ne_zero_of_one_lt_re s hs)
  exact div_ne_zero (mul_ne_zero hs_ne0 (sub_ne_zero.mpr hs_ne1)) two_ne_zero

theorem riemannXiRotated_ne_zero_at_center_of_one_lt
    (σ : ℝ) (hσ : 1 < σ) :
    riemannXiRotated (riemannXiRotatedCenter σ) ≠ 0 := by
  rw [riemannXiRotated_at_center]
  exact riemannXi_ne_zero_of_one_lt_re (σ : ℂ) (by simpa using hσ)

theorem riemannXiRotated_ne_zero_at_centerAt_of_one_lt
    (σ T : ℝ) (hσ : 1 < σ) :
    riemannXiRotated (riemannXiRotatedCenterAt σ T) ≠ 0 := by
  rw [riemannXiRotated_at_centerAt]
  exact riemannXi_ne_zero_of_one_lt_re ((σ : ℂ) + (T : ℂ) * Complex.I) (by
    simp [hσ])

theorem riemannXiRotated_analyticOrderAt_ne_top (z : ℂ) :
    analyticOrderAt riemannXiRotated z ≠ ⊤ := by
  intro h_top
  rw [analyticOrderAt_eq_top] at h_top
  have h_fre : ∃ᶠ w in 𝓝[≠] z, riemannXiRotated w = 0 := by
    have : ∀ᶠ w in 𝓝[≠] z, riemannXiRotated w = 0 :=
      h_top.filter_mono nhdsWithin_le_nhds
    exact this.frequently
  have hEq :=
    riemannXiRotated_analyticOnNhd_univ.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ z) h_fre
  have h0 := hEq (Set.mem_univ (riemannXiRotatedCenter 2))
  exact (riemannXiRotated_ne_zero_at_center_of_one_lt 2 (by norm_num)) h0

theorem riemannXiRotated_zeros_finite_in_closedBall (c : ℂ) (R : ℝ) :
    (Metric.closedBall c R ∩ {z | riemannXiRotated z = 0}).Finite := by
  have hMero : MeromorphicOn riemannXiRotated (Metric.closedBall c R) :=
    (riemannXiRotated_analyticOnNhd_univ.mono (Set.subset_univ _)).meromorphicOn
  have hDiv_fin :=
    (MeromorphicOn.divisor riemannXiRotated (Metric.closedBall c R)).finiteSupport
      (isCompact_closedBall c R)
  apply hDiv_fin.subset
  intro z hz
  have hz_ball : z ∈ Metric.closedBall c R := hz.1
  have hz_zero : riemannXiRotated z = 0 := hz.2
  have hAnal : AnalyticAt ℂ riemannXiRotated z :=
    riemannXiRotated_analyticOnNhd_univ z (Set.mem_univ _)
  have hAnalOrd_ne_zero : analyticOrderAt riemannXiRotated z ≠ 0 := by
    intro hzero
    rw [hAnal.analyticOrderAt_eq_zero] at hzero
    exact hzero hz_zero
  have hAnalOrd_ne_top := riemannXiRotated_analyticOrderAt_ne_top z
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℕ∞) = analyticOrderAt riemannXiRotated z :=
    ENat.ne_top_iff_exists.mp hAnalOrd_ne_top
  have hn_ne : n ≠ 0 := by
    intro h
    apply hAnalOrd_ne_zero
    rw [← hn, h]
    rfl
  simp only [Function.mem_support]
  rw [MeromorphicOn.divisor_apply hMero hz_ball, hAnal.meromorphicOrderAt_eq, ← hn]
  simp [hn_ne]

theorem nontrivialZerosNearHeight_finite (T H : ℝ) :
    (nontrivialZerosNearHeight T H).Finite := by
  apply Set.Finite.subset (ZeroCount.NontrivialZeros_inter_closedBall_finite (|T| + H + 1))
  intro ρ hρ
  rcases hρ with ⟨hρ_ntz, hρ_im⟩
  have hnorm : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
  have hre : |ρ.re| ≤ 1 := by
    have hρ_re_pos : 0 < ρ.re := hρ_ntz.1
    have hρ_re_lt : ρ.re < 1 := hρ_ntz.2.1
    rw [abs_of_pos hρ_re_pos]
    linarith
  have him : |ρ.im| ≤ |T| + H := by
    refine abs_le.mpr ?_
    constructor
    · have hT : -|T| ≤ T := neg_abs_le T
      have hleft : -H ≤ ρ.im - T := (abs_le.mp hρ_im).1
      linarith
    · have hT : T ≤ |T| := le_abs_self T
      have hright : ρ.im - T ≤ H := (abs_le.mp hρ_im).2
      linarith
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) (|T| + H + 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  exact ⟨hρ_ntz, hmem⟩

theorem nontrivialZeroToRotated_mem_closedBall_of_near_height
    {ρ : ℂ} {T H : ℝ}
    (hρ : ρ ∈ nontrivialZerosNearHeight T H) :
    ((ρ - (1 / 2 : ℂ)) / Complex.I) ∈ Metric.closedBall (riemannXiRotatedCenterAt 2 T) (H + 2) := by
  rcases hρ with ⟨hρ_ntz, hρ_im⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hρ_re_lt : ρ.re < 1 := hρ_ntz.2.1
  have hρ_re_pos : 0 < ρ.re := hρ_ntz.1
  have hre_nonneg : 0 ≤ 2 - ρ.re := by linarith
  have hre_le : 2 - ρ.re ≤ 2 := by linarith
  have h_eq :
      ((ρ - (1 / 2 : ℂ)) / Complex.I) - riemannXiRotatedCenterAt 2 T =
        (((ρ.im - T : ℝ) : ℂ) + ((2 - ρ.re : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext <;>
      simp [riemannXiRotatedCenterAt_eq, Complex.sub_re, Complex.sub_im]
  calc
    ‖((ρ - (1 / 2 : ℂ)) / Complex.I) - riemannXiRotatedCenterAt 2 T‖
      = ‖(((ρ.im - T : ℝ) : ℂ) + ((2 - ρ.re : ℝ) : ℂ) * Complex.I)‖ := by
          rw [h_eq]
    _ ≤ |ρ.im - T| + |2 - ρ.re| := by
          simpa using
            (Complex.norm_le_abs_re_add_abs_im
              ((((ρ.im - T : ℝ) : ℂ) + ((2 - ρ.re : ℝ) : ℂ) * Complex.I)))
    _ ≤ H + 2 := by
          rw [abs_of_nonneg hre_nonneg]
          linarith

theorem nontrivialZeroToRotated_mem_rotatedZeroSet_of_near_height
    {ρ : ℂ} {T H : ℝ} (hρ : ρ ∈ nontrivialZerosNearHeight T H) :
    ((ρ - (1 / 2 : ℂ)) / Complex.I) ∈ {z | riemannXiRotated z = 0} := by
  exact riemannXiRotated_eq_zero_of_mem_NontrivialZeros ρ hρ.1

theorem nontrivialZeroToRotated_image_subset
    (T H : ℝ) :
    (fun ρ : ℂ => ((ρ - (1 / 2 : ℂ)) / Complex.I)) '' nontrivialZerosNearHeight T H ⊆
      Metric.closedBall (riemannXiRotatedCenterAt 2 T) (H + 2) ∩
        {z | riemannXiRotated z = 0} := by
  intro z hz
  rcases hz with ⟨ρ, hρ, rfl⟩
  exact ⟨nontrivialZeroToRotated_mem_closedBall_of_near_height hρ,
    nontrivialZeroToRotated_mem_rotatedZeroSet_of_near_height hρ⟩

theorem nontrivialZeroToRotated_injective :
    Function.Injective (fun ρ : ℂ => ((ρ - (1 / 2 : ℂ)) / Complex.I)) := by
  intro ρ₁ ρ₂ h
  have hmul := congrArg (fun z : ℂ => z * Complex.I) h
  have hsub : ρ₁ - (1 / 2 : ℂ) = ρ₂ - (1 / 2 : ℂ) := by
    simpa [Complex.I_ne_zero] using hmul
  have hadd := congrArg (fun z : ℂ => z + (1 / 2 : ℂ)) hsub
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd

theorem ncard_nontrivialZerosNearHeight_le_ncard_rotated_zeros
    (T H : ℝ) :
    ((nontrivialZerosNearHeight T H).ncard : ℝ) ≤
      ((Metric.closedBall (riemannXiRotatedCenterAt 2 T) (H + 2) ∩
        {z | riemannXiRotated z = 0}).ncard : ℝ) := by
  let f : ℂ → ℂ := fun ρ : ℂ => ((ρ - (1 / 2 : ℂ)) / Complex.I)
  have hfin_big :
      (Metric.closedBall (riemannXiRotatedCenterAt 2 T) (H + 2) ∩
        {z | riemannXiRotated z = 0}).Finite :=
    riemannXiRotated_zeros_finite_in_closedBall (riemannXiRotatedCenterAt 2 T) (H + 2)
  have hsub :
      f '' nontrivialZerosNearHeight T H ⊆
        Metric.closedBall (riemannXiRotatedCenterAt 2 T) (H + 2) ∩
          {z | riemannXiRotated z = 0} :=
    nontrivialZeroToRotated_image_subset T H
  have hmono :
      (f '' nontrivialZerosNearHeight T H).ncard ≤
        (Metric.closedBall (riemannXiRotatedCenterAt 2 T) (H + 2) ∩
          {z | riemannXiRotated z = 0}).ncard :=
    Set.ncard_le_ncard hsub hfin_big
  have himage :
      (f '' nontrivialZerosNearHeight T H).ncard = (nontrivialZerosNearHeight T H).ncard :=
    Set.ncard_image_of_injective _ nontrivialZeroToRotated_injective
  exact_mod_cast himage.symm.trans_le hmono

theorem ncard_nontrivialZerosNearHeight_one_le_ncard_rotated_zeros (T : ℝ) :
    ((nontrivialZerosNearHeight T 1).ncard : ℝ) ≤
      ((Metric.closedBall (riemannXiRotatedCenterAt 2 T) 3 ∩
        {z | riemannXiRotated z = 0}).ncard : ℝ) := by
  convert ncard_nontrivialZerosNearHeight_le_ncard_rotated_zeros T 1 using 1
  norm_num

/-- A radius-`4` outer bound for rotated `ξ` around the safe center `2 + iT`
controls the number of nontrivial zeros with ordinates in `[T-1, T+1]`. -/
theorem ncard_nontrivialZerosNearHeight_one_le_of_rotated_bound
    {T B : ℝ} (hB : 1 ≤ B)
    (hbound : ∀ z ∈ Metric.closedBall (riemannXiRotatedCenterAt 2 T) 4,
      ‖riemannXiRotated z‖ ≤ B * ‖riemannXiRotated (riemannXiRotatedCenterAt 2 T)‖) :
    ((nontrivialZerosNearHeight T 1).ncard : ℝ) ≤ Real.log B / Real.log (4 / 3) := by
  refine le_trans (ncard_nontrivialZerosNearHeight_one_le_ncard_rotated_zeros T) ?_
  exact JensenZerosBound.zeros_bound_centered (r := 3) (R := 4) (B := B)
    (by norm_num) (by norm_num) hB
    (riemannXiRotated_analyticOnNhd_univ.mono (Set.subset_univ _))
    (riemannXiRotated_ne_zero_at_centerAt_of_one_lt 2 T (by norm_num)) hbound

/-- Variant of the local zero-count bound using an explicit positive lower bound
at the center and a uniform radius-`4` outer bound. -/
theorem ncard_nontrivialZerosNearHeight_one_le_of_rotated_bound_center_norm_le
    {T m M : ℝ} (hm : 0 < m)
    (hcenter : m ≤ ‖riemannXiRotated (riemannXiRotatedCenterAt 2 T)‖)
    (hbound : ∀ z ∈ Metric.closedBall (riemannXiRotatedCenterAt 2 T) 4, ‖riemannXiRotated z‖ ≤ M) :
    ((nontrivialZerosNearHeight T 1).ncard : ℝ) ≤ Real.log (M / m) / Real.log (4 / 3) := by
  refine le_trans (ncard_nontrivialZerosNearHeight_one_le_ncard_rotated_zeros T) ?_
  exact JensenZerosBound.zeros_bound_centered_of_center_norm_le
    (r := 3) (R := 4) (m := m) (M := M)
    (by norm_num) (by norm_num) hm
    (riemannXiRotated_analyticOnNhd_univ.mono (Set.subset_univ _))
    hcenter hbound

/-- Centered Jensen bound for rotated `ξ` around a right-half-plane basepoint. -/
theorem riemannXiRotated_zeros_bound_centered_of_one_lt
    {σ r R B : ℝ}
    (hσ : 1 < σ) (hr : 0 < r) (hrR : r < R) (hB : 1 ≤ B)
    (hbound : ∀ z ∈ Metric.closedBall (riemannXiRotatedCenter σ) R,
      ‖riemannXiRotated z‖ ≤ B * ‖riemannXiRotated (riemannXiRotatedCenter σ)‖) :
    ((Metric.closedBall (riemannXiRotatedCenter σ) r ∩ {z | riemannXiRotated z = 0}).ncard : ℝ)
      ≤ Real.log B / Real.log (R / r) := by
  exact JensenZerosBound.zeros_bound_centered hr hrR hB
    (riemannXiRotated_analyticOnNhd_univ.mono (Set.subset_univ _))
    (riemannXiRotated_ne_zero_at_center_of_one_lt σ hσ) hbound

/-- Variant of the centered Jensen bound using an explicit positive lower bound
at the center and a uniform outer bound. -/
theorem riemannXiRotated_zeros_bound_centered_of_center_norm_le
    {σ r R m M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hm : 0 < m)
    (hcenter : m ≤ ‖riemannXiRotated (riemannXiRotatedCenter σ)‖)
    (hbound : ∀ z ∈ Metric.closedBall (riemannXiRotatedCenter σ) R, ‖riemannXiRotated z‖ ≤ M) :
    ((Metric.closedBall (riemannXiRotatedCenter σ) r ∩ {z | riemannXiRotated z = 0}).ncard : ℝ)
      ≤ Real.log (M / m) / Real.log (R / r) := by
  exact JensenZerosBound.zeros_bound_centered_of_center_norm_le hr hrR hm
    (riemannXiRotated_analyticOnNhd_univ.mono (Set.subset_univ _))
    hcenter hbound

/-- Height-`T` centered Jensen bound for rotated `ξ` around the safe basepoint
corresponding to `σ + iT` with `σ > 1`. -/
theorem riemannXiRotated_zeros_bound_centered_at_of_one_lt
    {σ T r R B : ℝ}
    (hσ : 1 < σ) (hr : 0 < r) (hrR : r < R) (hB : 1 ≤ B)
    (hbound : ∀ z ∈ Metric.closedBall (riemannXiRotatedCenterAt σ T) R,
      ‖riemannXiRotated z‖ ≤ B * ‖riemannXiRotated (riemannXiRotatedCenterAt σ T)‖) :
    ((Metric.closedBall (riemannXiRotatedCenterAt σ T) r ∩ {z | riemannXiRotated z = 0}).ncard : ℝ)
      ≤ Real.log B / Real.log (R / r) := by
  exact JensenZerosBound.zeros_bound_centered hr hrR hB
    (riemannXiRotated_analyticOnNhd_univ.mono (Set.subset_univ _))
    (riemannXiRotated_ne_zero_at_centerAt_of_one_lt σ T hσ) hbound

/-- Variant of the height-`T` centered Jensen bound with an explicit center
lower bound and a uniform outer bound. -/
theorem riemannXiRotated_zeros_bound_centered_at_of_center_norm_le
    {σ T r R m M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hm : 0 < m)
    (hcenter : m ≤ ‖riemannXiRotated (riemannXiRotatedCenterAt σ T)‖)
    (hbound : ∀ z ∈ Metric.closedBall (riemannXiRotatedCenterAt σ T) R, ‖riemannXiRotated z‖ ≤ M) :
    ((Metric.closedBall (riemannXiRotatedCenterAt σ T) r ∩ {z | riemannXiRotated z = 0}).ncard : ℝ)
      ≤ Real.log (M / m) / Real.log (R / r) := by
  exact JensenZerosBound.zeros_bound_centered_of_center_norm_le hr hrR hm
    (riemannXiRotated_analyticOnNhd_univ.mono (Set.subset_univ _))
    hcenter hbound

end ZD
