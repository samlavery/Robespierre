import RequestProject.DoubleCoshValidation
import RequestProject.CoshZetaSymmetry

/-!
# Cosh–Zeta Intertwiner

The algebraically-exact bridge between the zeta side (`riemannZeta`,
`NontrivialZeros`, the FE reflection `s ↦ 1 − s`, complex conjugation
`s ↦ s̄`) and the cosh side (real offsets `β`, the real reflection
`β ↦ 1 − β`).

## Naming discipline

* **`Intertwiner`** — the algebraically exact bridge. A map `Φ` commuting
  with *both* generators of the zero symmetry group:
    `Φ ∘ R_ζ   = R_cosh   ∘ Φ`     (FE reflection)
    `Φ ∘ F_ζ   = F_cosh   ∘ Φ`     (complex conjugation)
* **`transport_*`** — geometric consequence: π/6 geometry carried to
  critical-line geometry at 1/2.
* **`transfer_*`** — one-way downstream corollary: property on one side
  *implies* property on the other, without committing to the exact bridge.

## Canonical instance

`canonicalIntertwiner` uses:
* `Φ s := s.re` (real-part projection)
* `R_ζ s := 1 − s`, `R_cosh β := 1 − β` (FE reflection)
* `F_ζ s := star s` (complex conjugation), `F_cosh β := β` (β real is fixed)

Both intertwining equations reduce to trivial real-arithmetic identities;
the content is that the zeta-side group action on zeros is faithfully
recorded by `ρ.re`, and that the classifier `R_double` respects this action.
-/

open Real ZetaDefs DoubleCoshResidue DoubleCoshValidation

noncomputable section

namespace CoshZeta

/-! ### §1. The intertwiner structure -/

/-- The algebraically exact bridge: a map `Φ : ℂ → ℝ` commuting with both
generators of the zero symmetry group. `R` is the FE reflection; `F` is
complex conjugation. The two actions generate `Z/2 × Z/2`, and `Φ` is a
`Z/2 × Z/2`-equivariant map. -/
structure Intertwiner where
  /-- Projection from the zeta side to the cosh side. -/
  Φ : ℂ → ℝ
  /-- Reflection on the zeta side (FE action). -/
  R_ζ : ℂ → ℂ
  /-- Reflection on the cosh side. -/
  R_cosh : ℝ → ℝ
  /-- Conjugation on the zeta side. -/
  F_ζ : ℂ → ℂ
  /-- Conjugation on the cosh side. -/
  F_cosh : ℝ → ℝ
  /-- **Reflection intertwining**: `Φ ∘ R_ζ = R_cosh ∘ Φ`. -/
  intertwines_R : ∀ s : ℂ, Φ (R_ζ s) = R_cosh (Φ s)
  /-- **Conjugation intertwining**: `Φ ∘ F_ζ = F_cosh ∘ Φ`. -/
  intertwines_F : ∀ s : ℂ, Φ (F_ζ s) = F_cosh (Φ s)

/-! ### §2. The canonical instance -/

/-- The canonical cosh–zeta intertwiner.
Real-part projection; FE reflection on ℂ paired with reflection β ↦ 1−β on ℝ;
complex conjugation on ℂ paired with the identity on ℝ. -/
def canonicalIntertwiner : Intertwiner where
  Φ s := s.re
  R_ζ s := 1 - s
  R_cosh β := 1 - β
  F_ζ s := star s
  F_cosh β := β
  intertwines_R s := by simp
  intertwines_F s := by simp

@[simp] theorem canonical_Φ (s : ℂ) : canonicalIntertwiner.Φ s = s.re := rfl
@[simp] theorem canonical_R_ζ (s : ℂ) : canonicalIntertwiner.R_ζ s = 1 - s := rfl
@[simp] theorem canonical_R_cosh (β : ℝ) : canonicalIntertwiner.R_cosh β = 1 - β := rfl
@[simp] theorem canonical_F_ζ (s : ℂ) : canonicalIntertwiner.F_ζ s = star s := rfl
@[simp] theorem canonical_F_cosh (β : ℝ) : canonicalIntertwiner.F_cosh β = β := rfl

/-! ### §3. Zero-set closure under the intertwiner actions -/

/-- The zeta-side FE reflection preserves `NontrivialZeros`: if
`ρ ∈ NontrivialZeros`, so is `1 − ρ`. -/
theorem R_ζ_preserves_zeros (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    canonicalIntertwiner.R_ζ ρ ∈ ZD.NontrivialZeros := by
  simp only [canonical_R_ζ]
  have hz : riemannZeta ρ = 0 := hρ.2.2
  have hne_neg : ∀ n : ℕ, ρ ≠ -(↑n : ℂ) := by
    intro n hn
    have := congr_arg Complex.re hn
    simp at this; linarith [hρ.1]
  have hne_one : ρ ≠ 1 := by
    intro h; have h1 := hρ.2.1; rw [h, Complex.one_re] at h1; linarith
  have hfe : riemannZeta (1 - ρ) = 0 := by
    rw [riemannZeta_one_sub hne_neg hne_one, hz, mul_zero]
  refine ⟨?_, ?_, hfe⟩
  · simp; linarith [hρ.2.1]
  · simp; linarith [hρ.1]

/-- The zeta-side conjugation preserves `NontrivialZeros`, via
`CoshZetaSymmetry.riemannZeta_conj`. -/
theorem F_ζ_preserves_zeros (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    canonicalIntertwiner.F_ζ ρ ∈ ZD.NontrivialZeros := by
  simp only [canonical_F_ζ]
  have hne_one : ρ ≠ 1 := by
    intro h
    have h1 := hρ.2.1
    rw [h, Complex.one_re] at h1
    linarith
  refine ⟨?_, ?_, ?_⟩
  · show 0 < (starRingEnd ℂ ρ).re
    simp; exact hρ.1
  · show (starRingEnd ℂ ρ).re < 1
    simp; exact hρ.2.1
  · show riemannZeta (starRingEnd ℂ ρ) = 0
    rw [CoshZetaSymmetry.riemannZeta_conj ρ hne_one, hρ.2.2, map_zero]

/-! ### §4. Transport to the critical line -/

/-- The cosh-side critical set: fixed points of `R_cosh`. For the canonical
intertwiner, this is `{1/2}`. -/
def coshCriticalSet (I : Intertwiner) : Set ℝ := {β | I.R_cosh β = β}

/-- For the canonical intertwiner, the cosh-side critical set is exactly
`{1/2}`. -/
theorem canonical_coshCriticalSet :
    coshCriticalSet canonicalIntertwiner = {(1:ℝ)/2} := by
  ext β
  simp only [coshCriticalSet, Set.mem_setOf_eq, canonical_R_cosh, Set.mem_singleton_iff]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Transport to the critical line**: the π/6-anchored cosh geometry
(whose distinguished fixed point is β = 1/2 under R_cosh) is carried by
`Φ` to the zeta-side critical-line condition. Fixed points of `R_cosh`
on `Φ`'s image correspond to `OnLineZeros`. -/
theorem transport_to_critical_line (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    canonicalIntertwiner.Φ ρ ∈ coshCriticalSet canonicalIntertwiner ↔
    ρ ∈ ZD.OnLineZeros := by
  simp only [coshCriticalSet, Set.mem_setOf_eq, canonical_R_cosh, canonical_Φ]
  refine ⟨fun h => ⟨hρ, by linarith⟩, fun hon => by linarith [hon.2]⟩

/-! ### §5. Transfer corollaries -/

/-- **Transfer of balance (cosh → zeta)**: classifier balance on the
cosh-side image forces on-line membership on the zeta side. -/
theorem transfer_balance (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros)
    {r : ℝ} (hr : 1 < r)
    (hbal : pairAgreementDefect r (canonicalIntertwiner.Φ ρ) = 0) :
    ρ ∈ ZD.OnLineZeros := by
  simp only [canonical_Φ] at hbal
  exact classifier_balanced_implies_online ρ hρ hr hbal

/-- **Transfer of zero-residue (zeta → cosh)**: on-line membership on the
zeta side forces classifier balance on the cosh-side image, at every scale. -/
theorem transfer_zero_residue (ρ : ℂ) (hρ : ρ ∈ ZD.OnLineZeros) (r : ℝ) :
    pairAgreementDefect r (canonicalIntertwiner.Φ ρ) = 0 := by
  simp only [canonical_Φ]
  exact online_zero_residue_zero ρ hρ r

/-- **Transfer of residue-positivity (zeta → cosh)**: off-line membership
on the zeta side forces strictly positive classifier residue on the
cosh-side image, at every admissible scale. -/
theorem transfer_residue_positive (ρ : ℂ) (hρ : ρ ∈ ZD.OffLineZeros)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    0 < pairAgreementDefect r (canonicalIntertwiner.Φ ρ) := by
  simp only [canonical_Φ]
  exact offline_zeros_read_unbalanced ρ hρ hr hr1

/-- **Transfer biconditional**: zeta-side on-line membership ↔ cosh-side
balance (at any admissible scale). The single compressed statement. -/
theorem transfer_iff (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros)
    {r : ℝ} (hr : 1 < r) :
    ρ ∈ ZD.OnLineZeros ↔
    pairAgreementDefect r (canonicalIntertwiner.Φ ρ) = 0 := by
  simp only [canonical_Φ]
  exact rho_online_iff_residue_zero ρ hρ hr

/-! ### §6. Intertwining applied to the zero set -/

/-- **FE intertwining on zeros**: if `ρ` is a nontrivial zero, the
FE-reflected `R_ζ ρ` is also a nontrivial zero, and its Φ-image is
`R_cosh (Φ ρ)`. This is the intertwining equation specialized to zeros. -/
theorem intertwines_R_on_zeros (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    canonicalIntertwiner.R_ζ ρ ∈ ZD.NontrivialZeros ∧
    canonicalIntertwiner.Φ (canonicalIntertwiner.R_ζ ρ) =
      canonicalIntertwiner.R_cosh (canonicalIntertwiner.Φ ρ) :=
  ⟨R_ζ_preserves_zeros ρ hρ, canonicalIntertwiner.intertwines_R ρ⟩

/-- **Conjugation intertwining on zeros**: conjugation preserves
`NontrivialZeros` and `Φ` is invariant under it. -/
theorem intertwines_F_on_zeros (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) :
    canonicalIntertwiner.F_ζ ρ ∈ ZD.NontrivialZeros ∧
    canonicalIntertwiner.Φ (canonicalIntertwiner.F_ζ ρ) =
      canonicalIntertwiner.F_cosh (canonicalIntertwiner.Φ ρ) :=
  ⟨F_ζ_preserves_zeros ρ hρ, canonicalIntertwiner.intertwines_F ρ⟩

/-! ### §7. Axiom hygiene -/

#print axioms canonicalIntertwiner
#print axioms R_ζ_preserves_zeros
#print axioms F_ζ_preserves_zeros
#print axioms canonical_coshCriticalSet
#print axioms transport_to_critical_line
#print axioms transfer_balance
#print axioms transfer_zero_residue
#print axioms transfer_residue_positive
#print axioms transfer_iff
#print axioms intertwines_R_on_zeros
#print axioms intertwines_F_on_zeros

end CoshZeta

end
