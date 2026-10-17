module
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-! # Literal coefficient rings for normalized moving-point incidence charts

The free variables are precisely the other entries of a normalized left kernel.
The original nonzero coordinate difference is inverted, so every field-valued
point of the chart remains off the selected point.
-/
@[expose] public noncomputable section
namespace QuadraticIncidence
namespace MovingPointChart
universe u
variable (B : Type u) [CommRing B] (d : ℕ) (i₀ : Fin d)

/-- The remaining left-kernel coordinates, with the distinguished entry removed. -/
abbrev WeightIndex := {i : Fin d // i ≠ i₀}

/-- The unlocalized normalized-weight parameter ring. -/
abbrev PolynomialRing := MvPolynomial (WeightIndex d i₀) B

/-- The actual coefficient chart off the original coordinate difference `t`. -/
abbrev Ring (t : B) := Localization.Away
  (MvPolynomial.C t : PolynomialRing B d i₀)

/-- The distinguished kernel coordinate is literally one; all others are variables. -/
def weight (t : B) (i : Fin d) : Ring B d i₀ t :=
  if h : i = i₀ then 1 else
    algebraMap (PolynomialRing B d i₀) (Ring B d i₀ t) (MvPolynomial.X ⟨i, h⟩)

@[simp]
theorem weight_distinguished (t : B) : weight B d i₀ t i₀ = 1 := by
  simp [weight]

/-- The original coordinate difference is a unit on the entire chart. -/
theorem difference_isUnit (t : B) :
    IsUnit (algebraMap B (Ring B d i₀ t) t) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := Ring B d i₀ t) (MvPolynomial.C t : PolynomialRing B d i₀)
  exact h

/-- No field-valued chart point can return to the deleted diagonal. -/
theorem difference_ne_zero (t : B) (K : Type u) [Field K]
    [Algebra B K] [Algebra (Ring B d i₀ t) K]
    [IsScalarTower B (Ring B d i₀ t) K] : algebraMap B K t ≠ 0 := by
  have h := (difference_isUnit B d i₀ t).map (algebraMap (Ring B d i₀ t) K)
  rw [← IsScalarTower.algebraMap_apply B (Ring B d i₀ t) K] at h
  exact h.ne_zero

end MovingPointChart
end QuadraticIncidence
