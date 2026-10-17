module
public import Mathlib.RingTheory.QuasiFinite.Polynomial
public import Mathlib.RingTheory.Algebraic.Basic

/-! # Quasi-finite domain algebras are algebraic

The generic-point polynomial kernel criterion gives algebraicity directly,
without fraction fields or assumptions that the structure map is injective.
-/
@[expose] public noncomputable section

namespace Algebra.QuasiFinite

/-- A quasi-finite algebra which is a domain is algebraic over its base. -/
theorem isAlgebraic_of_isDomain
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
    [QuasiFinite A B] : Algebra.IsAlgebraic A B := by
  refine ⟨fun b => isAlgebraic_iff_not_injective.mpr ?_⟩
  rw [RingHom.injective_iff_ker_eq_bot]
  have h := Polynomial.map_under_lt_comap_of_quasiFiniteAt
    (Polynomial.aeval (R := A) b) (⊥ : Ideal B)
  exact ne_of_gt (lt_of_le_of_lt bot_le h)

end Algebra.QuasiFinite
