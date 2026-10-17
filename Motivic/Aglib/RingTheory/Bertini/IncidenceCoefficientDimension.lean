/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.IncidenceCoefficientField
public import Motivic.Aglib.RingTheory.AlgebraicIndependent.FractionImageTrdeg

/-! # Dimension of the actual coefficient image field, without injectivity assumptions -/
@[expose] public noncomputable section
universe u
namespace IncidenceCoefficientField

/-- Passing through the actual coefficient image and taking its fraction field
cannot increase its original transcendence degree, even for a nonreduced source. -/
theorem trdeg_field_le (k A E : Type u) [Field k] [CommRing A] [Field E]
    [Algebra k A] [Algebra k E] [Algebra A E] [IsScalarTower k A E] :
    Algebra.trdeg k (field k A E) ≤ Algebra.trdeg k A := by
  let := imageAlgebra k A E
  have : Algebra.IsAlgebraic (image k A E) (field k A E) :=
    IsLocalization.isAlgebraic (field k A E) (nonZeroDivisors (image k A E))
  have he : Algebra.trdeg k (field k A E) = Algebra.trdeg k (image k A E) := by
    simpa only [trdeg_eq_zero, add_zero] using
      (trdeg_add_eq k (image k A E) (A := field k A E)).symm
  rw [he]
  exact trdeg_le_of_surjective (imageMap k A E) (imageMap_surjective k A E)

end IncidenceCoefficientField
