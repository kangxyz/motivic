/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.OpenRestriction
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.Relative.LinearGraph
/-! # Literal inclusion between the two polynomial opens in a moving diagram -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra.Smooth k R] [Algebra R A] [Algebra k A]
    [IsScalarTower k R A] [Algebra.Smooth k A]

/-- Changing target from the smaller open to the larger one does not change the original span. -/
theorem cycle_narrowInclusion (p : A[X]) (hp : p.Monic) (f g : R[X])
    (h : IsUnit (AdjoinRoot.mk p ((f * g).map (algebraMap R A)))) :
    cycle (k := k) p hp (f * g) h ≫ (_root_.Motivic.Cor.graphFunctor k).map (narrowInclusion (k
        := k) f g) =
      cycle (k := k) p hp f (old_boundary_unit p f g h) := by
  let : IsOpenImmersion (openInclusion (k := k) f).left := inferInstanceAs
    (IsOpenImmersion (principalOpen f).ι)
  apply _root_.Motivic.Cor.comp_open_graph_injective (openInclusion (k := k) f)
  dsimp only
  erw [Category.assoc, ← Functor.map_comp, narrowInclusion_comp,
    cycle_comp_inclusion, cycle_comp_inclusion]

end AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
