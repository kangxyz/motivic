/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.Open.LinearGraph
/-! # Literal inclusion between the two polynomial opens in a moving diagram -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace Motivic.PolynomialOpenSpans
open _root_.AlgebraicGeometry.Scheme
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- The actual inclusion D(fg) into D(f). -/
def narrowInclusion (f g : k[X]) : openSite (f * g) ⟶ openSite f :=
  SmoothSite.homMk (Scheme.homOfLE (Spec (.of k[X])) (PrimeSpectrum.basicOpen_mul_le_left f g)) (by
    change Scheme.homOfLE _ _ ≫ ((principalOpen f).ι ≫ _) = _
    rw [← Category.assoc, Scheme.homOfLE_ι]
    rfl)

@[reassoc (attr := simp)] theorem narrowInclusion_comp (f g : k[X]) :
    narrowInclusion f g ≫ openInclusion f = openInclusion (f * g) := by
  apply MorphismProperty.Over.Hom.ext
  exact Scheme.homOfLE_ι _ (PrimeSpectrum.basicOpen_mul_le_left f g)

omit [Algebra.Smooth k R] in
/-- The larger boundary remains a unit on the same entire quotient. -/
theorem old_boundary_unit (p : R[X]) (f g : k[X])
    (h : IsUnit (AdjoinRoot.mk p ((f * g).map (algebraMap k R)))) :
    IsUnit (AdjoinRoot.mk p (f.map (algebraMap k R))) := by
  rw [Polynomial.map_mul, map_mul] at h
  exact (IsUnit.mul_iff.mp h).1

/-- Changing target from the smaller open to the larger one does not change the original span. -/
theorem cycle_narrowInclusion (p : R[X]) (hp : p.Monic) (f g : k[X])
    (h : IsUnit (AdjoinRoot.mk p ((f * g).map (algebraMap k R)))) :
    cycle p hp (f * g) h ≫ (Cor.graphFunctor k).map (narrowInclusion f g) =
      cycle p hp f (old_boundary_unit p f g h) := by
  let : IsOpenImmersion (openInclusion f).left := inferInstanceAs
    (IsOpenImmersion (principalOpen f).ι)
  apply Cor.comp_open_graph_injective (openInclusion f)
  dsimp only
  erw [Category.assoc, ← Functor.map_comp, narrowInclusion_comp,
    cycle_comp_inclusion, cycle_comp_inclusion]

end Motivic.PolynomialOpenSpans
