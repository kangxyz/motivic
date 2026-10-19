/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOrdinaryEdgeMap
public import Motivic.Cohomology.A1.BoundaryEtaleLocalization
public import Motivic.Aglib.CategoryTheory.Sites.RestrictionSourceComposition

/-! # Actual free-source coherence for geometric inverse-image composition -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite
variable {R S T : Scheme.{u}} (f : R ⟶ T) (g : T ⟶ S)

/-- The actual free-source maps commute with the actual inverse-image
composition and the original iterated scheme pullback isomorphism. -/
theorem inverseImageSourceIso_comp (V : FiniteEtaleSite S) :
    (inverseImage f).map (inverseImageSourceIso g V).hom ≫
      (inverseImageSourceIso f ((baseChange g).obj V)).hom ≫
        (Hypercohomology.freeAbelianSheafFunctor (nisnevichTopology R)).map
          ((MorphismProperty.Over.pullbackComp
            (P := etaleSeparatedFiniteType) (Q := ⊤) f g).inv.app V) =
    (inverseImageCompIso f g).hom.app
        (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1} (nisnevichTopology S) V) ≫
      (inverseImageSourceIso (f ≫ g) V).hom := by
  exact Hypercohomology.restrictionSourceIso_comp
    (nisnevichTopology S) (nisnevichTopology T) (nisnevichTopology R)
    (baseChange g) (baseChange f) (baseChange (f ≫ g))
    (MorphismProperty.Over.pullbackComp
      (P := etaleSeparatedFiniteType) (Q := ⊤) f g).symm V

end Motivic.FiniteEtaleSite
