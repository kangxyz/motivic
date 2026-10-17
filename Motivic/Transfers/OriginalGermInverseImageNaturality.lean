/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermInverseImageRepresentative
public import Motivic.Transfers.PointedGermLiftGraph

/-! # Actual pullback refinements for inverse-image germ naturality -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.SmoothSite
open RelativeNisnevichNeighborhood NisnevichNeighborhood
variable {B : Scheme.{u}} {V U X : SmoothSite B}
  (f : U ⟶ X) [Etale f.left] (g : V ⟶ U) [Etale g.left] (v : V.left)

local instance : Etale (g ≫ f).left :=
  inferInstanceAs (Etale (g.left ≫ f.left))

/-- The original pointed pullback is an actual morphism of the corresponding small objects. -/
def originalSmallPullbackRefinement (M : NisnevichNeighborhood U (g.left v)) :
    smallObject (g ≫ f) v (compose (g ≫ f) v (pullbackAlong g v M)) ⟶
      smallObject f (g.left v) (compose f (g.left v) M) :=
  MorphismProperty.Over.homMk (pullback.fst M.toBase.left g.left) (by
    change pullback.fst M.toBase.left g.left ≫ (M.toBase.left ≫ f.left) =
      pullback.snd M.toBase.left g.left ≫ (g.left ≫ f.left)
    rw [← Category.assoc, pullback.condition, Category.assoc])

/-- The change of structural-map parentheses preserves the original restriction map. -/
theorem originalSmallPullbackRefinement_underlying
    (M : NisnevichNeighborhood U (g.left v)) :
    ((composeForgetIso (g ≫ f) v).app (pullbackAlong g v M)).hom ≫
        pullbackAlongToTarget g v M =
      (FiniteEtaleSite.toSmoothSite X).map (originalSmallPullbackRefinement f g v M) ≫
        ((composeForgetIso f (g.left v)).app M).hom := by
  apply MorphismProperty.Over.Hom.ext
  exact (Category.id_comp _).trans (Category.comp_id _).symm

variable {S : Scheme.{u}} (b : S ⟶ X.left)
  (q : Spec (U.left.residueField (g.left v)) ⟶ S)
  [Etale q] [IsSeparated q] [QuasiCompact q]
  (h : q ≫ b = U.left.fromSpecResidueField (g.left v) ≫ f.left)

omit [Etale f.left] [Etale g.left] [Etale q] [IsSeparated q] [QuasiCompact q] in
include h in
/-- The source factorization uses the native residue-field map, without a residue isomorphism. -/
theorem originalSourceFactorization :
    (Spec.map (g.left.residueFieldMap v) ≫ q) ≫ b =
      V.left.fromSpecResidueField v ≫ (g ≫ f).left := by
  rw [Category.assoc, h, ← Category.assoc,
    g.left.SpecMap_residueFieldMap_fromSpecResidueField]
  exact Category.assoc _ _ _

/-- The field-object arrow is exactly the original residue-field map. -/
def originalResidueFieldObjectMap :
    FiniteEtaleSite.fieldObject (V.left.residueField v)
        (Spec.map (g.left.residueFieldMap v) ≫ q) ⟶
      FiniteEtaleSite.fieldObject (U.left.residueField (g.left v)) q :=
  MorphismProperty.Over.homMk (Spec.map (g.left.residueFieldMap v)) rfl

end Motivic.SmoothSite
