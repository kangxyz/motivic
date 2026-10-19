/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Germs.InverseImageNaturality

/-! # Literal residue restrictions and original pointed pullbacks -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.Scheme.SmoothSite.RelativeNisnevichNeighborhood
open _root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood
variable {B : Scheme.{u}} {V U X : SmoothSite B}
  (f : U ⟶ X) [Etale f.left] (g : V ⟶ U) [Etale g.left] (v : V.left)
  {S : Scheme.{u}} (b : S ⟶ X.left)
  (q : Spec (U.left.residueField (g.left v)) ⟶ S)
  [Etale q] [IsSeparated q] [QuasiCompact q]
  (h : q ≫ b = U.left.fromSpecResidueField (g.left v) ≫ f.left)
local instance : Etale (g ≫ f).left :=
  inferInstanceAs (Etale (g.left ≫ f.left))

/-- Actual field-point pullback lifts commute with the original neighborhood refinement. -/
theorem originalSmallMark_lift_naturality (M : NisnevichNeighborhood U (g.left v)) :
    (EtaleSeparatedFiniteType.fieldPointLiftEquiv b (V.left.residueField v)
      (Spec.map (g.left.residueFieldMap v) ≫ q)
      (RelativeNisnevichNeighborhood.smallObject (g ≫ f) v (RelativeNisnevichNeighborhood.compose (g
          ≫ f) v (NisnevichNeighborhood.pullbackAlong g v M)))).symm
        (originalSmallMark (g ≫ f) v b _ (originalSourceFactorization f g v b q h)
          (NisnevichNeighborhood.pullbackAlong g v M)) ≫
      (EtaleSeparatedFiniteType.baseChange b).map (originalSmallPullbackRefinement f g v M) =
    originalResidueFieldObjectMap g v q ≫
      (EtaleSeparatedFiniteType.fieldPointLiftEquiv b (U.left.residueField (g.left v)) q
        (RelativeNisnevichNeighborhood.smallObject f (g.left v)
            (RelativeNisnevichNeighborhood.compose f (g.left v) M))).symm
          (originalSmallMark f (g.left v) b q h M) := by
  apply MorphismProperty.Over.Hom.ext
  dsimp [EtaleSeparatedFiniteType.fieldPointLiftEquiv, originalSmallMark,
    originalResidueFieldObjectMap, originalSmallPullbackRefinement,
    EtaleSeparatedFiniteType.baseChange, MorphismProperty.Over.pullback]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    change NisnevichNeighborhood.pullbackAlongPoint g v M ≫ pullback.fst M.toBase.left g.left = _
    exact pullback.lift_fst _ _ _
  · simp only [Category.assoc, pullback.lift_snd]

end AlgebraicGeometry.Scheme.SmoothSite
