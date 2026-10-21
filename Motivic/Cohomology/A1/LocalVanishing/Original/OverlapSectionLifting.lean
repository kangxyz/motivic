/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.WholeBase.Target
public import Motivic.Cohomology.A1.LocalVanishing.RelativeCurve.LocalLifting
/-! # The retained target restricts the original overlap, not its coefficient sheaf -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic ProjectiveSpace
open Scheme.Hom Opposite
universe u
namespace AlgebraicGeometry.Scheme.Hom
/-- The smoothness instance used in this module. -/
local instance overlapSectionLiftingSmooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
variable (k : Type u) [Field k] (R : Type u) [CommRing R] (ι : Type u)
  {X Y A C : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine A]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 q]
  (p : Y ⟶ X) [Etale p] (a : A ⟶ X) [IsOpenImmersion a]
  (f : C ⟶ ProjectiveSpace R ι) (j : Y ⟶ C)
  (hj : j ≫ (f ≫ toSpec R ι) = p ≫ q)
  (U : X.Opens) (V : (Spec (.of R)).Opens)
  [IsAffine V.toScheme] [IsAffine (boundaryBaseSourceOpen q U V).toScheme]
  [SmoothOfRelativeDimension 1 ((pullback.fst p a ≫ j) ≫ (f ≫ toSpec R ι))]

/-- The actual pencil lift restricts original overlap sections; the auxiliary base
presentation does not replace the coefficient presheaf or original overlap. -/
theorem originalOverlap_hasRestrictionDifferenceLifting
    (P : PresheafWithTransfers.{u + 1} k)
    (hL : PresheafWithTransfers.HasRestrictionDifferenceLifting P
      (boundaryBasePencilGraph k R ι t q p a f j hj U V (pullback.fst p a ≫ j)
        (𝟙 _) (Category.id_comp _))
      (boundaryBasePencilBeta k R ι t q p a f j hj U V)
      (boundaryBasePencilAlpha k R ι t q p a f j hj U V)) :
    PresheafWithTransfers.HasRestrictionDifferenceLifting P
      (boundaryBaseOverlapRestriction k R ι t q p a f j hj U V)
      (boundaryBasePencilBeta k R ι t q p a f j hj U V)
      (boundaryBasePencilAlpha k R ι t q p a f j hj U V) := by
  intro d
  let i := boundaryBaseOriginalOverlapTargetRestriction k R ι t q p a f j hj V
  obtain ⟨b, c, hbc⟩ := hL (((PresheafWithTransfers.toPresheaf k).obj P).map i.op d)
  refine ⟨b, c, ?_⟩
  rw [← boundaryBaseOriginalOverlapTargetRestriction_graph k R ι t q p a f j hj U V,
    op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  exact hbc

end AlgebraicGeometry.Scheme.Hom
