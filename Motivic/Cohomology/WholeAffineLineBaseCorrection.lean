/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.WholeAffineLineBaseTarget
/-! # The retained target restricts the original overlap, not its coefficient sheaf -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic ProjectiveSpace
open Scheme.Hom Opposite
open Motivic.SheafCohomology
universe w u
namespace AlgebraicGeometry.Scheme.Hom
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
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


variable
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Consume the genuine base-only difference lifting on the retained target.
The overlap section is the discrepancy of the original class, restricted along
its actual inclusion into the original overlap. -/
theorem h_one_boundaryBase_restriction_eq_zero
    (F : SheafWithTransfers.{u + 1} k)
    (hL : PresheafWithTransfers.HasRestrictionDifferenceLifting F.obj
      (boundaryBasePencilGraph k R ι t q p a f j hj U V (pullback.fst p a ≫ j)
        (𝟙 _) (Category.id_comp _))
      (boundaryBasePencilBeta k R ι t q p a f j hj U V)
      (boundaryBasePencilAlpha k R ι t q p a f j hj U V))
    {Z : Scheme.{u}} (z : Z ⟶ (boundaryBaseSourceOpen q U V).toScheme)
    [IsClosedImmersion z]
    (hcomp : Set.range z = (Set.range (boundaryBaseCoverMap q a U V))ᶜ)
    [IsIso (pullback.snd (boundaryBaseCoverMap q p U V) z)]
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1 (originalAmbientSite k R t q))
    (hA : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1).map (originalOpenArrow k R t q a).op x = 0)
    (hY : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1).map (originalEtaleArrow k R t q p).op x = 0) :
    (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1).map
        (boundaryBaseAmbientRestriction k R t q U V).op x = 0 := by
  let : IsOpenImmersion
      (boundaryBasePencilSquare k R ι t q p a f j hj U V).f₂₄.left := by
    change IsOpenImmersion (a ∣_ boundaryBaseSourceOpen q U V)
    infer_instance
  let : Etale (boundaryBasePencilSquare k R ι t q p a f j hj U V).f₃₄.left := by
    change Etale (p ∣_ boundaryBaseSourceOpen q U V)
    infer_instance
  let : IsIso (pullback.snd
      (boundaryBasePencilSquare k R ι t q p a f j hj U V).f₃₄.left z) :=
    inferInstanceAs (IsIso (pullback.snd (boundaryBaseCoverMap q p U V) z))
  apply h_one_restriction_eq_zero_of_square_difference_lifting
    ((SheafWithTransfers.toSheaf k).obj F) (originalBoundarySquare k R t q p a)
    (boundaryBasePencilSquare k R ι t q p a f j hj U V)
    (boundaryBasePencilSquare_isPullback k R ι t q p a f j hj U V)
    (boundaryBaseOverlapRestriction k R ι t q p a f j hj U V)
    (boundaryBaseOpenRestriction k R t q a U V)
    (boundaryBaseEtaleRestriction k R ι t q p f j hj U V)
    (boundaryBaseAmbientRestriction k R t q U V)
    (boundaryBaseOverlapRestriction_open k R ι t q p a f j hj U V)
    (boundaryBaseOverlapRestriction_etale k R ι t q p a f j hj U V)
    (boundaryBaseOpenRestriction_ambient k R t q a U V)
    (boundaryBaseEtaleRestriction_ambient k R ι t q p f j hj U V)
    z hcomp _ x hA hY
  intro d
  let i := boundaryBaseOriginalOverlapTargetRestriction k R ι t q p a f j hj V
  obtain ⟨b, c, hbc⟩ := hL (((SheafWithTransfers.toSheaf k).obj F).obj.map i.op d)
  refine ⟨b, c, ?_⟩
  rw [← boundaryBaseOriginalOverlapTargetRestriction_graph k R ι t q p a f j hj U V,
    op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  exact hbc

end AlgebraicGeometry.Scheme.Hom
