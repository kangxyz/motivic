/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Germs.InverseImageRestriction

/-! # The genuine inverse-image comparison preserves original germ pullback -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.Scheme.SmoothSite.RelativeNisnevichNeighborhood
open _root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood
variable {B : Scheme.{u}} [IsAffine B] {V U X : SmoothSite B}
  (F : Sheaf (nisnevichTopology B) AddCommGrpCat.{u + 1})
  (f : U ⟶ X) [Etale f.left] (g : V ⟶ U) [Etale g.left] (v : V.left)
  {S : Scheme.{u}} (b : S ⟶ X.left)
  (q : Spec (U.left.residueField (g.left v)) ⟶ S)
  [Etale q] [IsSeparated q] [QuasiCompact q]
  (h : q ≫ b = U.left.fromSpecResidueField (g.left v) ≫ f.left)
local instance : Etale (g ≫ f).left :=
  inferInstanceAs (Etale (g.left ≫ f.left))

/-- The original point-fiber pullback corresponds to literal inverse-image restriction
along the native residue-field map. No compatibility law is supplied as a hypothesis. -/
@[reassoc]
theorem originalGermInverseImageOfFactorization_pullback :
    originalGermPullback.{u, u + 1} F.obj g v ≫
      (originalGermInverseImageOfFactorization F (g ≫ f) v b
        (Spec.map (g.left.residueFieldMap v) ≫ q)
        (originalSourceFactorization f g v b q h)).hom =
    (originalGermInverseImageOfFactorization F f (g.left v) b q h).hom ≫
      ((EtaleSeparatedFiniteType.inverseImage b).obj
        ((EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj F)).obj.map
          (originalResidueFieldObjectMap g v q).op := by
  apply (isColimitNisnevichPointFiberCocone U (g.left v) F.obj).hom_ext
  intro M
  rw [originalGermPullback_ι_assoc,
    originalGermInverseImageOfFactorization_ι,
    originalGermInverseImageOfFactorization_ι_assoc]
  let d := originalSmallPullbackRefinement f g v M.unop
  let G := (EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj F
  let H := (EtaleSeparatedFiniteType.inverseImage b).obj G
  have hd := congrArg (fun a => F.obj.map a.op)
    (originalSmallPullbackRefinement_underlying f g v M.unop)
  simp only [op_comp, F.obj.map_comp] at hd
  rw [← Category.assoc, ← Category.assoc, hd]
  rw [Category.assoc, Category.assoc]
  congr 1
  have hn := ((EtaleSeparatedFiniteType.imageAdjunction b).unit.app G).hom.naturality d.op
  change G.obj.map d.op ≫ _ = _ at hn
  rw [← Category.assoc]
  erw [hn]
  rw [Category.assoc]
  congr 1
  change H.obj.map ((EtaleSeparatedFiniteType.baseChange b).map d).op ≫ H.obj.map _ =
    H.obj.map _ ≫ H.obj.map _
  rw [← H.obj.map_comp, ← H.obj.map_comp, ← op_comp, ← op_comp]
  exact congrArg (fun a => H.obj.map a.op)
    (originalSmallMark_lift_naturality f g v b q h M.unop)

end AlgebraicGeometry.Scheme.SmoothSite
