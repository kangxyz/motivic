/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Boundary.Contraction.Sheaf
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.Marked.ResidueGerms
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.CokernelLifting
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.InverseImageUnit

/-! # A zero canonical boundary has an actual pointed ambient extension -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k)

/-- An original Laurent representative with zero canonical boundary extends on
an actual pointed ambient étale refinement. Neither generic detection nor purity
is assumed; the sheaf cokernel and closed inverse-image unit remain unchanged. -/
theorem exists_pointed_extension_of_laurent_boundary_zero
    (V : EtaleSeparatedFiniteType X.left) (v : V.left)
    (s : (((toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.torusSections F.obj)).obj (op V)))
    (hs : (ambientCokernelToBoundary X F).app (op V)
      ((laurentToAmbientCokernel X F).app (op V) s) = 0) :
    ∃ (E : EtaleSeparatedFiniteType (SmoothSite.a1Cylinder (.of k) X).left)
      (f : E ⟶ (cylinderNeighborhood X).obj V)
      (e : (markedResiduePoint V v).fiber.obj
        ((baseChange (SmoothSite.a1Section (.of k) X 0).left).obj E))
      (t : ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat).obj
        ((SheafWithTransfers.toSheaf k).obj F)).obj.obj (op E)),
      (markedResiduePoint V v).fiber.map
        ((baseChange (SmoothSite.a1Section (.of k) X 0).left).map f) e =
        (markedResiduePoint V v).fiber.map (zeroNeighborhoodLift X V)
          (markedResidueElement V v) ∧
      (restrictionToDirectImage ((SheafWithTransfers.toSheaf k).obj F)
        (SmoothSite.contractionOpen (.of k) X)).hom.app (op E) t =
      ((directImage (SmoothSite.contractionOpen (.of k) X).left).obj
        ((restrict (SmoothSite.torusCylinder (.of k) X) AddCommGrpCat).obj
          ((SheafWithTransfers.toSheaf k).obj F))).obj.map f.op
        (((SheafWithTransfers.toSheaf k).obj F).obj.map (puncturedProjection X V).op s) := by
  let i := (SmoothSite.a1Section (.of k) X 0).left
  let Φ := markedResiduePoint V v
  let : InitiallySmall.{u + 1} (baseChange i ⋙ Φ.fiber).Elements :=
    initiallySmall_of_essentiallySmall _
  let x := Φ.fiber.map (zeroNeighborhoodLift X V) (markedResidueElement V v)
  let r := restrictionToDirectImage ((SheafWithTransfers.toSheaf k).obj F)
    (SmoothSite.contractionOpen (.of k) X)
  let Q := cokernel r
  let a := ((SheafWithTransfers.toSheaf k).obj F).obj.map (puncturedProjection X V).op s
  let c := (cokernel.π r).hom.app (op ((cylinderNeighborhood X).obj V)) a
  have h : Φ.toPresheafFiber ((zeroNeighborhood X).obj V) x ((inverseImage i).obj Q).obj
      (((imageAdjunction i).unit.app Q).hom.app (op ((cylinderNeighborhood X).obj V)) c) = 0 := by
    rw [← Φ.toPresheafFiber_w_apply]
    have hs' : ((inverseImage i).obj Q).obj.map (zeroNeighborhoodLift X V).op
        (((imageAdjunction i).unit.app Q).hom.app (op ((cylinderNeighborhood X).obj V)) c) = 0 := hs
    rw [hs', map_zero]
  have hz := comap_germ_eq_zero_of_inverseImage_unit_germ_eq_zero i Φ Q
    ((cylinderNeighborhood X).obj V) x c h
  exact exists_pointed_local_lift_of_cokernel_germ_zero
    (Φ.comap (baseChange i) (CoverPreserving.of_isContinuous (baseChange i) _ _))
    r ((cylinderNeighborhood X).obj V) x a hz

end Motivic.FiniteEtaleSite
