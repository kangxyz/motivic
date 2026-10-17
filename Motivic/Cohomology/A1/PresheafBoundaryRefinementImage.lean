/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.PresheafBoundaryLaurentImage

/-! # A literal signed lift on an étale refinement belongs to the canonical image sieve -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite.OriginalPresheaf
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (P : PresheafWithTransfers.{u + 1} k)
/-- The ambient correction is killed in the original quotient. A refinement whose
zero section is the actual prescribed lift therefore gives a canonical Laurent image. -/
theorem imageSieve_of_refinement_difference
    {W W' : FiniteEtaleSite (SmoothSite.a1Cylinder (.of k) X).left}
    (V : FiniteEtaleSite X.left) (f : W' ⟶ W)
    (b : W' ⟶ (cylinderNeighborhood X).obj V)
    (z : V ⟶ (baseChange
      (SmoothSite.a1Section (.of k) X 0).left).obj W')
    (hz : z ≫ (baseChange
      (SmoothSite.a1Section (.of k) X 0).left).map b = zeroNeighborhoodLift X V)
    (s : ((baseChange
      (SmoothSite.contractionOpen (.of k) X).left).op ⋙
      (toSmoothSite (SmoothSite.torusCylinder (.of k) X)).op ⋙
      (PresheafWithTransfers.toPresheaf k).obj P).obj (op W))
    (a : ((toSmoothSite X).op ⋙
      (PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.torusSections P)).obj (op V))
    (c : ((toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).op ⋙
      (PresheafWithTransfers.toPresheaf k).obj P).obj (op W'))
    (h : ((baseChange
      (SmoothSite.contractionOpen (.of k) X).left).op ⋙
      (toSmoothSite (SmoothSite.torusCylinder (.of k) X)).op ⋙
      (PresheafWithTransfers.toPresheaf k).obj P).map b.op ((laurentToPunctured X P).app (op V) a) -
      (presheafBoundaryRestriction ((PresheafWithTransfers.toPresheaf k).obj P)
      (SmoothSite.contractionOpen (.of k) X)).app (op W') c =
      ((baseChange
      (SmoothSite.contractionOpen (.of k) X).left).op ⋙
      (toSmoothSite (SmoothSite.torusCylinder (.of k) X)).op ⋙
      (PresheafWithTransfers.toPresheaf k).obj P).map f.op s) :
    Presheaf.imageSieve (contractionToBoundary X P).hom
      ((presheafBoundaryGenerator ((PresheafWithTransfers.toPresheaf k).obj P)
      (SmoothSite.contractionOpen (.of k) X)
      (SmoothSite.a1Section (.of k) X 0)).app (op W) s)
      (z ≫ (baseChange
      (SmoothSite.a1Section (.of k) X 0).left).map f) := by
  obtain ⟨a', ha'⟩ := laurent_boundary_mem_image X P V a
  refine ⟨a', ha'.trans ?_⟩
  have hf := presheafBoundaryGenerator_of_difference
    ((PresheafWithTransfers.toPresheaf k).obj P)
      (SmoothSite.contractionOpen (.of k) X)
      (SmoothSite.a1Section (.of k) X 0)
    f s (((baseChange
      (SmoothSite.contractionOpen (.of k) X).left).op ⋙
      (toSmoothSite (SmoothSite.torusCylinder (.of k) X)).op ⋙
      (PresheafWithTransfers.toPresheaf k).obj P).map b.op
        ((laurentToPunctured X P).app (op V) a)) c h
  have hb := ConcreteCategory.congr_hom
    ((presheafBoundaryGenerator ((PresheafWithTransfers.toPresheaf k).obj P)
      (SmoothSite.contractionOpen (.of k) X)
      (SmoothSite.a1Section (.of k) X 0)).naturality b.op)
    ((laurentToPunctured X P).app (op V) a)
  have he := congrArg ((zeroSectionBoundary X P).obj.map z.op) (hb.symm.trans hf)
  have hc := ConcreteCategory.congr_hom
    (congr_app (laurent_generator_formula X P) (op V)) a
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hc
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hc
  have hm := congrArg (fun q => (zeroSectionBoundary X P).obj.map q.op) hz
  rw [op_comp, (zeroSectionBoundary X P).obj.map_comp] at hm
  have hm' := ConcreteCategory.congr_hom hm
    ((presheafBoundaryGenerator ((PresheafWithTransfers.toPresheaf k).obj P)
      (SmoothSite.contractionOpen (.of k) X)
      (SmoothSite.a1Section (.of k) X 0)).app (op ((cylinderNeighborhood X).obj V))
      ((laurentToPunctured X P).app (op V) a))
  exact hc.trans (hm'.symm.trans (he.trans
    (ConcreteCategory.congr_hom ((zeroSectionBoundary X P).obj.map_comp ((baseChange
      (SmoothSite.a1Section (.of k) X 0).left).map f).op z.op)
      ((presheafBoundaryGenerator ((PresheafWithTransfers.toPresheaf k).obj P)
      (SmoothSite.contractionOpen (.of k) X)
      (SmoothSite.a1Section (.of k) X 0)).app (op W) s)).symm))

end Motivic.FiniteEtaleSite.OriginalPresheaf
