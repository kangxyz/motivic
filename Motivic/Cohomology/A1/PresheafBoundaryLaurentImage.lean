/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.PresheafBoundaryLiftingRelation

/-! # Original Laurent sections give elements in the canonical sheaf-map image -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite.OriginalPresheaf
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (P : PresheafWithTransfers.{u + 1} k)

/-- Actual restriction of Laurent sections to the literal punctured cylinder neighborhoods. -/
def laurentToPunctured :
    (toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.torusSections P) ⟶
    (cylinderNeighborhood X).op ⋙
      (baseChange (SmoothSite.contractionOpen (.of k) X).left).op ⋙
        (toSmoothSite (SmoothSite.torusCylinder (.of k) X)).op ⋙
          (PresheafWithTransfers.toPresheaf k).obj P :=
  Functor.whiskerLeft (toSmoothSite X).op
      (PresheafWithTransfers.withParameterUnderlyingIso P (SmoothSite.torus (.of k))).hom ≫
    Functor.whiskerRight (NatTrans.op (puncturedProjectionNat X))
      ((PresheafWithTransfers.toPresheaf k).obj P)

/-- Canonical Laurent representatives expressed with the actual original generator map. -/
theorem laurent_generator_formula :
    laurentToAmbientCokernel X P ≫ ambientCokernelToBoundary X P =
      laurentToPunctured X P ≫
        Functor.whiskerLeft (cylinderNeighborhood X).op
          (presheafBoundaryGenerator ((PresheafWithTransfers.toPresheaf k).obj P)
            (SmoothSite.contractionOpen (.of k) X) (SmoothSite.a1Section (.of k) X 0)) ≫
        Functor.whiskerRight (NatTrans.op (zeroNeighborhoodLiftNat X))
          (zeroSectionBoundary X P).obj := by
  simp only [laurentToAmbientCokernel, ambientCokernelToBoundary, laurentToPunctured,
    presheafBoundaryGenerator, Functor.whiskerLeft_comp, Category.assoc]

/-- The original Laurent representative lies in the image after sheafifying the
original contraction, with its original quotient projection retained. -/
theorem laurent_boundary_mem_image (V : FiniteEtaleSite X.left)
    (a : ((PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.torusSections P)).obj (op ((toSmoothSite X).obj V))) :
    ∃ c, (contractionToBoundary X P).hom.app (op V) c =
      (ambientCokernelToBoundary X P).app (op V)
        ((laurentToAmbientCokernel X P).app (op V) a) := by
  refine ⟨(toSheafify (nisnevichTopology X.left)
    ((toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.contraction P))).app (op V)
    (((PresheafWithTransfers.toPresheaf k).map
      (PresheafWithTransfers.toContraction P)).app (op ((toSmoothSite X).obj V)) a), ?_⟩
  exact ConcreteCategory.congr_hom
    (congr_app (laurent_sheafified_boundary X P) (op V)) a

end Motivic.FiniteEtaleSite.OriginalPresheaf
