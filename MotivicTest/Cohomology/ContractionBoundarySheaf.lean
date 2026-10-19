module

public import Motivic.Cohomology.A1.Boundary.Contraction.Sheaf

/-! # Consumers of the actual small-site boundary sheaf

These tests require only ordinary homotopy invariance and the original transfer
sheaf. There are no relative purity, positive cohomology or strict HI premises.
-/

@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (EtaleSeparatedFiniteType)

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Opposite Motivic

universe u

namespace MotivicTest.Cohomology.ContractionBoundarySheaf

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)

/-- The source remains the original contraction sheaf, not a replacement local model. -/
def canonicalMap :
    (_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj
        ((SheafWithTransfers.toSheaf k).obj (SheafWithTransfers.contraction F hF)) ⟶
      FiniteEtaleSite.zeroSectionBoundary X F :=
  FiniteEtaleSite.contractionToBoundary X F hF

/-- On every original quotient representative, the map is the actual open
restriction/cokernel/closed-inverse-image construction. -/
theorem canonicalMap_on_representative (V : EtaleSeparatedFiniteType X.left)
    (s : PresheafWithTransfers.sections (PresheafWithTransfers.torusSections F.obj)
      (Cor.mk ((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.toSmoothSite X).obj V))) :
    (canonicalMap X F hF).hom.app (op V)
        ((PresheafWithTransfers.toContraction F.obj).hom.app
          (op (Cor.mk ((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.toSmoothSite
              X).obj V))) s) =
      (FiniteEtaleSite.ambientCokernelToBoundary X F).app (op V)
        ((FiniteEtaleSite.laurentToAmbientCokernel X F).app (op V) s) := by
  have h := congrArg (fun f ↦ f.app (op V))
    (FiniteEtaleSite.toContraction_contractionToBoundaryPresheaf X F)
  exact congrArg (fun f ↦ f s) h

/-- The closed inverse-image functor is genuinely left adjoint to small-site direct image. -/
def closedImageAdjunction :=
  _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.imageAdjunction (SmoothSite.a1Section
      (.of k) X 0).left

end MotivicTest.Cohomology.ContractionBoundarySheaf
