/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermSmallRepresentative
public import Motivic.Transfers.OriginalGermDiagramTransport
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldMarkedUnit

/-! # The actual inverse-image unit on original Nisnevich germ representatives -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Motivic.SmoothSite
open RelativeNisnevichNeighborhood
variable {B : Scheme.{u}} [IsAffine B] {U X : SmoothSite B}
  (F : Sheaf (nisnevichTopology B) AddCommGrpCat.{u + 1})
  (f : U ⟶ X) [Etale f.left] (u : U.left) {S : Scheme.{u}}
  (b : S ⟶ X.left) (q : Spec (U.left.residueField u) ⟶ S)
  [Etale q] [IsSeparated q] [QuasiCompact q]
  (h : q ≫ b = U.left.fromSpecResidueField u ≫ f.left)

/-- The mark on a composed original neighborhood, using the specified literal factorization. -/
def originalSmallMark (M : NisnevichNeighborhood U u) :
    Over.mk (q ≫ b) ⟶
      (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ X.left).obj
        (smallObject f u (compose f u M)) :=
  Over.homMk M.obj.val.left (by
    change M.obj.val.left ≫ (M.toBase.left ≫ f.left) = q ≫ b
    rw [← Category.assoc, show M.obj.val.left ≫ M.toBase.left =
      U.left.fromSpecResidueField u from Over.w M.obj.val, h])

/-- Original representatives map by the genuine inverse-image adjunction unit
and restriction along the actual pullback lift of their marked field point. -/
@[reassoc]
theorem originalGermInverseImageOfFactorization_ι (M : NisnevichNeighborhood U u) :
    (nisnevichPointFiberCocone U u F.obj).ι.app (op M) ≫
      (originalGermInverseImageOfFactorization F f u b q h).hom =
    F.obj.map ((composeForgetIso f u).app M).hom.op ≫
      ((FiniteEtaleSite.imageAdjunction b).unit.app
        ((FiniteEtaleSite.restrict X AddCommGrpCat).obj F)).hom.app
          (op (smallObject f u (compose f u M))) ≫
      ((FiniteEtaleSite.inverseImage b).obj
        ((FiniteEtaleSite.restrict X AddCommGrpCat).obj F)).obj.map
          ((FiniteEtaleSite.fieldPointLiftEquiv b (U.left.residueField u) q
            (smallObject f u (compose f u M))).symm (originalSmallMark f u b q h M)).op := by
  dsimp only [originalGermInverseImageOfFactorization, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom]
  rw [original_ι_smallOriginalFiberIso_inv_assoc]
  congr 1
  change smallFieldDiagramInjection F.obj (U.left.residueField u)
      (U.left.fromSpecResidueField u ≫ f.left) (smallObject f u (compose f u M))
        M.obj.val.left _ ≫ eqToHom _ ≫ _ = _
  rw [smallFieldDiagramInjection_transport_assoc F.obj (U.left.residueField u) h.symm
    (smallObject f u (compose f u M)) M.obj.val.left _ (Over.w (originalSmallMark f u b q h M))]
  exact FiniteEtaleSite.fieldNeighborhoodInverseImageIso_marked_ι b
    (U.left.residueField u) q ((FiniteEtaleSite.restrict X AddCommGrpCat).obj F)
      (smallObject f u (compose f u M)) (originalSmallMark f u b q h M)

end Motivic.SmoothSite
