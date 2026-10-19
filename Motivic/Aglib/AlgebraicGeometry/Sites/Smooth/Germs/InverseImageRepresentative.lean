/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Germs.SmallRepresentative
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Germs.DiagramTransport
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Field.MarkedUnit

/-! # The actual inverse-image unit on original Nisnevich germ representatives -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.Scheme.SmoothSite.RelativeNisnevichNeighborhood
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
        (RelativeNisnevichNeighborhood.smallObject f u (RelativeNisnevichNeighborhood.compose f u
            M)) :=
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
    F.obj.map ((RelativeNisnevichNeighborhood.composeForgetIso f u).app M).hom.op ≫
      ((EtaleSeparatedFiniteType.imageAdjunction b).unit.app
        ((EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj F)).hom.app
          (op (RelativeNisnevichNeighborhood.smallObject f u (RelativeNisnevichNeighborhood.compose
              f u M))) ≫
      ((EtaleSeparatedFiniteType.inverseImage b).obj
        ((EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj F)).obj.map
          ((EtaleSeparatedFiniteType.fieldPointLiftEquiv b (U.left.residueField u) q
            (RelativeNisnevichNeighborhood.smallObject f u (RelativeNisnevichNeighborhood.compose f
                u M))).symm (originalSmallMark f u b q h M)).op := by
  dsimp only [originalGermInverseImageOfFactorization, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom]
  rw [original_ι_smallOriginalFiberIso_inv_assoc]
  congr 1
  change smallFieldDiagramInjection F.obj (U.left.residueField u)
      (U.left.fromSpecResidueField u ≫ f.left) (RelativeNisnevichNeighborhood.smallObject f u
          (RelativeNisnevichNeighborhood.compose f u M))
        M.obj.val.left _ ≫ eqToHom _ ≫ _ = _
  rw [smallFieldDiagramInjection_transport_assoc F.obj (U.left.residueField u) h.symm
    (RelativeNisnevichNeighborhood.smallObject f u (RelativeNisnevichNeighborhood.compose f u M))
        M.obj.val.left _ (Over.w (originalSmallMark f u b q h M))]
  exact EtaleSeparatedFiniteType.fieldNeighborhoodInverseImageIso_marked_ι b
    (U.left.residueField u) q ((EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj F)
      (RelativeNisnevichNeighborhood.smallObject f u (RelativeNisnevichNeighborhood.compose f u M))
          (originalSmallMark f u b q h M)

end AlgebraicGeometry.Scheme.SmoothSite
