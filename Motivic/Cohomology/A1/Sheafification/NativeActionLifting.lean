/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Pencils.OriginalMiddleInput
public import Motivic.Transfers.Presheaf.Actions.Pencils.OriginalHistoryMiddleRelations
public import Motivic.Cohomology.A1.Sheafification.MiddleLiftDifference

/-! # Lifting from the native action diagram

For `P : PresheafWithTransfers.{u + 1} k` over a field, the native action
diagram is transported to the original matching image representatives. The
adapter retains the actual two-arrow Nisnevich cover, source and puncture
restrictions, parameter map and four supplied E2/E4/E3/E5 action relations.
E3 remains zero action of the original signed difference.

The conclusion is an image section on the whole cylinder over the given
nonempty base open, with the original sheafification-unit equation. The
`OriginalLocalizationHistory` specialization supplies its middle relations
from coefficient HI; the general diagram adapter retains them as inputs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme Scheme.Hom Scheme.Modules Scheme.Modules.Invertible
open Scheme.RelativeAffineLineEtaleCompactification Scheme.RelativeCurvePencil
open RelativeProjectiveLine AlgebraicGeometry.FiniteSchemeNormBaseChange
open Motivic Motivic.PresheafWithTransfers
universe u v w

namespace Motivic.PresheafWithTransfers
variable {k : Type u} [Field k]

/-- Transport one actual native pencil action diagram to the original matching
representatives and construct an image section on the whole cylinder. -/
theorem nisnevichImage_wholeCylinder_lift_of_native_action_diagram
    (P : PresheafWithTransfers.{u + 1} k)
    {X U U' T A Y B A' Y' Xn Yn An Qn Vn : SmoothSite (Spec (.of k))}
    (jU : U ⟶ X) (l : U' ⟶ U)
    [IsOpenImmersion jU.left] [IsOpenImmersion l.left]
    (hU' : Nonempty U'.left) (eT : T ≅ SmoothSite.a1Cylinder (.of k) U)
    (h : SmoothSite.a1Cylinder (.of k) U' ⟶ T)
    (he : h ≫ eT.hom = SmoothSite.a1Map (.of k) l)
    (a : A ⟶ T) (p : Y ⟶ T) (bAorig : B ⟶ A) (bYorig : B ⟶ Y)
    (HB : IsPullback bAorig bYorig a p)
    (i' : A' ⟶ SmoothSite.a1Cylinder (.of k) U')
    (v' : Y' ⟶ SmoothSite.a1Cylinder (.of k) U')
    (rA : A' ⟶ A) (rY : Y' ⟶ Y)
    (hi' : rA ≫ a = i' ≫ h) (hv' : rY ≫ p = v' ≫ h)
    (hcover' : Sieve.ofTwoArrows i' v' ∈
      SmoothSite.nisnevichTopology (Spec (.of k)) (SmoothSite.a1Cylinder (.of k) U'))
    (pSite : Yn ⟶ Xn) (aSite : An ⟶ Xn)
    (uSite : Vn ⟶ Yn) (wSite : Vn ⟶ Qn) (δ : An ⟶ Qn)
    (ηY : Y' ⟶ Yn) (ηA : A' ⟶ An)
    (κ : SmoothSite.a1Cylinder (.of k) U' ⟶ Xn)
    (rYnative : Yn ⟶ Y) (rAnative : Qn ⟶ A)
    (hsourceSite : ηY ≫ pSite = v' ≫ κ)
    (hpunctureSite : ηA ≫ aSite = i' ≫ κ)
    (hsourceRestrictionSite : ηY ≫ rYnative = rY)
    (hparameterRestrictionSite : ηA ≫ δ ≫ rAnative = rA)
    (hsquare : (wSite ≫ rAnative) ≫ a = (uSite ≫ rYnative) ≫ p)
    (lambdaNative : (Cor.graphFunctor k).obj Xn ⟶ (Cor.graphFunctor k).obj Qn)
    (sourceLambda : (Cor.graphFunctor k).obj Yn ⟶ (Cor.graphFunctor k).obj Vn)
    (sourcePsi : (Cor.graphFunctor k).obj An ⟶ (Cor.graphFunctor k).obj Vn)
    (hE2native : (nisnevichImage P).transfer
      (sourceLambda ≫ (Cor.graphFunctor k).map uSite) =
        (nisnevichImage P).transfer ((Cor.graphFunctor k).map (𝟙 Yn)))
    (hE4native : (nisnevichImage P).transfer
      (sourcePsi ≫ (Cor.graphFunctor k).map uSite) = 0)
    (hE3native : (nisnevichImage P).transfer
      (Sub.sub (α := (Cor.graphFunctor k).obj Yn ⟶ (Cor.graphFunctor k).obj Qn)
        (sourceLambda ≫ (Cor.graphFunctor k).map wSite)
        ((Cor.graphFunctor k).map pSite ≫ lambdaNative)) = 0)
    (hE5same : (nisnevichImage P).transfer
      ((Cor.graphFunctor k).map aSite ≫ lambdaNative) =
        (nisnevichImage P).transfer (show
            (Cor.graphFunctor k).obj An ⟶ (Cor.graphFunctor k).obj Qn from
          sourcePsi ≫ (Cor.graphFunctor k).map wSite) +
          (nisnevichImage P).transfer (show
            (Cor.graphFunctor k).obj An ⟶ (Cor.graphFunctor k).obj Qn from
            (Cor.graphFunctor k).map δ))
    (g : ((nisnevichSheafify k).obj P).obj.sections
      ((Cor.graphFunctor k).obj (SmoothSite.a1Cylinder (.of k) X)))
    (sA : (nisnevichImage P).sections ((Cor.graphFunctor k).obj A))
    (sY : (nisnevichImage P).sections ((Cor.graphFunctor k).obj Y))
    (hm : (nisnevichImage P).transfer ((Cor.graphFunctor k).map bAorig) sA =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map bYorig) sY)
    (hgA : (nisnevichImageι P).hom.app (op ((Cor.graphFunctor k).obj A)) sA =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (a ≫ eT.hom ≫ SmoothSite.a1Map (.of k) jU)) g)
    (hgY : (nisnevichImageι P).hom.app (op ((Cor.graphFunctor k).obj Y)) sY =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (p ≫ eT.hom ≫ SmoothSite.a1Map (.of k) jU)) g) :
    IsOpenImmersion (l ≫ jU).left ∧ Nonempty U'.left ∧
      ∃ t : (nisnevichImage P).sections
        ((Cor.graphFunctor k).obj (SmoothSite.a1Cylinder (.of k) U')),
        (nisnevichImageι P).hom.app
          (op ((Cor.graphFunctor k).obj (SmoothSite.a1Cylinder (.of k) U'))) t =
          ((nisnevichSheafify k).obj P).obj.transfer
            ((Cor.graphFunctor k).map (SmoothSite.a1Map (.of k) (l ≫ jU))) g := by
  let S := nisnevichImage P
  let hB := HB.lift (wSite ≫ rAnative) (uSite ≫ rYnative) hsquare
  have hB_A : hB ≫ bAorig = wSite ≫ rAnative :=
    HB.lift_fst (wSite ≫ rAnative) (uSite ≫ rYnative) hsquare
  have hB_Y : hB ≫ bYorig = uSite ≫ rYnative :=
    HB.lift_snd (wSite ≫ rAnative) (uSite ≫ rYnative) hsquare
  let lambdaA := (Cor.graphFunctor k).map κ ≫ lambdaNative ≫
    (Cor.graphFunctor k).map rAnative
  let lambdaB := (Cor.graphFunctor k).map ηY ≫ sourceLambda ≫ (Cor.graphFunctor k).map hB
  let psi := (Cor.graphFunctor k).map ηA ≫ sourcePsi ≫ (Cor.graphFunctor k).map hB
  let e3Difference : (Cor.graphFunctor k).obj Yn ⟶ (Cor.graphFunctor k).obj Qn :=
    (sourceLambda ≫ (Cor.graphFunctor k).map wSite) -
      ((Cor.graphFunctor k).map pSite ≫ lambdaNative)
  have hE3Difference : e3Difference =
      (sourceLambda ≫ (Cor.graphFunctor k).map wSite) -
      ((Cor.graphFunctor k).map pSite ≫ lambdaNative) := rfl
  have hE3nativeSame : S.transfer e3Difference = 0 := hE3native
  have hE2same :
      S.transfer (sourceLambda ≫ (Cor.graphFunctor k).map (uSite ≫ rYnative)) =
        S.transfer ((Cor.graphFunctor k).map rYnative) := by
    calc
      _ = S.transfer ((Cor.graphFunctor k).map rYnative) ≫
          S.transfer (sourceLambda ≫ (Cor.graphFunctor k).map uSite) := by
        simp only [Functor.map_comp, transfer_comp, Category.assoc]
      _ = _ := by rw [hE2native, CategoryTheory.Functor.map_id, transfer_id, Category.comp_id]
  have hE4same :
      S.transfer (sourcePsi ≫ (Cor.graphFunctor k).map (uSite ≫ rYnative)) = 0 := by
    calc
      _ = S.transfer ((Cor.graphFunctor k).map rYnative) ≫
          S.transfer (sourcePsi ≫ (Cor.graphFunctor k).map uSite) := by
        simp only [Functor.map_comp, transfer_comp, Category.assoc]
      _ = 0 := by rw [hE4native, comp_zero]
  -- These are equalities of transported correspondences obtained from
  -- graph functoriality and the actual HB.lift projections. They do NOT
  -- upgrade any of the native action equalities to correspondence equality.
  have hLambdaB_Y :
      lambdaB ≫ (Cor.graphFunctor k).map bYorig =
        (Cor.graphFunctor k).map ηY ≫
          (sourceLambda ≫ (Cor.graphFunctor k).map (uSite ≫ rYnative)) := by
    simp only [lambdaB, Category.assoc, ← Functor.map_comp, hB_Y]
  have hPsi_Y :
      psi ≫ (Cor.graphFunctor k).map bYorig =
        (Cor.graphFunctor k).map ηA ≫
          (sourcePsi ≫ (Cor.graphFunctor k).map (uSite ≫ rYnative)) := by
    simp only [psi, Category.assoc, ← Functor.map_comp, hB_Y]
  have hLambdaB_A :
      lambdaB ≫ (Cor.graphFunctor k).map bAorig =
        (Cor.graphFunctor k).map ηY ≫
          (sourceLambda ≫ (Cor.graphFunctor k).map wSite) ≫
            (Cor.graphFunctor k).map rAnative := by
    simp only [lambdaB, Category.assoc, ← Functor.map_comp, hB_A]
  have hPsi_A :
      psi ≫ (Cor.graphFunctor k).map bAorig =
        (Cor.graphFunctor k).map ηA ≫
          (sourcePsi ≫ (Cor.graphFunctor k).map wSite) ≫
            (Cor.graphFunctor k).map rAnative := by
    simp only [psi, Category.assoc, ← Functor.map_comp, hB_A]
  have hVLambdaA :
      (Cor.graphFunctor k).map v' ≫ lambdaA =
        (Cor.graphFunctor k).map ηY ≫
          ((Cor.graphFunctor k).map pSite ≫ lambdaNative) ≫
            (Cor.graphFunctor k).map rAnative := by
    simpa only [lambdaA, Functor.map_comp, Category.assoc] using
      congrArg (fun f => (Cor.graphFunctor k).map f ≫ lambdaNative ≫
        (Cor.graphFunctor k).map rAnative) hsourceSite.symm
  have hILambdaA :
      (Cor.graphFunctor k).map i' ≫ lambdaA =
        (Cor.graphFunctor k).map ηA ≫
          ((Cor.graphFunctor k).map aSite ≫ lambdaNative) ≫
            (Cor.graphFunctor k).map rAnative := by
    simpa only [lambdaA, Functor.map_comp, Category.assoc] using
      congrArg (fun f => (Cor.graphFunctor k).map f ≫ lambdaNative ≫
        (Cor.graphFunctor k).map rAnative) hpunctureSite.symm
  -- E2: the original Y restriction, not a restriction cancelled in S.
  have hE2 :
      S.transfer (lambdaB ≫ (Cor.graphFunctor k).map bYorig) =
        S.transfer ((Cor.graphFunctor k).map rY) := by
    rw [hLambdaB_Y, transfer_comp, hE2same]
    rw [← transfer_comp, ← Functor.map_comp, hsourceRestrictionSite]
  -- E3 is retained as a DIFFERENCE-ZERO relation on the original maps.
  -- This Cor identity is just the already proved graph transports and bilinearity;
  -- no action equality is promoted to equality of correspondences.
  have hE3transport :
      (Sub.sub (α := (Cor.graphFunctor k).obj Y' ⟶ (Cor.graphFunctor k).obj A)
        (lambdaB ≫ (Cor.graphFunctor k).map bAorig)
        ((Cor.graphFunctor k).map v' ≫ lambdaA)) =
      (Cor.graphFunctor k).map ηY ≫ e3Difference ≫
        (Cor.graphFunctor k).map rAnative := by
    rw [hLambdaB_A, hVLambdaA, hE3Difference]
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc]
    rfl
  have hE3zero :
      S.transfer
        (Sub.sub (α := (Cor.graphFunctor k).obj Y' ⟶ (Cor.graphFunctor k).obj A)
          (lambdaB ≫ (Cor.graphFunctor k).map bAorig)
          ((Cor.graphFunctor k).map v' ≫ lambdaA)) = 0 := by
    rw [hE3transport]
    simp only [transfer_comp, hE3nativeSame,
      CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]
  -- E4: the source adapter cannot change the zero action.
  have hE4 :
      S.transfer (psi ≫ (Cor.graphFunctor k).map bYorig) = 0 := by
    rw [hPsi_Y, transfer_comp, hE4same, zero_comp]
  -- The two summands in transported E5 are identified independently.
  have hCorrectionAction :
      S.transfer ((Cor.graphFunctor k).map rAnative) ≫
        S.transfer (sourcePsi ≫ (Cor.graphFunctor k).map wSite) ≫
          S.transfer ((Cor.graphFunctor k).map ηA) =
        S.transfer (psi ≫ (Cor.graphFunctor k).map bAorig) := by
    rw [hPsi_A]
    simp only [transfer_comp, Category.assoc]
  have hParameterAction :
      S.transfer ((Cor.graphFunctor k).map rAnative) ≫
        S.transfer ((Cor.graphFunctor k).map δ) ≫
          S.transfer ((Cor.graphFunctor k).map ηA) =
        S.transfer ((Cor.graphFunctor k).map rA) := by
    simpa only [Functor.map_comp, transfer_comp, Category.assoc] using
      congrArg (fun f => S.transfer ((Cor.graphFunctor k).map f))
        hparameterRestrictionSite
  have hE5add :
      S.transfer ((Cor.graphFunctor k).map i' ≫ lambdaA) =
        S.transfer (psi ≫ (Cor.graphFunctor k).map bAorig) +
          S.transfer ((Cor.graphFunctor k).map rA) := by
    calc
      _ = S.transfer ((Cor.graphFunctor k).map rAnative) ≫
          S.transfer ((Cor.graphFunctor k).map aSite ≫ lambdaNative) ≫
            S.transfer ((Cor.graphFunctor k).map ηA) := by
        rw [hILambdaA]
        simp only [transfer_comp, Category.assoc]
      _ = S.transfer ((Cor.graphFunctor k).map rAnative) ≫
          (S.transfer (sourcePsi ≫ (Cor.graphFunctor k).map wSite) +
            S.transfer ((Cor.graphFunctor k).map δ)) ≫
              S.transfer ((Cor.graphFunctor k).map ηA) := by
        rw [hE5same]
      _ = (S.transfer ((Cor.graphFunctor k).map rAnative) ≫
            S.transfer (sourcePsi ≫ (Cor.graphFunctor k).map wSite) ≫
              S.transfer ((Cor.graphFunctor k).map ηA)) +
          (S.transfer ((Cor.graphFunctor k).map rAnative) ≫
            S.transfer ((Cor.graphFunctor k).map δ) ≫
              S.transfer ((Cor.graphFunctor k).map ηA)) := by
        simp only [Preadditive.comp_add, Preadditive.add_comp]
      _ = _ := by rw [hCorrectionAction, hParameterAction]
  -- E5: this is the exact Sub.sub spelling of the middle-lift input.
  -- The sign is lambda - psi, retaining c.dS - c.nS in sourcePsi.
  have hE5 :
      S.transfer
        (Sub.sub (α := (Cor.graphFunctor k).obj A' ⟶ (Cor.graphFunctor k).obj A)
          ((Cor.graphFunctor k).map i' ≫ lambdaA)
          (psi ≫ (Cor.graphFunctor k).map bAorig)) =
        S.transfer ((Cor.graphFunctor k).map rA) := by
    change S.transfer (((Cor.graphFunctor k).map i' ≫ lambdaA) -
      (psi ≫ (Cor.graphFunctor k).map bAorig)) = _
    rw [transfer_sub, hE5add, add_sub_cancel_left]
  exact nisnevichImage_wholeCylinder_lift_of_middle_difference_relations
    P jU l hU' eT h he a p bAorig bYorig i' v' rA rY hi' hv' hcover'
    lambdaA lambdaB psi hE2 hE3zero hE4 hE5 g sA sY hm hgA hgY


end Motivic.PresheafWithTransfers

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.OriginalMiddleInput
variable {k : Type u} [Field k]
/-- Consume the shared middle relations without reopening any pencil constructors. -/
theorem wholeCylinder_lift_of_middleRelations
    (G : OriginalMiddleInput k)
    (aSite : G.siteA ⟶ G.siteX) (delta : G.siteA ⟶ G.siteQ)
    (P : PresheafWithTransfers.{u + 1} k)
    {X U U' T A Y B A' Y' : SmoothSite (Spec (.of k))}
    (jU : U ⟶ X) (l : U' ⟶ U)
    [IsOpenImmersion jU.left] [IsOpenImmersion l.left]
    (hU' : Nonempty U'.left) (eT : T ≅ SmoothSite.a1Cylinder (.of k) U)
    (h : SmoothSite.a1Cylinder (.of k) U' ⟶ T)
    (he : h ≫ eT.hom = SmoothSite.a1Map (.of k) l)
    (a : A ⟶ T) (p : Y ⟶ T) (bAorig : B ⟶ A) (bYorig : B ⟶ Y)
    (HB : IsPullback bAorig bYorig a p)
    (i' : A' ⟶ SmoothSite.a1Cylinder (.of k) U')
    (v' : Y' ⟶ SmoothSite.a1Cylinder (.of k) U')
    (rA : A' ⟶ A) (rY : Y' ⟶ Y)
    (hi' : rA ≫ a = i' ≫ h) (hv' : rY ≫ p = v' ≫ h)
    (hcover' : Sieve.ofTwoArrows i' v' ∈
      SmoothSite.nisnevichTopology (Spec (.of k)) (SmoothSite.a1Cylinder (.of k) U'))
    (ηY : Y' ⟶ G.siteY) (ηA : A' ⟶ G.siteA)
    (κ : SmoothSite.a1Cylinder (.of k) U' ⟶ G.siteX)
    (rYnative : G.siteY ⟶ Y) (rAnative : G.siteQ ⟶ A)
    (hsourceSite : ηY ≫ G.pSite = v' ≫ κ)
    (hpunctureSite : ηA ≫ aSite = i' ≫ κ)
    (hsourceRestrictionSite : ηY ≫ rYnative = rY)
    (hparameterRestrictionSite : ηA ≫ delta ≫ rAnative = rA)
    (hsquare : (G.wSite ≫ rAnative) ≫ a = (G.uSite ≫ rYnative) ≫ p)
    (hMiddle : G.MiddleRelations aSite delta (nisnevichImage P))
    (g : ((nisnevichSheafify k).obj P).obj.sections
      ((Cor.graphFunctor k).obj (SmoothSite.a1Cylinder (.of k) X)))
    (sA : (nisnevichImage P).sections ((Cor.graphFunctor k).obj A))
    (sY : (nisnevichImage P).sections ((Cor.graphFunctor k).obj Y))
    (hm : (nisnevichImage P).transfer ((Cor.graphFunctor k).map bAorig) sA =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map bYorig) sY)
    (hgA : (nisnevichImageι P).hom.app (op ((Cor.graphFunctor k).obj A)) sA =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (a ≫ eT.hom ≫ SmoothSite.a1Map (.of k) jU)) g)
    (hgY : (nisnevichImageι P).hom.app (op ((Cor.graphFunctor k).obj Y)) sY =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (p ≫ eT.hom ≫ SmoothSite.a1Map (.of k) jU)) g) :
    IsOpenImmersion (l ≫ jU).left ∧ Nonempty U'.left ∧
      ∃ t : (nisnevichImage P).sections
        ((Cor.graphFunctor k).obj (SmoothSite.a1Cylinder (.of k) U')),
        (nisnevichImageι P).hom.app
          (op ((Cor.graphFunctor k).obj (SmoothSite.a1Cylinder (.of k) U'))) t =
          ((nisnevichSheafify k).obj P).obj.transfer
            ((Cor.graphFunctor k).map (SmoothSite.a1Map (.of k) (l ≫ jU))) g := by
  obtain ⟨hE2, hE4, hE3, hE5⟩ := hMiddle
  exact nisnevichImage_wholeCylinder_lift_of_native_action_diagram
    P jU l hU' eT h he a p bAorig bYorig HB i' v' rA rY hi' hv' hcover'
    G.pSite aSite G.uSite G.wSite delta
    ηY ηA κ rYnative rAnative hsourceSite hpunctureSite
    hsourceRestrictionSite hparameterRestrictionSite hsquare
    G.arrows.target G.arrows.source G.arrows.correction
    hE2 hE4 hE3 hE5 g sA sY hm hgA hgY

end AlgebraicGeometry.Scheme.RelativeCurvePencil.OriginalMiddleInput

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
attribute [local instance] OriginalLocalizationSeed.commRing OriginalLocalizationSeed.domain
  OriginalLocalizationSeed.normal OriginalLocalizationSeed.noetherian
  OriginalLocalizationSeed.affineY OriginalLocalizationSeed.affineA
  OriginalLocalizationSeed.etaleP OriginalLocalizationSeed.quasiCompactP
  OriginalLocalizationSeed.separatedP OriginalLocalizationSeed.openA
  OriginalLocalizationSeed.closedZ OriginalLocalizationSeed.finiteZ
  OriginalLocalizationSeed.affineO OriginalLocalizationHistory.affineV
  OriginalTargetSectionWitnesses.unitA OriginalTargetSectionWitnesses.unitB
namespace OriginalLocalizationHistory
attribute [local instance] chartOpen chartSmooth seedEtale seedOpen seedInclusionOpen
  seedMarkedFinite seedMarkedClosed sourceEtale punctureOpen inclusionOpen sourceSmooth
  lineSmooth lineSeparated compactificationProper retainedProductOpen seedProjectiveMarked
  firstProjectiveMarked finalProjectiveMarked firstSourceAffine firstPunctureAffine
  finalSourceAffine finalPunctureAffine retainedAffine overlapAffine retainedOpen
  overlapSmooth overlapFlat infinityAffine
local instance (S : OriginalLocalizationSeed.{u}) : IsFinite S.F₁ :=
  boundaryBaseProjectiveMap_finite S.R (ULift.{u} (Fin 2)) (toProjectiveLine S.R S.p) S.O
local instance (H : OriginalLocalizationHistory.{u}) : IsFinite H.F₂ :=
  boundaryBaseProjectiveMap_finite H.seed.R₁ (ULift.{u} (Fin 2)) H.seed.F₁ H.V

namespace SourceWitnesses
attribute [local instance]
  Scheme.RelativeCurvePencil.nativeTargetCorrectionSectionsSmoothRelativeDimension1
  Scheme.RelativeCurvePencil.nativeTargetCorrectionSectionsSmoothRelativeDimension2
variable {H : OriginalLocalizationHistory.{u}} {B : H.BoundaryWitnesses}
  {k : Type u} [Field k] (W : H.SourceWitnesses B) (T : H.TargetWitnesses)
  (t : Spec Γ(H.V.toScheme, ⊤) ⟶ Spec (.of k)) [Smooth t]
/-- Apply the accepted lifting adapter to the actual history relations. -/
theorem wholeCylinder_lift
    (P : Motivic.PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    {X U U' Tc A Y B A' Y' : SmoothSite (Spec (.of k))}
    (jU : U ⟶ X) (l : U' ⟶ U)
    [IsOpenImmersion jU.left] [IsOpenImmersion l.left]
    (hU' : Nonempty U'.left) (eT : Tc ≅ SmoothSite.a1Cylinder (.of k) U)
    (h : SmoothSite.a1Cylinder (.of k) U' ⟶ Tc)
    (he : h ≫ eT.hom = SmoothSite.a1Map (.of k) l)
    (a : A ⟶ Tc) (p : Y ⟶ Tc) (bAorig : B ⟶ A) (bYorig : B ⟶ Y)
    (HB : IsPullback bAorig bYorig a p)
    (i' : A' ⟶ SmoothSite.a1Cylinder (.of k) U')
    (v' : Y' ⟶ SmoothSite.a1Cylinder (.of k) U')
    (rA : A' ⟶ A) (rY : Y' ⟶ Y)
    (hi' : rA ≫ a = i' ≫ h) (hv' : rY ≫ p = v' ≫ h)
    (hcover' : Sieve.ofTwoArrows i' v' ∈
      SmoothSite.nisnevichTopology (Spec (.of k)) (SmoothSite.a1Cylinder (.of k) U'))
    (ηY : Y' ⟶ (W.toNative T t).toInput.siteY) (ηA : A' ⟶ (W.toNative T t).toInput.siteA)
    (κ : SmoothSite.a1Cylinder (.of k) U' ⟶ (W.toNative T t).toInput.siteX)
    (rYnative : (W.toNative T t).toInput.siteY ⟶ Y) (rAnative : (W.toNative T t).toInput.siteQ ⟶ A)
    (hsourceSite : ηY ≫ (W.toNative T t).toInput.pSite = v' ≫ κ)
    (hpunctureSite : ηA ≫ (W.toNative T t).aSite = i' ≫ κ)
    (hsourceRestrictionSite : ηY ≫ rYnative = rY)
    (hparameterRestrictionSite : ηA ≫ (W.toNative T t).delta ≫ rAnative = rA)
    (hsquare : ((W.toNative T t).toInput.wSite ≫ rAnative) ≫ a = ((W.toNative T t).toInput.uSite
      ≫ rYnative) ≫ p)
    (g : ((nisnevichSheafify k).obj P).obj.sections
      ((Cor.graphFunctor k).obj (SmoothSite.a1Cylinder (.of k) X)))
    (sA : (nisnevichImage P).sections ((Cor.graphFunctor k).obj A))
    (sY : (nisnevichImage P).sections ((Cor.graphFunctor k).obj Y))
    (hm : (nisnevichImage P).transfer ((Cor.graphFunctor k).map bAorig) sA =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map bYorig) sY)
    (hgA : (nisnevichImageι P).hom.app (op ((Cor.graphFunctor k).obj A)) sA =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (a ≫ eT.hom ≫ SmoothSite.a1Map (.of k) jU)) g)
    (hgY : (nisnevichImageι P).hom.app (op ((Cor.graphFunctor k).obj Y)) sY =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (p ≫ eT.hom ≫ SmoothSite.a1Map (.of k) jU)) g) :
    IsOpenImmersion (l ≫ jU).left ∧ Nonempty U'.left ∧
      ∃ t : (nisnevichImage P).sections
        ((Cor.graphFunctor k).obj (SmoothSite.a1Cylinder (.of k) U')),
        (nisnevichImageι P).hom.app
          (op ((Cor.graphFunctor k).obj (SmoothSite.a1Cylinder (.of k) U'))) t =
          ((nisnevichSheafify k).obj P).obj.transfer
            ((Cor.graphFunctor k).map (SmoothSite.a1Map (.of k) (l ≫ jU))) g := by
  exact ((W.toNative T t).toInput.wholeCylinder_lift_of_middleRelations
      (W.toNative T t).aSite (W.toNative T t).delta P
      jU l hU' eT h he a p bAorig bYorig HB i' v' rA rY hi' hv' hcover'
      ηY ηA κ rYnative rAnative hsourceSite hpunctureSite
      hsourceRestrictionSite hparameterRestrictionSite hsquare
      (W.middleRelations T t P hP) g sA sY hm hgA hgY)

end SourceWitnesses
end OriginalLocalizationHistory
end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
