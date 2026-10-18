/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PointedMarkedCylinderComparison
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-! # Original cylinder germs on actual open neighborhoods

The marked-slice comparison retains arbitrary field-valued marks. The open
comparison uses their literal lift into the open, not a residue-field replacement
or a derived-continuity assertion.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite

/-- The native marked-neighborhood slice computes the original cylinder germ
for every field-valued marking of an actual small-site test object. -/
def fieldPointCylinderColimitIso (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
    (V : FiniteEtaleSite X.left) (K : Type u) [Field K]
    (b : Spec (.of K) ⟶ V.left)
    (P : (SmoothSite (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    colimit (pointedCylinderValues R (X := (toSmoothSite X).obj V)
      (relativeFieldPoint b K (𝟙 _)) P
      (pointedBase R (X := (toSmoothSite X).obj V) (relativeFieldPoint b K (𝟙 _)))) ≅
    colimit (pointedCylinderValues R (X := X)
      (relativeFieldPoint (b ≫ V.hom) K (𝟙 _)) P
      (pointedBase R (X := X) (relativeFieldPoint (b ≫ V.hom) K (𝟙 _)))) :=
  (relativeFieldPoint b K (𝟙 _)).presheafFiber.mapIso
    (Functor.isoWhiskerRight (NatIso.op (Functor.isoWhiskerRight
      (composeObjectToSmoothIso X V) (SmoothSite.parameterProduct (SmoothSite.affineLine R)))) P) ≪≫
    fieldPointComposeFiberIso V K b
      ((toSmoothSite X ⋙ SmoothSite.parameterProduct (SmoothSite.affineLine R)).op ⋙ P)

/-- The comparison sends every original cylinder representative by its literal
smooth-cylinder comparison and preserves its entire field-valued marking. -/
@[reassoc]
theorem toPresheafFiber_fieldPointCylinderColimitIso_hom
    (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
    (V : FiniteEtaleSite X.left) (K : Type u) [Field K]
    (b : Spec (.of K) ⟶ V.left)
    (P : (SmoothSite (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (W : FiniteEtaleSite V.left) (a : (relativeFieldPoint b K (𝟙 _)).fiber.obj W) :
    (relativeFieldPoint b K (𝟙 _)).toPresheafFiber W a
        ((toSmoothSite ((toSmoothSite X).obj V) ⋙
          SmoothSite.parameterProduct (SmoothSite.affineLine R)).op ⋙ P) ≫
      (fieldPointCylinderColimitIso R X V K b P).hom =
    P.map (SmoothSite.a1Map R ((composeObjectToSmoothIso X V).hom.app W)).op ≫
      (relativeFieldPoint (b ≫ V.hom) K (𝟙 _)).toPresheafFiber
        (composeObject V W) (fieldPointComposeElement V K b W a)
          ((toSmoothSite X ⋙ SmoothSite.parameterProduct (SmoothSite.affineLine R)).op ⋙ P) := by
  dsimp only [fieldPointCylinderColimitIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality_assoc]
  exact congrArg
    (fun f => P.map (SmoothSite.a1Map R ((composeObjectToSmoothIso X V).hom.app W)).op ≫ f)
    (toPresheafFiber_fieldPointComposeFiberIso_hom V K b
      ((toSmoothSite X ⋙ SmoothSite.parameterProduct (SmoothSite.affineLine R)).op ⋙ P) W a)

section OpenLift

variable {S : Scheme.{u}} (K : Type u) [Field K] (b : Spec (.of K) ⟶ S)
  (p : Spec (.of K)) (O : S.Opens) (hO : b p ∈ O)

/-- The actual field-valued marking lifts to every open containing its image. -/
def openFieldPointLift : Spec (.of K) ⟶ O.toScheme :=
  IsOpenImmersion.lift O.ι b (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    have hq : q = p := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [hq]
    exact hO)

/-- The lift retains the entire original field-valued map. -/
@[reassoc]
theorem openFieldPointLift_ι : openFieldPointLift K b p O hO ≫ O.ι = b :=
  IsOpenImmersion.lift_fac _ _ _

/-- Its image is the original point regarded as a point of the open. -/
theorem openFieldPointLift_apply :
    openFieldPointLift K b p O hO p = (⟨b p, hO⟩ : O) := by
  apply Subtype.ext
  exact congrArg (fun f : Spec (.of K) ⟶ S => f p) (openFieldPointLift_ι K b p O hO)

end OpenLift

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (K : Type u) [Field K] (b : Spec (.of K) ⟶ X.left)
  (p : Spec (.of K)) (O : X.left.Opens) (hO : b p ∈ O)

/-- Passing to an actual open neighborhood does not change the original cylinder
germ, including arbitrary residue extensions in its field-valued marking. -/
def openFieldPointCylinderColimitIso
    (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    colimit (pointedCylinderValues (.of k) (X := (toSmoothSite X).obj (openObject O))
      (relativeFieldPoint (openFieldPointLift K b p O hO) K (𝟙 _)) P
      (pointedBase (.of k) (X := (toSmoothSite X).obj (openObject O))
        (relativeFieldPoint (openFieldPointLift K b p O hO) K (𝟙 _)))) ≅
    colimit (pointedCylinderValues (.of k) (X := X) (relativeFieldPoint b K (𝟙 _)) P
      (pointedBase (.of k) (X := X) (relativeFieldPoint b K (𝟙 _)))) := by
  refine fieldPointCylinderColimitIso (.of k) X (openObject O) K
    (openFieldPointLift K b p O hO) P ≪≫ eqToIso ?_
  change colimit (pointedCylinderValues (.of k) (X := X)
    (relativeFieldPoint (openFieldPointLift K b p O hO ≫ O.ι) K (𝟙 _)) P
      (pointedBase (.of k) (X := X)
        (relativeFieldPoint (openFieldPointLift K b p O hO ≫ O.ι) K (𝟙 _)))) = _
  rw [openFieldPointLift_ι]

end Motivic.FiniteEtaleSite
