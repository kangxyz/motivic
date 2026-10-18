/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PointedOpenCylinderComparison
public import Motivic.Cohomology.A1.PresheafBoundaryEtaleExcision
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleSmoothNeighborhood

/-! # Actual marked cylinder restrictions under etale localization

The comparison uses the native marked-neighborhood slice and the actual
Cartesian puncture isomorphism. It applies to the original presheaf before
sheafification, and keeps the entire field-valued marking unchanged.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite

/-- The native marked-slice comparison is natural in the original presheaf
map. This is an equation of the actual point-fiber maps. -/
@[reassoc]
theorem fieldPointComposeFiberIso_hom_naturality {S : Scheme.{u}}
    (V : FiniteEtaleSite S) (K : Type u) [Field K] (b : Spec (.of K) ⟶ V.left)
    {P Q : (FiniteEtaleSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : P ⟶ Q) :
    (fieldPointComposeFiberIso V K b P).hom ≫
        (relativeFieldPoint (b ≫ V.hom) K (𝟙 _)).presheafFiber.map f =
      (relativeFieldPoint b K (𝟙 _)).presheafFiber.map
          (Functor.whiskerLeft (composeObjectFunctor V).op f) ≫
        (fieldPointComposeFiberIso V K b Q).hom := by
  apply (relativeFieldPoint b K (𝟙 _)).presheafFiber_hom_ext
  intro W w
  rw [toPresheafFiber_fieldPointComposeFiberIso_hom_assoc,
    GrothendieckTopology.Point.toPresheafFiber_naturality,
    GrothendieckTopology.Point.toPresheafFiber_naturality_assoc]
  change f.app (op (composeObject V W)) ≫ _ =
    f.app (op (composeObject V W)) ≫ _
  rw [toPresheafFiber_fieldPointComposeFiberIso_hom]

section Presheaf
variable {B : Scheme.{u}}
  (P : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  {U Y U' Y' : SmoothSite B}
  (j : U ⟶ Y) (p : Y' ⟶ Y) (j' : U' ⟶ Y') (q : U' ⟶ U)
  [Etale p.left] (hpb : IsPullback q j' j p)
  (K : Type u) [Field K] (b : Spec (.of K) ⟶ Y'.left)

/-- The actual source and puncture comparisons preserve the original
restriction map at the complete field-valued point. -/
theorem fieldPoint_etale_restriction_comparison :
    ((relativeFieldPoint b K (𝟙 _)).presheafFiber.map
        (presheafEtaleCoefficientIso P p).inv ≫
      (fieldPointComposeFiberIso (ofSmoothMap Y Y' p) K b
        ((toSmoothSite Y).op ⋙ P)).hom) ≫
        (relativeFieldPoint (b ≫ p.left) K (𝟙 _)).presheafFiber.map
          (presheafBoundaryRestriction P j) =
    (relativeFieldPoint b K (𝟙 _)).presheafFiber.map
        (presheafBoundaryRestriction P j') ≫
      ((relativeFieldPoint b K (𝟙 _)).presheafFiber.map
          (presheafEtalePuncturedCoefficientIso P j p j' q hpb).inv ≫
        (fieldPointComposeFiberIso (ofSmoothMap Y Y' p) K b
          ((baseChange j.left).op ⋙ (toSmoothSite U).op ⋙ P)).hom) := by
  let Ψ := relativeFieldPoint b K (𝟙 _)
  have h : (presheafEtaleCoefficientIso P p).inv ≫
      Functor.whiskerLeft (etalePostcompose p.left).op
        (presheafBoundaryRestriction P j) =
      presheafBoundaryRestriction P j' ≫
        (presheafEtalePuncturedCoefficientIso P j p j' q hpb).inv := by
    apply (cancel_mono (presheafEtalePuncturedCoefficientIso P j p j' q hpb).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [presheafEtaleCoefficient_restriction, Iso.inv_hom_id_assoc]
  rw [Category.assoc, fieldPointComposeFiberIso_hom_naturality]
  change Ψ.presheafFiber.map _ ≫ Ψ.presheafFiber.map _ ≫ _ = _
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]

include hpb in
/-- A genuine etale chart reflects monicity of the original puncture map on
the same full marked germ. The premise is a single map on the displayed
chart, not a supplied localization family. -/
theorem fieldPoint_presheafRestriction_mono_of_etale
    [Mono ((relativeFieldPoint b K (𝟙 _)).presheafFiber.map
      (presheafBoundaryRestriction P j'))] :
    Mono ((relativeFieldPoint (b ≫ p.left) K (𝟙 _)).presheafFiber.map
      (presheafBoundaryRestriction P j)) := by
  let e₀ := (relativeFieldPoint b K (𝟙 _)).presheafFiber.mapIso
      (presheafEtaleCoefficientIso P p).symm ≪≫
    fieldPointComposeFiberIso (ofSmoothMap Y Y' p) K b ((toSmoothSite Y).op ⋙ P)
  let e₁ := (relativeFieldPoint b K (𝟙 _)).presheafFiber.mapIso
      (presheafEtalePuncturedCoefficientIso P j p j' q hpb).symm ≪≫
    fieldPointComposeFiberIso (ofSmoothMap Y Y' p) K b
      ((baseChange j.left).op ⋙ (toSmoothSite U).op ⋙ P)
  have h : e₀.hom ≫ (relativeFieldPoint (b ≫ p.left) K (𝟙 _)).presheafFiber.map
        (presheafBoundaryRestriction P j) =
      (relativeFieldPoint b K (𝟙 _)).presheafFiber.map
        (presheafBoundaryRestriction P j') ≫ e₁.hom :=
    fieldPoint_etale_restriction_comparison P j p j' q hpb K b
  have hf : (relativeFieldPoint (b ≫ p.left) K (𝟙 _)).presheafFiber.map
        (presheafBoundaryRestriction P j) =
      e₀.inv ≫ (relativeFieldPoint b K (𝟙 _)).presheafFiber.map
        (presheafBoundaryRestriction P j') ≫ e₁.hom := by
    rw [← h, Iso.inv_hom_id_assoc]
  rw [hf]
  infer_instance

end Presheaf

/-- Specialization to the literal original whole-cylinder restriction. The
normal chart is chosen on the base before the homotopy cylinder is formed. -/
theorem fieldPoint_cylinderRestriction_mono_of_etale
    (R : CommRingCat.{u})
    (P : (SmoothSite (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    {U Y U' Y' : SmoothSite (Spec R)}
    (j : U ⟶ Y) (p : Y' ⟶ Y) (j' : U' ⟶ Y') (q : U' ⟶ U)
    [Etale p.left] (hpb : IsPullback q j' j p)
    (K : Type u) [Field K] (b : Spec (.of K) ⟶ Y'.left)
    [Mono (colim.map (pointedCylinderRestriction R j'
      (relativeFieldPoint b K (𝟙 _)) P))] :
    Mono (colim.map (pointedCylinderRestriction R j
      (relativeFieldPoint (b ≫ p.left) K (𝟙 _)) P)) :=
  fieldPoint_presheafRestriction_mono_of_etale
    ((SmoothSite.parameterProduct (SmoothSite.affineLine R)).op ⋙ P)
    j p j' q hpb K b

end Motivic.FiniteEtaleSite
