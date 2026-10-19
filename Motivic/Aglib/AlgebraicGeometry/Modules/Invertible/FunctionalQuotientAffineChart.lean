/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.FunctionalRatio
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.IdealFrameBoundaryScalar
public import Mathlib.AlgebraicGeometry.AffineScheme
/-! # Original functional quotients under affine chart identification

The original module functionals and their literal pullbacks are retained. The
canonical affine chart changes only the coordinate ring through the existing
`topIso` and `ΓSpecIso`; it does not dualize an independently pulled section.

Intended upstream module:
`Aglib.AlgebraicGeometry.Modules.Invertible.FunctionalQuotientAffineChart`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`GenericFiber.LineRatioIdentity`, `GenericFiber.LineRatioIso`,
`Correction.FunctionalUnitBoundary`, `Correction.OriginalCorrectionInfinityUnits`,
`Norm.SectionPairNormNeighborhood`, `Norm.SectionPairTargetGenericRatio`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- A further pullback of an actual invertible local functional is invertible. -/
theorem pullbackUnitMap_comp_isIso_of_first
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) {M : X.Modules}
    (c : M ⟶ SheafOfModules.unit X.ringCatSheaf) [IsIso (pullbackUnitMap f c)] :
    IsIso (pullbackUnitMap (g ≫ f) c) := by
  have h : pullbackUnitMap (g ≫ f) c =
      ((Modules.pullbackComp g f).app M).inv ≫ pullbackUnitMap g (pullbackUnitMap f c) := by
    rw [← pullbackUnitMap_comp, Iso.inv_hom_id_assoc]
  rw [h]
  change IsIso (((Modules.pullbackComp g f).app M).inv ≫
    (Modules.pullback g).map (pullbackUnitMap f c) ≫ (pullbackUnitIso g).hom)
  infer_instance

/-- A denominator unit on the actual nested chart is a unit on the composite chart.
No invertibility on the intermediate parameter space is required. -/
theorem pullbackUnitMap_comp_isIso_of_nested
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) {M : X.Modules}
    (c : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso (pullbackUnitMap g (pullbackUnitMap f c))] :
    IsIso (pullbackUnitMap (g ≫ f) c) := by
  have h : pullbackUnitMap (g ≫ f) c =
      ((Modules.pullbackComp g f).app M).inv ≫ pullbackUnitMap g (pullbackUnitMap f c) := by
    rw [← pullbackUnitMap_comp, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- The pullback-composition isomorphism preserves invertibility in the other presentation. -/
theorem pullbackUnitMap_nested_isIso_of_comp
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) {M : X.Modules}
    (c : M ⟶ SheafOfModules.unit X.ringCatSheaf) [IsIso (pullbackUnitMap (g ≫ f) c)] :
    IsIso (pullbackUnitMap g (pullbackUnitMap f c)) := by
  rw [← pullbackUnitMap_comp]
  infer_instance

/-- The original quotient commutes with further pullback, without replacing its functionals. -/
theorem functionalQuotient_pullback
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) {M : X.Modules}
    (a c : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso (pullbackUnitMap f c)] [IsIso (pullbackUnitMap (g ≫ f) c)] :
    Hom.unitEndomorphismPullback g
      (inv (pullbackUnitMap f c) ≫ pullbackUnitMap f a) =
      inv (pullbackUnitMap (g ≫ f) c) ≫ pullbackUnitMap (g ≫ f) a := by
  apply functionalQuotient_boundary_of_equation f g a c
  rw [IsIso.hom_inv_id_assoc]

/-- Pulling the original functionals first by a parameter map gives exactly the
same quotient as their literal composite pullback, including all canonical comparisons. -/
theorem functionalQuotient_comp
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) {M : X.Modules}
    (a c : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso (pullbackUnitMap (g ≫ f) c)] :
    let := pullbackUnitMap_nested_isIso_of_comp f g c
    inv (pullbackUnitMap g (pullbackUnitMap f c)) ≫
      pullbackUnitMap g (pullbackUnitMap f a) =
      inv (pullbackUnitMap (g ≫ f) c) ≫ pullbackUnitMap (g ≫ f) a := by
  let := pullbackUnitMap_nested_isIso_of_comp f g c
  dsimp only
  apply (cancel_epi (pullbackUnitMap g (pullbackUnitMap f c))).mp
  rw [IsIso.hom_inv_id_assoc]
  rw [← pullbackUnitMap_comp g f c, Category.assoc, IsIso.hom_inv_id_assoc]
  exact (pullbackUnitMap_comp g f a).symm

/-- The canonical affine Spec chart inherits the original open's denominator unit. -/
theorem pullbackUnitMap_fromSpec_isIso
    {X : Scheme.{u}} {M : X.Modules}
    (c : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opens) (hU : IsAffineOpen U) [IsIso (pullbackUnitMap U.ι c)] :
    IsIso (pullbackUnitMap hU.fromSpec c) := by
  change IsIso (pullbackUnitMap (hU.isoSpec.inv ≫ U.ι) c)
  exact pullbackUnitMap_comp_isIso_of_first U.ι hU.isoSpec.inv c

/-- The scalar on the canonical Spec chart is literally the scalar transported
by `topIso` from the original open, not merely a section with the same germ. -/
theorem functionalQuotient_fromSpec_coefficient
    {X : Scheme.{u}} {M : X.Modules}
    (a c : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opens) (hU : IsAffineOpen U) [IsIso (pullbackUnitMap U.ι c)] :
    let := pullbackUnitMap_fromSpec_isIso c U hU
    (Scheme.ΓSpecIso Γ(X, U)).hom (Modules.Hom.app
      (inv (pullbackUnitMap hU.fromSpec c) ≫ pullbackUnitMap hU.fromSpec a) ⊤
        (1 : Γ(Spec Γ(X, U), ⊤))) =
      U.topIso.hom (Modules.Hom.app
        (inv (pullbackUnitMap U.ι c) ≫ pullbackUnitMap U.ι a) ⊤
          (1 : Γ(U.toScheme, ⊤))) := by
  let := pullbackUnitMap_fromSpec_isIso c U hU
  let := pullbackUnitMap_comp_isIso_of_first U.ι hU.isoSpec.inv c
  dsimp only
  have h := congrArg (fun l : SheafOfModules.unit (Spec Γ(X, U)).ringCatSheaf ⟶
      SheafOfModules.unit (Spec Γ(X, U)).ringCatSheaf =>
        (show Γ(Spec Γ(X, U), ⊤) from
          Modules.Hom.app l ⊤ (1 : Γ(Spec Γ(X, U), ⊤))))
    (functionalQuotient_pullback U.ι hU.isoSpec.inv a c)
  have hs := (Hom.unitEndomorphismPullback_app_one hU.isoSpec.inv
    (inv (pullbackUnitMap U.ι c) ≫ pullbackUnitMap U.ι a)).symm.trans h
  dsimp only [IsAffineOpen.fromSpec]
  refine (congrArg (fun x : Γ(Spec Γ(X, U), ⊤) =>
    (Scheme.ΓSpecIso Γ(X, U)).hom x) hs.symm).trans ?_
  rw [hU.isoSpec_inv_appTop]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]

/-- The affine coefficient comparison also keeps a prior original parameter
pullback literal; no canonical dual of a pulled section is substituted. -/
theorem functionalQuotient_parameter_fromSpec_coefficient
    {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules}
    (a c : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U : Y.Opens) (hU : IsAffineOpen U)
    [IsIso (pullbackUnitMap (U.ι ≫ f) c)]
    [IsIso (pullbackUnitMap (hU.fromSpec ≫ f) c)] :
    let := pullbackUnitMap_nested_isIso_of_comp f U.ι c
    (Scheme.ΓSpecIso Γ(Y, U)).hom (Modules.Hom.app
      (inv (pullbackUnitMap (hU.fromSpec ≫ f) c) ≫
        pullbackUnitMap (hU.fromSpec ≫ f) a) ⊤ (1 : Γ(Spec Γ(Y, U), ⊤))) =
      U.topIso.hom (Modules.Hom.app
        (inv (pullbackUnitMap U.ι (pullbackUnitMap f c)) ≫
          pullbackUnitMap U.ι (pullbackUnitMap f a)) ⊤
            (1 : Γ(U.toScheme, ⊤))) := by
  let := pullbackUnitMap_nested_isIso_of_comp f U.ι c
  let := pullbackUnitMap_nested_isIso_of_comp f hU.fromSpec c
  dsimp only
  rw [← functionalQuotient_comp f hU.fromSpec a c]
  exact functionalQuotient_fromSpec_coefficient (pullbackUnitMap f a) (pullbackUnitMap f c) U hU

end AlgebraicGeometry.Scheme.Modules.Invertible
