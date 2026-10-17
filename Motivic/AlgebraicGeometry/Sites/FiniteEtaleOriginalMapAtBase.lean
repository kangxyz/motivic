/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOriginalMapRecognition

/-! # The original restriction map at the actual small-site base object -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {B : Scheme.{u}} {X Y : SmoothSite B} (h : Y ⟶ X)

/-- Actual base change of the identity neighborhood is the identity neighborhood. -/
def baseChangeIdentityIso :
    (baseChange h.left).obj (identityObject X) ≅ identityObject Y :=
  ((identityObjectIsTerminal X).isTerminalObj (baseChange h.left) _).uniqueUpToIso
    (identityObjectIsTerminal Y)

/-- The geometric triangle is the original scheme morphism, not a replacement arrow. -/
theorem baseChangeIdentityIso_triangle :
    (restrictionProjection h).app (identityObject X) ≫ (identityImageIso X).hom =
      (toSmoothSite Y).map (baseChangeIdentityIso h).hom ≫
        (identityImageIso Y).hom ≫ h := by
  apply MorphismProperty.Over.Hom.ext
  have ht := MorphismProperty.Over.w (baseChangeIdentityIso h).hom
  change (baseChangeIdentityIso h).hom.left ≫ 𝟙 Y.left =
    pullback.snd (𝟙 X.left) h.left at ht
  change pullback.fst (𝟙 X.left) h.left ≫ 𝟙 X.left =
    (baseChangeIdentityIso h).hom.left ≫ 𝟙 Y.left ≫ h.left
  rw [← Category.assoc, ht]
  exact pullback.condition

/-- The geometric triangle induces the same original map on every additive presheaf. -/
theorem baseChangeIdentityIso_presheaf_triangle
    (P : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (x : P.obj (op X)) :
    P.map ((restrictionProjection h).app (identityObject X)).op
      (P.map (identityImageIso X).hom.op x) =
      P.map ((toSmoothSite Y).map (baseChangeIdentityIso h).hom).op
        (P.map (identityImageIso Y).hom.op (P.map h.op x)) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    baseChangeIdentityIso_triangle]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  rfl

variable [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1})]

/-- Original small-site restriction commutes with the original comparison. -/
theorem cohomologyRestrictionEquiv_restriction
    (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
    (n : ℕ) {U V : FiniteEtaleSite X.left} (f : U ⟶ V)
    (x : SheafCohomology.H.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology B) F n ((toSmoothSite X).obj V)) :
    cohomologyRestrictionEquiv X F n U
      ((SheafCohomology.presheaf (SmoothSite.nisnevichTopology B) F n).map
        ((toSmoothSite X).map f).op x) =
      (SheafCohomology.presheaf (nisnevichTopology X.left)
        ((restrict X AddCommGrpCat).obj F) n).map f.op
          (cohomologyRestrictionEquiv X F n V x) := by
  rw [cohomologyRestrictionEquiv_apply_source, cohomologyRestrictionEquiv_apply_source,
    SheafCohomology.restriction_apply, SheafCohomology.restriction_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by omega), Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by omega), Ext.mk₀_comp_mk₀]
  congr 2
  have hs := congrArg (((toSmoothSite X).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (nisnevichTopology X.left) (SmoothSite.nisnevichTopology B)).homEquiv _ _)
    (Hypercohomology.restrictionSourceIso_naturality.{u + 1, u, u + 1, u + 1}
      (nisnevichTopology X.left) (SmoothSite.nisnevichTopology B) (toSmoothSite X) f)
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at hs
  exact hs.symm

/-- The base comparison is precisely comparison after the original source isomorphism. -/
theorem cohomologyAtBaseEquiv_apply_restriction
    (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
    (n : ℕ) (x : SheafCohomology.H.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology B) F n X) :
    cohomologyAtBaseEquiv X F n x =
      cohomologyRestrictionEquiv X F n (identityObject X)
        ((SheafCohomology.presheaf (SmoothSite.nisnevichTopology B) F n).map
          (identityImageIso X).hom.op x) := rfl

omit [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})] in
/-- Terminal-object transport agrees with the literal original big-site restriction. -/
theorem cohomologyRestrictionEquiv_atBase_triangle
    (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
    (n : ℕ) (x : SheafCohomology.H.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology B) F n X) :
    cohomologyRestrictionEquiv Y F n ((baseChange h.left).obj (identityObject X))
      ((SheafCohomology.presheaf (SmoothSite.nisnevichTopology B) F n).map
        ((restrictionProjection h).app (identityObject X)).op
        ((SheafCohomology.presheaf (SmoothSite.nisnevichTopology B) F n).map
          (identityImageIso X).hom.op x)) =
      (SheafCohomology.presheaf (nisnevichTopology Y.left)
        ((restrict Y AddCommGrpCat).obj F) n).map (baseChangeIdentityIso h).hom.op
          (cohomologyAtBaseEquiv Y F n
            ((SheafCohomology.presheaf (SmoothSite.nisnevichTopology B) F n).map h.op x)) := by
  rw [baseChangeIdentityIso_presheaf_triangle]
  exact cohomologyRestrictionEquiv_restriction F n (baseChangeIdentityIso h).hom _

/-- The original restriction transported to the actual small-site terminal objects equals
literal coefficient restriction followed by the genuine ordinary edge map. -/
theorem ordinaryEdgeMap_atBase_originalRestriction
    (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
    (n : ℕ) (x : SheafCohomology.H.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology B) F n X) :
    ordinaryEdgeMap h.left (identityObject X) ((restrict Y AddCommGrpCat).obj F) n
      (((SheafCohomology.presheafFunctor (nisnevichTopology X.left) n).map
        (restrictionToDirectImage F h)).app (op (identityObject X))
          (cohomologyAtBaseEquiv X F n x)) =
      (SheafCohomology.presheaf (nisnevichTopology Y.left)
        ((restrict Y AddCommGrpCat).obj F) n).map (baseChangeIdentityIso h).hom.op
          (cohomologyAtBaseEquiv Y F n
            ((SheafCohomology.presheaf (SmoothSite.nisnevichTopology B) F n).map h.op x)) := by
  rw [cohomologyAtBaseEquiv_apply_restriction]
  exact (ordinaryEdgeMap_restrictionToDirectImage h F n (identityObject X) _).trans
    (cohomologyRestrictionEquiv_atBase_triangle h F n x)

end Motivic.FiniteEtaleSite
