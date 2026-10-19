/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Field.Point.InverseImage
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Exact genuine small-site inverse image and injective direct image

Only inverse image is asserted exact for arbitrary scheme maps. Direct image
preserves injectives because its actual left adjoint preserves monomorphisms;
no exactness of arbitrary direct image or enough-injectives hypothesis is used.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S T : Scheme.{u}} (b : T ⟶ S)

/-- Pointwise Kan extension on the actual unequal-universe site categories. -/
def baseChangeLanEvaluationIso (V : (EtaleSeparatedFiniteType T)ᵒᵖ) :
    (baseChange b).op.lan ⋙ (_root_.CategoryTheory.evaluation (EtaleSeparatedFiniteType T)ᵒᵖ
        AddCommGrpCat.{u + 1}).obj V
        ≅
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
        (CostructuredArrow.proj (baseChange b).op V) ⋙ colim :=
  NatIso.ofComponents (fun P =>
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit (baseChange b).op P V)
      (colimit.isColimit _)) (fun {P Q} φ => by
        apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
          (baseChange b).op P V).hom_ext
        intro T
        have h₁ := fun (P : (EtaleSeparatedFiniteType S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) =>
          IsColimit.comp_coconePointUniqueUpToIso_hom
            (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
              (baseChange b).op P V) (colimit.isColimit _) T
        have h₂ := congr_app ((baseChange b).op.lanUnit.naturality φ) T.left
        dsimp at h₁ h₂ ⊢
        simp only [Category.assoc] at h₁ ⊢
        simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
        rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
          ι_colimMap, Functor.whiskerLeft_app]
        rfl)

instance baseChangeLan_preservesFiniteLimits :
    PreservesFiniteLimits
      ((baseChange b).op.lan : _ ⥤ (EtaleSeparatedFiniteType T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) := by
  let : AB5OfSize.{u, u + 1} AddCommGrpCat.{u + 1} :=
    AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} _
  apply preservesFiniteLimits_of_evaluation
  intro V
  have : IsFiltered (CostructuredArrow (baseChange b).op V) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (baseChange b) V.unop)
  exact preservesFiniteLimits_of_natIso (baseChangeLanEvaluationIso b V).symm

instance inverseImage_preservesFiniteLimits : PreservesFiniteLimits (inverseImage b) := by
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

instance inverseImage_preservesFiniteColimits : PreservesFiniteColimits (inverseImage b) := by
  have := (imageAdjunction b).isLeftAdjoint
  infer_instance

instance inverseImage_additive : (inverseImage b).Additive :=
  Functor.additive_of_preserves_binary_products _

instance directImage_preservesFiniteLimits : PreservesFiniteLimits (directImage b) := by
  have := (imageAdjunction b).isRightAdjoint
  infer_instance

instance directImage_additive : (directImage b).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The actual inverse image takes ordinary short exact sequences to short exact sequences. -/
theorem inverseImage_shortExact
    (D : ShortComplex (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}))
    (hD : D.ShortExact) : (D.map (inverseImage b)).ShortExact :=
  hD.map_of_exact (inverseImage b)

/-- Actual small-site direct image preserves an injective coefficient object. -/
instance directImage_obj_injective
    (I : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) [Injective I] :
    Injective ((directImage b).obj I) :=
  Injective.injective_of_adjoint (imageAdjunction b) I

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
