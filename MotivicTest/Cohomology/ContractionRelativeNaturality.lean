/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Contraction.RelativeNaturality

/-!
# Direct Ext consumers of contraction-boundary naturality

The coefficient action is written as actual Ext postcomposition, and ordinary
restriction as actual Ext precomposition with the map of relative free-sheaf
cokernels. These consumers use the standard Ext instance, the original
coefficient universe and the literal transfer contraction maps.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite Motivic

universe u

namespace MotivicTest.Cohomology.ContractionRelativeNaturality

variable {k : Type u} [Field k]

local instance : HasExt.{u + 2}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasExt.standard _

/-- Actual Ext postcomposition commutes with the original coefficient contraction map. -/
theorem actual_ext_coefficient_naturality {F G : SheafWithTransfers.{u + 1} k}
    (η : F ⟶ G) (X : Cor k)
    (c : PresheafWithTransfers.sections (PresheafWithTransfers.contraction F.obj) X) :
    (SheafWithTransfers.contractionToRelative.{u + 2} F X c).comp
        (Ext.mk₀ ((SheafWithTransfers.toSheaf.{u + 1} k).map η)) (add_zero 1) =
      SheafWithTransfers.contractionToRelative.{u + 2} G X
        ((PresheafWithTransfers.contractionMap η.hom).hom.app (op X) c) :=
  SheafWithTransfers.contractionToRelative_coefficient_naturality η X c

/-- Actual Ext precomposition uses the genuine map of the original relative cokernels. -/
theorem actual_ext_restriction_naturality (F : SheafWithTransfers.{u + 1} k)
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y)
    (c : PresheafWithTransfers.sections (PresheafWithTransfers.contraction F.obj) (Cor.mk Y)) :
    (Ext.mk₀ (_root_.CategoryTheory.Sheaf.LargeCohomology.relativeSourceMap.{u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
      (SmoothSite.contractionOpen (.of k) X) (SmoothSite.contractionOpen (.of k) Y)
      (SmoothSite.productMap f (𝟙 (SmoothSite.torus (.of k)))) (SmoothSite.a1Map (.of k) f)
      (SmoothSite.contractionOpen_naturality (.of k) f))).comp
        (SheafWithTransfers.contractionToRelative.{u + 2} F (Cor.mk Y) c) (zero_add 1) =
      SheafWithTransfers.contractionToRelative.{u + 2} F (Cor.mk X)
        (PresheafWithTransfers.transfer (PresheafWithTransfers.contraction F.obj)
          ((Cor.graphFunctor k).map f) c) :=
  SheafWithTransfers.contractionToRelative_restriction_naturality F f c

/-- The section boundary itself is natural, before passage to the literal quotient. -/
theorem actual_signed_boundary_coefficient {F G : SheafWithTransfers.{u + 1} k}
    (η : F ⟶ G) (X : Cor k)
    (s : PresheafWithTransfers.sections (PresheafWithTransfers.torusSections F.obj) X) :
    (SheafWithTransfers.contractionSectionBoundary.{u + 2} F X s).comp
        (Ext.mk₀ ((SheafWithTransfers.toSheaf.{u + 1} k).map η)) (add_zero 1) =
      SheafWithTransfers.contractionSectionBoundary.{u + 2} G X
        (η.hom.hom.app (op (Cor.mk (SmoothSite.torusCylinder (.of k) X.toSmoothSite))) s) :=
  SheafWithTransfers.contractionSectionBoundary_coefficient_naturality η X s

#print axioms actual_ext_coefficient_naturality
#print axioms actual_ext_restriction_naturality

end MotivicTest.Cohomology.ContractionRelativeNaturality
