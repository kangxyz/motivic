/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Contraction.Relative

/-!
# Standard-Ext consumers of the actual contraction boundary

These consumers keep the original transfer quotient at coefficient universe
`u + 1`, and use the standard actual Ext instance at `u + 2`. They test the
negative boundary formula on original quotient representatives, injectivity,
and the exact image condition, without a homotopy-invariance hypothesis.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite Motivic

universe u

namespace MotivicTest.Cohomology.ContractionRelative

variable {k : Type u} [Field k]

local instance : HasExt.{u + 2}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasExt.standard _

variable (F : SheafWithTransfers.{u + 1} k) (X : Cor k)

/-- The literal Laurent open is mono, rather than an abstract replacement arrow. -/
example : Mono (SmoothSite.contractionOpen (.of k) X.toSmoothSite) := inferInstance

/-- The actual transfer contraction embeds in actual standard relative Ext. -/
theorem actual_contraction_injective :
    Function.Injective (SheafWithTransfers.contractionToRelative.{u + 2} F X) :=
  SheafWithTransfers.contractionToRelative_injective F X

/-- On original quotient representatives, the boundary is the negative extension class. -/
theorem actual_negative_boundary
    (s : PresheafWithTransfers.sections (PresheafWithTransfers.torusSections F.obj) X) :
    SheafWithTransfers.contractionToRelative.{u + 2} F X
        ((PresheafWithTransfers.toContraction F.obj).hom.app (op X) s) =
      -((_root_.CategoryTheory.Sheaf.LargeCohomology.relativeExtClass.{u + 2, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
        (SmoothSite.contractionOpen (.of k) X.toSmoothSite)).comp
        ((_root_.CategoryTheory.Sheaf.LargeCohomology.zeroSections.{u + 2, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf.{u + 1} k).obj F)
          (SmoothSite.torusCylinder (.of k) X.toSmoothSite)).symm s) (by decide)) := by
  rw [SheafWithTransfers.contractionToRelative_toContraction,
    SheafWithTransfers.contractionSectionBoundary_apply]

/-- The actual quotient image is exactly the kernel of forgetting the relative condition. -/
theorem actual_image_ker :
    (SheafWithTransfers.contractionToRelative.{u + 2} F X).range =
      (_root_.CategoryTheory.Sheaf.LargeCohomology.relativeForget.{u + 2, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
        (SmoothSite.contractionOpen (.of k) X.toSmoothSite)
        ((SheafWithTransfers.toSheaf.{u + 1} k).obj F) 1).hom.ker :=
  SheafWithTransfers.contractionToRelative_range F X

/-- A relative class has an original contraction representative precisely when it vanishes
under the actual quotient-induced Ext map to the affine-line cylinder. -/
theorem actual_representative_iff
    (z : SheafWithTransfers.contractionRelativeH.{u + 2} F X) :
    (∃ c : PresheafWithTransfers.sections (PresheafWithTransfers.contraction F.obj) X,
      SheafWithTransfers.contractionToRelative.{u + 2} F X c = z) ↔
      (Ext.mk₀ (_root_.CategoryTheory.Sheaf.LargeCohomology.relativeSourceπ.{u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
        (SmoothSite.contractionOpen (.of k) X.toSmoothSite))).comp z (zero_add 1) = 0 :=
  SheafWithTransfers.contractionToRelative_mem_range_iff F X z

end MotivicTest.Cohomology.ContractionRelative
