/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Relative.Basic
public import Motivic.Transfers.Presheaf.Contraction
public import Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.DegreeZero
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.FreeSheafMonomorphisms
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Motivic.Transfers.Sheaf.Basic

/-!
# The actual contraction inside relative degree-one Ext

The original contraction quotient maps injectively to relative degree-one
cohomology for the literal Laurent open in the affine-line cylinder. On a
Laurent section, this map is the standard signed degree-zero boundary after
the actual `zeroSections` comparison. Its image is exactly the kernel of the
relative-to-ordinary map.

The coefficient universe stays `u + 1`; the Ext universe `w` is independent.
Thus the map is a cross-universe additive homomorphism, and monicity is stated
as injectivity. No homotopy invariance, purity, or surjectivity onto the whole
relative cohomology group is assumed or asserted.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe w u

namespace AlgebraicGeometry.Scheme.SmoothSite
open _root_.CategoryTheory.Sheaf

/-- The original Laurent open stays mono after taking the literal cylinder product. -/
instance contractionOpen_mono (R : CommRingCat.{u}) (X : SmoothSite (Spec R)) :
    Mono (contractionOpen R X) := by
  have : Mono (torusInAffineLine R) :=
    Hypercohomology.smoothSite_mono_of_isOpenImmersion _
  constructor
  intro Z f g h
  apply product_hom_ext
  · simpa only [Category.assoc, contractionOpen, productMap_fst, Category.comp_id] using
      congrArg (fun e => e ≫ productFst X (affineLine R)) h
  · apply (cancel_mono (torusInAffineLine R)).mp
    simpa only [Category.assoc, contractionOpen, productMap_snd] using
      congrArg (fun e => e ≫ productSnd X (affineLine R)) h

end AlgebraicGeometry.Scheme.SmoothSite

namespace Motivic.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf

open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

variable {k : Type u} [Field k]
variable [HasExt.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable (F : SheafWithTransfers.{u + 1} k) (X : Cor k)

/-- Actual relative degree-one Ext for the original Laurent-open cylinder. -/
abbrev contractionRelativeH :=
  LargeCohomology.relativeH.{w, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
    (SmoothSite.contractionOpen (.of k) X.toSmoothSite) ((toSheaf k).obj F) 1

/-- The actual map forgetting the relative condition on the affine-line cylinder. -/
abbrev contractionRelativeForget :=
  LargeCohomology.relativeForget.{w, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
    (SmoothSite.contractionOpen (.of k) X.toSmoothSite) ((toSheaf k).obj F) 1

/-- The signed boundary on genuine Laurent sections, with independent Ext universe. -/
def contractionSectionBoundary : sections (torusSections F.obj) X →+
    contractionRelativeH F X :=
  (LargeCohomology.relativeBoundary.{w, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k)))
    (SmoothSite.contractionOpen (.of k) X.toSmoothSite) ((toSheaf k).obj F) 0).hom.comp
      (LargeCohomology.zeroSections.{w, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F)
        (SmoothSite.torusCylinder (.of k) X.toSmoothSite)).symm.toAddMonoidHom

private theorem zeroSections_symm_contractionRestriction
    (s : sections (affineLineSections F.obj) X) :
    (LargeCohomology.zeroSections.{w, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F)
      (SmoothSite.torusCylinder (.of k) X.toSmoothSite)).symm
        ((contractionRestriction F.obj).hom.app (op X) s) =
      (LargeCohomology.presheaf.{w, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) 0).map
        (SmoothSite.contractionOpen (.of k) X.toSmoothSite).op
        ((LargeCohomology.zeroSections.{w, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F)
          (SmoothSite.a1Cylinder (.of k) X.toSmoothSite)).symm s) := by
  apply (LargeCohomology.zeroSections _ _ _).injective
  rw [AddEquiv.apply_symm_apply, LargeCohomology.zeroSections_restriction,
    AddEquiv.apply_symm_apply]
  rfl

/-- The boundary uses exactly the negative extension class in degree zero. -/
theorem contractionSectionBoundary_apply (s : sections (torusSections F.obj) X) :
    contractionSectionBoundary F X s =
      -((LargeCohomology.relativeExtClass.{w, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
        (SmoothSite.contractionOpen (.of k) X.toSmoothSite)).comp
        ((LargeCohomology.zeroSections.{w, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F)
          (SmoothSite.torusCylinder (.of k) X.toSmoothSite)).symm s) (by decide)) := by
  change Int.negOnePow 1 • (_ : contractionRelativeH F X) = _
  simp only [Int.negOnePow_one, Units.smul_def, Units.val_neg, Units.val_one, neg_one_zsmul]
  rfl

/-- The original affine-line restriction is killed by the signed relative boundary. -/
theorem contractionSectionBoundary_restriction
    (s : sections (affineLineSections F.obj) X) :
    contractionSectionBoundary F X ((contractionRestriction F.obj).hom.app (op X) s) = 0 := by
  rw [contractionSectionBoundary_apply, zeroSections_symm_contractionRestriction]
  apply neg_eq_zero.mpr
  exact (LargeCohomology.relativePresentation_shortExact
    (SmoothSite.nisnevichTopology (Spec (.of k)))
    (SmoothSite.contractionOpen (.of k) X.toSmoothSite)).extClass_comp_assoc _

/-- Its kernel is precisely the image defining the actual contraction quotient. -/
theorem contractionSectionBoundary_eq_zero_iff (s : sections (torusSections F.obj) X) :
    contractionSectionBoundary F X s = 0 ↔
      ∃ t : sections (affineLineSections F.obj) X,
        (contractionRestriction F.obj).hom.app (op X) t = s := by
  constructor
  · intro hs
    obtain ⟨y, hy⟩ := LargeCohomology.restriction_lift_of_relativeBoundary_zero
      (SmoothSite.nisnevichTopology (Spec (.of k)))
      (SmoothSite.contractionOpen (.of k) X.toSmoothSite) ((toSheaf k).obj F) 0
      ((LargeCohomology.zeroSections.{w, u + 1} _ _ _).symm s) hs
    refine ⟨LargeCohomology.zeroSections _ _ _ y, ?_⟩
    apply (LargeCohomology.zeroSections.{w, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F)
      (SmoothSite.torusCylinder (.of k) X.toSmoothSite)).symm.injective
    rw [zeroSections_symm_contractionRestriction, AddEquiv.symm_apply_apply]
    exact hy
  · rintro ⟨t, rfl⟩
    exact contractionSectionBoundary_restriction F X t

/-- Kernel equality for the original restriction and the signed section boundary. -/
theorem contractionRestriction_range_eq_boundary_ker :
    ((contractionRestriction F.obj).hom.app (op X)).hom.range =
      (contractionSectionBoundary F X).ker := by
  ext s
  exact (contractionSectionBoundary_eq_zero_iff F X s).symm

/-- The actual transfer quotient maps to relative Ext through its signed boundary. -/
def contractionToRelative : sections (contraction F.obj) X →+ contractionRelativeH F X :=
  (QuotientAddGroup.lift _ (contractionSectionBoundary F X)
    (contractionRestriction_range_eq_boundary_ker F X).le).comp
      (contractionSectionsIsoQuotient F.obj X).addCommGroupIsoToAddEquiv.toAddMonoidHom

/-- This cross-universe additive map is a monomorphism of groups. -/
theorem contractionToRelative_injective : Function.Injective (contractionToRelative F X) :=
  ((QuotientAddGroup.injective_lift_iff _ _
    (contractionRestriction_range_eq_boundary_ker F X).le).2
      (contractionRestriction_range_eq_boundary_ker F X)).comp
        (contractionSectionsIsoQuotient F.obj X).addCommGroupIsoToAddEquiv.injective

omit [HasExt.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
private theorem contractionSectionsIsoQuotient_toContraction
    (s : sections (torusSections F.obj) X) :
    (contractionSectionsIsoQuotient F.obj X).hom
        ((toContraction F.obj).hom.app (op X) s) =
      QuotientAddGroup.mk' ((contractionRestriction F.obj).hom.app (op X)).hom.range s := by
  have h : (toContraction F.obj).hom.app (op X) ≫
      (contractionSectionsIsoQuotient F.obj X).hom =
        AddCommGrpCat.ofHom (QuotientAddGroup.mk'
          ((contractionRestriction F.obj).hom.app (op X)).hom.range) := by
    exact (PreservesCokernel.π_iso_hom_assoc
      ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op X)) (contractionRestriction F.obj).hom
      (AddCommGrpCat.cokernelIsoQuotient
        ((contractionRestriction F.obj).hom.app (op X))).hom).trans (cokernel.π_desc _ _ _)
  exact ConcreteCategory.congr_hom h s

/-- The descended map retains the original quotient representatives and boundary. -/
theorem contractionToRelative_toContraction (s : sections (torusSections F.obj) X) :
    contractionToRelative F X ((toContraction F.obj).hom.app (op X) s) =
      contractionSectionBoundary F X s := by
  change QuotientAddGroup.lift _ _ (contractionRestriction_range_eq_boundary_ker F X).le
    ((contractionSectionsIsoQuotient F.obj X).hom
      ((toContraction F.obj).hom.app (op X) s)) = _
  rw [contractionSectionsIsoQuotient_toContraction]
  rfl

/-- Forgetting the relative condition kills the signed boundary of every Laurent section. -/
theorem contractionRelativeForget_sectionBoundary (s : sections (torusSections F.obj) X) :
    contractionRelativeForget F X (contractionSectionBoundary F X s) = 0 := by
  rw [contractionSectionBoundary_apply, map_neg]
  apply neg_eq_zero.mpr
  exact (LargeCohomology.relativePresentation_shortExact
    (SmoothSite.nisnevichTopology (Spec (.of k)))
    (SmoothSite.contractionOpen (.of k) X.toSmoothSite)).comp_extClass_assoc _ _

/-- Every actual contraction class maps into the kernel of forgetting the relative condition. -/
theorem contractionRelativeForget_toRelative (c : sections (contraction F.obj) X) :
    contractionRelativeForget F X (contractionToRelative F X c) = 0 := by
  obtain ⟨s, rfl⟩ := toContraction_surjective F.obj X c
  rw [contractionToRelative_toContraction]
  exact contractionRelativeForget_sectionBoundary F X s

/-- The image is exactly the kernel, without claiming all relative degree-one Ext is reached. -/
theorem contractionToRelative_mem_range_iff (z : contractionRelativeH F X) :
    z ∈ (contractionToRelative F X).range ↔ contractionRelativeForget F X z = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    exact contractionRelativeForget_toRelative F X c
  · intro hz
    obtain ⟨x, hx⟩ := LargeCohomology.relativeBoundary_lift_of_forget_zero
      (SmoothSite.nisnevichTopology (Spec (.of k)))
      (SmoothSite.contractionOpen (.of k) X.toSmoothSite) ((toSheaf k).obj F) 0 z hz
    refine ⟨(toContraction F.obj).hom.app (op X)
      (LargeCohomology.zeroSections _ _ _ x), ?_⟩
    rw [contractionToRelative_toContraction]
    change LargeCohomology.relativeBoundary _ _ _ 0
      ((LargeCohomology.zeroSections.{w, u + 1} _ _ _).symm
        (LargeCohomology.zeroSections _ _ _ x)) = z
    rw [AddEquiv.symm_apply_apply]
    exact hx

/-- Equality of the actual image subgroup and the actual relative-forget kernel. -/
theorem contractionToRelative_range :
    (contractionToRelative F X).range = (contractionRelativeForget F X).hom.ker := by
  ext z
  exact contractionToRelative_mem_range_iff F X z

end Motivic.SheafWithTransfers
