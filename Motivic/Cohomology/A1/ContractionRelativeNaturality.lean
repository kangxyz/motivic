/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.ContractionRelative
public import Motivic.Cohomology.RelativeSheafCohomologyNaturality

/-!
# Naturality of the actual contraction boundary

The injection of the original transfer contraction into relative degree-one
Ext is natural in coefficient sheaves and in ordinary smooth-site maps. The
relative source map is the genuine map of free-sheaf cokernels induced by the
literal affine-line and Laurent-cylinder maps. Signed boundary naturality and
the actual degree-zero section comparison give the asserted equations.

No action of arbitrary finite correspondences on positive-degree ordinary
cohomology is asserted. The coefficient and Ext universes remain independent.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite

universe w u

namespace Motivic.SmoothSite

/-- The original Laurent opens commute with the actual product maps of cylinders. -/
theorem contractionOpen_naturality (R : CommRingCat.{u})
    {X Y : SmoothSite (Spec R)} (f : X ⟶ Y) :
    contractionOpen R X ≫ a1Map R f =
      productMap f (𝟙 (torus R)) ≫ contractionOpen R Y := by
  change productMap (𝟙 X) (torusInAffineLine R) ≫ productMap f (𝟙 _) =
    productMap f (𝟙 _) ≫ productMap (𝟙 Y) (torusInAffineLine R)
  rw [← productMap_comp, ← productMap_comp]
  simp only [Category.id_comp, Category.comp_id]

end Motivic.SmoothSite

namespace Motivic.SheafWithTransfers

open PresheafWithTransfers

variable {k : Type u} [Field k]
variable [HasExt.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Coefficient changes act by actual Ext postcomposition on the relative group. -/
abbrev contractionRelativeCoefficientMap {F G : SheafWithTransfers.{u + 1} k}
    (η : F ⟶ G) (X : Cor k) : contractionRelativeH F X ⟶ contractionRelativeH G X :=
  SheafCohomology.relativeCoefficientMap.{w, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k)))
    (SmoothSite.contractionOpen (.of k) X.toSmoothSite) ((toSheaf k).map η) 1

/-- Ordinary smooth-site maps induce actual Ext precomposition on relative cokernels. -/
abbrev contractionRelativeRestriction (F : SheafWithTransfers.{u + 1} k)
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    contractionRelativeH F (Cor.mk Y) ⟶ contractionRelativeH F (Cor.mk X) :=
  SheafCohomology.relativeRestriction.{w, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k)))
    (SmoothSite.contractionOpen (.of k) X) (SmoothSite.contractionOpen (.of k) Y)
    (SmoothSite.productMap f (𝟙 (SmoothSite.torus (.of k)))) (SmoothSite.a1Map (.of k) f)
    (SmoothSite.contractionOpen_naturality (.of k) f) ((toSheaf k).obj F) 1

private theorem zeroSections_symm_coefficient {F G : SheafWithTransfers.{u + 1} k}
    (η : F ⟶ G) (T : SmoothSite (Spec (.of k)))
    (s : sections F.obj (Cor.mk T)) :
    (SheafCohomology.zeroSections.{w, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj G) T).symm
      (η.hom.hom.app (op (Cor.mk T)) s) =
    ((SheafCohomology.presheafFunctor.{w, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) 0).map ((toSheaf k).map η)).app (op T)
      ((SheafCohomology.zeroSections.{w, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) T).symm s) := by
  apply (SheafCohomology.zeroSections _ _ _).injective
  rw [AddEquiv.apply_symm_apply, SheafCohomology.zeroSections_naturality,
    AddEquiv.apply_symm_apply]
  rfl

private theorem zeroSections_symm_restriction (F : SheafWithTransfers.{u + 1} k)
    {T T' : SmoothSite (Spec (.of k))} (f : T ⟶ T')
    (s : sections F.obj (Cor.mk T')) :
    (SheafCohomology.zeroSections.{w, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) T).symm
      (transfer F.obj ((Cor.graphFunctor k).map f) s) =
    (SheafCohomology.presheaf.{w, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) 0).map f.op
      ((SheafCohomology.zeroSections.{w, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) T').symm s) := by
  apply (SheafCohomology.zeroSections _ _ _).injective
  rw [AddEquiv.apply_symm_apply, SheafCohomology.zeroSections_restriction,
    AddEquiv.apply_symm_apply]
  rfl

/-- The signed boundary on Laurent sections is natural in the coefficient sheaf. -/
theorem contractionSectionBoundary_coefficient_naturality
    {F G : SheafWithTransfers.{u + 1} k} (η : F ⟶ G) (X : Cor k)
    (s : sections (torusSections F.obj) X) :
    contractionRelativeCoefficientMap η X (contractionSectionBoundary F X s) =
      contractionSectionBoundary G X
        (η.hom.hom.app (op (Cor.mk (SmoothSite.torusCylinder (.of k) X.toSmoothSite))) s) := by
  have h := SheafCohomology.relativeBoundary_coefficient.{w, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k)))
    (SmoothSite.contractionOpen (.of k) X.toSmoothSite) ((toSheaf k).map η) 0
    ((SheafCohomology.zeroSections.{w, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F)
      (SmoothSite.torusCylinder (.of k) X.toSmoothSite)).symm s)
  exact h.trans (congrArg (SheafCohomology.relativeBoundary.{w, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k)))
    (SmoothSite.contractionOpen (.of k) X.toSmoothSite) ((toSheaf k).obj G) 0)
    (zeroSections_symm_coefficient η _ s).symm)

/-- The signed boundary on Laurent sections respects the literal cylinder product square. -/
theorem contractionSectionBoundary_restriction_naturality
    (F : SheafWithTransfers.{u + 1} k) {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y)
    (s : sections (torusSections F.obj) (Cor.mk Y)) :
    contractionRelativeRestriction F f (contractionSectionBoundary F (Cor.mk Y) s) =
      contractionSectionBoundary F (Cor.mk X)
        (transfer F.obj ((Cor.graphFunctor k).map
          (SmoothSite.productMap f (𝟙 (SmoothSite.torus (.of k))))) s) := by
  have h := SheafCohomology.relativeBoundary_restriction.{w, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k)))
    (SmoothSite.contractionOpen (.of k) X) (SmoothSite.contractionOpen (.of k) Y)
    (SmoothSite.productMap f (𝟙 (SmoothSite.torus (.of k)))) (SmoothSite.a1Map (.of k) f)
    (SmoothSite.contractionOpen_naturality (.of k) f) ((toSheaf k).obj F) 0
    ((SheafCohomology.zeroSections.{w, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F)
      (SmoothSite.torusCylinder (.of k) Y)).symm s)
  exact h.trans (congrArg (SheafCohomology.relativeBoundary.{w, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k)))
    (SmoothSite.contractionOpen (.of k) X) ((toSheaf k).obj F) 0)
    (zeroSections_symm_restriction F _ s).symm)

/-- The original contraction quotient injection is natural in actual coefficient maps. -/
theorem contractionToRelative_coefficient_naturality
    {F G : SheafWithTransfers.{u + 1} k} (η : F ⟶ G) (X : Cor k)
    (c : sections (contraction F.obj) X) :
    contractionRelativeCoefficientMap η X (contractionToRelative F X c) =
      contractionToRelative G X ((contractionMap η.hom).hom.app (op X) c) := by
  obtain ⟨s, rfl⟩ := toContraction_surjective F.obj X c
  have h := ConcreteCategory.congr_hom
    (congrArg (fun θ => θ.hom.app (op X)) (toContraction_map η.hom)) s
  change (contractionMap η.hom).hom.app (op X) ((toContraction F.obj).hom.app (op X) s) =
    (toContraction G.obj).hom.app (op X)
      (η.hom.hom.app (op (Cor.mk (SmoothSite.torusCylinder (.of k) X.toSmoothSite))) s) at h
  rw [h, contractionToRelative_toContraction, contractionToRelative_toContraction]
  exact contractionSectionBoundary_coefficient_naturality η X s

/-- The injection commutes with genuine ordinary smooth-site restriction maps. -/
theorem contractionToRelative_restriction_naturality
    (F : SheafWithTransfers.{u + 1} k) {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y)
    (c : sections (contraction F.obj) (Cor.mk Y)) :
    contractionRelativeRestriction F f (contractionToRelative F (Cor.mk Y) c) =
      contractionToRelative F (Cor.mk X)
        (transfer (contraction F.obj) ((Cor.graphFunctor k).map f) c) := by
  obtain ⟨s, rfl⟩ := toContraction_surjective F.obj (Cor.mk Y) c
  rw [contraction_graph_apply, contractionToRelative_toContraction,
    contractionToRelative_toContraction]
  exact contractionSectionBoundary_restriction_naturality F f s

end Motivic.SheafWithTransfers
