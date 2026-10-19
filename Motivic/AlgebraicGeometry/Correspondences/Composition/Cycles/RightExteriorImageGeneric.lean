/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Image.Generic

/-!
# Generic points of the actual right exterior intermediate image

The original right support product maps through the first and second supports
and then through the first support times the original smooth middle scheme.
Both steps are Cartesian base changes of actual generator projections over
normal smooth schemes. The whole right image product is finite over that same
exterior base. Generalization lifting followed by quasi-finite reflection proves
that the actual intermediate image map preserves generic points. Neither the
first support nor its exterior product is assumed normal. All nilpotents,
components, and collisions are retained.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Products

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g)
  (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The first and second original supports, before the second pair incidence. -/
abbrev rightExteriorFirstSupportProduct : Scheme.{u} :=
  pullback (F.targetProjection ≫ g) (G.projection ≫ g)

/-- Forget the third support while retaining both original earlier supports. -/
def rightExteriorFirstSupportMap : F.rightIntermediateSupportProduct G H ⟶
    F.rightExteriorFirstSupportProduct G :=
  pullback.lift
    (pullback.fst (F.targetProjection ≫ g) (G.incidenceSource H ≫ g))
    (pullback.snd (F.targetProjection ≫ g) (G.incidenceSource H ≫ g) ≫
      G.incidenceFst H) (by
        simpa only [incidenceSource, Category.assoc] using
          (pullback.condition (f := F.targetProjection ≫ g)
            (g := G.incidenceSource H ≫ g)))

/-- The first support is unchanged in this first right factor. -/
@[reassoc (attr := simp)] theorem rightExteriorFirstSupportMap_fst :
    F.rightExteriorFirstSupportMap G H ≫
      pullback.fst (F.targetProjection ≫ g) (G.projection ≫ g) =
    pullback.fst (F.targetProjection ≫ g) (G.incidenceSource H ≫ g) :=
  pullback.lift_fst _ _ _

/-- The second support coordinate is the original pair incidence projection. -/
@[reassoc (attr := simp)] theorem rightExteriorFirstSupportMap_snd :
    F.rightExteriorFirstSupportMap G H ≫
      pullback.snd (F.targetProjection ≫ g) (G.projection ≫ g) =
    pullback.snd (F.targetProjection ≫ g) (G.incidenceSource H ≫ g) ≫
      G.incidenceFst H :=
  pullback.lift_snd _ _ _

/-- The first right factor is Cartesian over the original second support. -/
theorem rightExteriorFirstSupportMap_pair_isPullback :
    IsPullback (F.rightExteriorFirstSupportMap G H)
      (pullback.snd (F.targetProjection ≫ g) (G.incidenceSource H ≫ g))
      (pullback.snd (F.targetProjection ≫ g) (G.projection ≫ g))
      (G.incidenceFst H) := by
  apply IsPullback.flip
  refine IsPullback.of_bot
    (t := (IsPullback.of_hasPullback (F.targetProjection ≫ g)
      (G.projection ≫ g)).flip) ?_
    (F.rightExteriorFirstSupportMap_snd G H).symm
  simpa only [F.rightExteriorFirstSupportMap_fst G H, incidenceSource,
    Category.assoc] using
    (IsPullback.of_hasPullback (F.targetProjection ≫ g)
      (G.incidenceSource H ≫ g)).flip

/-- The first right factor is the actual base change of the third generator
projection over its original smooth source. -/
theorem rightExteriorFirstSupportMap_isPullback :
    IsPullback (F.rightExteriorFirstSupportMap G H)
      (pullback.snd (F.targetProjection ≫ g) (G.incidenceSource H ≫ g) ≫
        G.incidenceSnd H)
      (pullback.snd (F.targetProjection ≫ g) (G.projection ≫ g) ≫
        G.targetProjection)
      H.projection :=
  (F.rightExteriorFirstSupportMap_pair_isPullback G H).paste_vert
    (IsPullback.of_hasPullback G.targetProjection H.projection)

/-- Replace the second support by its original source, keeping the first support. -/
def rightExteriorFirstSourceMap : F.rightExteriorFirstSupportProduct G ⟶
    pullback (F.targetProjection ≫ g) g :=
  pullback.lift
    (pullback.fst (F.targetProjection ≫ g) (G.projection ≫ g))
    (pullback.snd (F.targetProjection ≫ g) (G.projection ≫ g) ≫ G.projection) (by
      simpa only [Category.assoc] using
        (pullback.condition (f := F.targetProjection ≫ g) (g := G.projection ≫ g)))

/-- The first support is unchanged in the second right factor. -/
@[reassoc (attr := simp)] theorem rightExteriorFirstSourceMap_fst :
    F.rightExteriorFirstSourceMap G ≫ pullback.fst (F.targetProjection ≫ g) g =
    pullback.fst (F.targetProjection ≫ g) (G.projection ≫ g) :=
  pullback.lift_fst _ _ _

/-- The second right factor uses the original second generator projection. -/
@[reassoc (attr := simp)] theorem rightExteriorFirstSourceMap_snd :
    F.rightExteriorFirstSourceMap G ≫ pullback.snd (F.targetProjection ≫ g) g =
    pullback.snd (F.targetProjection ≫ g) (G.projection ≫ g) ≫ G.projection :=
  pullback.lift_snd _ _ _

/-- The second right factor is Cartesian over the original first middle scheme. -/
theorem rightExteriorFirstSourceMap_isPullback :
    IsPullback (F.rightExteriorFirstSourceMap G)
      (pullback.snd (F.targetProjection ≫ g) (G.projection ≫ g))
      (pullback.snd (F.targetProjection ≫ g) g) G.projection := by
  apply IsPullback.flip
  refine IsPullback.of_bot
    (t := (IsPullback.of_hasPullback (F.targetProjection ≫ g) g).flip) ?_
    (F.rightExteriorFirstSourceMap_snd G).symm
  simpa only [F.rightExteriorFirstSourceMap_fst G] using
    (IsPullback.of_hasPullback (F.targetProjection ≫ g) (G.projection ≫ g)).flip

/-- The whole right support product projects to the first-support exterior base. -/
abbrev rightExteriorSourceMap : F.rightIntermediateSupportProduct G H ⟶
    pullback (F.targetProjection ≫ g) g :=
  F.rightExteriorFirstSupportMap G H ≫ F.rightExteriorFirstSourceMap G

/-- The whole right image product projects to the same exterior base, using its
actual scheme-image inclusion and retaining its possibly nonreduced structure. -/
def rightExteriorImageSourceMap : F.rightIntermediateImageProduct G H ⟶
    pullback (F.targetProjection ≫ g) g :=
  pullback.lift
    (pullback.fst (F.targetProjection ≫ g)
      ((G.incidenceMap H).imageι ≫ pullback.fst g i ≫ g))
    (pullback.snd (F.targetProjection ≫ g)
      ((G.incidenceMap H).imageι ≫ pullback.fst g i ≫ g) ≫
      (G.incidenceMap H).imageι ≫ pullback.fst g i) (by
        simpa only [Category.assoc] using
          (pullback.condition (f := F.targetProjection ≫ g)
            (g := (G.incidenceMap H).imageι ≫ pullback.fst g i ≫ g)))

/-- The image projection leaves the original first support unchanged. -/
@[reassoc (attr := simp)] theorem rightExteriorImageSourceMap_fst :
    F.rightExteriorImageSourceMap G H ≫ pullback.fst (F.targetProjection ≫ g) g =
    pullback.fst (F.targetProjection ≫ g)
      ((G.incidenceMap H).imageι ≫ pullback.fst g i ≫ g) :=
  pullback.lift_fst _ _ _

/-- The exterior source coordinate uses the literal whole image inclusion. -/
@[reassoc (attr := simp)] theorem rightExteriorImageSourceMap_snd :
    F.rightExteriorImageSourceMap G H ≫ pullback.snd (F.targetProjection ≫ g) g =
    pullback.snd (F.targetProjection ≫ g)
      ((G.incidenceMap H).imageι ≫ pullback.fst g i ≫ g) ≫
      (G.incidenceMap H).imageι ≫ pullback.fst g i :=
  pullback.lift_snd _ _ _

/-- This actual image projection is a base change of the finite source projection
of the whole second pair scheme image. -/
theorem rightExteriorImageSourceMap_isPullback :
    IsPullback (F.rightExteriorImageSourceMap G H)
      (pullback.snd (F.targetProjection ≫ g)
        ((G.incidenceMap H).imageι ≫ pullback.fst g i ≫ g))
      (pullback.snd (F.targetProjection ≫ g) g)
      ((G.incidenceMap H).imageι ≫ pullback.fst g i) := by
  apply IsPullback.flip
  refine IsPullback.of_bot
    (t := (IsPullback.of_hasPullback (F.targetProjection ≫ g) g).flip) ?_
    (F.rightExteriorImageSourceMap_snd G H).symm
  simpa only [F.rightExteriorImageSourceMap_fst G H, Category.assoc] using
    (IsPullback.of_hasPullback (F.targetProjection ≫ g)
      ((G.incidenceMap H).imageι ≫ pullback.fst g i ≫ g)).flip

/-- The genuine intermediate image map commutes with the two constructed source
projections as a literal equality of scheme morphisms. -/
@[reassoc (attr := simp)] theorem rightIntermediateImageMap_source :
    F.rightIntermediateImageMap G H ≫ F.rightExteriorImageSourceMap G H =
      F.rightExteriorSourceMap G H := by
  apply pullback.hom_ext
  · simp only [Category.assoc, rightExteriorImageSourceMap_fst,
      rightIntermediateImageMap_fst, rightExteriorSourceMap,
      rightExteriorFirstSourceMap_fst, rightExteriorFirstSupportMap_fst]
  · simp only [Category.assoc, rightExteriorImageSourceMap_snd,
      rightIntermediateImageMap_snd_assoc, Scheme.Hom.toImage_imageι_assoc,
      incidenceMap_fst, rightExteriorSourceMap, rightExteriorFirstSourceMap_snd,
      rightExteriorFirstSupportMap_snd_assoc, incidenceSource]

section SmoothSite

variable (k : Type u) [Field k]
  {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The test map to the third smooth object is locally finite type. Only actual
support structure maps and the original second target projection are used. -/
theorem locallyOfFiniteType_rightExteriorFirstSupportTarget :
    LocallyOfFiniteType
      (pullback.snd (F.targetProjection ≫ Y.hom) (G.projection ≫ Y.hom) ≫
        G.targetProjection) := by
  have := F.locallyOfFiniteType_targetProjection (S := Spec (.of k))
  have := G.locallyOfFiniteType_targetProjection (S := Spec (.of k))
  infer_instance

/-- Generalization lifting for the first right factor uses normality of Z,
without normality of either support or of their exterior product. -/
theorem generalizingMap_rightExteriorFirstSupportMap :
    GeneralizingMap (F.rightExteriorFirstSupportMap G H) := by
  have := F.locallyOfFiniteType_rightExteriorFirstSupportTarget k G
  have : IsNoetherian ((𝟭 Scheme).obj Z.left) :=
    inferInstanceAs (IsNoetherian Z.left)
  exact generalizingMap_of_isPullback_component _ _ _ _
    (F.rightExteriorFirstSupportMap_isPullback G H) H.range_projection_mem
    (fun z ↦ ⟨SmoothSite.isDomain_stalk k Z z,
      SmoothSite.isIntegrallyClosed_stalk k Z z⟩)

/-- The second test map is the actual base change of the first support's
finite-type structure map to the base field. -/
theorem locallyOfFiniteType_rightExteriorSourceProjection :
    LocallyOfFiniteType (pullback.snd (F.targetProjection ≫ Y.hom) Y.hom) := by
  have := F.locallyOfFiniteType_targetProjection (S := Spec (.of k))
  infer_instance

/-- Generalization lifting for the second right factor uses normality of Y,
not normality of the first support or of its product with Y. -/
theorem generalizingMap_rightExteriorFirstSourceMap :
    GeneralizingMap (F.rightExteriorFirstSourceMap G) := by
  have := F.locallyOfFiniteType_rightExteriorSourceProjection k
  have : IsNoetherian ((𝟭 Scheme).obj Y.left) :=
    inferInstanceAs (IsNoetherian Y.left)
  exact generalizingMap_of_isPullback_component _ _ _ _
    (F.rightExteriorFirstSourceMap_isPullback G) G.range_projection_mem
    (fun y ↦ ⟨SmoothSite.isDomain_stalk k Y y,
      SmoothSite.isIntegrallyClosed_stalk k Y y⟩)

/-- The whole right support projection is generalizing by the two actual
component-normal Cartesian base changes. -/
theorem generalizingMap_rightExteriorSourceMap :
    GeneralizingMap (F.rightExteriorSourceMap G H) :=
  (F.generalizingMap_rightExteriorFirstSupportMap k G H).comp
    (F.generalizingMap_rightExteriorFirstSourceMap k G)

/-- Every right exterior source generic dominates a genuine exterior base generic. -/
theorem rightExteriorSourceMap_mem_genericPoints
    (w : F.rightIntermediateSupportProduct G H)
    (hw : w ∈ genericPoints (F.rightIntermediateSupportProduct G H)) :
    F.rightExteriorSourceMap G H w ∈
      genericPoints (pullback (F.targetProjection ≫ Y.hom) Y.hom : Scheme.{u}) :=
  mem_genericPoints_of_generalizing _ (F.generalizingMap_rightExteriorSourceMap k G H) w hw

/-- The whole right intermediate image product is finite over the same exterior
base, by the actual finite second-pair image projection. -/
theorem isFinite_rightExteriorImageSourceMap :
    IsFinite (F.rightExteriorImageSourceMap G H) := by
  have := G.isFinite_incidenceImageProjection k H
  exact MorphismProperty.of_isPullback
    (F.rightExteriorImageSourceMap_isPullback G H).flip inferInstance

/-- The actual right whole intermediate image map preserves generic points.
No injectivity of components, separability, reduction, or flatness of the
correspondence supports is required. -/
theorem rightIntermediateImageMap_mem_genericPoints
    (w : F.rightIntermediateSupportProduct G H)
    (hw : w ∈ genericPoints (F.rightIntermediateSupportProduct G H)) :
    F.rightIntermediateImageMap G H w ∈ genericPoints (F.rightIntermediateImageProduct G H) := by
  have := F.isFinite_rightExteriorImageSourceMap k G H
  apply mem_genericPoints_of_image_generic (F.rightExteriorImageSourceMap G H)
  change (F.rightIntermediateImageMap G H ≫ F.rightExteriorImageSourceMap G H) w ∈ _
  rw [F.rightIntermediateImageMap_source G H]
  exact F.rightExteriorSourceMap_mem_genericPoints k G H w hw

end SmoothSite

end Motivic.FiniteCorrespondenceGenerator
