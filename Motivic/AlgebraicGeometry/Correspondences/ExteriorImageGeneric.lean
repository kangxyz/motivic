/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleGenericDominance
public import Motivic.AlgebraicGeometry.Correspondences.IteratedIncidenceSupport

/-!
# Generic points of the actual exterior intermediate image

The actual map from pair incidence times the third support to its whole
intermediate scheme image times the third support sends generic points to
generic points. This is not a generic-preservation assertion for arbitrary
finite maps. The exterior source projection factors into two actual finite
base changes of the original generators over normal smooth components.
Their finite-type test maps give genuine generalization lifting. The whole
image product is finite over the exterior source, so quasi-finite reflection
then gives the desired genericity, retaining nilpotents and collisions.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g)
  (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The first and third original support schemes, before either diagonal. -/
abbrev leftExteriorFirstSupportProduct : Scheme.{u} :=
  pullback (F.projection ≫ f) (H.projection ≫ h)

/-- The actual exterior incidence projection to the first support product. -/
def leftExteriorFirstSupportMap : F.leftIntermediateSupportProduct G H ⟶
    F.leftExteriorFirstSupportProduct H :=
  pullback.lift
    (pullback.fst (F.incidenceTarget G ≫ h) (H.projection ≫ h) ≫ F.incidenceFst G)
    (pullback.snd (F.incidenceTarget G ≫ h) (H.projection ≫ h)) (by
      have hb : F.incidenceFst G ≫ (F.projection ≫ f) = F.incidenceTarget G ≫ h := by
        simpa only [incidenceSource, Category.assoc] using F.incidence_base G
      simpa only [Category.assoc, hb] using
        (pullback.condition (f := F.incidenceTarget G ≫ h) (g := H.projection ≫ h)))

/-- The first-support projection retains the original incidence first projection. -/
@[reassoc (attr := simp)] theorem leftExteriorFirstSupportMap_fst :
    F.leftExteriorFirstSupportMap G H ≫
      pullback.fst (F.projection ≫ f) (H.projection ≫ h) =
    pullback.fst (F.incidenceTarget G ≫ h) (H.projection ≫ h) ≫ F.incidenceFst G :=
  pullback.lift_fst _ _ _

/-- The third support is unchanged by the first-support projection. -/
@[reassoc (attr := simp)] theorem leftExteriorFirstSupportMap_snd :
    F.leftExteriorFirstSupportMap G H ≫
      pullback.snd (F.projection ≫ f) (H.projection ≫ h) =
    pullback.snd (F.incidenceTarget G ≫ h) (H.projection ≫ h) :=
  pullback.lift_snd _ _ _

/-- Forgetting the exterior factor gives a Cartesian square of actual supports. -/
theorem leftExteriorFirstSupportMap_pair_isPullback :
    IsPullback (F.leftExteriorFirstSupportMap G H)
      (pullback.fst (F.incidenceTarget G ≫ h) (H.projection ≫ h))
      (pullback.fst (F.projection ≫ f) (H.projection ≫ h)) (F.incidenceFst G) := by
  apply IsPullback.flip
  refine IsPullback.of_bot
    (t := IsPullback.of_hasPullback (F.projection ≫ f) (H.projection ≫ h)) ?_
    (F.leftExteriorFirstSupportMap_fst G H).symm
  have hb : F.incidenceFst G ≫ (F.projection ≫ f) = F.incidenceTarget G ≫ h := by
    simpa only [incidenceSource, Category.assoc] using F.incidence_base G
  simpa only [F.leftExteriorFirstSupportMap_snd G H, Category.assoc, hb] using
    (IsPullback.of_hasPullback (F.incidenceTarget G ≫ h) (H.projection ≫ h))

/-- The first exterior map is the genuine base change of the second generator's
finite projection, with its original smooth intermediate scheme as base. -/
theorem leftExteriorFirstSupportMap_isPullback :
    IsPullback (F.leftExteriorFirstSupportMap G H)
      (pullback.fst (F.incidenceTarget G ≫ h) (H.projection ≫ h) ≫ F.incidenceSnd G)
      (pullback.fst (F.projection ≫ f) (H.projection ≫ h) ≫ F.targetProjection)
      G.projection :=
  (F.leftExteriorFirstSupportMap_pair_isPullback G H).paste_vert
    (IsPullback.of_hasPullback F.targetProjection G.projection)

/-- The original first generator's projection with the actual third support. -/
def leftExteriorFirstSourceMap : F.leftExteriorFirstSupportProduct H ⟶
    pullback f (H.projection ≫ h) :=
  pullback.lift
    (pullback.fst (F.projection ≫ f) (H.projection ≫ h) ≫ F.projection)
    (pullback.snd (F.projection ≫ f) (H.projection ≫ h)) (by
      simpa only [Category.assoc] using
        (pullback.condition (f := F.projection ≫ f) (g := H.projection ≫ h)))

/-- The first exterior source map retains the original first projection. -/
@[reassoc (attr := simp)] theorem leftExteriorFirstSourceMap_fst :
    F.leftExteriorFirstSourceMap H ≫ pullback.fst f (H.projection ≫ h) =
    pullback.fst (F.projection ≫ f) (H.projection ≫ h) ≫ F.projection :=
  pullback.lift_fst _ _ _

/-- The third support is unchanged by the exterior source map. -/
@[reassoc (attr := simp)] theorem leftExteriorFirstSourceMap_snd :
    F.leftExteriorFirstSourceMap H ≫ pullback.snd f (H.projection ≫ h) =
    pullback.snd (F.projection ≫ f) (H.projection ≫ h) :=
  pullback.lift_snd _ _ _

/-- The exterior source map is an actual base change of the first generator. -/
theorem leftExteriorFirstSourceMap_isPullback :
    IsPullback (F.leftExteriorFirstSourceMap H)
      (pullback.fst (F.projection ≫ f) (H.projection ≫ h))
      (pullback.fst f (H.projection ≫ h)) F.projection := by
  apply IsPullback.flip
  refine IsPullback.of_bot
    (t := IsPullback.of_hasPullback f (H.projection ≫ h)) ?_
    (F.leftExteriorFirstSourceMap_fst H).symm
  simpa only [F.leftExteriorFirstSourceMap_snd H] using
    (IsPullback.of_hasPullback (F.projection ≫ f) (H.projection ≫ h))

/-- The original-source projection of the whole exterior incidence product. -/
abbrev leftExteriorSourceMap : F.leftIntermediateSupportProduct G H ⟶
    pullback f (H.projection ≫ h) :=
  F.leftExteriorFirstSupportMap G H ≫ F.leftExteriorFirstSourceMap H

/-- The whole intermediate scheme image, with its actual source projection and
the third support. The image scheme is not replaced by a reduced component. -/
def leftExteriorImageSourceMap : F.leftIntermediateImageProduct G H ⟶
    pullback f (H.projection ≫ h) :=
  pullback.lift
    (pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd f h ≫ h)
      (H.projection ≫ h) ≫ (F.incidenceMap G).imageι ≫ pullback.fst f h)
    (pullback.snd ((F.incidenceMap G).imageι ≫ pullback.snd f h ≫ h)
      (H.projection ≫ h)) (by
      simp only [Category.assoc, pullback.condition])

/-- The image product's source projection uses the actual scheme-image inclusion. -/
@[reassoc (attr := simp)] theorem leftExteriorImageSourceMap_fst :
    F.leftExteriorImageSourceMap G H ≫ pullback.fst f (H.projection ≫ h) =
    pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd f h ≫ h)
      (H.projection ≫ h) ≫ (F.incidenceMap G).imageι ≫ pullback.fst f h :=
  pullback.lift_fst _ _ _

/-- The whole intermediate image map leaves the third support unchanged. -/
@[reassoc (attr := simp)] theorem leftExteriorImageSourceMap_snd :
    F.leftExteriorImageSourceMap G H ≫ pullback.snd f (H.projection ≫ h) =
    pullback.snd ((F.incidenceMap G).imageι ≫ pullback.snd f h ≫ h)
      (H.projection ≫ h) :=
  pullback.lift_snd _ _ _

/-- The image product projection is the genuine base change of the finite
original-source projection of the whole pair scheme image. -/
theorem leftExteriorImageSourceMap_isPullback :
    IsPullback (F.leftExteriorImageSourceMap G H)
      (pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd f h ≫ h)
        (H.projection ≫ h))
      (pullback.fst f (H.projection ≫ h))
      ((F.incidenceMap G).imageι ≫ pullback.fst f h) := by
  apply IsPullback.flip
  refine IsPullback.of_bot
    (t := IsPullback.of_hasPullback f (H.projection ≫ h)) ?_
    (F.leftExteriorImageSourceMap_fst G H).symm
  simpa only [F.leftExteriorImageSourceMap_snd G H, Category.assoc,
    pullback.condition] using
    (IsPullback.of_hasPullback
      ((F.incidenceMap G).imageι ≫ pullback.snd f h ≫ h) (H.projection ≫ h))

/-- The original finite image-product map commutes with the proved exterior
source projections, as a literal equality of scheme morphisms. -/
@[reassoc (attr := simp)] theorem leftIntermediateImageMap_source :
    F.leftIntermediateImageMap G H ≫ F.leftExteriorImageSourceMap G H =
      F.leftExteriorSourceMap G H := by
  apply pullback.hom_ext
  · simp only [Category.assoc, leftExteriorImageSourceMap_fst,
      leftIntermediateImageMap_fst_assoc, Scheme.Hom.toImage_imageι_assoc,
      incidenceMap_fst, leftExteriorSourceMap, leftExteriorFirstSourceMap_fst,
      leftExteriorFirstSupportMap_fst_assoc, incidenceSource]
  · simp only [Category.assoc, leftExteriorImageSourceMap_snd,
      leftIntermediateImageMap_snd, leftExteriorSourceMap,
      leftExteriorFirstSourceMap_snd, leftExteriorFirstSupportMap_snd]

section SmoothSite

variable (k : Type u) [Field k]
  {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The test map to the original intermediate smooth scheme is locally finite
type, derived from the actual exterior projection and original target map. -/
theorem locallyOfFiniteType_leftExteriorFirstSupportTarget :
    LocallyOfFiniteType
      (pullback.fst (F.projection ≫ X.hom) (H.projection ≫ Z.hom) ≫
        F.targetProjection) := by
  have := F.locallyOfFiniteType_targetProjection (S := Spec (.of k))
  infer_instance

/-- Normality of the original intermediate smooth scheme gives genuine
generalization lifting for the actual exterior first-support map. -/
theorem generalizingMap_leftExteriorFirstSupportMap :
    GeneralizingMap (F.leftExteriorFirstSupportMap G H) := by
  have := F.locallyOfFiniteType_leftExteriorFirstSupportTarget k H
  have : IsNoetherian ((𝟭 Scheme).obj Y.left) :=
    inferInstanceAs (IsNoetherian Y.left)
  exact generalizingMap_of_isPullback_component _ _ _ _
    (F.leftExteriorFirstSupportMap_isPullback G H) G.range_projection_mem
    (fun y ↦ ⟨SmoothSite.isDomain_stalk k Y y,
      SmoothSite.isIntegrallyClosed_stalk k Y y⟩)

/-- The second test map is locally finite type because it is the actual base
change of the third support's finite-type structure map. -/
theorem locallyOfFiniteType_leftExteriorSourceProjection :
    LocallyOfFiniteType (pullback.fst X.hom (H.projection ≫ Z.hom)) := by
  infer_instance

/-- Normality of the original source smooth scheme gives generalization
lifting for the exterior first generator, without assuming that source integral. -/
theorem generalizingMap_leftExteriorFirstSourceMap :
    GeneralizingMap (F.leftExteriorFirstSourceMap H) := by
  have := H.locallyOfFiniteType_leftExteriorSourceProjection k (X := X)
  have : IsNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsNoetherian X.left)
  exact generalizingMap_of_isPullback_component _ _ _ _
    (F.leftExteriorFirstSourceMap_isPullback H) F.range_projection_mem
    (fun x ↦ ⟨SmoothSite.isDomain_stalk k X x,
      SmoothSite.isIntegrallyClosed_stalk k X x⟩)

/-- The actual whole exterior incidence projection is generalizing, by the
two proved component-normal Cartesian base changes. -/
theorem generalizingMap_leftExteriorSourceMap :
    GeneralizingMap (F.leftExteriorSourceMap G H) :=
  (F.generalizingMap_leftExteriorFirstSupportMap k G H).comp
    (F.generalizingMap_leftExteriorFirstSourceMap k H)

/-- Generic exterior incidence points dominate genuine exterior source generics. -/
theorem leftExteriorSourceMap_mem_genericPoints
    (w : F.leftIntermediateSupportProduct G H)
    (hw : w ∈ genericPoints (F.leftIntermediateSupportProduct G H)) :
    F.leftExteriorSourceMap G H w ∈
      genericPoints (pullback X.hom (H.projection ≫ Z.hom) : Scheme.{u}) :=
  mem_genericPoints_of_generalizing _ (F.generalizingMap_leftExteriorSourceMap k G H) w hw

/-- The actual whole image product is finite over the exterior original source. -/
theorem isFinite_leftExteriorImageSourceMap :
    IsFinite (F.leftExteriorImageSourceMap G H) := by
  have := F.isFinite_incidenceImageProjection k G
  exact MorphismProperty.of_isPullback
    (F.leftExteriorImageSourceMap_isPullback G H).flip inferInstance

/-- The actual finite intermediate image-product map preserves generic points
because its composite dominates an exterior source component and the next map
is quasi-finite. No injectivity of the generic-point map is asserted. -/
theorem leftIntermediateImageMap_mem_genericPoints
    (w : F.leftIntermediateSupportProduct G H)
    (hw : w ∈ genericPoints (F.leftIntermediateSupportProduct G H)) :
    F.leftIntermediateImageMap G H w ∈ genericPoints (F.leftIntermediateImageProduct G H) := by
  have := F.isFinite_leftExteriorImageSourceMap k G H
  apply mem_genericPoints_of_image_generic (F.leftExteriorImageSourceMap G H)
  change (F.leftIntermediateImageMap G H ≫ F.leftExteriorImageSourceMap G H) w ∈ _
  rw [F.leftIntermediateImageMap_source G H]
  exact F.leftExteriorSourceMap_mem_genericPoints k G H w hw

end SmoothSite

end Motivic.FiniteCorrespondenceGenerator
