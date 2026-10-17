/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IntegralExteriorCyclePushforward
public import Motivic.AlgebraicGeometry.Correspondences.FieldBaseChangeSupport

/-!
# Actual incidence-component pushforward under arbitrary field change

The actual finite point-closure map of a generator incidence is pulled back
along an arbitrary field extension. All branches and their whole-scheme local
lengths are retained. Generic preservation is proved through the finite source
projection onto a smooth component and quasi-finite reflection through the
new image projection. No normality of the image, separability, or finite-type
assumption on the field extension is imposed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FieldBaseChangePushforward

open IntegralClosedSubscheme

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y Z : SmoothSite.overField k}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (x : genericPoints (A.incidence B))

/-- The original reduced incidence component's actual finite source projection. -/
abbrev originalSourceProjection :=
  (pointClosure x.1).val.subschemeι ≫ A.incidenceSource B

/-- The original reduced image component's actual source projection. -/
abbrev originalTargetProjection :=
  (pointClosure (A.incidenceMap B x.1)).val.subschemeι ≫ pullback.fst X.hom Z.hom

@[reassoc (attr := simp)]
theorem pointClosureMap_source :
    pointClosureMap (A.incidenceMap B) x.1 ≫ originalTargetProjection A B x =
      originalSourceProjection A B x := by
  simp only [originalTargetProjection, originalSourceProjection,
    pointClosureMap_ambient_assoc, FiniteCorrespondenceGenerator.incidenceMap_fst]

/-- Finiteness uses the literal finite image, transported to its equal point closure. -/
instance originalTargetProjection_isFinite : IsFinite (originalTargetProjection A B x) := by
  have hfinite := A.isFinite_incidenceImage_projection B (pointClosure x.1)
  have heq := pointClosure_finiteImage (A.incidenceMap B) x.1
  rw [heq] at hfinite
  exact hfinite

/-- The whole new target point closure, before reducing its field pullback. -/
abbrev target := pullback (originalTargetProjection A B x ≫ X.hom)
  (Spec.map (CommRingCat.ofHom φ))

/-- The whole new source point closure, before reducing its field pullback. -/
abbrev source := pullback (originalSourceProjection A B x ≫ X.hom)
  (Spec.map (CommRingCat.ofHom φ))

/-- The literal field base change of the original finite point-closure map. -/
def map : source φ A B x ⟶ target φ A B x :=
  pullback.lift
    (pullback.fst (originalSourceProjection A B x ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) ≫ pointClosureMap (A.incidenceMap B) x.1)
    (pullback.snd (originalSourceProjection A B x ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ))) (by
        rw [Category.assoc, ← Category.assoc (pointClosureMap (A.incidenceMap B) x.1),
          pointClosureMap_source]
        exact pullback.condition)

@[reassoc (attr := simp)]
theorem map_fst : map φ A B x ≫
    pullback.fst (originalTargetProjection A B x ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) =
      pullback.fst (originalSourceProjection A B x ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)) ≫ pointClosureMap (A.incidenceMap B) x.1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem map_snd : map φ A B x ≫
    pullback.snd (originalTargetProjection A B x ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) =
      pullback.snd (originalSourceProjection A B x ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.lift_snd _ _ _

/-- The displayed square is Cartesian for the exact original point-closure map. -/
theorem isPullback :
    IsPullback
      (pullback.fst (originalSourceProjection A B x ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)))
      (map φ A B x) (pointClosureMap (A.incidenceMap B) x.1)
      (pullback.fst (originalTargetProjection A B x ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ))) := by
  refine IsPullback.of_bot (t := IsPullback.of_hasPullback
    (originalTargetProjection A B x ≫ X.hom) (Spec.map (CommRingCat.ofHom φ))) ?_
    (map_fst φ A B x).symm
  rw [map_snd, ← Category.assoc (pointClosureMap (A.incidenceMap B) x.1),
    pointClosureMap_source]
  exact IsPullback.of_hasPullback (originalSourceProjection A B x ≫ X.hom)
    (Spec.map (CommRingCat.ofHom φ))

instance map_isFinite : IsFinite (map φ A B x) :=
  MorphismProperty.of_isPullback (isPullback φ A B x) inferInstance

/-- The new source projection to the actual smooth source over the new field. -/
def sourceProjection : source φ A B x ⟶ ((SmoothSite.fieldBaseChange φ).obj X).left :=
  pullback.lift
    (pullback.fst (originalSourceProjection A B x ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) ≫ originalSourceProjection A B x)
    (pullback.snd (originalSourceProjection A B x ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ))) (by
        simpa only [Category.assoc] using (pullback.condition
          (f := originalSourceProjection A B x ≫ X.hom)
          (g := Spec.map (CommRingCat.ofHom φ))))

/-- The new target projection to the same actual smooth source. -/
def targetProjection : target φ A B x ⟶ ((SmoothSite.fieldBaseChange φ).obj X).left :=
  pullback.lift
    (pullback.fst (originalTargetProjection A B x ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) ≫ originalTargetProjection A B x)
    (pullback.snd (originalTargetProjection A B x ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ))) (by
        simpa only [Category.assoc] using (pullback.condition
          (f := originalTargetProjection A B x ≫ X.hom)
          (g := Spec.map (CommRingCat.ofHom φ))))

@[reassoc (attr := simp)]
theorem sourceProjection_fst : sourceProjection φ A B x ≫
    pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ)) =
      pullback.fst (originalSourceProjection A B x ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)) ≫ originalSourceProjection A B x :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem sourceProjection_snd : sourceProjection φ A B x ≫
    pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ)) =
      pullback.snd (originalSourceProjection A B x ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem targetProjection_fst : targetProjection φ A B x ≫
    pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ)) =
      pullback.fst (originalTargetProjection A B x ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)) ≫ originalTargetProjection A B x :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem targetProjection_snd : targetProjection φ A B x ≫
    pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ)) =
      pullback.snd (originalTargetProjection A B x ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.lift_snd _ _ _

/-- Source finiteness is transported by this actual Cartesian square. -/
theorem sourceProjection_isPullback :
    IsPullback
      (pullback.fst (originalSourceProjection A B x ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)))
      (sourceProjection φ A B x) (originalSourceProjection A B x)
      (pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))) := by
  refine IsPullback.of_bot (t := IsPullback.of_hasPullback X.hom
    (Spec.map (CommRingCat.ofHom φ))) ?_ (sourceProjection_fst φ A B x).symm
  simpa only [sourceProjection_snd] using IsPullback.of_hasPullback
    (originalSourceProjection A B x ≫ X.hom) (Spec.map (CommRingCat.ofHom φ))

/-- Target finiteness is transported by this actual Cartesian square. -/
theorem targetProjection_isPullback :
    IsPullback
      (pullback.fst (originalTargetProjection A B x ≫ X.hom)
        (Spec.map (CommRingCat.ofHom φ)))
      (targetProjection φ A B x) (originalTargetProjection A B x)
      (pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))) := by
  refine IsPullback.of_bot (t := IsPullback.of_hasPullback X.hom
    (Spec.map (CommRingCat.ofHom φ))) ?_ (targetProjection_fst φ A B x).symm
  simpa only [targetProjection_snd] using IsPullback.of_hasPullback
    (originalTargetProjection A B x ≫ X.hom) (Spec.map (CommRingCat.ofHom φ))

instance sourceProjection_isFinite : IsFinite (sourceProjection φ A B x) :=
  MorphismProperty.of_isPullback (sourceProjection_isPullback φ A B x) inferInstance

instance targetProjection_isFinite : IsFinite (targetProjection φ A B x) :=
  MorphismProperty.of_isPullback (targetProjection_isPullback φ A B x) inferInstance

/-- Noetherianity comes from the new smooth source and a finite map. -/
instance source_isNoetherian : IsNoetherian (source φ A B x) :=
  isNoetherian_of_finiteType (sourceProjection φ A B x)

/-- Noetherianity does not require the field extension to be finite type. -/
instance target_isNoetherian : IsNoetherian (target φ A B x) :=
  isNoetherian_of_finiteType (targetProjection φ A B x)

@[reassoc (attr := simp)]
theorem map_source : map φ A B x ≫ targetProjection φ A B x = sourceProjection φ A B x := by
  apply pullback.hom_ext
  · simp only [Category.assoc, targetProjection_fst, sourceProjection_fst,
      map_fst_assoc, pointClosureMap_source]
  · simp only [Category.assoc, targetProjection_snd, sourceProjection_snd, map_snd]

/-- Every new incidence-component generic dominates a new smooth-source component. -/
theorem sourceProjection_generic (w : genericPoints (source φ A B x)) :
    sourceProjection φ A B x w.1 ∈
      genericPoints ((SmoothSite.fieldBaseChange φ).obj X).left := by
  have : Flat (Spec.map (CommRingCat.ofHom φ)) :=
    Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField k) φ)
  have : IsNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsNoetherian X.left)
  apply mem_genericPoints_of_isPullback_flat_component
    (sourceProjection φ A B x) _ _ (originalSourceProjection A B x)
    (sourceProjection_isPullback φ A B x).flip
  · change Set.range ((pointClosure x.1).val.subschemeι ≫ A.incidenceSource B) ∈ _
    rw [A.range_incidence_component_source k B x]
    exact A.range_projection_mem
  · exact fun y => SmoothSite.isDomain_stalk L _ y
  · exact fun y => SmoothSite.isDomain_stalk k X y
  · exact w.2

/-- Finite image projection reflects genericity; the new image need not be normal. -/
theorem map_generic (w : genericPoints (source φ A B x)) :
    map φ A B x w.1 ∈ genericPoints (target φ A B x) := by
  apply mem_genericPoints_of_image_generic (targetProjection φ A B x)
  change (map φ A B x ≫ targetProjection φ A B x) w.1 ∈ _
  rw [map_source]
  exact sourceProjection_generic φ A B x w

/-- Every new target generic lies over the original image-closure generic. -/
theorem target_generic_projection (y : genericPoints (target φ A B x)) :
    pullback.fst (originalTargetProjection A B x ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ)) y.1 =
        genericPoint (pointClosure (A.incidenceMap B x.1)).val.subscheme := by
  have : Flat (Spec.map (CommRingCat.ofHom φ)) :=
    Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField k) φ)
  have hg := mem_genericPoints_of_generalizing
    (pullback.fst (originalTargetProjection A B x ≫ X.hom)
      (Spec.map (CommRingCat.ofHom φ))) (Flat.generalizingMap _) y.1 y.2
  simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hg

/-- All-branch, collision-aware equality of the full cycles, retaining the
original incidence residue degree and all inseparable local lengths. -/
theorem finitePushforward_fundamentalCycle :
    IntegralCycle.finitePushforward (map φ A B x) (fundamentalCycle (source φ A B x)) =
      ((A.incidenceMap B).residueDegree x.1 : ℤ) • fundamentalCycle (target φ A B x) := by
  exact IntegralExteriorCyclePushforward.finitePushforward_fundamentalCycle_pointClosure_baseChange
    (A.incidenceMap B) x.1 (isPullback φ A B x)
    (map_generic φ A B x) (target_generic_projection φ A B x)

open IntegralExteriorCyclePushforward in
/-- Nongeneric coefficients vanish as well, so the equality holds at every point. -/
theorem pushforward_eq_zero_of_not_generic (y : target φ A B x)
    (hy : y ∉ genericPoints (target φ A B x)) :
    IntegralCycle.toPoints
      (IntegralCycle.finitePushforward (map φ A B x) (fundamentalCycle (source φ A B x))) y = 0 :=
  toPoints_finitePushforward_fundamentalCycle_eq_zero_of_not_generic
    (map φ A B x) (map_generic φ A B x) y hy

end Motivic.FieldBaseChangePushforward
