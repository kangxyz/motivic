/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IntegralExteriorCyclePushforward
public import Motivic.AlgebraicGeometry.Cycles.FundamentalClosedSubscheme
public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGeometry

/-!
# Finite point-closure pushforward after adjoining a smooth integral parameter

The actual finite point-closure map is base-changed by a geometrically
integral smooth parameter. Its pushed fundamental cycle has precisely the
original ambient residue degree. The generic-preservation and generic-base
point hypotheses of the degree-length theorem are proved here from the
literal product geometry. The original ambient schemes need not be reduced.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.ExteriorPointClosurePushforward

open IntegralClosedSubscheme

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Y) [IsFinite f] (x : X) (b : Y ⟶ Spec (.of k))
  (T : SmoothSite (Spec (.of k)))

/-- The original target point closure with its induced base structure. -/
abbrev targetHom := (pointClosure (f x)).val.subschemeι ≫ b

/-- The full product of the target point closure with the parameter. -/
abbrev target := pullback (targetHom f x b) T.hom

/-- The full product of the source point closure with the same parameter. -/
abbrev source := pullback (pointClosureMap f x ≫ targetHom f x b) T.hom

/-- The actual product of the original finite support map and the identity. -/
def map : source f x b T ⟶ target f x b T :=
  pullback.map _ _ _ _ (pointClosureMap f x) (𝟙 T.left) (𝟙 (Spec (.of k)))
    (by simp) (by simp)

@[reassoc (attr := simp)]
theorem map_fst : map f x b T ≫ pullback.fst (targetHom f x b) T.hom =
    pullback.fst (pointClosureMap f x ≫ targetHom f x b) T.hom ≫ pointClosureMap f x :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem map_snd : map f x b T ≫ pullback.snd (targetHom f x b) T.hom =
    pullback.snd (pointClosureMap f x ≫ targetHom f x b) T.hom :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The displayed product square is Cartesian before taking cycles. -/
theorem isPullback :
    IsPullback (pullback.fst (pointClosureMap f x ≫ targetHom f x b) T.hom)
      (map f x b T) (pointClosureMap f x) (pullback.fst (targetHom f x b) T.hom) := by
  refine IsPullback.of_bot (t := IsPullback.of_hasPullback (targetHom f x b) T.hom) ?_
    (map_fst f x b T).symm
  simpa only [map_snd] using
    (IsPullback.of_hasPullback (pointClosureMap f x ≫ targetHom f x b) T.hom)

instance map_isFinite : IsFinite (map f x b T) :=
  MorphismProperty.of_isPullback (isPullback f x b T) inferInstance

instance map_surjective : Surjective (map f x b T) := by
  let : Surjective (pointClosureMap f x) := ⟨pointClosureMap_surjective f x⟩
  exact MorphismProperty.of_isPullback (isPullback f x b T) inferInstance

variable [IsNoetherian X] [IsNoetherian Y]

instance source_isNoetherian : IsNoetherian (source f x b T) :=
  isNoetherian_of_finiteType
    (pullback.fst (pointClosureMap f x ≫ targetHom f x b) T.hom)

instance target_isNoetherian : IsNoetherian (target f x b T) :=
  isNoetherian_of_finiteType (pullback.fst (targetHom f x b) T.hom)

variable [GeometricallyIntegral T.hom]

instance source_isIntegral : IsIntegral (source f x b T) := inferInstance

instance target_isIntegral : IsIntegral (target f x b T) := inferInstance

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
/-- The exterior finite map sends the unique source generic point to the target generic point. -/
theorem map_genericPoint :
    map f x b T (genericPoint (source f x b T)) = genericPoint (target f x b T) := by
  symm
  apply (genericPoint_spec (target f x b T)).eq
  simpa only [Set.image_univ, Set.range_eq_univ.mpr (map f x b T).surjective,
    closure_univ] using
    (genericPoint_spec (source f x b T)).image (map f x b T).continuous

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
  [IsFinite f] [GeometricallyIntegral T.hom] in
/-- All target exterior generic points project to the original integral target generic point. -/
theorem target_generic_projection (y : genericPoints (target f x b T)) :
    pullback.fst (targetHom f x b) T.hom y.1 =
      genericPoint (pointClosure (f x)).val.subscheme := by
  have hg := mem_genericPoints_of_generalizing
    (pullback.fst (targetHom f x b) T.hom) (Flat.generalizingMap _) y.1 y.2
  simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hg

/-- The original ambient degree is retained by the full exterior fundamental-cycle pushforward. -/
theorem finitePushforward_fundamentalCycle :
    IntegralCycle.finitePushforward (map f x b T) (fundamentalCycle (source f x b T)) =
      (f.residueDegree x : ℤ) • fundamentalCycle (target f x b T) := by
  apply IntegralExteriorCyclePushforward.finitePushforward_fundamentalCycle_pointClosure_baseChange
    f x (isPullback f x b T)
  · intro w
    have hw : w.1 = genericPoint (source f x b T) := by
      simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using w.2
    rw [hw, map_genericPoint]
    simp only [genericPoints_eq_singleton, Set.mem_singleton_iff]
  · exact target_generic_projection f x b T

end Motivic.ExteriorPointClosurePushforward
