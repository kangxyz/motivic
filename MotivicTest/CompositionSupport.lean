/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.CompositionSupportEmbedding
public import Motivic.AlgebraicGeometry.Correspondences.CompositionSupportGraphs
public import Motivic.AlgebraicGeometry.Cycles.IntegralCycle
public import Motivic.AlgebraicGeometry.Cycles.FiniteResidueDegree

/-!
# Consumers of geometric composition support

The examples check the actual finite maps, the full scheme-theoretic
intersection, component-sensitive source images, and graph-unit isomorphisms.
They also apply the existing finite-image and cycle-pushforward APIs to an
arbitrary supplied integral cycle on incidence. No intersection cycle is
chosen or identified with the scheme-fiber length.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

example : A.incidence B = pullback A.targetProjection B.projection := rfl

example : IsFinite (A.incidenceSource B) := inferInstance

example [IsSeparated h] : IsFinite (A.incidenceMap B) := inferInstance

example : IsClosedImmersion (A.incidenceInclusion B) := inferInstance

example : A.incidenceInclusion B ≫ correspondenceTripleProjection f g h = A.incidenceMap B :=
  A.incidenceInclusion_projection B

example : (A.incidenceInclusion B).ker =
    A.val.comap (pullback.fst (pullback.snd f g) (pullback.fst g h)) ⊔
      B.val.comap (pullback.snd (pullback.snd f g) (pullback.fst g h)) :=
  A.ker_incidenceInclusion B

example : Nonempty (A.incidence B ≅
    (A.val.comap (pullback.fst (pullback.snd f g) (pullback.fst g h)) ⊔
      B.val.comap (pullback.snd (pullback.snd f g) (pullback.fst g h))).subscheme) :=
  ⟨A.incidenceIntersectionIso B⟩

example : Set.range (A.incidenceSource B) =
    A.projection '' (A.targetProjection ⁻¹' Set.range B.projection) :=
  A.range_incidenceSource B

example (hAB : Set.range A.targetProjection ⊆ Set.range B.projection) :
    Set.range (A.incidenceSource B) ∈ irreducibleComponents X :=
  A.range_incidenceSource_mem_of_coverage B hAB

example [IrreducibleSpace Y] :
    Set.range (A.incidenceSource B) = Set.range A.projection :=
  A.range_incidenceSource_of_irreducible B

example [IsSeparated h] :
    ((A.incidenceImageIdeal B).support : Set (pullback (C := Scheme) f h)) =
      Set.range (A.incidenceMap B) :=
  A.support_incidenceImageIdeal B

example [IsSeparated h] (V : IntegralClosedSubscheme (A.incidence B)) :
    (V.finiteImage (A.incidenceMap B)).point = (A.incidenceMap B) V.point :=
  V.point_finiteImage _

example [IsSeparated h] (V : IntegralClosedSubscheme (A.incidence B)) :
    0 < V.imageDegree (A.incidenceMap B) := by
  rw [V.imageDegree_eq]
  exact residueDegree_pos _ _

example [IsSeparated h] (V : IntegralClosedSubscheme (A.incidence B)) (n : ℤ) :
    IntegralCycle.finitePushforward (A.incidenceMap B) (Finsupp.single V n) =
      Finsupp.single (V.finiteImage (A.incidenceMap B))
        (n * (V.imageDegree (A.incidenceMap B) : ℤ)) :=
  IntegralCycle.finitePushforward_single_imageDegree _ _ _

example [IsSeparated h] (c : IntegralCycle (A.incidence B)) :
    IntegralCycle.toPoints (IntegralCycle.finitePushforward (A.incidenceMap B) c) =
      FiniteSupportCycle.residuePushforward (A.incidenceMap B) (IntegralCycle.toPoints c) :=
  DFunLike.congr_fun (IntegralCycle.toPoints_finitePushforward _) c

example [IsIntegral Y] [IsSeparated g] :
    A.incidenceMap (identityGenerator g) = (A.rightIdentityIncidenceIso).hom ≫ A.inclusion :=
  A.incidenceMap_identity_right

example [IsIntegral Y] [IsSeparated g] :
    A.incidenceImageIdeal (identityGenerator g) = A.val :=
  A.incidenceImageIdeal_identity_right

example [IsIntegral X] [IsSeparated f] :
    (identityGenerator f).incidenceMap A = (A.leftIdentityIncidenceIso).hom ≫ A.inclusion :=
  A.incidenceMap_identity_left

example [IsIntegral X] [IsSeparated f] :
    (identityGenerator f).incidenceImageIdeal A = A.val :=
  A.incidenceImageIdeal_identity_left

example (ψ : Y ⟶ Z) (w : ψ ≫ h = g) [IsIntegral Y] [IsSeparated h] :
    A.incidenceImageIdeal (graphGeneratorOver ψ w) = (A.graphPostcompositionMap ψ w).ker :=
  A.incidenceImageIdeal_graph_right ψ w
