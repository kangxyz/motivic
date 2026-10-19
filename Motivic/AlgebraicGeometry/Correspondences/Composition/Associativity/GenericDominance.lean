/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Support.ComponentDominance
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.Incidence
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.QuasiFinite.GenericFiber

/-!
# Generic dominance of actual pair and triple images

Actual pair and triple incidence generic points map to generic points of the
original source component. The proof uses genuine generalization lifting over
smooth, possibly disconnected intermediate schemes and the first generator's
literal component image. Their actual scheme images are finite over that
source; quasi-finite reflection then proves genericity in those images.
No arbitrary finite map is asserted to preserve generic points, and no
numerical dimension, purity, reducedness or global integrality is assumed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Products

variable {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

/-- An elementary support's actual generic point maps to the generic point of
its specified source component, including disconnected source schemes. -/
theorem projection_mem_genericPoints (F : FiniteCorrespondenceGenerator f g)
    (x : F.scheme) (hx : x ∈ genericPoints F.scheme) :
    F.projection x ∈ genericPoints X := by
  have hcl : closure ({x} : Set F.scheme) = Set.univ := by
    simpa only [genericPoints, Set.mem_ofPred_eq, irreducibleComponents_eq_singleton,
      Set.mem_singleton_iff] using hx
  change closure ({F.projection x} : Set X) ∈ irreducibleComponents X
  rw [← Set.image_singleton,
    F.projection.isClosedMap.closure_image_eq_of_continuous F.projection.continuous,
    hcl, Set.image_univ]
  exact F.range_projection_mem

variable (k : Type u) [Field k]
  {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- A generic point of actual pair incidence dominates an actual source component. -/
theorem incidenceSource_mem_genericPoints (x : F.incidence G)
    (hx : x ∈ genericPoints (F.incidence G)) :
    F.incidenceSource G x ∈ genericPoints X.left :=
  F.projection_mem_genericPoints (F.incidenceFst G x)
    (mem_genericPoints_of_generalizing _ (F.generalizingMap_incidenceFst_smooth k G) x hx)

/-- The actual incidence target is locally finite type over the next smooth object. -/
theorem locallyOfFiniteType_incidenceTarget : LocallyOfFiniteType (F.incidenceTarget G) := by
  have : LocallyOfFiniteType (F.incidenceTarget G ≫ Z.hom) := by
    rw [← F.incidence_base G]
    infer_instance
  exact locallyOfFiniteType_of_comp (F.incidenceTarget G) Z.hom

/-- The triple-to-first-pair map is genuinely generalizing over the appropriate
normal component of the third smooth object. -/
theorem generalizingMap_tripleIncidenceFst_smooth :
    GeneralizingMap (F.tripleIncidenceFst G H) := by
  have := F.locallyOfFiniteType_incidenceTarget k G
  have : IsNoetherian ((𝟭 Scheme).obj Z.left) :=
    inferInstanceAs (IsNoetherian Z.left)
  exact generalizingMap_of_isPullback_component _ _ _ _ (.of_hasPullback _ _)
    H.range_projection_mem (fun z ↦
      ⟨SmoothSite.isDomain_stalk k Z z, SmoothSite.isIntegrallyClosed_stalk k Z z⟩)

/-- Actual triple-incidence generic points dominate actual original-source generics. -/
theorem tripleIncidenceSource_mem_genericPoints (x : F.tripleIncidence G H)
    (hx : x ∈ genericPoints (F.tripleIncidence G H)) :
    F.tripleIncidenceSource G H x ∈ genericPoints X.left :=
  F.incidenceSource_mem_genericPoints k G (F.tripleIncidenceFst G H x)
    (mem_genericPoints_of_generalizing _
      (F.generalizingMap_tripleIncidenceFst_smooth k G H) x hx)

/-- The whole actual pair scheme image, retaining nilpotents and collisions,
has finite original-source projection. -/
theorem isFinite_incidenceImageProjection :
    IsFinite ((F.incidenceMap G).imageι ≫ pullback.fst X.hom Z.hom) := by
  have : IsFinite (F.incidenceMap G ≫ pullback.fst X.hom Z.hom) := by
    rw [F.incidenceMap_fst G]
    infer_instance
  exact isFinite_image_projection (F.incidenceMap G) (pullback.fst X.hom Z.hom)

/-- The whole actual triple scheme image has finite original-source projection. -/
theorem isFinite_tripleIncidenceImageProjection :
    IsFinite ((F.tripleIncidenceMap G H).imageι ≫ pullback.fst X.hom W.hom) := by
  have : IsFinite (F.tripleIncidenceMap G H ≫ pullback.fst X.hom W.hom) := by
    rw [F.tripleIncidenceMap_fst G H]
    infer_instance
  exact isFinite_image_projection (F.tripleIncidenceMap G H) (pullback.fst X.hom W.hom)

set_option backward.isDefEq.respectTransparency false in
/-- Pair generic points map to actual generics of the whole pair image;
source-component dominance rules out nested image contributions. -/
theorem incidenceToImage_mem_genericPoints (x : F.incidence G)
    (hx : x ∈ genericPoints (F.incidence G)) :
    (F.incidenceMap G).toImage x ∈ genericPoints (F.incidenceMap G).image := by
  let p := (F.incidenceMap G).imageι ≫ pullback.fst X.hom Z.hom
  have : IsFinite p := F.isFinite_incidenceImageProjection k G
  apply mem_genericPoints_of_image_generic (Y := X.left) p
  change ((F.incidenceMap G).toImage ≫ p) x ∈ genericPoints X.left
  rw [show (F.incidenceMap G).toImage ≫ p = F.incidenceSource G by simp [p]]
  exact F.incidenceSource_mem_genericPoints k G x hx

set_option backward.isDefEq.respectTransparency false in
/-- Triple generic points map to actual generics of the whole final image,
without any unsupported generic-preservation claim for arbitrary finite maps. -/
theorem tripleIncidenceToImage_mem_genericPoints (x : F.tripleIncidence G H)
    (hx : x ∈ genericPoints (F.tripleIncidence G H)) :
    (F.tripleIncidenceMap G H).toImage x ∈ genericPoints (F.tripleIncidenceMap G H).image := by
  let p := (F.tripleIncidenceMap G H).imageι ≫ pullback.fst X.hom W.hom
  have : IsFinite p := F.isFinite_tripleIncidenceImageProjection k G H
  apply mem_genericPoints_of_image_generic (Y := X.left) p
  change ((F.tripleIncidenceMap G H).toImage ≫ p) x ∈ genericPoints X.left
  rw [show (F.tripleIncidenceMap G H).toImage ≫ p = F.tripleIncidenceSource G H by
    simp [p]]
  exact F.tripleIncidenceSource_mem_genericPoints k G H x hx

end Motivic.FiniteCorrespondenceGenerator
