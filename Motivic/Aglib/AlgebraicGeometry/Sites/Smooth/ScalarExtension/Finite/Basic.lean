/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.Separable

/-!
# Finite scalar extension of smooth sites
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]

local instance : Algebra.FormallyEtale k E := Algebra.FormallyEtale.of_isSeparable k E
local instance : Algebra.Etale k E :=
  ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
local instance : Etale (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
local instance : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- A finite separable scalar extension, viewed over its original ground field. -/
def finiteScalarExtension (X : SmoothSite (Spec (.of k))) :
    SmoothSite (Spec (.of k)) :=
  mk (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E))) ≫ X.hom)

/-- The literal finite scalar projection, as a morphism over the ground field. -/
def finiteScalarProjection (X : SmoothSite (Spec (.of k))) :
    finiteScalarExtension (E := E) X ⟶ X :=
  homMk (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E)))) rfl

instance (X : SmoothSite (Spec (.of k))) :
    IsFinite (finiteScalarProjection (E := E) X).left :=
  inferInstanceAs (IsFinite
    (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E)))))

instance (X : SmoothSite (Spec (.of k))) :
    Flat (finiteScalarProjection (E := E) X).left :=
  inferInstanceAs (Flat
    (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E)))))

/-- The original map after finite scalar extension, still viewed over k. -/
def finiteScalarMap {U X : SmoothSite (Spec (.of k))} (j : U ⟶ X) :
    finiteScalarExtension (E := E) U ⟶ finiteScalarExtension (E := E) X :=
by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let g : pullback U.hom f ⟶ pullback X.hom f :=
    pullback.lift (pullback.fst U.hom f ≫ j.left) (pullback.snd U.hom f)
      (by rw [Category.assoc, MorphismProperty.Over.w, pullback.condition])
  refine homMk g ?_
  change g ≫ (pullback.fst X.hom f ≫ X.hom) = pullback.fst U.hom f ≫ U.hom
  rw [← Category.assoc, show g ≫ pullback.fst X.hom f =
    pullback.fst U.hom f ≫ j.left from pullback.lift_fst _ _ _]
  rw [Category.assoc, MorphismProperty.Over.w]

/-- The actual scalar projection square is Cartesian, without a supplied square. -/
theorem finiteScalarMap_isPullback {U X : SmoothSite (Spec (.of k))} (j : U ⟶ X) :
    IsPullback (finiteScalarProjection (E := E) U).left
      (finiteScalarMap (E := E) j).left j.left
      (finiteScalarProjection (E := E) X).left := by
  apply IsPullback.flip
  apply IsPullback.of_right
    (h₁₂ := pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E))))
    (h₂₂ := X.hom) (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap k E)))
  · simp only [finiteScalarMap, homMk_left, pullback.lift_snd,
      finiteScalarProjection, MorphismProperty.Over.w]
    exact (IsPullback.of_hasPullback U.hom _).flip
  · simp [finiteScalarMap, finiteScalarProjection]
  · exact (IsPullback.of_hasPullback X.hom _).flip

end AlgebraicGeometry.Scheme.SmoothSite
