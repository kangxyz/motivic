/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.BaseChange.GenericComponents

/-!
# Consumers of generic preservation under arbitrary flat base change

The field extension below has no algebraicity or finite-type hypothesis.
The actual Cartesian square consumer allows disconnected ambient schemes and
a nonreduced, reducible pullback. The closed support image is verified to be
an actual irreducible component of the new target.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme (IntegralClosedSubscheme)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MotivicTest.FlatBaseChangeGeneric
open _root_.AlgebraicGeometry.Scheme.Hom

/-- Arbitrary field extensions preserve genericity in the actual affine
pullback, even for a nonreduced or disconnected original affine support. -/
theorem arbitraryFieldExtension
    (K L B : Type u) [Field K] [Field L] [CommRing B]
    [Algebra K L] [Algebra K B]
    (w : (pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (Spec.map (CommRingCat.ofHom (algebraMap K B))) : Scheme.{u}))
    (hw : w ∈ genericPoints (pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (Spec.map (CommRingCat.ofHom (algebraMap K B))) : Scheme.{u})) :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (Spec.map (CommRingCat.ofHom (algebraMap K B))) w ∈ genericPoints (Spec (.of L)) :=
  mem_genericPoints_pullbackFst_spec_flat K L B w hw

/-- The integral geometric consumer also has no finite-type assumption on g. -/
theorem arbitraryFlatIntegralSquare
    {W A B Y : Scheme.{u}} [IsIntegral A] [IsIntegral B] [IsIntegral Y]
    (p : W ⟶ A) (q : W ⟶ B) (g : A ⟶ Y) (f : B ⟶ Y)
    (H : IsPullback p q g f) [IsFinite f] [Surjective f] [Flat g]
    (w : genericPoints W) :
    Function.Surjective ((IntegralClosedSubscheme.pointClosure w.1).val.subschemeι ≫ p) :=
  surjective_pointClosure_of_isPullback_flat_integral p q g f H w.1 w.2

/-- Neither ambient scheme is assumed integral or connected. -/
theorem disconnectedAmbientGenericImage
    {W A B Y : Scheme.{u}} [IsNoetherian A] [IsNoetherian Y] [IsIntegral B]
    (p : W ⟶ A) (q : W ⟶ B) (g : A ⟶ Y) (f : B ⟶ Y)
    (H : IsPullback p q g f) [IsFinite f] [Flat g]
    (hf : Set.range f ∈ irreducibleComponents Y)
    (hA : ∀ a : A, IsDomain (A.presheaf.stalk a))
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y))
    (w : genericPoints W) : p w.1 ∈ genericPoints A :=
  mem_genericPoints_of_isPullback_flat_component p q g f H hf hA hY w.1 w.2

/-- Each reduced component closure has exactly an irreducible-component image;
no reduction or irreducibility is imposed on the whole pullback. -/
theorem disconnectedAmbientComponentImage
    {W A B Y : Scheme.{u}} [IsNoetherian A] [IsNoetherian Y] [IsIntegral B]
    (p : W ⟶ A) (q : W ⟶ B) (g : A ⟶ Y) (f : B ⟶ Y)
    (H : IsPullback p q g f) [IsFinite f] [Flat g]
    (hf : Set.range f ∈ irreducibleComponents Y)
    (hA : ∀ a : A, IsDomain (A.presheaf.stalk a))
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y))
    (w : genericPoints W) :
    Set.range ((IntegralClosedSubscheme.pointClosure w.1).val.subschemeι ≫ p) ∈
      irreducibleComponents A := by
  have : IsFinite p := MorphismProperty.of_isPullback H.flip inferInstance
  change Set.range (p ∘ (IntegralClosedSubscheme.pointClosure w.1).val.subschemeι) ∈ _
  rw [Set.range_comp, (IntegralClosedSubscheme.pointClosure w.1).val.range_subschemeι,
    IntegralClosedSubscheme.support_pointClosure,
    ← p.isClosedMap.closure_image_eq_of_continuous p.continuous, Set.image_singleton]
  exact disconnectedAmbientGenericImage p q g f H hf hA hY w

open Lean in
run_cmd do
  for name in #[``_root_.AlgebraicGeometry.Scheme.Hom.mem_genericPoints_pullbackFst_spec_flat,
      ``_root_.AlgebraicGeometry.Scheme.Hom.mem_genericPoints_of_isPullback_flat_affine,
      ``_root_.AlgebraicGeometry.Scheme.Hom.mem_genericPoints_of_isPullback_flat_integral,
      ``surjective_pointClosure_of_isPullback_flat_integral,
      ``_root_.AlgebraicGeometry.Scheme.Hom.mem_genericPoints_of_isPullback_flat_domainStalks,
      ``_root_.AlgebraicGeometry.Scheme.Hom.mem_genericPoints_of_isPullback_flat_component,
      ``arbitraryFieldExtension, ``arbitraryFlatIntegralSquare,
      ``disconnectedAmbientGenericImage, ``disconnectedAmbientComponentImage] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Flat base-change generic preservation uses only standard foundations."

end MotivicTest.FlatBaseChangeGeneric
