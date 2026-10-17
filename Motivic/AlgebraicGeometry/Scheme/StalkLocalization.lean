/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Actual stalks of the canonical stalk-spectrum morphism

The canonical morphism `Spec (𝒪_{X,x}) ⟶ X` is flat. Since it is also a
preimmersion, all its actual stalk maps are isomorphisms. Composing with the
standard affine stalk isomorphism identifies the global scheme stalk at the
image of a prime with the localization of the original stalk at that prime.
No finiteness, Noetherian, reducedness or dimension assumption is used.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

/-- The canonical morphism from an actual scheme stalk spectrum is flat. -/
theorem flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top x)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx, IsAffineOpen.fromSpecStalk]
  have : Flat (Spec.map (X.presheaf.germ U x hx)) := by
    rw [Flat.SpecMap_iff]
    let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨x, hx⟩
    exact IsLocalization.flat (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- A flat morphism surjective on stalks has bijective actual stalk maps:
flat local maps are faithfully flat and therefore injective. -/
theorem stalkMap_bijective_of_flat_of_surjectiveOnStalks {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [SurjectiveOnStalks f] (x : X) :
    Function.Bijective (f.stalkMap x) := by
  refine ⟨?_, f.stalkMap_surjective x⟩
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

/-- Every actual stalk map of the canonical stalk-spectrum morphism is bijective. -/
theorem fromSpecStalk_stalkMap_bijective (X : Scheme.{u}) (x : X)
    (p : Spec (X.presheaf.stalk x)) :
    Function.Bijective ((X.fromSpecStalk x).stalkMap p) := by
  have := flat_fromSpecStalk X x
  exact stalkMap_bijective_of_flat_of_surjectiveOnStalks _ p

/-- The actual global scheme stalk at the image of a prime is the stalk of the
canonical stalk spectrum at that prime. The forward map is the actual stalk map. -/
noncomputable def fromSpecStalkStalkIso (X : Scheme.{u}) (x : X)
    (p : Spec (X.presheaf.stalk x)) :
    X.presheaf.stalk (X.fromSpecStalk x p) ≅ (Spec (X.presheaf.stalk x)).presheaf.stalk p := by
  have : IsIso ((X.fromSpecStalk x).stalkMap p) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (fromSpecStalk_stalkMap_bijective X x p)
  exact asIso ((X.fromSpecStalk x).stalkMap p)

@[simp]
theorem fromSpecStalkStalkIso_hom (X : Scheme.{u}) (x : X)
    (p : Spec (X.presheaf.stalk x)) :
    (fromSpecStalkStalkIso X x p).hom = (X.fromSpecStalk x).stalkMap p := rfl

/-- A localization of the original stalk at any prime agrees with the actual
global scheme stalk at its image through the actual canonical stalk map. -/
noncomputable def fromSpecStalkLocalizationIso (X : Scheme.{u}) (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.presheaf.stalk (X.fromSpecStalk x p) ≅ CommRingCat.of (Localization.AtPrime p.asIdeal) :=
  fromSpecStalkStalkIso X x p ≪≫ Spec.stalkIso (X.presheaf.stalk x) p

@[simp]
theorem fromSpecStalkLocalizationIso_hom (X : Scheme.{u}) (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    (fromSpecStalkLocalizationIso X x p).hom =
      (X.fromSpecStalk x).stalkMap p ≫ (Spec.stalkIso (X.presheaf.stalk x) p).hom := rfl

/-- Every point of the stalk spectrum maps to a generalization of the original point. -/
theorem fromSpecStalk_image_specializes (X : Scheme.{u}) (x : X)
    (p : Spec (X.presheaf.stalk x)) : X.fromSpecStalk x p ⤳ x := by
  have h : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
  rwa [X.range_fromSpecStalk] at h

set_option backward.isDefEq.respectTransparency.types false in
/-- The global specialization action on the actual image stalk is carried to
its literal localization algebra map. This is an equality of the actual maps. -/
@[reassoc]
theorem stalkSpecializes_fromSpecStalkLocalizationIso (X : Scheme.{u}) (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.presheaf.stalkSpecializes (fromSpecStalk_image_specializes X x p) ≫
        (fromSpecStalkLocalizationIso X x p).hom =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal)) := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hx => ?_
  simp only [fromSpecStalkLocalizationIso_hom, Category.assoc,
    TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap_assoc,
    Scheme.fromSpecStalk_app hx]
  simp only [TopCat.Presheaf.germ_res_assoc,
    Spec.germ_stalkMapIso_hom, Iso.inv_hom_id_assoc]

/-- The actual image stalk and literal localization are equivalent as algebras
for the genuine specialization action from the original scheme stalk. -/
noncomputable def fromSpecStalkLocalizationAlgEquiv (X : Scheme.{u}) (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk (X.fromSpecStalk x p)) :=
      (X.presheaf.stalkSpecializes (fromSpecStalk_image_specializes X x p)).hom.toAlgebra
    X.presheaf.stalk (X.fromSpecStalk x p) ≃ₐ[X.presheaf.stalk x]
      Localization.AtPrime p.asIdeal := by
  letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk (X.fromSpecStalk x p)) :=
    (X.presheaf.stalkSpecializes (fromSpecStalk_image_specializes X x p)).hom.toAlgebra
  exact { (fromSpecStalkLocalizationIso X x p).commRingCatIsoToRingEquiv with
    commutes' := fun r => ConcreteCategory.congr_hom
      (stalkSpecializes_fromSpecStalkLocalizationIso X x p) r }

/-- Under the actual specialization action, the global image stalk really is
a localization of the original stalk at the specified prime. -/
theorem isLocalization_fromSpecStalkImage (X : Scheme.{u}) (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk (X.fromSpecStalk x p)) :=
      (X.presheaf.stalkSpecializes (fromSpecStalk_image_specializes X x p)).hom.toAlgebra
    IsLocalization.AtPrime (X.presheaf.stalk (X.fromSpecStalk x p)) p.asIdeal := by
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk (X.fromSpecStalk x p)) :=
    (X.presheaf.stalkSpecializes (fromSpecStalk_image_specializes X x p)).hom.toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl
    (fromSpecStalkLocalizationAlgEquiv X x p).symm

end Motivic
