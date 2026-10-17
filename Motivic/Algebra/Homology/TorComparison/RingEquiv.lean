/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.FlatBaseChange
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Actual Tor transport through ring and scalar isomorphisms

Flat base change along a ring isomorphism and the genuine scalar-extension
adjunction identify categorical Tor before and after scalar restriction.
Module isomorphisms with specified scalar actions can then be transported
without assuming any derived comparison. The final helper constructs these
module isomorphisms from an actual commuting square of ring homomorphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace Motivic.TorComparison

variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]

set_option backward.isDefEq.respectTransparency false in
/-- Actual Tor commutes with restriction along a ring isomorphism. -/
def ringEquivRestrictTorIso (e : R ≃+* S) (M N : ModuleCat.{u} S) (n : ℕ) :
    ((Tor (ModuleCat R) n).obj ((ModuleCat.restrictScalars e.toRingHom).obj M)).obj
        ((ModuleCat.restrictScalars e.toRingHom).obj N) ≅
      (ModuleCat.restrictScalars e.toRingHom).obj (((Tor (ModuleCat S) n).obj M).obj N) := by
  let adj : ModuleCat.extendScalars.{u, u, u} e.toRingHom ⊣
      ModuleCat.restrictScalars.{u} e.toRingHom :=
    ModuleCat.extendRestrictScalarsAdj e.toRingHom
  have : (ModuleCat.restrictScalars.{u} e.toRingHom).IsEquivalence := inferInstance
  have : (ModuleCat.extendScalars.{u, u, u} e.toRingHom).IsEquivalence :=
    adj.isEquivalence_left_of_isEquivalence_right
  let cM : (ModuleCat.extendScalars e.toRingHom).obj
      ((ModuleCat.restrictScalars e.toRingHom).obj M) ≅ M := asIso (adj.counit.app M)
  let cN : (ModuleCat.extendScalars e.toRingHom).obj
      ((ModuleCat.restrictScalars e.toRingHom).obj N) ≅ N := asIso (adj.counit.app N)
  let T := ((Tor (ModuleCat R) n).obj ((ModuleCat.restrictScalars e.toRingHom).obj M)).obj
    ((ModuleCat.restrictScalars e.toRingHom).obj N)
  have : IsIso (adj.unit.app T) := adj.isIso_unit_app_of_iso
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).counitIso.app T).symm
  exact asIso (adj.unit.app T) ≪≫ (ModuleCat.restrictScalars e.toRingHom).mapIso
    (flatBaseChangeTorIso e.toRingHom (RingHom.Flat.of_bijective e.bijective) _ _ n ≪≫
      ((Tor (ModuleCat S) n).mapIso cM).app _ ≪≫
      ((Tor (ModuleCat S) n).obj M).mapIso cN)

/-- Module identifications with the actual restricted scalar actions induce
an isomorphism of actual Tor modules in every degree. -/
def torIsoOfScalarIso (e : R ≃+* S) (M N : ModuleCat.{u} R)
    (M' N' : ModuleCat.{u} S)
    (hM : M ≅ (ModuleCat.restrictScalars e.toRingHom).obj M')
    (hN : N ≅ (ModuleCat.restrictScalars e.toRingHom).obj N') (n : ℕ) :
    ((Tor (ModuleCat R) n).obj M).obj N ≅
      (ModuleCat.restrictScalars e.toRingHom).obj (((Tor (ModuleCat S) n).obj M').obj N') :=
  ((Tor (ModuleCat R) n).mapIso hM).app N ≪≫
    ((Tor (ModuleCat R) n).obj ((ModuleCat.restrictScalars e.toRingHom).obj M')).mapIso hN ≪≫
    ringEquivRestrictTorIso e M' N' n

set_option backward.isDefEq.respectTransparency false in
/-- A commuting square of actual ring homomorphisms gives the scalar-compatible
module isomorphism used by the Tor transport theorem. -/
def ringModuleIso (e : R ≃+* S) (a : A ≃+* B) (f : R →+* A) (g : S →+* B)
    (h : ∀ r, a (f r) = g (e r)) :
    (ModuleCat.restrictScalars f).obj (ModuleCat.of A A) ≅
      (ModuleCat.restrictScalars e.toRingHom).obj
        ((ModuleCat.restrictScalars g).obj (ModuleCat.of B B)) := by
  let : Module R A := Module.compHom A f
  let : Module R B := Module.compHom B (g.comp e.toRingHom)
  let a' : A ≃ₗ[R] B := {
    __ := a.toAddEquiv
    map_smul' r x := by
      change a (f r * x) = g (e r) * a x
      rw [map_mul, h] }
  exact a'.toModuleIso

/-- The scalar-compatible module isomorphism is the given concrete ring map. -/
theorem ringModuleIso_hom_apply (e : R ≃+* S) (a : A ≃+* B)
    (f : R →+* A) (g : S →+* B) (h : ∀ r, a (f r) = g (e r)) (x : A) :
    (ringModuleIso e a f g h).hom x = a x := rfl

end Motivic.TorComparison
