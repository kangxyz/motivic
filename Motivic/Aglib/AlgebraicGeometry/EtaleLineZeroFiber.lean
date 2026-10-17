/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoordinateGraphIdeal
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # The actual zero fiber of an etale affine-line chart is Cartier -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- Flat pullback of the literal zero section has its original ideal trivialized,
not merely an abstract Cartier class. -/
def etaleLineZeroFiberIdealIso (B : Type u) [CommRing B] {Y : Scheme.{u}}
    (h : Y ⟶ Spec (.of (Polynomial B))) [Flat h] :
    SheafOfModules.unit Y.ringCatSheaf ≅
      idealModule (pullback.snd
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : B)))) h) := by
  let z := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : B)))
  have : IsClosedImmersion z := IsClosedImmersion.spec_of_surjective _
    (fun b => ⟨Polynomial.C b, by simp⟩)
  let v := idealPullbackMap z (pullback.snd z h) h (pullback.fst z h)
    (pullback.condition (f := z) (g := h))
  have : IsIso v := idealPullbackMap_isIso_of_flat_ambient z (pullback.snd z h) h
    (pullback.fst z h) (pullback.condition (f := z) (g := h)) (IsPullback.of_hasPullback z h)
  exact (pullbackUnitIso h).symm ≪≫
    (Scheme.Modules.pullback h).mapIso (coordinateGraphIdealIso B 0) ≪≫ asIso v

/-- This is the actual kernel ideal of the zero-fiber closed immersion. -/
theorem etaleLineZeroFiber_isLocallyRankOne (B : Type u) [CommRing B] {Y : Scheme.{u}}
    (h : Y ⟶ Spec (.of (Polynomial B))) [Flat h] :
    IsLocallyRankOne Y (idealModule (pullback.snd
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : B)))) h)) :=
  isLocallyRankOne_of_iso Y (etaleLineZeroFiberIdealIso B h)
    (isLocallyRankOne_of_iso Y
      (coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit Y.ringCatSheaf))
      (trivialLineBundle Y).property)

end AlgebraicGeometry.Scheme.Hom
