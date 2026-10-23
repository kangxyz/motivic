/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting.Frames
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Morphisms
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting.TransitionBaseChange

/-! # Actual projective twisting-module coefficient comparison -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- A map given by the actual structure-ring map in two unit frames has invertible adjoint. -/
theorem isIso_adjoint_of_unit_frames {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules}
    (eM : M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (eN : N ≅ SheafOfModules.unit X.ringCatSheaf)
    (φ : M ⟶ (pushforward f).obj N)
    (hφ : φ = eM.hom ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
      (pushforward f).map eN.inv) :
    IsIso (((pullbackPushforwardAdjunction f).homEquiv M N).symm φ) := by
  have h : ((pullbackPushforwardAdjunction f).homEquiv M N).symm φ =
      (pullback f).map eM.hom ≫ (pullbackUnitIso f).hom ≫ eN.inv := by
    apply ((pullbackPushforwardAdjunction f).homEquiv M N).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right, pullbackUnitIso_homEquiv]
    exact hφ
  rw [h]
  infer_instance

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules.Invertible
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The target frame on the exact inverse image of an original coordinate open. -/
def mappedTwistingGenerator (f : R →+* S) (ι : Type u) (n : ℤ) (i : ι) :
    Γ((Scheme.Modules.pushforward (map f ι)).obj (twistingSheaf S ι n),
      coordinateOpen R ι i) :=
  twistingGenerator S ι n i
    (le_coordinateOpen_of_le_preimage f ι i le_rfl le_rfl)

/-- Original structure maps and transition units make these frames compatible. -/
theorem mappedTwistingGenerator_compatible (f : R →+* S) (ι : Type u) (n : ℤ)
    (i j : ι) (V : (ProjectiveSpace R ι).Opens)
    (hi : V ≤ coordinateOpen R ι i) (hj : V ≤ coordinateOpen R ι j) :
    ((Scheme.Modules.pushforward (map f ι)).obj (twistingSheaf S ι n)).val.map
        (homOfLE hj).op (mappedTwistingGenerator f ι n j) =
      (((coordinateUnitCocycle R ι).zpow (-n)).transitionOn i j hi hj).val •
        ((Scheme.Modules.pushforward (map f ι)).obj (twistingSheaf S ι n)).val.map
          (homOfLE hi).op (mappedTwistingGenerator f ι n i) := by
  rw [UnitCocycle.zpow_transitionOn, coordinateUnitCocycle_transitionOn]
  change (twistingSheaf S ι n).val.map
      (homOfLE (((TopologicalSpace.Opens.map (map f ι).base).map (homOfLE hj)).le)).op
      (twistingGenerator S ι n j
        (le_coordinateOpen_of_le_preimage f ι j le_rfl le_rfl)) =
    ((map f ι).app V).hom (coordinateTransitionOn R ι i j hi hj ^ (-n)).val •
      (twistingSheaf S ι n).val.map
        (homOfLE (((TopologicalSpace.Opens.map (map f ι).base).map (homOfLE hi)).le)).op
        (twistingGenerator S ι n i
          (le_coordinateOpen_of_le_preimage f ι i le_rfl le_rfl))
  rw [twistingGenerator_restrict S ι n j, twistingGenerator_restrict S ι n i]
  have hu := congrArg Units.val (coordinateTransitionOn_zpow_map_app f ι i j hi hj (-n))
  rw [show ((map f ι).app V).hom (coordinateTransitionOn R ι i j hi hj ^ (-n)).val =
      (coordinateTransitionOn S ι i j
        (le_coordinateOpen_of_le_preimage f ι i le_rfl hi)
        (le_coordinateOpen_of_le_preimage f ι j le_rfl hj) ^ (-n)).val from hu]
  exact twistingGenerator_transition S ι n i j _ _

/-- Actual coefficient change of projective twist sections, before adjunction. -/
def twistingBaseChangePushforward (f : R →+* S) (ι : Type u) (n : ℤ) :
    twistingSheaf R ι n ⟶ (Scheme.Modules.pushforward (map f ι)).obj (twistingSheaf S ι n) :=
  ((coordinateUnitCocycle R ι).zpow (-n)).homOfLocalSections _
    (iSup_coordinateOpen_eq_top R ι) (mappedTwistingGenerator f ι n)
    (mappedTwistingGenerator_compatible f ι n)

/-- The original coefficient map in a common coordinate frame. -/
theorem twistingBaseChangePushforward_local (f : R →+* S) (ι : Type u) (n : ℤ)
    (i : ι) (V : (ProjectiveSpace R ι).Opens) (hi : V ≤ coordinateOpen R ι i)
    (s : Γ(twistingSheaf R ι n, V)) :
    (twistingBaseChangePushforward f ι n).val.app (op V) s =
      ((map f ι).app V).hom (twistingSectionsEquiv R ι n i hi s) •
        twistingGenerator S ι n i (le_coordinateOpen_of_le_preimage f ι i le_rfl hi) := by
  have h := ((coordinateUnitCocycle R ι).zpow (-n)).homOfLocalSections_apply _
    (iSup_coordinateOpen_eq_top R ι) (mappedTwistingGenerator f ι n)
    (mappedTwistingGenerator_compatible f ι n) i V hi s
  change (twistingBaseChangePushforward f ι n).val.app (op V) s =
    ((map f ι).app V).hom (twistingSectionsEquiv R ι n i hi s) •
      (twistingSheaf S ι n).val.map
        (homOfLE (((TopologicalSpace.Opens.map (map f ι).base).map (homOfLE hi)).le)).op
        (twistingGenerator S ι n i
          (le_coordinateOpen_of_le_preimage f ι i le_rfl le_rfl)) at h
  rw [twistingGenerator_restrict S ι n i] at h
  exact h

/-- The actual pullback comparison, adjoint to coefficient change. -/
def twistingBaseChangeMap (f : R →+* S) (ι : Type u) (n : ℤ) :
    (Scheme.Modules.pullback (map f ι)).obj (twistingSheaf R ι n) ⟶ twistingSheaf S ι n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (map f ι)).homEquiv _ _).symm
    (twistingBaseChangePushforward f ι n)

end AlgebraicGeometry.ProjectiveSpace
