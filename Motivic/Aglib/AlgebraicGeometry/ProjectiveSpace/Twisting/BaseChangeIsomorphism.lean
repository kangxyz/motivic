/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting.RestrictedFrames
public import Motivic.Aglib.AlgebraicGeometry.Modules.LocalFrameComparison

/-! # The actual projective twisting-module base-change isomorphism -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The actual adjoint is locally invertible when its restricted map is the ring map in frames. -/
theorem isIso_restrict_adjoint_of_frames {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    {M : Y.Modules} {N : X.Modules}
    (eM : (restrictFunctor U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (eN : (restrictFunctor (f ⁻¹ᵁ U).ι).obj N ≅
      SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf)
    (φ : M ⟶ (pushforward f).obj N)
    (h : (restrictFunctor U.ι).map φ ≫ restrictedPushforwardMap f U N ≫
        (pushforward (f ∣_ U)).map eN.hom =
      eM.hom ≫ SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom) :
    IsIso ((restrictFunctor (f ⁻¹ᵁ U).ι).map
      (((pullbackPushforwardAdjunction f).homEquiv M N).symm φ)) := by
  have hf : (restrictFunctor U.ι).map φ ≫ restrictedPushforwardMap f U N =
      eM.hom ≫ SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom ≫
        (pushforward (f ∣_ U)).map eN.inv := by
    rw [← Category.assoc]
    apply (Iso.eq_comp_inv ((pushforward (f ∣_ U)).mapIso eN)).mpr
    exact (Category.assoc _ _ _).trans h
  have := isIso_adjoint_of_unit_frames (f ∣_ U) eM eN _ hf
  rw [restrictedAdjoint_eq]
  infer_instance

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- In the actual restricted frames, coefficient change is the native structure map. -/
theorem twistingBaseChangePushforward_restrict_frame (f : R →+* S) (ι : Type u)
    (n : ℤ) (i : ι) :
    (restrictFunctor (coordinateOpen R ι i).ι).map
        (twistingBaseChangePushforward f ι n) ≫
      restrictedPushforwardMap (map f ι) (coordinateOpen R ι i) (twistingSheaf S ι n) ≫
      (pushforward ((map f ι) ∣_ coordinateOpen R ι i)).map
        (twistingRestrictIso ι n i
          (le_coordinateOpen_of_le_preimage f ι i le_rfl le_rfl)).hom =
    (twistingRestrictIso ι n i le_rfl).hom ≫
      SheafOfModules.unitToPushforwardObjUnit
        ((map f ι) ∣_ coordinateOpen R ι i).toRingCatSheafHom := by
  apply localFrameComparison_of_apply
  intro V s
  refine (twistingRestrictIso_hom_apply_coefficient (R := S) ι n i
    (le_coordinateOpen_of_le_preimage f ι i le_rfl le_rfl) _ _).trans ?_
  refine (twistingBaseChangePushforward_restrict_apply f ι n i V s).trans ?_
  exact congrArg ((map f ι ∣_ coordinateOpen R ι i).app V).hom
    (twistingRestrictIso_hom_apply_coefficient (R := R) ι n i
      (U := coordinateOpen R ι i) le_rfl V s).symm

/-- The actual coefficient comparison of twists is invertible. -/
instance twistingBaseChangeMap_isIso (f : R →+* S) (ι : Type u) (n : ℤ) :
    IsIso (twistingBaseChangeMap f ι n) := by
  apply isIso_of_local_restrict
  intro x
  have hx : (map f ι) x ∈ ⨆ i, coordinateOpen R ι i := by
    rw [iSup_coordinateOpen_eq_top]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨i, hi⟩ := hx
  refine ⟨map f ι ⁻¹ᵁ coordinateOpen R ι i, hi, ?_⟩
  exact isIso_restrict_adjoint_of_frames (map f ι) (coordinateOpen R ι i)
    (twistingRestrictIso (R := R) ι n i le_rfl)
    (twistingRestrictIso (R := S) ι n i
      (le_coordinateOpen_of_le_preimage f ι i le_rfl le_rfl))
    (twistingBaseChangePushforward f ι n)
    (twistingBaseChangePushforward_restrict_frame f ι n i)

/-- Actual projective twists commute with arbitrary coefficient change. -/
def twistingBaseChangeIso (f : R →+* S) (ι : Type u) (n : ℤ) :
    (pullback (map f ι)).obj (twistingSheaf R ι n) ≅ twistingSheaf S ι n :=
  asIso (twistingBaseChangeMap f ι n)

end AlgebraicGeometry.ProjectiveSpace
