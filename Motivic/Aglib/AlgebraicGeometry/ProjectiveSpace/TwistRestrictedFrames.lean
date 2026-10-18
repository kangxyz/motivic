/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.TwistBaseChange
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.TwistFrameTransport

/-! # The actual projective twisting-module base-change isomorphism -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction

namespace AlgebraicGeometry.ProjectiveSpace

universe u
variable {R S : Type u} [CommRing R] [CommRing S]

private theorem schemeModules_comp_apply {X : Scheme.{u}} {M N P : X.Modules}
    (a : M ⟶ N) (b : N ⟶ P) (V : X.Opensᵒᵖ) (s : M.val.obj V) :
    (a ≫ b).val.app V s = b.val.app V (a.val.app V s) := rfl

private theorem schemeModules_pushforward_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : X.Modules} (a : M ⟶ N) (V : Y.Opensᵒᵖ)
    (s : ((pushforward f).obj M).val.obj V) :
    ((pushforward f).map a).val.app V s = a.val.app (op (f ⁻¹ᵁ V.unop)) s := rfl

private theorem schemeModules_restrict_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {M N : Y.Modules} (a : M ⟶ N) (V : X.Opensᵒᵖ)
    (s : ((restrictFunctor f).obj M).val.obj V) :
    ((restrictFunctor f).map a).val.app V s = a.val.app (op (f ''ᵁ V.unop)) s := rfl

private theorem schemeModules_unit_pushforward_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opensᵒᵖ) (s : Γ(Y, V.unop)) :
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val.app V s =
      (f.app V.unop).hom s := rfl

/-- The original coordinate frame, on an actual open subscheme. -/
def twistingRestrictIsoCore (ι : Type u) (n : ℤ) (i : ι)
    {U : (ProjectiveSpace R ι).Opens} (hi : U ≤ coordinateOpen R ι i) :
    (restrictFunctor U.ι).obj (twistingSheaf R ι n) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
  ((overFunctorEquiv U).app (twistingSheaf R ι n)).symm ≪≫
    (overEquiv U).functor.mapIso
      (restrictOverUnitIso (ProjectiveSpace R ι) (twistingSheaf R ι n)
        (homOfLE hi) (twistingLocalIso R ι n i)) ≪≫ overUnitIso U

/-- Evaluation of the transported coordinate frame is the original frame coefficient. -/
theorem twistingRestrictIsoCore_hom_apply (ι : Type u) (n : ℤ) (i : ι)
    {U : (ProjectiveSpace R ι).Opens} (hi : U ≤ coordinateOpen R ι i)
    (V : U.toScheme.Opens) (s : Γ((restrictFunctor U.ι).obj (twistingSheaf R ι n), V)) :
    (twistingRestrictIsoCore ι n i hi).hom.val.app (op V) s =
      (U.ι.appIso V).hom (twistingSectionsEquiv R ι n i
        ((U.ι_image_le V).trans hi) s) := by
  rfl

/-- The open-subscheme frame has the original coefficient under native identification. -/
theorem twistingRestrictIsoCore_hom_apply_coefficient (ι : Type u) (n : ℤ) (i : ι)
    {U : (ProjectiveSpace R ι).Opens} (hi : U ≤ coordinateOpen R ι i)
    (V : U.toScheme.Opens) (s : Γ((restrictFunctor U.ι).obj (twistingSheaf R ι n), V)) :
    (twistingRestrictIsoCore ι n i hi).hom.val.app (op V) s =
      twistingSectionsEquiv R ι n i ((U.ι_image_le V).trans hi) s := by
  rw [twistingRestrictIsoCore_hom_apply, Scheme.Opens.ι_appIso]
  rfl

/-- Existence of an actual open-subscheme frame with its original coefficient formula. -/
theorem exists_twistingRestrictIso (ι : Type u) (n : ℤ) (i : ι)
    {U : (ProjectiveSpace R ι).Opens} (hi : U ≤ coordinateOpen R ι i) :
    ∃ e : (restrictFunctor U.ι).obj (twistingSheaf R ι n) ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf,
      ∀ (V : U.toScheme.Opens)
        (s : Γ((restrictFunctor U.ι).obj (twistingSheaf R ι n), V)),
        e.hom.val.app (op V) s =
          twistingSectionsEquiv R ι n i ((U.ι_image_le V).trans hi) s :=
  ⟨twistingRestrictIsoCore ι n i hi,
    twistingRestrictIsoCore_hom_apply_coefficient ι n i hi⟩

/-- An opaque choice of the proved original-coordinate local frame. -/
def twistingRestrictIso (ι : Type u) (n : ℤ) (i : ι)
    {U : (ProjectiveSpace R ι).Opens} (hi : U ≤ coordinateOpen R ι i) :
    (restrictFunctor U.ι).obj (twistingSheaf R ι n) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
  Classical.choose (exists_twistingRestrictIso ι n i hi)

/-- The chosen frame has exactly the original coefficient formula. -/
theorem twistingRestrictIso_hom_apply_coefficient (ι : Type u) (n : ℤ) (i : ι)
    {U : (ProjectiveSpace R ι).Opens} (hi : U ≤ coordinateOpen R ι i)
    (V : U.toScheme.Opens) (s : Γ((restrictFunctor U.ι).obj (twistingSheaf R ι n), V)) :
    (twistingRestrictIso ι n i hi).hom.val.app (op V) s =
      twistingSectionsEquiv R ι n i ((U.ι_image_le V).trans hi) s :=
  Classical.choose_spec (exists_twistingRestrictIso ι n i hi) V s

/-- The restricted coefficient comparison in the original standard frame. -/
theorem twistingBaseChangePushforward_restrict_apply (f : R →+* S) (ι : Type u)
    (n : ℤ) (i : ι) (V : (coordinateOpen R ι i).toScheme.Opens)
    (s : Γ(twistingSheaf R ι n, (coordinateOpen R ι i).ι ''ᵁ V)) :
    twistingSectionsEquiv S ι n i
      ((image_morphismRestrict_preimage (map f ι) (coordinateOpen R ι i) V).le.trans
        (le_coordinateOpen_of_le_preimage f ι i le_rfl
          ((coordinateOpen R ι i).ι_image_le V)))
      ((twistingSheaf S ι n).val.map
        (eqToHom (image_morphismRestrict_preimage (map f ι) (coordinateOpen R ι i) V)).op
        ((twistingBaseChangePushforward f ι n).val.app
          (op ((coordinateOpen R ι i).ι ''ᵁ V)) s)) =
      ((map f ι ∣_ coordinateOpen R ι i).app V).hom
        (twistingSectionsEquiv R ι n i ((coordinateOpen R ι i).ι_image_le V) s) := by
  rw [twistingSectionsEquiv_eqToHom_opens S ι n i _
    (le_coordinateOpen_of_le_preimage f ι i le_rfl
      ((coordinateOpen R ι i).ι_image_le V))]
  rw [twistingBaseChangePushforward_local f ι n i _
    ((coordinateOpen R ι i).ι_image_le V)]
  rw [_root_.map_smul, twistingSectionsEquiv_generator, smul_eq_mul, mul_one]
  rw [morphismRestrict_app']
  rfl


end AlgebraicGeometry.ProjectiveSpace
