/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.LiteralQuotientTorCoherence
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.QuotientScalarExtensionCoherence
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.TorSupportBaseChangeCoordinates

/-!
# Coherence of canonical supported Tor restrictions

Canonical supported Tor restriction is the actual quotient scalar extension
followed by flat Tor base change and literal quotient-coefficient identification.
The target of direct restriction is viewed over the canonically equal iterated
image-support ideal. The resulting cocycle is proved on the actual maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace ModuleCat.TorComparison

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The literal support quotient map commutes with the ambient quotient projections. -/
theorem supportQuotientMapSup_square (f : R →+* S) (J K : Ideal R) :
    (supportQuotientMapSup f J K).comp (Ideal.Quotient.mk (J ⊔ K)) =
      (Ideal.Quotient.mk (J.map f ⊔ K.map f)).comp f :=
  Ideal.quotientMap_comp_mk _

/-- The direct support image is the actual sum of the two iterated image ideals. -/
theorem torSupportCompositeIdeal (f : R →+* S) (g : S →+* T) (J K : Ideal R) :
    (J ⊔ K).map (g.comp f) = (J.map f).map g ⊔ (K.map f).map g := by
  rw [Ideal.map_sup, Ideal.map_map, Ideal.map_map]

/-- The iterated support quotient annihilates the direct literal target Tor. -/
theorem torSupportCompositeTarget_support (f : R →+* S) (g : S →+* T)
    (J K : Ideal R) (n : ℕ) :
    (J.map f).map g ⊔ (K.map f).map g ≤ Module.annihilator T
      (((Tor (ModuleCat T) n).obj (ModuleCat.of T (T ⧸ K.map (g.comp f)))).obj
        (ModuleCat.of T (T ⧸ J.map (g.comp f)))) := by
  simpa only [Ideal.map_map] using
    quotient_support_le_annihilator (J.map (g.comp f)) (K.map (g.comp f)) n

/-- Direct literal target Tor over the canonically identified iterated support ring. -/
def torSupportCompositeTarget (f : R →+* S) (g : S →+* T) (J K : Ideal R) (n : ℕ) :
    ModuleCat.{u} (T ⧸ ((J.map f).map g ⊔ (K.map f).map g)) :=
  quotientModule _
    (((Tor (ModuleCat T) n).obj (ModuleCat.of T (T ⧸ K.map (g.comp f)))).obj
      (ModuleCat.of T (T ⧸ J.map (g.comp f))))
    (torSupportCompositeTarget_support f g J K n)

/-- The two actual image-ideal associators act on the supported target Tor. -/
def torSupportCompositeTargetIso (f : R →+* S) (g : S →+* T) (J K : Ideal R) (n : ℕ) :
    torSupportModule ((J.map f).map g) ((K.map f).map g) n ≅
      torSupportCompositeTarget f g J K n :=
  quotientLinearIso _ (quotient_support_le_annihilator _ _ n)
    (torSupportCompositeTarget_support f g J K n) (mappedQuotientsTorCompIso f g J K n)

/-- Direct canonical restriction, with its actual quotient map and image-support associator. -/
def torSupportDirectCompositeIso (f : R →+* S) (g : S →+* T)
    (hf : f.Flat) (hg : g.Flat) (J K : Ideal R) (n : ℕ) :
    (ModuleCat.extendScalars
      ((supportQuotientMapSup g (J.map f) (K.map f)).comp
        (supportQuotientMapSup f J K))).obj (torSupportModule J K n) ≅
      torSupportCompositeTarget f g J K n :=
  quotientScalarExtensionIsoOfMap (g.comp f) (J ⊔ K)
      ((J.map f).map g ⊔ (K.map f).map g) (torSupportCompositeIdeal f g J K)
      ((supportQuotientMapSup g (J.map f) (K.map f)).comp (supportQuotientMapSup f J K))
      (quotientScalarSquare_comp f g _ _ _ _ _
        (supportQuotientMapSup_square f J K)
        (supportQuotientMapSup_square g (J.map f) (K.map f)))
      _ (quotient_support_le_annihilator J K n) ≪≫
    quotientLinearIso _ _ (torSupportCompositeTarget_support f g J K n)
      (flatBaseChangeLiteralTorIso (g.comp f) (hf.comp hg) J K n)

/-- The direct comparison retains the exact ambient canonical flat Tor map on pure tensors. -/
@[simp] theorem torSupportDirectCompositeIso_hom_tmul (f : R →+* S) (g : S →+* T)
    (hf : f.Flat) (hg : g.Flat) (J K : Ideal R) (n : ℕ) (t : T)
    (m : torSupportModule J K n) :
    (torSupportDirectCompositeIso f g hf hg J K n).hom
      (Ideal.Quotient.mk ((J.map f).map g ⊔ (K.map f).map g) t ⊗ₜ[R ⧸ (J ⊔ K),
        (supportQuotientMapSup g (J.map f) (K.map f)).comp (supportQuotientMapSup f J K)] m) =
      (flatBaseChangeLiteralTorIso (g.comp f) (hf.comp hg) J K n).hom
        (t ⊗ₜ[R,g.comp f] m) := by
  exact congrArg (flatBaseChangeLiteralTorIso (g.comp f) (hf.comp hg) J K n).hom
    (quotientScalarExtensionIsoOfMap_hom_tmul (g.comp f) (J ⊔ K)
      ((J.map f).map g ⊔ (K.map f).map g) (torSupportCompositeIdeal f g J K)
      ((supportQuotientMapSup g (J.map f) (K.map f)).comp (supportQuotientMapSup f J K))
      (quotientScalarSquare_comp f g _ _ _ _ _
        (supportQuotientMapSup_square f J K)
        (supportQuotientMapSup_square g (J.map f) (K.map f)))
      _ (quotient_support_le_annihilator J K n) t m)

/-- Actual supported Tor restrictions obey the canonical scalar and image-ideal associators. -/
theorem torSupportBaseChangeIso_hom_comp (f : R →+* S) (g : S →+* T)
    (hf : f.Flat) (hg : g.Flat) (J K : Ideal R) (n : ℕ) :
    (ModuleCat.extendScalarsComp (supportQuotientMapSup f J K)
        (supportQuotientMapSup g (J.map f) (K.map f))).hom.app (torSupportModule J K n) ≫
      (ModuleCat.extendScalars (supportQuotientMapSup g (J.map f) (K.map f))).map
        (torSupportBaseChangeIso f hf J K n).hom ≫
      (torSupportBaseChangeIso g hg (J.map f) (K.map f) n).hom ≫
      (torSupportCompositeTargetIso f g J K n).hom =
    (torSupportDirectCompositeIso f g hf hg J K n).hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  have ha := ModuleCat.extendScalarsComp_hom_app_one_tmul
    (supportQuotientMapSup f J K) (supportQuotientMapSup g (J.map f) (K.map f))
    (torSupportModule J K n) m
  have h₁ := torSupportBaseChangeIso_hom_tmul f hf J K n 1 m
  have h₂ := torSupportBaseChangeIso_hom_tmul g hg (J.map f) (K.map f) n 1
    ((flatBaseChangeLiteralTorIso f hf J K n).hom ((1 : S) ⊗ₜ[R,f] m))
  have h₃ := torSupportDirectCompositeIso_hom_tmul f g hf hg J K n 1 m
  simp only [map_one] at h₁ h₂ h₃
  have hc := congrArg (fun φ => φ ((1 : T) ⊗ₜ[R,g.comp f] m))
    (flatBaseChangeLiteralTorIso_hom_comp f g hf hg J K n)
  have hb := ModuleCat.extendScalarsComp_hom_app_one_tmul f g
    (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).obj
      (ModuleCat.of R (R ⧸ J))) m
  have hc' := (congrArg (fun x => (mappedQuotientsTorCompIso f g J K n).hom
      ((flatBaseChangeLiteralTorIso g hg (J.map f) (K.map f) n).hom
        (((ModuleCat.extendScalars g).map (flatBaseChangeLiteralTorIso f hf J K n).hom) x)))
      hb).symm.trans hc
  exact (congrArg (fun x => (torSupportCompositeTargetIso f g J K n).hom
      ((torSupportBaseChangeIso g hg (J.map f) (K.map f) n).hom
        (((ModuleCat.extendScalars (supportQuotientMapSup g (J.map f) (K.map f))).map
          (torSupportBaseChangeIso f hf J K n).hom) x))) ha).trans
    ((congrArg (fun x => (torSupportCompositeTargetIso f g J K n).hom
      ((torSupportBaseChangeIso g hg (J.map f) (K.map f) n).hom
        ((1 : T ⧸ ((J.map f).map g ⊔ (K.map f).map g)) ⊗ₜ[S ⧸ (J.map f ⊔ K.map f),
          supportQuotientMapSup g (J.map f) (K.map f)] x))) h₁).trans
      ((congrArg (torSupportCompositeTargetIso f g J K n).hom h₂).trans
        (hc'.trans h₃.symm)))

/-- Changing an equal support ideal is restriction along its canonical ring isomorphism. -/
def quotientModuleChangeIdealIso (I I' : Ideal R) (h : I = I')
    (M : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M)
    (hM' : I' ≤ Module.annihilator R M) :
    quotientModule I M hM ≅
      (ModuleCat.restrictScalars (Ideal.quotEquivOfEq h).toRingHom).obj
        (quotientModule I' M hM') := by
  let e : quotientModule I M hM ≃ₗ[R ⧸ I]
      ((ModuleCat.restrictScalars (Ideal.quotEquivOfEq h).toRingHom).obj
        (quotientModule I' M hM')) :=
    { toFun := fun m => m
      invFun := fun m => m
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a m
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        rfl }
  exact e.toModuleIso

/-- The actual support-ring associator for iterated versus composite ideal images. -/
def torSupportCompositeRingIso (f : R →+* S) (g : S →+* T) (J K : Ideal R) :
    (T ⧸ ((J.map f).map g ⊔ (K.map f).map g)) ≃+*
      (T ⧸ (J.map (g.comp f) ⊔ K.map (g.comp f))) :=
  Ideal.quotEquivOfEq (by rw [Ideal.map_map, Ideal.map_map])

/-- The direct target is literal supported Tor restricted along the actual ring associator. -/
def torSupportCompositeTargetRestrictIso (f : R →+* S) (g : S →+* T)
    (J K : Ideal R) (n : ℕ) :
    torSupportCompositeTarget f g J K n ≅
      (ModuleCat.restrictScalars (torSupportCompositeRingIso f g J K).toRingHom).obj
        (torSupportModule (J.map (g.comp f)) (K.map (g.comp f)) n) :=
  quotientModuleChangeIdealIso _ _ _ _ _ _

/-- The identity-image support ideal annihilates the actual original Tor. -/
theorem torSupportIdentityTarget_support (J K : Ideal R) (n : ℕ) :
    J.map (RingHom.id R) ⊔ K.map (RingHom.id R) ≤ Module.annihilator R
      (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).obj
        (ModuleCat.of R (R ⧸ J))) := by
  simpa only [Ideal.map_id] using quotient_support_le_annihilator J K n

/-- Original Tor over the canonically identified identity-image support ring. -/
def torSupportIdentityTarget (J K : Ideal R) (n : ℕ) :
    ModuleCat.{u} (R ⧸ (J.map (RingHom.id R) ⊔ K.map (RingHom.id R))) :=
  quotientModule _
    (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).obj (ModuleCat.of R (R ⧸ J)))
    (torSupportIdentityTarget_support J K n)

/-- The two actual identity-image quotient identifications act on supported Tor. -/
def torSupportIdentityTargetIso (J K : Ideal R) (n : ℕ) :
    torSupportModule (J.map (RingHom.id R)) (K.map (RingHom.id R)) n ≅
      torSupportIdentityTarget J K n :=
  quotientLinearIso _ (quotient_support_le_annihilator _ _ n)
    (torSupportIdentityTarget_support J K n) (mappedQuotientsTorIdIso J K n)

/-- The actual scalar unitor with its identity-image support ring identification. -/
def torSupportUnitIso (J K : Ideal R) (n : ℕ) :
    (ModuleCat.extendScalars (supportQuotientMapSup (RingHom.id R) J K)).obj
        (torSupportModule J K n) ≅ torSupportIdentityTarget J K n :=
  quotientScalarExtensionIsoOfMap (RingHom.id R) (J ⊔ K)
      (J.map (RingHom.id R) ⊔ K.map (RingHom.id R)) (Ideal.map_sup _ J K)
      (supportQuotientMapSup (RingHom.id R) J K)
      (supportQuotientMapSup_square (RingHom.id R) J K)
      _ (quotient_support_le_annihilator J K n) ≪≫
    quotientLinearIso _ _ (torSupportIdentityTarget_support J K n)
      ((ModuleCat.extendScalarsId R).app _)

/-- The transported support unitor is the identity on the generating unit tensors. -/
@[simp] theorem torSupportUnitIso_hom_one_tmul (J K : Ideal R) (n : ℕ)
    (m : torSupportModule J K n) :
    (torSupportUnitIso J K n).hom
      ((1 : R ⧸ (J.map (RingHom.id R) ⊔ K.map (RingHom.id R))) ⊗ₜ[R ⧸ (J ⊔ K),
        supportQuotientMapSup (RingHom.id R) J K] m) = m := by
  have h := quotientScalarExtensionIsoOfMap_hom_tmul (RingHom.id R) (J ⊔ K)
    (J.map (RingHom.id R) ⊔ K.map (RingHom.id R)) (Ideal.map_sup _ J K)
    (supportQuotientMapSup (RingHom.id R) J K)
    (supportQuotientMapSup_square (RingHom.id R) J K)
    _ (quotient_support_le_annihilator J K n) 1 m
  simp only [map_one] at h
  exact (congrArg ((ModuleCat.extendScalarsId R).hom.app _) h).trans
    (ModuleCat.extendScalarsId_hom_app_one_tmul _ m)

/-- Actual supported Tor restriction obeys the scalar and image-ideal identity law. -/
theorem torSupportBaseChangeIso_hom_id (J K : Ideal R) (n : ℕ) :
    (torSupportBaseChangeIso (RingHom.id R) (RingHom.Flat.id R) J K n).hom ≫
        (torSupportIdentityTargetIso J K n).hom = (torSupportUnitIso J K n).hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  have h := torSupportBaseChangeIso_hom_tmul (RingHom.id R) (RingHom.Flat.id R) J K n 1 m
  simp only [map_one] at h
  have hc := congrArg (fun φ => φ ((1 : R) ⊗ₜ[R,RingHom.id R] m))
    (flatBaseChangeLiteralTorIso_hom_id J K n)
  exact (congrArg (torSupportIdentityTargetIso J K n).hom h).trans
    (hc.trans ((ModuleCat.extendScalarsId_hom_app_one_tmul _ m).trans
      (torSupportUnitIso_hom_one_tmul J K n m).symm))

/-- The actual support-ring unitor for the identity image ideals. -/
def torSupportIdentityRingIso (J K : Ideal R) :
    (R ⧸ (J.map (RingHom.id R) ⊔ K.map (RingHom.id R))) ≃+* (R ⧸ (J ⊔ K)) :=
  Ideal.quotEquivOfEq (by rw [Ideal.map_id, Ideal.map_id])

/-- The identity target is literal supported Tor restricted along the ring unitor. -/
def torSupportIdentityTargetRestrictIso (J K : Ideal R) (n : ℕ) :
    torSupportIdentityTarget J K n ≅
      (ModuleCat.restrictScalars (torSupportIdentityRingIso J K).toRingHom).obj
        (torSupportModule J K n) :=
  quotientModuleChangeIdealIso _ _ _ _ _ _

/-- The support-ring associator identifies the composed quotient map with direct restriction. -/
theorem supportQuotientMapSup_comp (f : R →+* S) (g : S →+* T) (J K : Ideal R) :
    (torSupportCompositeRingIso f g J K).toRingHom.comp
        ((supportQuotientMapSup g (J.map f) (K.map f)).comp (supportQuotientMapSup f J K)) =
      supportQuotientMapSup (g.comp f) J K := by
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The actual support-ring unitor identifies the identity quotient map with the identity. -/
theorem supportQuotientMapSup_id (J K : Ideal R) :
    (torSupportIdentityRingIso J K).toRingHom.comp (supportQuotientMapSup (RingHom.id R) J K) =
      RingHom.id (R ⧸ (J ⊔ K)) := by
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end ModuleCat.TorComparison
