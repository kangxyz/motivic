/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.TorSupportRestrictionCoherence

/-!
# Source transport for canonical supported Tor coherence

The actual scalar-extension source transport across equal target ideals is
constructed from canonical quotient pushout comparisons. Its pure-tensor
coordinate identifies the direct comparison in the supported cocycle with the
existing literal supported Tor base-change map, restricted along the actual
support-ring associator. The identity case retains the genuine scalar unitor.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace ModuleCat.TorComparison

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The inverse canonical quotient comparison also retains tensor representatives. -/
@[simp] theorem quotientScalarExtensionIsoOfMap_inv_tmul (f : R →+* S)
    (I : Ideal R) (J : Ideal S) (hJ : I.map f = J) (q : R ⧸ I →+* S ⧸ J)
    (hq : q.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp f)
    (M : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M) (s : S) (m : M) :
    letI := quotientModuleAction I M hM
    (quotientScalarExtensionIsoOfMap f I J hJ q hq M hM).inv (s ⊗ₜ[R,f] m) =
      Ideal.Quotient.mk J s ⊗ₜ[R ⧸ I,q] (m : quotientModule I M hM) := by
  have h := congrArg (quotientScalarExtensionIsoOfMap f I J hJ q hq M hM).inv
    (quotientScalarExtensionIsoOfMap_hom_tmul f I J hJ q hq M hM s m)
  exact h.symm.trans (ModuleCat.inv_hom_apply
    (quotientScalarExtensionIsoOfMap f I J hJ q hq M hM) _)

/-- Canonical scalar-extension transport across an actual equality of image support ideals. -/
def quotientScalarExtensionChangeIdealIso (f : R →+* S)
    (I : Ideal R) (J J' : Ideal S) (hJ : I.map f = J) (hJ' : I.map f = J')
    (q : R ⧸ I →+* S ⧸ J) (q' : R ⧸ I →+* S ⧸ J')
    (hq : q.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp f)
    (hq' : q'.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J').comp f)
    (M : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M) :
    (ModuleCat.extendScalars q).obj (quotientModule I M hM) ≅
      (ModuleCat.restrictScalars
        (Ideal.quotEquivOfEq (hJ.symm.trans hJ') : S ⧸ J →+* S ⧸ J')).obj
        ((ModuleCat.extendScalars q').obj (quotientModule I M hM)) :=
  quotientScalarExtensionIsoOfMap f I J hJ q hq M hM ≪≫
    quotientModuleChangeIdealIso J J' (hJ.symm.trans hJ') ((ModuleCat.extendScalars f).obj M)
      (quotientScalarExtension_support_of_map f I J hJ M hM)
      (quotientScalarExtension_support_of_map f I J' hJ' M hM) ≪≫
    (ModuleCat.restrictScalars (Ideal.quotEquivOfEq (hJ.symm.trans hJ')).toRingHom).mapIso
      (quotientScalarExtensionIsoOfMap f I J' hJ' q' hq' M hM).symm

/-- The canonical source transport changes only the literal quotient representative. -/
@[simp] theorem quotientScalarExtensionChangeIdealIso_hom_tmul (f : R →+* S)
    (I : Ideal R) (J J' : Ideal S) (hJ : I.map f = J) (hJ' : I.map f = J')
    (q : R ⧸ I →+* S ⧸ J) (q' : R ⧸ I →+* S ⧸ J')
    (hq : q.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp f)
    (hq' : q'.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J').comp f)
    (M : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M) (s : S) (m : M) :
    letI := quotientModuleAction I M hM
    (quotientScalarExtensionChangeIdealIso f I J J' hJ hJ' q q' hq hq' M hM).hom
      (Ideal.Quotient.mk J s ⊗ₜ[R ⧸ I,q] (m : quotientModule I M hM)) =
      Ideal.Quotient.mk J' s ⊗ₜ[R ⧸ I,q'] (m : quotientModule I M hM) := by
  exact (congrArg (quotientScalarExtensionIsoOfMap f I J' hJ' q' hq' M hM).inv
    (quotientScalarExtensionIsoOfMap_hom_tmul f I J hJ q hq M hM s m)).trans
      (quotientScalarExtensionIsoOfMap_inv_tmul f I J' hJ' q' hq' M hM s m)

/-- The equal-ideal ring isomorphism carries the first actual quotient map to the second. -/
theorem quotientScalarExtensionChangeIdeal_comp (f : R →+* S)
    (I : Ideal R) (J J' : Ideal S) (hJ : I.map f = J) (hJ' : I.map f = J')
    (q : R ⧸ I →+* S ⧸ J) (q' : R ⧸ I →+* S ⧸ J')
    (hq : q.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp f)
    (hq' : q'.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J').comp f) :
    (Ideal.quotEquivOfEq (hJ.symm.trans hJ')).toRingHom.comp q = q' := by
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (congrArg (Ideal.quotEquivOfEq (hJ.symm.trans hJ'))
    (RingHom.congr_fun hq r)).trans (RingHom.congr_fun hq' r).symm

/-- Actual source transport from composite restriction to direct supported scalar extension. -/
def torSupportCompositeSourceIso (f : R →+* S) (g : S →+* T) (J K : Ideal R) (n : ℕ) :
    (ModuleCat.extendScalars
      ((supportQuotientMapSup g (J.map f) (K.map f)).comp
        (supportQuotientMapSup f J K))).obj (torSupportModule J K n) ≅
      (ModuleCat.restrictScalars
        (torSupportCompositeRingIso f g J K :
          T ⧸ ((J.map f).map g ⊔ (K.map f).map g) →+*
            T ⧸ (J.map (g.comp f) ⊔ K.map (g.comp f)))).obj
        ((ModuleCat.extendScalars (supportQuotientMapSup (g.comp f) J K)).obj
          (torSupportModule J K n)) :=
  quotientScalarExtensionChangeIdealIso (g.comp f) (J ⊔ K)
    ((J.map f).map g ⊔ (K.map f).map g) (J.map (g.comp f) ⊔ K.map (g.comp f))
    (torSupportCompositeIdeal f g J K) (Ideal.map_sup _ J K)
    ((supportQuotientMapSup g (J.map f) (K.map f)).comp (supportQuotientMapSup f J K))
    (supportQuotientMapSup (g.comp f) J K)
    (quotientScalarSquare_comp f g _ _ _ _ _ (supportQuotientMapSup_square f J K)
      (supportQuotientMapSup_square g (J.map f) (K.map f)))
    (supportQuotientMapSup_square (g.comp f) J K) _ (quotient_support_le_annihilator J K n)

/-- Composite source transport is the literal map on tensor representatives. -/
@[simp] theorem torSupportCompositeSourceIso_hom_tmul (f : R →+* S) (g : S →+* T)
    (J K : Ideal R) (n : ℕ) (t : T) (m : torSupportModule J K n) :
    (torSupportCompositeSourceIso f g J K n).hom
      (Ideal.Quotient.mk ((J.map f).map g ⊔ (K.map f).map g) t ⊗ₜ[R ⧸ (J ⊔ K),
        (supportQuotientMapSup g (J.map f) (K.map f)).comp (supportQuotientMapSup f J K)] m) =
      Ideal.Quotient.mk (J.map (g.comp f) ⊔ K.map (g.comp f)) t ⊗ₜ[R ⧸ (J ⊔ K),
        supportQuotientMapSup (g.comp f) J K] m :=
  quotientScalarExtensionChangeIdealIso_hom_tmul _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The transported direct comparison is exactly the existing literal supported Tor comparison. -/
theorem torSupportDirectCompositeIso_transport (f : R →+* S) (g : S →+* T)
    (hf : f.Flat) (hg : g.Flat) (J K : Ideal R) (n : ℕ) :
    (torSupportDirectCompositeIso f g hf hg J K n).hom ≫
        (torSupportCompositeTargetRestrictIso f g J K n).hom =
      (torSupportCompositeSourceIso f g J K n).hom ≫
        (ModuleCat.restrictScalars (torSupportCompositeRingIso f g J K).toRingHom).map
          (torSupportBaseChangeIso (g.comp f) (hf.comp hg) J K n).hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  have h₁ := torSupportDirectCompositeIso_hom_tmul f g hf hg J K n 1 m
  have h₂ := torSupportCompositeSourceIso_hom_tmul f g J K n 1 m
  have h₃ := torSupportBaseChangeIso_hom_tmul (g.comp f) (hf.comp hg) J K n 1 m
  simp only [map_one] at h₁ h₂ h₃
  exact h₁.trans ((congrArg
    (torSupportBaseChangeIso (g.comp f) (hf.comp hg) J K n).hom h₂).trans h₃).symm

/-- Two actual supported transitions equal the existing direct transition under source transport. -/
theorem torSupportBaseChangeIso_hom_comp_transport (f : R →+* S) (g : S →+* T)
    (hf : f.Flat) (hg : g.Flat) (J K : Ideal R) (n : ℕ) :
    (ModuleCat.extendScalarsComp (supportQuotientMapSup f J K)
        (supportQuotientMapSup g (J.map f) (K.map f))).hom.app (torSupportModule J K n) ≫
      (ModuleCat.extendScalars (supportQuotientMapSup g (J.map f) (K.map f))).map
        (torSupportBaseChangeIso f hf J K n).hom ≫
      (torSupportBaseChangeIso g hg (J.map f) (K.map f) n).hom ≫
      (torSupportCompositeTargetIso f g J K n).hom ≫
      (torSupportCompositeTargetRestrictIso f g J K n).hom =
    (torSupportCompositeSourceIso f g J K n).hom ≫
      (ModuleCat.restrictScalars (torSupportCompositeRingIso f g J K).toRingHom).map
        (torSupportBaseChangeIso (g.comp f) (hf.comp hg) J K n).hom := by
  have h := congrArg (· ≫ (torSupportCompositeTargetRestrictIso f g J K n).hom)
    (torSupportBaseChangeIso_hom_comp f g hf hg J K n)
  simp only [Category.assoc] at h
  exact h.trans (torSupportDirectCompositeIso_transport f g hf hg J K n)

/-- Actual source transport from identity restriction to literal identity scalar extension. -/
def torSupportIdentitySourceIso (J K : Ideal R) (n : ℕ) :
    (ModuleCat.extendScalars (supportQuotientMapSup (RingHom.id R) J K)).obj
        (torSupportModule J K n) ≅
      (ModuleCat.restrictScalars
        (torSupportIdentityRingIso J K :
          R ⧸ (J.map (RingHom.id R) ⊔ K.map (RingHom.id R)) →+* R ⧸ (J ⊔ K))).obj
        ((ModuleCat.extendScalars (RingHom.id (R ⧸ (J ⊔ K)))).obj (torSupportModule J K n)) :=
  quotientScalarExtensionChangeIdealIso (RingHom.id R) (J ⊔ K)
    (J.map (RingHom.id R) ⊔ K.map (RingHom.id R)) (J ⊔ K)
    (Ideal.map_sup _ J K) (Ideal.map_id (J ⊔ K))
    (supportQuotientMapSup (RingHom.id R) J K) (RingHom.id (R ⧸ (J ⊔ K)))
    (supportQuotientMapSup_square (RingHom.id R) J K) rfl
    _ (quotient_support_le_annihilator J K n)

/-- The identity source transport preserves generating unit tensors. -/
@[simp] theorem torSupportIdentitySourceIso_hom_one_tmul (J K : Ideal R) (n : ℕ)
    (m : torSupportModule J K n) :
    (torSupportIdentitySourceIso J K n).hom
      ((1 : R ⧸ (J.map (RingHom.id R) ⊔ K.map (RingHom.id R))) ⊗ₜ[R ⧸ (J ⊔ K),
        supportQuotientMapSup (RingHom.id R) J K] m) =
      (1 : R ⧸ (J ⊔ K)) ⊗ₜ[R ⧸ (J ⊔ K),RingHom.id (R ⧸ (J ⊔ K))] m := by
  have h := quotientScalarExtensionChangeIdealIso_hom_tmul (RingHom.id R) (J ⊔ K)
    (J.map (RingHom.id R) ⊔ K.map (RingHom.id R)) (J ⊔ K)
    (Ideal.map_sup _ J K) (Ideal.map_id (J ⊔ K))
    (supportQuotientMapSup (RingHom.id R) J K) (RingHom.id (R ⧸ (J ⊔ K)))
    (supportQuotientMapSup_square (RingHom.id R) J K) rfl
    _ (quotient_support_le_annihilator J K n) 1 m
  simp only [map_one] at h
  exact h

/-- The transported support unitor is exactly the genuine quotient scalar-extension unitor. -/
theorem torSupportUnitIso_transport (J K : Ideal R) (n : ℕ) :
    (torSupportUnitIso J K n).hom ≫ (torSupportIdentityTargetRestrictIso J K n).hom =
      (torSupportIdentitySourceIso J K n).hom ≫
        (ModuleCat.restrictScalars (torSupportIdentityRingIso J K).toRingHom).map
          ((ModuleCat.extendScalarsId (R ⧸ (J ⊔ K))).hom.app (torSupportModule J K n)) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  exact (torSupportUnitIso_hom_one_tmul J K n m).trans
    ((congrArg ((ModuleCat.extendScalarsId (R ⧸ (J ⊔ K))).hom.app (torSupportModule J K n))
      (torSupportIdentitySourceIso_hom_one_tmul J K n m)).trans
        (ModuleCat.extendScalarsId_hom_app_one_tmul (torSupportModule J K n) m)).symm

/-- The existing supported identity transition equals the scalar unitor under genuine transport. -/
theorem torSupportBaseChangeIso_hom_id_transport (J K : Ideal R) (n : ℕ) :
    (torSupportBaseChangeIso (RingHom.id R) (RingHom.Flat.id R) J K n).hom ≫
      (torSupportIdentityTargetIso J K n).hom ≫
      (torSupportIdentityTargetRestrictIso J K n).hom =
    (torSupportIdentitySourceIso J K n).hom ≫
      (ModuleCat.restrictScalars (torSupportIdentityRingIso J K).toRingHom).map
        ((ModuleCat.extendScalarsId (R ⧸ (J ⊔ K))).hom.app (torSupportModule J K n)) := by
  have h := congrArg (· ≫ (torSupportIdentityTargetRestrictIso J K n).hom)
    (torSupportBaseChangeIso_hom_id J K n)
  simp only [Category.assoc] at h
  exact h.trans (torSupportUnitIso_transport J K n)

end ModuleCat.TorComparison
