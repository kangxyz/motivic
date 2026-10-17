/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.QuotientScalarExtensionCoordinates

/-!
# Coherence of quotient and ambient scalar extension

The canonical quotient pushout comparison respects actual scalar-extension
associators and unitors. An equality-transported form records a literal target
ideal and its actual quotient ring map, so ideal-map equalities do not obscure
the underlying comparison. All comparison maps are constructed from the
existing quotient pushout isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace Motivic.TorComparison

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- A quotient square determines its induced ring map uniquely. -/
theorem supportQuotientMap_unique (f : R →+* S) (I : Ideal R)
    (q : R ⧸ I →+* S ⧸ I.map f)
    (hq : q.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk (I.map f)).comp f) :
    q = supportQuotientMap f I := by
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact RingHom.congr_fun hq r

/-- Image-ideal transport gives the actual annihilation needed by a literal target quotient. -/
theorem quotientScalarExtension_support_of_map (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (hJ : I.map f = J) (M : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M) :
    J ≤ Module.annihilator S ((ModuleCat.extendScalars f).obj M) :=
  hJ ▸ map_support_le_annihilator_extendScalars f I M hM

/-- The canonical comparison with a literal target ideal and its actual induced quotient map. -/
def quotientScalarExtensionIsoOfMap (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (hJ : I.map f = J) (q : R ⧸ I →+* S ⧸ J)
    (hq : q.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp f)
    (M : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M) :
    (ModuleCat.extendScalars q).obj (quotientModule I M hM) ≅
      quotientModule J ((ModuleCat.extendScalars f).obj M)
        (quotientScalarExtension_support_of_map f I J hJ M hM) := by
  subst J
  have hq' := supportQuotientMap_unique f I q hq
  subst q
  exact quotientScalarExtensionIso f I M hM

/-- Literal-ideal transport preserves the same canonical pure-tensor coordinate. -/
@[simp] theorem quotientScalarExtensionIsoOfMap_hom_tmul (f : R →+* S)
    (I : Ideal R) (J : Ideal S) (hJ : I.map f = J) (q : R ⧸ I →+* S ⧸ J)
    (hq : q.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp f)
    (M : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M) (s : S) (m : M) :
    letI := quotientModuleAction I M hM
    (quotientScalarExtensionIsoOfMap f I J hJ q hq M hM).hom
      (Ideal.Quotient.mk J s ⊗ₜ[R ⧸ I,q] (m : quotientModule I M hM)) = s ⊗ₜ[R,f] m := by
  subst J
  have hq' := supportQuotientMap_unique f I q hq
  subst q
  exact quotientScalarExtensionIso_hom_tmul f I M hM s m

/-- Specialization to the original induced quotient map changes no comparison. -/
theorem quotientScalarExtensionIsoOfMap_self (f : R →+* S) (I : Ideal R)
    (M : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M) :
    quotientScalarExtensionIsoOfMap f I (I.map f) rfl (supportQuotientMap f I)
      (Ideal.quotientMap_comp_mk Ideal.le_comap_map) M hM =
        quotientScalarExtensionIso f I M hM := rfl

/-- Composing actual quotient squares gives the square for the composite ambient map. -/
theorem quotientScalarSquare_comp (f : R →+* S) (g : S →+* T)
    (I : Ideal R) (J : Ideal S) (K : Ideal T)
    (q : R ⧸ I →+* S ⧸ J) (p : S ⧸ J →+* T ⧸ K)
    (hq : q.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp f)
    (hp : p.comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk K).comp g) :
    (p.comp q).comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk K).comp (g.comp f) := by
  apply RingHom.ext
  intro r
  change p (q (Ideal.Quotient.mk I r)) = Ideal.Quotient.mk K (g (f r))
  exact (congrArg p (RingHom.congr_fun hq r)).trans (RingHom.congr_fun hp (f r))

/-- The image ideal of the composite agrees with the literal iterated image ideal. -/
theorem quotientImage_comp (f : R →+* S) (g : S →+* T)
    (I : Ideal R) (J : Ideal S) (K : Ideal T) (hJ : I.map f = J) (hK : J.map g = K) :
    I.map (g.comp f) = K := by rw [← Ideal.map_map, hJ, hK]

/-- The actual quotient pushout comparison respects scalar-extension associators. -/
theorem quotientScalarExtensionIsoOfMap_hom_comp (f : R →+* S) (g : S →+* T)
    (I : Ideal R) (J : Ideal S) (K : Ideal T) (hJ : I.map f = J) (hK : J.map g = K)
    (q : R ⧸ I →+* S ⧸ J) (p : S ⧸ J →+* T ⧸ K)
    (hq : q.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp f)
    (hp : p.comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk K).comp g)
    (M : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M) :
    let hN := quotientScalarExtension_support_of_map f I J hJ M hM
    let hP := quotientScalarExtension_support_of_map g J K hK
      ((ModuleCat.extendScalars f).obj M) hN
    let hD := quotientScalarExtension_support_of_map (g.comp f) I K
      (quotientImage_comp f g I J K hJ hK) M hM
    (ModuleCat.extendScalarsComp q p).hom.app (quotientModule I M hM) ≫
        (ModuleCat.extendScalars p).map
          (quotientScalarExtensionIsoOfMap f I J hJ q hq M hM).hom ≫
        (quotientScalarExtensionIsoOfMap g J K hK p hp
          ((ModuleCat.extendScalars f).obj M) hN).hom =
      (quotientScalarExtensionIsoOfMap (g.comp f) I K
        (quotientImage_comp f g I J K hJ hK) (p.comp q)
        (quotientScalarSquare_comp f g I J K q p hq hp) M hM).hom ≫
      quotientLinearMap K hD hP ((ModuleCat.extendScalarsComp f g).hom.app M) := by
  dsimp only
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  let hN := quotientScalarExtension_support_of_map f I J hJ M hM
  have h₁ := quotientScalarExtensionIsoOfMap_hom_tmul f I J hJ q hq M hM 1 m
  have h₂ := quotientScalarExtensionIsoOfMap_hom_tmul g J K hK p hp
    ((ModuleCat.extendScalars f).obj M) hN 1 ((1 : S) ⊗ₜ[R,f] m)
  have h₃ := quotientScalarExtensionIsoOfMap_hom_tmul (g.comp f) I K
    (quotientImage_comp f g I J K hJ hK) (p.comp q)
    (quotientScalarSquare_comp f g I J K q p hq hp) M hM 1 m
  simp only [map_one] at h₁ h₂ h₃
  have ha := ModuleCat.extendScalarsComp_hom_app_one_tmul q p
    (quotientModule I M hM) m
  have hb := ModuleCat.extendScalarsComp_hom_app_one_tmul f g M m
  exact (congrArg (fun x =>
    (quotientScalarExtensionIsoOfMap g J K hK p hp
      ((ModuleCat.extendScalars f).obj M) hN).hom
      (((ModuleCat.extendScalars p).map
        (quotientScalarExtensionIsoOfMap f I J hJ q hq M hM).hom) x)) ha).trans
    ((congrArg (fun x => (quotientScalarExtensionIsoOfMap g J K hK p hp
      ((ModuleCat.extendScalars f).obj M) hN).hom ((1 : T ⧸ K) ⊗ₜ[S ⧸ J,p] x)) h₁).trans
      (h₂.trans ((congrArg ((ModuleCat.extendScalarsComp f g).hom.app M) h₃).trans hb).symm))

/-- The transported quotient comparison is natural in every actual module map. -/
@[reassoc] theorem quotientScalarExtensionIsoOfMap_hom_naturality (f : R →+* S)
    (I : Ideal R) (J : Ideal S) (hJ : I.map f = J) (q : R ⧸ I →+* S ⧸ J)
    (hq : q.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp f)
    (M N : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M)
    (hN : I ≤ Module.annihilator R N) (φ : M ⟶ N) :
    (ModuleCat.extendScalars q).map (quotientLinearMap I hM hN φ) ≫
        (quotientScalarExtensionIsoOfMap f I J hJ q hq N hN).hom =
      (quotientScalarExtensionIsoOfMap f I J hJ q hq M hM).hom ≫
        quotientLinearMap J
          (quotientScalarExtension_support_of_map f I J hJ M hM)
          (quotientScalarExtension_support_of_map f I J hJ N hN)
          ((ModuleCat.extendScalars f).map φ) := by
  subst J
  have hq' := supportQuotientMap_unique f I q hq
  subst q
  exact quotientScalarExtensionIso_hom_naturality f I M N hM hN φ

/-- The actual quotient pushout comparison respects the scalar-extension unitor. -/
theorem quotientScalarExtensionIsoOfMap_hom_id (I : Ideal R)
    (M : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M) :
    (quotientScalarExtensionIsoOfMap (RingHom.id R) I I (Ideal.map_id I)
      (RingHom.id (R ⧸ I)) rfl M hM).hom ≫
      quotientLinearMap I
        (quotientScalarExtension_support_of_map (RingHom.id R) I I (Ideal.map_id I) M hM)
        hM ((ModuleCat.extendScalarsId R).hom.app M) =
      (ModuleCat.extendScalarsId (R ⧸ I)).hom.app (quotientModule I M hM) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  have h := quotientScalarExtensionIsoOfMap_hom_tmul (RingHom.id R) I I (Ideal.map_id I)
    (RingHom.id (R ⧸ I)) rfl M hM 1 m
  simp only [map_one] at h
  exact (congrArg ((ModuleCat.extendScalarsId R).hom.app M) h).trans
    ((ModuleCat.extendScalarsId_hom_app_one_tmul M m).trans
      (ModuleCat.extendScalarsId_hom_app_one_tmul (quotientModule I M hM) m).symm)

end Motivic.TorComparison
