/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.QuotientCoefficientExtension

/-!
# Coherence of literal quotient-coefficient scalar extension

The actual quotient-coefficient comparison respects the canonical scalar-extension
unitor and associator. The image-ideal equalities are realized by the canonical
quotient module isomorphisms, retaining quotient representatives.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace ModuleCat.TorComparison

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The actual quotient module transport for the image ideal of the identity map. -/
def mappedQuotientIdIso (I : Ideal R) :
    ModuleCat.of R (R ⧸ I.map (RingHom.id R)) ≅ ModuleCat.of R (R ⧸ I) :=
  (Ideal.quotientEquivAlgOfEq R (Ideal.map_id I)).toLinearEquiv.toModuleIso

/-- The actual quotient module transport for two successive image ideals. -/
def mappedQuotientCompIso (f : R →+* S) (g : S →+* T) (I : Ideal R) :
    ModuleCat.of T (T ⧸ (I.map f).map g) ≅ ModuleCat.of T (T ⧸ I.map (g.comp f)) :=
  (Ideal.quotientEquivAlgOfEq T (Ideal.map_map f g)).toLinearEquiv.toModuleIso

/-- The identity-image quotient transport keeps representatives. -/
@[simp] theorem mappedQuotientIdIso_hom_mk (I : Ideal R) (r : R) :
    (mappedQuotientIdIso I).hom (Ideal.Quotient.mk (I.map (RingHom.id R)) r) =
      Ideal.Quotient.mk I r := rfl

/-- The composite-image quotient transport keeps representatives. -/
@[simp] theorem mappedQuotientCompIso_hom_mk (f : R →+* S) (g : S →+* T)
    (I : Ideal R) (t : T) :
    (mappedQuotientCompIso f g I).hom (Ideal.Quotient.mk ((I.map f).map g) t) =
      Ideal.Quotient.mk (I.map (g.comp f)) t := rfl

/-- Literal quotient-coefficient scalar extension respects the canonical unitor. -/
@[reassoc] theorem extendedIdealQuotientIso_hom_id (I : Ideal R) :
    (extendedIdealQuotientIso (RingHom.id R) I).hom ≫ (mappedQuotientIdIso I).hom =
      (ModuleCat.extendScalarsId R).hom.app (ModuleCat.of R (R ⧸ I)) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  have h := extendedIdealQuotientIso_hom_tmul (RingHom.id R) I 1 r
  simp only [one_mul, RingHom.id_apply] at h
  exact (congrArg (mappedQuotientIdIso I).hom h).trans
    (ModuleCat.extendScalarsId_hom_app_one_tmul (ModuleCat.of R (R ⧸ I))
      (Ideal.Quotient.mk I r)).symm

/-- Literal quotient-coefficient scalar extension respects the canonical associator. -/
@[reassoc] theorem extendedIdealQuotientIso_hom_comp (f : R →+* S) (g : S →+* T)
    (I : Ideal R) :
    (ModuleCat.extendScalarsComp f g).hom.app (ModuleCat.of R (R ⧸ I)) ≫
        (ModuleCat.extendScalars g).map (extendedIdealQuotientIso f I).hom ≫
        (extendedIdealQuotientIso g (I.map f)).hom ≫ (mappedQuotientCompIso f g I).hom =
      (extendedIdealQuotientIso (g.comp f) I).hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  have ha := ModuleCat.extendScalarsComp_hom_app_one_tmul f g
    (ModuleCat.of R (R ⧸ I)) (Ideal.Quotient.mk I r)
  have hf := extendedIdealQuotientIso_hom_tmul f I 1 r
  have hg := extendedIdealQuotientIso_hom_tmul g (I.map f) 1 (f r)
  have hc := extendedIdealQuotientIso_hom_tmul (g.comp f) I 1 r
  simp only [one_mul] at hf hg hc
  exact (congrArg (fun x => (mappedQuotientCompIso f g I).hom
      ((extendedIdealQuotientIso g (I.map f)).hom
        (((ModuleCat.extendScalars g).map (extendedIdealQuotientIso f I).hom) x))) ha).trans
    ((congrArg (fun x => (mappedQuotientCompIso f g I).hom
      ((extendedIdealQuotientIso g (I.map f)).hom ((1 : T) ⊗ₜ[S,g] x))) hf).trans
      ((congrArg (mappedQuotientCompIso f g I).hom hg).trans hc.symm))

end ModuleCat.TorComparison
