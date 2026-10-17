/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.ClosedIntersectionTorRestriction
public import Motivic.Algebra.Homology.TorComparison.TorSupportRestrictionCoherence

/-!
# Coordinates and coherence of actual Tor chart refinements

The ring-equivalence square comparison retains its original unit-tensor
coordinates. These coordinates support the identity and composition comparison
for actual closed-intersection chart restrictions.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

universe u

namespace Motivic.Intersection

variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]

/-- The canonical equivalence comparison preserves generating unit tensors. -/
theorem extendScalarsRingEquivIso_hom_one_tmul (e : R ≃+* S) (M : ModuleCat.{u} R)
    (m : M) :
    (extendScalarsRingEquivIso e M).hom ((1 : S) ⊗ₜ[R,e.toRingHom] m) = m := by
  change (ModuleCat.extendRestrictScalarsAdj e.toRingHom).counit.app
    ((ModuleCat.restrictScalars e.symm.toRingHom).obj M)
    ((1 : S) ⊗ₜ[R,e.toRingHom]
      (m : (ModuleCat.restrictScalars e.toRingHom).obj
        ((ModuleCat.restrictScalars e.symm.toRingHom).obj M))) = m
  exact ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul
    (f := e.toRingHom) ((ModuleCat.restrictScalars e.symm.toRingHom).obj M) m

/-- The inverse equivalence comparison is the canonical unit tensor. -/
theorem extendScalarsRingEquivIso_inv_apply (e : R ≃+* S) (M : ModuleCat.{u} R)
    (m : M) :
    (extendScalarsRingEquivIso e M).inv m = (1 : S) ⊗ₜ[R,e.toRingHom] m := by
  have h := congrArg (extendScalarsRingEquivIso e M).inv
    (extendScalarsRingEquivIso_hom_one_tmul e M m)
  exact h.symm.trans (ModuleCat.inv_hom_apply (extendScalarsRingEquivIso e M) _)

/-- Equality of the literal scalar maps preserves the same unit tensor. -/
theorem extendScalarsEqToIso_hom_one_tmul (f g : R →+* S) (h : f = g)
    (M : ModuleCat.{u} R) (m : M) :
    (eqToIso (congrArg (fun q : R →+* S => (ModuleCat.extendScalars q).obj M) h)).hom
      ((1 : S) ⊗ₜ[R,f] m) = (1 : S) ⊗ₜ[R,g] m := by
  subst g
  rfl

/-- The inverse genuine scalar associator contracts two generating unit tensors. -/
theorem extendScalarsComp_inv_one_tmul (f : R →+* S) (g : S →+* A)
    (M : ModuleCat.{u} R) (m : M) :
    (ModuleCat.extendScalarsComp f g).inv.app M
      ((1 : A) ⊗ₜ[S,g] ((1 : S) ⊗ₜ[R,f] m)) = (1 : A) ⊗ₜ[R,g.comp f] m := by
  have h := congrArg ((ModuleCat.extendScalarsComp f g).inv.app M)
    (ModuleCat.extendScalarsComp_hom_app_one_tmul f g M m)
  exact h.symm.trans (ModuleCat.inv_hom_apply ((ModuleCat.extendScalarsComp f g).app M) _)

/-- The actual ring-equivalence square comparison preserves the original generator,
with no transported replacement for either scalar action. -/
theorem extendScalarsRingEquivSquareIso_hom_one_tmul
    (f : R →+* S) (g : A →+* B) (eR : R ≃+* A) (eS : S ≃+* B)
    (h : g.comp eR.toRingHom = eS.toRingHom.comp f) (M : ModuleCat.{u} R) (m : M) :
    (extendScalarsRingEquivSquareIso f g eR eS h M).hom
      ((1 : B) ⊗ₜ[A,g] (m : (ModuleCat.restrictScalars eR.symm.toRingHom).obj M)) =
        (1 : S) ⊗ₜ[R,f] m := by
  change (extendScalarsRingEquivIso eS ((ModuleCat.extendScalars f).obj M)).hom
    ((ModuleCat.extendScalarsComp f eS.toRingHom).hom.app M
      ((eqToIso (congrArg (fun q : R →+* B => (ModuleCat.extendScalars q).obj M) h)).hom
        ((ModuleCat.extendScalarsComp eR.toRingHom g).inv.app M
          ((1 : B) ⊗ₜ[A,g] ((extendScalarsRingEquivIso eR M).inv m))))) = _
  have h₁ := congrArg (fun x => (ModuleCat.extendScalarsComp eR.toRingHom g).inv.app M
    ((1 : B) ⊗ₜ[A,g] x)) (extendScalarsRingEquivIso_inv_apply eR M m)
  have h₂ := h₁.trans (extendScalarsComp_inv_one_tmul eR.toRingHom g M m)
  have h₃ := (congrArg
    (eqToIso (congrArg (fun q : R →+* B => (ModuleCat.extendScalars q).obj M) h)).hom
    h₂).trans (extendScalarsEqToIso_hom_one_tmul _ _ h M m)
  have h₄ := (congrArg ((ModuleCat.extendScalarsComp f eS.toRingHom).hom.app M) h₃).trans
    (ModuleCat.extendScalarsComp_hom_app_one_tmul f eS.toRingHom M m)
  exact (congrArg (extendScalarsRingEquivIso eS ((ModuleCat.extendScalars f).obj M)).hom h₄).trans
    (extendScalarsRingEquivIso_hom_one_tmul eS ((ModuleCat.extendScalars f).obj M) _)


/-- Equality transport of the two literal quotient ideals in actual categorical Tor. -/
def quotientTorIsoOfIdeals (J K J' K' : Ideal R) (hJ : J = J') (hK : K = K') (n : ℕ) :
    (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).obj
      (ModuleCat.of R (R ⧸ J))) ≅
    (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K'))).obj
      (ModuleCat.of R (R ⧸ J'))) := by
  subst J' K'
  exact Iso.refl _

/-- Equality transport is exactly Tor of the two canonical quotient equality maps. -/
theorem quotientTorIsoOfIdeals_eq (J K J' K' : Ideal R) (hJ : J = J') (hK : K = K')
    (n : ℕ) :
    quotientTorIsoOfIdeals J K J' K' hJ hK n =
      ((Tor (ModuleCat R) n).mapIso
        (Ideal.quotientEquivAlgOfEq R hK).toLinearEquiv.toModuleIso).app _ ≪≫
      ((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K'))).mapIso
        (Ideal.quotientEquivAlgOfEq R hJ).toLinearEquiv.toModuleIso := by
  subst J' K'
  have hi (I : Ideal R) :
      (Ideal.quotientEquivAlgOfEq R (rfl : I = I)).toLinearEquiv.toModuleIso.hom =
        𝟙 (ModuleCat.of R (R ⧸ I)) := by
    ext
    rfl
  apply Iso.ext
  simp only [quotientTorIsoOfIdeals, Iso.refl_hom, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, hi]
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp]

/-- The literal-target support comparison retains the canonical ambient Tor map
on every generating unit tensor. -/
theorem torSupportBaseChangeIsoOfMaps_hom_one_tmul
    (f : R →+* S) (hf : f.Flat) (J K : Ideal R) (J' K' : Ideal S)
    (hJ : J.map f = J') (hK : K.map f = K')
    (q : R ⧸ (J ⊔ K) →+* S ⧸ (J' ⊔ K'))
    (hq : q.comp (Ideal.Quotient.mk (J ⊔ K)) = (Ideal.Quotient.mk (J' ⊔ K')).comp f)
    (n : ℕ) (m : TorComparison.torSupportModule J K n) :
    (torSupportBaseChangeIsoOfMaps f hf J K J' K' hJ hK q hq n).hom
      ((1 : S ⧸ (J' ⊔ K')) ⊗ₜ[R ⧸ (J ⊔ K),q] m) =
    (quotientTorIsoOfIdeals (J.map f) (K.map f) J' K' hJ hK n).hom
      ((TorComparison.flatBaseChangeLiteralTorIso f hf J K n).hom ((1 : S) ⊗ₜ[R,f] m)) := by
  subst J' K'
  have he : q = TorComparison.supportQuotientMapSup f J K := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    exact RingHom.congr_fun hq r
  subst q
  have h := TorComparison.torSupportBaseChangeIso_hom_tmul f hf J K n 1 m
  change (TorComparison.torSupportBaseChangeIso f hf J K n).hom
    ((1 : S ⧸ (J.map f ⊔ K.map f)) ⊗ₜ[R ⧸ (J ⊔ K),
      TorComparison.supportQuotientMapSup f J K] m) =
        (TorComparison.flatBaseChangeLiteralTorIso f hf J K n).hom ((1 : S) ⊗ₜ[R,f] m)
  simp only [map_one] at h
  exact h

/-- Reversing equality of the literal ideals reverses the actual Tor transport. -/
theorem quotientTorIsoOfIdeals_symm (J K J' K' : Ideal R) (hJ : J = J') (hK : K = K')
    (n : ℕ) :
    quotientTorIsoOfIdeals J' K' J K hJ.symm hK.symm n =
      (quotientTorIsoOfIdeals J K J' K' hJ hK n).symm := by
  subst J' K'
  rfl

/-- Identity scalar extension of the literal-target support module keeps generators. -/
theorem torSupportBaseChangeIsoOfMaps_id_one_tmul (J K : Ideal R) (n : ℕ)
    (m : TorComparison.torSupportModule J K n) :
    (torSupportBaseChangeIsoOfMaps (RingHom.id R) (RingHom.Flat.id R) J K J K
      (Ideal.map_id J) (Ideal.map_id K) (RingHom.id (R ⧸ (J ⊔ K))) rfl n).hom
        ((1 : R ⧸ (J ⊔ K)) ⊗ₜ[R ⧸ (J ⊔ K),RingHom.id (R ⧸ (J ⊔ K))] m) = m := by
  have h := torSupportBaseChangeIsoOfMaps_hom_one_tmul
    (RingHom.id R) (RingHom.Flat.id R) J K J K (Ideal.map_id J) (Ideal.map_id K)
    (RingHom.id (R ⧸ (J ⊔ K))) rfl n m
  have he : quotientTorIsoOfIdeals (J.map (RingHom.id R)) (K.map (RingHom.id R)) J K
      (Ideal.map_id J) (Ideal.map_id K) n = TorComparison.mappedQuotientsTorIdIso J K n :=
    quotientTorIsoOfIdeals_eq _ _ _ _ _ _ _
  rw [he] at h
  have hc := congrArg (fun φ => φ ((1 : R) ⊗ₜ[R,RingHom.id R] m))
    (TorComparison.flatBaseChangeLiteralTorIso_hom_id J K n)
  exact h.trans (hc.trans (ModuleCat.extendScalarsId_hom_app_one_tmul _ m))

/-- Canonical literal-target restriction for a composite scalar map agrees on generators
with the two successive canonical supported Tor restrictions. -/
theorem torSupportBaseChangeIsoOfMaps_comp_one_tmul
    (f : R →+* S) (g : S →+* A) (hf : f.Flat) (hg : g.Flat)
    (J K : Ideal R) (n : ℕ) (m : TorComparison.torSupportModule J K n) :
    (torSupportBaseChangeIsoOfMaps (g.comp f) (hf.comp hg) J K
      ((J.map f).map g) ((K.map f).map g) (Ideal.map_map f g).symm
      (Ideal.map_map f g).symm
      ((TorComparison.supportQuotientMapSup g (J.map f) (K.map f)).comp
        (TorComparison.supportQuotientMapSup f J K))
      (TorComparison.quotientScalarSquare_comp f g _ _ _ _ _
        (TorComparison.supportQuotientMapSup_square f J K)
        (TorComparison.supportQuotientMapSup_square g (J.map f) (K.map f))) n).hom
      ((1 : A ⧸ ((J.map f).map g ⊔ (K.map f).map g)) ⊗ₜ[R ⧸ (J ⊔ K),
        (TorComparison.supportQuotientMapSup g (J.map f) (K.map f)).comp
          (TorComparison.supportQuotientMapSup f J K)] m) =
    (TorComparison.torSupportBaseChangeIso g hg (J.map f) (K.map f) n).hom
      ((1 : A ⧸ ((J.map f).map g ⊔ (K.map f).map g)) ⊗ₜ[S ⧸ (J.map f ⊔ K.map f),
        TorComparison.supportQuotientMapSup g (J.map f) (K.map f)]
      ((TorComparison.torSupportBaseChangeIso f hf J K n).hom
        ((1 : S ⧸ (J.map f ⊔ K.map f)) ⊗ₜ[R ⧸ (J ⊔ K),
          TorComparison.supportQuotientMapSup f J K] m))) := by
  have h := torSupportBaseChangeIsoOfMaps_hom_one_tmul (g.comp f) (hf.comp hg) J K
    ((J.map f).map g) ((K.map f).map g) (Ideal.map_map f g).symm
    (Ideal.map_map f g).symm _
    (TorComparison.quotientScalarSquare_comp f g _ _ _ _ _
      (TorComparison.supportQuotientMapSup_square f J K)
      (TorComparison.supportQuotientMapSup_square g (J.map f) (K.map f))) n m
  have he : quotientTorIsoOfIdeals (J.map (g.comp f)) (K.map (g.comp f))
      ((J.map f).map g) ((K.map f).map g) (Ideal.map_map f g).symm
      (Ideal.map_map f g).symm n = (TorComparison.mappedQuotientsTorCompIso f g J K n).symm := by
    rw [quotientTorIsoOfIdeals_symm, quotientTorIsoOfIdeals_eq]
    rfl
  rw [he] at h
  have hc := congrArg (fun φ => φ
      ((1 : A ⧸ ((J.map f).map g ⊔ (K.map f).map g)) ⊗ₜ[R ⧸ (J ⊔ K),
        (TorComparison.supportQuotientMapSup g (J.map f) (K.map f)).comp
          (TorComparison.supportQuotientMapSup f J K)] m))
    (TorComparison.torSupportBaseChangeIso_hom_comp f g hf hg J K n)
  have ha := ModuleCat.extendScalarsComp_hom_app_one_tmul
    (TorComparison.supportQuotientMapSup f J K)
    (TorComparison.supportQuotientMapSup g (J.map f) (K.map f))
    (TorComparison.torSupportModule J K n) m
  have hd := TorComparison.torSupportDirectCompositeIso_hom_tmul f g hf hg J K n 1 m
  simp only [map_one] at hd
  have hc' := (congrArg (fun x =>
    (TorComparison.torSupportCompositeTargetIso f g J K n).hom
      ((TorComparison.torSupportBaseChangeIso g hg (J.map f) (K.map f) n).hom
        (((ModuleCat.extendScalars (TorComparison.supportQuotientMapSup g (J.map f)
          (K.map f))).map (TorComparison.torSupportBaseChangeIso f hf J K n).hom) x)))
    ha).symm.trans (hc.trans hd)
  exact h.trans ((congrArg (TorComparison.mappedQuotientsTorCompIso f g J K n).inv
    hc'.symm).trans (ModuleCat.inv_hom_apply _ _))

/-- The literal-target support comparison obeys composition for any proved image ideals
and actual quotient scalar squares. No transition equality is assumed. -/
theorem torSupportBaseChangeIsoOfMaps_comp_generators
    (f : R →+* S) (g : S →+* A) (hf : f.Flat) (hg : g.Flat)
    (J K : Ideal R) (J' K' : Ideal S) (J'' K'' : Ideal A)
    (hJ : J.map f = J') (hK : K.map f = K')
    (hJ' : J'.map g = J'') (hK' : K'.map g = K'')
    (q : R ⧸ (J ⊔ K) →+* S ⧸ (J' ⊔ K'))
    (q' : S ⧸ (J' ⊔ K') →+* A ⧸ (J'' ⊔ K''))
    (hq : q.comp (Ideal.Quotient.mk (J ⊔ K)) = (Ideal.Quotient.mk (J' ⊔ K')).comp f)
    (hq' : q'.comp (Ideal.Quotient.mk (J' ⊔ K')) = (Ideal.Quotient.mk (J'' ⊔ K'')).comp g)
    (n : ℕ) (m : TorComparison.torSupportModule J K n) :
    (torSupportBaseChangeIsoOfMaps (g.comp f) (hf.comp hg) J K J'' K''
      ((Ideal.map_map f g).symm.trans ((congrArg (fun I : Ideal S => I.map g) hJ).trans hJ'))
      ((Ideal.map_map f g).symm.trans ((congrArg (fun I : Ideal S => I.map g) hK).trans hK'))
      (q'.comp q) (TorComparison.quotientScalarSquare_comp f g _ _ _ q q' hq hq') n).hom
      ((1 : A ⧸ (J'' ⊔ K'')) ⊗ₜ[R ⧸ (J ⊔ K),q'.comp q] m) =
    (torSupportBaseChangeIsoOfMaps g hg J' K' J'' K'' hJ' hK' q' hq' n).hom
      ((1 : A ⧸ (J'' ⊔ K'')) ⊗ₜ[S ⧸ (J' ⊔ K'),q']
        ((torSupportBaseChangeIsoOfMaps f hf J K J' K' hJ hK q hq n).hom
          ((1 : S ⧸ (J' ⊔ K')) ⊗ₜ[R ⧸ (J ⊔ K),q] m))) := by
  subst J' K' J'' K''
  have he : q = TorComparison.supportQuotientMapSup f J K := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    exact RingHom.congr_fun hq r
  subst q
  have he' : q' = TorComparison.supportQuotientMapSup g (J.map f) (K.map f) := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    exact RingHom.congr_fun hq' r
  subst q'
  exact torSupportBaseChangeIsoOfMaps_comp_one_tmul f g hf hg J K n m

variable {P T D : Scheme.{u}} (i : T ⟶ P) (j : D ⟶ P)

/-- The literal ambient affine restriction has its original identity ring map. -/
theorem affineRestriction_refl (U : P.affineOpens) :
    (P.presheaf.map (homOfLE (show U.1 ≤ U.1 from le_rfl)).op).hom = RingHom.id _ := by
  change (P.presheaf.map (𝟙 (Opposite.op U.1))).hom = _
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The literal ambient affine section maps have the genuine composition law. -/
theorem affineRestriction_comp {U V L : P.affineOpens} (h : U ≤ V) (k : V ≤ L) :
    (P.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom.comp
        (P.presheaf.map (homOfLE (show V.1 ≤ L.1 from k)).op).hom =
      (P.presheaf.map (homOfLE (show U.1 ≤ L.1 from h.trans k)).op).hom := by
  ext r
  exact (ConcreteCategory.congr_hom (P.presheaf.map_comp
    (homOfLE (show V.1 ≤ L.1 from k)).op (homOfLE (show U.1 ≤ V.1 from h)).op) r).symm

/-- Actual support quotient restriction is the identity on an unchanged affine chart. -/
theorem closedIntersectionSupportQuotientRestriction_refl (U : P.affineOpens) :
    closedIntersectionSupportQuotientRestriction i j (show U ≤ U from le_rfl) =
      RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  ext r
  change Ideal.Quotient.mk _
    ((P.presheaf.map (homOfLE (show U.1 ≤ U.1 from le_rfl)).op).hom r) = _
  rw [affineRestriction_refl]
  rfl

/-- Actual support quotient restriction preserves the original composition. -/
theorem closedIntersectionSupportQuotientRestriction_comp {U V L : P.affineOpens}
    (h : U ≤ V) (k : V ≤ L) :
    (closedIntersectionSupportQuotientRestriction i j h).comp
      (closedIntersectionSupportQuotientRestriction i j k) =
        closedIntersectionSupportQuotientRestriction i j (h.trans k) := by
  apply Ideal.Quotient.ringHom_ext
  ext r
  change Ideal.Quotient.mk _
    (((P.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom.comp
      (P.presheaf.map (homOfLE (show V.1 ≤ L.1 from k)).op).hom) r) = _
  rw [affineRestriction_comp h k]
  rfl


/-- Literal-target support restriction transports equality of the scalar map on generators. -/
theorem torSupportBaseChangeIsoOfMaps_congr_one_tmul
    (f f' : R →+* S) (hf : f.Flat) (hf' : f'.Flat) (ef : f = f')
    (J K : Ideal R) (J' K' : Ideal S)
    (hJ : J.map f = J') (hK : K.map f = K')
    (hJ' : J.map f' = J') (hK' : K.map f' = K')
    (q q' : R ⧸ (J ⊔ K) →+* S ⧸ (J' ⊔ K')) (eq : q = q')
    (hq : q.comp (Ideal.Quotient.mk (J ⊔ K)) = (Ideal.Quotient.mk (J' ⊔ K')).comp f)
    (hq' : q'.comp (Ideal.Quotient.mk (J ⊔ K)) = (Ideal.Quotient.mk (J' ⊔ K')).comp f')
    (n : ℕ) (m : TorComparison.torSupportModule J K n) :
    (torSupportBaseChangeIsoOfMaps f hf J K J' K' hJ hK q hq n).hom
      ((1 : S ⧸ (J' ⊔ K')) ⊗ₜ[R ⧸ (J ⊔ K),q] m) =
    (torSupportBaseChangeIsoOfMaps f' hf' J K J' K' hJ' hK' q' hq' n).hom
      ((1 : S ⧸ (J' ⊔ K')) ⊗ₜ[R ⧸ (J ⊔ K),q'] m) := by
  subst f' q'
  rfl

/-- On an unchanged chart, the original quotient-supported Tor refinement keeps generators. -/
theorem closedIntersectionQuotientTorRestrictionIso_refl_one_tmul
    (U : P.affineOpens) (n : ℕ)
    (m : TorComparison.torSupportModule (j.ker.ideal U) (i.ker.ideal U) n) :
    (closedIntersectionQuotientTorRestrictionIso i j (show U ≤ U from le_rfl) n).hom
      ((ModuleCat.extendRestrictScalarsAdj
        (closedIntersectionSupportQuotientRestriction i j (show U ≤ U from le_rfl))).unit.app
          (TorComparison.torSupportModule (j.ker.ideal U) (i.ker.ideal U) n) m) = m := by
  exact (torSupportBaseChangeIsoOfMaps_congr_one_tmul _ _ _ _ (affineRestriction_refl U)
    _ _ _ _ (j.ker.map_ideal (show U ≤ U from le_rfl))
    (i.ker.map_ideal (show U ≤ U from le_rfl)) (Ideal.map_id _) (Ideal.map_id _)
    _ _ (closedIntersectionSupportQuotientRestriction_refl i j U)
    (closedIntersectionSupportQuotientRestriction_square i j (show U ≤ U from le_rfl))
      rfl n m).trans
      (torSupportBaseChangeIsoOfMaps_id_one_tmul _ _ n m)
/-- The actual quotient-supported chart restrictions have the composition equation
on the original generating sections. -/
theorem closedIntersectionQuotientTorRestrictionIso_comp_one_tmul
    {U V L : P.affineOpens} (h : U ≤ V) (k : V ≤ L) (n : ℕ)
    (m : TorComparison.torSupportModule (j.ker.ideal L) (i.ker.ideal L) n) :
    (closedIntersectionQuotientTorRestrictionIso i j (h.trans k) n).hom
      ((1 : Γ(P, U) ⧸ (j.ker.ideal U ⊔ i.ker.ideal U)) ⊗ₜ[_,
        closedIntersectionSupportQuotientRestriction i j (h.trans k)] m) =
    (closedIntersectionQuotientTorRestrictionIso i j h n).hom
      ((1 : Γ(P, U) ⧸ (j.ker.ideal U ⊔ i.ker.ideal U)) ⊗ₜ[_,
        closedIntersectionSupportQuotientRestriction i j h]
        ((closedIntersectionQuotientTorRestrictionIso i j k n).hom
          ((1 : Γ(P, V) ⧸ (j.ker.ideal V ⊔ i.ker.ideal V)) ⊗ₜ[_,
            closedIntersectionSupportQuotientRestriction i j k] m))) := by
  have hc := torSupportBaseChangeIsoOfMaps_comp_generators
    (P.presheaf.map (homOfLE (show V.1 ≤ L.1 from k)).op).hom
    (P.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom
    (affineRestriction_flat k) (affineRestriction_flat h)
    (j.ker.ideal L) (i.ker.ideal L) (j.ker.ideal V) (i.ker.ideal V)
    (j.ker.ideal U) (i.ker.ideal U) (j.ker.map_ideal k) (i.ker.map_ideal k)
    (j.ker.map_ideal h) (i.ker.map_ideal h)
    (closedIntersectionSupportQuotientRestriction i j k)
    (closedIntersectionSupportQuotientRestriction i j h)
    (closedIntersectionSupportQuotientRestriction_square i j k)
    (closedIntersectionSupportQuotientRestriction_square i j h) n m
  exact (torSupportBaseChangeIsoOfMaps_congr_one_tmul _ _ _ _
    (affineRestriction_comp h k) _ _ _ _ _ _ (j.ker.map_ideal (h.trans k))
    (i.ker.map_ideal (h.trans k)) _ _
    (closedIntersectionSupportQuotientRestriction_comp i j h k) _
    (closedIntersectionSupportQuotientRestriction_square i j (h.trans k)) n m).symm.trans hc

variable {W : Scheme.{u}} (a : W ⟶ D) (b : W ⟶ T)
  [IsClosedImmersion i] [IsClosedImmersion j] (sq : IsPullback a b j i)

omit [IsClosedImmersion j] in
/-- Restricting the same whole inverse-image chart gives the identity section map. -/
theorem closedIntersectionAffineRestriction_refl (U : P.affineOpens) :
    closedIntersectionAffineRestriction j a (show U ≤ U from le_rfl) = RingHom.id _ := by
  change (W.presheaf.map (𝟙 (Opposite.op ((a ≫ j) ⁻¹ᵁ U)))).hom = _
  rw [CategoryTheory.Functor.map_id]
  rfl

omit [IsClosedImmersion j] in
/-- The actual closed inverse-image section restrictions preserve composition. -/
theorem closedIntersectionAffineRestriction_comp {U V L : P.affineOpens}
    (h : U ≤ V) (k : V ≤ L) :
    (closedIntersectionAffineRestriction j a h).comp (closedIntersectionAffineRestriction j a k) =
      closedIntersectionAffineRestriction j a (h.trans k) := by
  ext r
  exact (ConcreteCategory.congr_hom (W.presheaf.map_comp
    (homOfLE ((a ≫ j).preimage_mono k)).op
    (homOfLE ((a ≫ j).preimage_mono h)).op) r).symm

/-- The actual chart refinement retains the canonical quotient-Tor map on its original
unit tensor, through the genuine quotient-chart scalar square. -/
theorem closedIntersectionAffineTorRestrictionIso_hom_one_tmul
    {U V : P.affineOpens} (h : U ≤ V) (n : ℕ)
    (m : closedIntersectionAffineTor i a b j sq V n) :
    (closedIntersectionAffineTorRestrictionIso i j a b sq h n).hom
      ((1 : Γ(W, (a ≫ j) ⁻¹ᵁ U)) ⊗ₜ[_,closedIntersectionAffineRestriction j a h] m) =
    (closedIntersectionQuotientTorRestrictionIso i j h n).hom
      ((1 : Γ(P, U) ⧸ (j.ker.ideal U ⊔ i.ker.ideal U)) ⊗ₜ[_,
        closedIntersectionSupportQuotientRestriction i j h] m) := by
  exact congrArg (closedIntersectionQuotientTorRestrictionIso i j h n).hom
    (extendScalarsRingEquivSquareIso_hom_one_tmul _ _
      (closedIntersectionAffineQuotientEquiv i a b j sq V)
      (closedIntersectionAffineQuotientEquiv i a b j sq U)
      (closedIntersectionAffineRestriction_square i j a b sq h) _ m)

/-- The original chart-module identity transition is the actual scalar-extension unitor. -/
theorem closedIntersectionAffineTorRestrictionIso_hom_refl (U : P.affineOpens) (n : ℕ) :
    (closedIntersectionAffineTorRestrictionIso i j a b sq (show U ≤ U from le_rfl) n).hom =
      (eqToIso (congrArg (fun q => (ModuleCat.extendScalars q).obj
        (closedIntersectionAffineTor i a b j sq U n))
        (closedIntersectionAffineRestriction_refl j a U))).hom ≫
      (ModuleCat.extendScalarsId Γ(W, (a ≫ j) ⁻¹ᵁ U)).hom.app
        (closedIntersectionAffineTor i a b j sq U n) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  have hc := closedIntersectionAffineTorRestrictionIso_hom_one_tmul i j a b sq
    (show U ≤ U from le_rfl) n m
  have hq := closedIntersectionQuotientTorRestrictionIso_refl_one_tmul i j U n m
  have ht := extendScalarsEqToIso_hom_one_tmul _ _
    (closedIntersectionAffineRestriction_refl j a U)
    (closedIntersectionAffineTor i a b j sq U n) m
  exact (hc.trans hq).trans ((congrArg
    ((ModuleCat.extendScalarsId Γ(W, (a ≫ j) ⁻¹ᵁ U)).hom.app
      (closedIntersectionAffineTor i a b j sq U n)) ht).trans
      (ModuleCat.extendScalarsId_hom_app_one_tmul _ m)).symm

/-- The two original chart-module transitions equal the direct original transition,
with the actual scalar associator and literal section-ring composition equality. -/
theorem closedIntersectionAffineTorRestrictionIso_hom_comp
    {U V L : P.affineOpens} (h : U ≤ V) (k : V ≤ L) (n : ℕ) :
    (ModuleCat.extendScalarsComp (closedIntersectionAffineRestriction j a k)
      (closedIntersectionAffineRestriction j a h)).hom.app
        (closedIntersectionAffineTor i a b j sq L n) ≫
      (ModuleCat.extendScalars (closedIntersectionAffineRestriction j a h)).map
        (closedIntersectionAffineTorRestrictionIso i j a b sq k n).hom ≫
      (closedIntersectionAffineTorRestrictionIso i j a b sq h n).hom =
    (eqToIso (congrArg (fun q => (ModuleCat.extendScalars q).obj
      (closedIntersectionAffineTor i a b j sq L n))
      (closedIntersectionAffineRestriction_comp j a h k))).hom ≫
      (closedIntersectionAffineTorRestrictionIso i j a b sq (h.trans k) n).hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  have ha := ModuleCat.extendScalarsComp_hom_app_one_tmul
    (closedIntersectionAffineRestriction j a k) (closedIntersectionAffineRestriction j a h)
    (closedIntersectionAffineTor i a b j sq L n) m
  have h₁ := closedIntersectionAffineTorRestrictionIso_hom_one_tmul i j a b sq k n m
  have h₂ := closedIntersectionAffineTorRestrictionIso_hom_one_tmul i j a b sq h n
    ((closedIntersectionQuotientTorRestrictionIso i j k n).hom
      ((1 : Γ(P, V) ⧸ (j.ker.ideal V ⊔ i.ker.ideal V)) ⊗ₜ[_,
        closedIntersectionSupportQuotientRestriction i j k] m))
  have hc := closedIntersectionQuotientTorRestrictionIso_comp_one_tmul i j h k n m
  have hd := closedIntersectionAffineTorRestrictionIso_hom_one_tmul i j a b sq (h.trans k) n m
  have ht := extendScalarsEqToIso_hom_one_tmul _ _
    (closedIntersectionAffineRestriction_comp j a h k)
    (closedIntersectionAffineTor i a b j sq L n) m
  have hA := congrArg (fun x =>
    (closedIntersectionAffineTorRestrictionIso i j a b sq h n).hom
      (((ModuleCat.extendScalars (closedIntersectionAffineRestriction j a h)).map
        (closedIntersectionAffineTorRestrictionIso i j a b sq k n).hom) x)) ha
  have hB := congrArg (fun x =>
    (closedIntersectionAffineTorRestrictionIso i j a b sq h n).hom
      ((1 : Γ(W, (a ≫ j) ⁻¹ᵁ U)) ⊗ₜ[Γ(W, (a ≫ j) ⁻¹ᵁ V),
        closedIntersectionAffineRestriction j a h] x)) h₁
  have hD := congrArg (closedIntersectionAffineTorRestrictionIso i j a b sq (h.trans k) n).hom ht
  have hm := ModuleCat.ExtendScalars.map_tmul (closedIntersectionAffineRestriction j a h)
    (closedIntersectionAffineTorRestrictionIso i j a b sq k n).hom 1
    ((1 : Γ(W, (a ≫ j) ⁻¹ᵁ V)) ⊗ₜ[Γ(W, (a ≫ j) ⁻¹ᵁ L),
      closedIntersectionAffineRestriction j a k] m)
  have hM := congrArg (closedIntersectionAffineTorRestrictionIso i j a b sq h n).hom hm
  have hAM := hA.trans hM
  have hAB := hAM.trans hB
  have hABC := hAB.trans h₂
  have hABCD := hABC.trans hc.symm
  exact (hABCD.trans hd.symm).trans hD.symm

end Motivic.Intersection
