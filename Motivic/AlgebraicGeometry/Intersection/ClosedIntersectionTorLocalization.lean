/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.ClosedIntersectionTorChart
public import Motivic.AlgebraicGeometry.Intersection.ExteriorKoszulTorSupport
public import Motivic.Algebra.Homology.TorComparison.QuotientCoefficientExtension

/-!
# Literal affine Tor localization at actual closed-intersection stalks

The germ map from an affine ambient neighborhood is flat, and it carries the
original two section ideals to the actual closed-stalk kernels. Canonical Tor
base change therefore identifies the affine quotient-supported coefficient
with the actual supported stalk, retaining the whole sum ideal and the genuine
section-to-stalk scalar square. No genericity or regular-list premise is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Motivic.Intersection

open TorComparison

/-- Extension through a ring equivalence agrees with inverse scalar restriction. -/
def extendScalarsRingEquivIso {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars e.toRingHom).obj M ≅
      (ModuleCat.restrictScalars e.symm.toRingHom).obj M := by
  let adj : ModuleCat.extendScalars.{u, u, u} e.toRingHom ⊣
      ModuleCat.restrictScalars.{u} e.toRingHom := ModuleCat.extendRestrictScalarsAdj e.toRingHom
  have : (ModuleCat.restrictScalars.{u} e.toRingHom).IsEquivalence := inferInstance
  have : (ModuleCat.extendScalars.{u, u, u} e.toRingHom).IsEquivalence :=
    adj.isEquivalence_left_of_isEquivalence_right
  let c : (ModuleCat.extendScalars e.toRingHom).obj
      ((ModuleCat.restrictScalars e.toRingHom).obj
        ((ModuleCat.restrictScalars e.symm.toRingHom).obj M)) ≅
      (ModuleCat.restrictScalars e.symm.toRingHom).obj M := asIso (adj.counit.app _)
  exact (ModuleCat.extendScalars e.toRingHom).mapIso
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).counitIso.app M).symm ≪≫
      c

/-- Scalar extension respects a proved square of ring equivalences and actual maps. -/
def extendScalarsRingEquivSquareIso {R S A B : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (f : R →+* S) (g : A →+* B) (eR : R ≃+* A) (eS : S ≃+* B)
    (h : g.comp eR.toRingHom = eS.toRingHom.comp f) (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars g).obj
        ((ModuleCat.restrictScalars eR.symm.toRingHom).obj M) ≅
      (ModuleCat.restrictScalars eS.symm.toRingHom).obj
        ((ModuleCat.extendScalars f).obj M) :=
  (ModuleCat.extendScalars g).mapIso (extendScalarsRingEquivIso eR M).symm ≪≫
    (ModuleCat.extendScalarsComp eR.toRingHom g).symm.app M ≪≫
    eqToIso (congrArg (fun q : R →+* B => (ModuleCat.extendScalars q).obj M) h) ≪≫
    (ModuleCat.extendScalarsComp f eS.toRingHom).app M ≪≫
    extendScalarsRingEquivIso eS ((ModuleCat.extendScalars f).obj M)

/-- An actual affine germ is flat because the actual stalk is its prime localization. -/
theorem affineGerm_flat {P : Scheme.{u}} (U : P.affineOpens) (p : P) (hp : p ∈ U.1) :
    (P.presheaf.germ U.1 p hp).hom.Flat := by
  let : Algebra Γ(P, U) (P.presheaf.stalk p) := (P.presheaf.germ U.1 p hp).hom.toAlgebra
  have := U.2.isLocalization_stalk ⟨p, hp⟩
  exact IsLocalization.flat (P.presheaf.stalk p) (U.2.primeIdealOf ⟨p, hp⟩).asIdeal.primeCompl

variable {D T P : Scheme.{u}} (i : D ⟶ P) (d : D) (j : T ⟶ P) (t : T)
  (hp : i d = j t) [IsClosedImmersion i] [IsClosedImmersion j]

/-- The literal source section ideal localizes to its actual stalk-map kernel. -/
theorem affineSourceKernel_map (U : P.affineOpens) (hd : i d ∈ U.1) :
    (i.ker.ideal U).map (P.presheaf.germ U.1 (i d) hd).hom =
      RingHom.ker (i.stalkMap d).hom := by
  rw [← i.ker.stalk_eq_map U hd, i.ker_stalk d]

omit [IsClosedImmersion i] in
/-- The coefficient ideal localizes with the exact common-point stalk transport. -/
theorem affineCoefficientKernel_map (U : P.affineOpens) (hd : i d ∈ U.1) :
    (j.ker.ideal U).map (P.presheaf.germ U.1 (i d) hd).hom =
      RingHom.ker (coefficientStalkMap i d j t hp).hom := by
  rw [← j.ker.stalk_eq_map U hd, coefficientStalkMap, CommRingCat.hom_comp,
    ← RingHom.comap_ker, ← j.ker_stalk t, j.ker.stalk_congr_comap hp]

variable {V : Scheme.{u}} (a : V ⟶ D) (b : V ⟶ T) (sq : IsPullback a b i j)

include sq in
/-- Both original affine ideals generate precisely the actual intersection stalk kernel. -/
theorem affineIntersectionSupport_map (U : P.affineOpens) (w : V)
    (hw : (a ≫ i) w ∈ U.1) :
    (i.ker.ideal U).map (P.presheaf.germ U.1 ((a ≫ i) w) hw).hom ⊔
        (j.ker.ideal U).map (P.presheaf.germ U.1 ((a ≫ i) w) hw).hom =
      RingHom.ker ((a ≫ i).stalkMap w).hom := by
  change (i.ker.ideal U).map (P.presheaf.germ U.1 (i (a w)) hw).hom ⊔
    (j.ker.ideal U).map (P.presheaf.germ U.1 (i (a w)) hw).hom = _
  rw [affineSourceKernel_map i (a w) U hw,
    affineCoefficientKernel_map i (a w) j (b w) (point_eq a b i j sq w) U hw]
  exact (stalkMap_kernel_eq_sup a b i j sq w).symm

/-- The full localized support quotient is the original actual intersection stalk. -/
def affineIntersectionStalkQuotientEquiv (U : P.affineOpens) (w : V)
    (hw : (a ≫ i) w ∈ U.1) :
    P.presheaf.stalk ((a ≫ i) w) ⧸
      ((i.ker.ideal U).map (P.presheaf.germ U.1 ((a ≫ i) w) hw).hom ⊔
        (j.ker.ideal U).map (P.presheaf.germ U.1 ((a ≫ i) w) hw).hom) ≃+*
      V.presheaf.stalk w :=
  (Ideal.quotEquivOfEq (affineIntersectionSupport_map i j a b sq U w hw)).trans
    (((a ≫ i).stalkMap w).hom.quotientKerEquivOfSurjective
      (intersectionStalkMap_surjective a b i j sq w))

/-- The localized support equivalence retains the literal ambient stalk map. -/
theorem affineIntersectionStalkQuotientEquiv_mk (U : P.affineOpens) (w : V)
    (hw : (a ≫ i) w ∈ U.1) (r : P.presheaf.stalk ((a ≫ i) w)) :
    affineIntersectionStalkQuotientEquiv i j a b sq U w hw
      (Ideal.Quotient.mk _ r) = (a ≫ i).stalkMap w r := by
  simp only [affineIntersectionStalkQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- The supported stalk uses the already constructed surjective-stalk descent action. -/
abbrev closedIntersectionSupportedStalkTor (w : V) (n : ℕ) :
    ModuleCat.{u} (V.presheaf.stalk w) :=
  StalkDescent.descendedModule ((a ≫ i).stalkMap w).hom
    (intersectionStalkMap_surjective a b i j sq w)
    (((Tor (ModuleCat (ambientStalk i (a w))) n).obj
      (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w))).obj
      (sourceStalkModule i (a w)))
    ((stalkMap_kernel_eq_sup a b i j sq w).symm ▸
      stalkSupport_annihilates_tor i (a w) j (b w) (point_eq a b i j sq w) n)

/-- The mapped affine support Tor has exactly the existing actual supported-stalk action. -/
def affineMappedTorSupportedStalkIso (U : P.affineOpens) (w : V)
    (hw : (a ≫ i) w ∈ U.1) (n : ℕ) :
    torSupportModule
      ((i.ker.ideal U).map (P.presheaf.germ U.1 ((a ≫ i) w) hw).hom)
      ((j.ker.ideal U).map (P.presheaf.germ U.1 ((a ≫ i) w) hw).hom) n ≅
      (ModuleCat.restrictScalars
        (affineIntersectionStalkQuotientEquiv i j a b sq U w hw).toRingHom).obj
          (closedIntersectionSupportedStalkTor i j a b sq w n) := by
  have aux (I J : Ideal (ambientStalk i (a w)))
      (hI : I = RingHom.ker (i.stalkMap (a w)).hom)
      (hJ : J = RingHom.ker
        (coefficientStalkMap i (a w) j (b w) (point_eq a b i j sq w)).hom)
      (e : (ambientStalk i (a w)) ⧸ (I ⊔ J) ≃+* V.presheaf.stalk w)
      (he : ∀ r, e (Ideal.Quotient.mk _ r) = (a ≫ i).stalkMap w r) :
      torSupportModule I J n ≅ (ModuleCat.restrictScalars e.toRingHom).obj
        (closedIntersectionSupportedStalkTor i j a b sq w n) := by
    subst I J
    let f : ambientStalk i (a w) →+* V.presheaf.stalk w := ((a ≫ i).stalkMap w).hom
    have hf : Function.Surjective f := intersectionStalkMap_surjective a b i j sq w
    have hker : RingHom.ker (i.stalkMap (a w)).hom ⊔
        RingHom.ker (coefficientStalkMap i (a w) j (b w) (point_eq a b i j sq w)).hom =
        RingHom.ker f := (stalkMap_kernel_eq_sup a b i j sq w).symm
    let e₀ := (Ideal.quotEquivOfEq hker).trans
      (f.quotientKerEquivOfSurjective hf)
    have heq : e = e₀ := by
      apply RingEquiv.ext
      intro x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      change e (Ideal.Quotient.mk _ r) =
        f.quotientKerEquivOfSurjective hf (Ideal.Quotient.mk _ r)
      exact (he r).trans
        (RingHom.quotientKerEquivOfSurjective_apply_mk (f := f) hf r).symm
    subst e
    exact torSupportActualStalkIso a b i j sq w n
  exact aux _ _ (affineSourceKernel_map i (a w) U hw)
    (affineCoefficientKernel_map i (a w) j (b w) (point_eq a b i j sq w) U hw)
    (affineIntersectionStalkQuotientEquiv i j a b sq U w hw)
    (affineIntersectionStalkQuotientEquiv_mk i j a b sq U w hw)

/-- Localizing the canonical affine support coefficient gives the actual supported
stalk through the full literal localized support quotient. -/
def affineCanonicalTorSupportedStalkIso (U : P.affineOpens) (w : V)
    (hw : (a ≫ i) w ∈ U.1) (n : ℕ) :
    (ModuleCat.extendScalars (supportQuotientMapSup
      (P.presheaf.germ U.1 ((a ≫ i) w) hw).hom (i.ker.ideal U) (j.ker.ideal U))).obj
        (torSupportModule (i.ker.ideal U) (j.ker.ideal U) n) ≅
      (ModuleCat.restrictScalars
        (affineIntersectionStalkQuotientEquiv i j a b sq U w hw).toRingHom).obj
          (closedIntersectionSupportedStalkTor i j a b sq w n) :=
  torSupportBaseChangeIso _ (affineGerm_flat U ((a ≫ i) w) hw) _ _ n ≪≫
    affineMappedTorSupportedStalkIso i j a b sq U w hw n

/-- The original section quotient chart and localized support chart commute
with the literal intersection germ, including nilpotent structure. -/
theorem affineIntersectionQuotient_germ_square (U : P.affineOpens) (w : V)
    (hw : (a ≫ i) w ∈ U.1) :
    (V.presheaf.germ ((a ≫ i) ⁻¹ᵁ U) w hw).hom.comp
        (closedIntersectionAffineQuotientEquiv j a b i sq U).toRingHom =
      (affineIntersectionStalkQuotientEquiv i j a b sq U w hw).toRingHom.comp
        (supportQuotientMapSup (P.presheaf.germ U.1 ((a ≫ i) w) hw).hom
          (i.ker.ideal U) (j.ker.ideal U)) := by
  apply Ideal.Quotient.ringHom_ext
  ext r
  change (V.presheaf.germ ((a ≫ i) ⁻¹ᵁ U) w hw)
    (closedIntersectionAffineQuotientEquiv j a b i sq U (Ideal.Quotient.mk _ r)) =
      affineIntersectionStalkQuotientEquiv i j a b sq U w hw
        (Ideal.Quotient.mk _ (P.presheaf.germ U.1 ((a ≫ i) w) hw r))
  rw [closedIntersectionAffineQuotientEquiv_mk, affineIntersectionStalkQuotientEquiv_mk]
  exact ((a ≫ i).germ_stalkMap_apply U w hw r).symm

/-- Scalar extension of the actual affine coefficient along its actual germ is
the existing supported intersection-stalk Tor in every degree. -/
def closedIntersectionAffineTorStalkIso (U : P.affineOpens) (w : V)
    (hw : (a ≫ i) w ∈ U.1) (n : ℕ) :
    (ModuleCat.extendScalars (V.presheaf.germ ((a ≫ i) ⁻¹ᵁ U) w hw).hom).obj
        (closedIntersectionAffineTor j a b i sq U n) ≅
      closedIntersectionSupportedStalkTor i j a b sq w n :=
  extendScalarsRingEquivSquareIso _ _
    (closedIntersectionAffineQuotientEquiv j a b i sq U)
    (affineIntersectionStalkQuotientEquiv i j a b sq U w hw)
    (affineIntersectionQuotient_germ_square i j a b sq U w hw) _ ≪≫
      (ModuleCat.restrictScalars
        (affineIntersectionStalkQuotientEquiv i j a b sq U w hw).symm.toRingHom).mapIso
        (affineCanonicalTorSupportedStalkIso i j a b sq U w hw n) ≪≫
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (affineIntersectionStalkQuotientEquiv i j a b sq U w hw)).unitIso.app _).symm

/-- The localization is also the literal tensor over the actual support-section
ring, with the algebra action defined by the original germ homomorphism. -/
def closedIntersectionAffineTorTensorStalkIso (U : P.affineOpens) (w : V)
    (hw : (a ≫ i) w ∈ U.1) (n : ℕ) :
    letI : Algebra Γ(V, (a ≫ i) ⁻¹ᵁ U) (V.presheaf.stalk w) :=
      (V.presheaf.germ ((a ≫ i) ⁻¹ᵁ U) w hw).hom.toAlgebra
    ModuleCat.of (V.presheaf.stalk w)
      (V.presheaf.stalk w ⊗[Γ(V, (a ≫ i) ⁻¹ᵁ U)]
        closedIntersectionAffineTor j a b i sq U n) ≅
      closedIntersectionSupportedStalkTor i j a b sq w n :=
  (extendScalarsTensorIso (V.presheaf.germ ((a ≫ i) ⁻¹ᵁ U) w hw).hom _).symm ≪≫
    closedIntersectionAffineTorStalkIso i j a b sq U w hw n

/-- Restriction of the constructed supported stalk recovers the original
ambient categorical Tor with its literal ambient-stalk map. -/
def closedIntersectionSupportedStalkTorRestrictIso (w : V) (n : ℕ) :
    (ModuleCat.restrictScalars ((a ≫ i).stalkMap w).hom).obj
        (closedIntersectionSupportedStalkTor i j a b sq w n) ≅
      (((Tor (ModuleCat (ambientStalk i (a w))) n).obj
        (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w))).obj
        (sourceStalkModule i (a w))) :=
  (StalkDescent.restrictIso _ (intersectionStalkMap_surjective a b i j sq w) _ _).symm

/-- The actual affine coefficient localization computes the original ambient
Koszul homology whenever the actual source kernel has a genuine regular list. -/
def closedIntersectionAffineTorKoszulStalkIso (U : P.affineOpens) (w : V)
    (hw : (a ≫ i) w ∈ U.1) (s : List (ambientStalk i (a w)))
    (hker : RingHom.ker (i.stalkMap (a w)).hom = Ideal.ofList s)
    (hs : RingTheory.Sequence.IsRegular (ambientStalk i (a w)) s) (n : ℕ) :
    (ModuleCat.restrictScalars ((a ≫ i).stalkMap w).hom).obj
      ((ModuleCat.extendScalars (V.presheaf.germ ((a ≫ i) ⁻¹ᵁ U) w hw).hom).obj
        (closedIntersectionAffineTor j a b i sq U n)) ≅
      (Koszul.coefficientComplex
        (coefficientStalkModule i (a w) j (b w) (point_eq a b i j sq w)) s).homology n :=
  (ModuleCat.restrictScalars ((a ≫ i).stalkMap w).hom).mapIso
    (closedIntersectionAffineTorStalkIso i j a b sq U w hw n) ≪≫
      closedIntersectionSupportedStalkTorRestrictIso i j a b sq w n ≪≫
      torIsoHomology i (a w) j (b w) (point_eq a b i j sq w) s hker hs n

end Motivic.Intersection
