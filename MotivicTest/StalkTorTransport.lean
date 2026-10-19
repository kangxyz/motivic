/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.StalkTorTransport

/-!
# Actual open-restriction and coordinate-scheme consumers

The open-neighborhood example uses actual inverse-image open subschemes and
proves their scalar squares by morphism restriction. The coordinate example
uses canonical affine scheme isomorphisms and their naturality. A quotient
chart example composes the geometric transport with actual localized Tor of
coordinate quotients. No module or Tor isomorphism is an input.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Intersection

universe u

namespace MotivicTest.StalkTorTransport

variable {D T P : Scheme.{u}}
  (i : D ⟶ P) (d : D) (j : T ⟶ P) (t : T) (hp : i d = j t)

include hp in
/-- Actual restricted source points still have exactly the same ambient point. -/
theorem openSubsetPoints_eq (U : P.Opens) (hd : i d ∈ U) (ht : j t ∈ U) :
    (i ∣_ U) ⟨d, hd⟩ = (j ∣_ U) ⟨t, ht⟩ := by
  apply Subtype.ext
  exact (morphismRestrict_base_coe i U ⟨d, hd⟩).trans
    (hp.trans (morphismRestrict_base_coe j U ⟨t, ht⟩).symm)

/-- Restricting the whole intersection diagram to a genuine ambient open
subset transports its actual all-degree Tor, including the two inverse-image opens. -/
def openSubsetStalkTorIso (U : P.Opens) (hd : i d ∈ U) (ht : j t ∈ U) (n : ℕ) :
    ((Tor (ModuleCat (ambientStalk i d)) n).obj
      (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d) ≅
      (ModuleCat.restrictScalars
        (neighborhoodAmbientStalkEquiv i d (i ∣_ U) ⟨d, hd⟩ (i ⁻¹ᵁ U).ι U.ι
          (morphismRestrict_ι i U).symm rfl).toRingHom).obj
        (((Tor (ModuleCat (ambientStalk (i ∣_ U) ⟨d, hd⟩)) n).obj
          (coefficientStalkModule (i ∣_ U) ⟨d, hd⟩ (j ∣_ U) ⟨t, ht⟩
            (openSubsetPoints_eq i d j t hp U hd ht))).obj
          (sourceStalkModule (i ∣_ U) ⟨d, hd⟩)) :=
  neighborhoodStalkTorIso i d j t hp (i ∣_ U) ⟨d, hd⟩ (j ∣_ U) ⟨t, ht⟩
    (openSubsetPoints_eq i d j t hp U hd ht) (i ⁻¹ᵁ U).ι (j ⁻¹ᵁ U).ι U.ι
    (morphismRestrict_ι i U).symm (morphismRestrict_ι j U).symm rfl rfl n

section AffineCoordinates

variable [IsAffine D] [IsAffine T] [IsAffine P]

include hp in
/-- Coordinate-scheme points agree by naturality of the canonical affine isomorphisms. -/
theorem affineCoordinatePoints_eq :
    Spec.map i.appTop (D.isoSpec.hom d) = Spec.map j.appTop (T.isoSpec.hom t) := by
  change (D.isoSpec.hom ≫ Spec.map i.appTop) d =
    (T.isoSpec.hom ≫ Spec.map j.appTop) t
  rw [Scheme.isoSpec_hom_naturality, Scheme.isoSpec_hom_naturality]
  exact congrArg P.isoSpec.hom hp

/-- Actual affine schemes transport to their actual coordinate spectra by the
canonical scheme isomorphisms, with all naturality squares discharged. -/
def affineCoordinateStalkTorIso (n : ℕ) :
    ((Tor (ModuleCat (ambientStalk i d)) n).obj
      (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d) ≅
      (ModuleCat.restrictScalars
        (neighborhoodAmbientStalkEquiv i d (Spec.map i.appTop) (D.isoSpec.hom d)
          D.isoSpec.inv P.isoSpec.inv (Scheme.isoSpec_inv_naturality i).symm
          (by simp [← Scheme.Hom.comp_apply])).toRingHom).obj
        (((Tor (ModuleCat (ambientStalk (Spec.map i.appTop) (D.isoSpec.hom d))) n).obj
          (coefficientStalkModule (Spec.map i.appTop) (D.isoSpec.hom d)
            (Spec.map j.appTop) (T.isoSpec.hom t)
            (affineCoordinatePoints_eq i d j t hp))).obj
          (sourceStalkModule (Spec.map i.appTop) (D.isoSpec.hom d))) :=
  neighborhoodStalkTorIso i d j t hp (Spec.map i.appTop) (D.isoSpec.hom d)
    (Spec.map j.appTop) (T.isoSpec.hom t) (affineCoordinatePoints_eq i d j t hp)
    D.isoSpec.inv T.isoSpec.inv P.isoSpec.inv
    (Scheme.isoSpec_inv_naturality i).symm (Scheme.isoSpec_inv_naturality j).symm
    (by simp [← Scheme.Hom.comp_apply]) (by simp [← Scheme.Hom.comp_apply]) n

end AffineCoordinates

section QuotientCharts

variable {R : Type u} [CommRing R]

/-- Affine open charts modeled by two actual quotient supports give localized
coordinate Tor on the original schemes, without regularity or support flatness. -/
def quotientChartStalkTorIso (I J : Ideal R)
    (p : PrimeSpectrum (R ⧸ I)) (q : PrimeSpectrum (R ⧸ J))
    (hpq : p.comap (Ideal.Quotient.mk I) = q.comap (Ideal.Quotient.mk J))
    (vD : Spec (.of (R ⧸ I)) ⟶ D) (vT : Spec (.of (R ⧸ J)) ⟶ T)
    (vP : Spec (.of R) ⟶ P)
    [IsOpenImmersion vD] [IsOpenImmersion vT] [IsOpenImmersion vP]
    (hD : vD ≫ i = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ vP)
    (hT : vT ≫ j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ vP)
    (hpd : d = vD p) (hqt : t = vT q) (n : ℕ) :
    ((Tor (ModuleCat (ambientStalk i d)) n).obj
      (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d) ≅
      (ModuleCat.restrictScalars
        (neighborhoodAmbientStalkEquiv i d
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) p vD vP hD hpd).toRingHom).obj
        ((ModuleCat.restrictScalars
          (specAmbientStalkEquiv (Ideal.Quotient.mk I) p).toRingHom).obj
          (ModuleCat.of (Localization.AtPrime (p.comap (Ideal.Quotient.mk I)).asIdeal)
            (LocalizedModule (p.comap (Ideal.Quotient.mk I)).asIdeal.primeCompl
              (((Tor (ModuleCat R) n).obj (specCoordinateModule (Ideal.Quotient.mk J))).obj
                (specCoordinateModule (Ideal.Quotient.mk I)))))) :=
  closedChartStalkTorIso i d j t hp (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective q hpq vD vT vP hD hT hpd hqt n

end QuotientCharts

end MotivicTest.StalkTorTransport
