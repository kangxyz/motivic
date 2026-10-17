/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.ClosedIntersectionTorLocalization
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Actual affine restriction of closed-intersection Tor coefficients

Refining the ambient affine open induces the literal restriction on the whole
closed inverse-image section rings. The actual quotient-chart square and
canonical flat support-Tor base change construct the corresponding scalar-
extension isomorphism of the original chart modules. Its existence is proved,
not supplied as a transition premise. Coherence is treated separately.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.Intersection

open TorComparison

/-- Canonical support-Tor base change with literal target ideals and the actual
induced quotient map; only the proved ideal images and scalar square are used. -/
def torSupportBaseChangeIsoOfMaps {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (J K : Ideal R) (J' K' : Ideal S)
    (hJ : J.map f = J') (hK : K.map f = K')
    (q : R ⧸ (J ⊔ K) →+* S ⧸ (J' ⊔ K'))
    (hq : q.comp (Ideal.Quotient.mk (J ⊔ K)) = (Ideal.Quotient.mk (J' ⊔ K')).comp f)
    (n : ℕ) :
    (ModuleCat.extendScalars q).obj (torSupportModule J K n) ≅ torSupportModule J' K' n := by
  subst J' K'
  have he : q = supportQuotientMapSup f J K := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    exact RingHom.congr_fun hq r
  subst q
  exact torSupportBaseChangeIso f hf J K n

/-- The actual restriction between two affine section rings is flat. -/
theorem affineRestriction_flat {P : Scheme.{u}} {U V : P.affineOpens} (h : U ≤ V) :
    (P.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom.Flat := by
  exact Scheme.Hom.flat_appLE (𝟙 P) V.2 U.2 h

variable {P T D : Scheme.{u}} (i : T ⟶ P) (j : D ⟶ P)

/-- The actual sum of original closed ideals restricts to the actual smaller sum. -/
theorem closedIntersectionAffineSupport_map {U V : P.affineOpens} (h : U ≤ V) :
    (j.ker.ideal V ⊔ i.ker.ideal V).map (P.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom =
      j.ker.ideal U ⊔ i.ker.ideal U := by
  rw [Ideal.map_sup]
  exact congrArg₂ (fun I J : Ideal Γ(P, U) => I ⊔ J)
    (j.ker.map_ideal h) (i.ker.map_ideal h)

/-- The literal quotient restriction for the two original closed ideals. -/
def closedIntersectionSupportQuotientRestriction {U V : P.affineOpens} (h : U ≤ V) :
    Γ(P, V) ⧸ (j.ker.ideal V ⊔ i.ker.ideal V) →+*
      Γ(P, U) ⧸ (j.ker.ideal U ⊔ i.ker.ideal U) :=
  Ideal.quotientMap _ (P.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom
    (Ideal.map_le_iff_le_comap.mp (closedIntersectionAffineSupport_map i j h).le)

/-- The quotient restriction acts by the original section restriction on representatives. -/
theorem closedIntersectionSupportQuotientRestriction_mk {U V : P.affineOpens}
    (h : U ≤ V) (r : Γ(P, V)) :
    closedIntersectionSupportQuotientRestriction i j h (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (P.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op r) := rfl

/-- The quotient restriction keeps the actual ambient restriction square. -/
theorem closedIntersectionSupportQuotientRestriction_square {U V : P.affineOpens}
    (h : U ≤ V) :
    (closedIntersectionSupportQuotientRestriction i j h).comp
        (Ideal.Quotient.mk (j.ker.ideal V ⊔ i.ker.ideal V)) =
      (Ideal.Quotient.mk (j.ker.ideal U ⊔ i.ker.ideal U)).comp
        (P.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom := rfl

/-- Canonical flat support-Tor base change reaches the exact original ideals on U. -/
def closedIntersectionQuotientTorRestrictionIso {U V : P.affineOpens}
    (h : U ≤ V) (n : ℕ) :
    (ModuleCat.extendScalars (closedIntersectionSupportQuotientRestriction i j h)).obj
        (torSupportModule (j.ker.ideal V) (i.ker.ideal V) n) ≅
      torSupportModule (j.ker.ideal U) (i.ker.ideal U) n :=
  torSupportBaseChangeIsoOfMaps _ (affineRestriction_flat h) _ _ _ _
    (j.ker.map_ideal h) (i.ker.map_ideal h) _
    (closedIntersectionSupportQuotientRestriction_square i j h) n

variable {W : Scheme.{u}} (a : W ⟶ D) (b : W ⟶ T)
  [IsClosedImmersion i] [IsClosedImmersion j] (sq : IsPullback a b j i)

/-- The original restriction on the actual whole closed inverse-image section rings. -/
def closedIntersectionAffineRestriction {U V : P.affineOpens} (h : U ≤ V) :
    Γ(W, (a ≫ j) ⁻¹ᵁ V) →+* Γ(W, (a ≫ j) ⁻¹ᵁ U) :=
  (W.presheaf.map (homOfLE ((a ≫ j).preimage_mono h)).op).hom

/-- The actual quotient charts commute with the original inverse-image section restrictions. -/
theorem closedIntersectionAffineRestriction_square {U V : P.affineOpens} (h : U ≤ V) :
    (closedIntersectionAffineRestriction j a h).comp
        (closedIntersectionAffineQuotientEquiv i a b j sq V).toRingHom =
      (closedIntersectionAffineQuotientEquiv i a b j sq U).toRingHom.comp
        (closedIntersectionSupportQuotientRestriction i j h) := by
  apply Ideal.Quotient.ringHom_ext
  ext r
  change W.presheaf.map (homOfLE ((a ≫ j).preimage_mono h)).op
      (closedIntersectionAffineQuotientEquiv i a b j sq V (Ideal.Quotient.mk _ r)) =
    closedIntersectionAffineQuotientEquiv i a b j sq U
      (Ideal.Quotient.mk _ (P.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op r))
  rw [closedIntersectionAffineQuotientEquiv_mk, closedIntersectionAffineQuotientEquiv_mk]
  exact (ConcreteCategory.congr_hom
    ((a ≫ j).naturality (homOfLE (show U.1 ≤ V.1 from h)).op) r).symm

/-- Actual affine refinement of the original chart coefficient is scalar
extension along the literal closed-inverse-image restriction. -/
def closedIntersectionAffineTorRestrictionIso {U V : P.affineOpens}
    (h : U ≤ V) (n : ℕ) :
    (ModuleCat.extendScalars (closedIntersectionAffineRestriction j a h)).obj
        (closedIntersectionAffineTor i a b j sq V n) ≅
      closedIntersectionAffineTor i a b j sq U n :=
  extendScalarsRingEquivSquareIso _ _
    (closedIntersectionAffineQuotientEquiv i a b j sq V)
    (closedIntersectionAffineQuotientEquiv i a b j sq U)
    (closedIntersectionAffineRestriction_square i j a b sq h) _ ≪≫
      (ModuleCat.restrictScalars
        (closedIntersectionAffineQuotientEquiv i a b j sq U).symm.toRingHom).mapIso
        (closedIntersectionQuotientTorRestrictionIso i j h n)

end Motivic.Intersection
