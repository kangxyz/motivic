/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.AffineMiddleTor
public import Motivic.AlgebraicGeometry.Intersection.StalkTorTransport
public import Motivic.AlgebraicGeometry.Diagonal.AffineMiddleSupportPoints
public import Motivic.AlgebraicGeometry.Correspondences.IncidenceTor

/-!
# Actual affine correspondence incidence lengths

The actual incidence point supplies all coordinate-prime compatibilities.
Constructed quotient charts and their actual stalk maps transport the local
middle-diagonal comparison to the original affine correspondence schemes.
No choice of chart, point compatibility, or Tor isomorphism is assumed in the
final length theorem. Genuine finite-length evidence transfers afterward.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct Motivic.MiddleDiagonal

universe u

namespace Motivic.Intersection

/-- Actual intersection Tor length is preserved by commuting open neighborhoods,
using the constructed actual stalk equivalence and its surjectivity. -/
theorem neighborhoodStalkTor_length
    {D T P D' T' P' : Scheme.{u}}
    (i : D ⟶ P) (d : D) (j : T ⟶ P) (t : T) (hp : i d = j t)
    (i' : D' ⟶ P') (d' : D') (j' : T' ⟶ P') (t' : T') (hp' : i' d' = j' t')
    (uD : D' ⟶ D) (uT : T' ⟶ T) (uP : P' ⟶ P)
    (hi : uD ≫ i = i' ≫ uP) (hj : uT ≫ j = j' ≫ uP)
    (hd : d = uD d') (ht : t = uT t')
    [IsOpenImmersion uD] [IsOpenImmersion uT] [IsOpenImmersion uP] (n : ℕ) :
    Module.length (ambientStalk i d)
      (((Tor (ModuleCat (ambientStalk i d)) n).obj
        (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d)) =
    Module.length (ambientStalk i' d')
      (((Tor (ModuleCat (ambientStalk i' d')) n).obj
        (coefficientStalkModule i' d' j' t' hp')).obj (sourceStalkModule i' d')) := by
  let e := neighborhoodStalkTorIso i d j t hp i' d' j' t' hp' uD uT uP hi hj hd ht n
  exact e.toLinearEquiv.length_eq.trans
    (TorComparison.length_restrictScalars_of_surjective
      (neighborhoodAmbientStalkEquiv i d i' d' uD uP hi hd).toRingHom
      (neighborhoodAmbientStalkEquiv i d i' d' uD uP hi hd).surjective _)

end Motivic.Intersection

namespace Motivic.AffineMiddle

open Intersection

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  (F : FiniteCorrespondenceGenerator (structureMap k A) (structureMap k B))
  (G : FiniteCorrespondenceGenerator (structureMap k B) (structureMap k C))

/-- The actual left ideal-subscheme inclusion after pullback to the triple product. -/
abbrev leftGeneratorPulledInclusion :=
  (F.val.comap (pullback.fst (pullback.snd (structureMap k A) (structureMap k B))
    (pullback.fst (structureMap k B) (structureMap k C)))).subschemeι

/-- The actual right ideal-subscheme inclusion after pullback to the triple product. -/
abbrev rightGeneratorPulledInclusion :=
  (G.val.comap (pullback.snd (pullback.snd (structureMap k A) (structureMap k B))
    (pullback.fst (structureMap k B) (structureMap k C)))).subschemeι

/-- The actual two pulled-support points have the same image in the triple product. -/
theorem pulledIncidencePoint_eq (w : F.incidence G) :
    rightGeneratorPulledInclusion k A B C G (incidenceToRightPulled k A B C F G w) =
      leftGeneratorPulledInclusion k A B C F (incidenceToLeftPulled k A B C F G w) :=
  (congrArg (fun f ↦ f w) (incidenceToRightPulled_inclusion k A B C F G)).trans
    (congrArg (fun f ↦ f w) (incidenceToLeftPulled_inclusion k A B C F G)).symm

/-- Actual triple-product stalk Tor of the two pulled ideal subschemes.
The left support is the coefficient; the right support is the resolved source. -/
def pulledIncidenceStalkTor (w : F.incidence G) (n : ℕ) :
    ModuleCat (ambientStalk (rightGeneratorPulledInclusion k A B C G)
      (incidenceToRightPulled k A B C F G w)) :=
  ((Tor (ModuleCat (ambientStalk (rightGeneratorPulledInclusion k A B C G)
    (incidenceToRightPulled k A B C F G w))) n).obj
      (coefficientStalkModule (rightGeneratorPulledInclusion k A B C G)
        (incidenceToRightPulled k A B C F G w) (leftGeneratorPulledInclusion k A B C F)
        (incidenceToLeftPulled k A B C F G w) (pulledIncidencePoint_eq k A B C F G w))).obj
      (sourceStalkModule (rightGeneratorPulledInclusion k A B C G)
        (incidenceToRightPulled k A B C F G w))

/-- The actual four-factor incidence Tor and actual triple-product pulled-support
Tor have equal local lengths. All quotient charts and point compatibilities
are constructed from the given affine correspondence generators. -/
theorem incidenceTor_length_eq_pulled (w : F.incidence G) (n : ℕ) :
    Module.length (F.incidenceAmbientStalk G w) (F.incidenceTor G w n) =
      Module.length (ambientStalk (rightGeneratorPulledInclusion k A B C G)
        (incidenceToRightPulled k A B C F G w)) (pulledIncidenceStalkTor k A B C F G w n) := by
  obtain ⟨I, J, eI, eJ, hI, hJ, e, he⟩ :=
    exists_generatorSupportProductPresentation k A B C F G
  let l : PrimeSpectrum (Intersection.AffineMiddleTor.leftRing k A B C I) :=
    incidenceLeftPrime k A B C F G I eI hI w
  let r : PrimeSpectrum (Intersection.AffineMiddleTor.rightRing k A B C J) :=
    incidenceRightPrime k A B C F G J eJ hJ w
  let t := incidenceSupportPrime k A B C F G I J e w
  let q := r.comap (Intersection.AffineMiddleTor.rightMap k A B C J)
  have hq : q = l.comap (Intersection.AffineMiddleTor.leftMap k A B C I) :=
    (incidenceTriplePrime_eq_right_comap k A B C F G J eJ hJ w).symm.trans
      (incidenceTriplePrime_eq_left_comap k A B C F G I eI hI w)
  have hp : q.comap (MiddleDiagonal.quotientMap k A B C).toRingHom =
      t.comap (supportRingMap k A B C I J).toRingHom := by
    change ((incidenceRightPrime k A B C F G J eJ hJ w).comap
      (Intersection.AffineMiddleTor.rightMap k A B C J)).comap _ = _
    erw [← incidenceTriplePrime_eq_right_comap k A B C F G J eJ hJ w]
    exact incidenceTriplePrime_comap_eq_support k A B C F G I J e he w
  have hd : F.incidenceInclusion G w = (tripleIso k A B C).hom q := by
    change _ = (tripleIso k A B C).hom
      ((incidenceRightPrime k A B C F G J eJ hJ w).comap
        (Intersection.AffineMiddleTor.rightMap k A B C J))
    erw [← incidenceTriplePrime_eq_right_comap k A B C F G J eJ hJ w]
    exact (Scheme.inv_hom_apply (tripleIso k A B C) (F.incidenceInclusion G w)).symm
  have ht : F.incidenceToSupportProduct G w = e.hom t :=
    (Scheme.inv_hom_apply e (F.incidenceToSupportProduct G w)).symm
  have hAmbient : Module.length (F.incidenceAmbientStalk G w) (F.incidenceTor G w n) =
      Module.length (ambientStalk
        (Intersection.AffineMiddleTor.diagonalSpecMap k A B C) q)
        (Intersection.AffineMiddleTor.ambientStalkTor k A B C I J l r t hq hp n) :=
    neighborhoodStalkTor_length
      (correspondenceTripleInclusion (structureMap k A) (structureMap k B) (structureMap k C))
      (F.incidenceInclusion G w) (F.supportProductInclusion G)
      (F.incidenceToSupportProduct G w)
      (Intersection.point_eq _ _ _ _ (F.incidence_ambient_isPullback G) w)
      (Intersection.AffineMiddleTor.diagonalSpecMap k A B C) q
      (Intersection.AffineMiddleTor.supportSpecMap k A B C I J) t hp
      (tripleIso k A B C).hom e.hom (ambientIso k A B C).hom
      (quotientMap_square k A B C).symm he.symm hd ht n
  have hr : incidenceToRightPulled k A B C F G w =
      (rightGeneratorPulledIso k A B C G J eJ hJ).hom r :=
    (Scheme.inv_hom_apply (rightGeneratorPulledIso k A B C G J eJ hJ)
      (incidenceToRightPulled k A B C F G w)).symm
  have hl : incidenceToLeftPulled k A B C F G w =
      (leftGeneratorPulledIso k A B C F I eI hI).hom l :=
    (Scheme.inv_hom_apply (leftGeneratorPulledIso k A B C F I eI hI)
      (incidenceToLeftPulled k A B C F G w)).symm
  have hPulled : Module.length (ambientStalk (rightGeneratorPulledInclusion k A B C G)
      (incidenceToRightPulled k A B C F G w)) (pulledIncidenceStalkTor k A B C F G w n) =
      Module.length (ambientStalk
        (Intersection.AffineMiddleTor.rightSpecMap k A B C J) r)
        (Intersection.AffineMiddleTor.pulledStalkTor k A B C I J l r hq n) :=
    neighborhoodStalkTor_length (rightGeneratorPulledInclusion k A B C G)
      (incidenceToRightPulled k A B C F G w) (leftGeneratorPulledInclusion k A B C F)
      (incidenceToLeftPulled k A B C F G w) (pulledIncidencePoint_eq k A B C F G w)
      (Intersection.AffineMiddleTor.rightSpecMap k A B C J) r
      (Intersection.AffineMiddleTor.leftSpecMap k A B C I) l hq
      (rightGeneratorPulledIso k A B C G J eJ hJ).hom
      (leftGeneratorPulledIso k A B C F I eI hI).hom (tripleIso k A B C).hom
      (rightGeneratorPulledIso_inclusion k A B C G J eJ hJ)
      (leftGeneratorPulledIso_inclusion k A B C F I eI hI) hr hl n
  exact hAmbient.trans
    ((Intersection.AffineMiddleTor.stalkTor_length k A B C I J l r t hq hp n).trans
      hPulled.symm)

/-- Genuine finite local Tor length and degree support transfer to the actual pulled supports. -/
theorem incidenceTor_finiteLengthSupport_iff_pulled (w : F.incidence G) :
    LengthEuler.FiniteLengthSupport (F.incidenceTor G w) ↔
      LengthEuler.FiniteLengthSupport (pulledIncidenceStalkTor k A B C F G w) := by
  have hlen := funext (incidenceTor_length_eq_pulled k A B C F G w)
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro n
      rw [← incidenceTor_length_eq_pulled k A B C F G w n]
      exact h.finite_length n
    · simpa only [hlen] using h.finite_support
  · intro h
    refine ⟨?_, ?_⟩
    · intro n
      rw [incidenceTor_length_eq_pulled k A B C F G w n]
      exact h.finite_length n
    · simpa only [hlen] using h.finite_support

/-- Actual finite local Euler coefficients agree, without discarding any higher Tor terms. -/
theorem incidenceTor_signedLengthSum_eq_pulled (w : F.incidence G) (sign : ℕ → ℤ)
    (h : LengthEuler.FiniteLengthSupport (F.incidenceTor G w)) :
    LengthEuler.signedLengthSum (F.incidenceTor G w) sign h =
      LengthEuler.signedLengthSum (pulledIncidenceStalkTor k A B C F G w) sign
        ((incidenceTor_finiteLengthSupport_iff_pulled k A B C F G w).mp h) := by
  unfold LengthEuler.signedLengthSum
  apply finsum_congr
  intro n
  simp only [LengthEuler.integerLength, incidenceTor_length_eq_pulled k A B C F G w n]

end Motivic.AffineMiddle
