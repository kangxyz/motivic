/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Diagonal.AffineClosedSupportCoordinates
public import Motivic.Aglib.AlgebraicGeometry.Intersection.Tor.NeighborhoodLength
public import Motivic.Aglib.AlgebraicGeometry.Intersection.AffineMiddleTor

/-!
# Middle-diagonal Tor for arbitrary affine closed supports

The supports are arbitrary closed immersions into the two adjacent affine
products. Their quotient and tensor charts are constructed. Actual common
points give genuine pulled-support points and every coordinate-prime square.
The local comparison requires no correspondence-generator premise.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct Algebra.TensorProduct.MiddleDiagonal

universe u

namespace AlgebraicGeometry.Scheme.Products.MiddleDiagonal.ClosedSupport
open _root_.Algebra.TensorProduct

open _root_.AlgebraicGeometry.Scheme.Intersection

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  {D E : Scheme.{u}} (a : D ⟶ leftProduct k A B) (b : E ⟶ rightProduct k B C)

/-- The actual left pulled-support inclusion in the triple product. -/
abbrev leftPulledInclusion : leftPulled k A B C a ⟶
    correspondenceTripleProduct (structureMap k A) (structureMap k B) (structureMap k C) :=
  pullback.fst _ _

/-- The actual right pulled-support inclusion in the triple product. -/
abbrev rightPulledInclusion : rightPulled k A B C b ⟶
    correspondenceTripleProduct (structureMap k A) (structureMap k B) (structureMap k C) :=
  pullback.fst _ _

/-- A genuine common ambient point gives points on both actual pulled supports. -/
theorem exists_pulledPoints
    (d : correspondenceTripleProduct (structureMap k A) (structureMap k B) (structureMap k C))
    (t : supportProduct k A B C a b)
    (hp : correspondenceTripleInclusion (structureMap k A) (structureMap k B)
      (structureMap k C) d = supportInclusion k A B C a b t) :
    ∃ l : leftPulled k A B C a, ∃ r : rightPulled k A B C b,
      leftPulledInclusion k A B C a l = d ∧ rightPulledInclusion k A B C b r = d := by
  have hL := congrArg
    (pullback.fst (pullback.snd (structureMap k A) (structureMap k B) ≫ structureMap k B)
      (pullback.fst (structureMap k B) (structureMap k C) ≫ structureMap k B)) hp
  have hR := congrArg
    (pullback.snd (pullback.snd (structureMap k A) (structureMap k B) ≫ structureMap k B)
      (pullback.fst (structureMap k B) (structureMap k C) ≫ structureMap k B)) hp
  simp only [← Scheme.Hom.comp_apply, supportInclusion, pullback.map, pullback.lift_fst] at hL
  simp only [← Scheme.Hom.comp_apply, supportInclusion, pullback.map, pullback.lift_snd] at hR
  obtain ⟨l, hl, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.fst (pullback.snd (structureMap k A) (structureMap k B))
      (pullback.fst (structureMap k B) (structureMap k C))) (g := a)
    d (pullback.fst (a ≫ pullback.snd (structureMap k A) (structureMap k B) ≫ structureMap k B)
      (b ≫ pullback.fst (structureMap k B) (structureMap k C) ≫ structureMap k B) t) hL
  obtain ⟨r, hr, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd (pullback.snd (structureMap k A) (structureMap k B))
      (pullback.fst (structureMap k B) (structureMap k C))) (g := b)
    d (pullback.snd (a ≫ pullback.snd (structureMap k A) (structureMap k B) ≫ structureMap k B)
      (b ≫ pullback.fst (structureMap k B) (structureMap k C) ≫ structureMap k B) t) hR
  exact ⟨l, r, hl, hr⟩

/-- Actual ambient stalk Tor, with the support product as coefficient. -/
abbrev ambientTor
    (d : correspondenceTripleProduct (structureMap k A) (structureMap k B) (structureMap k C))
    (t : supportProduct k A B C a b)
    (hp : correspondenceTripleInclusion (structureMap k A) (structureMap k B)
      (structureMap k C) d = supportInclusion k A B C a b t) (n : ℕ) :=
  ((Tor (ModuleCat (ambientStalk
    (correspondenceTripleInclusion (structureMap k A) (structureMap k B) (structureMap k C)) d))
    n).obj (coefficientStalkModule
      (correspondenceTripleInclusion (structureMap k A) (structureMap k B) (structureMap k C)) d
      (supportInclusion k A B C a b) t hp)).obj
    (sourceStalkModule
      (correspondenceTripleInclusion (structureMap k A) (structureMap k B) (structureMap k C)) d)

/-- Actual triple-product stalk Tor, retaining the left coefficient and right source. -/
abbrev pulledTor (l : leftPulled k A B C a) (r : rightPulled k A B C b)
    (hp : rightPulledInclusion k A B C b r = leftPulledInclusion k A B C a l) (n : ℕ) :=
  ((Tor (ModuleCat (ambientStalk (rightPulledInclusion k A B C b) r)) n).obj
    (coefficientStalkModule (rightPulledInclusion k A B C b) r
      (leftPulledInclusion k A B C a) l hp)).obj
    (sourceStalkModule (rightPulledInclusion k A B C b) r)


/-- Actual four-factor and pulled-support Tor lengths agree for arbitrary adjacent
closed supports. All quotient charts and coordinate-prime compatibilities are derived. -/
theorem stalkTor_length_eq_pulled [IsClosedImmersion a] [IsClosedImmersion b]
    (d : correspondenceTripleProduct (structureMap k A) (structureMap k B) (structureMap k C))
    (t : supportProduct k A B C a b)
    (hp : correspondenceTripleInclusion (structureMap k A) (structureMap k B)
      (structureMap k C) d = supportInclusion k A B C a b t)
    (l : leftPulled k A B C a) (r : rightPulled k A B C b)
    (hl : leftPulledInclusion k A B C a l = d)
    (hr : rightPulledInclusion k A B C b r = d) (n : ℕ) :
    Module.length (ambientStalk
      (correspondenceTripleInclusion (structureMap k A) (structureMap k B) (structureMap k C)) d)
      (ambientTor k A B C a b d t hp n) =
    Module.length (ambientStalk (rightPulledInclusion k A B C b) r)
      (pulledTor k A B C a b l r (hr.trans hl.symm) n) := by
  obtain ⟨I, J, eI, eJ, hI, hJ, e, he⟩ := exists_supportProductPresentation k A B C a b
  let : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
    (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
  let l' : PrimeSpectrum (AffineMiddleTor.leftRing k A B C I) :=
    (leftPulledIso k A B C a I eI hI).inv l
  let r' : PrimeSpectrum (AffineMiddleTor.rightRing k A B C J) :=
    (rightPulledIso k A B C b J eJ hJ).inv r
  let t' := e.inv t
  let q' := r'.comap (AffineMiddleTor.rightMap k A B C J)
  have hdL : (tripleIso k A B C).hom
      (l'.comap (AffineMiddleTor.leftMap k A B C I)) = d := by
    have hh := congrArg (fun m ↦ m l') (leftPulledIso_inclusion k A B C a I eI hI)
    change leftPulledInclusion k A B C a ((leftPulledIso k A B C a I eI hI).hom l') =
      (tripleIso k A B C).hom
        (l'.comap (AffineMiddleTor.leftMap k A B C I)) at hh
    have heq : (leftPulledIso k A B C a I eI hI).hom l' = l :=
      Scheme.inv_hom_apply _ _
    rw [heq] at hh
    exact hh.symm.trans hl
  have hdR : (tripleIso k A B C).hom q' = d := by
    have hh := congrArg (fun m ↦ m r') (rightPulledIso_inclusion k A B C b J eJ hJ)
    change rightPulledInclusion k A B C b ((rightPulledIso k A B C b J eJ hJ).hom r') =
      (tripleIso k A B C).hom q' at hh
    have heq : (rightPulledIso k A B C b J eJ hJ).hom r' = r :=
      Scheme.inv_hom_apply _ _
    rw [heq] at hh
    exact hh.symm.trans hr
  have hq : q' = l'.comap (AffineMiddleTor.leftMap k A B C I) :=
    (tripleIso k A B C).hom.isOpenEmbedding.injective (hdR.trans hdL.symm)
  have hp' : q'.comap (MiddleDiagonal.quotientMap k A B C).toRingHom =
      t'.comap (supportRingMap k A B C I J).toRingHom := by
    apply (ambientIso k A B C).hom.isOpenEmbedding.injective
    calc
      (ambientIso k A B C).hom
          (q'.comap (MiddleDiagonal.quotientMap k A B C).toRingHom) =
        correspondenceTripleInclusion (structureMap k A) (structureMap k B) (structureMap k C)
          ((tripleIso k A B C).hom q') :=
        congrArg (fun m ↦ m q') (quotientMap_square k A B C)
      _ = correspondenceTripleInclusion (structureMap k A) (structureMap k B)
          (structureMap k C) d := by rw [hdR]
      _ = supportInclusion k A B C a b t := hp
      _ = supportInclusion k A B C a b (e.hom t') :=
        congrArg (supportInclusion k A B C a b) (Scheme.inv_hom_apply e t).symm
      _ = (ambientIso k A B C).hom
          (t'.comap (supportRingMap k A B C I J).toRingHom) :=
        (congrArg (fun m ↦ m t') he).symm
  have hAmbient : Module.length (ambientStalk
      (correspondenceTripleInclusion (structureMap k A) (structureMap k B) (structureMap k C)) d)
      (ambientTor k A B C a b d t hp n) =
      Module.length (ambientStalk (AffineMiddleTor.diagonalSpecMap k A B C) q')
        (AffineMiddleTor.ambientStalkTor k A B C I J l' r' t' hq hp' n) :=
    neighborhoodStalkTor_length
      (correspondenceTripleInclusion (structureMap k A) (structureMap k B) (structureMap k C))
      d (supportInclusion k A B C a b) t hp
      (AffineMiddleTor.diagonalSpecMap k A B C) q'
      (AffineMiddleTor.supportSpecMap k A B C I J) t' hp'
      (tripleIso k A B C).hom e.hom (ambientIso k A B C).hom
      (quotientMap_square k A B C).symm he.symm hdR.symm
      (Scheme.inv_hom_apply e t).symm n
  have hPulled :
      Module.length (ambientStalk (rightPulledInclusion k A B C b) r)
        (pulledTor k A B C a b l r (hr.trans hl.symm) n) =
      Module.length (ambientStalk (AffineMiddleTor.rightSpecMap k A B C J) r')
        (AffineMiddleTor.pulledStalkTor k A B C I J l' r' hq n) :=
    neighborhoodStalkTor_length (rightPulledInclusion k A B C b) r
      (leftPulledInclusion k A B C a) l (hr.trans hl.symm)
      (AffineMiddleTor.rightSpecMap k A B C J) r'
      (AffineMiddleTor.leftSpecMap k A B C I) l' hq
      (rightPulledIso k A B C b J eJ hJ).hom (leftPulledIso k A B C a I eI hI).hom
      (tripleIso k A B C).hom (rightPulledIso_inclusion k A B C b J eJ hJ)
      (leftPulledIso_inclusion k A B C a I eI hI)
      (Scheme.inv_hom_apply (rightPulledIso k A B C b J eJ hJ) r).symm
      (Scheme.inv_hom_apply (leftPulledIso k A B C a I eI hI) l).symm n
  exact hAmbient.trans
    ((AffineMiddleTor.stalkTor_length k A B C I J l' r' t' hq hp' n).trans
      hPulled.symm)

/-- Both pulled points and the all-degree comparison are constructed from the
original common ambient point, with no supplied coordinate presentation. -/
theorem exists_stalkTor_length_eq_pulled [IsClosedImmersion a] [IsClosedImmersion b]
    (d : correspondenceTripleProduct (structureMap k A) (structureMap k B) (structureMap k C))
    (t : supportProduct k A B C a b)
    (hp : correspondenceTripleInclusion (structureMap k A) (structureMap k B)
      (structureMap k C) d = supportInclusion k A B C a b t) :
    ∃ l : leftPulled k A B C a, ∃ r : rightPulled k A B C b,
    ∃ hl : leftPulledInclusion k A B C a l = d,
    ∃ hr : rightPulledInclusion k A B C b r = d,
    ∀ n : ℕ,
      Module.length (ambientStalk
        (correspondenceTripleInclusion (structureMap k A) (structureMap k B) (structureMap k C)) d)
        (ambientTor k A B C a b d t hp n) =
      Module.length (ambientStalk (rightPulledInclusion k A B C b) r)
        (pulledTor k A B C a b l r (hr.trans hl.symm) n) := by
  obtain ⟨l, r, hl, hr⟩ := exists_pulledPoints k A B C a b d t hp
  exact ⟨l, r, hl, hr, stalkTor_length_eq_pulled k A B C a b d t hp l r hl hr⟩

end AlgebraicGeometry.Scheme.Products.MiddleDiagonal.ClosedSupport
