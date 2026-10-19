/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.StalkTorTransport
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.AmbientLength
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Constructed quotient charts on closed-support neighborhoods

An arbitrary closed support restricted to an actual affine open neighborhood
has a quotient chart with the exact inclusion square and exact point range.
The restricted support need not be a finite-correspondence generator. Its
quotient presentation and point lifts are constructed, rather than assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Intersection

variable {P T : Scheme.{u}} (R : Type u) [CommRing R]
  (i : T ⟶ P) [IsClosedImmersion i]
  (uP : Spec (CommRingCat.of R) ⟶ P) [IsOpenImmersion uP]

/-- Restriction of any closed support to an affine open has an actual quotient
chart. Its range is exactly the support points lying in the ambient open. -/
theorem exists_closedAffineNeighborhood :
    ∃ I : Ideal R, ∃ v : Spec (CommRingCat.of (R ⧸ I)) ⟶ T,
      IsOpenImmersion v ∧
      v ≫ i = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ uP ∧
      Set.range v = i ⁻¹' Set.range uP := by
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (f := pullback.fst uP i)).mp inferInstance
  let v : Spec (CommRingCat.of (R ⧸ I)) ⟶ T := e.inv ≫ pullback.snd uP i
  have hs : v ≫ i = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ uP := by
    dsimp [v]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, he]
    simp only [Iso.inv_hom_id_assoc]
  refine ⟨I, v, inferInstance, hs, ?_⟩
  ext t
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) q,
      (congrArg (fun m ↦ m q) hs).symm⟩
  · intro ht
    have ht' : t ∈ Set.range (pullback.snd uP i) := by
      rw [Scheme.Pullback.range_snd]
      exact ht
    obtain ⟨w, hw⟩ := ht'
    refine ⟨e.hom w, ?_⟩
    change pullback.snd uP i (e.inv (e.hom w)) = t
    rw [Scheme.hom_inv_apply, hw]

/-- Every given support point in the ambient affine neighborhood has a point
in the constructed quotient chart; no finite-source assertion is required. -/
theorem exists_pointedClosedAffineNeighborhood (t : T) (ht : i t ∈ Set.range uP) :
    ∃ I : Ideal R, ∃ v : Spec (CommRingCat.of (R ⧸ I)) ⟶ T,
      IsOpenImmersion v ∧
      v ≫ i = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ uP ∧
      ∃ q : PrimeSpectrum (R ⧸ I), v q = t := by
  obtain ⟨I, v, hv, hs, hr⟩ := exists_closedAffineNeighborhood R i uP
  refine ⟨I, v, hv, hs, ?_⟩
  change t ∈ Set.range v
  rw [hr]
  exact ht

variable {D : Scheme.{u}} (j : D ⟶ P) [IsClosedImmersion j]

/-- Two actual closed supports have simultaneous quotient neighborhoods over the
same ambient affine chart. Their coordinate primes agree over the ambient ring. -/
theorem exists_closedAffineIntersectionCharts (d : T) (t : D) (hp : i d = j t)
    (hd : i d ∈ Set.range uP) :
    ∃ I J : Ideal R,
    ∃ vI : Spec (CommRingCat.of (R ⧸ I)) ⟶ T,
    ∃ vJ : Spec (CommRingCat.of (R ⧸ J)) ⟶ D,
      IsOpenImmersion vI ∧ IsOpenImmersion vJ ∧
      vI ≫ i = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ uP ∧
      vJ ≫ j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ uP ∧
      ∃ q : PrimeSpectrum (R ⧸ I), ∃ r : PrimeSpectrum (R ⧸ J),
        vI q = d ∧ vJ r = t ∧
        q.comap (Ideal.Quotient.mk I) = r.comap (Ideal.Quotient.mk J) := by
  obtain ⟨I, vI, hvI, hsI, q, hq⟩ := exists_pointedClosedAffineNeighborhood R i uP d hd
  obtain ⟨J, vJ, hvJ, hsJ, r, hr⟩ := exists_pointedClosedAffineNeighborhood R j uP t
    (hp ▸ hd)
  refine ⟨I, J, vI, vJ, hvI, hvJ, hsI, hsJ, q, r, hq, hr, ?_⟩
  apply uP.isOpenEmbedding.injective
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ uP) q =
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ uP) r
  rw [← hsI, ← hsJ]
  change i (vI q) = j (vJ r)
  rw [hq, hr, hp]

/-- Literal quotient-coordinate Tor localized at the source's ambient prime.
The second ideal supplies the coefficient and the first the resolved source. -/
abbrev quotientLocalizedTor (I J : Ideal R) (q : PrimeSpectrum (R ⧸ I)) (n : ℕ) :=
  ModuleCat.of (Localization.AtPrime (q.comap (Ideal.Quotient.mk I)).asIdeal)
    (LocalizedModule (q.comap (Ideal.Quotient.mk I)).asIdeal.primeCompl
      (((Tor (ModuleCat R) n).obj (specCoordinateModule (Ideal.Quotient.mk J))).obj
        (specCoordinateModule (Ideal.Quotient.mk I))))

/-- Actual closed-support intersection lengths have constructed quotient coordinates
on any given ambient affine neighborhood. The equality is extended-natural. -/
theorem exists_closedAffineStalkTorLength (d : T) (t : D) (hp : i d = j t)
    (hd : i d ∈ Set.range uP) :
    ∃ I J : Ideal R, ∃ q : PrimeSpectrum (R ⧸ I), ∃ r : PrimeSpectrum (R ⧸ J),
      q.comap (Ideal.Quotient.mk I) = r.comap (Ideal.Quotient.mk J) ∧
      ∀ n : ℕ,
        Module.length (ambientStalk i d)
          (((Tor (ModuleCat (ambientStalk i d)) n).obj
            (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d)) =
        Module.length (Localization.AtPrime (q.comap (Ideal.Quotient.mk I)).asIdeal)
          (quotientLocalizedTor R I J q n) := by
  obtain ⟨I, J, vI, vJ, hvI, hvJ, hsI, hsJ, q, r, hq, hr, hqr⟩ :=
    exists_closedAffineIntersectionCharts R i uP j d t hp hd
  let := hvI
  let := hvJ
  refine ⟨I, J, q, r, hqr, fun n ↦ ?_⟩
  let e := closedChartStalkTorIso i d j t hp
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective q
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective r hqr
    vI vJ uP hsI hsJ hq.symm hr.symm n
  exact e.toLinearEquiv.length_eq.trans
    ((_root_.ModuleCat.length_restrictScalars_of_surjective
      (neighborhoodAmbientStalkEquiv i d (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        q vI uP hsI hq.symm).toRingHom
      (neighborhoodAmbientStalkEquiv i d (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        q vI uP hsI hq.symm).surjective _).trans
      (_root_.ModuleCat.length_restrictScalars_of_surjective
        (specAmbientStalkEquiv (Ideal.Quotient.mk I) q).toRingHom
        (specAmbientStalkEquiv (Ideal.Quotient.mk I) q).surjective _))

/-- At every common point of arbitrary closed supports, actual local Tor lengths
admit quotient coordinates obtained from an actual ambient affine neighborhood.
No chart, point-compatibility, or Tor-comparison premise is supplied. -/
theorem exists_stalkTorLength_quotientCoordinates (d : T) (t : D) (hp : i d = j t) :
    ∃ R : CommRingCat.{u}, ∃ I J : Ideal R,
    ∃ q : PrimeSpectrum (R ⧸ I), ∃ r : PrimeSpectrum (R ⧸ J),
      q.comap (Ideal.Quotient.mk I) = r.comap (Ideal.Quotient.mk J) ∧
      ∀ n : ℕ,
        Module.length (ambientStalk i d)
          (((Tor (ModuleCat (ambientStalk i d)) n).obj
            (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d)) =
        Module.length (Localization.AtPrime (q.comap (Ideal.Quotient.mk I)).asIdeal)
          (quotientLocalizedTor R I J q n) := by
  obtain ⟨R, uP, huP, p, hp'⟩ := Scheme.exists_Spec_apply_eq (i d)
  let := huP
  exact ⟨R, exists_closedAffineStalkTorLength R i uP j d t hp ⟨p, hp'⟩⟩

end AlgebraicGeometry.Scheme.Intersection
