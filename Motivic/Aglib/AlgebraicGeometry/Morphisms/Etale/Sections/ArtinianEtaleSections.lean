/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Sections.HenselianEtaleSections
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Sections of étale schemes over Artinian bases

An étale morphism over a locally Artinian scheme admits a section if each
residue-field point has a rational lift. The base is covered by disjoint
singleton affine opens, and the local Artinian sections glue. In particular,
this applies over any commutative Artinian ring, including nonlocal,
nonreduced, and zero rings. The total scheme need not be affine or finite.

This result splits an étale cover over the entire Artinian base. It does not
by itself descend that splitting to a neighborhood of a larger ambient base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Hom.ArtinianEtale

private theorem exists_lift_of_field_point {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ y : Y, ∃ s : Spec (Y.residueField y) ⟶ X,
      s ≫ f = Y.fromSpecResidueField y)
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ Y) :
    ∃ b : Spec (.of K) ⟶ X, b ≫ f = a := by
  obtain ⟨s, hs⟩ := h (a (closedPoint K))
  refine ⟨Spec.map (Y.descResidueField (Scheme.stalkClosedPointTo a)) ≫ s, ?_⟩
  rw [Category.assoc, hs]
  exact Y.descResidueField_stalkClosedPointTo_fromSpecResidueField K a

private theorem exists_section_over_singleton {X Y : Scheme.{u}}
    [IsLocallyArtinian Y] [Subsingleton Y] (y : Y)
    (f : X ⟶ Y) [Etale f]
    (h : ∀ y : Y, ∃ s : Spec (Y.residueField y) ⟶ X,
      s ≫ f = Y.fromSpecResidueField y) :
    ∃ t : Y ⟶ X, t ≫ f = 𝟙 Y := by
  let A := Γ(Y, ⊤)
  let e : Y ≅ Spec A := Y.isoSpec
  have : IsArtinianRing A := inferInstance
  have : Subsingleton (PrimeSpectrum A) := ⟨fun a b ↦
    e.inv.homeomorph.injective (Subsingleton.elim _ _)⟩
  let p : PrimeSpectrum A := e.hom y
  have : IsLocalRing A := IsLocalRing.of_unique_max_ideal
    ⟨p.asIdeal, p.isPrime.isMaximal', fun I hI ↦
      congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (⟨I, hI.isPrime⟩ : PrimeSpectrum A) p)⟩
  let r : Spec (.of (ResidueField A)) ⟶ Spec A :=
    Spec.map (CommRingCat.ofHom (_root_.IsLocalRing.residue A))
  obtain ⟨b, hb⟩ := exists_lift_of_field_point f h (r ≫ e.inv)
  let s : Spec (.of (ResidueField A)) ⟶ pullback f e.inv := pullback.lift b r hb
  obtain ⟨t, ht, _⟩ := HenselianEtale.exists_section_of_etale_of_artinian
    (pullback.snd f e.inv) s (pullback.lift_snd b r hb)
  refine ⟨e.hom ≫ t ≫ pullback.fst f e.inv, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc t, ht]
  simp

/-- Any étale morphism with a rational point over each point of a locally
Artinian base admits a section over the entire base. -/
theorem exists_section_of_etale_of_isLocallyArtinian {X Y : Scheme.{u}}
    [IsLocallyArtinian Y] (f : X ⟶ Y) [Etale f]
    (h : ∀ y : Y, ∃ s : Spec (Y.residueField y) ⟶ X,
      s ≫ f = Y.fromSpecResidueField y) :
    ∃ t : Y ⟶ X, t ≫ f = 𝟙 Y := by
  let U (y : Y) : Y.Opens := ⟨{y}, isOpen_discrete _⟩
  let C : Y.OpenCover := Y.openCoverOfIsOpenCover U (.mk (by ext; simp [U]))
  have hu (y : Y) : Subsingleton (U y) := inferInstanceAs (Subsingleton ({y} : Set Y))
  have hlocal (y : Y) : ∃ t : (U y).toScheme ⟶ X, t ≫ f = (U y).ι := by
    have hp : ∀ z : (U y).toScheme, ∃ s : Spec ((U y).toScheme.residueField z) ⟶
        pullback f (U y).ι, s ≫ pullback.snd f (U y).ι =
          (U y).toScheme.fromSpecResidueField z := by
      intro z
      obtain ⟨b, hb⟩ := exists_lift_of_field_point f h
        ((U y).toScheme.fromSpecResidueField z ≫ (U y).ι)
      exact ⟨pullback.lift b ((U y).toScheme.fromSpecResidueField z) hb, pullback.lift_snd _ _ _⟩
    obtain ⟨t, ht⟩ := exists_section_over_singleton (⟨y, by simp [U]⟩ : U y)
      (pullback.snd f (U y).ι) hp
    refine ⟨t ≫ pullback.fst f (U y).ι, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  change ∀ y : C.I₀, ∃ t : C.X y ⟶ X, t ≫ f = C.f y at hlocal
  choose t ht using hlocal
  have hc : ∀ i j, pullback.fst (C.f i) (C.f j) ≫ t i =
      pullback.snd (C.f i) (C.f j) ≫ t j := by
    intro i j
    by_cases hij : i = j
    · subst j
      have heq : pullback.fst (C.f i) (C.f i) = pullback.snd (C.f i) (C.f i) :=
        (cancel_mono (C.f i)).mp pullback.condition
      rw [heq]
    · have : IsEmpty ↥(pullback (C.f i) (C.f j)) := ⟨fun z ↦ by
        have hz := congrArg (fun k : pullback (C.f i) (C.f j) ⟶ Y ↦ k z)
          (pullback.condition (f := C.f i) (g := C.f j))
        have hi : C.f i (pullback.fst (C.f i) (C.f j) z) = i :=
          (pullback.fst (C.f i) (C.f j) z).property
        have hj : C.f j (pullback.snd (C.f i) (C.f j) z) = j :=
          (pullback.snd (C.f i) (C.f j) z).property
        exact hij (hi.symm.trans (hz.trans hj))⟩
      exact isInitialOfIsEmpty.hom_ext _ _
  refine ⟨C.glueMorphisms t hc, C.hom_ext _ _ fun i ↦ ?_⟩
  rw [← Category.assoc, C.ι_glueMorphisms, Category.comp_id]
  exact ht i

/-- Over an arbitrary commutative Artinian ring, an arbitrary étale scheme with
a rational lift of every residue-field point admits a whole-base section. -/
theorem exists_section_of_etale_of_artinian {R : Type u} [CommRing R]
    [IsArtinianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Etale f]
    (h : ∀ y : Spec (.of R), ∃ s : Spec ((Spec (.of R)).residueField y) ⟶ X,
      s ≫ f = (Spec (.of R)).fromSpecResidueField y) :
    ∃ t : Spec (.of R) ⟶ X, t ≫ f = 𝟙 _ :=
  exists_section_of_etale_of_isLocallyArtinian f h

end AlgebraicGeometry.Scheme.Hom.ArtinianEtale
