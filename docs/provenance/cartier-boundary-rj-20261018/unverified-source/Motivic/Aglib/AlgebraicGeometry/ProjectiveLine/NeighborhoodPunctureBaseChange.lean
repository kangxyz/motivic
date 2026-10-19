/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodPunctureIdentification

/-! # Actual coefficient-base change on original punctured neighborhoods -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Polynomial coefficient extension preserves the literal original line projection. -/
@[reassoc] theorem polynomial_scalar_projection :
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ≫
      Scheme.Hom.boundaryLineProjection R =
    Scheme.Hom.boundaryLineProjection S ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [Scheme.Hom.boundaryLineProjection, Scheme.Hom.boundaryLineProjection,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext x
  simp

variable (V : (Spec (.of (Polynomial R))).Opens)

/-- Base change of the actual polynomial open, not an unrelated new neighborhood. -/
abbrev neighborhoodBaseChangeOpen : (Spec (.of (Polynomial S))).Opens :=
  Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ⁻¹ᵁ V

/-- The unchanged original punctured open receives its literal base restriction. -/
def neighborhoodPunctureBaseChangeScheme :
    (commonNeighborhoodSource S (neighborhoodBaseChangeOpen f V) 1).toScheme ⟶
      (commonNeighborhoodSource R V 1).toScheme :=
  IsOpenImmersion.lift (commonNeighborhoodSource R V 1).ι
    ((commonNeighborhoodSource S (neighborhoodBaseChangeOpen f V) 1).ι ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f))) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [commonNeighborhoodSource_one]
    have hx : x.val ∈ neighborhoodBaseChangeOpen f V ⊓
        PrimeSpectrum.basicOpen (Polynomial.X : Polynomial S) :=
      (congrArg (fun O : (Spec (.of (Polynomial S))).Opens => x.val ∈ O)
        (commonNeighborhoodSource_one S (neighborhoodBaseChangeOpen f V))).mp x.property
    refine ⟨hx.1, ?_⟩
    change x.val ∈ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ⁻¹ᵁ
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R)
    rw [SpecMap_preimage_basicOpen]
    change Polynomial.map f (Polynomial.X : Polynomial R) ∉
      (x.val : PrimeSpectrum (Polynomial S)).asIdeal
    simpa only [Polynomial.map_X] using
      (show (Polynomial.X : Polynomial S) ∉
        (x.val : PrimeSpectrum (Polynomial S)).asIdeal from hx.2))

@[reassoc (attr := simp)] theorem neighborhoodPunctureBaseChangeScheme_ι :
    neighborhoodPunctureBaseChangeScheme f V ≫ (commonNeighborhoodSource R V 1).ι =
      (commonNeighborhoodSource S (neighborhoodBaseChangeOpen f V) 1).ι ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) :=
  IsOpenImmersion.lift_fac _ _ _

variable (k : Type u) [Field k] (b : Spec (.of R) ⟶ Spec (.of k)) [Smooth b]
  [Smooth (Spec.map (CommRingCat.ofHom f) ≫ b)]
  [IsAffine V.toScheme] [IsAffine (neighborhoodBaseChangeOpen f V).toScheme]

/-- The base-change restriction is over the same original field structure. -/
def neighborhoodPunctureBaseChange :
    neighborhoodCommonSite k S (Spec.map (CommRingCat.ofHom f) ≫ b)
      (neighborhoodBaseChangeOpen f V) 1 ⟶ neighborhoodCommonSite k R b V 1 :=
  SmoothSite.homMk (neighborhoodPunctureBaseChangeScheme f V) (by
    change neighborhoodPunctureBaseChangeScheme f V ≫
      (((commonNeighborhoodSource R V 1).ι ≫ Scheme.Hom.boundaryLineProjection R) ≫ b) =
      ((commonNeighborhoodSource S (neighborhoodBaseChangeOpen f V) 1).ι ≫
        Scheme.Hom.boundaryLineProjection S) ≫ (Spec.map (CommRingCat.ofHom f) ≫ b)
    simp only [Category.assoc, neighborhoodPunctureBaseChangeScheme_ι_assoc,
      polynomial_scalar_projection_assoc])

end AlgebraicGeometry.RelativeProjectiveLine
