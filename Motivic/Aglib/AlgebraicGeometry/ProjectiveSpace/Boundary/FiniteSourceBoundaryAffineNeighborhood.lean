/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.FiniteSupportImage
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.PeriodicBoundaryAffineNeighborhood
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Twists.PrescribedTransport
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian

/-!
# A full-boundary affine ambient for an original finite projective cover

Only a nonzero element of the original coefficient ring is inverted. The actual
image of the full boundary is framed before Serre lifting; the full finite
inverse image of the resulting target affine open is affine. No parameter open,
reduced boundary, or commutation of image formation with base change is assumed.


Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.FiniteSourceBoundaryAffineNeighborhood`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.SourceTargetBoundaryAffineNeighborhood`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.FiniteSourceGraph`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme Scheme.Modules Scheme.CoherentGraph

universe u
namespace AlgebraicGeometry.ProjectiveSpace

/-- The full original boundary after coefficient localization factors through an
actual affine open of the original finite source after that same localization. -/
theorem exists_affine_full_boundary_coefficient_neighborhood
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C B : Scheme.{u}} (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
    (b : B ⟶ C) [IsFinite ((b ≫ f) ≫ toSpec R ι)] :
    ∃ r : R, r ≠ 0 ∧
      let m := ProjectiveSpace.map (algebraMap R (Localization.Away r)) ι
      let br := pullback.lift (pullback.fst (b ≫ f) m ≫ b)
        (pullback.snd (b ≫ f) m) (by simp [Category.assoc, pullback.condition])
      ∃ W : (pullback f m).Opens, IsAffineOpen W ∧
        ∃ t : pullback (b ≫ f) m ⟶ W.toScheme, t ≫ W.ι = br := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  let g := b ≫ f
  let i := g.imageι
  have : IsFinite (i ≫ toSpec R ι) := Hom.isFinite_image_over_base (toSpec R ι) g
  obtain ⟨r, hr, ⟨er⟩⟩ := exists_principal_positiveTwist_unitIso R ι i
    (genericPoint (Spec (.of R)))
  have hr0 : r ≠ 0 := by
    intro h
    subst r
    simp at hr
  let S := Localization.Away r
  let a := algebraMap R S
  let m := ProjectiveSpace.map a ι
  let V := (i ≫ toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
  let ir : pullback i m ⟶ ProjectiveSpace S ι := pullback.snd i m
  let pr : pullback i m ⟶ g.image := pullback.fst i m
  have hpr : Set.range pr ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (pr ≫ i ≫ toSpec R ι) x ∈ PrimeSpectrum.basicOpen r
    have hc : pr ≫ i ≫ toSpec R ι =
        ir ≫ toSpec S ι ≫ Spec.map (CommRingCat.ofHom a) := by
      rw [← Category.assoc, pullback.condition, Category.assoc, map_toSpec]
    rw [hc]
    change PrimeSpectrum.comap a ((ir ≫ toSpec S ι) x) ∈ PrimeSpectrum.basicOpen r
    exact (PrimeSpectrum.localization_away_comap_range S r).le
      (Set.mem_range_self (f := PrimeSpectrum.comap (algebraMap R S))
        ((ir ≫ toSpec S ι) x))
  let v : pullback i m ⟶ V.toScheme := IsOpenImmersion.lift V.ι pr hpr
  have hv : v ≫ V.ι = pr := IsOpenImmersion.lift_fac V.ι pr hpr
  have hsquare : ir ≫ m = v ≫ (V.ι ≫ i) := by
    rw [← Category.assoc, hv]
    exact (pullback.condition (f := i) (g := m)).symm
  let e1 := prescribedBoundaryRelativeTwistIso R S a ι (V.ι ≫ i) v ir hsquare 1 (er 1)
  obtain ⟨k, hk, s, hsi, hA, hIA⟩ :=
    exists_affine_unitOpen_of_periodic_boundary_frame S ι n e ir 1 (by decide) e1
  let A := twistSectionUnitOpen S ι (1 * k) s
  let q : pullback f m ⟶ ProjectiveSpace S ι := pullback.snd f m
  let W := q ⁻¹ᵁ A
  have hW : IsAffineOpen W := hA.preimage q
  let br : pullback (b ≫ f) m ⟶ pullback f m :=
    pullback.lift (pullback.fst (b ≫ f) m ≫ b) (pullback.snd (b ≫ f) m)
      (by simp [Category.assoc, pullback.condition])
  let bi : pullback (b ≫ f) m ⟶ pullback i m :=
    pullback.lift (pullback.fst (b ≫ f) m ≫ g.toImage)
      (pullback.snd (b ≫ f) m) (by simp [i, g, Category.assoc, pullback.condition])
  have hbr : Set.range br ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (br ≫ q) x ∈ A
    have heq : br ≫ q = bi ≫ ir := by simp [br, q, bi, ir]
    rw [heq]
    exact hIA ⟨bi x, rfl⟩
  refine ⟨r, hr0, W, hW, IsOpenImmersion.lift W.ι br hbr, ?_⟩
  exact IsOpenImmersion.lift_fac W.ι br hbr

end AlgebraicGeometry.ProjectiveSpace
