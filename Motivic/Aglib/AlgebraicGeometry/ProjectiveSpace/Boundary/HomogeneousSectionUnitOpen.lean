/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.HomogeneousSections
public import Aglib.AlgebraicGeometry.Cohomology.Projective.GlobalSections.Polynomial

/-! # The actual unit open of a homogeneous twist section

The unit open is formed from the actual section's coefficients in the native
coordinate frames. It is the homogeneous basic open, hence affine in positive
degree, with no shrinking of the coefficient or parameter scheme.


Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.HomogeneousSectionUnitOpen`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.TwistSectionBoundaryUnitOpen`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MvPolynomial HomogeneousLocalization
open AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
namespace AlgebraicGeometry.ProjectiveSpace
variable (R : Type u) [CommRing R] (ι : Type u)

/-- The literal coefficient of the polynomial section has the expected unit open
inside each original standard coordinate chart. -/
theorem basicOpen_homogeneousChartSection (n : ℕ) (hn : 0 < n)
    (p : homogeneousSubmodule ι R n) (i : ι) :
    (ProjectiveSpace R ι).basicOpen (homogeneousChartSection R ι n p i) =
      coordinateOpen R ι i ⊓ Proj.basicOpen (homogeneousSubmodule ι R) p.val := by
  let U := coordinateOpen R ι i
  let a := homogeneousChartFraction R ι n p i
  let e := Proj.basicOpenIsoSpec (homogeneousSubmodule ι R) (X i)
    (isHomogeneous_X R i) Nat.zero_lt_one
  let v := Proj.awayι (homogeneousSubmodule ι R) (X i)
    (isHomogeneous_X R i) Nat.zero_lt_one
  have hchart : U.ι ⁻¹ᵁ (ProjectiveSpace R ι).basicOpen
      (homogeneousChartSection R ι n p i) =
      e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen a := by
    change U.ι ⁻¹ᵁ (ProjectiveSpace R ι).basicOpen
      (Proj.awayToSection _ _ a) =
      (U.toSpecΓ ≫ Spec.map (Proj.awayToSection _ _)) ⁻¹ᵁ PrimeSpectrum.basicOpen a
    rw [Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen]
    exact (Scheme.Opens.toSpecΓ_preimage_basicOpen U _).symm
  have hscalar : v ⁻¹ᵁ (ProjectiveSpace R ι).basicOpen
      (homogeneousChartSection R ι n p i) = PrimeSpectrum.basicOpen a := by
    change (e.inv ≫ U.ι) ⁻¹ᵁ _ = _
    rw [Scheme.Hom.comp_preimage, hchart, ← Scheme.Hom.comp_preimage]
    simp
  have hpoly : v ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule ι R) p.val =
      PrimeSpectrum.basicOpen a := by
    have h := Proj.awayι_preimage_basicOpen (homogeneousSubmodule ι R)
      (isHomogeneous_X R i) Nat.zero_lt_one p.property hn
    simpa only [v, a, Away.isLocalizationElem, pow_one, homogeneousChartFraction] using h
  have heq := congrArg (fun V => v ''ᵁ V) (hscalar.trans hpoly.symm)
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Hom.image_preimage_eq_opensRange_inf,
    Proj.opensRange_awayι] at heq
  exact (inf_eq_right.mpr (Scheme.basicOpen_le _ _)).symm.trans heq

/-- The unit open of the actual twist section, expressed in its native frames. -/
def twistSectionUnitOpen (n : ℕ)
    (s : Γ(twistingSheaf R ι (n : ℤ), ⊤)) : (ProjectiveSpace R ι).Opens :=
  ⨆ i : ι, (ProjectiveSpace R ι).basicOpen
    (twistingSectionsEquiv R ι (n : ℤ) i le_rfl
      ((twistingSheaf R ι (n : ℤ)).val.map (homOfLE le_top).op s))

/-- No replacement section occurs: the native homogeneous section's unit locus
is precisely its original homogeneous basic open. -/
theorem twistSectionUnitOpen_homogeneousSection (n : ℕ) (hn : 0 < n)
    (p : homogeneousSubmodule ι R n) :
    twistSectionUnitOpen R ι n (homogeneousSection R ι n p) =
      Proj.basicOpen (homogeneousSubmodule ι R) p.val := by
  simp only [twistSectionUnitOpen, homogeneousSection_local,
    basicOpen_homogeneousChartSection R ι n hn]
  rw [← iSup_inf_eq, iSup_coordinateOpen_eq_top, top_inf_eq]

/-- Positive twist sections on projective space have affine unit opens. -/
theorem isAffineOpen_twistSectionUnitOpen [Finite ι] (j : ι)
    (n : ℕ) (hn : 0 < n) (s : Γ(twistingSheaf R ι (n : ℤ), ⊤)) :
    IsAffineOpen (twistSectionUnitOpen R ι n s) := by
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨p, rfl⟩ := (Scheme.Cohomology.homogeneousSectionLinearEquiv R ι j n).surjective s
  rw [Scheme.Cohomology.homogeneousSectionLinearEquiv_apply,
    twistSectionUnitOpen_homogeneousSection R ι n hn]
  exact Proj.isAffineOpen_basicOpen _ _ p.property hn

end AlgebraicGeometry.ProjectiveSpace
