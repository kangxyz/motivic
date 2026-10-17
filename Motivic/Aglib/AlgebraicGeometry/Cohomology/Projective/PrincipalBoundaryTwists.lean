/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteBoundaryTwists

/-! # Principal neighborhoods trivializing all boundary twists -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- One principal base neighborhood trivializes every positive boundary twist. -/
theorem exists_principal_positiveTwist_unitIso
    (R : Type u) [CommRing R] (ι : Type u)
    {Z : Scheme.{u}} (g : Z ⟶ ProjectiveSpace R ι)
    [IsFinite (g ≫ toSpec R ι)] (s : Spec (CommRingCat.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      Nonempty ((n : ℕ) →
        (Modules.pullback (((g ≫ toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι ≫ g)).obj
          (twistingSheaf R ι (n : ℤ)) ≅
            SheafOfModules.unit
              ((g ≫ toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme.ringCatSheaf) := by
  let f := g ≫ toSpec R ι
  let L := Modules.Invertible.pullbackLineBundle g (twistingLineBundle R ι 1)
  obtain ⟨V, hs, ⟨eV⟩⟩ := Modules.Invertible.exists_base_open_unitIso_of_isFinite f s L
  obtain ⟨_, ⟨_, ⟨r : R, rfl⟩, rfl⟩, hsr, hrV⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hs V.isOpen
  let W := f ⁻¹ᵁ PrimeSpectrum.basicOpen r
  have hWV : W ≤ f ⁻¹ᵁ V := fun x hx => hrV hx
  let eW := Modules.Invertible.restrictUnitIsoOfLE L.val hWV eV
  let e₁ : (Modules.pullback (W.ι ≫ g)).obj (twistingSheaf R ι 1) ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
    (Modules.pullbackComp W.ι g).symm.app (twistingSheaf R ι 1) ≪≫
      (restrictFunctorIsoPullback W.ι).symm.app
        ((Modules.pullback g).obj (twistingSheaf R ι 1)) ≪≫ eW
  exact ⟨r, hsr, ⟨positiveTwistUnitIso R ι (W.ι ≫ g) e₁⟩⟩

end AlgebraicGeometry.Scheme.CoherentGraph
