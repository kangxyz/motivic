/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteMapSectionLifting

/-! # Two independently prescribed boundary-unit lifts on the unchanged affine base

The two full-boundary trivializations may differ. A common Serre bound lifts their exact
prescribed values on the same positive twist. This constructs the numerator/denominator
sections needed for the correcting pencil directly, without assuming a rational function
or shrinking the affine base.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- Actual global sections with two independently specified full-boundary unit values.
The base is not shrunk: both equalities are at the original top open. -/
theorem finiteMap_exists_global_boundary_unit_pair
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C Z : Scheme.{u}} [IsLocallyNoetherian C]
    (k : C ⟶ ProjectiveSpace R ι) [IsFinite k]
    (z : Z ⟶ C) [IsClosedImmersion z]
    (M N : C.Modules) (hM : affineLocallyFiniteType C M) (hN : affineLocallyFiniteType C N)
    (eM : (Modules.pullback z).obj M ≅ SheafOfModules.unit Z.ringCatSheaf)
    (eN : (Modules.pullback z).obj N ≅ SheafOfModules.unit Z.ringCatSheaf) :
    let O := SheafOfModules.unit C.ringCatSheaf
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let L := (Modules.pullback k).obj (twistingSheaf R ι (d : ℤ))
      let T := moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)
      ∀ σ : Γ((Modules.pushforward k).obj ((Modules.pushforward z).obj
          (T.obj ((Modules.pullback z).obj O))), ⊤),
      ∃ a : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj M), ⊤),
      ∃ b : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj N), ⊤),
        ((Modules.pushforward k).map (boundaryRestriction z L M)).app ⊤ a =
          ((Modules.pushforward k).map ((Modules.pushforward z).map
            (T.map ((pullbackUnitIso z).hom ≫ eM.inv)))).app ⊤ σ ∧
        ((Modules.pushforward k).map (boundaryRestriction z L N)).app ⊤ b =
          ((Modules.pushforward k).map ((Modules.pushforward z).map
            (T.map ((pullbackUnitIso z).hom ≫ eN.inv)))).app ⊤ σ := by
  dsimp only
  obtain ⟨BM, hBM⟩ := finite_boundaryRestriction_eventually_principal_app_surjective
    R ι n e k z M hM
  obtain ⟨BN, hBN⟩ := finite_boundaryRestriction_eventually_principal_app_surjective
    R ι n e k z N hN
  refine ⟨max BM BN, fun d hd σ => ?_⟩
  have hA := hBM (d : ℤ) (Int.ofNat_le.mpr ((le_max_left BM BN).trans hd)) (1 : R)
  have hB := hBN (d : ℤ) (Int.ofNat_le.mpr ((le_max_right BM BN).trans hd)) (1 : R)
  change Function.Surjective (((Modules.pushforward k).map
    (boundaryRestriction z ((Modules.pullback k).obj (twistingSheaf R ι (d : ℤ))) M)).app
      ((toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (1 : R))) at hA
  change Function.Surjective (((Modules.pushforward k).map
    (boundaryRestriction z ((Modules.pullback k).obj (twistingSheaf R ι (d : ℤ))) N)).app
      ((toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (1 : R))) at hB
  have htop : (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (1 : R) = ⊤ := by
    rw [PrimeSpectrum.basicOpen_one, Scheme.Hom.preimage_top]
  rw [htop] at hA hB
  obtain ⟨a, ha⟩ := hA (((Modules.pushforward k).map ((Modules.pushforward z).map
    ((moduleTensorLeftFunctor Z ((Modules.pullback z).obj
      ((Modules.pullback k).obj (twistingSheaf R ι (d : ℤ))))).map
        ((pullbackUnitIso z).hom ≫ eM.inv)))).app ⊤ σ)
  obtain ⟨b, hb⟩ := hB (((Modules.pushforward k).map ((Modules.pushforward z).map
    ((moduleTensorLeftFunctor Z ((Modules.pullback z).obj
      ((Modules.pullback k).obj (twistingSheaf R ι (d : ℤ))))).map
        ((pullbackUnitIso z).hom ≫ eN.inv)))).app ⊤ σ)
  exact ⟨a, b, ha, hb⟩

end AlgebraicGeometry.Scheme.CoherentGraph
