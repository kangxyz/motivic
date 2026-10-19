/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Sections.FiniteGraphSections

/-! # Actual sections representing a prescribed boundary-trivialized line bundle

The boundary is the entire original closed scheme. Its generating positive-twist
section is constructed on one principal base neighborhood. The two lifts use the
maximum of two original Serre bounds. No graph or denominator ideal is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- Actual twisted sections with the prescribed full-boundary trivialization.
The coefficient module can be any coherent module trivialized on the boundary;
in particular this applies to the diagonal line bundle. -/
theorem exists_prescribed_boundary_section_pair
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C Z : Scheme.{u}} [IsLocallyNoetherian C]
    (k : C ⟶ ProjectiveSpace R ι) [IsClosedImmersion k]
    (z : Z ⟶ C) [IsClosedImmersion z]
    [IsFinite ((z ≫ k) ≫ toSpec R ι)]
    (M : C.Modules) (hM : affineLocallyFiniteType C M)
    (eB : (Modules.pullback z).obj M ≅ SheafOfModules.unit Z.ringCatSheaf)
    (s : Spec (CommRingCat.of R)) :
    let O := SheafOfModules.unit C.ringCatSheaf
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
      let L := (Modules.pullback k).obj (twistingSheaf R ι (d : ℤ))
      let Q := (moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).obj
        ((Modules.pullback z).obj O)
      let W := ((z ≫ k) ≫ toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
      ∃ eQ : Q.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf,
      let σ := (openUnitSectionsIso W Q eQ).inv (1 : Γ(W.toScheme, ⊤))
      ∃ a : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj M), V),
      ∃ b : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj O), V),
        ((Modules.pushforward k).map (boundaryRestriction z L M)).app V a =
          ((Modules.pushforward k).map ((Modules.pushforward z).map
            ((moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).map
              ((pullbackUnitIso z).hom ≫ eB.inv)))).app V σ ∧
        ((Modules.pushforward k).map (boundaryRestriction z L O)).app V b = σ := by
  let O := SheafOfModules.unit C.ringCatSheaf
  have hO : affineLocallyFiniteType C O := by
    let eO : SheafOfModules.free (R := C.ringCatSheaf) PUnit ≅ O := coproductUniqueIso _
    let := finiteLocallyFree_of_iso eO
    exact coherent_of_finiteLocallyFree _
  obtain ⟨r, hr, ⟨eQ⟩⟩ := exists_principal_boundaryCoefficient_unitIso R ι k z s
  obtain ⟨BM, hBM⟩ := embedded_boundaryRestriction_eventually_principal_app_surjective
    R ι n e k z M hM
  obtain ⟨BO, hBO⟩ := embedded_boundaryRestriction_eventually_principal_app_surjective
    R ι n e k z O hO
  refine ⟨r, hr, max BM BO, fun d hd => ?_⟩
  refine ⟨eQ d, ?_⟩
  let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
  let L := (Modules.pullback k).obj (twistingSheaf R ι (d : ℤ))
  let W := ((z ≫ k) ≫ toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
  let σ := (openUnitSectionsIso W _ (eQ d)).inv (1 : Γ(W.toScheme, ⊤))
  let τ := ((Modules.pushforward k).map ((Modules.pushforward z).map
    ((moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).map
      ((pullbackUnitIso z).hom ≫ eB.inv)))).app V σ
  obtain ⟨a, ha⟩ := hBM (d : ℤ) (Int.ofNat_le.mpr ((le_max_left BM BO).trans hd)) r τ
  obtain ⟨b, hb⟩ := hBO (d : ℤ) (Int.ofNat_le.mpr ((le_max_right BM BO).trans hd)) r σ
  exact ⟨a, b, ha, hb⟩

end AlgebraicGeometry.Scheme.CoherentGraph
