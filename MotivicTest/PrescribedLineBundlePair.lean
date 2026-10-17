/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.PrescribedLineBundlePair

/-! # Direct finite-boundary generating section consumer -/
@[expose] public section
noncomputable section
set_option linter.hashCommand false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.CoherentGraph
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
example
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
        ((Modules.pushforward k).map (boundaryRestriction z L O)).app V b = σ :=
  exists_prescribed_boundary_section_pair R ι n e k z M hM eB s

example
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C Z : Scheme.{u}} [IsLocallyNoetherian C]
    (k : C ⟶ ProjectiveSpace R ι) [IsClosedImmersion k]
    (z : Z ⟶ C) [IsClosedImmersion z]
    [IsFinite ((z ≫ k) ≫ toSpec R ι)]
    (L₀ : Modules.Invertible.LineBundle C)
    (eB : (Modules.pullback z).obj L₀.val ≅ SheafOfModules.unit Z.ringCatSheaf)
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
      ∃ a : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj L₀.val), V),
      ∃ b : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj O), V),
        ((Modules.pushforward k).map (boundaryRestriction z L L₀.val)).app V a =
          ((Modules.pushforward k).map ((Modules.pushforward z).map
            ((moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).map
              ((pullbackUnitIso z).hom ≫ eB.inv)))).app V σ ∧
        ((Modules.pushforward k).map (boundaryRestriction z L O)).app V b = σ := by
  let := Modules.Invertible.finiteLocallyFree_of_isLocallyRankOne L₀.val L₀.property
  exact exists_prescribed_boundary_section_pair R ι n e k z L₀.val
    (coherent_of_finiteLocallyFree _) eB s

#print axioms exists_prescribed_boundary_section_pair
