/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Sections.FiniteGraphSections

/-! # Direct finite-boundary generating section consumer -/
@[expose] public section
noncomputable section
set_option linter.hashCommand false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.CoherentGraph
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
example
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C U Z : Scheme.{u}} [IsNoetherian C] [IsLocallyNoetherian U]
    (k : C ⟶ ProjectiveSpace R ι) [IsClosedImmersion k]
    (j : U ⟶ C) [IsOpenImmersion j] (i : Z ⟶ U) [IsClosedImmersion (i ≫ j)]
    [IsFinite (((i ≫ j) ≫ k) ≫ toSpec R ι)]
    (h : Γ(U, ⊤)) (s : Spec (CommRingCat.of R)) :
    let O := SheafOfModules.unit C.ringCatSheaf
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r;
      let L := (Modules.pullback k).obj (ProjectiveSpace.twistingSheaf R ι (d : ℤ))
      let Q := (moduleTensorLeftFunctor Z ((Modules.pullback (i ≫ j)).obj L)).obj
        ((Modules.pullback (i ≫ j)).obj O)
      let W := (((i ≫ j) ≫ k) ≫ toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
      ∃ eQ : Q.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf,
      let σ := (openUnitSectionsIso W Q eQ).inv (1 : Γ(W.toScheme, ⊤))
      ∃ s₀ s₁ : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj O), V),
        ((Modules.pushforward k).map (boundaryRestriction (i ≫ j) L O)).app V s₀ = σ ∧
        ((Modules.pushforward k).map (boundaryRestriction (i ≫ j) L O)).app V s₁ =
          (((Modules.pushforward k).map ((Modules.pushforward (i ≫ j)).map
            ((moduleTensorLeftFunctor Z ((Modules.pullback (i ≫ j)).obj L)).map
              (boundaryScalar j i h)))).app V σ) ∧
        (openSectionRestriction k j ((moduleTensorLeftFunctor C L).obj O)).app V s₁ =
          (((Modules.pushforward k).map ((Modules.pushforward j).map
            (openTwistScalar j L h))).app V
              ((openSectionRestriction k j ((moduleTensorLeftFunctor C L).obj O)).app V s₀)) :=
  exists_finiteBoundary_numerator_denominator R ι n e k j i h s

#print axioms exists_finiteBoundary_numerator_denominator
#print axioms exists_principal_boundaryCoefficient_unitIso
#print axioms AlgebraicGeometry.Scheme.Cohomology.cohomology_restrict_principal_subsingleton
