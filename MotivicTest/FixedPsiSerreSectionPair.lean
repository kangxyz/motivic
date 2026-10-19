module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.FixedOpen.Sections.SerrePair

/-! # Strict consumers of the relative fixed-source psi construction -/
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RelativeProjectiveLine


example (R : Type) [CommRing R] (r : R) :
    fixedPsiSource R r = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) ⊓
      (Scheme.Hom.boundaryLineProjection R ⁻¹ᵁ PrimeSpectrum.basicOpen r) :=
  fixedPsiSource_eq R r

example (R : Type) [CommRing R] (r : R)
    (V : (Spec (.of (Polynomial R))).Opens)
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    IsClosedImmersion (fixedPsiBoundaryMap R r V) :=
  fixedPsiBoundary_closed R r V hV

open Scheme.Modules

example (R : Type) [CommRing R] [IsNoetherianRing R]
    (V : (Spec (.of (Polynomial R))).Opens)
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (r : R)
    (e : (n : ℕ) → (Scheme.Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
        fullNeighborhoodBoundaryMap R V)).obj
      (ProjectiveSpace.twistingSheaf R (ULift (Fin 2)) (n : ℤ)) ≅
        SheafOfModules.unit (fullBoundaryPrincipalOpen R V r).toScheme.ringCatSheaf) :
    let C := fixedPsiAmbient R r
    let W := fixedPsiBoundary R V r
    let zD := fixedPsiBoundaryMap R r V
    let O := SheafOfModules.unit C.ringCatSheaf
    let E := fixedPsiBoundaryUnit R V r
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      let L := fixedPsiSerreTwist R r d
      let T := moduleTensorLeftFunctor W ((Scheme.Modules.pullback zD).obj L)
      ∃ u : SheafOfModules.unit W.ringCatSheaf ⟶ T.obj ((Scheme.Modules.pullback zD).obj O),
      IsIso u ∧
      ∃ n t : O ⟶ (moduleTensorLeftFunctor C L).obj O,
        (pullbackUnitIso zD).inv ≫ (Scheme.Modules.pullback zD).map n ≫
          pullbackTensorMap zD L O =
            u ≫ T.map ((pullbackUnitIso zD).hom ≫ E.hom ≫ (pullbackUnitIso zD).inv) ∧
        (pullbackUnitIso zD).inv ≫ (Scheme.Modules.pullback zD).map t ≫
          pullbackTensorMap zD L O = u ∧
        IsIso ((pullbackUnitIso zD).inv ≫ (Scheme.Modules.pullback zD).map n) ∧
        IsIso ((pullbackUnitIso zD).inv ≫ (Scheme.Modules.pullback zD).map t) :=
  exists_fixedPsiSerreSectionPair R V hV r e
