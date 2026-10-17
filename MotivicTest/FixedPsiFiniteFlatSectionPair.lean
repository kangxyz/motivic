module
import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.FixedPsiFiniteFlatSectionPair
/-! # Strict consumer of whole relative psi finite flat factors -/
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open AlgebraicGeometry.RelativeProjectiveLine

example (R : Type) [CommRing R] [IsNoetherianRing R]
    (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
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
        IsIso ((pullbackUnitIso zD).inv ≫ (Scheme.Modules.pullback zD).map t) ∧
        FixedPsiSectionFiniteFlat R r V d n ∧
        FixedPsiSectionFiniteFlat R r V d t :=
  exists_fixedPsiFiniteFlatSectionPair R V hV r e
