module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.FixedPsiSectionDivisors
/-! # Both actual relative psi sections have whole finite flat zeros -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
  (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
  (r : R)
include hV in
/-- The same original base shrink and all sufficiently positive degrees produce
both exact psi values and their whole finite flat zero factors. -/
theorem exists_fixedPsiFiniteFlatSectionPair
    (e : (n : ℕ) → (Scheme.Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
        fullNeighborhoodBoundaryMap R V)).obj
      (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
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
        FixedPsiSectionFiniteFlat R r V d t := by
  obtain ⟨N, hN⟩ := exists_fixedPsiSerreSectionPair R V hV r e
  refine ⟨N, fun d hd => ?_⟩
  obtain ⟨u, hu, n, t, hn, ht, hIn, hIt⟩ := hN d hd
  have : IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) n) := hIn
  have : IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) t) := hIt
  exact ⟨u, hu, n, t, hn, ht, hIn, hIt,
    fixedPsiSectionDivisor_finite_mono_flat R r V (fixedPsiSectionLine R r d) n,
    fixedPsiSectionDivisor_finite_mono_flat R r V (fixedPsiSectionLine R r d) t⟩
end AlgebraicGeometry.RelativeProjectiveLine
