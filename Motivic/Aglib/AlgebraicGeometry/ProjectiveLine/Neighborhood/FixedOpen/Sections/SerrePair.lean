module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.FixedOpen.Boundary.Twist
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Sections.GlobalSectionMaps
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting
/-! # Actual relative psi sections on the fixed punctured source -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  (V : (Spec (.of (Polynomial R))).Opens)
  (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
  (r : R)

include hV in
/-- Both sections are produced on the entire fixed Gm over D(r).  The only frames
are those on the original whole boundary; the Serre bound works for every larger degree. -/
theorem exists_fixedPsiSerreSectionPair
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
        IsIso ((pullbackUnitIso zD).inv ≫ (Scheme.Modules.pullback zD).map t) := by
  have : IsLocallyNoetherian (fixedPsiSource R r).toScheme := inferInstance
  have : IsNoetherianRing Γ((fixedPsiSource R r).toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have := fixedPsiBoundary_closed R r V hV
  let a := (fixedPsiProjectiveIso R r).hom
  have : IsLocallyNoetherian (fixedPsiAmbient R r) :=
    LocallyOfFiniteType.isLocallyNoetherian a
  let O := SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf
  have hO : Invertible.IsLocallyRankOne (fixedPsiAmbient R r) O :=
    Invertible.isLocallyRankOne_of_iso _
      (coproductUniqueIso (fun _ : PUnit.{u + 1} => O))
      (Invertible.trivialLineBundle (fixedPsiAmbient R r)).property
  have := Invertible.finiteLocallyFree_of_isLocallyRankOne O hO
  let zD := fixedPsiBoundaryMap R r V
  obtain ⟨N, hN⟩ := Scheme.CoherentGraph.finiteMap_exists_global_section_map
    Γ((fixedPsiSource R r).toScheme, ⊤) (ULift.{u} (Fin 2)) 1 Equiv.ulift a zD O
    (coherent_of_finiteLocallyFree _)
  refine ⟨N, fun d hd => ?_⟩
  let L := fixedPsiSerreTwist R r d
  let T := moduleTensorLeftFunctor (fixedPsiBoundary R V r)
    ((Scheme.Modules.pullback zD).obj L)
  let Q : T.obj ((Scheme.Modules.pullback zD).obj O) ≅
      SheafOfModules.unit (fixedPsiBoundary R V r).ringCatSheaf :=
    T.mapIso (pullbackUnitIso zD) ≪≫
      (SheafOfModulesOfCommRing.tensorRightUnitIso (fixedPsiBoundary R V r).sheaf).app _ ≪≫
      fixedPsiBoundaryTwistIso R r V d (e d)
  let v := Q.inv ≫ T.map ((pullbackUnitIso zD).hom ≫
    (fixedPsiBoundaryUnit R V r).hom ≫ (pullbackUnitIso zD).inv)
  obtain ⟨n, hn⟩ := hN d hd v
  obtain ⟨t, ht⟩ := hN d hd Q.inv
  let LL := Invertible.pullbackLineBundle a
    (ProjectiveSpace.twistingLineBundle Γ((fixedPsiSource R r).toScheme, ⊤)
      (ULift.{u} (Fin 2)) (d : ℤ))
  exact ⟨Q.inv, inferInstance, n, t, hn, ht,
    Scheme.CoherentGraph.isIso_pullbackSection_of_tensor_eq zD LL O n v hn,
    Scheme.CoherentGraph.isIso_pullbackSection_of_tensor_eq zD LL O t Q.inv ht⟩
end AlgebraicGeometry.RelativeProjectiveLine
