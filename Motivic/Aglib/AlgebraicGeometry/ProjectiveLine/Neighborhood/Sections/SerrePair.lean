module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.RelativeBoundaryTwist
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Sections.GlobalUnitPair
/-! # Actual prescribed graph sections over a common original base neighborhood -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.QuasiCoherent
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)

/-- The principal open in the section-ring projective line induced by the base element `r`. -/
abbrev neighborhoodSerreOpen (r : R) :=
  (ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2))) ⁻¹ᵁ
    PrimeSpectrum.basicOpen (Scheme.ConstantCurve.coefficientMap (neighborhoodAffineBase R V) r)

lemma neighborhoodGraphBoundary_base :
    neighborhoodGraphBoundaryMap R V hV ≫ (neighborhoodProjectiveIso R V).hom ≫
      ProjectiveSpace.toSpec Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom
          (Scheme.ConstantCurve.coefficientMap (neighborhoodAffineBase R V))) =
    neighborhoodGraphBoundaryToOriginal R V hV ≫ fullBoundaryStructure R V := by
  simp only [Scheme.ConstantCurve.map_coefficientMap, neighborhoodAffineBase,
    neighborhoodProjectiveIso_toSpec_assoc, Category.assoc, Iso.hom_inv_id_assoc]
  change neighborhoodGraphBoundaryMap R V hV ≫ pullback.fst _ _ ≫
      neighborhoodProjection R V = _
  rw [pullback.condition]
  exact neighborhoodGraphBoundaryToOriginal_fac_assoc R V hV (ProjectiveSpace.toSpec R _)

lemma neighborhoodSerreOpen_boundary (r : R) :
    (neighborhoodGraphBoundaryMap R V hV) ⁻¹ᵁ
      ((neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r) =
    neighborhoodGraphBoundaryOpen R V hV r := by
  have h := congrArg (fun f => f ⁻¹ᵁ PrimeSpectrum.basicOpen r)
    (neighborhoodGraphBoundary_base R V hV)
  have hb : Spec.map (CommRingCat.ofHom
      (Scheme.ConstantCurve.coefficientMap (neighborhoodAffineBase R V))) ⁻¹ᵁ
        PrimeSpectrum.basicOpen r = PrimeSpectrum.basicOpen
          (Scheme.ConstantCurve.coefficientMap (neighborhoodAffineBase R V) r) := by
    ext x
    rfl
  simpa only [Scheme.Hom.comp_preimage, hb, neighborhoodSerreOpen,
    neighborhoodGraphBoundaryOpen] using h

/-- The pulled-back Serre twist tensored with the pulled-back ambient unit sheaf on the graph
boundary. -/
abbrev neighborhoodBoundaryCoefficient (n : ℕ) :=
  (moduleTensorLeftFunctor (neighborhoodGraphBoundarySource R V hV)
    ((Scheme.Modules.pullback (neighborhoodGraphBoundaryMap R V hV)).obj
      (neighborhoodSerreTwist R V n))).obj
    ((Scheme.Modules.pullback (neighborhoodGraphBoundaryMap R V hV)).obj
      (SheafOfModules.unit (neighborhoodGraphAmbient R V).ringCatSheaf))

/-- Trivialize the boundary coefficient module over the principal open using the given original
frame. -/
def neighborhoodBoundaryCoefficientIso (r : R) (n : ℕ)
    (e : (Scheme.Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
        fullNeighborhoodBoundaryMap R V)).obj
      (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
        SheafOfModules.unit (fullBoundaryPrincipalOpen R V r).toScheme.ringCatSheaf) :
    (neighborhoodBoundaryCoefficient R V hV n).restrict
      (neighborhoodGraphBoundaryOpen R V hV r).ι ≅
        SheafOfModules.unit (neighborhoodGraphBoundaryOpen R V hV r).toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctor (neighborhoodGraphBoundaryOpen R V hV r).ι).mapIso
    ((moduleTensorLeftFunctor (neighborhoodGraphBoundarySource R V hV) _).mapIso
      (pullbackUnitIso (neighborhoodGraphBoundaryMap R V hV)) ≪≫
      (SheafOfModulesOfCommRing.tensorRightUnitIso
        (neighborhoodGraphBoundarySource R V hV).sheaf).app _) ≪≫
    neighborhoodGraphRelativeBoundaryTwistIso R V hV r n e

/-- The boundary coefficient section corresponding to one in the given boundary frame. -/
def neighborhoodBoundaryUnitSection (r : R) (n : ℕ)
    (e : (Scheme.Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
        fullNeighborhoodBoundaryMap R V)).obj
      (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
        SheafOfModules.unit (fullBoundaryPrincipalOpen R V r).toScheme.ringCatSheaf) :
    Γ(neighborhoodBoundaryCoefficient R V hV n,
      (neighborhoodGraphBoundaryMap R V hV) ⁻¹ᵁ
        ((neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r)) :=
  ((neighborhoodBoundaryCoefficient R V hV n).presheaf.mapIso
    (eqToIso (neighborhoodSerreOpen_boundary R V hV r)).op).hom
      ((Scheme.CoherentGraph.openUnitSectionsIso (neighborhoodGraphBoundaryOpen R V hV r)
        (neighborhoodBoundaryCoefficient R V hV n)
        (neighborhoodBoundaryCoefficientIso R V hV r n e)).inv
          (1 : Γ((neighborhoodGraphBoundaryOpen R V hV r).toScheme, ⊤)))

attribute [local instance] neighborhoodGraphBoundary_closed

/-- Serre constructs the actual two graph sections over every common original base
shrink carrying a boundary frame. The bound does not shrink V independently. -/
theorem exists_neighborhoodSerreSectionPair [IsNoetherianRing R] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ r : R,
      ∀ e : (Scheme.Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
          fullNeighborhoodBoundaryMap R V)).obj
        (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
          SheafOfModules.unit (fullBoundaryPrincipalOpen R V r).toScheme.ringCatSheaf,
      let C := neighborhoodGraphAmbient R V
      let k := (neighborhoodProjectiveIso R V).hom
      let z := neighborhoodGraphBoundaryMap R V hV
      let M := (neighborhoodGraphDivisor R V).val
      let O := SheafOfModules.unit C.ringCatSheaf
      let L := neighborhoodSerreTwist R V n
      let T := moduleTensorLeftFunctor (neighborhoodGraphBoundarySource R V hV)
        ((Scheme.Modules.pullback z).obj L)
      let σ' := neighborhoodBoundaryUnitSection R V hV r n e
      ∃ a : Γ((Scheme.Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj M),
          neighborhoodSerreOpen R V r),
      ∃ b : Γ((Scheme.Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj O),
          neighborhoodSerreOpen R V r),
        ((Scheme.Modules.pushforward k).map (Scheme.CoherentGraph.boundaryRestriction z L M)).app
          (neighborhoodSerreOpen R V r) a =
            ((Scheme.Modules.pushforward k).map ((Scheme.Modules.pushforward z).map
              (T.map ((pullbackUnitIso z).hom ≫ (neighborhoodGraphBoundaryIso R V hV).inv)))).app
                (neighborhoodSerreOpen R V r) σ' ∧
        ((Scheme.Modules.pushforward k).map (Scheme.CoherentGraph.boundaryRestriction z L O)).app
          (neighborhoodSerreOpen R V r) b = σ' := by
  have : IsLocallyNoetherian V.toScheme := inferInstance
  have : IsNoetherianRing Γ(V.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V.toScheme⟩
  let k := (neighborhoodProjectiveIso R V).hom
  have : IsLocallyNoetherian (neighborhoodGraphAmbient R V) :=
    LocallyOfFiniteType.isLocallyNoetherian k
  have := neighborhoodGraphBoundary_closed R V hV
  let M := (neighborhoodGraphDivisor R V).val
  let O := SheafOfModules.unit (neighborhoodGraphAmbient R V).ringCatSheaf
  have := Invertible.finiteLocallyFree_of_isLocallyRankOne M
    (neighborhoodGraphDivisor R V).property
  have hO : affineLocallyFiniteType (neighborhoodGraphAmbient R V) O := by
    let eO : SheafOfModules.free (R := (neighborhoodGraphAmbient R V).ringCatSheaf) PUnit ≅ O :=
      coproductUniqueIso _
    have := finiteLocallyFree_of_iso eO
    exact coherent_of_finiteLocallyFree _
  obtain ⟨NM, hM⟩ :=
    Scheme.CoherentGraph.finite_boundaryRestriction_eventually_principal_app_surjective
    Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)) 1 Equiv.ulift k
    (neighborhoodGraphBoundaryMap R V hV) M (coherent_of_finiteLocallyFree _)
  obtain ⟨NO, hO⟩ :=
    Scheme.CoherentGraph.finite_boundaryRestriction_eventually_principal_app_surjective
    Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)) 1 Equiv.ulift k
    (neighborhoodGraphBoundaryMap R V hV) O hO
  refine ⟨max NM NO, fun n hn r e => ?_⟩
  dsimp only
  have hM' := hM (n : ℤ) (Int.ofNat_le.mpr ((le_max_left NM NO).trans hn))
    (Scheme.ConstantCurve.coefficientMap (neighborhoodAffineBase R V) r)
  have hO' := hO (n : ℤ) (Int.ofNat_le.mpr ((le_max_right NM NO).trans hn))
    (Scheme.ConstantCurve.coefficientMap (neighborhoodAffineBase R V) r)
  let σ := neighborhoodBoundaryUnitSection R V hV r n e
  let τ := ((Scheme.Modules.pushforward k).map ((Scheme.Modules.pushforward
    (neighborhoodGraphBoundaryMap R V hV)).map
      ((moduleTensorLeftFunctor (neighborhoodGraphBoundarySource R V hV)
        ((Scheme.Modules.pullback (neighborhoodGraphBoundaryMap R V hV)).obj
          (neighborhoodSerreTwist R V n))).map
        ((pullbackUnitIso (neighborhoodGraphBoundaryMap R V hV)).hom ≫
          (neighborhoodGraphBoundaryIso R V hV).inv)))).app
            (neighborhoodSerreOpen R V r) σ
  obtain ⟨a, ha⟩ := hM' τ
  obtain ⟨b, hb⟩ := hO' σ
  exact ⟨a, b, ha, hb⟩

end AlgebraicGeometry.RelativeProjectiveLine
