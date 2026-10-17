module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodSerreSectionPair
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.OpenBoundaryRestrictionPullback
/-! # Constructed relative graph sections as actual unit-domain maps -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)

abbrev neighborhoodFrame (r : R) (n : ℕ) :=
  (Scheme.Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
    fullNeighborhoodBoundaryMap R V)).obj
      (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
        SheafOfModules.unit (fullBoundaryPrincipalOpen R V r).toScheme.ringCatSheaf
abbrev neighborhoodSectionOpen (r : R) :=
  (neighborhoodProjectiveIso R V).hom ⁻¹ᵁ neighborhoodSerreOpen R V r
abbrev neighborhoodNumeratorModule (n : ℕ) :=
  (moduleTensorLeftFunctor (neighborhoodGraphAmbient R V) (neighborhoodSerreTwist R V n)).obj
    (neighborhoodGraphDivisor R V).val
abbrev neighborhoodDenominatorModule (n : ℕ) :=
  (moduleTensorLeftFunctor (neighborhoodGraphAmbient R V) (neighborhoodSerreTwist R V n)).obj
    (SheafOfModules.unit (neighborhoodGraphAmbient R V).ringCatSheaf)

def neighborhoodNumeratorBoundaryMap (n : ℕ) :=
  (moduleTensorLeftFunctor (neighborhoodGraphBoundarySource R V hV)
    ((Scheme.Modules.pullback (neighborhoodGraphBoundaryMap R V hV)).obj
      (neighborhoodSerreTwist R V n))).map
    ((pullbackUnitIso (neighborhoodGraphBoundaryMap R V hV)).hom ≫
      (neighborhoodGraphBoundaryIso R V hV).inv)

instance (n : ℕ) : IsIso (neighborhoodNumeratorBoundaryMap R V hV n) := by
  unfold neighborhoodNumeratorBoundaryMap
  infer_instance

attribute [local instance] neighborhoodGraphBoundary_closed

/-- These are the actual constructed open sections and their original restriction equations. -/
structure NeighborhoodSectionPair (r : R) (n : ℕ) (e : neighborhoodFrame R V r n) where
  numerator : Γ(neighborhoodNumeratorModule R V n, neighborhoodSectionOpen R V r)
  denominator : Γ(neighborhoodDenominatorModule R V n, neighborhoodSectionOpen R V r)
  numerator_value :
    (Scheme.CoherentGraph.boundaryRestriction (neighborhoodGraphBoundaryMap R V hV)
      (neighborhoodSerreTwist R V n) (neighborhoodGraphDivisor R V).val).app
        (neighborhoodSectionOpen R V r) numerator =
    (neighborhoodNumeratorBoundaryMap R V hV n).app
      ((neighborhoodGraphBoundaryMap R V hV) ⁻¹ᵁ neighborhoodSectionOpen R V r)
        (neighborhoodBoundaryUnitSection R V hV r n e)
  denominator_value :
    (Scheme.CoherentGraph.boundaryRestriction (neighborhoodGraphBoundaryMap R V hV)
      (neighborhoodSerreTwist R V n)
      (SheafOfModules.unit (neighborhoodGraphAmbient R V).ringCatSheaf)).app
        (neighborhoodSectionOpen R V r) denominator = neighborhoodBoundaryUnitSection R V hV r n e

/-- Actual Serre sections populate the package; none of its fields is an input hypothesis. -/
theorem exists_neighborhoodSectionPair [IsNoetherianRing R] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ r : R, ∀ e : neighborhoodFrame R V r n,
      Nonempty (NeighborhoodSectionPair R V hV r n e) := by
  obtain ⟨N, hN⟩ := exists_neighborhoodSerreSectionPair R V hV
  refine ⟨N, fun n hn r e => ?_⟩
  obtain ⟨a, b, ha, hb⟩ := hN n hn r e
  exact ⟨⟨a, b, ha, hb⟩⟩

variable {R V hV} {r : R} {n : ℕ} {e : neighborhoodFrame R V r n}

def NeighborhoodSectionPair.numeratorHom (d : NeighborhoodSectionPair R V hV r n e) :=
  openSectionHom (neighborhoodGraphAmbient R V) (neighborhoodSectionOpen R V r)
    (neighborhoodNumeratorModule R V n) d.numerator

def NeighborhoodSectionPair.denominatorHom (d : NeighborhoodSectionPair R V hV r n e) :=
  openSectionHom (neighborhoodGraphAmbient R V) (neighborhoodSectionOpen R V r)
    (neighborhoodDenominatorModule R V n) d.denominator

lemma neighborhoodBoundaryUnitSection_isIso :
    IsIso (openSectionHom (neighborhoodGraphBoundarySource R V hV)
      ((neighborhoodGraphBoundaryMap R V hV) ⁻¹ᵁ neighborhoodSectionOpen R V r)
      (neighborhoodBoundaryCoefficient R V hV n)
      (neighborhoodBoundaryUnitSection R V hV r n e)) := by
  unfold neighborhoodBoundaryUnitSection
  exact Scheme.CoherentGraph.isIso_openSectionHom_unit_boundary_of_eq
    (X := neighborhoodGraphBoundarySource R V hV)
    ((neighborhoodGraphBoundaryMap R V hV) ⁻¹ᵁ neighborhoodSectionOpen R V r)
    (neighborhoodGraphBoundaryOpen R V hV r)
    (neighborhoodSerreOpen_boundary R V hV r)
    (neighborhoodBoundaryCoefficient R V hV n) (neighborhoodBoundaryCoefficientIso R V hV r n e)

lemma NeighborhoodSectionPair.denominatorHom_boundary_isIso
    (d : NeighborhoodSectionPair R V hV r n e) :
    IsIso (pullbackSectionMap
      (neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r) d.denominatorHom) := by
  have := neighborhoodBoundaryUnitSection_isIso (R := R) (V := V) (hV := hV) (e := e)
  exact Scheme.CoherentGraph.isIso_pullback_openSection_of_boundary_value _ _ _ _ _ _
    d.denominator_value

lemma NeighborhoodSectionPair.numeratorHom_boundary_isIso
    (d : NeighborhoodSectionPair R V hV r n e) :
    IsIso (pullbackSectionMap
      (neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r) d.numeratorHom) := by
  have := neighborhoodBoundaryUnitSection_isIso (R := R) (V := V) (hV := hV) (e := e)
  have hunit : IsIso (openSectionHom (neighborhoodGraphBoundarySource R V hV)
      ((neighborhoodGraphBoundaryMap R V hV) ⁻¹ᵁ neighborhoodSectionOpen R V r) _
      ((neighborhoodNumeratorBoundaryMap R V hV n).app _
        (neighborhoodBoundaryUnitSection R V hV r n e))) := by
    rw [← openSectionHom_naturality]
    infer_instance
  exact Scheme.CoherentGraph.isIso_pullback_openSection_of_boundary_value _ _ _ _ _ _
    d.numerator_value
end AlgebraicGeometry.RelativeProjectiveLine
