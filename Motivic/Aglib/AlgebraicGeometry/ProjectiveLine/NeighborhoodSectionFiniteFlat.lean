module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.NeighborhoodSectionOpen
/-! # Whole zero schemes on the literal Serre open -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
variable (r : R)

/-- All whole and retained zero properties are preserved by the canonical equality of opens. -/
def NeighborhoodOpenSectionFiniteFlat
    (U : (neighborhoodGraphAmbient R V).Opens) (hU : U = neighborhoodCompactOpen R V r)
    (L : LineBundle U.toScheme)
    (a : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶ L.val) : Prop :=
  let q := ((neighborhoodGraphAmbient R V).isoOfEq hU).hom ≫
    neighborhoodRestrictedProjection R V r
  let j := neighborhoodRetainedInclusion R V ∣_ U
  let t := sectionDualFunctional _ L a
  IsFinite (Scheme.Modules.Hom.zeroInclusion t ≫ q) ∧
    Flat (Scheme.Modules.Hom.zeroInclusion t ≫ q) ∧
    Set.range (Scheme.Modules.Hom.zeroInclusion t) ⊆ Set.range j ∧
    IsFinite (Scheme.Modules.Hom.zeroInclusion (Scheme.Modules.Hom.pullbackToUnit t j) ≫ j ≫ q) ∧
    Mono (Scheme.Modules.Hom.pullbackToUnit t j) ∧
    Flat (Scheme.Modules.Hom.zeroInclusion (Scheme.Modules.Hom.pullbackToUnit t j) ≫ j ≫ q)

theorem neighborhoodOpenSection_finite_flat
    (U : (neighborhoodGraphAmbient R V).Opens) (hU : U = neighborhoodCompactOpen R V r)
    (L : LineBundle U.toScheme)
    (a : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap (neighborhoodGraphBoundaryMap R V hV ∣_ U) a)] :
    NeighborhoodOpenSectionFiniteFlat R V r U hU L a := by
  subst U
  simpa only [NeighborhoodOpenSectionFiniteFlat, Scheme.isoOfEq_rfl, Iso.refl_hom,
    Category.id_comp] using neighborhoodSection_finite_mono_flat R V hV r L a

/-- Literal restriction of a line bundle, matching the original open-section maps. -/
def neighborhoodRestrictLineBundle (L : LineBundle (neighborhoodGraphAmbient R V))
    (U : (neighborhoodGraphAmbient R V).Opens) : LineBundle U.toScheme :=
  ⟨(restrictFunctor U.ι).obj L.val, isLocallyRankOne_of_iso _
    ((restrictFunctorIsoPullback U.ι).symm.app L.val)
      (pullback_locallyRankOne U.ι L.val L.property)⟩

/-- The original numerator coefficient line. -/
def neighborhoodNumeratorLine (n : ℕ) : LineBundle (neighborhoodGraphAmbient R V) :=
  tensorLineBundle _ (pullbackLineBundle (neighborhoodProjectiveIso R V).hom
    (ProjectiveSpace.twistingLineBundle Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)) (n : ℤ)))
      (neighborhoodGraphDivisor R V)

/-- The original denominator coefficient line, with the actual unit module. -/
def neighborhoodDenominatorLine (n : ℕ) : LineBundle (neighborhoodGraphAmbient R V) :=
  tensorLineBundle _ (pullbackLineBundle (neighborhoodProjectiveIso R V).hom
    (ProjectiveSpace.twistingLineBundle Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)) (n : ℤ)))
    ⟨SheafOfModules.unit (neighborhoodGraphAmbient R V).ringCatSheaf,
      isLocallyRankOne_of_iso _
        (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
          SheafOfModules.unit (neighborhoodGraphAmbient R V).ringCatSheaf))
        (trivialLineBundle (neighborhoodGraphAmbient R V)).property⟩
end AlgebraicGeometry.RelativeProjectiveLine
