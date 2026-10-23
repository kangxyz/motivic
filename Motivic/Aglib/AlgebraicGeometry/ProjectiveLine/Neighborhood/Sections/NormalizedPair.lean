/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Sections.FiniteFlatPair
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Dual.Restriction
/-! # Actual local diagonal sections in the native restricted dual line -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
private lemma pullbackSectionMap_postIso_isIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N : X.Modules} (s : SheafOfModules.unit X.ringCatSheaf ⟶ M) (e : M ≅ N)
    [IsIso (pullbackSectionMap f s)] : IsIso (pullbackSectionMap f (s ≫ e.hom)) := by
  unfold pullbackSectionMap
  rw [Functor.map_comp, ← Category.assoc]
  change IsIso (pullbackSectionMap f s ≫ (Scheme.Modules.pullback f).map e.hom)
  infer_instance
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
variable (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]
variable (r : R) (n : ℕ)

/-- The nonnegative twisting line bundle pulled back to the graph ambient scheme. -/
def neighborhoodTwistLine : LineBundle (neighborhoodGraphAmbient R V) :=
  pullbackLineBundle (neighborhoodProjectiveIso R V).hom
    (ProjectiveSpace.twistingLineBundle Γ(V.toScheme, ⊤) (ULift.{u} (Fin 2)) (n : ℤ))
/-- The twisting line bundle restricted to the section open. -/
def neighborhoodLocalTwist : LineBundle (neighborhoodSectionOpen R V r).toScheme :=
  restrictLineBundle (neighborhoodSectionOpen R V r).ι (neighborhoodTwistLine R V n)
/-- The graph ideal line bundle restricted to the section open. -/
def neighborhoodLocalIdeal : LineBundle (neighborhoodSectionOpen R V r).toScheme :=
  restrictLineBundle (neighborhoodSectionOpen R V r).ι (neighborhoodGraphLine R V)

/-- Identify the restricted numerator module with the local twist tensored with the dual graph
ideal. -/
def neighborhoodNumeratorNormalizeIso :
    (restrictFunctor (neighborhoodSectionOpen R V r).ι).obj
      (neighborhoodNumeratorModule R V n) ≅
    (tensorLineBundle _ (neighborhoodLocalTwist R V r n)
      (dualLineBundle _ (neighborhoodLocalIdeal R V r))).val :=
  (tensorRestrictionIso (neighborhoodSectionOpen R V r).ι
    (neighborhoodSerreTwist R V n) (neighborhoodGraphDivisor R V).val).symm ≪≫
    tensorSheafIso _ (Iso.refl _)
      (restrictDualIso (neighborhoodSectionOpen R V r).ι (neighborhoodGraphLine R V))

/-- Identify the restricted denominator module with the local twisting line bundle. -/
def neighborhoodDenominatorNormalizeIso :
    (restrictFunctor (neighborhoodSectionOpen R V r).ι).obj
      (neighborhoodDenominatorModule R V n) ≅ (neighborhoodLocalTwist R V r n).val :=
  (tensorRestrictionIso (neighborhoodSectionOpen R V r).ι
    (neighborhoodSerreTwist R V n)
      (SheafOfModules.unit (neighborhoodGraphAmbient R V).ringCatSheaf)).symm ≪≫
    tensorSheafIso _ (Iso.refl _) (restrictUnitIso (neighborhoodSectionOpen R V r).ι) ≪≫
      tensorSheafRightUnit _ _

variable {R V r n}
variable {hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V}
variable {e : neighborhoodFrame R V r n}
/-- The numerator section map expressed in the local twist tensored with the dual graph ideal. -/
def NeighborhoodSectionPair.normalizedNumerator (d : NeighborhoodSectionPair R V hV r n e) :=
  d.numeratorHom ≫ (neighborhoodNumeratorNormalizeIso R V r n).hom
/-- The denominator section map expressed in the local twisting line bundle. -/
def NeighborhoodSectionPair.normalizedDenominator (d : NeighborhoodSectionPair R V hV r n e) :=
  d.denominatorHom ≫ (neighborhoodDenominatorNormalizeIso R V r n).hom

lemma NeighborhoodSectionPair.normalizedNumerator_boundary_isIso
    (d : NeighborhoodSectionPair R V hV r n e) :
    IsIso (pullbackSectionMap
      (neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r)
      d.normalizedNumerator) := by
  have := d.numeratorHom_boundary_isIso
  exact pullbackSectionMap_postIso_isIso
    (neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r)
    d.numeratorHom (neighborhoodNumeratorNormalizeIso R V r n)

lemma NeighborhoodSectionPair.normalizedDenominator_boundary_isIso
    (d : NeighborhoodSectionPair R V hV r n e) :
    IsIso (pullbackSectionMap
      (neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r)
      d.normalizedDenominator) := by
  have := d.denominatorHom_boundary_isIso
  exact pullbackSectionMap_postIso_isIso
    (neighborhoodGraphBoundaryMap R V hV ∣_ neighborhoodSectionOpen R V r)
    d.denominatorHom (neighborhoodDenominatorNormalizeIso R V r n)

lemma NeighborhoodSectionPair.normalizedNumerator_finite_flat
    (d : NeighborhoodSectionPair R V hV r n e) :
    NeighborhoodOpenSectionFiniteFlat R V r (neighborhoodSectionOpen R V r)
      (neighborhoodSerreOpen_eq_compact R V r)
      (tensorLineBundle _ (neighborhoodLocalTwist R V r n)
        (dualLineBundle _ (neighborhoodLocalIdeal R V r))) d.normalizedNumerator := by
  have := d.normalizedNumerator_boundary_isIso
  exact neighborhoodOpenSection_finite_flat R V hV r (neighborhoodSectionOpen R V r)
    (neighborhoodSerreOpen_eq_compact R V r)
    (tensorLineBundle _ (neighborhoodLocalTwist R V r n)
      (dualLineBundle _ (neighborhoodLocalIdeal R V r))) d.normalizedNumerator

lemma NeighborhoodSectionPair.normalizedDenominator_finite_flat
    (d : NeighborhoodSectionPair R V hV r n e) :
    NeighborhoodOpenSectionFiniteFlat R V r (neighborhoodSectionOpen R V r)
      (neighborhoodSerreOpen_eq_compact R V r)
      (neighborhoodLocalTwist R V r n) d.normalizedDenominator := by
  have := d.normalizedDenominator_boundary_isIso
  exact neighborhoodOpenSection_finite_flat R V hV r (neighborhoodSectionOpen R V r)
    (neighborhoodSerreOpen_eq_compact R V r)
    (neighborhoodLocalTwist R V r n) d.normalizedDenominator
end AlgebraicGeometry.RelativeProjectiveLine
