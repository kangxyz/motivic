module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.FiniteChart.CompactificationChart
/-! # One target presentation gives the actual full finite source boundary -/
set_option linter.hashCommand false
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleCompactification
variable (X C : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [IsIntegral C] [IsLocallyNoetherian C]
  [∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x)]
  {Y S D Z : Scheme.{u}} (p : Y ⟶ X) [Etale p] [QuasiCompact p] [IsSeparated p]
  (j : X ⟶ C) [IsOpenImmersion j] [QuasiCompact j]
  (q : C ⟶ S) [IsProper q] (d : D ⟶ C) [IsFinite (d ≫ q)]
  (hbad : (j ''ᵁ finiteLocusOpen X p : Set C)ᶜ ⊆ Set.range d)
  (s : Z ⟶ Y) [IsClosedImmersion s] [IsFinite (s ≫ p ≫ j ≫ q)]
include hbad in
example : IsFinite (boundaryInclusion C (p ≫ j) s ≫
    (genericMap C (p ≫ j)).fromNormalization ≫ q) :=
  finite_full_source_boundary_over_fixed_target X C p j q d hbad s
example : IsClosedImmersion (boundaryInclusion C (p ≫ j) s) :=
  full_source_boundary_closed_over_fixed_target X C p j q s
#print axioms finite_full_source_boundary_over_fixed_target
#print axioms full_source_boundary_closed_over_fixed_target
end AlgebraicGeometry.Scheme.EtaleCompactification
