module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.FiniteChart.EnvelopeGoodOpen
/-! # The original finite locus is computed before any curve projection -/
set_option linter.hashCommand false
public section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleCompactification
variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  {Y : Scheme.{u}} (p : Y ⟶ X) [Etale p] [QuasiCompact p] [IsSeparated p]
example : IsFinite (p ∣_ finiteLocusOpen X p) := finite_on_finiteLocusOpen X p
example : genericPoint X ∈ finiteLocusOpen X p := genericPoint_mem_finiteLocusOpen X p
#print axioms finite_on_finiteLocusOpen
#print axioms genericPoint_mem_finiteLocusOpen
end AlgebraicGeometry.Scheme.EtaleCompactification
