module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.FiniteBoundarySourceLift
/-! # The entire source boundary over a fixed finite target bad boundary -/
set_option linter.hashCommand false
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleCompactification
variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  {Y S D : Scheme.{u}} (f : Y ⟶ X) [Etale f] [QuasiCompact f] [IsSeparated f]
  (q : X ⟶ S) [IsProper q] (d : D ⟶ X) [IsFinite (d ≫ q)]
  (U : X.Opens) [IsIntegralHom (pullback.snd f U.ι)]
  (hbad : (U : Set X)ᶜ ⊆ Set.range d)
include hbad in
example : IsFinite
    (infinityInclusion X f ≫ (genericMap X f).fromNormalization ≫ q) :=
  finite_infinity_of_finite_target_boundary X f q d U hbad
#print axioms finite_infinity_of_finite_target_boundary
end AlgebraicGeometry.Scheme.EtaleCompactification
