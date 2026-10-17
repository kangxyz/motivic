module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.RelativeAffineLineEtaleCompactification

/-! # Relative étale compactification regression tests

The base is a normal Noetherian domain, not a field. The source is unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
universe u

namespace MotivicTest.RelativeAffineLineEtaleCompactification

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {W : Scheme.{u}}
  (p : W ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p]

example : IsOpenImmersion (inclusion R p) := inferInstance

example : IsFinite (toProjectiveLine R p) := inferInstance

example : IsProper (infinityInclusion R p ≫ projection R p) := inferInstance

omit [IsSeparated p] in
example (z : Spec (.of R) ⟶ W)
    (hz : z ≫ p = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) :
    liftedZero R p z ≫ toProjectiveLine R p =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
        RelativeProjectiveLine.chart R ⟨0⟩ :=
  liftedZero_toProjectiveLine R p z hz

example (z : Spec (.of R) ⟶ W) (s : Spec (.of R)) :
    liftedZero R p z s ∉ Set.range (infinityInclusion R p) :=
  liftedZero_not_mem_infinity R p z s

end MotivicTest.RelativeAffineLineEtaleCompactification
