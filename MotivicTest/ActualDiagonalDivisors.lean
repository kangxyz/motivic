/-
Copyright (c) 2026 Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualDiagonalDivisors

/-! Direct original-overlap finite-flat divisor consumer. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.AffineLineEtaleCompactification
universe u
example (k : Type u) [Field k] {Y S Z : Scheme.{u}} [IsAffine S]
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
    (r : S ⟶ Y) (s : Z ⟶ S) (U : (Spec (.of (Polynomial k))).Opens)
    (z : Z ⟶ Spec (.of (Polynomial k))) (H : IsPullback (s ≫ r) (𝟙 _) p z)
    (hz : Set.range z = (U : Set (Spec (.of (Polynomial k))))ᶜ)
    (L : LineBundle (diagonalAmbient k p r))
    (a : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap (diagonalBoundaryMap k p r s) a)] :=
  actualSectionDivisor_finite_mono_flat k p r s U z H hz L a
#print axioms actualSectionDivisor_finite_mono_flat
#print axioms diagonalBoundary_retained_cover
