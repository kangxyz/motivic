module

import Motivic.Cohomology.WeightOne.SheafComparison

import Lean.Util.CollectAxioms

/-! # Direct original-complex consumers and foundational axiom audit -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

example (k : Type u) [Field k] :
    Motivic.motivicSheafComplex k 1 ⟶
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (Scheme.SmoothSite.largeUnitsSheaf (Spec (.of k))))⟦(-1 : ℤ)⟧ :=
  Motivic.weightOneSheafComparison k

example (k : Type u) [Field k] : QuasiIso (Motivic.weightOneSheafComparison k) :=
  inferInstance


open Lean in
run_cmd do
  for name in #[
      ``Motivic.reducedNormSheafMap_quasiIso,
      ``Motivic.weightOneSheafChainComparison,
      ``Motivic.weightOneSheafChainComparison_quasiIso,
      ``Motivic.weightOneSheafComparison,
      ``Motivic.weightOneSheafComparison_quasiIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original-complex comparison uses only standard foundations."
