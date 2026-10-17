module

import Motivic.Cohomology.Motivic.OrdinaryShiftComparison
import Motivic.Algebra.Homology.AcyclicKernelQuasiIso

import Lean.Util.CollectAxioms

/-! # Direct original-complex consumers and foundational axiom audit -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

example (k : Type u) [Field k] (q : ℕ) :
    Motivic.motivicSheafComplex k q ≅
      ((Motivic.SingularComplex.sheafObj
        (Motivic.SmoothSite.nisnevichTopology (Spec (.of k)))
        (Motivic.AlgebraicSimplex.cosimplicialSmoothSite k)
        ((Motivic.PresheafWithTransfers.toPresheaf k).obj
          (Motivic.PresheafWithTransfers.reducedTorus k q))).extend
            (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧ :=
  Motivic.motivicSheafComplexOrdinaryShiftIso k q


open Lean in
run_cmd do
  for name in #[
      ``Motivic.quasiIso_of_shortExact_isZero_homology,
      ``Motivic.MapExtension.iso,
      ``Motivic.motivicSheafComplexOrdinaryShiftIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original-complex comparison uses only standard foundations."
