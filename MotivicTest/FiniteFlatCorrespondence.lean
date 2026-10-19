/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Basic
public import Motivic.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.CurveFamily

/-!
# Consumers of full finite-flat correspondence assembly

The main consumer has no connectedness or reducedness assumptions. It retains
all original local lengths and residue degrees and agrees with the pre-existing
irreducible closed-support adapter wherever both interfaces apply.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.FiniteFlatCorrespondence
open _root_.AlgebraicGeometry.Scheme (IntegralCycle SmoothSite)
open _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  {D : Scheme.{u}} (f : D ⟶ X.left) [IsFinite f] [Flat f]
  (g : D ⟶ Y.left) (h : f ≫ X.hom = g ≫ Y.hom)

/-- The actual category consumer allows disconnected smooth objects and a
nonreduced finite scheme; no image embedding is required. -/
theorem wholeSpanCycle :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
      (Cor.ofFiniteFlatSpan f g h) =
      letI : IsFinite (pullback.lift f g h) :=
        Motivic.FiniteFlatCorrespondence.isFinite_productMap f _ (pullback.lift_fst _ _ _)
      letI : IsNoetherian D := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType f
      IntegralCycle.finitePushforward (pullback.lift f g h)
          (_root_.AlgebraicGeometry.Scheme.fundamentalCycle D) :=
  Cor.toIntegralCycle_ofFiniteFlatSpan f g h

/-- The zero case uses an actually empty support, with the same original maps. -/
theorem emptySpan [IsEmpty D] : Cor.ofFiniteFlatSpan f g h = 0 := by
  have : IsNoetherian D := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType f
  have : IsFinite (pullback.lift f g h) :=
    Motivic.FiniteFlatCorrespondence.isFinite_productMap f _ (pullback.lift_fst _ _ _)
  exact Motivic.FiniteFlatCorrespondence.fundamentalCorrespondence_eq_zero_of_isEmpty f _ _

/-- On the already-covered irreducible closed-support domain, the new adapter
is literally equal to the old actual correspondence, not merely isomorphic. -/
theorem agreesWithIrreducibleClosedAdapter [IrreducibleSpace X.left] [IsNoetherian D]
    (j : D ⟶ pullback X.hom Y.hom) [IsClosedImmersion j]
    (hj : j ≫ pullback.fst X.hom Y.hom = f)
    (hdom : ∀ z : genericPoints D,
      Function.Surjective ((AffineLineField.componentSupport z).val.subschemeι ≫ f)) :
    Motivic.FiniteFlatCorrespondence.fundamentalCorrespondence f j hj =
      _root_.Motivic.FiniteFlatCurveFamily.genericFundamentalCorrespondence f j hj hdom := by
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [Motivic.FiniteFlatCorrespondence.toIntegralCycle_fundamentalCorrespondence,
    _root_.Motivic.FiniteFlatCurveFamily.toIntegralCycle_genericFundamentalCorrespondence]

open Lean in
run_cmd do
  for name in #[``Scheme.Hom.image_closure_singleton_of_isFinite,
      ``Scheme.Hom.image_closure_mem_irreducibleComponents_of_finite_generalizing,
      ``Scheme.Hom.image_closure_mem_irreducibleComponents_of_finite_flat,
      ``Motivic.FiniteFlatCorrespondence.isFinite_productMap,
      ``Motivic.FiniteFlatCorrespondence.componentGenerator,
      ``Motivic.FiniteFlatCorrespondence.cycleAssembly,
      ``Motivic.FiniteFlatCorrespondence.cycleAssembly_coefficient,
      ``Motivic.FiniteFlatCorrespondence.toIntegralCycle_cycleAssembly,
      ``Motivic.FiniteFlatCorrespondence.toIntegralCycle_fundamentalCorrespondence,
      ``Cor.ofFiniteFlatSpan, ``Cor.toIntegralCycle_ofFiniteFlatSpan,
      ``wholeSpanCycle, ``emptySpan, ``agreesWithIrreducibleClosedAdapter] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Full finite-flat correspondences use only standard foundations."

end MotivicTest.FiniteFlatCorrespondence
