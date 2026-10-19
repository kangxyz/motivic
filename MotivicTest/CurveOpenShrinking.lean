/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Open.CurveOpenShrinking
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.Fibers.OpenFiberShrinking
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Dimension.EtaleCurveDimension
public import Motivic.Aglib.AlgebraicGeometry.AffineLine.Open.AffineLineReducedComplement

/-! Direct actual affine-line Nisnevich-neighborhood shrinking consumer. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Motivic.MotivicTest
open _root_.AlgebraicGeometry.Scheme

/-- A genuine étale neighborhood of the full reduced affine-line complement
can be shrunk to precisely any generic-containing open of its overlap, without
losing its original scheme-theoretic isomorphism over that complement. -/
theorem affineLine_etaleNeighborhood_shrinking
    {k : Type u} [Field k] {V : Scheme.{u}} [IsNoetherian V]
    (p : V ⟶ AffineLineReducedComplement.line k) [Etale p]
    (U : (AffineLineReducedComplement.line k).Opens)
    [IsIso (pullback.snd p (AffineLineReducedComplement.inclusion U))]
    (O : (p ⁻¹ᵁ U).toScheme.Opens)
    (hgeneric : genericPoints (p ⁻¹ᵁ U).toScheme ⊆ (O : Set (p ⁻¹ᵁ U).toScheme)) :
    ∃ T : V.Opens, ((p ⁻¹ᵁ U : V.Opens) : Set V)ᶜ ⊆ (T : Set V) ∧
      (p ⁻¹ᵁ U).ι ⁻¹ᵁ T = O ∧ ((T : Set V)ᶜ).Finite ∧
      IsIso (pullback.snd (T.ι ≫ p) (AffineLineReducedComplement.inclusion U)) := by
  let : JacobsonSpace V := LocallyOfFiniteType.jacobsonSpace p
  have hdim : topologicalKrullDim (p ⁻¹ᵁ U).toScheme ≤ 1 :=
    Scheme.topologicalKrullDim_le_one_of_etale_affineLine ((p ⁻¹ᵁ U).ι ≫ p)
  obtain ⟨T, hT, hTO, hfin⟩ :=
    Scheme.exists_open_shrinking_retaining_complement (p ⁻¹ᵁ U) O hgeneric hdim
  refine ⟨T, hT, hTO, hfin, ?_⟩
  apply Scheme.Hom.isIso_pullback_snd_of_open_retains_fiber p
    (AffineLineReducedComplement.inclusion U) T
  rw [AffineLineReducedComplement.range_inclusion]
  exact hT

open Lean in
run_cmd do
  for name in #[``Scheme.finite_closed_complement_of_genericPoints_subset,
      ``Scheme.exists_open_shrinking_retaining_complement,
      ``Scheme.topologicalKrullDim_le_of_etale,
      ``Scheme.topologicalKrullDim_le_one_of_etale_affineLine,
      ``Scheme.Hom.isIso_pullback_snd_of_open_retains_fiber,
      ``affineLine_etaleNeighborhood_shrinking] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual curve finite-point deletion and retained Nisnevich fiber: standard axioms only."

end Motivic.MotivicTest
