/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.ScalarBranches
public import Aglib.KTheory.MilnorK.K3.ResidueBaseChangeSupport
public import Lean.Util.CollectAxioms

/-!
# Consumers of the whole scalar polynomial scheme

The original finite `placesAbove` set indexes the complete fundamental cycle.
The scalar square and both projections use the literal polynomial quotient
maps. Its factor branches compose to the existing residue-field map before
applying any cycle class, norm, or motivic quotient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial AdjoinRoot
open MilnorK.K3.PolynomialResidue
open _root_.AlgebraicGeometry.Scheme.PolynomialQuotient.ScalarBranches
open scoped BigOperators

universe u

namespace Motivic.MotivicTest.AdjoinRootScalarBranchesGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.PolynomialQuotient.ScalarBranches

variable {k L : Type u} [Field k] [Field L]

open scoped Classical in
/-- The complete fundamental cycle is the exact original finite sum of
polynomial target places, each with coefficient one. -/
theorem original_places_fundamentalCycle [CharZero k]
    (φ : k →+* L) (p : MonicIrreducible k) :
    fundamentalCycle (Spec (.of (AdjoinRoot (p.val.map φ)))) =
      ∑ q ∈ (placesAbove φ p).attach,
        IntegralCycle.finitePushforward
          (branchMap (p.val.map φ) ⟨q.val, (mem_placesAbove φ p q.val).mp q.property⟩)
          (fundamentalCycle (Spec (.of (AdjoinRoot q.val.val)))) := by
  classical
  let : Module.Finite L (AdjoinRoot (p.val.map φ)) := (p.property.1.map φ).finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot (p.val.map φ)) := .of_finite L _
  let : Fintype (MaximalSpectrum (AdjoinRoot (p.val.map φ))) := Fintype.ofFinite _
  let : Fintype (IrreducibleBranch (p.val.map φ)) :=
    Fintype.ofEquiv (MaximalSpectrum (AdjoinRoot (p.val.map φ)))
      (branchEquivMaximal (p.val.map φ) (p.property.1.map φ).ne_zero).symm
  have h := scalar_fundamentalCycle_eq_sum_branches φ p.val p.property.1
  dsimp only at h
  rw [h, Finset.attach_eq_univ]
  symm
  apply Fintype.sum_equiv (Equiv.subtypeEquivRight (fun q => mem_placesAbove φ p q))
  intro q
  rfl

/-- The literal polynomial quotient, with its original ring maps, is the
whole Cartesian scalar fiber. -/
theorem original_scalar_square (φ : k →+* L) (p : MonicIrreducible k) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (AdjoinRoot.of (p.val.map φ))))
      (Spec.map (CommRingCat.ofHom (scalarMap φ p.val)))
      (Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom (AdjoinRoot.of p.val))) :=
  scalar_isPullback φ p.val

/-- Going from the actual pullback back to the polynomial quotient preserves
its projection to the original source field. -/
theorem inverse_original_projection (φ : k →+* L) (p : MonicIrreducible k) :
    (scalarSchemeIso φ p.val).inv ≫ Spec.map (CommRingCat.ofHom (scalarMap φ p.val)) =
      pullback.snd _ _ := by
  rw [← scalarSchemeIso_hom_snd, Iso.inv_hom_id_assoc]

/-- The complete branch square uses the already existing residue homomorphism. -/
theorem original_place_projection (φ : k →+* L) (p : MonicIrreducible k)
    (q : {q // q ∈ placesAbove φ p}) :
    branchMap (p.val.map φ) ⟨q.val, (mem_placesAbove φ p q.val).mp q.property⟩ ≫
      Spec.map (CommRingCat.ofHom (scalarMap φ p.val)) =
        Spec.map (CommRingCat.ofHom (Polynomial.LocalResidue.adjoinRootMap φ p.val q.val.val
          ((mem_placesAbove φ p q.val).mp q.property))) :=
  branchMap_scalarMap φ p.val _

open Lean in
run_cmd do
  for name in #[``_root_.AlgebraicGeometry.Scheme.PolynomialQuotient.ScalarBranches.scalarSchemeIso,
      ``scalarSchemeIso_hom_fst, ``scalarSchemeIso_hom_snd,
      ``_root_.AlgebraicGeometry.Scheme.PolynomialQuotient.ScalarBranches.scalar_isPullback,
          ``branchMap_genericPoint, ``finitePushforward_branchMap,
      ``fundamentalCycle_eq_sum_branches, ``scalar_fundamentalCycle_eq_sum_branches,
      ``_root_.AlgebraicGeometry.Scheme.PolynomialQuotient.ScalarBranches.branchMap_scalarMap,
          ``original_places_fundamentalCycle, ``original_scalar_square,
      ``inverse_original_projection, ``original_place_projection] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole scalar polynomial geometry uses only standard Lean foundations."

end Motivic.MotivicTest.AdjoinRootScalarBranchesGeometry
