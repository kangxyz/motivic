/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoMonicDeformation
public import Lean.Util.CollectAxioms

/-!
# Actual endpoint classes for finite monic two-unit deformations

The consumers keep the auxiliary root coordinate until graph projection,
include constant coordinate pairs with colliding images, and expose both
literal singular faces and the equality in the original weight-two homology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Motivic
open Polynomial.TwoUnitPolynomialFamily Polynomial.TwoUnitMonicDeformation
open AlgebraicGeometry.FiniteTwoUnitPolynomialFamily
open Motivic.WeightTwoMonicDeformation

universe u

namespace MotivicTest.WeightTwoMonicDeformation

variable {k : Type u} [Field k]

/-- Even completely colliding unit coordinates retain a genuine closed family. -/
theorem constant_pair_retained_closed (f : k[X][X]) (hf : f.Monic) :
    IsClosedImmersion (inclusion f 1 1) := inclusion_closed hf 1 1

/-- A full repeated polynomial quotient is retained even when both units are constant. -/
theorem repeated_constant_pair_closed (c : k) :
    IsClosedImmersion (polynomialInclusion ((X - C c) ^ 2) 1 1) := inferInstance

/-- The retained point cycle is the pushforward of the unreduced fundamental cycle. -/
theorem full_endpoint_fundamental (p : k[X]) (hp : p.Monic) (a b : (AdjoinRoot p)ˣ) :
    FiniteCorrespondence.toIntegralCycle (retainedPolynomialCycle p hp a b) =
      IntegralCycle.finitePushforward (polynomialInclusion p a b)
        (fundamentalCycle (Spec (.of (AdjoinRoot p)))) :=
  toIntegralCycle_retainedPolynomialCycle p hp a b

/-- Both literal singular faces retain all of the corresponding endpoint quotients. -/
theorem full_singular_faces (f : k[X][X]) (hf : f.Monic) (a b : (AdjoinRoot f)ˣ)
    (p q : k[X]) (hp : f.map (evalRingHom 0) = p) (hq : f.map (evalRingHom 1) = q)
    (hpm : p.Monic) (hqm : q.Monic) :
    ((WeightOneBoundaryNorm.zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ 0 ≫
          singularCorrespondence f hf a b =
      polynomialCycle p hpm (endpointUnit f 0 p hp a) (endpointUnit f 0 p hp b)) ∧
    ((WeightOneBoundaryNorm.zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ 1 ≫
          singularCorrespondence f hf a b =
      polynomialCycle q hqm (endpointUnit f 1 q hq a) (endpointUnit f 1 q hq b)) :=
  ⟨singularCorrespondence_face_zero f hf a b p hp hpm,
    singularCorrespondence_face_one f hf a b q hq hqm⟩

/-- The irreducible balanced-degree input gives the original raw-H22 relation. -/
theorem actual_raw_endpoint_relation (p A B : k[X]) (γ : k) (hp : p.Monic)
    (hi : Irreducible p) (hA : A ≠ 0) (hB : B ≠ 0)
    (hdeg : A.natDegree + B.natDegree < p.natDegree) :
    WeightTwoSymbols.cycleClass k
        (zeroCycle p A B γ hp (isCoprime_product hi hA hB hdeg)) =
      WeightTwoSymbols.cycleClass k
        (oneCycle p A B γ hp hdeg (isCoprime_product hi hA hB hdeg)) :=
  irreducible_cycleClass_endpoints p A B γ hp hi hA hB hdeg

/-- Both actual endpoint pairs are the specified polynomial images. -/
theorem original_coordinates (p A B : k[X]) (γ : k) (hcop : IsCoprime p (A * B)) :
    (zeroFirstUnit p A B γ hcop : AdjoinRoot p) = AdjoinRoot.mk p A ∧
      (zeroSecondUnit p A B γ hcop : AdjoinRoot p) = AdjoinRoot.mk p B ∧
      (oneFirstUnit p A B γ hcop : AdjoinRoot (endpointPolynomial p A B γ 1)) =
        AdjoinRoot.mk (endpointPolynomial p A B γ 1) A ∧
      (oneSecondUnit p A B γ hcop : AdjoinRoot (endpointPolynomial p A B γ 1)) =
        AdjoinRoot.mk (endpointPolynomial p A B γ 1) B := by
  simp only [zeroFirstUnit_val, zeroSecondUnit_val, oneFirstUnit_val, oneSecondUnit_val,
    and_self]

/-- The one endpoint in this explicit characteristic-zero relation is a repeated factor. -/
theorem repeated_endpoint_polynomial :
    endpointPolynomial (X ^ 2 + 1 : ℚ[X]) X 1 2 1 = (X - 1) ^ 2 := by
  simp only [endpointPolynomial, one_mul, mul_one]
  rw [map_ofNat]
  ring

/-- The actual homology equality includes the entire double-root endpoint. -/
theorem repeated_endpoint_raw_relation :
    let p : ℚ[X] := X ^ 2 + 1
    let hp : p.Monic := by
      dsimp only [p]
      monicity
      norm_num
    let hd : (X : ℚ[X]).natDegree + (1 : ℚ[X]).natDegree < p.natDegree := by
      norm_num [p, natDegree_X_pow_add_C]
    let hc : IsCoprime p (X * 1) := by
      refine ⟨1, -X, ?_⟩
      dsimp only [p]
      ring
    WeightTwoSymbols.cycleClass ℚ (zeroCycle p X 1 2 hp hc) =
      WeightTwoSymbols.cycleClass ℚ (oneCycle p X 1 2 hp hd hc) := by
  dsimp only
  exact monicDeformation_cycleClass_endpoints _ _ _ _ _ _ _

open Lean in
run_cmd do
  for name in #[``closedImmersion_of_coordinates, ``family_hom_ext,
      ``fiberPolynomialSchemeIso_inv_fst, ``fiberPolynomialSchemeIso_inv_snd,
      ``retainedTarget, ``forgetRoot, ``targetMap, ``inclusion, ``inclusion_closed,
      ``polynomialRootMap, ``polynomialRootMap_closed, ``polynomialTargetMap,
      ``polynomialInclusion, ``polynomialInclusion_closed, ``retainedPolynomialCycle,
      ``toIntegralCycle_retainedPolynomialCycle, ``polynomialCycle,
      ``retainedCorrespondence, ``fundamentalCorrespondence, ``endpointUnit,
      ``endpoint_targetMap, ``fiberInclusion_closed, ``fiberPolynomialSchemeIso_inv_inclusion,
      ``retained_graph_restriction, ``graph_restriction, ``singularCorrespondence,
      ``singularCorrespondence_face_zero, ``singularCorrespondence_face_one,
      ``cycleClass_endpoints, ``deformation_specialize_zero, ``zeroFirstUnit,
      ``zeroSecondUnit, ``oneFirstUnit, ``oneSecondUnit, ``zeroFirstUnit_val,
      ``zeroSecondUnit_val, ``oneFirstUnit_val, ``oneSecondUnit_val, ``zeroCycle, ``oneCycle,
      ``monicDeformation_cycleClass_endpoints, ``irreducible_cycleClass_endpoints,
      ``constant_pair_retained_closed, ``repeated_constant_pair_closed,
      ``full_endpoint_fundamental, ``full_singular_faces, ``actual_raw_endpoint_relation,
      ``original_coordinates, ``repeated_endpoint_polynomial, ``repeated_endpoint_raw_relation] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole monic two-unit endpoint classes use only standard Lean foundations."

end MotivicTest.WeightTwoMonicDeformation
