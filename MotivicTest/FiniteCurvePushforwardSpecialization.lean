/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.FiniteCurvePushforwardSpecialization

/-!
# Consumers of genuine finite Cartier-fiber geometry

No normality, flatness of the finite curve map, or reducedness of an endpoint
is assumed. The original-point Cartier balance is proved from the whole
finite algebra and then assembled into the unconditional scheme equality.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open AlgebraicGeometry.FiniteFlatCurve
open scoped Polynomial

universe u

namespace MotivicTest.FiniteCurvePushforwardSpecialization

variable {k : Type u} [Field k] {C D : Scheme.{u}}
  (f : D ⟶ Spec (.of k[X])) [IsFinite f] (j : C ⟶ D) [IsFinite j]

/-- Finite fiber maps do not require flatness of the finite curve map. -/
example (a : k) : IsFinite (fiberMap f a j) := inferInstance

/-- A surjective curve map is still surjective after the actual endpoint cut. -/
example [Surjective j] (a : k) : Surjective (fiberMap f a j) := inferInstance

omit [IsFinite f] [IsFinite j] in
/-- The source point's original degree is the degree used at the endpoint. -/
theorem originalResidueWeight (a : k) (x : fiber (j ≫ f) a) :
    (fiberMap f a j).residueDegree x =
      j.residueDegree (fiberInclusion (j ≫ f) a x) :=
  fiberMap_residueDegree f a j x

/-- The target endpoint retains its original, possibly nonreduced local length. -/
theorem originalTargetLength [IsNoetherian D] (a : k) (y : fiber f a) :
    IntegralCycle.toPoints (fundamentalCycle (fiber f a)) y =
      ((Module.length (D.presheaf.stalk (fiberInclusion f a y))
        ((D.presheaf.stalk (fiberInclusion f a y)) ⧸
          Ideal.ofList [scalar f a (fiberInclusion f a y)])).toNat : ℤ) :=
  fiber_fundamentalCoefficient f a y

/-- The zero endpoint keeps every original source point with its own weight. -/
theorem zeroEndpointCoefficient [IsNoetherian C] (y : fiber f (0 : k)) :
    IntegralCycle.toPoints (IntegralCycle.finitePushforward (fiberMap f 0 j)
        (fundamentalCycle (fiber (j ≫ f) 0))) y =
      ∑ᶠ x : {x : C // j x = fiberInclusion f 0 y},
        (j.residueDegree x.1 : ℤ) *
          ((Module.length (C.presheaf.stalk x.1)
            ((C.presheaf.stalk x.1) ⧸ Ideal.ofList [scalar (j ≫ f) 0 x.1])).toNat : ℤ) :=
  fiberMap_fundamentalCoefficient f 0 j y

/-- The one endpoint uses the unchanged equation t−1 and all original branches. -/
theorem oneEndpointCoefficient [IsNoetherian C] (y : fiber f (1 : k)) :
    IntegralCycle.toPoints (IntegralCycle.finitePushforward (fiberMap f 1 j)
        (fundamentalCycle (fiber (j ≫ f) 1))) y =
      ∑ᶠ x : {x : C // j x = fiberInclusion f 1 y},
        (j.residueDegree x.1 : ℤ) *
          ((Module.length (C.presheaf.stalk x.1)
            ((C.presheaf.stalk x.1) ⧸ Ideal.ofList [scalar (j ≫ f) 1 x.1])).toNat : ℤ) :=
  fiberMap_fundamentalCoefficient f 1 j y

/-- Arbitrary endpoints use the actual generic degree of the finite curve map. -/
theorem arbitraryEndpoint [IsIntegral C] [IsIntegral D]
    [Surjective f] [Surjective j] [IsNoetherian C] [IsNoetherian D] (a : k) :
    IntegralCycle.finitePushforward (fiberMap f a j)
        (fundamentalCycle (fiber (j ≫ f) a)) =
      (j.residueDegree (genericPoint C) : ℤ) • fundamentalCycle (fiber f a) :=
  finiteCurve_finitePushforward_fiber f j a

/-- Signed coefficients and any further genuine finite pushforward retain
both the complete endpoint cycle and the original generic multiplier. -/
theorem signedEndpoint [IsIntegral C] [IsIntegral D]
    [Surjective f] [Surjective j] [IsNoetherian C] [IsNoetherian D]
    (a : k) {Q : Scheme.{u}} (g : fiber f a ⟶ Q) [IsFinite g] (n : ℤ) :
    IntegralCycle.finitePushforward (fiberMap f a j ≫ g)
        (n • fundamentalCycle (fiber (j ≫ f) a)) =
      (n * (j.residueDegree (genericPoint C) : ℤ)) •
        IntegralCycle.finitePushforward g (fundamentalCycle (fiber f a)) := by
  rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    map_zsmul, arbitraryEndpoint f j a, map_zsmul, map_zsmul, smul_smul]

open Lean in
run_cmd do
  for name in #[
      ``fiberMap_isFinite, ``fiberMap_surjective, ``fiberMap_residueDegree,
      ``scalar_stalkMap, ``fiber_stalk_length, ``fiber_cut_length_ne_top,
      ``fiber_fundamentalCoefficient, ``fiberMapPointEquiv,
      ``fiberMapPointEquiv_apply_val, ``fiberGenericPointEquiv,
      ``fiberMap_fundamentalCoefficient, ``finitePushforward_fiber_of_cartierLength,
      ``Koszul.finiteAlgebra_cartierEuler, ``Koszul.cartierQuotientRingEquiv,
      ``Koszul.cartierQuotient_length_ringEquiv, ``Koszul.cartier_regular_ringEquiv,
      ``localScalar, ``alignedStalkMap_scalar,
      ``originalSourceLocalizationIso_scalar, ``originalSourceLocalizationIso_cartierLength,
      ``originalSourceLocalizationIso_regular, ``Koszul.finiteAlgebra_domainCartierLength,
      ``originalCartierLength_sum,
      ``AlgebraicGeometry.finiteCurve_finitePushforward_fiber,
      ``arbitraryEndpoint, ``signedEndpoint,
      ``originalResidueWeight, ``originalTargetLength,
      ``zeroEndpointCoefficient, ``oneEndpointCoefficient] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual finite Cartier pushforward specialization uses only standard foundations."

end MotivicTest.FiniteCurvePushforwardSpecialization
