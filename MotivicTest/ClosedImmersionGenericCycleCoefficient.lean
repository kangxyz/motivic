/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.ClosedImmersionGenericCycleCoefficient

/-!
# Consumers of actual closed-support generic coefficients

The tests retain the original specialization scalar map, the original affine
point, the actual kernel quotient, and the literal restricted closed immersion.
The outside-image test applies at the original point, while the coefficient
identity itself allows that point to belong to the image and its ambient
generic to lie outside it. No generic-preservation hypothesis is imposed.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open scoped TensorProduct

universe u

namespace MotivicTest.ClosedImmersionGenericCycleCoefficient

variable {E T : Scheme.{u}}

/-- The scalar square uses the actual specialization and canonical localization map. -/
theorem actualGenericScalarSquare (x : T) (q : {q : genericPoints T // q.1 ⤳ x}) :
    T.presheaf.stalkSpecializes q.2 ≫ (genericStalkLocalizationIso T x q).hom =
      CommRingCat.ofHom (algebraMap (T.presheaf.stalk x)
        (Localization.AtPrime (genericStalkLocalizationPrime T x q).asIdeal)) :=
  stalkSpecializes_genericStalkLocalizationIso T x q

/-- The closed ideal specializes literally; neither radical nor reduced support intervenes. -/
theorem actualClosedStalkIdeal (j : E ⟶ T)
    (x : T) (q : {q : genericPoints T // q.1 ⤳ x}) :
    (j.ker.stalk x).map (T.presheaf.stalkSpecializes q.2).hom = j.ker.stalk q.1.1 :=
  j.ker.stalk_map_specializes q.2

/-- A point outside the closed image has the unit kernel ideal and zero quotient module. -/
theorem outsideClosedImage (j : E ⟶ T) [IsClosedImmersion j]
    (x : T) (hx : x ∉ Set.range j) :
    j.ker.stalk x = ⊤ ∧ Subsingleton ((T.presheaf.stalk x) ⧸ j.ker.stalk x) :=
  ⟨closedImmersion_ker_stalk_eq_top j hx,
    Ideal.Quotient.subsingleton_iff.mpr (closedImmersion_ker_stalk_eq_top j hx)⟩

/-- Generic length is finite before conversion, including the possibly zero localization. -/
theorem actualFiniteGenericLength (j : E ⟶ T)
    [IsLocallyNoetherian T] (x : T) (q : {q : genericPoints T // q.1 ⤳ x}) :
    Module.length (Localization.AtPrime (genericStalkLocalizationPrime T x q).asIdeal)
        (Localization.AtPrime (genericStalkLocalizationPrime T x q).asIdeal ⊗[T.presheaf.stalk x]
          ((T.presheaf.stalk x) ⧸ j.ker.stalk x)) ≠ ⊤ :=
  genericStalkQuotient_length_ne_top j.ker x q

/-- The actual affine-point quotient supplies precisely the restricted-cycle coefficient. -/
theorem actualAffineRestrictedCoefficient
    (j : E ⟶ T) [IsClosedImmersion j] [IsNoetherian E] [IsLocallyNoetherian T]
    (V : T.affineOpens) [IsNoetherian (j ⁻¹ᵁ V.1).toScheme]
    (p : PrimeSpectrum Γ(T, V)) (q : {q : genericPoints T // q.1 ⤳ V.2.fromSpec p}) :
    Koszul.fixedSupportGenericLength
        (ModuleCat.of (T.presheaf.stalk (V.2.fromSpec p))
          ((T.presheaf.stalk (V.2.fromSpec p)) ⧸ j.ker.stalk (V.2.fromSpec p)))
        ⊥ bot_le ⟨(genericStalkLocalizationPrime T (V.2.fromSpec p) q).asIdeal,
          genericStalkLocalizationPrime_mem_minimalPrimes T (V.2.fromSpec p) q⟩ =
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (j ∣_ V.1)
          (fundamentalCycle (j ⁻¹ᵁ V.1).toScheme))
        ⟨q.1.1, q.2.mem_open V.1.isOpen
          (V.2.range_fromSpec.subset (Set.mem_range_self p))⟩ :=
  fixedSupportGenericLength_closedImmersion_openRestriction j V.1 (V.2.fromSpec p)
    (V.2.range_fromSpec.subset (Set.mem_range_self p)) q

end MotivicTest.ClosedImmersionGenericCycleCoefficient
