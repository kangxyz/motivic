/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IntegralGenericCoordinateFiber
public import Motivic.Aglib.RingTheory.DomainCartierMultiplicity
public import Motivic.Algebra.Homology.KoszulFiniteFamilyRealization
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Generic multiplicity of the whole finite domain algebra

The actual generic localization of an injective finite map of domains has
length equal to the residue degree of the original affine scheme map. The
comparison uses the original generic-localization and residue scalar square;
no separability, flatness, or choice of a generic branch is required.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Motivic.GenericFinitePushforwardMultiplicity

open FiniteDomainGenericFiber FiniteFiber IntegralGenericCoordinateFiber

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A B : CommRingCat.{u}) [IsDomain A] [IsDomain B]
  [Algebra A B] [Module.Finite A B]

/-- The length of the whole generic algebra is the original affine residue degree.
The two field identifications commute with the literal original scalar map. -/
theorem wholeGeneric_length (hAB : Function.Injective (algebraMap A B)) :
    Module.length (Localization.AtPrime (zeroPrime A).asIdeal)
        (localAlgebra A B (zeroPrime A)) =
      ((Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B)).residueDegree
        (zeroPrime B) : ℕ∞) := by
  let := genericLocal_isFractionRing A
  let : Field (Localization.AtPrime (zeroPrime A).asIdeal) := IsFractionRing.toField A
  let := localAlgebra_finite A B (zeroPrime A)
  let := (pointedSpecResidueMap (CommRingCat.ofHom (algebraMap A B))
    (zeroPrime A) (zeroPrime B) (zeroPrime_comap A B hAB)).hom.toAlgebra
  rw [Module.length_eq_finrank]
  congr 1
  calc
    _ = Module.finrank ((Spec A).residueField (zeroPrime A))
        ((Spec B).residueField (zeroPrime B)) := by
      apply Algebra.finrank_eq_of_equiv_equiv
        (genericLocalResidueIso A).commRingCatIsoToRingEquiv
        (wholeResidueIso A B hAB).commRingCatIsoToRingEquiv
      exact (congrArg CommRingCat.Hom.hom (wholeResidueIso_base_square A B hAB)).symm
    _ = _ := pointedSpecResidue_finrank (CommRingCat.ofHom (algebraMap A B))
      (zeroPrime A) (zeroPrime B) (zeroPrime_comap A B hAB)

/-- The rank over the original domain agrees with the degree of its actual
scheme residue extension, using the proved whole generic-algebra comparison. -/
theorem finrank_eq_residueDegree (hAB : Function.Injective (algebraMap A B)) :
    Module.finrank A B =
      (Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B)).residueDegree
        (zeroPrime B) := by
  let := genericLocal_isFractionRing A
  let : Field (Localization.AtPrime (zeroPrime A).asIdeal) := IsFractionRing.toField A
  let := localAlgebra_finite A B (zeroPrime A)
  have h := wholeGeneric_length A B hAB
  rw [Module.length_eq_finrank,
    (TensorProduct.isBaseChange (R := A)
      (S := Localization.AtPrime (zeroPrime A).asIdeal) (M := B)).finrank_eq] at h
  exact_mod_cast h

/-- The integer generic length of the whole algebra localized at any target
prime is the original affine generic residue degree. This localizes the whole
coefficient twice, without passing to any branch or quotient. -/
theorem localAlgebra_genericLength [IsNoetherianRing A]
    (p : PrimeSpectrum A) (hAB : Function.Injective (algebraMap A B)) :
    Koszul.domainGenericLength
        (Koszul.finiteFamilyRestriction (Localization.AtPrime p.asIdeal)
          (localAlgebra A B p) (ModuleCat.of (localAlgebra A B p) (localAlgebra A B p))) =
      ((Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B)).residueDegree
        (zeroPrime B) : ℤ) := by
  let R := Localization.AtPrime p.asIdeal
  let S := localAlgebra A B p
  let K := Localization.AtPrime (zeroPrime R).asIdeal
  let := genericLocal_isFractionRing (.of R)
  let : Field K := IsFractionRing.toField R
  let e : Koszul.finiteFamilyRestriction R S (ModuleCat.of S S) ≃ₗ[R] S :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r s
        change S at s
        change algebraMap R S r * (s : S) = r • (s : S)
        exact (Algebra.smul_def r (s : S)).symm }
  have hl : Module.length K
      (K ⊗[R] Koszul.finiteFamilyRestriction R S (ModuleCat.of S S)) =
      Module.length K (K ⊗[R] S) :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e).length_eq
  calc
    _ = ((Module.length K (K ⊗[R] S)).toNat : ℤ) :=
      congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) hl
    _ = (Module.finrank K (K ⊗[R] S) : ℤ) := by
      rw [Module.length_eq_finrank, ENat.toNat_natCast]
    _ = (Module.finrank R S : ℤ) := congrArg (fun n : ℕ => (n : ℤ))
      (TensorProduct.isBaseChange (R := R) (S := K) (M := S)).finrank_eq
    _ = (Module.finrank A B : ℤ) := congrArg (fun n : ℕ => (n : ℤ))
      (TensorProduct.isBaseChange (R := A)
        (S := Localization.AtPrime p.asIdeal) (M := B)).finrank_eq
    _ = _ := congrArg (fun n : ℕ => (n : ℤ)) (finrank_eq_residueDegree A B hAB)

section Schemes

variable {C D : Scheme.{u}} [IsIntegral C] [IsIntegral D] [IsLocallyNoetherian D]
  (j : C ⟶ D) [IsFinite j] [IsDominant j]
  {U : D.Opens} [Nonempty U] (hU : IsAffineOpen U) (p : Spec Γ(D, U))

/-- The coordinate action is the original map of sections. -/
local instance chartAlgebra : Algebra Γ(D, U) Γ(C, j ⁻¹ᵁ U) :=
  (j.app U).hom.toAlgebra

/-- For a finite dominant map of integral schemes, every local whole-algebra
coefficient has the actual source-generic residue degree. The scalar action
is the original chart map, and the whole inverse image is retained. -/
theorem scheme_genericLength :
    letI : IsNoetherianRing Γ(D, U) :=
      IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI : Module.Finite Γ(D, U) Γ(C, j ⁻¹ᵁ U) := j.finite_app U hU
    Koszul.domainGenericLength
        (Koszul.finiteFamilyRestriction (Localization.AtPrime p.asIdeal)
          (localAlgebra Γ(D, U) Γ(C, j ⁻¹ᵁ U) p)
          (ModuleCat.of (localAlgebra Γ(D, U) Γ(C, j ⁻¹ᵁ U) p)
            (localAlgebra Γ(D, U) Γ(C, j ⁻¹ᵁ U) p))) =
      (j.residueDegree (genericPoint C) : ℤ) := by
  let : IsNoetherianRing Γ(D, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Module.Finite Γ(D, U) Γ(C, j ⁻¹ᵁ U) := j.finite_app U hU
  have : Surjective j := surjective_of_isDominant_of_isClosed_range j
    j.isClosedMap.isClosed_range
  obtain ⟨y⟩ := ‹Nonempty U›
  obtain ⟨x, hx⟩ := j.surjective y.1
  let : Nonempty (j ⁻¹ᵁ U) := ⟨⟨x, by
    change j x ∈ U
    rw [hx]
    exact y.2⟩⟩
  let : IsSchemeTheoreticallyDominant j := .of_isDominant j
  rw [localAlgebra_genericLength Γ(D, U) Γ(C, j ⁻¹ᵁ U) p (j.app_injective U)]
  have h := FiniteAffineChart.residueDegree_eq j hU (zeroPrime Γ(C, j ⁻¹ᵁ U))
  rw [FiniteAffineChart.sourceChart, fromSpec_zero] at h
  exact congrArg (fun n : ℕ => (n : ℤ)) h

end Schemes

end Motivic.GenericFinitePushforwardMultiplicity
