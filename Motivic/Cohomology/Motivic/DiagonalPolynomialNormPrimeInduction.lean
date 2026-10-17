/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalPolynomialNormInduction
public import Motivic.Cohomology.Motivic.DiagonalMilnorCoprimeRestriction

/-! # The genuine prime-degree diagonal norm comparison induction step -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace Motivic.DiagonalPolynomialNormInduction
open PresheafWithTransfers DiagonalMilnorSymbol DiagonalCorestriction
open KTheory MilnorK.PolynomialResidue MilnorK.PolynomialNorm
variable {k : Type u} [Field k] [CharZero k]
local instance rootFinite (F : Type u) [Field F] (p : MonicIrreducible F) :
    Module.Finite F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot
local instance primeRootCharZero (F : Type u) [Field F] [CharZero F]
    (p : MonicIrreducible F) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot p.val)).injective

/-- The zero-degree comparison follows from restriction surjectivity on K₀ and
both actual degree formulas, including arbitrary polynomial degrees. -/
theorem rawSymbol_polynomialNorm_zero (p : MonicIrreducible k)
    (x : MilnorK.K (AdjoinRoot p.val) 0) :
    rawSymbol k 0 (polynomialNorm 0 p x) =
      corestriction (k := k) 0 (rawSymbol (AdjoinRoot p.val) 0 x) := by
  let y := (MilnorK.zeroEquiv k).symm (MilnorK.zeroEquiv (AdjoinRoot p.val) x)
  have hy : MilnorK.map 0 (algebraMap k (AdjoinRoot p.val)) y = x := by
    apply (MilnorK.zeroEquiv (AdjoinRoot p.val)).injective
    rw [MilnorK.zeroEquiv_map]
    exact (MilnorK.zeroEquiv k).apply_symm_apply _
  rw [← hy, polynomialNorm_map_constants, map_zsmul,
    ← DiagonalFieldChange.rawSymbol_fieldChange, corestriction_fieldChange]
  rw [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank, AdjoinRoot.powerBasis_dim]

/-- Prime degree, without normality: the original degree and the constructed
coprime restriction degree annihilate the same defect. Only the displayed strict
lower-degree comparison premise is used. -/
theorem rawSymbol_polynomialNorm_prime_of_lower_degrees
    (n : ℕ) (p : MonicIrreducible k) (hp : p.val.natDegree.Prime)
    (ih : ∀ (r : MonicIrreducible (AdjoinRoot p.val)),
      r.val.natDegree < p.val.natDegree →
      ∀ y : MilnorK.K (AdjoinRoot r.val) n,
        rawSymbol (AdjoinRoot p.val) n (polynomialNorm n r y) =
          corestriction (k := AdjoinRoot p.val) n (rawSymbol (AdjoinRoot r.val) n y))
    (x : MilnorK.K (AdjoinRoot p.val) n) :
    rawSymbol k n (polynomialNorm n p x) =
      corestriction (k := k) n (rawSymbol (AdjoinRoot p.val) n x) := by
  cases n with
  | zero => exact rawSymbol_polynomialNorm_zero p x
  | succ m =>
    obtain ⟨L, hL, hA, hfd, _hsep, hcop, hrestricted⟩ :=
      DiagonalMilnorCoprimeRestriction.exists_coprime_restriction_norm_eq p hp m x
    let := hfd
    let δ := rawSymbol k (m + 1) (polynomialNorm (m + 1) p x) -
      corestriction (k := k) (m + 1) (rawSymbol (AdjoinRoot p.val) (m + 1) x)
    have hd : (p.val.natDegree : ℤ) • δ = 0 :=
      degree_smul_comparison_defect_eq_zero (m + 1) p hp.one_lt ih x
    have he : (Module.finrank k L : ℤ) • δ = 0 := by
      have h := congrArg (corestriction (k := k) (E := L) (m + 1)) hrestricted
      rw [corestriction_fieldChange, corestriction_fieldChange] at h
      exact (smul_sub _ _ _).trans (sub_eq_zero.mpr h)
    apply sub_eq_zero.mp
    change δ = 0
    obtain ⟨a, b, hab⟩ := hcop.isCoprime
    calc
      δ = (1 : ℤ) • δ := (one_smul ℤ δ).symm
      _ = (a * p.val.natDegree + b * (Module.finrank k L : ℤ)) • δ := by rw [hab]
      _ = 0 := by rw [add_smul, mul_smul, mul_smul, hd, he, smul_zero, smul_zero, add_zero]

end Motivic.DiagonalPolynomialNormInduction
