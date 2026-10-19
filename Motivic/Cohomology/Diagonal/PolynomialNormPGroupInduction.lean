/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.PolynomialNormPrimeInduction
public import Motivic.Cohomology.Diagonal.CorestrictionPresentationTransport
public import Motivic.Cohomology.Diagonal.CorestrictionTower
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.Tower
public import Aglib.FieldTheory.PGroupNormalSubfieldEmbedding

/-!
# The genuine p-group ambient norm-symbol induction step

An actual normal-prime subfield of the original embedded root field supplies
strictly smaller lower and upper degrees whenever the root degree is composite.
The actual finite-extension norm tower and diagonal transfer tower then compare
the original maps. The sole comparison premise concerns strictly smaller
polynomial degrees over all characteristic-zero base fields, at fixed weight.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Motivic.DiagonalPolynomialNormInduction

open DiagonalMilnorSymbol DiagonalCorestriction
open MilnorK.PolynomialResidue MilnorK.PolynomialNorm
open MilnorK.K3.PolynomialNorm (rootEvaluationEquiv rootEvaluationEquiv_toRingHom)

local instance pGroupRootFinite (F : Type u) [Field F] (p : MonicIrreducible F) :
    Module.Finite F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

local instance pGroupRootCharZero (F : Type u) [Field F] [CharZero F]
    (p : MonicIrreducible F) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot p.val)).injective

variable {k : Type u} [Field k] [CharZero k]

/-- A comparison on an actual polynomial presentation transfers to the original
finite field, using the already proved norm and transfer presentation laws. -/
theorem rawSymbol_finiteExtensionNorm_of_presentation
    {E : Type u} [Field E] [CharZero E] [Algebra k E] [FiniteDimensional k E]
    (n : ℕ) (p : MonicIrreducible k) (ε : AdjoinRoot p.val ≃ₐ[k] E)
    (h : ∀ y : MilnorK.K (AdjoinRoot p.val) n,
      rawSymbol k n (polynomialNorm n p y) =
        corestriction (k := k) n (rawSymbol (AdjoinRoot p.val) n y))
    (x : MilnorK.K E n) :
    rawSymbol k n (MilnorK.finiteExtensionNorm k E n x) =
      corestriction (k := k) n (rawSymbol E n x) := by
  let y := MilnorK.map n ε.symm.toRingHom x
  have hy : MilnorK.map n ε.toRingHom y = x := by
    dsimp only [y]
    rw [← LinearMap.comp_apply, ← MilnorK.map_comp]
    have he : ε.toRingHom.comp ε.symm.toRingHom = RingHom.id E := by
      apply RingHom.ext
      exact ε.apply_symm_apply
    rw [he, MilnorK.map_id, LinearMap.id_apply]
  calc
    rawSymbol k n (MilnorK.finiteExtensionNorm k E n x) =
        rawSymbol k n (polynomialNorm n p y) := by
      rw [MilnorK.finiteExtensionNorm_eq_presentation k E n p ε]
      rfl
    _ = corestriction (k := k) n (rawSymbol (AdjoinRoot p.val) n y) := h y
    _ = corestriction (k := k) n (rawSymbol E n (MilnorK.map n ε.toRingHom y)) :=
      corestriction_rawSymbol_algEquiv ε n y
    _ = corestriction (k := k) n (rawSymbol E n x) := by rw [hy]

/-- The strict polynomial-degree induction premise applies to an actual finite
field of smaller degree without replacing its original scalar structure. -/
theorem rawSymbol_finiteExtensionNorm_of_lower_degrees
    {E : Type u} [Field E] [CharZero E] [Algebra k E] [FiniteDimensional k E]
    (n d : ℕ) (hd : Module.finrank k E < d)
    (ih : ∀ (p : MonicIrreducible k), p.val.natDegree < d →
      ∀ y : MilnorK.K (AdjoinRoot p.val) n,
        rawSymbol k n (polynomialNorm n p y) =
          corestriction (k := k) n (rawSymbol (AdjoinRoot p.val) n y))
    (x : MilnorK.K E n) :
    rawSymbol k n (MilnorK.finiteExtensionNorm k E n x) =
      corestriction (k := k) n (rawSymbol E n x) := by
  let p := MilnorK.finiteNormPolynomial k E
  let ε := MilnorK.finiteNormPresentation k E
  have hp : p.val.natDegree = Module.finrank k E := by
    have h := ε.toLinearEquiv.finrank_eq
    rw [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank, AdjoinRoot.powerBasis_dim] at h
    exact h
  exact rawSymbol_finiteExtensionNorm_of_presentation n p ε (ih p (hp ▸ hd)) x

/-- Linear root presentations compare by the actual field equivalence and
identity transfer, in every Milnor weight. -/
theorem rawSymbol_polynomialNorm_of_degree_one (n : ℕ) (p : MonicIrreducible k)
    (hp : p.val.natDegree = 1) (x : MilnorK.K (AdjoinRoot p.val) n) :
    rawSymbol k n (polynomialNorm n p x) =
      corestriction (k := k) n (rawSymbol (AdjoinRoot p.val) n x) := by
  rw [polynomialNorm_eq_map_rootEvaluation n p hp]
  simpa only [corestriction_id, AddMonoidHom.id_apply, rootEvaluationEquiv_toRingHom] using
    (corestriction_rawSymbol_algEquiv (rootEvaluationEquiv p hp) n x).symm

/-- In a genuine finite Galois p-group ambient, the original norm and diagonal
transfer compare using only strict lower-degree comparisons over all fields. -/
theorem rawSymbol_polynomialNorm_of_pGroup_of_lower_degrees
    {Ω : Type u} [Field Ω] [Algebra k Ω] [FiniteDimensional k Ω] [IsGalois k Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[k] Ω))
    (n d : ℕ) (p : MonicIrreducible k) (hd : p.val.natDegree ≤ d)
    (g : AdjoinRoot p.val →ₐ[k] Ω)
    (ih : ∀ (L : Type u) [Field L] [CharZero L] (r : MonicIrreducible L),
      r.val.natDegree < d → ∀ y : MilnorK.K (AdjoinRoot r.val) n,
        rawSymbol L n (polynomialNorm n r y) =
          corestriction (k := L) n (rawSymbol (AdjoinRoot r.val) n y))
    (x : MilnorK.K (AdjoinRoot p.val) n) :
    rawSymbol k n (polynomialNorm n p x) =
      corestriction (k := k) n (rawSymbol (AdjoinRoot p.val) n x) := by
  by_cases hpone : p.val.natDegree = 1
  · exact rawSymbol_polynomialNorm_of_degree_one n p hpone x
  by_cases hpprime : p.val.natDegree.Prime
  · apply rawSymbol_polynomialNorm_prime_of_lower_degrees n p hpprime ?_ x
    intro r hr y
    exact ih (AdjoinRoot p.val) r (hr.trans_le hd) y
  have hdegree : Module.finrank k (AdjoinRoot p.val) = p.val.natDegree := by
    rw [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  have hdim : 1 < Module.finrank k (AdjoinRoot p.val) := by
    rw [hdegree]
    have hpos := p.property.2.natDegree_pos
    omega
  obtain ⟨R, hnormal, hrdegree, hupper⟩ :=
    IntermediateField.exists_normal_prime_subfield_of_embedding ℓ hG g hdim
  let : CharZero R := charZero_of_injective_algebraMap (algebraMap k R).injective
  let : FiniteDimensional R (AdjoinRoot p.val) :=
    FiniteDimensional.right k R (AdjoinRoot p.val)
  have hle : Module.finrank k R ≤ Module.finrank k (AdjoinRoot p.val) := by
    rw [← Module.finrank_mul_finrank k R (AdjoinRoot p.val)]
    exact Nat.le_mul_of_pos_right _ Module.finrank_pos
  have hlower : Module.finrank k R < d := by
    have hne : Module.finrank k R ≠ Module.finrank k (AdjoinRoot p.val) := by
      intro heq
      apply hpprime
      rw [← hdegree, ← heq, hrdegree]
      exact Fact.out
    exact (lt_of_le_of_ne hle hne).trans_le (hdegree ▸ hd)
  have hupper' : Module.finrank R (AdjoinRoot p.val) < d :=
    hupper.trans_le (hdegree ▸ hd)
  rw [← MilnorK.finiteExtensionNorm_adjoinRoot p n,
    MilnorK.finiteExtensionNorm_tower R (AdjoinRoot p.val) n x,
    rawSymbol_finiteExtensionNorm_of_lower_degrees n d hlower (ih k),
    rawSymbol_finiteExtensionNorm_of_lower_degrees n d hupper' (ih R)]
  exact DFunLike.congr_fun
    (corestriction_comp (k := k) (L := R) (E := AdjoinRoot p.val) n)
    (rawSymbol (AdjoinRoot p.val) n x)

end Motivic.DiagonalPolynomialNormInduction
