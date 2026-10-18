/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalPolynomialNormPGroupInduction
public import Motivic.Cohomology.Motivic.DiagonalRestrictionSylow
public import Aglib.FieldTheory.AdjoinRootSplitBranchEmbedding

/-!
# All-weight polynomial norms agree with actual diagonal corestriction

Strong degree induction is simultaneous over all characteristic-zero fields.
The whole scalar polynomial fiber is retained over each Sylow fixed field;
its branches embed in the actual p-group splitting ambient. Actual transfer
degree laws jointly detect equality on the original raw homology group.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace Motivic.DiagonalPolynomialNormComparisonAll
open PresheafWithTransfers DiagonalMilnorSymbol DiagonalCorestriction
open MilnorK.PolynomialResidue MilnorK.PolynomialNorm
open Polynomial Polynomial.LocalResidue AdjoinRoot
local instance rootFinite (F : Type u) [Field F] (p : MonicIrreducible F) :
    Module.Finite F (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot
local instance rootCharZero (F : Type u) [Field F] [CharZero F]
    (p : MonicIrreducible F) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot p.val)).injective

/-- The actual full branch formula compares restrictions to a p-group splitting ambient
under only the displayed strict lower-degree comparison premise. -/
theorem restriction_comparison_of_pGroup_of_lower_degrees
    {k L Ω : Type u} [Field k] [CharZero k] [Field L] [CharZero L] [Field Ω]
    [Algebra k L] [Algebra L Ω] [Algebra k Ω] [IsScalarTower k L Ω]
    [FiniteDimensional L Ω] [IsGalois L Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[L] Ω))
    (n d : ℕ) (p : MonicIrreducible k) (hd : p.val.natDegree ≤ d)
    (hsplit : (p.val.map (algebraMap k Ω)).Splits)
    (ih : ∀ (A : Type u) [Field A] [CharZero A] (r : MonicIrreducible A),
      r.val.natDegree < d → ∀ y : MilnorK.K (AdjoinRoot r.val) n,
        rawSymbol A n (polynomialNorm n r y) =
          corestriction (k := A) n (rawSymbol (AdjoinRoot r.val) n y))
    (x : MilnorK.K (AdjoinRoot p.val) n) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap (algebraMap k L) n) n
        (rawSymbol k n (polynomialNorm n p x)) =
      HomologicalComplex.homologyMap (motivicRawBaseComplexMap (algebraMap k L) n) n
        (corestriction (k := k) n (rawSymbol (AdjoinRoot p.val) n x)) := by
  classical
  rw [DiagonalFieldChange.rawSymbol_fieldChange, polynomialNorm_restrict,
    DiagonalMilnorNormBaseChange.corestriction_rawSymbol_baseChange_algebraMap]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  let rb : IrreducibleBranch (p.val.map (algebraMap k L)) :=
    ⟨r.val, (mem_placesAbove (algebraMap k L) p r.val).mp r.property⟩
  have hdeg : r.val.val.natDegree ≤ d := by
    have hle := natDegree_le_of_dvd rb.property (Polynomial.map_ne_zero p.property.2.ne_zero)
    rw [natDegree_map] at hle
    exact hle.trans hd
  obtain ⟨⟨g⟩, _⟩ := AdjoinRoot.nonempty_algHom_branch_of_splits p.val
    p.property.2.ne_zero hsplit rb
  exact DiagonalPolynomialNormInduction.rawSymbol_polynomialNorm_of_pGroup_of_lower_degrees
    ℓ hG n d r.val hdeg g ih _

/-- Genuine all-degree polynomial norm/corestriction comparison on original raw homology.
No comparison, normality, or symbol-surjectivity hypothesis remains. -/
theorem rawSymbol_polynomialNorm {k : Type u} [Field k] [CharZero k]
    (n : ℕ) (p : MonicIrreducible k) (x : MilnorK.K (AdjoinRoot p.val) n) :
    rawSymbol k n (polynomialNorm n p x) =
      corestriction (k := k) n (rawSymbol (AdjoinRoot p.val) n x) := by
  classical
  have main : ∀ d : ℕ, ∀ (A : Type u) [Field A] [CharZero A]
      (r : MonicIrreducible A), r.val.natDegree = d →
      ∀ y : MilnorK.K (AdjoinRoot r.val) n,
        rawSymbol A n (polynomialNorm n r y) =
          corestriction (k := A) n (rawSymbol (AdjoinRoot r.val) n y) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro A _ _ r hdeg y
      let Ω := r.val.SplittingField
      let : IsGalois A Ω := ⟨⟩
      apply DiagonalRestrictionSylow.eq_of_sylow_restrictions A Ω n
      intro ℓ hℓ
      let : Fact ℓ.Prime := ⟨hℓ⟩
      let S : Sylow ℓ (Ω ≃ₐ[A] Ω) := Classical.arbitrary _
      let L := IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[A] Ω))
      let : CharZero L := charZero_of_injective_algebraMap (algebraMap A L).injective
      refine ⟨S, ?_⟩
      apply restriction_comparison_of_pGroup_of_lower_degrees
        (Ω := Ω) ℓ (IntermediateField.isPGroup_aut_over_sylow_fixedField ℓ S)
        n d r hdeg.le (SplittingField.splits r.val) ?_ y
      intro B _ _ a ha z
      exact ih a.val.natDegree ha B a rfl z
  exact main p.val.natDegree k p rfl x

/-- The original finite extension, not just a chosen polynomial root field, has
actual all-weight norm/corestriction compatibility. -/
theorem rawSymbol_finiteExtensionNorm
    {k E : Type u} [Field k] [CharZero k] [Field E] [CharZero E]
    [Algebra k E] [FiniteDimensional k E] (n : ℕ) (x : MilnorK.K E n) :
    rawSymbol k n (MilnorK.finiteExtensionNorm k E n x) =
      corestriction (k := k) n (rawSymbol E n x) :=
  DiagonalPolynomialNormInduction.rawSymbol_finiteExtensionNorm_of_presentation n
    (MilnorK.finiteNormPolynomial k E) (MilnorK.finiteNormPresentation k E)
    (rawSymbol_polynomialNorm n _) x

end Motivic.DiagonalPolynomialNormComparisonAll
