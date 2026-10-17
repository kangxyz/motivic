/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.LengthEuler
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# Euler length additivity from actual homology exact sequences

Images in a long exact sequence have finite length because they are quotients
of its finite-length terms. Exactness splits each middle length into its two
adjacent image lengths. The signed image lengths cancel, including the
connecting homomorphisms of an actual short exact sequence of complexes.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Motivic.LengthEuler

variable {R : Type u} [Ring R]

/-- The image of a map from a finite-length module has finite length. -/
theorem range_finite_length {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hM : Module.length R M ≠ ⊤) :
    Module.length R (LinearMap.range f) ≠ ⊤ :=
  ne_top_of_le_ne_top hM (Module.length_le_of_surjective f.rangeRestrict
    (LinearMap.range_eq_top.mp f.range_rangeRestrict))

/-- Integer length of an actual linear-map image, with finite length certified. -/
noncomputable def imageLength {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hM : Module.length R M ≠ ⊤) : ℤ :=
  integerLength (LinearMap.range f) (range_finite_length f hM)

/-- Exactness splits the middle integer length into its adjacent image lengths. -/
theorem integerLength_exact_pair {U V W : Type v}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (f : U →ₗ[R] V) (g : V →ₗ[R] W)
    (hex : Function.Exact f g) (hU : Module.length R U ≠ ⊤)
    (hV : Module.length R V ≠ ⊤) :
    integerLength V hV = imageLength f hU + imageLength g hV := by
  have he : Function.Exact (LinearMap.range f).subtype g.rangeRestrict := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict]
    exact LinearMap.exact_iff.mp hex
  have hl := Module.length_eq_add_of_exact (LinearMap.range f).subtype g.rangeRestrict
    (Submodule.subtype_injective _) (LinearMap.range_eq_top.mp g.range_rangeRestrict) he
  simp only [integerLength, imageLength]
  rw [hl, ENat.toNat_add (range_finite_length f hU) (range_finite_length g hV), Nat.cast_add]

variable {ι : Type w}

/-- A family of image lengths is finitely supported whenever its source is. -/
theorem finiteSupport_imageLength {X Y : ι → ModuleCat.{v} R}
    (f : ∀ i, X i ⟶ Y i) (hX : FiniteLengthSupport X) :
    (fun i => imageLength (f i).hom (hX.finite_length i)).HasFiniteSupport := by
  apply hX.finite_support.subset
  intro i hi
  contrapose! hi
  simp only [Function.mem_support, not_not] at hi ⊢
  have hl : Module.length R (LinearMap.range (f i).hom) = 0 := by
    apply le_antisymm _ bot_le
    exact (Module.length_le_of_surjective (f i).hom.rangeRestrict
      (LinearMap.range_eq_top.mp (f i).hom.range_rangeRestrict)).trans_eq hi
  simp [imageLength, integerLength, hl]

/-- A finite signed sum splits into image sums along an exact family of pairs. -/
theorem signedLengthSum_exact_pair {X Y Z : ι → ModuleCat.{v} R}
    (f : ∀ i, X i ⟶ Y i) (g : ∀ i, Y i ⟶ Z i)
    (hex : ∀ i, Function.Exact (f i) (g i))
    (hX : FiniteLengthSupport X) (hY : FiniteLengthSupport Y) (sign : ι → ℤ) :
    signedLengthSum Y sign hY =
      (∑ᶠ i, sign i * imageLength (f i).hom (hX.finite_length i)) +
      ∑ᶠ i, sign i * imageLength (g i).hom (hY.finite_length i) := by
  unfold signedLengthSum
  simp_rw [integerLength_exact_pair (f _).hom (g _).hom (hex _)
    (hX.finite_length _) (hY.finite_length _), mul_add]
  exact finsum_add_distrib
    (Function.HasFiniteSupport.mul_right sign (finiteSupport_imageLength f hX))
    (Function.HasFiniteSupport.mul_right sign (finiteSupport_imageLength g hY))

/-- Translating an integer-indexed alternating sum by one changes its sign. -/
theorem alternatingSum_succ (a : ℤ → ℤ) :
    (∑ᶠ i, (i.negOnePow : ℤ) * a (i + 1)) =
      -(∑ᶠ i, (i.negOnePow : ℤ) * a i) := by
  have he := finsum_comp (fun i : ℤ => i + 1)
    (show Function.Bijective (fun i : ℤ => i + 1) from (Equiv.addRight 1).bijective)
    (g := fun i : ℤ => (i.negOnePow : ℤ) * a i)
  simp only [Int.negOnePow_succ, Units.val_neg, neg_mul, finsum_neg_distrib] at he
  exact neg_eq_iff_eq_neg.mp he

/-- A short exact sequence of actual cochain complexes has additive homology
Euler length whenever all three homologies have finite length and finite support.
The proof uses the connecting maps in its genuine long exact homology sequence. -/
theorem cochainEuler_add_of_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{v} R) ℤ)) (hS : S.ShortExact)
    (hA : FiniteHomology S.X₁) (hB : FiniteHomology S.X₂) (hC : FiniteHomology S.X₃) :
    cochainEuler S.X₂ hB = cochainEuler S.X₁ hA + cochainEuler S.X₃ hC := by
  let f := fun i => HomologicalComplex.homologyMap S.f i
  let g := fun i => HomologicalComplex.homologyMap S.g i
  let δ := fun i : ℤ => hS.δ i (i + 1) rfl
  have hf : ∀ i, Function.Exact (f i) (g i) := fun i =>
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₂ i)
  have hg : ∀ i, Function.Exact (g i) (δ i) := fun i =>
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₃ i (i + 1) rfl)
  have hδ : ∀ i, Function.Exact (δ i) (f (i + 1)) := fun i =>
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₁ i (i + 1) rfl)
  have hA' := hA.comp (fun i : ℤ => i + 1) (Equiv.addRight 1).injective
  have hb := signedLengthSum_exact_pair f g hf hA hB (fun i => (i.negOnePow : ℤ))
  have hc := signedLengthSum_exact_pair g δ hg hB hC (fun i => (i.negOnePow : ℤ))
  have ha := signedLengthSum_exact_pair δ (fun i => f (i + 1)) hδ hC hA'
    (fun i => (i.negOnePow : ℤ))
  change (∑ᶠ i, (i.negOnePow : ℤ) * integerLength (S.X₁.homology (i + 1))
    (hA.finite_length (i + 1))) = _ at ha
  rw [alternatingSum_succ (fun i => integerLength (S.X₁.homology i) (hA.finite_length i)),
    alternatingSum_succ (fun i => imageLength (f i).hom (hA.finite_length i))] at ha
  change cochainEuler S.X₂ hB = _ at hb
  change cochainEuler S.X₃ hC = _ at hc
  change -cochainEuler S.X₁ hA = _ at ha
  omega

end Motivic.LengthEuler
