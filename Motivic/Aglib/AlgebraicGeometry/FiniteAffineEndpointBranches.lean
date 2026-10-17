/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.FiniteCurveBranchOrders
public import Motivic.Aglib.RingTheory.AdicCompletion.DedekindBranches

/-!
# Actual affine endpoint points and original Dedekind ideal branches

The full scheme-theoretic endpoint fiber is reindexed by the original prime
ideal factors of the image of `(X - C a)`. This is a bijection of all points,
not a choice of a branch list. The ambient prime is unchanged literally.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Motivic
open scoped Polynomial

universe u

namespace AlgebraicGeometry.FiniteAffineEndpointBranches

variable {k : Type u} [Field k] (S : Type u) [CommRing S] [IsDedekindDomain S]
  [Algebra k[X] S] [FaithfulSMul k[X] S]

open FiniteFlatCurve

/-- The original affine-line structural morphism. -/
abbrev baseMap : Spec (.of S) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] S))

/-- The original endpoint ideal, before passing to any localization. -/
abbrev endpointIdeal (a : k) : Ideal S :=
  (Ideal.span {Polynomial.X - Polynomial.C a}).map (algebraMap k[X] S)

omit [IsDedekindDomain S] in
/-- Faithfulness keeps the literal endpoint ideal nonzero. -/
theorem endpointIdeal_ne_bot (a : k) : endpointIdeal S a ≠ ⊥ := by
  simp only [endpointIdeal, Ideal.map_span, Set.image_singleton, ne_eq,
    Ideal.span_singleton_eq_bot]
  exact (FaithfulSMul.algebraMap_eq_zero_iff k[X] S).not.mpr (Polynomial.X_sub_C_ne_zero a)

omit [IsDedekindDomain S] [FaithfulSMul k[X] S] in
/-- The actual closed fiber includes exactly the primes containing the unchanged
endpoint equation. This does not assume reducedness of that fiber. -/
theorem mem_range_fiberInclusion_iff (a : k) (p : Spec (.of S)) :
    p ∈ Set.range (fiberInclusion (baseMap S) a) ↔
      algebraMap k[X] S (Polynomial.X - Polynomial.C a) ∈ p.asIdeal := by
  let : Algebra S ((Spec (.of S)).presheaf.stalk p) :=
    (StructureSheaf.toStalk S p).hom.toAlgebra
  have : IsLocalization.AtPrime ((Spec (.of S)).presheaf.stalk p) p.asIdeal :=
    inferInstanceAs (IsLocalization.AtPrime ((Spec.structureSheaf S).presheaf.stalk p)
      p.asIdeal)
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff
    ((Spec (.of S)).presheaf.stalk p) p.asIdeal]
  change _ ↔ StructureSheaf.toStalk S p _ ∈ _
  rw [← scalar_specMap]
  constructor
  · rintro ⟨x, rfl⟩
    exact scalar_mem_maximalIdeal (baseMap S) a x
  · intro hp
    by_contra hn
    have ht := closedImmersion_ker_stalk_eq_top (fiberInclusion (baseMap S) a) hn
    rw [fiberInclusion_stalk] at ht
    have hle : Ideal.ofList [scalar (baseMap S) a p] ≤
        IsLocalRing.maximalIdeal ((Spec (.of S)).presheaf.stalk p) := by
      rw [Ideal.ofList_singleton]
      exact (Ideal.span_singleton_le_iff_mem _).mpr hp
    rw [ht] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)

attribute [local instance] Classical.decEq

/-- Every actual fiber point gives its literal original prime ideal factor. -/
def toBranch (a : k) (x : fiber (baseMap S) a) :
    AdicCompletion.IdealBranch (endpointIdeal S a) :=
  ⟨(fiberInclusion (baseMap S) a x).asIdeal, by
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff (endpointIdeal_ne_bot S a)]
    refine ⟨inferInstance, ?_⟩
    rw [endpointIdeal, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
    exact (mem_range_fiberInclusion_iff S a _).mp ⟨x, rfl⟩⟩

@[simp] theorem toBranch_val (a : k) (x : fiber (baseMap S) a) :
    (toBranch S a x).val = (fiberInclusion (baseMap S) a x).asIdeal := rfl

/-- No actual endpoint point is lost and no prime factor is repeated. -/
theorem toBranch_bijective (a : k) : Function.Bijective (toBranch S a) := by
  constructor
  · intro x y h
    apply (fiberInclusion (baseMap S) a).isEmbedding.injective
    exact PrimeSpectrum.ext (congrArg Subtype.val h)
  · intro q
    let p : Spec (.of S) := ⟨q.val, inferInstance⟩
    have hq : endpointIdeal S a ≤ q.val :=
      ((Ideal.mem_normalizedFactors_iff (endpointIdeal_ne_bot S a)).mp
        (Multiset.mem_toFinset.mp q.property)).2
    simp only [endpointIdeal, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_le_iff_mem] at hq
    obtain ⟨x, hx⟩ := (mem_range_fiberInclusion_iff S a p).mpr hq
    refine ⟨x, Subtype.ext ?_⟩
    exact congrArg PrimeSpectrum.asIdeal hx

/-- The actual full endpoint fiber and all original ideal branches are the same
finite indexing set, through their unchanged ambient prime. -/
def pointEquiv (a : k) :
    fiber (baseMap S) a ≃ AdicCompletion.IdealBranch (endpointIdeal S a) :=
  Equiv.ofBijective (toBranch S a) (toBranch_bijective S a)

@[simp] theorem pointEquiv_apply_val (a : k) (x : fiber (baseMap S) a) :
    (pointEquiv S a x).val = (fiberInclusion (baseMap S) a x).asIdeal := rfl

/-- The inverse also returns the same prime, not an isomorphic replacement. -/
@[simp] theorem pointEquiv_symm_asIdeal (a : k)
    (q : AdicCompletion.IdealBranch (endpointIdeal S a)) :
    (fiberInclusion (baseMap S) a ((pointEquiv S a).symm q)).asIdeal = q.val :=
  congrArg Subtype.val ((pointEquiv S a).apply_symm_apply q)

/-- The ambient prime point itself is unchanged under inverse reindexing. -/
@[simp] theorem pointEquiv_symm_point (a : k)
    (q : AdicCompletion.IdealBranch (endpointIdeal S a)) :
    fiberInclusion (baseMap S) a ((pointEquiv S a).symm q) =
      (⟨q.val, inferInstance⟩ : PrimeSpectrum S) :=
  PrimeSpectrum.ext (pointEquiv_symm_asIdeal S a q)

/-- Finiteness is a property of the actual point set, with no supplied enumeration. -/
instance fiber_finite (a : k) : Finite (fiber (baseMap S) a) :=
  Finite.of_equiv _ (pointEquiv S a).symm

/-- The closed fiber's residue field is identified by its actual inclusion map,
not by a chosen abstract isomorphism. -/
def fiberResidueEquiv (a : k) (x : fiber (baseMap S) a) :
    (Spec (.of S)).residueField (fiberInclusion (baseMap S) a x) ≃+*
      (fiber (baseMap S) a).residueField x :=
  RingEquiv.ofBijective ((fiberInclusion (baseMap S) a).residueFieldMap x).hom
    ⟨((fiberInclusion (baseMap S) a).residueFieldMap x).hom.injective,
      Motivic.residueFieldMap_surjective (fiberInclusion (baseMap S) a) x⟩

omit [IsDedekindDomain S] [FaithfulSMul k[X] S] in
/-- This equivalence is literally the map induced by the closed immersion. -/
@[simp] theorem fiberResidueEquiv_toRingHom (a : k) (x : fiber (baseMap S) a) :
    (fiberResidueEquiv S a x).toRingHom =
      ((fiberInclusion (baseMap S) a).residueFieldMap x).hom := rfl

omit [IsDedekindDomain S] [FaithfulSMul k[X] S] in
/-- Original scalar reduction commutes with the actual fiber-inclusion stalk map. -/
theorem fiberResidueEquiv_scalar (a : k) (x : fiber (baseMap S) a) (s : S) :
    fiberResidueEquiv S a x
        (IsLocalRing.residue ((Spec (.of S)).presheaf.stalk
          (fiberInclusion (baseMap S) a x))
          (StructureSheaf.toStalk S (fiberInclusion (baseMap S) a x) s)) =
      IsLocalRing.residue ((fiber (baseMap S) a).presheaf.stalk x)
        ((fiberInclusion (baseMap S) a).stalkMap x
          (StructureSheaf.toStalk S (fiberInclusion (baseMap S) a x) s)) :=
  IsLocalRing.ResidueField.map_residue _ _

omit [IsDedekindDomain S] [FaithfulSMul k[X] S] in
/-- The same equivalence respects the original global coordinate restriction
and the actual fiber evaluation, including on nonreduced endpoint fibers. -/
theorem fiberResidueEquiv_Γevaluation (a : k) (x : fiber (baseMap S) a)
    (s : (Spec (.of S)).presheaf.obj (Opposite.op ⊤)) :
    fiberResidueEquiv S a x
        ((Spec (.of S)).Γevaluation (fiberInclusion (baseMap S) a x) s) =
      (fiber (baseMap S) a).Γevaluation x
        ((fiberInclusion (baseMap S) a).appTop s) :=
  Scheme.Γevaluation_naturality_apply (fiberInclusion (baseMap S) a) x s

end AlgebraicGeometry.FiniteAffineEndpointBranches
