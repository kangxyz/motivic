/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.AdjoinRootScalarBranches
public import Motivic.Cohomology.Motivic.WeightOneFundamentalNorm

/-!
# Whole scalar polynomial fibers and their actual branch cycles

The literal mapped polynomial quotient is the scheme-theoretic scalar
pullback, with both projection equations proved from the tensor equivalence.
For a squarefree monic polynomial its full fundamental cycle is the sum of
finite pushforwards from its literal irreducible quotient fields. No branch,
residue extension, or local multiplicity is discarded.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial AdjoinRoot
open scoped BigOperators

universe u

namespace Motivic.AdjoinRootScalarBranches

open WeightOneFundamentalNorm

variable {k L : Type u} [Field k] [Field L]

/-- The whole scalar-extended polynomial scheme is the actual scalar pullback. -/
def scalarSchemeIso (φ : k →+* L) (p : k[X]) :
    Spec (.of (AdjoinRoot (p.map φ))) ≅
      pullback (Spec.map (CommRingCat.ofHom φ))
        (Spec.map (CommRingCat.ofHom (AdjoinRoot.of p))) := by
  let := φ.toAlgebra
  exact Scheme.Spec.mapIso
      (scalarExtensionEquiv (L := L) p).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso k L (AdjoinRoot p)).symm

/-- The first projection is the original target-field scalar structure. -/
@[reassoc]
theorem scalarSchemeIso_hom_fst (φ : k →+* L) (p : k[X]) :
    (scalarSchemeIso φ p).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of (p.map φ))) := by
  let := φ.toAlgebra
  change ((Scheme.Spec.mapIso
      (scalarExtensionEquiv (L := L) p).toRingEquiv.toCommRingCatIso.op).hom ≫
    (pullbackSpecIso k L (AdjoinRoot p)).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst']
  change Spec.map (CommRingCat.ofHom (scalarExtensionEquiv (L := L) p).toRingHom) ≫
    Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (scalarExtensionEquiv (L := L) p).commutes

/-- The second projection is the literal polynomial coefficient-extension map. -/
@[reassoc]
theorem scalarSchemeIso_hom_snd (φ : k →+* L) (p : k[X]) :
    (scalarSchemeIso φ p).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (scalarMap φ p)) := by
  let := φ.toAlgebra
  change ((Scheme.Spec.mapIso
      (scalarExtensionEquiv (L := L) p).toRingEquiv.toCommRingCatIso.op).hom ≫
    (pullbackSpecIso k L (AdjoinRoot p)).inv) ≫ pullback.snd _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_snd]
  change Spec.map (CommRingCat.ofHom (scalarExtensionEquiv (L := L) p).toRingHom) ≫
    Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact scalarExtensionEquiv_comp_includeRight p

/-- The scalar square on the original quotient rings is scheme-theoretically
Cartesian for every coefficient-field homomorphism. -/
theorem scalar_isPullback (φ : k →+* L) (p : k[X]) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (AdjoinRoot.of (p.map φ))))
      (Spec.map (CommRingCat.ofHom (scalarMap φ p)))
      (Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom (AdjoinRoot.of p))) := by
  apply (IsPullback.of_hasPullback _ _).of_iso'
    (scalarSchemeIso φ p) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.comp_id] using scalarSchemeIso_hom_fst φ p
  · simpa only [Iso.refl_hom, Category.comp_id] using scalarSchemeIso_hom_snd φ p
  · simp
  · simp

/-- The literal finite closed immersion of an irreducible polynomial branch. -/
def branchMap (p : k[X]) (q : IrreducibleBranch p) :
    Spec (.of (AdjoinRoot q.val.val)) ⟶ Spec (.of (AdjoinRoot p)) :=
  Spec.map (CommRingCat.ofHom (divisorMap p q.val.val q.property))

instance (p : k[X]) (q : IrreducibleBranch p) : IsClosedImmersion (branchMap p q) :=
  IsClosedImmersion.spec_of_surjective _ (divisorMap_surjective p q.val.val q.property)

/-- A branch generic point maps to its original maximal kernel. -/
theorem branchMap_genericPoint (p : k[X]) (q : IrreducibleBranch p) :
    branchMap p q (genericPoint (Spec (.of (AdjoinRoot q.val.val)))) =
      (branchMaximal p q).toPrimeSpectrum := by
  apply PrimeSpectrum.ext
  change Ideal.comap (divisorMap p q.val.val q.property)
    (genericPoint (Spec (.of (AdjoinRoot q.val.val)))).asIdeal = _
  have h : (genericPoint (Spec (.of (AdjoinRoot q.val.val)))).asIdeal = ⊥ :=
    Ideal.eq_bot_of_prime _
  rw [h]
  rfl

/-- A literal irreducible quotient contributes its actual reduced closed
support with coefficient one. -/
theorem finitePushforward_branchMap (p : k[X]) (q : IrreducibleBranch p) :
    IntegralCycle.finitePushforward (branchMap p q)
      (fundamentalCycle (Spec (.of (AdjoinRoot q.val.val)))) =
        Finsupp.single (quotientSupport (branchMaximal p q)) 1 := by
  rw [fundamentalCycle_of_isIntegral, IntegralCycle.finitePushforward_single,
    residueDegree_of_surjectiveOnStalks, Nat.cast_one, mul_one]
  congr 1
  apply IntegralClosedSubscheme.point_injective
  rw [IntegralClosedSubscheme.point_finiteImage,
    IntegralClosedSubscheme.point_pointClosure, branchMap_genericPoint, quotientSupport_point]

/-- The full fundamental cycle of the original squarefree polynomial algebra
is the sum of the finite pushforwards from every literal factor field. -/
theorem fundamentalCycle_eq_sum_branches (p : k[X]) (hp : p.Monic) (hs : Squarefree p) :
    let : Module.Finite k (AdjoinRoot p) := hp.finite_adjoinRoot
    let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
    let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
    let : Fintype (IrreducibleBranch p) :=
      Fintype.ofEquiv (MaximalSpectrum (AdjoinRoot p)) (branchEquivMaximal p hp.ne_zero).symm
    fundamentalCycle (Spec (.of (AdjoinRoot p))) =
      ∑ q : IrreducibleBranch p, IntegralCycle.finitePushforward (branchMap p q)
        (fundamentalCycle (Spec (.of (AdjoinRoot q.val.val)))) := by
  classical
  let : Module.Finite k (AdjoinRoot p) := hp.finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite k _
  let : Fintype (MaximalSpectrum (AdjoinRoot p)) := Fintype.ofFinite _
  let : Fintype (IrreducibleBranch p) :=
    Fintype.ofEquiv (MaximalSpectrum (AdjoinRoot p)) (branchEquivMaximal p hp.ne_zero).symm
  dsimp only
  rw [fundamentalCycle_affine_eq_sum (k := k)]
  symm
  apply Fintype.sum_equiv (branchEquivMaximal p hp.ne_zero)
  intro q
  rw [finitePushforward_branchMap, local_length_eq_one_of_squarefree p hp hs]
  rfl

/-- The full scalar-extended fundamental cycle has one copy of every actual
factor branch, for every characteristic-zero coefficient extension. -/
theorem scalar_fundamentalCycle_eq_sum_branches [CharZero k]
    (φ : k →+* L) (p : k[X]) (hp : p.Monic) [Fact (Irreducible p)] :
    let : Module.Finite L (AdjoinRoot (p.map φ)) := (hp.map φ).finite_adjoinRoot
    let : IsArtinianRing (AdjoinRoot (p.map φ)) := .of_finite L _
    let : Fintype (MaximalSpectrum (AdjoinRoot (p.map φ))) := Fintype.ofFinite _
    let : Fintype (IrreducibleBranch (p.map φ)) :=
      Fintype.ofEquiv (MaximalSpectrum (AdjoinRoot (p.map φ)))
        (branchEquivMaximal (p.map φ) (hp.map φ).ne_zero).symm
    fundamentalCycle (Spec (.of (AdjoinRoot (p.map φ)))) =
      ∑ q : IrreducibleBranch (p.map φ),
        IntegralCycle.finitePushforward (branchMap (p.map φ) q)
          (fundamentalCycle (Spec (.of (AdjoinRoot q.val.val)))) :=
  fundamentalCycle_eq_sum_branches (p.map φ) (hp.map φ)
    (Polynomial.LocalResidue.squarefree_map φ p)

/-- The branch projection composed with the whole scalar projection is the
original concrete polynomial residue-field map. -/
theorem branchMap_scalarMap (φ : k →+* L) (p : k[X]) [Fact (Irreducible p)]
    (q : IrreducibleBranch (p.map φ)) :
    branchMap (p.map φ) q ≫ Spec.map (CommRingCat.ofHom (scalarMap φ p)) =
      Spec.map (CommRingCat.ofHom
        (Polynomial.LocalResidue.adjoinRootMap φ p q.val.val q.property)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact divisorMap_comp_scalarMap φ p q.val.val q.property

end Motivic.AdjoinRootScalarBranches
