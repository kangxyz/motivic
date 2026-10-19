/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.GenericRatioNormCycle
public import Motivic.Aglib.AlgebraicGeometry.Divisors.Order.PrincipalOrderCancellation

/-! # Signed comparison of two original generic section norms

Both terms are the whole original zero schemes pushed along their original finite
maps. The specified unit representative is retained; its full-boundary properties
are not inferred from the germ equation.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.GenericRatioNormArithmetic`.
Incoming project consumers:
`Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.BoundaryFunctional.NormCommuting`,
`Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.BoundaryFunctional.NormComparison`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules.Invertible AlgebraicGeometry.FiniteSchemeNormBaseChange
universe u
namespace AlgebraicGeometry.Scheme

private theorem genericRatioNorm_ne_zero {C T : Scheme.{u}} [IsIntegral T]
    (f : C ⟶ T) [IsFinite f] (L : LineBundle C)
    (a b : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono a] [Mono b] :
    Scheme.genericFiberLineRatioNorm f L a b ≠ 0 := by
  let G := pullback f (T.fromSpecStalk (genericPoint T))
  let q := pullback.snd f (T.fromSpecStalk (genericPoint T))
  let : Algebra T.functionField Γ(G, ⊤) := (scalarMap q).toAlgebra
  let : Module.Finite T.functionField Γ(G, ⊤) := sections_finite q
  exact ((Scheme.genericFiberLineRatioUnit f L a b).isUnit.map
    (Algebra.norm T.functionField)).ne_zero

/-- Subtraction of two original pushed section divisors is the principal cycle
of the quotient of their canonical norms. No desired cycle equality is supplied. -/
theorem residuePushforward_zeroCycles_sub_eq_principalOrderCycle_ratio
    {T : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
    (C : Fin 2 → Scheme.{u}) (f : ∀ i, C i ⟶ T) [∀ i, IsFinite (f i)]
    (hnormal : ∀ (U : T.Opens), IsAffineOpen U → Nonempty U →
      IsIntegrallyClosed Γ(T, U))
    (hfree : ∀ i (x : T), ∃ (U : T.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      (let : Algebra Γ(T, U) Γ(Limits.pullback (f i) hU.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (f i) hU.fromSpec)).toAlgebra
       Module.Free Γ(T, U) Γ(Limits.pullback (f i) hU.fromSpec, ⊤)))
    (L : ∀ i, LineBundle (C i))
    (a b : ∀ i, (L i).val ⟶ SheafOfModules.unit (C i).ringCatSheaf)
    [∀ i, Mono (a i)] [∀ i, Mono (b i)]
    (W : T.Opens) [Nonempty W] (r : Γ(T, W)) (hr : IsUnit r)
    (hg : T.germToFunctionField W r =
      Scheme.genericFiberLineRatioNorm (f 0) (L 0) (a 0) (b 0) /
        Scheme.genericFiberLineRatioNorm (f 1) (L 1) (a 1) (b 1)) :
    let : ∀ i, IsNoetherian (C i) := fun i =>
        _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (f i)
    let : ∀ i, IsNoetherian (Scheme.Modules.Hom.zeroScheme (a i)) :=
      fun i => _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
          (Scheme.Modules.Hom.zeroInclusion (a i))
    let : ∀ i, IsNoetherian (Scheme.Modules.Hom.zeroScheme (b i)) :=
      fun i => _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
          (Scheme.Modules.Hom.zeroInclusion (b i))
    let z := fun i => _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward (f i)
      (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
          (Scheme.Modules.Hom.zeroInclusion (a i))
          (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme (a
              i))) -
        _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
            (Scheme.Modules.Hom.zeroInclusion (b i))
          (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme (b
              i))))
    z 0 - z 1 = _root_.AlgebraicGeometry.Scheme.principalOrderCycle W r hr := by
  let : ∀ i, IsNoetherian (C i) := fun i =>
      _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (f i)
  let : ∀ i, IsNoetherian (Scheme.Modules.Hom.zeroScheme (a i)) :=
    fun i => _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
        (Scheme.Modules.Hom.zeroInclusion (a i))
  let : ∀ i, IsNoetherian (Scheme.Modules.Hom.zeroScheme (b i)) :=
    fun i => _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
        (Scheme.Modules.Hom.zeroInclusion (b i))
  dsimp only
  ext x
  rw [Finsupp.sub_apply, _root_.AlgebraicGeometry.Scheme.principalOrderCycle_apply, hg]
  rw [_root_.AlgebraicGeometry.Scheme.residuePushforward_zeroCycle_sub_eq_ord_genericRatioNorm (f 0)
      hnormal (hfree 0),
    _root_.AlgebraicGeometry.Scheme.residuePushforward_zeroCycle_sub_eq_ord_genericRatioNorm (f 1)
        hnormal (hfree 1)]
  have h := T.ord_add_ord_ratio
    (Scheme.genericFiberLineRatioNorm (f 1) (L 1) (a 1) (b 1))
    (Scheme.genericFiberLineRatioNorm (f 0) (L 0) (a 0) (b 0))
    (genericRatioNorm_ne_zero (f 1) (L 1) (a 1) (b 1))
    (genericRatioNorm_ne_zero (f 0) (L 0) (a 0) (b 0)) x
  omega

/-- Addition of the original pushed section divisors has the product norm,
with the correction sign retained in the original numerator and denominator. -/
theorem residuePushforward_zeroCycles_add_eq_principalOrderCycle_product
    {T : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
    (C : Fin 2 → Scheme.{u}) (f : ∀ i, C i ⟶ T) [∀ i, IsFinite (f i)]
    (hnormal : ∀ (U : T.Opens), IsAffineOpen U → Nonempty U →
      IsIntegrallyClosed Γ(T, U))
    (hfree : ∀ i (x : T), ∃ (U : T.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      (let : Algebra Γ(T, U) Γ(Limits.pullback (f i) hU.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (f i) hU.fromSpec)).toAlgebra
       Module.Free Γ(T, U) Γ(Limits.pullback (f i) hU.fromSpec, ⊤)))
    (L : ∀ i, LineBundle (C i))
    (a b : ∀ i, (L i).val ⟶ SheafOfModules.unit (C i).ringCatSheaf)
    [∀ i, Mono (a i)] [∀ i, Mono (b i)]
    (W : T.Opens) [Nonempty W] (r : Γ(T, W)) (hr : IsUnit r)
    (hg : T.germToFunctionField W r =
      Scheme.genericFiberLineRatioNorm (f 0) (L 0) (a 0) (b 0) *
        Scheme.genericFiberLineRatioNorm (f 1) (L 1) (a 1) (b 1)) :
    let : ∀ i, IsNoetherian (C i) := fun i =>
        _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (f i)
    let : ∀ i, IsNoetherian (Scheme.Modules.Hom.zeroScheme (a i)) :=
      fun i => _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
          (Scheme.Modules.Hom.zeroInclusion (a i))
    let : ∀ i, IsNoetherian (Scheme.Modules.Hom.zeroScheme (b i)) :=
      fun i => _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
          (Scheme.Modules.Hom.zeroInclusion (b i))
    let z := fun i => _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward (f i)
      (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
          (Scheme.Modules.Hom.zeroInclusion (a i))
          (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme (a
              i))) -
        _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
            (Scheme.Modules.Hom.zeroInclusion (b i))
          (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle (Scheme.Modules.Hom.zeroScheme (b
              i))))
    z 0 + z 1 = _root_.AlgebraicGeometry.Scheme.principalOrderCycle W r hr := by
  let : ∀ i, IsNoetherian (C i) := fun i =>
      _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (f i)
  let : ∀ i, IsNoetherian (Scheme.Modules.Hom.zeroScheme (a i)) :=
    fun i => _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
        (Scheme.Modules.Hom.zeroInclusion (a i))
  let : ∀ i, IsNoetherian (Scheme.Modules.Hom.zeroScheme (b i)) :=
    fun i => _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
        (Scheme.Modules.Hom.zeroInclusion (b i))
  dsimp only
  ext x
  rw [Finsupp.add_apply, _root_.AlgebraicGeometry.Scheme.principalOrderCycle_apply, hg]
  rw [_root_.AlgebraicGeometry.Scheme.residuePushforward_zeroCycle_sub_eq_ord_genericRatioNorm (f 0)
      hnormal (hfree 0),
    _root_.AlgebraicGeometry.Scheme.residuePushforward_zeroCycle_sub_eq_ord_genericRatioNorm (f 1)
        hnormal (hfree 1)]
  exact (T.ord_mul
    (genericRatioNorm_ne_zero (f 0) (L 0) (a 0) (b 0))
    (genericRatioNorm_ne_zero (f 1) (L 1) (a 1) (b 1))).symm

end AlgebraicGeometry.Scheme
