/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.ScalarPairChange
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual two-coordinate scalar change

The statements retain arbitrary source rings and exact scalar maps. No finite
extension, separability, reducedness, or conclusion-like hypothesis is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open WeightTwoCubicBoundary WeightTwoCorestriction WeightTwoScalarPairChange

universe u

namespace MotivicTest.WeightTwoScalarPairChange

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- Even a nonreduced affine source retains both original unit coordinates. -/
theorem arbitrary_affine_pair {R : Type u} [CommRing R] (c : L →+* R) (a b : Rˣ) :
    pairMap c a b ≫ torusMap (k := k) (E := L) 2 =
      pairMap (c.comp (algebraMap k L)) a b :=
  pairMap_torusMap c a b

/-- The entire point equality has no finite-dimensionality assumption. -/
theorem actual_scalar_point {E F : Type u} [Field E] [Field F]
    [Algebra k E] [Algebra k F] (ψ : E →+* F)
    (hψ : ψ.comp (algebraMap k E) = algebraMap k F) (a b : Eˣ) :
    Spec.map (CommRingCat.ofHom ψ) ≫
      scalarPoint (k := k) (WeightTwoSymbols.rationalPair E a b) =
      scalarPoint (k := k) (WeightTwoSymbols.rationalPair F
        (Units.map ψ.toMonoidHom a) (Units.map ψ.toMonoidHom b)) :=
  scalarPoint_rationalPair_comp ψ hψ a b

/-- A mixed square uses exactly the two specified coefficient maps. -/
theorem actual_mixed_pair {E F : Type u} [Field E] [Field F]
    [Algebra k E] [Algebra L F] (ψ : E →+* F)
    (hψ : ψ.comp (algebraMap k E) = (algebraMap L F).comp (algebraMap k L))
    (a b : Eˣ) :
    Spec.map (CommRingCat.ofHom ψ) ≫
      (WeightTwoSymbols.rationalPair E a b).left ≫ torusMap (k := k) (E := E) 2 =
      (WeightTwoSymbols.rationalPair F
        (Units.map ψ.toMonoidHom a) (Units.map ψ.toMonoidHom b)).left ≫
          torusMap (k := L) (E := F) 2 ≫ torusMap (k := k) (E := L) 2 :=
  rationalPair_scalarSquare ψ hψ a b

/-- An algebra homomorphism supplies the required compatibility automatically. -/
theorem algebra_hom_scalar_point {E F : Type u} [Field E] [Field F]
    [Algebra k E] [Algebra k F] (ψ : E →ₐ[k] F) (a b : Eˣ) :
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      scalarPoint (k := k) (WeightTwoSymbols.rationalPair E a b) =
      scalarPoint (k := k) (WeightTwoSymbols.rationalPair F
        (Units.map ψ.toMonoidHom a) (Units.map ψ.toMonoidHom b)) := by
  apply scalarPoint_rationalPair_comp
  ext x
  exact ψ.commutes x

open Lean in
run_cmd do
  for name in #[``unitMap_torusMap, ``pairMap_torusMap, ``scalarPoint_rationalPair_comp,
      ``rationalPair_scalarSquare, ``arbitrary_affine_pair, ``actual_scalar_point,
      ``actual_mixed_pair, ``algebra_hom_scalar_point] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Literal scalar pair change uses only standard foundations."

end MotivicTest.WeightTwoScalarPairChange
