/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoPolynomialTransfer

/-!
# Literal scalar change of two-coordinate points

Scalar restriction and affine change of source preserve both Laurent coordinates
of the original pair. The equalities hold as scheme morphisms before forming
cycle classes, without finite-dimensionality or separability hypotheses.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.WeightTwoScalarPairChange

open WeightTwoCubicBoundary WeightTwoCorestriction WeightTwoPolynomialTransfer

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- A literal Laurent evaluation retains its unit under restriction of coefficients. -/
theorem unitMap_torusMap {R : Type u} [CommRing R] (c : L →+* R) (a : Rˣ) :
    unitMap c a ≫ Spec.map (CommRingCat.PolynomialLaurent.laurentMap
      (CommRingCat.ofHom (algebraMap k L))) =
        unitMap (c.comp (algebraMap k L)) a := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply CommRingCat.PolynomialLaurent.laurent_hom_ext
  · intro r
    change LaurentPolynomial.eval₂ c a
      (CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom (algebraMap k L))
        (LaurentPolynomial.C r)) =
      LaurentPolynomial.eval₂ (c.comp (algebraMap k L)) a (LaurentPolynomial.C r)
    rw [CommRingCat.PolynomialLaurent.laurentMap_C]
    simp only [LaurentPolynomial.eval₂_C, RingHom.comp_apply]
    rfl
  · change LaurentPolynomial.eval₂ c a
      (CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom (algebraMap k L))
        (LaurentPolynomial.T 1)) =
      LaurentPolynomial.eval₂ (c.comp (algebraMap k L)) a (LaurentPolynomial.T 1)
    rw [CommRingCat.PolynomialLaurent.laurentMap_T]
    simp only [LaurentPolynomial.eval₂_T]

/-- Restricting a pair uses the composite coefficient map and the same two units. -/
theorem pairMap_torusMap {R : Type u} [CommRing R] (c : L →+* R) (a b : Rˣ) :
    pairMap c a b ≫ torusMap (k := k) (E := L) 2 =
      pairMap (c.comp (algebraMap k L)) a b := by
  apply pair_hom_ext
  · rw [Category.assoc, torusMap_coordinate, ← Category.assoc,
      pairMap_first, pairMap_first]
    exact unitMap_torusMap c a
  · rw [Category.assoc, torusMap_coordinate, ← Category.assoc,
      pairMap_second, pairMap_second]
    exact unitMap_torusMap c b

/-- A compatible affine field map preserves the entire original scalar point. -/
theorem scalarPoint_rationalPair_comp {E F : Type u} [Field E] [Field F]
    [Algebra k E] [Algebra k F] (ψ : E →+* F)
    (hψ : ψ.comp (algebraMap k E) = algebraMap k F) (a b : Eˣ) :
    Spec.map (CommRingCat.ofHom ψ) ≫
      scalarPoint (k := k) (WeightTwoSymbols.rationalPair E a b) =
      scalarPoint (k := k) (WeightTwoSymbols.rationalPair F
        (Units.map ψ.toMonoidHom a) (Units.map ψ.toMonoidHom b)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, scalarPoint_fst, scalarPoint_fst, ← Spec.map_comp]
    exact congrArg Spec.map (congrArg CommRingCat.ofHom hψ)
  · rw [Category.assoc, scalarPoint_snd, scalarPoint_snd,
      rationalPair_torusMap, rationalPair_torusMap]
    exact pairMap_comp (algebraMap k E) (algebraMap k F) ψ a b
      (Units.map ψ.toMonoidHom a) (Units.map ψ.toMonoidHom b) hψ rfl rfl

/-- In a scalar square the old pair is the restriction of the new pair,
with the actual specified field map applied to both original units. -/
theorem rationalPair_scalarSquare {E F : Type u} [Field E] [Field F]
    [Algebra k E] [Algebra L F] (ψ : E →+* F)
    (hψ : ψ.comp (algebraMap k E) = (algebraMap L F).comp (algebraMap k L))
    (a b : Eˣ) :
    Spec.map (CommRingCat.ofHom ψ) ≫
      (WeightTwoSymbols.rationalPair E a b).left ≫ torusMap (k := k) (E := E) 2 =
      (WeightTwoSymbols.rationalPair F
        (Units.map ψ.toMonoidHom a) (Units.map ψ.toMonoidHom b)).left ≫
          torusMap (k := L) (E := F) 2 ≫ torusMap (k := k) (E := L) 2 := by
  rw [rationalPair_torusMap, ← Category.assoc, rationalPair_torusMap,
    pairMap_torusMap]
  exact pairMap_comp (algebraMap k E)
    ((algebraMap L F).comp (algebraMap k L)) ψ a b
    (Units.map ψ.toMonoidHom a) (Units.map ψ.toMonoidHom b) hψ rfl rfl

end Motivic.WeightTwoScalarPairChange
