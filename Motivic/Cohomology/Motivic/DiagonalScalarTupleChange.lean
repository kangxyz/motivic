/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalCorestriction
public import Motivic.Cohomology.Motivic.WeightTwoCubicBoundary

/-! # Literal coefficient squares for arbitrary rational torus tuples -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace Motivic.DiagonalScalarTupleChange
open WeightTwoCubicBoundary WeightTwoCorestriction DiagonalCycleSymbols
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

/-- An actual scalar square preserves every coordinate of the original tuple. -/
theorem rationalTuple_scalarSquare {E F : Type u} [Field E] [Field F]
    [Algebra k E] [Algebra L F] (ψ : E →+* F)
    (hψ : ψ.comp (algebraMap k E) = (algebraMap L F).comp (algebraMap k L))
    (n : ℕ) (a : Fin n → Eˣ) :
    Spec.map (CommRingCat.ofHom ψ) ≫
      (rationalTuple E n a).left ≫ torusMap (k := k) (E := E) n =
      (rationalTuple F n (fun i => Units.map ψ.toMonoidHom (a i))).left ≫
        torusMap (k := L) (E := F) n ≫ torusMap (k := k) (E := L) n := by
  apply torusPower_scheme_hom_ext n
  · have he := MorphismProperty.Over.w (rationalTuple E n a)
    have hf := MorphismProperty.Over.w
      (rationalTuple F n (fun i => Units.map ψ.toMonoidHom (a i)))
    change (rationalTuple E n a).left ≫ (SmoothSite.torusPower (.of E) n).hom =
      𝟙 _ at he
    change (rationalTuple F n (fun i => Units.map ψ.toMonoidHom (a i))).left ≫
      (SmoothSite.torusPower (.of F) n).hom = 𝟙 _ at hf
    simp only [Category.assoc, torusMap_projection, torusMap_projection_assoc]
    rw [← Category.assoc (rationalTuple E n a).left, he, Category.id_comp]
    rw [← Category.assoc
      (rationalTuple F n (fun i => Units.map ψ.toMonoidHom (a i))).left,
      hf, Category.id_comp]
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (congrArg CommRingCat.ofHom hψ)
  · intro i
    simp only [Category.assoc, torusMap_coordinate, torusMap_coordinate_assoc]
    have he := congrArg (fun f => f.left)
      (SmoothSite.torusPowerLift_coordinate (.of E) n
        (fun j => WeightOnePointNorm.rationalTorusPoint E (a j)) i)
    have hf := congrArg (fun f => f.left)
      (SmoothSite.torusPowerLift_coordinate (.of F) n
        (fun j => WeightOnePointNorm.rationalTorusPoint F
          (Units.map ψ.toMonoidHom (a j))) i)
    dsimp only [MorphismProperty.Comma.comp_left] at he hf
    change (rationalTuple E n a).left ≫
      (SmoothSite.torusCoordinate (.of E) n i).left = _ at he
    change (rationalTuple F n (fun i => Units.map ψ.toMonoidHom (a i))).left ≫
      (SmoothSite.torusCoordinate (.of F) n i).left = _ at hf
    rw [← Category.assoc (rationalTuple E n a).left, he,
      ← Category.assoc
        (rationalTuple F n (fun i => Units.map ψ.toMonoidHom (a i))).left, hf]
    rw [rationalTorusPoint_scalar, ← Category.assoc, rationalTorusPoint_scalar]
    change Spec.map (CommRingCat.ofHom ψ) ≫ unitMap (algebraMap k E) (a i) =
      unitMap (algebraMap L F) (Units.map ψ.toMonoidHom (a i)) ≫ _
    rw [unitMap_torusMap]
    exact unitMap_comp (algebraMap k E) ((algebraMap L F).comp (algebraMap k L))
      ψ (a i) (Units.map ψ.toMonoidHom (a i)) hψ rfl

end Motivic.DiagonalScalarTupleChange
