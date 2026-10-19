/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.TopDegree
public import Motivic.Cohomology.WeightOne.InterpolationCycle
public import Motivic.Cohomology.WeightOne.SplitPolynomialCycle
public import Motivic.Cohomology.WeightTwo.Symbols

/-!
# All-weight rational symbols on the actual reduced torus

Every rational tuple defines a class of its literal graph correspondence.
The actual finite quadratic interpolation proves multilinearity in any chosen
coordinate. Every identity coordinate vanishes in the original reduced quotient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial

universe w u

namespace Motivic.DiagonalCycleSymbols
open _root_.AlgebraicGeometry.Scheme

open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers WeightOneBoundaryNorm
open WeightOneInterpolationCycle WeightOneSplitPolynomialCycle DiagonalTopDegree

variable (k : Type u) [Field k]

/-- The actual n-fold torus target. -/
abbrev target (q : ℕ) : Cor k := Cor.mk (SmoothSite.torusPower (.of k) q)

/-- Actual signed point correspondences map to their genuine homology classes. -/
def cycleClass (q : ℕ) : (point k ⟶ target k q) →+
    (motivicRawBaseComplex k q).homology q :=
  (singularClass k q).comp
    (((toReducedTorus k q).hom.app (op (Cor.simplexProduct (point k) 0))).hom.comp
      ((AddEquiv.ulift : ULift.{u + 1}
        (Cor.simplexProduct (point k) 0 ⟶ target k q) ≃+
          (Cor.simplexProduct (point k) 0 ⟶ target k q)).symm.toAddMonoidHom.comp
        (Preadditive.leftComp (target k q) (zeroProductIso k).hom)))

/-- The actual quotient class of a represented zero-simplex. -/
theorem singularClass_quotient (q : ℕ) (α : Cor.simplexProduct (point k) 0 ⟶ target k q) :
    singularClass k q ((toReducedTorus k q).hom.app
      (op (Cor.simplexProduct (point k) 0)) (ULift.up α)) =
        cycleClass k q ((zeroProductIso k).inv ≫ α) := by
  change _ = singularClass k q ((toReducedTorus k q).hom.app
    (op (Cor.simplexProduct (point k) 0))
      (ULift.up ((zeroProductIso k).hom ≫ (zeroProductIso k).inv ≫ α)))
  rw [Iso.hom_inv_id_assoc]

/-- A literal coface evaluates to its original endpoint cycle. -/
theorem singularClass_face_quotient (q : ℕ) (i : Fin 2)
    (α : Cor.simplexProduct (point k) 1 ⟶ target k q) :
    singularClass k q (transfer (reducedTorus k q)
      ((Cor.simplexProductCosimplicial (point k)).δ i)
        ((toReducedTorus k q).hom.app (op (Cor.simplexProduct (point k) 1)) (ULift.up α))) =
      cycleClass k q ((zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (point k)).δ i ≫ α) := by
  exact (congrArg (singularClass k q) (reducedTorus_transfer_apply k q
    ((Cor.simplexProductCosimplicial (point k)).δ i) α)).trans
      (singularClass_quotient k q _)

/-- The two full endpoint cycles of any actual singular correspondence have equal classes. -/
theorem cycleClass_endpoints (q : ℕ) (α : Cor.simplexProduct (point k) 1 ⟶ target k q) :
    cycleClass k q ((zeroProductIso k).inv ≫
      (Cor.simplexProductCosimplicial (point k)).δ 0 ≫ α) =
    cycleClass k q ((zeroProductIso k).inv ≫
      (Cor.simplexProductCosimplicial (point k)).δ 1 ≫ α) := by
  have h := singularClass_boundary k q ((toReducedTorus k q).hom.app
    (op (Cor.simplexProduct (point k) 1)) (ULift.up α))
  rw [boundary_eq_endpoints] at h
  change singularClass k q
    (transfer (reducedTorus k q) ((Cor.simplexProductCosimplicial (point k)).δ 0)
      ((toReducedTorus k q).hom.app (op (Cor.simplexProduct (point k) 1)) (ULift.up α)) -
    transfer (reducedTorus k q) ((Cor.simplexProductCosimplicial (point k)).δ 1)
      ((toReducedTorus k q).hom.app (op (Cor.simplexProduct (point k) 1)) (ULift.up α))) = 0 at h
  rw [map_sub, singularClass_face_quotient, singularClass_face_quotient, sub_eq_zero] at h
  exact h

/-- Every actual identity-axis cycle vanishes before taking homology. -/
theorem cycleClass_axis (q : ℕ) (i : Fin (q + 1)) (α : point k ⟶ target k q) :
    cycleClass k (q + 1) (α ≫ (Cor.graphFunctor k).map
      (SmoothSite.torusInsertOne (.of k) q i)) = 0 := by
  have h := congrArg (fun η => η.hom.app
      (op (Cor.simplexProduct (point k) 0)))
    (torusIdentityAxis_toReducedTorus k (q + 1) i)
  have he := ConcreteCategory.congr_hom h (ULift.up ((zeroProductIso k).hom ≫ α))
  change (toReducedTorus k (q + 1)).hom.app (op (Cor.simplexProduct (point k) 0))
    (ULift.up (((zeroProductIso k).hom ≫ α) ≫
      (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) q i))) = 0 at he
  change singularClass k (q + 1) ((toReducedTorus k (q + 1)).hom.app
    (op (Cor.simplexProduct (point k) 0))
      (ULift.up ((zeroProductIso k).hom ≫ α ≫
        (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) q i)))) = 0
  rw [Category.assoc] at he
  rw [he, map_zero]

/-- The actual rational point with the specified tuple of unit coordinates. -/
def rationalTuple (q : ℕ) (a : Fin q → kˣ) :
    SmoothSite.base (Spec (.of k)) ⟶ SmoothSite.torusPower (.of k) q :=
  SmoothSite.torusPowerLift (.of k) q (fun i => WeightOnePointNorm.rationalTorusPoint k (a i))

/-- Rational tuples have the original structure map to the base. -/
@[reassoc (attr := simp)]
theorem rationalTuple_toBase (q : ℕ) (a : Fin q → kˣ) :
    rationalTuple k q a ≫ SmoothSite.torusPowerToBase (.of k) q = 𝟙 _ := by
  apply SmoothSite.torusPower_hom_ext (.of k) 0
  intro i
  exact Fin.elim0 i

/-- A tuple with an identity coordinate factors through its actual identity axis. -/
theorem rationalTuple_axis (q : ℕ) (a : Fin (q + 1) → kˣ)
    (i : Fin (q + 1)) (hi : a i = 1) :
    rationalTuple k (q + 1) a =
      rationalTuple k q (fun j => a (i.succAbove j)) ≫
        SmoothSite.torusInsertOne (.of k) q i := by
  apply SmoothSite.torusPower_hom_ext
  intro j
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove i j
  · simp only [rationalTuple, SmoothSite.torusPowerLift_coordinate, Category.assoc,
      SmoothSite.torusInsertOne_coordinate_self, hi]
    rw [← rationalTuple, rationalTuple_toBase_assoc, WeightTwoSymbols.rationalTorusPoint_one]
  · simp only [rationalTuple, SmoothSite.torusPowerLift_coordinate, Category.assoc,
      SmoothSite.torusInsertOne_coordinate_succAbove]

/-- The actual raw diagonal class of a literal rational tuple graph. -/
def graphSymbol (q : ℕ) (a : Fin q → kˣ) : (motivicRawBaseComplex k q).homology q :=
  cycleClass k q ((Cor.graphFunctor k).map (rationalTuple k q a))

/-- A rational symbol with any identity entry vanishes in the actual quotient. -/
theorem graphSymbol_one (q : ℕ) (a : Fin q → kˣ) (i : Fin q) (hi : a i = 1) :
    graphSymbol k q a = 0 := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    rw [graphSymbol, rationalTuple_axis k q a i hi, Functor.map_comp]
    exact cycleClass_axis k q i _

/-- Insert a varying single torus coordinate among the specified fixed coordinates. -/
def varyingCoordinate (q : ℕ) (a : Fin q → kˣ) (i : Fin q) :
    SmoothSite.torusPower (.of k) 1 ⟶ SmoothSite.torusPower (.of k) q :=
  SmoothSite.torusPowerLift (.of k) q (fun j => if j = i then
    SmoothSite.torusCoordinate (.of k) 1 0 else
      SmoothSite.torusPowerToBase (.of k) 1 ≫ WeightOnePointNorm.rationalTorusPoint k (a j))

/-- The varying-coordinate map preserves the exact rational tuple and its indexing. -/
@[reassoc (attr := simp)]
theorem rationalPoint_varyingCoordinate (q : ℕ) (a : Fin q → kˣ) (i : Fin q) (b : kˣ) :
    WeightOnePointNorm.rationalPoint k b ≫ varyingCoordinate k q a i =
      rationalTuple k q (Function.update a i b) := by
  classical
  apply SmoothSite.torusPower_hom_ext
  intro j
  rw [Category.assoc, varyingCoordinate, rationalTuple,
    SmoothSite.torusPowerLift_coordinate, SmoothSite.torusPowerLift_coordinate]
  by_cases hj : j = i
  · subst j
    simp only [ite_true, Function.update_self]
    exact SmoothSite.torusPowerLift_coordinate (.of k) 1 _ 0
  · simp only [hj, ite_false, Function.update_of_ne hj,
      WeightTwoSymbols.rationalPoint_toBase_assoc]

/-- The complete quadratic endpoint relation survives arbitrary target graph postcomposition. -/
theorem cycleClass_quadratic_postcompose (q : ℕ) (a b : kˣ)
    (ψ : SmoothSite.torusPower (.of k) 1 ⟶ SmoothSite.torusPower (.of k) q) :
    cycleClass k q ((Cor.graphFunctor k).map (WeightOnePointNorm.rationalPoint k a ≫ ψ)) +
      cycleClass k q ((Cor.graphFunctor k).map (WeightOnePointNorm.rationalPoint k b ≫ ψ)) =
    cycleClass k q ((Cor.graphFunctor k).map (WeightOnePointNorm.rationalPoint k (a * b) ≫ ψ)) +
      cycleClass k q ((Cor.graphFunctor k).map (WeightOnePointNorm.rationalPoint k 1 ≫ ψ)) := by
  let p : k[X] := (X - C (a : k)) * (X - C (b : k))
  have hd : 1 ≤ p.natDegree := by rw [twoLinear_natDegree]; decide
  let α := singularCorrespondence (twoLinear_monic a b) hd (twoLinear_coeff_zero_ne_zero a b)
  let γ := (Cor.graphFunctor k).map ψ
  have h := cycleClass_endpoints k q (α ≫ γ)
  have h0 := congrArg (fun β => β ≫ γ)
    (singularCorrespondence_face_zero (twoLinear_monic a b) hd
      (twoLinear_coeff_zero_ne_zero a b))
  have h1 := congrArg (fun β => β ≫ γ)
    (singularCorrespondence_face_one (twoLinear_monic a b) hd
      (twoLinear_coeff_zero_ne_zero a b))
  dsimp only [α] at h
  simp only [Category.assoc] at h0 h1 h
  rw [h0, h1, polynomialCycle_twoLinear,
    polynomialCycle_target p hd (twoLinear_coeff_zero_ne_zero a b)] at h
  have hu : Units.mk0 (Polynomial.MonicUnitInterpolation.normValue p)
      (Polynomial.MonicUnitInterpolation.normValue_ne_zero p
        (twoLinear_coeff_zero_ne_zero a b)) = a * b := by
    apply Units.ext
    exact twoLinear_normValue a b
  rw [hu] at h
  simpa only [p, twoLinear_natDegree, Nat.reduceSub, Nat.cast_one, one_zsmul,
    Preadditive.add_comp, map_add, γ, ← Functor.map_comp] using h

/-- Multiplication in any chosen unit coordinate is addition of actual graph classes. -/
theorem graphSymbol_mul (q : ℕ) (a : Fin q → kˣ) (i : Fin q) (b c : kˣ) :
    graphSymbol k q (Function.update a i (b * c)) =
      graphSymbol k q (Function.update a i b) + graphSymbol k q (Function.update a i c) := by
  have h := cycleClass_quadratic_postcompose k q b c (varyingCoordinate k q a i)
  simp only [rationalPoint_varyingCoordinate] at h
  change graphSymbol k q (Function.update a i b) + graphSymbol k q (Function.update a i c) =
    graphSymbol k q (Function.update a i (b * c)) + graphSymbol k q (Function.update a i 1) at h
  have hz := graphSymbol_one k q (Function.update a i 1) i (Function.update_self i 1 a)
  simpa only [hz, add_zero] using h.symm

/-- Every actual diagonal class has an actual signed point-cycle representative. -/
theorem cycleClass_surjective (q : ℕ) : Function.Surjective (cycleClass k q) := by
  intro y
  obtain ⟨x, rfl⟩ := singularClass_surjective k q y
  obtain ⟨⟨α⟩, hα⟩ := toReducedTorus_surjective k q
    (Cor.simplexProduct (point k) 0) x
  refine ⟨(zeroProductIso k).inv ≫ α, ?_⟩
  rw [← singularClass_quotient, hα]

end Motivic.DiagonalCycleSymbols
