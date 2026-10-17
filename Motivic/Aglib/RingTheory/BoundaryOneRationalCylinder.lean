/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.BoundaryOneRationalFunctor
public import Motivic.Algebra.Homology.SingularSetwisePaths
public import Motivic.AlgebraicGeometry.AlgebraicSimplex
public import Mathlib.Algebra.Category.Ring.Colimits

/-! # Actual ring-cylinder paths for boundary-one rational functions -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace Polynomial.BoundaryOneRationalFunctions

open Motivic.SingularComplex

/-- The actual coefficient presheaf on the opposite category of commutative rings. -/
def ringPresheaf : CommRingCat.{u}ᵒᵖᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (opOpEquivalence CommRingCat).functor ⋙ functor

variable (Δ : CosimplicialObject CommRingCat.{u}ᵒᵖ)

/-- The genuine categorical cylinder ring. -/
abbrev cylinderRing (n : SimplexCategory) : CommRingCat.{u} :=
  ((Prism.cylinder Δ).obj n).unop

/-- The original simplex ring's injection into the cylinder ring. -/
def cylinderInclusion (n : SimplexCategory) : (Δ.obj n).unop →+* cylinderRing Δ n :=
  (prod.snd : Δ.obj ⦋1⦌ ⨯ Δ.obj n ⟶ Δ.obj n).unop.hom

/-- Evaluate the polynomial homotopy parameter at the cylinder's interval coordinate. -/
def cylinderEvaluation (t : (Δ.obj ⦋1⦌).unop) (n : SimplexCategory) :
    ((Δ.obj n).unop)[X] →+* cylinderRing Δ n :=
  eval₂RingHom (cylinderInclusion Δ n)
    ((prod.fst : Δ.obj ⦋1⦌ ⨯ Δ.obj n ⟶ Δ.obj ⦋1⦌).unop.hom t)

theorem cylinderEvaluation_natural (t : (Δ.obj ⦋1⦌).unop)
    {m n : SimplexCategory} (f : m ⟶ n) :
    (((Prism.cylinder Δ).map f).unop.hom).comp (cylinderEvaluation Δ t n) =
      (cylinderEvaluation Δ t m).comp (Polynomial.mapRingHom (Δ.map f).unop.hom) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, cylinderEvaluation, coe_eval₂RingHom, eval₂_C,
      Polynomial.coe_mapRingHom, Polynomial.map_C]
    change ((Prism.cylinder Δ).map f).unop.hom (cylinderInclusion Δ n r) =
      cylinderInclusion Δ m ((Δ.map f).unop.hom r)
    have h : (Prism.cylinder Δ).map f ≫
        (prod.snd : Δ.obj ⦋1⦌ ⨯ Δ.obj n ⟶ Δ.obj n) =
        (prod.snd : Δ.obj ⦋1⦌ ⨯ Δ.obj m ⟶ Δ.obj m) ≫ Δ.map f := by
      simp [Prism.cylinder]
    exact congrArg (fun a : (Prism.cylinder Δ).obj m ⟶ Δ.obj n => a.unop.hom r) h
  · simp only [RingHom.comp_apply, cylinderEvaluation, coe_eval₂RingHom, eval₂_X,
      Polynomial.coe_mapRingHom, Polynomial.map_X]
    change ((Prism.cylinder Δ).map f).unop.hom
      ((prod.fst : Δ.obj ⦋1⦌ ⨯ Δ.obj n ⟶ Δ.obj ⦋1⦌).unop.hom t) =
        (prod.fst : Δ.obj ⦋1⦌ ⨯ Δ.obj m ⟶ Δ.obj ⦋1⦌).unop.hom t
    have h := prod.map_fst (𝟙 (Δ.obj ⦋1⦌)) (Δ.map f)
    simpa only [Prism.cylinder, Functor.comp_map, Functor.comp_obj, prod.functor_obj_obj,
      prod.functor_obj_map,
      Category.comp_id, unop_comp, CommRingCat.hom_comp, RingHom.comp_apply] using
      congrArg (fun a => a.unop.hom t) h

/-- A setwise path in the actual singular-cylinder group. -/
def cylinderPath (t : (Δ.obj ⦋1⦌).unop) (n : ℕ)
    (x : (obj Δ ringPresheaf).X n) : (obj (Prism.cylinder Δ) ringPresheaf).X n :=
  Additive.ofMul (map (cylinderEvaluation Δ t ⦋n⦌) (homotopy x.toMul))

@[simp] theorem cylinderPath_zero (t : (Δ.obj ⦋1⦌).unop) (n : ℕ) :
    cylinderPath Δ t n 0 = 0 := by
  change Additive.ofMul (map _ (homotopy 1)) = 0
  rw [homotopy_identity, map_one]
  rfl

theorem cylinderPath_face (t : (Δ.obj ⦋1⦌).unop) (n : ℕ)
    (i : Fin (n + 2)) (x : (obj Δ ringPresheaf).X (n + 1)) :
    ringPresheaf.map ((Prism.cylinder Δ).δ i).op (cylinderPath Δ t (n + 1) x) =
      cylinderPath Δ t n (ringPresheaf.map (Δ.δ i).op x) := by
  change Additive.ofMul (map (((Prism.cylinder Δ).δ i).unop.hom)
      (map (cylinderEvaluation Δ t ⦋n + 1⦌) (homotopy x.toMul))) =
    Additive.ofMul (map (cylinderEvaluation Δ t ⦋n⦌)
      (homotopy (map (Δ.δ i).unop.hom x.toMul)))
  rw [← homotopy_natural, ← map_comp, ← map_comp]
  exact congrArg (fun φ => Additive.ofMul (map φ
    (homotopy (Additive.toMul (α := group (Δ.obj ⦋n + 1⦌).unop) x))))
    (cylinderEvaluation_natural Δ t (SimplexCategory.δ i))

theorem cylinderEvaluation_endpoint (t : (Δ.obj ⦋1⦌).unop) (v : Fin 2)
    (n : SimplexCategory) (a : (Δ.obj n).unop)
    (ht : (Δ.map (SimplexCategory.const n ⦋1⦌ v)).unop.hom t = a) :
    (((Prism.endpoint Δ v).app n).unop.hom).comp (cylinderEvaluation Δ t n) =
      evalRingHom a := by
  apply Polynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, cylinderEvaluation, coe_eval₂RingHom, eval₂_C,
      coe_evalRingHom, eval_C]
    change ((Prism.endpoint Δ v).app n).unop.hom
      ((prod.snd : Δ.obj ⦋1⦌ ⨯ Δ.obj n ⟶ Δ.obj n).unop.hom r) = r
    have h := prod.lift_snd (Δ.map (SimplexCategory.const n ⦋1⦌ v)) (𝟙 (Δ.obj n))
    exact congrArg (fun b => b.unop.hom r) h
  · simp only [RingHom.comp_apply, cylinderEvaluation, coe_eval₂RingHom, eval₂_X,
      coe_evalRingHom, eval_X]
    change ((Prism.endpoint Δ v).app n).unop.hom
      ((prod.fst : Δ.obj ⦋1⦌ ⨯ Δ.obj n ⟶ Δ.obj ⦋1⦌).unop.hom t) = a
    have h := prod.lift_fst (Δ.map (SimplexCategory.const n ⦋1⦌ v)) (𝟙 (Δ.obj n))
    exact (congrArg (fun b => b.unop.hom t) h).trans ht

theorem cylinderPath_start (t : (Δ.obj ⦋1⦌).unop)
    (ht : ∀ n : SimplexCategory,
      (Δ.map (SimplexCategory.const n ⦋1⦌ 0)).unop.hom t = 0)
    (n : ℕ) (x : (obj Δ ringPresheaf).X n) :
    (geometryMap (Prism.endpoint Δ 0) ringPresheaf).f n (cylinderPath Δ t n x) = 0 := by
  change Additive.ofMul (map (((Prism.endpoint Δ 0).app ⦋n⦌).unop.hom)
    (map (cylinderEvaluation Δ t ⦋n⦌) (homotopy x.toMul))) = 0
  rw [← map_comp, cylinderEvaluation_endpoint Δ t 0 ⦋n⦌ 0 (ht ⦋n⦌), homotopy_zero]
  rfl

theorem cylinderPath_end (t : (Δ.obj ⦋1⦌).unop)
    (ht : ∀ n : SimplexCategory,
      (Δ.map (SimplexCategory.const n ⦋1⦌ 1)).unop.hom t = 1)
    (n : ℕ) (x : (obj Δ ringPresheaf).X n) :
    (geometryMap (Prism.endpoint Δ 1) ringPresheaf).f n (cylinderPath Δ t n x) = x := by
  change Additive.ofMul (map (((Prism.endpoint Δ 1).app ⦋n⦌).unop.hom)
    (map (cylinderEvaluation Δ t ⦋n⦌) (homotopy x.toMul))) = x
  rw [← map_comp, cylinderEvaluation_endpoint Δ t 1 ⦋n⦌ 1 (ht ⦋n⦌), homotopy_one]
  rfl

/-- The actual affine rational-function model is acyclic for any ring-valued
cosimplicial interval carrying a coordinate with endpoints zero and one. -/
theorem isZero_homology_of_interval (t : (Δ.obj ⦋1⦌).unop)
    (h0 : ∀ n : SimplexCategory,
      (Δ.map (SimplexCategory.const n ⦋1⦌ 0)).unop.hom t = 0)
    (h1 : ∀ n : SimplexCategory,
      (Δ.map (SimplexCategory.const n ⦋1⦌ 1)).unop.hom t = 1)
    (n : ℕ) : IsZero ((obj Δ ringPresheaf).homology n) :=
  isZero_homology_of_setwise_paths Δ ringPresheaf (cylinderPath Δ t)
    (cylinderPath_zero Δ t) (cylinderPath_face Δ t)
    (cylinderPath_start Δ t h0) (cylinderPath_end Δ t h1) n

variable (R : Type u) [CommRing R]

/-- The concrete algebraic-simplex geometry used for the affine model. -/
abbrev algebraicSimplex : CosimplicialObject CommRingCat.{u}ᵒᵖ :=
  (Motivic.AlgebraicSimplex.simplicialRing R).rightOp

@[simp] theorem algebraicSimplex_interval_zero (n : SimplexCategory) :
    ((algebraicSimplex R).map (SimplexCategory.const n ⦋1⦌ 0)).unop.hom
      (Motivic.AlgebraicSimplex.coordinate R 1 1) = 0 := by
  change Motivic.AlgebraicSimplex.pullback R
    (SimplexCategory.const n ⦋1⦌ 0).toOrderHom
    (Motivic.AlgebraicSimplex.coordinate R 1 1) = 0
  simp [Motivic.AlgebraicSimplex.pullback_coordinate, SimplexCategory.const]

@[simp] theorem algebraicSimplex_interval_one (n : SimplexCategory) :
    ((algebraicSimplex R).map (SimplexCategory.const n ⦋1⦌ 1)).unop.hom
      (Motivic.AlgebraicSimplex.coordinate R 1 1) = 1 := by
  change Motivic.AlgebraicSimplex.pullback R
    (SimplexCategory.const n ⦋1⦌ 1).toOrderHom
    (Motivic.AlgebraicSimplex.coordinate R 1 1) = 1
  simp [Motivic.AlgebraicSimplex.pullback_coordinate, SimplexCategory.const]

/-- In every degree, the actual affine boundary-one rational-function complex
on the actual algebraic simplices has zero homology. This is not yet the
identification with the original correspondence/sheaf kernel. -/
theorem isZero_homology_algebraicSimplex (n : ℕ) :
    IsZero ((obj (algebraicSimplex R) ringPresheaf).homology n) :=
  isZero_homology_of_interval (algebraicSimplex R)
    (Motivic.AlgebraicSimplex.coordinate R 1 1)
    (algebraicSimplex_interval_zero R) (algebraicSimplex_interval_one R) n

end Polynomial.BoundaryOneRationalFunctions
