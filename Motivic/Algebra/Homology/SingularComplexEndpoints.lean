/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.SingularComplexPrism

/-!
# Endpoint chain homotopy on the actual singular complex

The prism gives the chain homotopy between the two ends of the cosimplicial
interval. This is the elementary singular-chain input to MVW Lemma 4.6;
it assumes no homotopy invariance of the coefficient presheaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open scoped Simplicial

universe v u v' u'

namespace Motivic.SingularComplex.Prism

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type u'} [Category.{v'} A]

/-- The interval parameter, with its actual cosimplicial simplex factor. -/
def cylinder (Δ : CosimplicialObject C) : CosimplicialObject C :=
  Δ ⋙ prod.functor.obj (Δ.obj ⦋1⦌)

/-- A constant vertex of the interval, retaining the simplex factor. -/
def endpoint (Δ : CosimplicialObject C) (v : Fin 2) : Δ ⟶ cylinder Δ where
  app n := prod.lift (Δ.map (SimplexCategory.const n ⦋1⦌ v)) (𝟙 _)
  naturality m n f := by
    apply prod.hom_ext
    · simp only [cylinder, Functor.comp_map, prod.functor_obj_map, Category.assoc,
        prod.lift_fst, prod.map_fst, Category.comp_id]
      rw [← Δ.map_comp]
      congr 1
    · simp [cylinder]

/-- The `i`-th prism simplex as an actual map into interval times simplex. -/
def simplex (Δ : CosimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    Δ.obj ⦋n + 1⦌ ⟶ (cylinder Δ).obj ⦋n⦌ :=
  prod.lift (Δ.map (cut i)) (Δ.σ i)

lemma simplex_zero_face (Δ : CosimplicialObject C) (n : ℕ) :
    Δ.δ 0 ≫ simplex Δ (0 : Fin (n + 1)) = (endpoint Δ 1).app ⦋n⦌ := by
  apply prod.hom_ext
  · simp only [simplex, endpoint, Category.assoc, prod.lift_fst, CosimplicialObject.δ]
    rw [← Δ.map_comp, cut_zero_face]
  · simp only [simplex, endpoint, Category.assoc, prod.lift_snd]
    exact Δ.δ_comp_σ_self (i := (0 : Fin (n + 1)))

lemma simplex_last_face (Δ : CosimplicialObject C) (n : ℕ) :
    Δ.δ (Fin.last (n + 1)) ≫ simplex Δ (Fin.last n) =
      (endpoint Δ 0).app ⦋n⦌ := by
  apply prod.hom_ext
  · simp only [simplex, endpoint, Category.assoc, prod.lift_fst, CosimplicialObject.δ]
    rw [← Δ.map_comp, cut_last_face]
  · simp only [simplex, endpoint, Category.assoc, prod.lift_snd]
    exact Δ.δ_comp_σ_succ (i := Fin.last n)

lemma simplex_face_left (Δ : CosimplicialObject C) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    Δ.δ i.castSucc ≫ simplex Δ j.succ = simplex Δ j ≫ (cylinder Δ).δ i := by
  apply prod.hom_ext
  · simp only [simplex, cylinder, CosimplicialObject.δ, Functor.comp_map,
      prod.functor_obj_map, Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id]
    rw [← Δ.map_comp, cut_face_left i j hij]
  · simpa [Category.assoc, simplex, cylinder, CosimplicialObject.δ, CosimplicialObject.σ] using
      Δ.δ_comp_σ_of_le hij

lemma simplex_face_middle (Δ : CosimplicialObject C) {n : ℕ} (j : Fin (n + 1)) :
    Δ.δ j.castSucc.succ ≫ simplex Δ j.succ =
      Δ.δ j.castSucc.succ ≫ simplex Δ j.castSucc := by
  apply prod.hom_ext
  · simp only [simplex, CosimplicialObject.δ, Category.assoc, prod.lift_fst]
    rw [← Δ.map_comp, ← Δ.map_comp, cut_face_middle]
  · simp only [simplex, Category.assoc, prod.lift_snd]
    exact (Δ.δ_comp_σ_self (i := j.succ)).trans (Δ.δ_comp_σ_succ (i := j.castSucc)).symm

lemma simplex_face_right (Δ : CosimplicialObject C) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    Δ.δ i.succ ≫ simplex Δ j.castSucc = simplex Δ j ≫ (cylinder Δ).δ i := by
  apply prod.hom_ext
  · simp only [simplex, cylinder, CosimplicialObject.δ, Functor.comp_map,
      prod.functor_obj_map, Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id]
    rw [← Δ.map_comp, cut_face_right i j hji]
  · simpa [Category.assoc, simplex, cylinder, CosimplicialObject.δ, CosimplicialObject.σ] using
      Δ.δ_comp_σ_of_gt hji

lemma simplex_degeneracy_left (Δ : CosimplicialObject C) {n : ℕ}
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    Δ.σ i.castSucc ≫ simplex Δ j = simplex Δ j.succ ≫ (cylinder Δ).σ i := by
  apply prod.hom_ext
  · simp only [simplex, cylinder, CosimplicialObject.σ, Functor.comp_map,
      prod.functor_obj_map, Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id]
    rw [← Δ.map_comp, cut_degeneracy_left i j hij]
  · simpa [Category.assoc, simplex, cylinder, CosimplicialObject.δ, CosimplicialObject.σ] using
      Δ.σ_comp_σ hij

lemma simplex_degeneracy_right (Δ : CosimplicialObject C) {n : ℕ}
    (i j : Fin (n + 1)) (hji : j ≤ i) :
    Δ.σ i.succ ≫ simplex Δ j = simplex Δ j.castSucc ≫ (cylinder Δ).σ i := by
  apply prod.hom_ext
  · simp only [simplex, cylinder, CosimplicialObject.σ, Functor.comp_map,
      prod.functor_obj_map, Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id]
    rw [← Δ.map_comp, cut_degeneracy_right i j hji]
  · simpa [Category.assoc, simplex, cylinder, CosimplicialObject.δ, CosimplicialObject.σ] using
      (Δ.σ_comp_σ hji).symm

/-- The prism is a simplicial homotopy on the originally evaluated presheaf. -/
def simplicialHomotopy (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    SimplicialObject.Homotopy
      (whiskerRight (NatTrans.op (endpoint Δ 0)) P)
      (whiskerRight (NatTrans.op (endpoint Δ 1)) P) where
  h i := P.map (simplex Δ i).op
  h_zero_comp_δ_zero n := by
    change P.map (simplex Δ (0 : Fin (n + 1))).op ≫ P.map (Δ.δ 0).op =
      P.map ((endpoint Δ 1).app ⦋n⦌).op
    rw [← P.map_comp, ← op_comp, simplex_zero_face]
  h_last_comp_δ_last n := by
    change P.map (simplex Δ (Fin.last n)).op ≫ P.map (Δ.δ (Fin.last (n + 1))).op =
      P.map ((endpoint Δ 0).app ⦋n⦌).op
    rw [← P.map_comp, ← op_comp, simplex_last_face]
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    change P.map (simplex Δ j.succ).op ≫ P.map (Δ.δ i.castSucc).op =
      P.map ((cylinder Δ).δ i).op ≫ P.map (simplex Δ j).op
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, simplex_face_left Δ i j hij]
  h_succ_comp_δ_castSucc_succ j := by
    change P.map (simplex Δ j.succ).op ≫ P.map (Δ.δ j.castSucc.succ).op =
      P.map (simplex Δ j.castSucc).op ≫ P.map (Δ.δ j.castSucc.succ).op
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, simplex_face_middle]
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    change P.map (simplex Δ j.castSucc).op ≫ P.map (Δ.δ i.succ).op =
      P.map ((cylinder Δ).δ i).op ≫ P.map (simplex Δ j).op
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, simplex_face_right Δ i j hji]
  h_comp_σ_castSucc_of_le i j hij := by
    change P.map (simplex Δ j).op ≫ P.map (Δ.σ i.castSucc).op =
      P.map ((cylinder Δ).σ i).op ≫ P.map (simplex Δ j.succ).op
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, simplex_degeneracy_left Δ i j hij]
  h_comp_σ_succ_of_lt i j hji := by
    change P.map (simplex Δ j).op ≫ P.map (Δ.σ i.succ).op =
      P.map ((cylinder Δ).σ i).op ≫ P.map (simplex Δ j.castSucc).op
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, simplex_degeneracy_right Δ i j hji]

variable [Preadditive A]

/-- MVW's endpoint chain homotopy on the existing, unnormalized singular complex. -/
def endpointHomotopy (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) :
    _root_.Homotopy (geometryMap (endpoint Δ 0) P) (geometryMap (endpoint Δ 1) P) :=
  (simplicialHomotopy Δ P).toChainHomotopy

/-- The two endpoint maps agree on every homology group, without assuming HI. -/
theorem endpoint_homologyMap_eq [CategoryWithHomology A]
    (Δ : CosimplicialObject C) (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    HomologicalComplex.homologyMap (geometryMap (endpoint Δ 0) P) n =
      HomologicalComplex.homologyMap (geometryMap (endpoint Δ 1) P) n :=
  (endpointHomotopy Δ P).homologyMap_eq n

/-- A cycle joining zero to a given endpoint supplies an explicit boundary.
The lift may be chosen nonlinearly: no additive contraction is assumed. -/
theorem boundary_of_cycle_path {D E : ChainComplex AddCommGrpCat.{u'} ℕ}
    {f g : D ⟶ E} (H : _root_.Homotopy f g) (n : ℕ) (y : D.X n)
    (hy : ∀ m, D.d n m y = 0) (hf : f.f n y = 0) :
    E.d (n + 1) n (-(H.hom n (n + 1) y)) = g.f n y := by
  have hc := H.comm n
  rw [prevD_eq H.hom (j := n) (j' := n + 1) (by simp)] at hc
  have he := ConcreteCategory.congr_hom hc y
  change f.f n y = H.hom _ n (D.d n _ y) + E.d (n + 1) n (H.hom n (n + 1) y) +
    g.f n y at he
  rw [hy, map_zero, zero_add, hf] at he
  rw [_root_.map_neg]
  exact (eq_neg_of_add_eq_zero_right he.symm).symm

end Motivic.SingularComplex.Prism
