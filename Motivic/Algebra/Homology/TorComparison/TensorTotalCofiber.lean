/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.ExteriorHomotopy
public import Mathlib.Algebra.Homology.HomotopyCofiber

/-!
# The homotopy cofiber of a first-factor tensor-total map

The comparison is built from the literal map of signed total complexes and
its canonical null-homotopy. In nonnegative chain degree the horizontal total
sign is one; the shifted vertical sign agrees with the negative differential
on the source summand of the homotopy cofiber.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex

namespace Motivic.TorComparison

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasBinaryBiproducts C₁] [HasBinaryBiproducts D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  {K L : ChainComplex C₁ ℕ} (f : K ⟶ L) (G : ChainComplex C₂ ℕ)
  [HasMapBifunctor K G F (ComplexShape.down ℕ)]
  [HasMapBifunctor L G F (ComplexShape.down ℕ)]
  [HasMapBifunctor (homotopyCofiber f) G F (ComplexShape.down ℕ)]

/-- Tensoring the canonical cofiber null-homotopy gives a null-homotopy of the
actual first-factor total map followed by the totalized right inclusion. -/
noncomputable def tensorTotalCofiberHomotopy :
    Homotopy
      (mapBifunctorMap f (𝟙 G) F (ComplexShape.down ℕ) ≫
        mapBifunctorMap (homotopyCofiber.inr f) (𝟙 G) F (ComplexShape.down ℕ)) 0 :=
  (Homotopy.ofEq (by rw [← exteriorTotalMap_comp]; simp)).trans
    ((mapBifunctorMapHomotopy₁
      (homotopyCofiber.inrCompHomotopy f (fun j => ⟨j + 1, rfl⟩))
      (𝟙 G) F (ComplexShape.down ℕ)).trans (Homotopy.ofEq (by ext; simp)))

/-- The canonical chain map from the cofiber of a tensor-total map to the
tensor total of the cofiber. It uses the actual given map `f`. -/
noncomputable def tensorTotalCofiberMap :
    homotopyCofiber (mapBifunctorMap f (𝟙 G) F (ComplexShape.down ℕ)) ⟶
      mapBifunctor (homotopyCofiber f) G F (ComplexShape.down ℕ) :=
  homotopyCofiber.desc _
    (mapBifunctorMap (homotopyCofiber.inr f) (𝟙 G) F (ComplexShape.down ℕ))
    (tensorTotalCofiberHomotopy F f G)

@[reassoc (attr := simp)]
theorem tensorTotalCofiberMap_inr (n : ℕ) :
    homotopyCofiber.inrX (mapBifunctorMap f (𝟙 G) F (ComplexShape.down ℕ)) n ≫
      (tensorTotalCofiberMap F f G).f n =
        (mapBifunctorMap (homotopyCofiber.inr f) (𝟙 G) F (ComplexShape.down ℕ)).f n := by
  simp [tensorTotalCofiberMap]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem tensorTotalCofiberMap_inl (p q n : ℕ) (h : p + q = n) :
    ιMapBifunctor K G F (ComplexShape.down ℕ) p q n h ≫
      homotopyCofiber.inlX (mapBifunctorMap f (𝟙 G) F (ComplexShape.down ℕ)) n
        (n + 1) rfl ≫ (tensorTotalCofiberMap F f G).f (n + 1) =
    (F.map (homotopyCofiber.inlX f p (p + 1) rfl)).app (G.X q) ≫
      ιMapBifunctor (homotopyCofiber f) G F (ComplexShape.down ℕ)
        (p + 1) q (n + 1) (by change p + 1 + q = n + 1; omega) := by
  simp only [tensorTotalCofiberMap, homotopyCofiber.inlX_desc_f,
    tensorTotalCofiberHomotopy, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Pi.zero_apply, zero_add, add_zero]
  dsimp only [mapBifunctorMapHomotopy₁]
  rw [mapBifunctorMapHomotopy.ιMapBifunctor_hom₁ _ _ _ _ (p + 1) p q n
    (n + 1) h ((ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl))]
  rw [homotopyCofiber.inrCompHomotopy_hom _ _ _ _ rfl,
    ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ (by change p + 1 + q = n + 1; omega)]
  simp

/-- The inverse in each degree, given on each actual tensor-total summand. -/
noncomputable def tensorTotalCofiberInvX (n : ℕ) :
    (mapBifunctor (homotopyCofiber f) G F (ComplexShape.down ℕ)).X n ⟶
      (homotopyCofiber (mapBifunctorMap f (𝟙 G) F (ComplexShape.down ℕ))).X n :=
  mapBifunctorDesc fun p q h =>
    (F.map (homotopyCofiber.sndX f p)).app (G.X q) ≫
      ιMapBifunctor L G F (ComplexShape.down ℕ) p q n h ≫
        homotopyCofiber.inrX (mapBifunctorMap f (𝟙 G) F (ComplexShape.down ℕ)) n +
    if hp : 0 < p then
      (F.map (homotopyCofiber.fstX f p (p - 1) (by change p - 1 + 1 = p; omega))).app
        (G.X q) ≫
        ιMapBifunctor K G F (ComplexShape.down ℕ) (p - 1) q (n - 1)
          (by change p + q = n at h; change p - 1 + q = n - 1; omega) ≫
        homotopyCofiber.inlX (mapBifunctorMap f (𝟙 G) F (ComplexShape.down ℕ))
          (n - 1) n (by change n - 1 + 1 = n; change p + q = n at h; omega)
    else 0

omit [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasBinaryBiproducts C₁] [HasBinaryBiproducts D]
  [F.Additive] [∀ X₁, (F.obj X₁).Additive] in
/-- Evaluation of a bifunctor map preserves composition in its first slot. -/
@[reassoc]
theorem tensorTotal_map_app_comp {A B C : C₁} (a : A ⟶ B) (b : B ⟶ C) (N : C₂) :
    (F.map a).app N ≫ (F.map b).app N = (F.map (a ≫ b)).app N := by
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem tensorTotalCofiberInvX_inr (p q n : ℕ) (h : p + q = n) :
    (F.map (homotopyCofiber.inrX f p)).app (G.X q) ≫
      ιMapBifunctor (homotopyCofiber f) G F (ComplexShape.down ℕ) p q n h ≫
        tensorTotalCofiberInvX F f G n =
      ιMapBifunctor L G F (ComplexShape.down ℕ) p q n h ≫
        homotopyCofiber.inrX (mapBifunctorMap f (𝟙 G) F (ComplexShape.down ℕ)) n := by
  simp only [tensorTotalCofiberInvX, ι_mapBifunctorDesc, comp_add]
  split_ifs
  · simp [tensorTotal_map_app_comp_assoc]
  · simp [tensorTotal_map_app_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem tensorTotalCofiberInvX_inl (p q n : ℕ) (h : p + q = n) :
    (F.map (homotopyCofiber.inlX f p (p + 1) rfl)).app (G.X q) ≫
      ιMapBifunctor (homotopyCofiber f) G F (ComplexShape.down ℕ) (p + 1) q
        (n + 1) (by change p + 1 + q = n + 1; omega) ≫
        tensorTotalCofiberInvX F f G (n + 1) =
      ιMapBifunctor K G F (ComplexShape.down ℕ) p q n h ≫
        homotopyCofiber.inlX (mapBifunctorMap f (𝟙 G) F (ComplexShape.down ℕ))
          n (n + 1) rfl := by
  simp [tensorTotalCofiberInvX, comp_add, tensorTotal_map_app_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The coordinate inverse is a right inverse of the comparison in every degree. -/
@[reassoc (attr := simp)]
theorem tensorTotalCofiberMap_invX (n : ℕ) :
    (tensorTotalCofiberMap F f G).f n ≫ tensorTotalCofiberInvX F f G n = 𝟙 _ := by
  cases n with
  | zero =>
      apply homotopyCofiber.ext_from_X'
        (mapBifunctorMap f (𝟙 G) F (ComplexShape.down ℕ)) 0 (by simp)
      apply mapBifunctor.hom_ext
      intro p q h
      simp [ι_mapBifunctorMap_assoc]
  | succ n =>
      apply homotopyCofiber.ext_from_X
        (mapBifunctorMap f (𝟙 G) F (ComplexShape.down ℕ)) n (n + 1) rfl
      · apply mapBifunctor.hom_ext
        intro p q h
        simp only [tensorTotalCofiberMap_inl_assoc]
        erw [Category.comp_id]
        exact tensorTotalCofiberInvX_inl F f G p q n h
      · apply mapBifunctor.hom_ext
        intro p q h
        simp [ι_mapBifunctorMap_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The coordinate inverse is also a left inverse of the comparison. -/
@[reassoc (attr := simp)]
theorem tensorTotalCofiberInvX_map (n : ℕ) :
    tensorTotalCofiberInvX F f G n ≫ (tensorTotalCofiberMap F f G).f n = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro p q h
  cases p with
  | zero =>
      simp [tensorTotalCofiberInvX, Category.assoc,
        tensorTotal_map_app_comp_assoc, homotopyCofiber.sndX_inrX f 0 (by simp)]
  | succ p =>
      have hn : n = p + q + 1 := by change p + 1 + q = n at h; omega
      revert h
      rw [hn]
      intro h
      have hd : homotopyCofiber.sndX f (p + 1) ≫ homotopyCofiber.inrX f (p + 1) +
          homotopyCofiber.fstX f (p + 1) p rfl ≫
            homotopyCofiber.inlX f p (p + 1) rfl = 𝟙 _ := by
        apply homotopyCofiber.ext_from_X f p (p + 1) rfl
        · simp [comp_add]
        · simp [comp_add]
      have hid :
          (F.map (homotopyCofiber.sndX f (p + 1))).app (G.X q) ≫
              (F.map (homotopyCofiber.inrX f (p + 1))).app (G.X q) +
            (F.map (homotopyCofiber.fstX f (p + 1) p rfl)).app (G.X q) ≫
              (F.map (homotopyCofiber.inlX f p (p + 1) rfl)).app (G.X q) = 𝟙 _ := by
        rw [tensorTotal_map_app_comp, tensorTotal_map_app_comp,
          ← NatTrans.app_add, ← Functor.map_add, hd]
        simp
      let a := ιMapBifunctor (homotopyCofiber f) G F (ComplexShape.down ℕ)
        (p + 1) q (p + q + 1) h
      have h₁ : (F.map (homotopyCofiber.inlX f p (p + 1) rfl)).app (G.X q) ≫
          a ≫ tensorTotalCofiberInvX F f G (p + q + 1) ≫
            (tensorTotalCofiberMap F f G).f (p + q + 1) =
          (F.map (homotopyCofiber.inlX f p (p + 1) rfl)).app (G.X q) ≫ a := by
        dsimp [a]
        rw [tensorTotalCofiberInvX_inl_assoc F f G p q (p + q) rfl,
          tensorTotalCofiberMap_inl F f G p q (p + q) rfl]
      have h₂ : (F.map (homotopyCofiber.inrX f (p + 1))).app (G.X q) ≫
          a ≫ tensorTotalCofiberInvX F f G (p + q + 1) ≫
            (tensorTotalCofiberMap F f G).f (p + q + 1) =
          (F.map (homotopyCofiber.inrX f (p + 1))).app (G.X q) ≫ a := by
        dsimp [a]
        simp
      change a ≫ tensorTotalCofiberInvX F f G (p + q + 1) ≫
        (tensorTotalCofiberMap F f G).f (p + q + 1) = a ≫ 𝟙 _
      rw [Category.comp_id]
      calc
        _ = 𝟙 _ ≫ (a ≫ tensorTotalCofiberInvX F f G (p + q + 1) ≫
            (tensorTotalCofiberMap F f G).f (p + q + 1)) := by simp
        _ = _ := by erw [← hid, add_comp, Category.assoc, Category.assoc, h₂, h₁]
        _ = a := by rw [← Category.assoc, ← Category.assoc, ← add_comp, hid]; simp

/-- Taking the cofiber commutes with the actual first-factor signed tensor total. -/
noncomputable def tensorTotalCofiberIso :
    homotopyCofiber (mapBifunctorMap f (𝟙 G) F (ComplexShape.down ℕ)) ≅
      mapBifunctor (homotopyCofiber f) G F (ComplexShape.down ℕ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n =>
      { hom := (tensorTotalCofiberMap F f G).f n
        inv := tensorTotalCofiberInvX F f G n
        hom_inv_id := tensorTotalCofiberMap_invX F f G n
        inv_hom_id := tensorTotalCofiberInvX_map F f G n })
    (fun i j _ => (tensorTotalCofiberMap F f G).comm i j)

/-- The isomorphism's forward map is the canonical cofiber-desc map. -/
@[simp]
theorem tensorTotalCofiberIso_hom :
    (tensorTotalCofiberIso F f G).hom = tensorTotalCofiberMap F f G := rfl

end Motivic.TorComparison
