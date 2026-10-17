/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleImageExact
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! # A zero cokernel germ gives an actual pointed local lift -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {S : Scheme.{u}} (Φ : (nisnevichTopology S).Point.{u + 1})

/-- Membership in the image on the genuine point fiber is witnessed on an actual
common pointed neighborhood, with the original section retained. -/
theorem exists_pointed_local_lift_of_fiber_image
    {P Q : (FiniteEtaleSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : P ⟶ Q)
    (V : FiniteEtaleSite S) (v : Φ.fiber.obj V) (s : Q.obj (op V))
    (h : ∃ t : (Φ.presheafFiber.obj P : AddCommGrpCat.{u + 1}),
      Φ.presheafFiber.map f t = Φ.toPresheafFiber V v Q s) :
    ∃ (W : FiniteEtaleSite S) (a : W ⟶ V) (w : Φ.fiber.obj W)
      (t : P.obj (op W)), Φ.fiber.map a w = v ∧ f.app (op W) t = Q.map a.op s := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨U, u, t, rfl⟩ := Φ.toPresheafFiber_jointly_surjective t
  obtain ⟨N, a, b, _⟩ := IsCofilteredOrEmpty.cone_objs
    (Functor.elementsMk Φ.fiber V v) (Functor.elementsMk Φ.fiber U u)
  have he : Φ.toPresheafFiber N.obj N.val Q (f.app (op N.obj) (P.map b.hom.op t)) =
      Φ.toPresheafFiber N.obj N.val Q (Q.map a.hom.op s) := by
    rw [NatTrans.naturality_apply, Φ.toPresheafFiber_w_apply,
      Φ.toPresheafFiber_w_apply, a.map_val, b.map_val]
    exact (Φ.toPresheafFiber_naturality_apply f U u t).symm.trans ht
  obtain ⟨W, c, w, hc, heq⟩ := (Φ.toPresheafFiber_eq_iff' _ _ _ _).mp he
  refine ⟨W, c ≫ a.hom, w, P.map c.op (P.map b.hom.op t), ?_, ?_⟩
  · simp only [Functor.map_comp, types_comp_apply, hc]
    exact a.map_val
  · rw [NatTrans.naturality_apply, heq]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Exactness of the original sheaf point fiber turns a zero cokernel germ into
an actual pointed local preimage. No global section-surjectivity is asserted. -/
theorem exists_pointed_local_lift_of_cokernel_germ_zero
    {F G : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (V : FiniteEtaleSite S) (v : Φ.fiber.obj V) (s : G.obj.obj (op V))
    (h : Φ.toPresheafFiber V v (cokernel f).obj
      ((cokernel.π f).hom.app (op V) s) = 0) :
    ∃ (W : FiniteEtaleSite S) (a : W ⟶ V) (w : Φ.fiber.obj W)
      (t : F.obj.obj (op W)),
      Φ.fiber.map a w = v ∧ f.hom.app (op W) t = G.obj.map a.op s := by
  let C := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hC := (ShortComplex.exact_cokernel f).map (Φ.sheafFiber (A := AddCommGrpCat.{u + 1}))
  apply exists_pointed_local_lift_of_fiber_image Φ f.hom V v s
  apply (ShortComplex.ab_exact_iff (C.map Φ.sheafFiber)).mp hC
  change Φ.presheafFiber.map (cokernel.π f).hom (Φ.toPresheafFiber V v G.obj s) = 0
  rw [Φ.toPresheafFiber_naturality_apply]
  exact h

end Motivic.FiniteEtaleSite
