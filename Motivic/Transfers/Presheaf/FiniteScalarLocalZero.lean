/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.FiniteScalarComparison
public import Motivic.Transfers.Presheaf.FiniteScalarDescent
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.FiniteScalarMarkedOpen

/-! # Original local zeros from two actual scalar zero opens

The coefficient universe is independent of the geometric universe. Actual
scalar restriction followed by trace gives degree annihilation on the same
original open. Bezout then gives an original local zero, without a sheaf
separation hypothesis, a factorization family, or a scalar presentation input.
The scalar zeros themselves remain explicit section-specific hypotheses.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe w u

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]
  (P : PresheafWithTransfers.{w} k)

/-- Scalar extension preserves an actual original restricted zero, through the
canonical native coefficient and section comparison maps. -/
theorem native_scalar_restriction_eq_zero_of_restriction_eq_zero
    {U X : SmoothSite (Spec (.of k))} (a : U ⟶ X) (s : sections P (Cor.mk X))
    (hs : transfer P ((Cor.graphFunctor k).map a) s = 0) :
    transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        ((SmoothSite.fieldBaseChange (algebraMap k L)).map a))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := L) X)) s) = 0 := by
  have hn := ConcreteCategory.congr_hom
    (finiteScalarSectionIso_naturality (L := L) P a)
    (transfer P ((Cor.graphFunctor k).map
      (SmoothSite.fieldBaseChangeForgetProjection (L := L) X)) s)
  have hp := ConcreteCategory.congr_hom
    (finiteScalarSectionIso_projection (L := L) P X) s
  have hr := ConcreteCategory.congr_hom
    (finiteScalarRestriction_naturality (E := L) P a) s
  simp only [ConcreteCategory.comp_apply] at hn hp hr
  erw [hp, ← hr, hs, map_zero] at hn
  apply (AddCommGrpCat.mono_iff_injective (finiteScalarSectionIso (L := L) P U).hom).mp
    inferInstance
  exact hn.trans (map_zero _).symm

/-- A native extended-coefficient zero along an original restriction kills that
original restricted section by the actual extension degree. No flatness is needed. -/
theorem finrank_smul_restriction_eq_zero_of_native_scalar_zero
    {U X : SmoothSite (Spec (.of k))} (a : U ⟶ X) (s : sections P (Cor.mk X))
    (hs : transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        ((SmoothSite.fieldBaseChange (algebraMap k L)).map a))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := L) X)) s) = 0) :
    (Module.finrank k L : ℤ) • transfer P ((Cor.graphFunctor k).map a) s = 0 := by
  have hn := ConcreteCategory.congr_hom
    (finiteScalarSectionIso_naturality (L := L) P a)
    (transfer P ((Cor.graphFunctor k).map
      (SmoothSite.fieldBaseChangeForgetProjection (L := L) X)) s)
  have hp := ConcreteCategory.congr_hom
    (finiteScalarSectionIso_projection (L := L) P X) s
  simp only [ConcreteCategory.comp_apply] at hn hp
  erw [hs, map_zero, hp] at hn
  have hr := ConcreteCategory.congr_hom
    (finiteScalarRestriction_naturality (E := L) P a) s
  simp only [ConcreteCategory.comp_apply] at hr
  apply finrank_smul_eq_zero_of_scalar_restriction_eq_zero (E := L) P U
  rw [hr]
  exact hn.symm

variable {E : Type u} [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]

/-- Two native scalar zeros on the same original object imply the original zero.
This is sectionwise degree descent, not descent of a whole factorization family. -/
theorem restriction_eq_zero_of_coprime_native_scalar_zeros
    {U X : SmoothSite (Spec (.of k))} (a : U ⟶ X) (s : sections P (Cor.mk X))
    (hE : transfer (finiteSeparableExtension E P) ((Cor.graphFunctor E).map
        ((SmoothSite.fieldBaseChange (algebraMap k E)).map a))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := E) X)) s) = 0)
    (hL : transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        ((SmoothSite.fieldBaseChange (algebraMap k L)).map a))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := L) X)) s) = 0)
    (hdegree : (Module.finrank k E).Coprime (Module.finrank k L)) :
    transfer P ((Cor.graphFunctor k).map a) s = 0 := by
  have he := finrank_smul_restriction_eq_zero_of_native_scalar_zero P a s hE
  have hl := finrank_smul_restriction_eq_zero_of_native_scalar_zero P a s hL
  let m := Module.finrank k E
  let n := Module.finrank k L
  have hg : Nat.gcdA m n * (m : ℤ) + Nat.gcdB m n * (n : ℤ) = 1 := by
    rw [mul_comm (Nat.gcdA m n), mul_comm (Nat.gcdB m n),
      ← Nat.gcd_eq_gcd_ab, hdegree.gcd_eq_one, Nat.cast_one]
  have h := congrArg (fun z : ℤ => z • transfer P ((Cor.graphFunctor k).map a) s) hg
  rw [add_smul, mul_smul, mul_smul, he, hl, smul_zero, smul_zero, zero_add,
    one_smul] at h
  exact h.symm

/-- Full-fiber scalar zero opens produce one original affine zero neighborhood.
All scalar factor maps are constructed from the actual original open. -/
theorem exists_affine_zero_open_of_coprime_scalar_zero_opens
    (X : SmoothSite (Spec (.of k))) (s : sections P (Cor.mk X)) (x : X.left)
    (V : ((SmoothSite.fieldBaseChange (algebraMap k E)).obj X).left.Opens)
    (W : ((SmoothSite.fieldBaseChange (algebraMap k L)).obj X).left.Opens)
    (hV : (SmoothSite.finiteScalarProjection (E := E) X).left ⁻¹' {x} ⊆
      (V : Set ((SmoothSite.fieldBaseChange (algebraMap k E)).obj X).left))
    (hW : (SmoothSite.finiteScalarProjection (E := L) X).left ⁻¹' {x} ⊆
      (W : Set ((SmoothSite.fieldBaseChange (algebraMap k L)).obj X).left))
    (zV : transfer (finiteSeparableExtension E P) ((Cor.graphFunctor E).map
        (SmoothSite.homMk (X := SmoothSite.mk (V.ι ≫
          ((SmoothSite.fieldBaseChange (algebraMap k E)).obj X).hom))
          (Y := (SmoothSite.fieldBaseChange (algebraMap k E)).obj X) V.ι rfl))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := E) X)) s) = 0)
    (zW : transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        (SmoothSite.homMk (X := SmoothSite.mk (W.ι ≫
          ((SmoothSite.fieldBaseChange (algebraMap k L)).obj X).hom))
          (Y := (SmoothSite.fieldBaseChange (algebraMap k L)).obj X) W.ι rfl))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := L) X)) s) = 0)
    (hdegree : (Module.finrank k E).Coprime (Module.finrank k L)) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ x ∈ U ∧
      transfer P ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (U.ι ≫ X.hom)) (Y := X) U.ι rfl)) s = 0 := by
  obtain ⟨U, hU, hxU, _, _, eV, eW, heV, heW⟩ :=
    SmoothSite.exists_common_affine_scalar_open X x V W hV hW
  refine ⟨U, hU, hxU, ?_⟩
  apply restriction_eq_zero_of_coprime_native_scalar_zeros (E := E) (L := L) P _ s
      ?_ ?_ hdegree
  · rw [← heV, Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply, zV, map_zero]
  · rw [← heW, Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply, zW, map_zero]

end Motivic.PresheafWithTransfers
