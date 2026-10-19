/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Sheafification.MiddleLift

/-!
# Whole-cylinder lifting from a middle difference-zero relation

This additive adapter retains every original cover, section and restriction.
Only E3 is supplied in difference-zero form; the existing middle-lift theorem
still owns the construction. This conditional helper does not itself produce
the geometric witnesses or any middle relation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
universe u
namespace Motivic.PresheafWithTransfers
variable {k : Type u} [Field k]

/-- Difference-form middle lifting. Only the generic additive transfer law is
used to recover the old E3 equality; every geometric witness and the remaining
three middle relations are passed unchanged to the existing lifting theorem. -/
theorem nisnevichImage_wholeCylinder_lift_of_middle_difference_relations
    (P : PresheafWithTransfers.{u + 1} k)
    {X U U' T A V B A' V' : SmoothSite (Spec (.of k))}
    (j : U ⟶ X) (l : U' ⟶ U) [IsOpenImmersion j.left] [IsOpenImmersion l.left]
    (hne : Nonempty U'.left) (e : T ≅ SmoothSite.a1Cylinder (.of k) U)
    (h : SmoothSite.a1Cylinder (.of k) U' ⟶ T)
    (he : h ≫ e.hom = SmoothSite.a1Map (.of k) l)
    (i : A ⟶ T) (v : V ⟶ T) (bA : B ⟶ A) (bV : B ⟶ V)
    (i' : A' ⟶ SmoothSite.a1Cylinder (.of k) U')
    (v' : V' ⟶ SmoothSite.a1Cylinder (.of k) U')
    (rA : A' ⟶ A) (rV : V' ⟶ V)
    (hi : rA ≫ i = i' ≫ h) (hv : rV ≫ v = v' ≫ h)
    (hcover : Sieve.ofTwoArrows i' v' ∈
      SmoothSite.nisnevichTopology (Spec (.of k)) (SmoothSite.a1Cylinder (.of k) U'))
    (lambdaA : Cor.mk (SmoothSite.a1Cylinder (.of k) U') ⟶ Cor.mk A)
    (lambdaB : Cor.mk V' ⟶ Cor.mk B) (ψ : Cor.mk A' ⟶ Cor.mk B)
    (hBu : (nisnevichImage P).transfer (lambdaB ≫ (Cor.graphFunctor k).map bV) =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map rV))
    (hBgzero : (nisnevichImage P).transfer
      (Sub.sub (α := Cor.mk V' ⟶ Cor.mk A)
        (lambdaB ≫ (Cor.graphFunctor k).map bA)
        ((Cor.graphFunctor k).map v' ≫ lambdaA)) = 0)
    (hψu : (nisnevichImage P).transfer (ψ ≫ (Cor.graphFunctor k).map bV) = 0)
    (hA : (nisnevichImage P).transfer
      (Sub.sub (α := Cor.mk A' ⟶ Cor.mk A)
        ((Cor.graphFunctor k).map i' ≫ lambdaA)
        (ψ ≫ (Cor.graphFunctor k).map bA)) =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map rA))
    (g : ((nisnevichSheafify k).obj P).obj.sections
      (Cor.mk (SmoothSite.a1Cylinder (.of k) X)))
    (sA : (nisnevichImage P).sections (Cor.mk A))
    (sV : (nisnevichImage P).sections (Cor.mk V))
    (hm : (nisnevichImage P).transfer ((Cor.graphFunctor k).map bA) sA =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map bV) sV)
    (huA : (nisnevichImageι P).hom.app (op (Cor.mk A)) sA =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (i ≫ e.hom ≫ SmoothSite.a1Map (.of k) j)) g)
    (huV : (nisnevichImageι P).hom.app (op (Cor.mk V)) sV =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (v ≫ e.hom ≫ SmoothSite.a1Map (.of k) j)) g) :
    IsOpenImmersion (l ≫ j).left ∧ Nonempty U'.left ∧
      ∃ t : (nisnevichImage P).sections (Cor.mk (SmoothSite.a1Cylinder (.of k) U')),
        (nisnevichImageι P).hom.app (op (Cor.mk (SmoothSite.a1Cylinder (.of k) U'))) t =
          ((nisnevichSheafify k).obj P).obj.transfer
            ((Cor.graphFunctor k).map (SmoothSite.a1Map (.of k) (l ≫ j))) g := by
  have hBg : (nisnevichImage P).transfer (lambdaB ≫ (Cor.graphFunctor k).map bA) =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map v' ≫ lambdaA) := by
    exact sub_eq_zero.mp ((transfer_sub (nisnevichImage P)
      (lambdaB ≫ (Cor.graphFunctor k).map bA)
      ((Cor.graphFunctor k).map v' ≫ lambdaA)).symm.trans hBgzero)
  exact nisnevichImage_wholeCylinder_lift_of_middle_relations P j l hne e h he
    i v bA bV i' v' rA rV hi hv hcover lambdaA lambdaB ψ
    hBu hBg hψu hA g sA sV hm huA huV

end Motivic.PresheafWithTransfers
