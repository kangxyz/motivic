/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.FiniteScalarDescent

/-!
# Actual scalar traces of original signed restriction differences

All corrections live on scalar extensions of one fixed original diagram. The
trace is the action of the constructed finite-flat correspondence, not an
assumed action on a relative boundary sheaf. No coefficient sheafification or
homotopy invariance is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)
variable {E : Type u} [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]

/-- On original sections, a flat restriction commutes with the actual scalar trace. -/
theorem finiteScalarTrace_restriction_apply
    {U X : SmoothSite (Spec (.of k))} (j : U ⟶ X) [Flat j.left]
    (s : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := E) X))) :
    transfer P ((Cor.graphFunctor k).map j)
        (transfer P (Cor.finiteFlatTrace
          (SmoothSite.finiteScalarProjection (E := E) X)) s) =
      transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) U))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.finiteScalarMap (E := E) j)) s) :=
  (ConcreteCategory.congr_hom (finiteScalarTrace_naturality (E := E) P j) s).symm

/-- Trace of an actual scalar restriction is the whole extension degree. -/
theorem finiteScalarTrace_scalarRestriction_apply
    (X : SmoothSite (Spec (.of k))) (s : sections P (Cor.mk X)) :
    transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) X))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.finiteScalarProjection (E := E) X)) s) =
      (Module.finrank k E : ℤ) • s :=
  ConcreteCategory.congr_hom (finiteScalar_restriction_trace (E := E) P X) s

/-- An extended signed relation yields degree times the original relation.
Only the two correction legs must be flat; the original generator leg is arbitrary. -/
theorem finiteScalarTrace_restriction_difference
    {O T A D : SmoothSite (Spec (.of k))}
    (β : O ⟶ T) [Flat β.left] (α : O ⟶ A) [Flat α.left] (φ : O ⟶ D)
    (s : sections P (Cor.mk D))
    (a : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := E) T)))
    (c : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := E) A)))
    (h : transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) β)) a -
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) α)) c =
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) φ))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.finiteScalarProjection (E := E) D)) s)) :
    transfer P ((Cor.graphFunctor k).map β)
        (transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) T)) a) -
      transfer P ((Cor.graphFunctor k).map α)
        (transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) A)) c) =
      (Module.finrank k E : ℤ) • transfer P ((Cor.graphFunctor k).map φ) s := by
  have ht := congrArg
    (transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) O))) h
  rw [map_sub, ← finiteScalarTrace_restriction_apply,
    ← finiteScalarTrace_restriction_apply] at ht
  have hr := ConcreteCategory.congr_hom
    (finiteScalarRestriction_naturality (E := E) P φ) s
  simp only [ConcreteCategory.comp_apply] at hr
  rw [← hr, finiteScalarTrace_scalarRestriction_apply] at ht
  exact ht

variable {L : Type u} [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

/-- Actual coprime traces descend signed correction witnesses on one unchanged
diagram. Arbitrary extension refinements are not identified or descended here. -/
theorem exists_restriction_difference_of_coprime_finiteScalar
    {O T A D : SmoothSite (Spec (.of k))}
    (β : O ⟶ T) [Flat β.left] (α : O ⟶ A) [Flat α.left] (φ : O ⟶ D)
    (s : sections P (Cor.mk D))
    (hE : ∃ (a : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := E) T)))
      (c : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := E) A))),
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) β)) a -
        transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) α)) c =
        transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) φ))
          (transfer P ((Cor.graphFunctor k).map
            (SmoothSite.finiteScalarProjection (E := E) D)) s))
    (hL : ∃ (a : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := L) T)))
      (c : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := L) A))),
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) β)) a -
        transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) α)) c =
        transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) φ))
          (transfer P ((Cor.graphFunctor k).map
            (SmoothSite.finiteScalarProjection (E := L) D)) s))
    (hdegree : (Module.finrank k E).Coprime (Module.finrank k L)) :
    ∃ (a : sections P (Cor.mk T)) (c : sections P (Cor.mk A)),
      transfer P ((Cor.graphFunctor k).map β) a -
        transfer P ((Cor.graphFunctor k).map α) c =
        transfer P ((Cor.graphFunctor k).map φ) s := by
  obtain ⟨aE, cE, hE⟩ := hE
  obtain ⟨aL, cL, hL⟩ := hL
  let m := Module.finrank k E
  let n := Module.finrank k L
  let a := transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) T)) aE
  let b := transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := L) T)) aL
  let c := transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) A)) cE
  let d := transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := L) A)) cL
  have he : transfer P ((Cor.graphFunctor k).map β) a -
      transfer P ((Cor.graphFunctor k).map α) c =
      (m : ℤ) • transfer P ((Cor.graphFunctor k).map φ) s :=
    finiteScalarTrace_restriction_difference P β α φ s aE cE hE
  have hl : transfer P ((Cor.graphFunctor k).map β) b -
      transfer P ((Cor.graphFunctor k).map α) d =
      (n : ℤ) • transfer P ((Cor.graphFunctor k).map φ) s :=
    finiteScalarTrace_restriction_difference P β α φ s aL cL hL
  refine ⟨Nat.gcdA m n • a + Nat.gcdB m n • b,
    Nat.gcdA m n • c + Nat.gcdB m n • d, ?_⟩
  simp only [map_add, map_zsmul]
  calc
    _ = Nat.gcdA m n • (transfer P ((Cor.graphFunctor k).map β) a -
          transfer P ((Cor.graphFunctor k).map α) c) +
        Nat.gcdB m n • (transfer P ((Cor.graphFunctor k).map β) b -
          transfer P ((Cor.graphFunctor k).map α) d) := by
      simp only [smul_sub]
      abel
    _ = (Nat.gcdA m n * (m : ℤ) + Nat.gcdB m n * (n : ℤ)) •
        transfer P ((Cor.graphFunctor k).map φ) s := by
      rw [he, hl, smul_smul, smul_smul, add_smul]
    _ = transfer P ((Cor.graphFunctor k).map φ) s := by
      have h : Nat.gcdA m n * (m : ℤ) + Nat.gcdB m n * (n : ℤ) = 1 := by
        rw [mul_comm (Nat.gcdA m n), mul_comm (Nat.gcdB m n),
          ← Nat.gcd_eq_gcd_ab, hdegree.gcd_eq_one, Nat.cast_one]
      rw [h, one_smul]

end Motivic.PresheafWithTransfers
