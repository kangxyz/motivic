/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.FiniteScalarTrace
public import Mathlib.Data.Int.GCD

/-!
# Descent of original local factorizations by two scalar extensions

The finite-extension factorization maps remain explicit inputs. All scalar
restrictions, traces, and their degree and naturality equations are the actual
maps of the unchanged presheaf with transfers. The two factorizations land on
the same original open object, so their signed combination is meaningful.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)
variable {E : Type u} [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]

/-- Original scalar restriction is natural for every original scheme map. -/
theorem finiteScalarRestriction_naturality {V X : SmoothSite (Spec (.of k))}
    (j : V ⟶ X) :
    transfer P ((Cor.graphFunctor k).map j) ≫
        transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarProjection (E := E) V)) =
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarProjection (E := E) X)) ≫
        transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) j)) := by
  have h : SmoothSite.finiteScalarMap (E := E) j ≫
      SmoothSite.finiteScalarProjection (E := E) X =
      SmoothSite.finiteScalarProjection (E := E) V ≫ j := by
    apply MorphismProperty.Over.Hom.ext
    exact (SmoothSite.finiteScalarMap_isPullback (E := E) j).w.symm
  have he := congrArg (fun f => transfer P ((Cor.graphFunctor k).map f)) h
  simpa only [Functor.map_comp, transfer_comp] using he.symm

/-- Push an extended local factorization back using the original scalar trace. -/
def finiteScalarFactorization {U V : SmoothSite (Spec (.of k))}
    (φ : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := E) V)) ⟶
      sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := E) U))) :
    sections P (Cor.mk V) ⟶ sections P (Cor.mk U) :=
  transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarProjection (E := E) V)) ≫
    φ ≫ transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) U))

/-- A genuine extended factorization descends to degree times the original
restriction, with the actual common target object unchanged. -/
theorem restriction_finiteScalarFactorization {U V X : SmoothSite (Spec (.of k))}
    (j : V ⟶ X) (a : U ⟶ X) [Flat a.left]
    (φ : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := E) V)) ⟶
      sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := E) U)))
    (hφ : transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) j)) ≫ φ =
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) a))) :
    transfer P ((Cor.graphFunctor k).map j) ≫ finiteScalarFactorization P φ =
      (Module.finrank k E : ℤ) • transfer P ((Cor.graphFunctor k).map a) := by
  rw [finiteScalarFactorization, ← Category.assoc, finiteScalarRestriction_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc _ φ, hφ, finiteScalarTrace_naturality, ← Category.assoc,
    finiteScalar_restriction_trace, Preadditive.zsmul_comp]
  rfl

variable {L : Type u} [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

/-- Two coprime finite separable scalar extensions give an original local
factorization. No abstract trace action or degree premise is supplied. -/
theorem exists_factorization_of_coprime_finiteScalar
    {U V X : SmoothSite (Spec (.of k))} (j : V ⟶ X) (a : U ⟶ X) [Flat a.left]
    (φ : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := E) V)) ⟶
      sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := E) U)))
    (ψ : sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := L) V)) ⟶
      sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := L) U)))
    (hφ : transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) j)) ≫ φ =
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) a)))
    (hψ : transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) j)) ≫ ψ =
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := L) a)))
    (hdegree : (Module.finrank k E).Coprime (Module.finrank k L)) :
    ∃ θ : sections P (Cor.mk V) ⟶ sections P (Cor.mk U),
      transfer P ((Cor.graphFunctor k).map j) ≫ θ =
        transfer P ((Cor.graphFunctor k).map a) := by
  let m := Module.finrank k E
  let n := Module.finrank k L
  refine ⟨Nat.gcdA m n • finiteScalarFactorization P φ +
    Nat.gcdB m n • finiteScalarFactorization P ψ, ?_⟩
  rw [Preadditive.comp_add, Preadditive.comp_zsmul, Preadditive.comp_zsmul,
    restriction_finiteScalarFactorization P j a φ hφ,
    restriction_finiteScalarFactorization P j a ψ hψ,
    smul_smul, smul_smul, ← add_smul]
  have h : Nat.gcdA m n * (m : ℤ) + Nat.gcdB m n * (n : ℤ) = 1 := by
    rw [mul_comm (Nat.gcdA m n), mul_comm (Nat.gcdB m n), ← Nat.gcd_eq_gcd_ab,
      hdegree.gcd_eq_one, Nat.cast_one]
  rw [h, one_smul]

end Motivic.PresheafWithTransfers
