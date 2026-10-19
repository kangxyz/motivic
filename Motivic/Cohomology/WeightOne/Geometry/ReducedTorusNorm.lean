/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.Geometry.TorusNormRelation
public import Motivic.Aglib.Algebra.Homology.Sheafification.Singular
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products.ParameterProducts

/-! # The ordinary norm on the project's original reduced torus

The map is descended objectwise through the literal original cokernel. Its
naturality uses only ordinary graph restriction, not any asserted transfer
structure on global units. Singular complexes are sheafified only after their
original degreewise construction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

universe u

namespace Motivic.SmoothSiteTorusDivisor
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- The actual defining relation is annihilated before taking its cokernel. -/
theorem norm_relation_app (X : SmoothSite (Spec (.of k))) :
    (torusRelation k 1).app (op (Cor.mk X)) ≫ norm.app (op X) = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change norm.app (op X) ((torusRelation k 1).app (op (Cor.mk X)) s) = 0
  rw [torusRelation_app_apply]
  simp only [Fin.sum_univ_one]
  exact congrArg (fun η => η.app (op X)
    ((biproduct.π (fun _ : Fin 1 => (torusRepresentable k 0).obj) 0).app
      (op (Cor.mk X)) s)) (norm_identityAxis (k := k))

/-- Descend through the actual evaluated original cokernel, not a replacement quotient. -/
def reducedNormApp (X : SmoothSite (Spec (.of k))) :
    ((toPresheaf k).obj (reducedTorus k 1)).obj (op X) ⟶
      (SmoothSite.largeUnitsPresheaf (Spec (.of k))).obj (op X) :=
  (PreservesCokernel.iso
    ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op (Cor.mk X))) (torusRelation k 1)).hom ≫
      cokernel.desc ((torusRelation k 1).app (op (Cor.mk X)))
        (norm.app (op X)) (norm_relation_app X)

/-- The descended ordinary map agrees with the norm on every original signed cycle. -/
@[reassoc] theorem toReduced_reducedNormApp (X : SmoothSite (Spec (.of k))) :
    ((toPresheaf k).map (toReducedTorus k 1)).app (op X) ≫ reducedNormApp X =
      norm.app (op X) := by
  change ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op (Cor.mk X))).map
    (cokernel.π (torusRelation k 1)) ≫
      ((PreservesCokernel.iso
        ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op (Cor.mk X)))
        (torusRelation k 1)).hom ≫ _) = _
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

/-- The norm on the actual reduced torus is natural for all ordinary smooth-site maps. -/
def reducedNorm : (toPresheaf k).obj (reducedTorus k 1) ⟶
    SmoothSite.largeUnitsPresheaf (Spec (.of k)) where
  app X := reducedNormApp X.unop
  naturality {X Y} f := by
    let q := (toPresheaf k).map (toReducedTorus k 1)
    have : Epi (q.app X) := by
      change Epi ((cokernel.π (torusRelation k 1)).app (op (Cor.mk X.unop)))
      infer_instance
    apply (cancel_epi (q.app X)).mp
    calc
      q.app X ≫ ((toPresheaf k).obj (reducedTorus k 1)).map f ≫ reducedNormApp Y.unop =
          ((toPresheaf k).obj (torusRepresentable k 1)).map f ≫
            q.app Y ≫ reducedNormApp Y.unop := by rw [← q.naturality_assoc]
      _ = ((toPresheaf k).obj (torusRepresentable k 1)).map f ≫ norm.app Y := by
        rw [toReduced_reducedNormApp]
      _ = norm.app X ≫ (SmoothSite.largeUnitsPresheaf (Spec (.of k))).map f :=
        norm.naturality f
      _ = q.app X ≫ reducedNormApp X.unop ≫
          (SmoothSite.largeUnitsPresheaf (Spec (.of k))).map f := by
        rw [← Category.assoc, toReduced_reducedNormApp]

/-- The global ordinary descended map recovers the original norm along the original quotient. -/
@[reassoc] theorem toReduced_reducedNorm :
    (toPresheaf k).map (toReducedTorus k 1) ≫ reducedNorm = norm := by
  apply NatTrans.ext
  funext X
  exact toReduced_reducedNormApp X.unop

/-- The explicit integral-affine formula retains the actual first torus-power coordinate. -/
theorem reducedNorm_affine_apply (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left]
    (z : Cor.mk X ⟶ Cor.mk (SmoothSite.torusPower (.of k) 1)) :
    reducedNorm.app (op X) ((toReducedTorus k 1).hom.app (op (Cor.mk X)) (ULift.up z)) =
      ULift.up (affinePowerOneNorm X z) := by
  have h := congrArg (fun η => η.app (op X) (ULift.up z))
    (toReduced_reducedNorm (k := k))
  rw [norm_app] at h
  exact h

/-- The original reduced singular complex maps to the genuine unit singular complex,
sheafifying after singular chains in every degree. -/
def reducedNormSheafMap :
    SingularComplex.sheafObj (SmoothSite.nisnevichTopology (Spec (.of k)))
        (cosimplicialSmoothSite k)
        ((toPresheaf k).obj (reducedTorus k 1)) ⟶
      SingularComplex.sheafObj (SmoothSite.nisnevichTopology (Spec (.of k)))
        (cosimplicialSmoothSite k)
        (SmoothSite.largeUnitsPresheaf (Spec (.of k))) :=
  (SingularComplex.sheafFunctor (SmoothSite.nisnevichTopology (Spec (.of k)))
    (cosimplicialSmoothSite k)).map reducedNorm

/-- Each degree is the native sheafification of the original parameter-wise norm. -/
theorem reducedNormSheafMap_f (n : ℕ) :
    (reducedNormSheafMap (k := k)).f n =
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).map
        ((SingularComplex.presheafMap (cosimplicialSmoothSite k)
          reducedNorm).f n) := rfl

end Motivic.SmoothSiteTorusDivisor
