/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.ContractionExterior
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.ContractionGeometry
public import Motivic.Aglib.AlgebraicGeometry.LaurentGeometricIntegrality
public import Motivic.Aglib.CategoryTheory.CokernelAdditive
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Contraction of actual presheaves with transfers

`contraction P` is the cokernel of restriction from the actual affine-line
product to its Laurent principal open. Its transfer action descends the actual
signed exterior correspondence, and its sections are the literal group quotient.
No sheafification or strict homotopy invariance is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k]

instance affineLine_geometricallyIntegral :
    GeometricallyIntegral (SmoothSite.affineLine (.of k)).hom :=
  inferInstanceAs (GeometricallyIntegral
    (AlgebraicGeometry.Scheme.PolynomialLaurent.polynomialProjection (.of k)))

instance torus_geometricallyIntegral :
    GeometricallyIntegral (SmoothSite.torus (.of k)).hom :=
  inferInstanceAs (GeometricallyIntegral
    (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection (.of k)))

/-- Coefficients on the genuine affine-line cylinder. -/
abbrev affineLineSections (P : PresheafWithTransfers.{v} k) : PresheafWithTransfers.{v} k :=
  withParameter P (SmoothSite.affineLine (.of k))

/-- Coefficients on the genuine Laurent cylinder. -/
abbrev torusSections (P : PresheafWithTransfers.{v} k) : PresheafWithTransfers.{v} k :=
  withParameter P (SmoothSite.torus (.of k))

/-- Restriction along the literal Laurent open inclusion. -/
def contractionRestriction (P : PresheafWithTransfers.{v} k) :
    affineLineSections P ⟶ torusSections P :=
  parameterPullback P (SmoothSite.torusInAffineLine (.of k))

@[simp] theorem contractionRestriction_app (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    (contractionRestriction P).hom.app (op X) =
      transfer P ((Cor.graphFunctor k).map
        (SmoothSite.contractionOpen (.of k) X.toSmoothSite)) := rfl

/-- The actual contraction, with additive transfers induced by exterior signed cycles. -/
def contraction (P : PresheafWithTransfers.{v} k) : PresheafWithTransfers.{v} k :=
  ⟨cokernel (contractionRestriction P).hom,
    Functor.cokernel_additive (contractionRestriction P).hom⟩

/-- The canonical quotient from Laurent-cylinder sections. -/
def toContraction (P : PresheafWithTransfers.{v} k) : torusSections P ⟶ contraction P :=
  ⟨cokernel.π (contractionRestriction P).hom⟩

@[reassoc (attr := simp)] theorem contractionRestriction_toContraction
    (P : PresheafWithTransfers.{v} k) :
    contractionRestriction P ≫ toContraction P = 0 := by
  apply ObjectProperty.hom_ext
  exact cokernel.condition _

/-- The quotient map commutes with arbitrary genuine signed transfers. -/
@[reassoc] theorem toContraction_naturality (P : PresheafWithTransfers.{v} k)
    {X Y : Cor k} (α : X ⟶ Y) :
    transfer (torusSections P) α ≫ (toContraction P).hom.app (op X) =
      (toContraction P).hom.app (op Y) ≫ transfer (contraction P) α :=
  transfer_naturality (toContraction P) α

/-- On a represented quotient class the transfer is precisely exterior pullback. -/
theorem contraction_transfer_apply (P : PresheafWithTransfers.{v} k)
    {X Y : Cor k} (α : X ⟶ Y) (s : sections (torusSections P) Y) :
    transfer (contraction P) α ((toContraction P).hom.app (op Y) s) =
      (toContraction P).hom.app (op X)
        (transfer P (FiniteCorrespondence.exteriorIdentity
          (X := X.toSmoothSite) (Y := Y.toSmoothSite) (SmoothSite.torus (.of k)) α) s) :=
  (NatTrans.naturality_apply (toContraction P).hom α.op s).symm

/-- Graph restrictions use exactly the actual relative product of the scheme map. -/
theorem contraction_graph_apply (P : PresheafWithTransfers.{v} k)
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y)
    (s : sections (torusSections P) (Cor.mk Y)) :
    transfer (contraction P) ((Cor.graphFunctor k).map f)
        ((toContraction P).hom.app (op (Cor.mk Y)) s) =
      (toContraction P).hom.app (op (Cor.mk X))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.productMap f (𝟙 (SmoothSite.torus (.of k))))) s) := by
  have h := contraction_transfer_apply P (X := Cor.mk X) (Y := Cor.mk Y)
    ((Cor.graphFunctor k).map f) s
  change _ = (toContraction P).hom.app (op (Cor.mk X))
      (transfer P ((Cor.parameterProduct _).map ((Cor.graphFunctor k).map f)) s) at h
  rw [Cor.parameterProduct_graph] at h
  exact h

/-- Every contraction section has a genuine Laurent-cylinder representative. -/
theorem toContraction_surjective (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    Function.Surjective ((toContraction P).hom.app (op X)) := by
  change Function.Surjective ((cokernel.π (contractionRestriction P).hom).app (op X))
  exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance

/-- Objectwise contraction is the ordinary quotient by the actual open-restriction image. -/
def contractionSectionsIsoQuotient (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    sections (contraction P) X ≅ AddCommGrpCat.of
      (sections (torusSections P) X ⧸
        ((contractionRestriction P).hom.app (op X)).hom.range) :=
  PreservesCokernel.iso ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op X))
      (contractionRestriction P).hom ≪≫
    AddCommGrpCat.cokernelIsoQuotient ((contractionRestriction P).hom.app (op X))

/-- Descend a transfer-natural map killing the actual affine-line restriction. -/
def contractionDesc (P : PresheafWithTransfers.{v} k)
    {Q : PresheafWithTransfers.{v} k} (η : torusSections P ⟶ Q)
    (hη : contractionRestriction P ≫ η = 0) : contraction P ⟶ Q :=
  ⟨cokernel.desc _ η.hom (congrArg (fun f => f.hom) hη)⟩

@[reassoc (attr := simp)] theorem toContraction_desc (P : PresheafWithTransfers.{v} k)
    {Q : PresheafWithTransfers.{v} k} (η : torusSections P ⟶ Q)
    (hη : contractionRestriction P ≫ η = 0) :
    toContraction P ≫ contractionDesc P η hη = η := by
  apply ObjectProperty.hom_ext
  exact cokernel.π_desc _ _ _

/-- Coefficient natural transformations induce genuine contraction morphisms. -/
def contractionMap {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q) :
    contraction P ⟶ contraction Q :=
  contractionDesc P (withParameterMap η (SmoothSite.torus (.of k)) ≫ toContraction Q) (by
    rw [← Category.assoc, contractionRestriction, parameterPullback_coefficient_naturality,
      Category.assoc]
    change withParameterMap η (SmoothSite.affineLine (.of k)) ≫
      (contractionRestriction Q ≫ toContraction Q) = 0
    rw [contractionRestriction_toContraction, comp_zero])

@[reassoc (attr := simp)] theorem toContraction_map
    {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q) :
    toContraction P ≫ contractionMap η =
      withParameterMap η (SmoothSite.torus (.of k)) ≫ toContraction Q :=
  toContraction_desc P _ _

end Motivic.PresheafWithTransfers
