/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Divisors.Order.IdealFrameOrderCancellation
public import Motivic.Aglib.RingTheory.Norm.FiniteFree.Fitting
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # The norm ideal in an actual affine closed triangle

Both closed maps have the same source, with their original ideal frames. The
quotient equivalence is constructed from these maps and their commutation, not
assumed. The common affine neighborhood and any graph specialization are separate.


Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.AffineClosedTriangle`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.OpenGraphTriangle`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {A B D : Scheme.{u}} [IsAffine A] [IsAffine B]
  (p : B ⟶ A) (iB : D ⟶ B) [IsClosedImmersion iB]
  (iA : D ⟶ A) [IsClosedImmersion iA] (h : iB ≫ p = iA)
  (hB : IsLocallyRankOne B (idealModule iB))
  (hA : IsLocallyRankOne A (idealModule iA))
  (eB : (idealModule iB).over ⊤ ≅ SheafOfModules.unit (B.ringCatSheaf.over ⊤))
  (eA : (idealModule iA).over ⊤ ≅ SheafOfModules.unit (A.ringCatSheaf.over ⊤))

/-- The original closed triangle gives a quotient equivalence over the actual
ring of target sections, retaining both exact ideal-frame generators. -/
def affineClosedTriangleQuotientEquiv :
    let : Algebra Γ(A, ⊤) Γ(B, ⊤) := p.appTop.hom.toAlgebra
    (Γ(B, ⊤) ⧸ Ideal.span {idealFrameScalar iB ⊤ eB}) ≃ₐ[Γ(A, ⊤)]
      (Γ(A, ⊤) ⧸ Ideal.span {idealFrameScalar iA ⊤ eA}) := by
  let : Algebra Γ(A, ⊤) Γ(B, ⊤) := p.appTop.hom.toAlgebra
  let : Algebra Γ(A, ⊤) Γ(D, ⊤) := iA.appTop.hom.toAlgebra
  let fB : Γ(B, ⊤) →ₐ[Γ(A, ⊤)] Γ(D, ⊤) :=
    { iB.appTop.hom with
      commutes' := fun a => by
        change (p.appTop ≫ iB.appTop) a = iA.appTop a
        rw [← Scheme.Hom.comp_appTop, h] }
  let fA : Γ(A, ⊤) →ₐ[Γ(A, ⊤)] Γ(D, ⊤) :=
    { iA.appTop.hom with commutes' := fun _ => rfl }
  have hfB : Function.Surjective fB := iB.app_surjective ⊤ (isAffineOpen_top B)
  have hfA : Function.Surjective fA := iA.app_surjective ⊤ (isAffineOpen_top A)
  have hkB : RingHom.ker fB.toRingHom = Ideal.span {idealFrameScalar iB ⊤ eB} :=
    ker_app_eq_span_idealFrameScalar iB hB ⊤ eB
  have hkA : RingHom.ker fA.toRingHom = Ideal.span {idealFrameScalar iA ⊤ eA} :=
    ker_app_eq_span_idealFrameScalar iA hA ⊤ eA
  exact ((Ideal.quotientEquivAlgOfEq Γ(A, ⊤) hkB.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hfB)).trans
    ((Ideal.quotientEquivAlgOfEq Γ(A, ⊤) hkA.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hfA)).symm

include h hB hA in
/-- The literal graph-compatible closed triangle identifies the norm ideal. Only
freeness of the original finite map's section module remains a chart hypothesis. -/
theorem span_norm_idealFrameScalar_eq [IsFinite p] :
    let : Algebra Γ(A, ⊤) Γ(B, ⊤) := p.appTop.hom.toAlgebra
    ∀ [Module.Free Γ(A, ⊤) Γ(B, ⊤)],
      Ideal.span {Algebra.norm Γ(A, ⊤) (idealFrameScalar iB ⊤ eB)} =
        Ideal.span {idealFrameScalar iA ⊤ eA} := by
  dsimp only
  let : Algebra Γ(A, ⊤) Γ(B, ⊤) := p.appTop.hom.toAlgebra
  intro hfree
  let := hfree
  let : Module.Finite Γ(A, ⊤) Γ(B, ⊤) := p.finite_appTop
  exact Algebra.span_norm_eq_of_quotient_linearEquiv _ _
    (affineClosedTriangleQuotientEquiv p iB iA h hB hA eB eA).toLinearEquiv

end AlgebraicGeometry.Scheme.Hom
