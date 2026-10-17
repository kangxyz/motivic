/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.SingularComplexEndpoints
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex

/-!
# The prism endpoints land in the original transfer singular complex

The generic prism is specialized to the actual smooth algebraic simplex.
The target is transported through the established `singularParameterIso`,
so the endpoint maps land in the original `singularObj`, not a replacement
complex. No homotopy-invariance hypothesis on the coefficient is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Simplicial

universe u v

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- The ordinary coefficient with its fixed actual smooth parameter. -/
def prismCoefficient (P : PresheafWithTransfers.{v} k)
    (U : SmoothSite (Spec (.of k))) :
    (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{v} :=
  (prod.functor.obj U).op ⋙ (toPresheaf k).obj P

/-- Singular chains with the actual algebraic interval and smooth parameter. -/
def prismSource (P : PresheafWithTransfers.{v} k)
    (U : SmoothSite (Spec (.of k))) : ChainComplex AddCommGrpCat.{v} ℕ :=
  SingularComplex.obj
    (SingularComplex.Prism.cylinder (AlgebraicSimplex.cosimplicialSmoothSite k))
    (prismCoefficient P U)

/-- Endpoint pullback into the original transfer singular complex. -/
def singularPrismEndpoint (P : PresheafWithTransfers.{v} k)
    (U : SmoothSite (Spec (.of k))) (a : Fin 2) :
    prismSource P U ⟶ singularObj P (Cor.mk U) :=
  SingularComplex.geometryMap
      (SingularComplex.Prism.endpoint (AlgebraicSimplex.cosimplicialSmoothSite k) a)
      (prismCoefficient P U) ≫ (singularParameterIso P U).inv

/-- The actual endpoints are chain homotopic in every degree, with no HI assumption. -/
def singularPrismEndpointHomotopy (P : PresheafWithTransfers.{v} k)
    (U : SmoothSite (Spec (.of k))) :
    Homotopy (singularPrismEndpoint P U 0) (singularPrismEndpoint P U 1) :=
  (SingularComplex.Prism.endpointHomotopy
    (AlgebraicSimplex.cosimplicialSmoothSite k) (prismCoefficient P U)).compRight
      (singularParameterIso P U).inv

/-- All homology degrees of the original transfer complex see equal endpoint maps. -/
theorem singularPrismEndpoint_homologyMap_eq (P : PresheafWithTransfers.{v} k)
    (U : SmoothSite (Spec (.of k))) (n : ℕ) :
    HomologicalComplex.homologyMap (singularPrismEndpoint P U 0) n =
      HomologicalComplex.homologyMap (singularPrismEndpoint P U 1) n :=
  (singularPrismEndpointHomotopy P U).homologyMap_eq n

end Motivic.PresheafWithTransfers
