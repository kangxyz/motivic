/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalFamilyEndpoints
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.Endpoints
public import Motivic.Cohomology.A1.Basic


/-!
# Principal correspondence nullity on homotopy invariant presheaves

The homotopy and both correspondence endpoints are constructed by the original
principal family. This is a statement about ordinary presheaves with transfers;
no Nisnevich sheafification invariance or sheaf condition is assumed.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules.Invertible.PolynomialBoundaryPencil

universe v u

namespace Motivic.PresheafWithTransfers

attribute [local instance] _root_.AlgebraicGeometry.PrincipalFamilyUnitOpen.nonemptyTop
  _root_.AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialProductIntegral
  _root_.AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialProductNoetherian
  Scheme.functionField_nonempty_preimage Scheme.nonempty_image_open

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
  (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
  {C V W B : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
  [IsNoetherian V] [V.IsQuasiAffine] [IsIntegral W] [IsNoetherian W]
  (q : C ⟶ X.left) [IsProper q]
  (j : V ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (v : W ⟶ C) [IsOpenImmersion v] (b : B ⟶ W) [Nonempty B]
  (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ v))
  (f : Γ(W, ⊤)) (hf : b.appTop f = 1) (hu : IsUnit f)
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom)

include hP hf in
/-- The original signed principal correspondence acts by zero on every HI PST.
The function is a unit on the full prescribed boundary neighborhood and equals
one on the actual boundary subscheme, with no reduced-boundary replacement. -/
theorem transfer_principalOrder_eq_zero :
    P.transfer (PrincipalOrderCorrespondence.correspondence q j (v ''ᵁ ⊤)
      (PrincipalFamilyCorrespondence.original_boundary_cover j v b hcover)
      ((v.appIso ⊤).inv f) (hu.map (v.appIso ⊤).inv.hom) g hbase) = 0 := by
  obtain ⟨hzero, hone⟩ := PrincipalFamilyCorrespondence.graph_endpoints
    X Y q j v b hcover f hf g hbase hu
  have h := transfer_homotopy_endpoints P hP X (Cor.mk Y)
    (PrincipalFamilyCorrespondence.correspondence X Y q j v b hcover f hf g hbase) 0 1
  rw [←
      _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLine.Endpoints.endpointMorphism_eq_a1Section,
    ← _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLine.Endpoints.endpointMorphism_eq_a1Section]
        at h
  erw [hzero, hone, transfer_zero] at h
  exact h.symm

end Motivic.PresheafWithTransfers
