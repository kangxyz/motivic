/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.GlobalBoundaryPencil
public import Motivic.AlgebraicGeometry.Correspondences.PencilA1Endpoints
public import Motivic.Cohomology.A1.Basic

/-!
# Homotopy-invariant action of an actual boundary-prescribed pencil

Equal invertible restrictions of two sections on the boundary give an actual
finite-flat signed pencil whose endpoint difference acts by zero. The family,
its finiteness and flatness, and its whole scheme-theoretic endpoint cycles are
constructed by `GlobalBoundaryPencil`; no correspondence or endpoint equation
is supplied here.

This is the boundary-one vanishing mechanism used in MVW Lemma 21.8. Identifying
these endpoint cycles with the correction chosen for a covering of standard
triples is a separate geometric obligation. In particular, this module does
not assert the six identities of MVW Theorem 21.6.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Motivic.RelativeEndpointDiagram Motivic.GlobalBoundaryPencil

universe u v

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k]
  (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
  (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
  {C B U : Scheme.{u}} (i : B ⟶ C) (q : C ⟶ relativeLine X.hom) [IsProper q]
  (j : U ⟶ C) [IsOpenImmersion j] [U.IsQuasiAffine]
  [SmoothOfRelativeDimension 1 (j ≫ q)] (L : LineBundle C)
  (a b : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) (t : Γ(C, ⊤))
  [IsIso ((Scheme.Modules.pullback i).map a)]
  (h : Hom.pullbackToUnit a i = Hom.pullbackToUnit b i)
  (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range i)
  (g : U ⟶ Y.left)
  (hbase : (j ≫ q) ≫ relativeLineHom X.hom = g ≫ Y.hom)

/-- The original two whole zero fibers of the geometric pencil have identical
transfer actions on every HI presheaf, in its unchanged coefficient universe. -/
theorem transfer_boundaryPencil_endpoints (c d : k) :
    transfer P (endpointCorrespondence X Y i q j L a b t h hcover g hbase c) =
      transfer P (endpointCorrespondence X Y i q j L a b t h hcover g hbase d) := by
  have he := transfer_homotopy_endpoints P hP X (Cor.mk Y)
    (correspondence X Y i q j L a b t h hcover g hbase) c d
  rw [← PencilA1Endpoints.endpointMorphism_eq_a1Section,
    ← PencilA1Endpoints.endpointMorphism_eq_a1Section,
    graph_endpoint_correspondence, graph_endpoint_correspondence] at he
  exact he

/-- A boundary-normalized numerator-minus-denominator cycle acts by zero.
This retains the actual signed finite correspondence, including nilpotent
multiplicities of both endpoint fibers. -/
theorem transfer_boundaryPencil_difference_eq_zero (c d : k) :
    transfer P
      (endpointCorrespondence X Y i q j L a b t h hcover g hbase c -
        endpointCorrespondence X Y i q j L a b t h hcover g hbase d) = 0 := by
  rw [transfer_sub,
    transfer_boundaryPencil_endpoints P hP X Y i q j L a b t h hcover g hbase c d,
    sub_self]

end Motivic.PresheafWithTransfers
