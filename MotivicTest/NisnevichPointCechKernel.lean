/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Points.ClosedCenterKernel
public import Lean.Util.CollectAxioms

/-!
# Consumers of point-local signed Čech kernel relations

The actual common closed support, signed relation, and original Cor boundary
maps are retained. The closed-center test requests residue lifts only at
centers in the chosen finite fiber, without a global covering premise.
-/

noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic _root_.AlgebraicGeometry.Scheme.SmoothSite

universe u

example {Z X Y : Scheme.{u}} (p : Z ⟶ X) [IsFinite p]
    (t : Z ⟶ Y) [LocallyOfFiniteType t] [JacobsonSpace Y]
    (z : Z) (hx : IsClosed ({p z} : Set X)) : IsClosed ({t z} : Set Y) :=
  p.isClosed_target_of_locallyQuasiFinite_source t z hx

section Relation

variable (k : Type u) [Field k] {X Y V : SmoothSite (Spec (.of k))}
  (α : FiniteCorrespondence X.hom V.hom) (q : V ⟶ Y) [Etale q.left]
  (hzero : (α : Cor.mk X ⟶ Cor.mk V) ≫ (Cor.graphFunctor k).map q = 0)
  (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom) [IsClosedImmersion j]
  [IsFinite (j ≫ pullback.fst X.hom Y.hom)]
  (r : ∀ A ∈ α.support, A.scheme ⟶ C)
  (hr : ∀ A hA, r A hA ≫ j =
    A.graphPostcompositionMap q.left (MorphismProperty.Over.w q))
  (x : X.left)

example (hq : ∀ z : C, (j ≫ pullback.fst X.hom Y.hom) z = x →
    ∃ v : V.left, q.left v = (j ≫ pullback.snd X.hom Y.hom) z ∧
      IsIso (q.left.residueFieldMap v)) :
    ∃ (N : NisnevichNeighborhood X x)
      (β : Cor.mk ((nisnevichNeighborhoodFunctor X x).obj N) ⟶ Cor.mk (etalePullback q q)),
      (Cor.graphFunctor k).map N.toBase ≫ α =
        β ≫ (Cor.graphFunctor k).map (etalePullbackFst q q) -
          β ≫ (Cor.graphFunctor k).map (etalePullbackSnd q q) :=
  FiniteCorrespondence.exists_pointed_cech_boundary_of_common_support_fiber
    k α q hzero C j r hr x hq

example (hx : IsClosed ({x} : Set X.left))
    (hq : ∀ y : Y.left, IsClosed ({y} : Set Y.left) →
      (∃ z : C, (j ≫ pullback.fst X.hom Y.hom) z = x ∧
        (j ≫ pullback.snd X.hom Y.hom) z = y) →
      ∃ v : V.left, q.left v = y ∧ IsIso (q.left.residueFieldMap v)) :
    ∃ (N : NisnevichNeighborhood X x)
      (β : Cor.mk ((nisnevichNeighborhoodFunctor X x).obj N) ⟶ Cor.mk (etalePullback q q)),
      (Cor.graphFunctor k).map N.toBase ≫ α =
        β ≫ (Cor.graphFunctor k).map (etalePullbackFst q q) -
          β ≫ (Cor.graphFunctor k).map (etalePullbackSnd q q) :=
  FiniteCorrespondence.exists_pointed_cech_boundary_of_common_support_closed_centers
    k α q hzero C j r hr x hx hq

end Relation

open Motivic.FiniteCorrespondence in
open Lean in
run_cmd do
  for name in #[``AlgebraicGeometry.Scheme.Hom.isClosed_singleton_of_isClosed_singleton_image,
      ``AlgebraicGeometry.Scheme.Hom.isClosed_target_of_locallyQuasiFinite_source,
      ``exists_pointed_cech_boundary_of_common_support_fiber,
      ``exists_pointed_cech_boundary_of_common_support_closed_centers] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Closed-center point-local Cor kernels use only standard Lean foundations."
