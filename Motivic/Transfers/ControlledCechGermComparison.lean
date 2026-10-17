/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.ArbitraryPointGermLocality
public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichPointRefinement
public import Motivic.AlgebraicGeometry.Correspondences.NisnevichPointControlledCechKernel

/-!
# Comparing lift evaluations through actual controlled Čech germs

A representative section whose two restrictions have matching germs on the
actual designated Čech points kills the original point-local kernel relation.
Apply the genuine controlled boundary and arbitrary-point signed locality,
then the original source fiber cocone. Consequently two different lift
correspondences with equal graph images give the same evaluated source germ.

The matching-germ hypothesis is an explicit condition on actual representatives
and actual Čech points. Its verification from arbitrary germ tuples and common
target refinements, and the all-point envelope functor, are separate steps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Motivic.PresheafWithTransfers

variable (k : Type u) [Field k] (P : PresheafWithTransfers.{max (u + 1) v} k)
  {X Y V : SmoothSite (Spec (.of k))}

/-- Matching germs on the actual designated Čech points annihilate the
original supported kernel transfer at an arbitrary source point. -/
theorem transfer_germ_eq_zero_of_matching_cech_germs
    (α : FiniteCorrespondence X.hom V.hom) (q : V ⟶ Y) [Etale q.left]
    (hzero : (α : Cor.mk X ⟶ Cor.mk V) ≫ (Cor.graphFunctor k).map q = 0)
    (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom) [IsClosedImmersion j]
    [IsFinite (j ≫ pullback.fst X.hom Y.hom)]
    (r : ∀ A ∈ α.support, A.scheme ⟶ C)
    (hr : ∀ A hA, r A hA ≫ j =
      A.graphPostcompositionMap q.left (MorphismProperty.Over.w q))
    (x : X.left) (T : Set V.left)
    (hfirst : ∀ A ∈ α.support, ∀ a : A.scheme, A.projection a = x →
      A.targetProjection a ∈ T)
    (hq : ∀ z : C, (j ≫ pullback.fst X.hom Y.hom) z = x →
      ∃ v : V.left, q.left v = (j ≫ pullback.snd X.hom Y.hom) z ∧
        IsIso (q.left.residueFieldMap v) ∧ v ∈ T)
    (s : P.sections (Cor.mk V))
    (hcompat : ∀ w : (SmoothSite.etalePullback q q).left,
      (SmoothSite.etalePullbackFst q q).left w ∈ T →
      (SmoothSite.etalePullbackSnd q q).left w ∈ T →
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) (SmoothSite.etalePullback q q) w
          (((toPresheaf k).obj P).map (SmoothSite.etalePullbackFst q q).op s) =
        SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) (SmoothSite.etalePullback q q) w
          (((toPresheaf k).obj P).map (SmoothSite.etalePullbackSnd q q).op s)) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α s) = 0 := by
  obtain ⟨N, β, hβ, hpoint⟩ :=
    FiniteCorrespondence.exists_pointed_cech_boundary_with_point_property
      k α q hzero C j r hr x (fun v ↦ v ∈ T) hq
  let d := ((toPresheaf k).obj P).map (SmoothSite.etalePullbackFst q q).op s -
    ((toPresheaf k).obj P).map (SmoothSite.etalePullbackSnd q q).op s
  have hd : ∀ B ∈ β.support, ∀ z : B.scheme, B.projection z = N.center →
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) (SmoothSite.etalePullback q q)
        (B.targetProjection z) d = 0 := by
    intro B hB z hz
    obtain ⟨A, hA, a, has, hat, hsecond⟩ := hpoint B hB z hz
    dsimp only [d]
    rw [map_sub, hcompat (B.targetProjection z) (hat ▸ hfirst A hA a has) hsecond, sub_self]
  have hz := transfer_germ_eq_zero_at_point k P β N.center d hd
  have he : ((toPresheaf k).obj P).map N.toBase.op (P.transfer α s) = P.transfer β d := by
    change (P.transfer α ≫ P.transfer ((Cor.graphFunctor k).map N.toBase)) s = _
    rw [← transfer_comp, hβ, transfer_sub]
    change P.transfer (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q)) s -
      P.transfer (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)) s = _
    rw [transfer_comp, transfer_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact (map_sub (P.transfer β).hom _ _).symm
  rw [← SmoothSite.restriction_sectionToNisnevichPoint _ N,
    ConcreteCategory.comp_apply, he]
  exact SmoothSite.nisnevichPointFiberCocone_eq_zero_of_center_germ_eq_zero _ N _ hz

/-- Two different lifts with the same original graph image evaluate equally
on an actual representative satisfying the designated Čech germ condition.
The common support maps are literal maps on the signed difference support. -/
theorem transfer_germ_eq_of_matching_cech_germs
    (α α' : FiniteCorrespondence X.hom V.hom) (q : V ⟶ Y) [Etale q.left]
    (heq : (α : Cor.mk X ⟶ Cor.mk V) ≫ (Cor.graphFunctor k).map q =
      α' ≫ (Cor.graphFunctor k).map q)
    (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom) [IsClosedImmersion j]
    [IsFinite (j ≫ pullback.fst X.hom Y.hom)]
    (r : ∀ A ∈ (α - α').support, A.scheme ⟶ C)
    (hr : ∀ A hA, r A hA ≫ j =
      A.graphPostcompositionMap q.left (MorphismProperty.Over.w q))
    (x : X.left) (T : Set V.left)
    (hfirst : ∀ A ∈ α.support, ∀ a : A.scheme, A.projection a = x →
      A.targetProjection a ∈ T)
    (hfirst' : ∀ A ∈ α'.support, ∀ a : A.scheme, A.projection a = x →
      A.targetProjection a ∈ T)
    (hq : ∀ z : C, (j ≫ pullback.fst X.hom Y.hom) z = x →
      ∃ v : V.left, q.left v = (j ≫ pullback.snd X.hom Y.hom) z ∧
        IsIso (q.left.residueFieldMap v) ∧ v ∈ T)
    (s : P.sections (Cor.mk V))
    (hcompat : ∀ w : (SmoothSite.etalePullback q q).left,
      (SmoothSite.etalePullbackFst q q).left w ∈ T →
      (SmoothSite.etalePullbackSnd q q).left w ∈ T →
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) (SmoothSite.etalePullback q q) w
          (((toPresheaf k).obj P).map (SmoothSite.etalePullbackFst q q).op s) =
        SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) (SmoothSite.etalePullback q q) w
          (((toPresheaf k).obj P).map (SmoothSite.etalePullbackSnd q q).op s)) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α s) =
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α' s) := by
  classical
  have hzero : (α - α' : Cor.mk X ⟶ Cor.mk V) ≫ (Cor.graphFunctor k).map q = 0 := by
    rw [Preadditive.sub_comp, heq, sub_self]
  have hdiff : ∀ A ∈ (α - α').support, ∀ a : A.scheme, A.projection a = x →
      A.targetProjection a ∈ T := by
    intro A hA a ha
    rcases Finset.mem_union.mp (Finsupp.support_sub hA) with hA | hA
    · exact hfirst A hA a ha
    · exact hfirst' A hA a ha
  have hz := transfer_germ_eq_zero_of_matching_cech_germs k P (α - α') q hzero
    C j r hr x T hdiff hq s hcompat
  rw [transfer_sub] at hz
  change SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x
    (P.transfer α s - P.transfer α' s) = 0 at hz
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

end Motivic.PresheafWithTransfers
