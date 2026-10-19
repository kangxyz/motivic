/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Cech.GermComparison
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.CommonImageCoverage

/-!
# Controlled Čech comparison with actual common support constructed

Finite coproducts of the original supports and their scheme-theoretic image
retain pointwise coverage. Residue-isomorphic designated centers therefore
supply every required lift on the common finite fiber. No common-support
compatibility law or closedness of the designated points is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] (P : PresheafWithTransfers.{max (u + 1) v} k)
  {X Y V : SmoothSite (Spec (.of k))}

/-- Actual finite common support and its point coverage are constructed, not assumed. -/
theorem transfer_germ_eq_zero_of_matching_cech_germs_auto_support
    (α : FiniteCorrespondence X.hom V.hom) (q : V ⟶ Y) [Etale q.left]
    (hzero : (α : Cor.mk X ⟶ Cor.mk V) ≫ (Cor.graphFunctor k).map q = 0)
    (x : X.left) (T : Set V.left)
    (hfirst : ∀ A ∈ α.support, ∀ a : A.scheme, A.projection a = x →
      A.targetProjection a ∈ T)
    (hres : ∀ v ∈ T, IsIso (q.left.residueFieldMap v))
    (s : P.sections (Cor.mk V))
    (hcompat : ∀ w : (SmoothSite.etalePullback q q).left,
      (SmoothSite.etalePullbackFst q q).left w ∈ T →
      (SmoothSite.etalePullbackSnd q q).left w ∈ T →
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) (SmoothSite.etalePullback q q) w
          (((toPresheaf k).obj P).map (SmoothSite.etalePullbackFst q q).op s) =
        SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) (SmoothSite.etalePullback q q) w
          (((toPresheaf k).obj P).map (SmoothSite.etalePullbackSnd q q).op s)) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α s) = 0 := by
  classical
  by_cases hα : α = 0
  · subst α
    simp
  have hnon : α.support.Nonempty := Finsupp.support_nonempty_iff.mpr hα
  obtain ⟨C, j, hj, hp, hr, hcover⟩ :=
    AlgebraicGeometry.exists_finite_common_closed_image_with_coverage
      (fun A : FiniteCorrespondenceGenerator X.hom V.hom => A.scheme)
      (fun A => A.graphPostcompositionMap q.left (MorphismProperty.Over.w q))
      (pullback.fst X.hom Y.hom) α.support hnon (by
        intro A _
        rw [FiniteCorrespondenceGenerator.graphPostcompositionMap_fst]
        infer_instance)
  let := hj
  let := hp
  choose r hr using hr
  apply transfer_germ_eq_zero_of_matching_cech_germs k P α q hzero C j r hr x T hfirst
    ?_ s hcompat
  intro z hz
  obtain ⟨A, hA, a, ha⟩ := hcover z
  have hax : A.projection a = x := by
    have h := congrArg (pullback.fst X.hom Y.hom) ha
    have hf := congrArg (fun g : A.scheme ⟶ X.left => g a)
      (A.graphPostcompositionMap_fst q.left (MorphismProperty.Over.w q))
    exact hf.symm.trans (h.symm.trans hz)
  have hat : A.targetProjection a ∈ T := hfirst A hA a hax
  refine ⟨A.targetProjection a, ?_, hres _ hat, hat⟩
  have h := congrArg (pullback.snd X.hom Y.hom) ha
  have hf := congrArg (fun g : A.scheme ⟶ Y.left => g a)
    (A.graphPostcompositionMap_snd q.left (MorphismProperty.Over.w q))
  exact hf.symm.trans h.symm

/-- Equal graph images compare using an actual constructed common finite support. -/
theorem transfer_germ_eq_of_matching_cech_germs_auto_support
    (α α' : FiniteCorrespondence X.hom V.hom) (q : V ⟶ Y) [Etale q.left]
    (heq : (α : Cor.mk X ⟶ Cor.mk V) ≫ (Cor.graphFunctor k).map q =
      α' ≫ (Cor.graphFunctor k).map q)
    (x : X.left) (T : Set V.left)
    (hfirst : ∀ A ∈ α.support, ∀ a : A.scheme, A.projection a = x →
      A.targetProjection a ∈ T)
    (hfirst' : ∀ A ∈ α'.support, ∀ a : A.scheme, A.projection a = x →
      A.targetProjection a ∈ T)
    (hres : ∀ v ∈ T, IsIso (q.left.residueFieldMap v))
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
  have hz := transfer_germ_eq_zero_of_matching_cech_germs_auto_support k P (α - α') q hzero
    x T hdiff hres s hcompat
  rw [transfer_sub] at hz
  change SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x
    (P.transfer α s - P.transfer α' s) = 0 at hz
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

end Motivic.PresheafWithTransfers
