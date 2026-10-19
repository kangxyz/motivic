/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Sections
public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Points.GeneratorLift
public import Motivic.Transfers.Presheaf.GraphRestriction

/-!
# Finite-support locality of transfer on section germs

If a section vanishes in every target germ met by a generator over a closed
source point, its actual transfer vanishes in that source germ. The proof
chooses genuine zero representatives at precisely the finite relevant target
centers, normalizes them, and applies the presheaf to the existing signed
incidence-Tor factorization.

This is a locality theorem for the action on existing sections. It does not
define an action on arbitrary tuples of target germs. That further construction
still needs literal support control for the constructed correspondence lifts
and a representative-independence proof.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]
  (P : PresheafWithTransfers.{max (u + 1) v} k)
  {X Y : SmoothSite (Spec (.of k))}

private theorem transfer_finset_sum_apply {I : Type w} (E : Finset I)
    (α : I → (Cor.mk X ⟶ Cor.mk Y)) (s : P.sections (Cor.mk Y)) :
    P.transfer (∑ i ∈ E, α i) s = ∑ i ∈ E, P.transfer (α i) s := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | @insert i E hi h =>
    simp only [Finset.sum_insert hi, transfer_add, AddCommGrpCat.hom_add_apply, h]

/-- The existing actual family factorization turns zero restrictions on the
target family into a zero restriction of the transferred section at the source point. -/
theorem exists_restriction_transfer_eq_zero_of_family
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
    {I : Type w} (V : I → SmoothSite (Spec (.of k))) (q : ∀ i, V i ⟶ Y)
    [∀ i, Etale (q i).left]
    (hq : ∀ z : A.scheme, A.projection z = x →
      ∃ (i : I) (v : (V i).left), (q i).left v = A.targetProjection z ∧
        IsIso ((q i).left.residueFieldMap v))
    (s : P.sections (Cor.mk Y))
    (hs : ∀ i, P.transfer ((Cor.graphFunctor k).map (q i)) s = 0) :
    ∃ N : SmoothSite.NisnevichNeighborhood X x,
      ((toPresheaf k).obj P).map N.toBase.op (P.transfer A.cycle s) = 0 := by
  obtain ⟨N, n, label, β, hβ⟩ := A.exists_pointed_graph_family_factorization k x V q hq
  refine ⟨N, ?_⟩
  change (P.transfer A.cycle ≫ P.transfer ((Cor.graphFunctor k).map N.toBase)) s = 0
  rw [← transfer_comp, ← hβ]
  erw [transfer_finset_sum_apply k P Finset.univ
    (fun j : Fin n ↦ β j ≫ (Cor.graphFunctor k).map (q (label j))) s]
  apply Finset.sum_eq_zero
  intro j _
  rw [transfer_comp, ConcreteCategory.comp_apply]
  erw [hs (label j), map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing on the finite relevant target germs implies vanishing of the
actual transferred section in the source germ. Only the source point is assumed closed. -/
theorem generator_transfer_germ_eq_zero
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (x : X.left) (hx : IsClosed ({x} : Set X.left)) (s : P.sections (Cor.mk Y))
    (hs : ∀ z : A.scheme, A.projection z = x →
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P)
        Y (A.targetProjection z) s = 0) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P)
      X x (P.transfer A.cycle s) = 0 := by
  classical
  let T : Set Y.left := A.targetProjection '' (A.projection ⁻¹' {x})
  have hT : T.Finite := (A.projection.finite_preimage_singleton x).image _
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace
    (Y := Spec (.of k)) (show Y.left ⟶ Spec (.of k) from Y.hom)
  have hclosed : ∀ y ∈ T, IsClosed ({y} : Set Y.left) := by
    rintro y ⟨z, hz, rfl⟩
    change A.projection z = x at hz
    exact Scheme.Hom.isClosed_target_of_locallyQuasiFinite_source (Y := Y.left)
      A.projection A.targetProjection z (hz.symm ▸ hx)
  have hzero (y : T) : SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P)
      Y y.val s = 0 := by
    obtain ⟨z, hz, hy⟩ := y.property
    exact hy ▸ hs z hz
  have hrep (y : T) := SmoothSite.exists_normalized_zero_representative
    ((toPresheaf k).obj P) s (hzero y) T hT hclosed y.property
  choose N hN using hrep
  let V (y : T) := (SmoothSite.nisnevichNeighborhoodFunctor Y y.val).obj (N y)
  let q (y : T) : V y ⟶ Y := (N y).toBase
  have : ∀ y, Etale (q y).left := by intro y; dsimp [q]; infer_instance
  have hq : ∀ z : A.scheme, A.projection z = x →
      ∃ (i : T) (v : (V i).left), (q i).left v = A.targetProjection z ∧
        IsIso ((q i).left.residueFieldMap v) := by
    intro z hz
    let y : T := ⟨A.targetProjection z, z, hz, rfl⟩
    exact ⟨y, (N y).center, (N y).toBase_center, inferInstance⟩
  apply (SmoothSite.sectionToNisnevichPoint_eq_zero_iff _ _).mpr
  exact exists_restriction_transfer_eq_zero_of_family k P A x V q hq s
    (fun y ↦ (hN y).2.2)

/-- Finite-support germ locality for an arbitrary signed correspondence.
All integer coefficients and cancellations are those of the original correspondence group. -/
theorem transfer_germ_eq_zero
    (α : FiniteCorrespondence X.hom Y.hom)
    (x : X.left) (hx : IsClosed ({x} : Set X.left)) (s : P.sections (Cor.mk Y))
    (hs : ∀ A ∈ α.support, ∀ z : A.scheme, A.projection z = x →
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P)
        Y (A.targetProjection z) s = 0) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P)
      X x (P.transfer α s) = 0 := by
  classical
  let ι : P.sections (Cor.mk X) ⟶
      ((SmoothSite.nisnevichPoint X x).presheafFiber (A := AddCommGrpCat.{max (u + 1) v})).obj
        ((toPresheaf k).obj P) :=
    SmoothSite.sectionToNisnevichPoint.{u, v} ((toPresheaf k).obj P) X x
  let L : (Cor.mk X ⟶ Cor.mk Y) →+
      ((SmoothSite.nisnevichPoint X x).presheafFiber (A := AddCommGrpCat.{max (u + 1) v})).obj
        ((toPresheaf k).obj P) :=
    { toFun := fun γ ↦ ι (P.transfer γ s)
      map_zero' := by simp
      map_add' := fun γ δ ↦ by
        simp only [transfer_add, AddCommGrpCat.hom_add_apply, map_add] }
  have hα : ∑ A ∈ α.support, α A • A.cycle = α := by
    simpa only [Finsupp.sum, FiniteCorrespondenceGenerator.cycle,
      Finsupp.smul_single, smul_eq_mul, mul_one] using α.sum_single
  change L α = 0
  rw [← hα, map_sum]
  apply Finset.sum_eq_zero
  intro A hA
  rw [map_zsmul]
  have hA0 : L A.cycle = 0 := generator_transfer_germ_eq_zero k P A x hx s (hs A hA)
  rw [hA0, smul_zero]

/-- Existing sections with the same finitely relevant target germs have the same
source germ after the original signed transfer. -/
theorem transfer_germ_eq_of_eq_on_support
    (α : FiniteCorrespondence X.hom Y.hom)
    (x : X.left) (hx : IsClosed ({x} : Set X.left)) (s t : P.sections (Cor.mk Y))
    (hst : ∀ A ∈ α.support, ∀ z : A.scheme, A.projection z = x →
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) Y (A.targetProjection z) s =
        SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) Y (A.targetProjection z) t) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α s) =
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α t) := by
  have hzero := transfer_germ_eq_zero k P α x hx (s - t) (by
    intro A hA z hz
    rw [map_sub, hst A hA z hz, sub_self])
  exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)

end Motivic.PresheafWithTransfers
