/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Tuples.Transfers
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Germs.EtalePullback
public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.FiniteLifting

/-!
# Comparing matching tuples above a Nisnevich lift

For the actual presheaf of original germ tuples, a matching family is determined
above a base point by its coordinate at any residue-isomorphic lift of that
point. The argument uses the actual scheme pullback and the already proved
invertibility of its original-germ restriction. No sheaf property of the tuple
presheaf, closed-point hypothesis, or replacement fibers are used.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u w
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)
set_option quotPrecheck false in
local notation "G" => ((toPresheaf k).obj (originalGermTuplePresheaf k P hP))

/-- Ordinary restriction in the actual tuple presheaf is the literal original
Nisnevich germ pullback at each point. -/
theorem originalGermTuplePresheaf_map_apply {X Y : SmoothSite (Spec (.of k))}
    (f : X ⟶ Y) (a : originalGermTuples k P (Cor.mk Y)) (x : X.left) :
    ((G).map f.op a) x = SmoothSite.originalGermPullback.{u, 0} F f x (a (f.left x)) :=
  originalGermTupleTransfer_graph k P hP f a x

/-- Agreement at a residue-isomorphic lift propagates to every coordinate above
the same base point in an actual matching family of original germ tuples. -/
theorem originalGermTuple_coordinate_eq_of_matching
    {I : Type w} {X : SmoothSite (Spec (.of k))}
    (V : I → SmoothSite (Spec (.of k))) (q : ∀ i, V i ⟶ X)
    (hq : ∀ i, Etale (q i).left)
    (s : ∀ i, originalGermTuples k P (Cor.mk (V i)))
    (hs : ∀ (i j : I) (W : SmoothSite (Spec (.of k)))
      (a : W ⟶ V i) (b : W ⟶ V j), a ≫ q i = b ≫ q j →
        (G).map a.op (s i) = (G).map b.op (s j))
    (t : originalGermTuples k P (Cor.mk X))
    (i : I) (x : (V i).left) [IsIso ((q i).left.residueFieldMap x)]
    (hx : ((G).map (q i).op t) x = s i x)
    (j : I) (y : (V j).left) (hy : (q j).left y = (q i).left x) :
    ((G).map (q j).op t) y = s j y := by
  have := hq i
  obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (q i).left) (g := (q j).left) x y hy.symm
  let a := SmoothSite.etalePullbackFst (q i) (q j)
  let b := SmoothSite.etalePullbackSnd (q i) (q j)
  have hb : IsIso (b.left.residueFieldMap z) :=
    (q i).left.isIso_residueFieldMap_pullback_snd (q j).left _ z rfl
  have hbe : Etale b.left := inferInstanceAs (Etale (pullback.snd (q i).left (q j).left))
  have := hb
  have := hbe
  apply (AddCommGrpCat.mono_iff_injective
    (SmoothSite.originalGermPullback.{u, 0} F b z)).mp inferInstance
  erw [← originalGermTuplePresheaf_map_apply k P hP b ((G).map (q j).op t) z,
    ← originalGermTuplePresheaf_map_apply k P hP b (s j) z]
  have hab : a ≫ q i = b ≫ q j :=
    (SmoothSite.etalePullbackCone (q i) (q j)).condition
  have hm := congrFun (hs i j (SmoothSite.etalePullback (q i) (q j)) a b hab) z
  rw [← hm]
  have hc : (G).map b.op ((G).map (q j).op t) = (G).map a.op ((G).map (q i).op t) := by
    rw [← ConcreteCategory.comp_apply, ← (G).map_comp, ← op_comp,
      ← hab, op_comp, (G).map_comp, ConcreteCategory.comp_apply]
  rw [congrFun hc z]
  erw [originalGermTuplePresheaf_map_apply k P hP a ((G).map (q i).op t) z,
    originalGermTuplePresheaf_map_apply k P hP a (s i) z]
  exact congrArg (SmoothSite.originalGermPullback.{u, 0} F a z) hx

end Motivic.PresheafWithTransfers
