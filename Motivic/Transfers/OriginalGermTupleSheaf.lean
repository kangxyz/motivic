/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermTupleCoverComparison

/-! # Nisnevich gluing for the actual original-germ tuple transfer presheaf -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite AlgebraicGeometry
universe u v
namespace Motivic.PresheafWithTransfers
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
  {X : SmoothSite (Spec (.of k))} {ι : Type v} {V : ι → SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)
set_option quotPrecheck false in
local notation "G" => ((toPresheaf k).obj (originalGermTuplePresheaf k P hP))

/-- An actual Nisnevich family detects equality of tuples through its
residue-isomorphic lifts, using the proved original-fiber isomorphisms. -/
theorem originalGermTuple_cover_injective (q : ∀ i, V i ⟶ X)
    (hq : Presieve.ofArrows V q ∈ SmoothSite.nisnevichPrecoverage (Spec (.of k)) X)
    (t t' : originalGermTuples k P (Cor.mk X))
    (h : ∀ i, (G).map (q i).op t = (G).map (q i).op t') : t = t' := by
  have hcover := (SmoothSite.ofArrows_mem_nisnevichPrecoverage_iff q).mp hq
  funext x
  obtain ⟨i, y, hy, hi⟩ := hcover.2 x
  let := hcover.1 i
  let := hi
  rw [← hy]
  apply (ConcreteCategory.bijective_of_isIso (SmoothSite.originalGermPullback.{u, 0} F (q i) y)).1
  have e := congrFun (h i) y
  simpa only [originalGermTuplePresheaf_map_apply] using e

/-- A matching cover family prescribes one actual original base germ at each
point. Its restriction agrees at every point of every covering member. -/
theorem exists_originalGermTuple_local_value (q : ∀ i, V i ⟶ X)
    (hq : Presieve.ofArrows V q ∈ SmoothSite.nisnevichPrecoverage (Spec (.of k)) X)
    (s : ∀ i, originalGermTuples k P (Cor.mk (V i)))
    (hs : ∀ i j (W : SmoothSite (Spec (.of k))) (f : W ⟶ V i) (g : W ⟶ V j),
      f ≫ q i = g ≫ q j → (G).map f.op (s i) = (G).map g.op (s j))
    (x : X.left) :
    ∃ b : (SmoothSite.nisnevichPointFiberCocone X x F).pt,
      ∀ t : originalGermTuples k P (Cor.mk X), t x = b →
        ∀ j (v : (V j).left), (q j).left v = x → ((G).map (q j).op t) v = s j v := by
  have hcover := (SmoothSite.ofArrows_mem_nisnevichPrecoverage_iff q).mp hq
  obtain ⟨i, y, hy, hi⟩ := hcover.2 x
  subst x
  let := hcover.1 i
  let := hi
  let e := SmoothSite.originalGermEtaleIso.{u, 0} F (q i) y
  refine ⟨e.inv (s i y), ?_⟩
  intro t ht j v hv
  have hchosen : ((G).map (q i).op t) y = s i y := by
    change originalGermTupleTransfer k P hP ((Cor.graphFunctor k).map (q i)) t y = _
    rw [originalGermTupleTransfer_graph, ht]
    exact ConcreteCategory.congr_hom e.inv_hom_id (s i y)
  exact originalGermTuple_coordinate_eq_of_matching k P hP V q hcover.1 s hs
    t i y hchosen j v hv

/-- Arbitrary genuine Nisnevich matching families glue uniquely in the original
germ-tuple group. The local values are derived, not assumed compatibility data. -/
theorem existsUnique_originalGermTuple_amalgamation (q : ∀ i, V i ⟶ X)
    (hq : Presieve.ofArrows V q ∈ SmoothSite.nisnevichPrecoverage (Spec (.of k)) X)
    (s : ∀ i, originalGermTuples k P (Cor.mk (V i)))
    (hs : ∀ i j (W : SmoothSite (Spec (.of k))) (f : W ⟶ V i) (g : W ⟶ V j),
      f ≫ q i = g ≫ q j → (G).map f.op (s i) = (G).map g.op (s j)) :
    ∃! t : originalGermTuples k P (Cor.mk X), ∀ i, (G).map (q i).op t = s i := by
  classical
  choose b hb using exists_originalGermTuple_local_value k P hP q hq s hs
  have ht : ∀ i, (G).map (q i).op b = s i := by
    intro i
    funext y
    exact hb ((q i).left y) b rfl i y rfl
  refine ⟨b, ht, ?_⟩
  intro t h
  exact originalGermTuple_cover_injective k P hP q hq t b (fun i => (h i).trans (ht i).symm)

/-- The actual original-germ tuple transfer presheaf is an ordinary Nisnevich sheaf. -/
theorem originalGermTuplePresheaf_isSheaf :
    Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) G := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget AddCommGrpCat.{u + 1})
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  apply (Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange _).mpr
  intro X R hR
  obtain ⟨ι, V, q, rfl⟩ := R.exists_eq_ofArrows
  rw [Presieve.isSheafFor_arrows_iff]
  intro s hs
  exact existsUnique_originalGermTuple_amalgamation k P hP q hR s hs

end Motivic.PresheafWithTransfers
