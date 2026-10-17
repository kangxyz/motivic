/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.OriginalAffineDetection
public import Motivic.Aglib.AlgebraicGeometry.AffineOpenComplementIdeal

/-! # Detection from an original nonempty affine good open, without coordinate data -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Motivic
universe u w
namespace Motivic.PresheafWithTransfers
variable (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.Smooth k B]
local instance : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)

/-- The bad ideal, finite generators and dimension split are all constructed internally. -/
theorem iSup_zero_opens_of_nonempty_affine_open
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left] [Nonempty A.left]
    (a : A ⟶ originalAffineObject k B) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk (originalAffineObject k B)))
    (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) :
    (⨆ O : {O : (Spec (.of B)).Opens // originalAffineZeroOpen k B P v O}, O.val) = ⊤ := by
  let J := Scheme.openComplementIdeal B a.left.opensRange
  have hJ : J ≠ ⊥ := Scheme.openComplementIdeal_ne_bot B a.left.opensRange
    (Set.range_nonempty a.left)
  have hr : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
      (Set.range a.left)ᶜ := by
    simpa only [Scheme.Hom.coe_opensRange] using
      Scheme.range_openComplementIdeal B a.left.opensRange
  apply iSup_original_zero_opens_eq_top k B J hJ a ?_ ?_ P hP v hv
  · rw [hr]
    exact disjoint_compl_right
  · intro y
    rw [hr]
    exact Classical.em _

/-- Every original point, not only every closed point, has a genuine affine open
neighborhood where the original section vanishes. -/
theorem exists_zero_neighborhood_of_nonempty_affine_open
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left] [Nonempty A.left]
    (a : A ⟶ originalAffineObject k B) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk (originalAffineObject k B)))
    (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) (x : Spec (.of B)) :
    ∃ O : (Spec (.of B)).Opens, x ∈ O ∧ originalAffineZeroOpen k B P v O := by
  have he := iSup_zero_opens_of_nonempty_affine_open k B a P hP v hv
  have hx : x ∈ ⨆ O : {O : (Spec (.of B)).Opens // originalAffineZeroOpen k B P v O}, O.val := by
    rw [he]
    trivial
  obtain ⟨O, hxO⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨O.val, hxO, O.property⟩

end Motivic.PresheafWithTransfers
