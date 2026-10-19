/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.LocalVanishing.Original.AffineZeroCover
public import Motivic.Cohomology.A1.Moving.ZeroDimensional
/-! # Original affine detection with generators and dimension chosen internally -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Motivic
universe u w
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
variable (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.Smooth k B]
local instance : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)

/-- The constructed neighborhoods cover every original point. The conclusion is
Zariski-local zero for a presheaf, not global zero inferred without separatedness. -/
theorem iSup_original_zero_opens_eq_top
    (J : Ideal B) (hJ : J ≠ ⊥)
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left]
    (a : A ⟶ originalAffineObject k B) [IsOpenImmersion a.left]
    (ha : Disjoint (Set.range a.left)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ y : Spec (.of B), y ∈ Set.range a.left ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk (originalAffineObject k B)))
    (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) :
    (⨆ O : {O : (Spec (.of B)).Opens // originalAffineZeroOpen k B P v O}, O.val) = ⊤ := by
  classical
  by_cases hd : Algebra.trdeg k B = 0
  · have hv0 := section_zero_of_trdeg_zero k B hd J hJ a hcover P v hv
    have hz : originalAffineZeroOpen k B P v ⊤ := by
      refine ⟨isAffineOpen_top _, ?_⟩
      rw [hv0, map_zero]
    exact top_unique (le_iSup_of_le ⟨⊤, hz⟩ le_rfl)
  · obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp
      (trdeg_lt_aleph0_of_finiteType (R := k) (S := B))
    cases n with
    | zero => exact (hd (by simpa using hn)).elim
    | succ d =>
      obtain ⟨G, hG⟩ := Algebra.FiniteType.out (R := k) (A := B)
      have hg : Algebra.adjoin k (Set.range (fun x : G => (x : B))) = ⊤ := by
        convert hG using 1
        congr 1
        ext b
        simp
      exact iSup_original_affine_zero_opens_eq_top k B J hJ (fun x : G => (x : B))
        hg d hn a ha hcover P hP v hv

end Motivic.PresheafWithTransfers
