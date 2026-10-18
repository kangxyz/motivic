/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IdealFrameMovedDominance
public import Motivic.AlgebraicGeometry.Correspondences.FinitePointCycle

/-!
# The original ideal-frame moved sum as an actual finite correspondence

Whole support finiteness and component dominance are constructed geometrically.
The generic finite-image assembler retains the literal fundamental coefficient
plus native rational order and every original residue degree. This is not the
principal A1 relation, which needs an additional geometric pencil producer.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom
open scoped BigOperators

universe u

namespace Motivic.IdealFrameMovedCorrespondence

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))} [IsAffine X.left]
  {C D V : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
  (i : D ⟶ C) [IsClosedImmersion i] (hI : IsLocallyRankOne C (idealModule i))
  (W : C.affineOpens) [Nonempty W.val]
  (e : (idealModule i).over W.val ≅ SheafOfModules.unit (C.ringCatSheaf.over W.val))
  (b : Γ(C, W.val)) (hb : IsUnit b)
  [V.IsQuasiAffine] (q : C ⟶ X.left) [IsProper q]
  (j : V ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (hW : (Set.range j)ᶜ ⊆ (W.val : Set C))
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom)

include hI hW in
omit [V.IsQuasiAffine] [IsOpenImmersion j] in
/-- Every whole original moved support lies inside the retained open. -/
theorem support_range (x : (idealFrameMovedCycle i W e b hb).support) :
    Set.range (IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ⊆ Set.range j := by
  rw [Scheme.IdealSheafData.range_subschemeι, IntegralClosedSubscheme.support_pointClosure]
  intro y hy
  by_contra hn
  exact idealFrameMovedCycle_support_closure i W e b hb hI x.val
    (Finsupp.mem_support_iff.mp x.property) hy (hW hn)

/-- The literal signed moved sum yields an actual finite correspondence. -/
def correspondence : Cor.mk X ⟶ Cor.mk Y :=
  FinitePointCycleCorrespondence.correspondence q j (idealFrameMovedCycle i W e b hb)
    (support_range i hI W e b hb j hW)
    (fun x => idealFrameMovedCycle_support_isFinite i W e b hb hI q j hW x.val
      (Finsupp.mem_support_iff.mp x.property))
    (fun x => idealFrameMovedCycle_support_dominates_component i hI W e b hb q j hW x.val
      (Finsupp.mem_support_iff.mp x.property)) g hbase

/-- The actual target-product map for an original moved support. -/
def productMap (x : (idealFrameMovedCycle i W e b hb).support) :=
  FinitePointCycleCorrespondence.productMap q j (idealFrameMovedCycle i W e b hb)
    (support_range i hI W e b hb j hW) g hbase x

/-- The actual finite-image generator for an original moved support. -/
def generator (x : (idealFrameMovedCycle i W e b hb).support) :=
  FinitePointCycleCorrespondence.generator q j (idealFrameMovedCycle i W e b hb)
    (support_range i hI W e b hb j hW)
    (fun x => idealFrameMovedCycle_support_isFinite i W e b hb hI q j hW x.val
      (Finsupp.mem_support_iff.mp x.property))
    (fun x => idealFrameMovedCycle_support_dominates_component i hI W e b hb q j hW x.val
      (Finsupp.mem_support_iff.mp x.property)) g hbase x

open Classical in
/-- Original moved coefficients and actual residue degrees are summed over all
supports with the same finite image; no multiplicities are discarded. -/
theorem correspondence_coefficient (H : FiniteCorrespondenceGenerator X.hom Y.hom) :
    (show FiniteCorrespondence X.hom Y.hom from
      correspondence i hI W e b hb q j hW g hbase) H =
      ∑ x : (idealFrameMovedCycle i W e b hb).support,
        if generator i hI W e b hb q j hW g hbase x = H then
          idealFrameMovedCycle i W e b hb x.val *
            ((productMap i hI W e b hb q j hW g hbase x).residueDegree
              (genericPoint (IntegralClosedSubscheme.pointClosure x.val).val.subscheme) : ℤ)
        else 0 :=
  FinitePointCycleCorrespondence.correspondence_coefficient q j
    (idealFrameMovedCycle i W e b hb) (support_range i hI W e b hb j hW)
    (fun x => idealFrameMovedCycle_support_isFinite i W e b hb hI q j hW x.val
      (Finsupp.mem_support_iff.mp x.property))
    (fun x => idealFrameMovedCycle_support_dominates_component i hI W e b hb q j hW x.val
      (Finsupp.mem_support_iff.mp x.property)) g hbase H

end Motivic.IdealFrameMovedCorrespondence
