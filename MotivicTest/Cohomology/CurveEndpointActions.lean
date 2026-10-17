/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.CurveEndpointActions

/-!
# Direct consumers of whole Cartier endpoint actions

The tests use the literal parameter-line evaluation and the original whole
Cartier endpoints with an arbitrary target map. Both the original transfer
sections and actual standard-Ext degree-zero action retain their coefficient
universe. The signed difference acts by zero without a reduced-fiber replacement.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open Scheme.Modules.Invertible Scheme.Hom
open scoped Polynomial

universe u

namespace MotivicTest.Cohomology.CurveEndpointActions

variable {k : Type u} [Field k]

/-- The actual second projection sends the constant cylinder section to scalar evaluation. -/
theorem literal_parameter_evaluation (a : k) :
    SmoothSite.a1Section (.of k) (SmoothSite.base (Spec (.of k))) a ≫
      SmoothSite.productSnd (SmoothSite.base (Spec (.of k))) (SmoothSite.affineLine (.of k)) =
        FiniteFlatCurveFamily.evaluationPoint k a :=
  SmoothSite.a1Section_baseCylinderCurveLineIso_hom k a

variable {C U D : Scheme.{u}}
  (p : C ⟶ Spec (.of k[X])) [SmoothOfRelativeDimension 1 p]
  [IsSeparated p] [QuasiCompact p] (j : U ⟶ C) [IsOpenImmersion j]
  {Y : SmoothSite (Spec (.of k))} (i : D ⟶ C) [IsClosedImmersion i]
  (hI : IsLocallyRankOne C (idealModule i)) [Flat (i ≫ p)] [IsProper (i ≫ p)]
  (hAvoid : Set.range i ⊆ Set.range j) (g : U ⟶ Y.left)
  (hbase : j ≫ p ≫ (FiniteFlatCurveFamily.line k).hom = g ≫ Y.hom)

/-- The signed difference of the whole original endpoint spans acts by zero on HI sections. -/
theorem actual_endpoint_difference_transfer (F : SheafWithTransfers.{u + 1} k)
    (hF : PresheafWithTransfers.IsA1Invariant F.obj) (a b : k) :
    F.obj.transfer
      (RelativeCartierDivisor.endpointCorrespondence p i hI j hAvoid g hbase a -
        RelativeCartierDivisor.endpointCorrespondence p i hI j hAvoid g hbase b) = 0 := by
  rw [PresheafWithTransfers.transfer_sub,
    RelativeCartierDivisor.transfer_endpoints_eq p j i hI hAvoid g hbase F.obj hF a b,
    sub_self]

local instance : HasExt.{u + 2}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasExt.standard _

/-- The original full endpoints also agree as actual ordinary H0 transfer maps. -/
theorem actual_degreeZero_endpoint_action (F : SheafWithTransfers.{u + 1} k)
    (hF : PresheafWithTransfers.IsA1Invariant F.obj) (a b : k) :
    F.degreeZeroTransfer.{u + 2}
        (RelativeCartierDivisor.endpointCorrespondence p i hI j hAvoid g hbase a) =
      F.degreeZeroTransfer.{u + 2}
        (RelativeCartierDivisor.endpointCorrespondence p i hI j hAvoid g hbase b) :=
  RelativeCartierDivisor.degreeZeroTransfer_endpoints_eq p j i hI hAvoid g hbase F hF a b

#print axioms actual_endpoint_difference_transfer
#print axioms actual_degreeZero_endpoint_action

end MotivicTest.Cohomology.CurveEndpointActions
