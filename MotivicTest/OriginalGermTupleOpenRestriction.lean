/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermTupleOpenRestriction
public import Lean.Util.CollectAxioms

/-! Direct surjectivity on the original germ tuple groups, not a replacement stalk. -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Motivic Motivic.PresheafWithTransfers
universe u
namespace MotivicTest.OriginalGermTupleOpenRestriction
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
    ((toPresheaf k).obj P))

/-- Every actual germ tuple on an open subscheme extends to the ambient scheme. -/
theorem actual_open_extension {U X : SmoothSite (Spec (.of k))} (j : U ⟶ X)
    [IsOpenImmersion j.left]
    (s : ((toPresheaf k).obj (originalGermTuplePresheaf k P hP)).obj (.op U)) :
    ∃ t, ((toPresheaf k).obj (originalGermTuplePresheaf k P hP)).map j.op t = s :=
  originalGermTuple_openRestriction_surjective k P hP j s

open Lean in
run_cmd do
  for name in #[``actual_open_extension, ``originalGermTuple_openRestriction_surjective] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original germ-tuple open extension: standard foundations only."

end MotivicTest.OriginalGermTupleOpenRestriction
