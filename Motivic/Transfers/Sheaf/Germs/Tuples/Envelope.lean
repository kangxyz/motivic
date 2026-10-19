/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Tuples.Sheaf
public import Motivic.Transfers.OriginalGermTupleEmbedding
public import Motivic.Transfers.Sheaf.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # The actual all-point sheaf envelope with signed transfers

The embedding and its splitting for transfer-injectives are proved here.
Ordinary-cohomological acyclicity remains a separate theorem.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite AlgebraicGeometry
universe u
namespace Motivic.SheafWithTransfers
variable (k : Type u) [Field k]

/-- The ordinary Nisnevich sheaf of original all-point germs, with its proved
signed finite-correspondence action. -/
def originalGermEnvelope (P : SheafWithTransfers.{u + 1} k) : SheafWithTransfers.{u + 1} k :=
  ⟨PresheafWithTransfers.originalGermTuplePresheaf k P.obj P.property,
    PresheafWithTransfers.originalGermTuplePresheaf_isSheaf k P.obj P.property⟩

/-- Original sections embed naturally for every actual signed correspondence. -/
def toOriginalGermEnvelope (P : SheafWithTransfers.{u + 1} k) :
    P ⟶ originalGermEnvelope k P :=
  ObjectProperty.homMk (PresheafWithTransfers.toOriginalGermTuplePresheaf k P.obj P.property)

instance toOriginalGermEnvelope_mono (P : SheafWithTransfers.{u + 1} k) :
    Mono (toOriginalGermEnvelope k P) where
  right_cancellation {Z} f g h := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    ext s
    apply PresheafWithTransfers.toOriginalGermTuplePresheaf_injective k P.obj P.property X.unop
    exact ConcreteCategory.congr_hom
      (congrArg (fun η => η.hom.hom.app X) h) s

/-- A transfer-injective sheaf is an actual retract of its all-point envelope.
No ordinary injectivity or acyclicity is inferred from this alone. -/
theorem exists_originalGermEnvelope_retraction (P : SheafWithTransfers.{u + 1} k)
    [Injective P] : ∃ r : originalGermEnvelope k P ⟶ P,
      toOriginalGermEnvelope k P ≫ r = 𝟙 P :=
  Injective.factors (𝟙 P) (toOriginalGermEnvelope k P)

end Motivic.SheafWithTransfers
