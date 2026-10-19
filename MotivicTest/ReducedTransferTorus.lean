/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.ReducedTorus
public import Lean.Util.CollectAxioms

/-!
# Consumers of the actual reduced transfer torus

These tests use genuine signed finite correspondences, the Laurent spectrum,
all identity-coordinate inclusions, and the quotient universal property.
They check the actual base object in weight zero and the actual Laurent
identity-section cokernel in weight one. No motivic-cohomology calculation
or hypercohomology comparison is asserted.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Motivic
open  _root_.Motivic.PresheafWithTransfers

universe u

namespace MotivicTest.ReducedTransferTorus

variable {k : Type u} [Field k]

example (q : ℕ) : (reducedTorus k q).obj.Additive := inferInstance

/-- The universe lift retains literal signed finite-cycle precomposition. -/
theorem liftedTransferDown {X Y Z : Cor k} (α : Y ⟶ Z) (β : Z ⟶ X) :
    (transfer ((representableLarge k).obj X) α (ULift.up β)).down = α ≫ β := rfl

/-- Arbitrary negative multiplicities and differences act additively on the quotient. -/
theorem signedReducedTransfer (q : ℕ) {X Y : Cor k} (α β : X ⟶ Y) :
    transfer (reducedTorus k q) ((-3 : ℤ) • (α - β)) =
      (-3 : ℤ) • (transfer (reducedTorus k q) α - transfer (reducedTorus k q) β) := by
  rw [transfer_zsmul, transfer_sub]

/-- On an actual cycle representative, quotient transfer is actual cycle composition. -/
theorem quotientCycleTransfer (q : ℕ) {X Y : Cor k} (α : X ⟶ Y)
    (β : Y ⟶ Cor.mk (SmoothSite.torusPower (.of k) q)) :
    transfer (reducedTorus k q) α ((toReducedTorus k q).hom.app (op Y) (ULift.up β)) =
      (toReducedTorus k q).hom.app (op X) (ULift.up (α ≫ β)) :=
  reducedTorus_transfer_apply k q α β

/-- Every genuine identity-axis graph cycle vanishes in the quotient. -/
theorem identityAxisCycleKilled (q : ℕ) (i : Fin (q + 1)) (X : Cor k)
    (α : X ⟶ Cor.mk (SmoothSite.torusPower (.of k) q)) :
    (toReducedTorus k (q + 1)).hom.app (op X)
      (ULift.up (α ≫ (Cor.graphFunctor k).map
        (SmoothSite.torusInsertOne (.of k) q i))) = 0 := by
  exact congrArg (fun η => η.hom.app (op X) (ULift.up α))
    (torusIdentityAxis_toReducedTorus k (q + 1) i)

/-- In particular neither of the two different identity axes is omitted in weight two. -/
theorem bothWeightTwoAxes :
    torusIdentityAxis k 2 0 ≫ toReducedTorus k 2 = 0 ∧
      torusIdentityAxis k 2 1 ≫ toReducedTorus k 2 = 0 :=
  ⟨torusIdentityAxis_toReducedTorus k 2 0, torusIdentityAxis_toReducedTorus k 2 1⟩

/-- This consumer uses exactly the sum of all genuine axis images. -/
def actualPointwiseQuotient (q : ℕ) (X : Cor k) :
    sections (reducedTorus k q) X ≅
      AddCommGrpCat.of (sections (torusRepresentable k q) X ⧸
        ⨆ i : Fin q, ((torusIdentityAxis k q i).hom.app (op X)).hom.range) :=
  reducedTorusSectionsIsoQuotient k q X

/-- The universal property produces a unique transfer-natural extension. -/
theorem uniqueTransferExtension (q : ℕ) (P : PresheafWithTransfers.{u + 1} k)
    (η : torusRepresentable k q ⟶ P)
    (hη : ∀ i : Fin q, torusIdentityAxis k q i ≫ η = 0) :
    ∃! θ : reducedTorus k q ⟶ P, toReducedTorus k q ≫ θ = η := by
  refine ⟨reducedTorusDesc k q η hη, toReducedTorus_desc k q η hη, ?_⟩
  intro θ hθ
  apply reducedTorus_hom_ext
  rw [hθ, toReducedTorus_desc]

/-- Weight zero is the actual base representable, with no relations. -/
def actualWeightZero : reducedTorus k 0 ≅
    (representableLarge k).obj (Cor.mk (SmoothSite.base (Spec (.of k)))) :=
  reducedTorusZeroIso k

example (X : Cor k) : torusIdentityRelations k 0 X = ⊥ := by
  simp [torusIdentityRelations]

/-- Weight one is the actual Laurent identity-point cokernel. -/
def actualWeightOne : reducedTorus k 1 ≅ pointedTorusCokernel k :=
  reducedTorusOneIso k

/-- This cokernel is taken on the genuine graph of the Laurent identity section. -/
example : (pointedTorusCokernel k).obj =
    cokernel (((representableLarge k).map
      ((Cor.graphFunctor k).map (SmoothSite.torusOne (.of k)))).hom) := rfl

open Lean in
run_cmd do
  for name in #[``CategoryTheory.Functor.cokernel_additive,
      ``Motivic.PresheafWithTransfers.representableLarge,
      ``Motivic.PresheafWithTransfers.torusIdentityAxis,
      ``Motivic.PresheafWithTransfers.reducedTorus,
      ``Motivic.PresheafWithTransfers.torusIdentityAxis_toReducedTorus,
      ``Motivic.PresheafWithTransfers.reducedTorus_transfer_apply,
      ``Motivic.PresheafWithTransfers.range_torusRelation,
      ``Motivic.PresheafWithTransfers.reducedTorusSectionsIsoQuotient,
      ``Motivic.PresheafWithTransfers.reducedTorusHomEquiv,
      ``Motivic.PresheafWithTransfers.reducedTorusZeroIso,
      ``Motivic.PresheafWithTransfers.reducedTorusOneIso] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual reduced transfer tori use only standard Lean logical foundations."

end MotivicTest.ReducedTransferTorus
