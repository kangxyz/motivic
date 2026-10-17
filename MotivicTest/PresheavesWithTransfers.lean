/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.Yoneda
public import Motivic.Algebra.Homology.SingularComplexPresheaf
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual presheaves with transfers

These tests use arbitrary fields and arbitrary smooth objects, including
possibly disconnected ones. They check the inherited additive category, signed
transfer laws, actual-cycle representables, additive Yoneda, and the ordinary
presheaf interface used by the existing singular-chain construction. No graph
composition or transfer-preserving sheafification hypothesis is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Motivic
open Motivic.PresheafWithTransfers

universe v u v' u'

namespace MotivicTest.PresheavesWithTransfers

variable {k : Type u} [Field k]

example : Category (PresheafWithTransfers.{v} k) := inferInstance
example : Preadditive (PresheafWithTransfers.{v} k) := inferInstance
example : (representable k).Full := inferInstance
example : (representable k).Faithful := inferInstance
example : (representable k).Additive := inferInstance

/-- General transfer laws apply to differences and negative integer multiplicities. -/
theorem signedTransfer (P : PresheafWithTransfers.{v} k) {X Y : Cor k}
    (α β : X ⟶ Y) :
    transfer P ((-3 : ℤ) • (α - β)) =
      (-3 : ℤ) • (transfer P α - transfer P β) := by
  rw [transfer_zsmul, transfer_sub]

/-- Pulling a section through a composite follows the actual cycle composition. -/
theorem compositeAction (P : PresheafWithTransfers.{v} k) {X Y Z : Cor k}
    (α : X ⟶ Y) (β : Y ⟶ Z) (s : sections P Z) :
    transfer P (α ≫ β) s = transfer P α (transfer P β s) := by
  rw [transfer_comp]
  rfl

/-- The representable acts by the actual incidence Tor pairing on actual cycles. -/
theorem actualRepresentableAction {X Y Z : Cor k}
    (α : FiniteCorrespondence Y.toSmoothSite.hom Z.toSmoothSite.hom)
    (β : FiniteCorrespondence Z.toSmoothSite.hom X.toSmoothSite.hom) :
    transfer ((representable k).obj X) α β =
      FiniteCorrespondence.incidenceTorPairing k
        (X := Y.toSmoothSite) (Y := Z.toSmoothSite) (Z := X.toSmoothSite) α β := rfl

/-- Additive Yoneda really evaluates on the full componentwise diagonal cycle. -/
theorem actualYonedaIdentity (P : PresheafWithTransfers.{u} k) (X : Cor k)
    (η : (representable k).obj X ⟶ P) :
    yonedaAddEquiv P X η = η.hom.app (op X)
      (componentIdentityCycle (X := X.toSmoothSite.left) X.toSmoothSite.hom) := rfl

/-- Every section is recovered from its representing natural transformation. -/
theorem sectionRoundTrip (P : PresheafWithTransfers.{u} k) (X : Cor k)
    (s : sections P X) : yonedaAddEquiv P X (sectionHom P X s) = s :=
  (yonedaAddEquiv P X).apply_symm_apply s

/-- Yoneda evaluation respects signed combinations of natural transformations. -/
theorem signedYoneda (P : PresheafWithTransfers.{u} k) (X : Cor k)
    (η θ : (representable k).obj X ⟶ P) :
    yonedaAddEquiv P X ((-2 : ℤ) • (η - θ)) =
      (-2 : ℤ) • (yonedaAddEquiv P X η - yonedaAddEquiv P X θ) := by
  rw [map_zsmul, map_sub]

variable {C : Type u'} [Category.{v'} C]

/-- The restriction interface retains additive natural transformations. -/
example (G : C ⥤ Cor k) : (restrictAlong.{v} G).Additive := inferInstance

/-- Restricted transfers are ordinary presheaves accepted by existing singular chains. -/
noncomputable def restrictedSingularComplex [HasBinaryProducts C]
    (G : C ⥤ Cor k) (Δ : CosimplicialObject C) (P : PresheafWithTransfers.{v} k) :
    ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ :=
  Motivic.SingularComplex.presheafObj Δ ((restrictAlong G).obj P)

open Lean in
run_cmd do
  for name in #[``Motivic.PresheafWithTransfers.representable,
      ``Motivic.PresheafWithTransfers.sectionHom,
      ``Motivic.PresheafWithTransfers.yonedaAddEquiv,
      ``Motivic.PresheafWithTransfers.yonedaAddEquiv_naturality_left] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Representable presheaves and additive Yoneda use only standard Lean logical foundations."

end MotivicTest.PresheavesWithTransfers
