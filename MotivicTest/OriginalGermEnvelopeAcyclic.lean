/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Envelope.Acyclic
public import Motivic.Transfers.Sheaf.Germs.Envelope.ProductUnit
public import Lean.Util.CollectAxioms

/-! Direct original-envelope sheaf/product/unit and ordinary-cohomology consumers. -/
@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe w u
namespace MotivicTest.OriginalEnvelopeAcyclic
open Motivic
variable (k : Type u) [Field k] (P : SheafWithTransfers.{u + 1} k)
  (X : SmoothSite (Spec (.of k)))

/-- The existing envelope, actual small restriction, and actual residue direct images. -/
def actualEnvelopeProduct :
    (_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj
      ((SheafWithTransfers.toSheaf k).obj (SheafWithTransfers.originalGermEnvelope k P)) ≅
    ∏ᶜ fun x : X.left ↦ (_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.directImage
        (X.left.fromSpecResidueField x)).obj
      ((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.inverseImage
          (X.left.fromSpecResidueField x)).obj
        ((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj
            ((SheafWithTransfers.toSheaf k).obj
            P))) :=
  SheafWithTransfers.originalEnvelopeProductIso k P X

variable [HasExt.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Ordinary cohomology is the original free-source Ext, with no vanishing input. -/
theorem actual_transfer_injective_ordinary_acyclic [Injective P] (n : ℕ)
    (e : _root_.CategoryTheory.Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj P) (n + 1) X) : e = 0 :=
  SheafWithTransfers.injective_underlying_H_succ_eq_zero k P X n e

open Lean in
run_cmd do
  for name in #[``actualEnvelopeProduct, ``actual_transfer_injective_ordinary_acyclic,
      ``SheafWithTransfers.originalGermEnvelope_H_succ_eq_zero,
      ``SheafWithTransfers.toOriginalGermEnvelope_product_unit,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.originalFiberGermIso_naturality,
      ``_root_.CategoryTheory.Sheaf.Products.sectionsEquiv] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original envelope, unit, ordinary acyclicity: standard foundations only."

end MotivicTest.OriginalEnvelopeAcyclic
