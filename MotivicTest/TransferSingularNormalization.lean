/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.SingularNormalization
public import Lean.Util.CollectAxioms

/-! # Consumers of actual transfer-compatible Moore normalization -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite AlgebraicTopology
open Motivic Motivic.PresheafWithTransfers
open scoped Simplicial

universe v u

namespace MotivicTest.TransferSingularNormalization

variable {k : Type u} [Field k]

/-- A full simplicial identity holds in transfer presheaves, including the degeneracy. -/
theorem degeneracy_face (P : PresheafWithTransfers.{v} k) (n : ℕ) (i : Fin (n + 1)) :
    (singularSimplicial P).σ i ≫ singularFace P n i.castSucc = 𝟙 _ :=
  (singularSimplicial P).δ_comp_σ_self

/-- Every degeneracy commutes with every actual signed correspondence. -/
theorem degeneracy_transfer (P : PresheafWithTransfers.{v} k) (n : ℕ) (i : Fin (n + 1))
    {X Y : Cor k} (α : X ⟶ Y) :
    transfer P (Cor.simplexExterior n α) ≫ ((singularSimplicial P).σ i).hom.app (op X) =
      ((singularSimplicial P).σ i).hom.app (op Y) ≫
        transfer P (Cor.simplexExterior (n + 1) α) :=
  ((singularSimplicial P).σ i).hom.naturality α.op

/-- Normalized chains carry additive, rather than merely objectwise, transfer actions. -/
theorem normalized_signed_transfer (P : PresheafWithTransfers.{v} k) (n : ℕ)
    {X Y : Cor k} (α β : X ⟶ Y) :
    ((normalizedSingularComplex P).X n).obj.map (α - β).op =
      ((normalizedSingularComplex P).X n).obj.map α.op -
        ((normalizedSingularComplex P).X n).obj.map β.op := by
  change ((normalizedSingularComplex P).X n).obj.map (α.op - β.op) = _
  exact ((normalizedSingularComplex P).X n).obj.map_sub

/-- The actual normalized inclusion is natural for transfers in every chain degree. -/
theorem inclusion_transfer (P : PresheafWithTransfers.{v} k) (n : ℕ)
    {X Y : Cor k} (α : X ⟶ Y) :
    ((normalizedSingularComplex P).X n).obj.map α.op ≫
        ((singularNormalizationInclusion P).f n).hom.app (op X) =
      ((singularNormalizationInclusion P).f n).hom.app (op Y) ≫
        transfer P (Cor.simplexExterior n α) :=
  ((singularNormalizationInclusion P).f n).hom.naturality α.op

example (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    ((singularNormalizationInclusion P).f n).hom =
      (inclusionOfMooreComplexMap (singularAmbientSimplicial P)).f n :=
  singularNormalizationInclusion_f_hom P n

/-- Both composites have actual transfer-natural homotopies, without homology assumptions. -/
def normalization (P : PresheafWithTransfers.{v} k) :
    HomotopyEquiv (normalizedSingularComplex P) (singularComplex P) :=
  singularNormalizationHomotopyEquiv P

example (P : PresheafWithTransfers.{v} k) :
    Homotopy ((normalization P).inv ≫ singularNormalizationInclusion P)
      (𝟙 (singularComplex P)) :=
  (normalization P).homotopyInvHomId

example (P : PresheafWithTransfers.{v} k)
    [∀ n, (normalizedSingularComplex P).HasHomology n]
    [∀ n, (singularComplex P).HasHomology n] : QuasiIso (singularNormalizationInclusion P) :=
  inferInstance

/-- The sheaf comparison is an actual homotopy equivalence, with no abelian-category premise. -/
def sheafNormalization (P : PresheafWithTransfers.{u + 1} k) :
    HomotopyEquiv (normalizedSingularSheafComplex P) (singularSheafComplex k P) :=
  singularSheafNormalizationHomotopyEquiv P

example (P : PresheafWithTransfers.{u + 1} k) (n : ℕ) :
    ((sheafNormalization P).hom.f n) =
      (nisnevichSheafify k).map ((singularNormalizationInclusion P).f n) := rfl

/-- Every weight retains the actual zero-extended normalization homotopies. -/
def placedNormalization (P : PresheafWithTransfers.{u + 1} k) (q : ℕ) :
    HomotopyEquiv (normalizedSingularSheafCochainComplex P q)
      (singularSheafCochainComplex k P q) :=
  singularSheafCochainNormalizationHomotopyEquiv P q

/-- Every signed shift retains the genuine normalization equivalence. -/
def shiftedNormalization (P : PresheafWithTransfers.{u + 1} k) (q : ℕ) :
    HomotopyEquiv ((normalizedSingularSheafCochainComplex P 0)⟦-(q : ℤ)⟧)
      ((singularSheafCochainComplex k P 0)⟦-(q : ℤ)⟧) :=
  singularSheafShiftedNormalizationHomotopyEquiv P q

example (P : PresheafWithTransfers.{u + 1} k) (q : ℕ)
    [∀ i, (normalizedSingularSheafCochainComplex P q).HasHomology i]
    [∀ i, (singularSheafCochainComplex k P q).HasHomology i] :
    QuasiIso (placedNormalization P q).hom := inferInstance

open Lean in
run_cmd do
  for name in #[``singularSimplicial, ``singularSimplicial_σ_app,
      ``normalizedSingularAmbient_X_additive, ``normalizedSingularComplex,
      ``singularAlternatingIso, ``singularSimplicialAlternatingIso,
      ``singularNormalizationInclusion_f_hom,
      ``normalization, ``degeneracy_face, ``degeneracy_transfer,
      ``normalized_signed_transfer, ``inclusion_transfer, ``sheafNormalization,
      ``placedNormalization, ``shiftedNormalization, ``normalizedSingularCochainShiftIso] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual transfer normalization uses only standard Lean foundations."

end MotivicTest.TransferSingularNormalization
