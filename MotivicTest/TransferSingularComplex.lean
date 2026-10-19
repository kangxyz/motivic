/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.SingularComplex.Presheaf
public import Lean.Util.CollectAxioms

/-! # Consumers of the actual singular complex of transfer presheaves -/

@[expose] public noncomputable section

open _root_.CategoryTheory.SingularComplex (presheafConstruction)
open _root_.CategoryTheory.SingularComplex.Indexing (singularDegree)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers
open scoped Simplicial

universe v u

namespace MotivicTest.TransferSingularComplex

variable {k : Type u} [Field k]

/-- No transfer-action hypothesis is supplied by the consumer. -/
def allDegrees (P : PresheafWithTransfers.{v} k) :
    ChainComplex (PresheafWithTransfers.{v} k) ℕ := singularComplex P

example (P : PresheafWithTransfers.{v} k) (n : ℕ) {X Y : Cor k} (α β : X ⟶ Y) :
    ((allDegrees P).X n).obj.map (α - β).op =
      transfer P (Cor.simplexExterior n α) - transfer P (Cor.simplexExterior n β) := by
  change transfer P (Cor.simplexExterior n (α - β)) = _
  simp

example (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    (allDegrees P).d (n + 2) (n + 1) ≫ (allDegrees P).d (n + 1) n = 0 :=
  (allDegrees P).d_comp_d _ _ _

/-- Coefficient maps commute with all actual exterior transfers, including signed cycles. -/
theorem coefficient_transfer_naturality {P Q : PresheafWithTransfers.{v} k}
    (η : P ⟶ Q) {X Y : Cor k} (α : X ⟶ Y) (n : ℕ) :
    transfer P (Cor.simplexExterior n α) ≫ ((singularComplexMap η).f n).hom.app (op X) =
      ((singularComplexMap η).f n).hom.app (op Y) ≫
        transfer Q (Cor.simplexExterior n α) :=
  ((singularComplexMap η).f n).hom.naturality α.op

example {P Q R : PresheafWithTransfers.{v} k} (η : P ⟶ Q) (θ : Q ⟶ R) :
    singularComplexMap (η ≫ θ) = singularComplexMap η ≫ singularComplexMap θ :=
  (singularComplexFunctor (k := k)).map_comp η θ

/-- On a representable, the degreewise transfer is literal composition of actual cycles. -/
theorem representable_transfer (Z : Cor k) (n : ℕ) {X Y : Cor k} (α : X ⟶ Y)
    (β : Cor.simplexProduct Y n ⟶ Z) :
    ((singularComplex ((representable k).obj Z)).X n).obj.map α.op β =
      Cor.simplexExterior n α ≫ β := rfl

example (P : PresheafWithTransfers.{v} k) :
    (singularCochainComplex P 2).X 1 ≅ (singularComplex P).X 1 :=
  singularCochainXIso P 2 1

example (P : PresheafWithTransfers.{v} k) :
    (singularCochainComplex P 2).X 2 ≅ (singularComplex P).X 0 :=
  singularCochainXIso P 2 0

example (P : PresheafWithTransfers.{v} k) :
    (singularCochainComplex P 2).X (-3) ≅ (singularComplex P).X 5 :=
  singularCochainXIso P 2 5

example (P : PresheafWithTransfers.{v} k) : IsZero ((singularCochainComplex P 2).X 3) :=
  isZero_singularCochainComplex_X P 2 3 (by norm_num)

example (P : PresheafWithTransfers.{v} k) :
    (singularCochainComplex P 2).d 1 2 =
      (singularCochainXIso P 2 1).hom ≫ (singularComplex P).d 1 0 ≫
        (singularCochainXIso P 2 0).inv :=
  singularCochainComplex_d P 2 0

/-- Graph restriction really is the ordinary singular complex, functorially in the coefficient. -/
def ordinaryComparison (P : PresheafWithTransfers.{v} k) := singularComplexUnderlyingIso P

example {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q) :
    ((singularComplexFunctor ⋙ (toPresheaf k).mapHomologicalComplex
      (ComplexShape.down ℕ)).map η) ≫ (singularComplexUnderlyingIso Q).hom =
      (singularComplexUnderlyingIso P).hom ≫
        ((toPresheaf k ⋙ presheafConstruction
          (cosimplicialSmoothSite k)).map η) :=
  singularComplexUnderlyingNatIso.hom.naturality η

/-- The odd sign cannot be dropped in weight one and chain degree one. -/
theorem weightOne_odd_sign (P : PresheafWithTransfers.{v} k) :
    (singularCochainShiftIso P 1).hom.f 0 =
      (-1 : ℤ) • ((singularCochainXIso P 1 1).hom ≫ (singularShiftedCochainXIso P 1 1).inv) := by
  simpa [singularDegree] using
    singularCochainShiftIso_hom_f P 1 1

example (P : PresheafWithTransfers.{v} k) (r : ℕ) :
    (singularCochainShiftIso P 2).hom.f (singularDegree 2 r) =
      (singularCochainXIso P 2 r).hom ≫ (singularShiftedCochainXIso P 2 r).inv :=
  singularCochainShiftIso_two_hom_f P r

open Lean in
run_cmd do
  for name in #[``singularComplex, ``singularComplexFunctor, ``singularComplex_d_app,
      ``singularFace, ``singularComplex_d, ``singularComplex_d_one_zero,
      ``singularComplexMap, ``singularCochainFunctor, ``singularCochainXIso,
      ``singularCochainComplex_d, ``isZero_singularCochainComplex_X,
      ``coefficient_transfer_naturality, ``representable_transfer, ``ordinaryComparison,
      ``singularComplexUnderlyingNatIso, ``singularCochainShiftNatIso,
      ``singularCochainShiftIso_hom_f, ``weightOne_odd_sign] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual transfer singular complexes use only standard Lean foundations."

end MotivicTest.TransferSingularComplex
