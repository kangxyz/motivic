/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.SingularComplex.Sheafification
public import Lean.Util.CollectAxioms

/-! # Actual degreewise transfer sheafification and the exact `q-r` dictionary -/

@[expose] public noncomputable section

open _root_.CategoryTheory.SingularComplex.Indexing (singularDegree)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

universe u

namespace MotivicTest.TransferSheafifiedSingularComplex

variable {k : Type u} [Field k]

/-- The actual chain complex needs no caller-supplied sheafification assumptions. -/
def allDegrees (P : PresheafWithTransfers.{u + 1} k) :
    ChainComplex (SheafWithTransfers.{u + 1} k) ℕ := singularSheafComplex k P

/-- The sheaf unit commutes with every actual signed transfer in each degree. -/
theorem unit_transfer_naturality (P : PresheafWithTransfers.{u + 1} k) (n : ℕ)
    {X Y : Cor k} (α : X ⟶ Y) :
    transfer ((singularComplex P).X n) α ≫
        (((singularSheafUnit k).app P).f n).hom.app (op X) =
      (((singularSheafUnit k).app P).f n).hom.app (op Y) ≫
        transfer ((allDegrees P).X n).obj α :=
  (((singularSheafUnit k).app P).f n).hom.naturality α.op

example (P : PresheafWithTransfers.{u + 1} k) (n : ℕ) :
    (allDegrees P).d (n + 2) (n + 1) ≫ (allDegrees P).d (n + 1) n = 0 :=
  (allDegrees P).d_comp_d _ _ _

example (P : PresheafWithTransfers.{u + 1} k) (n : ℕ) :
    IsNisnevichSheaf k ((allDegrees P).X n).obj := ((allDegrees P).X n).property

example {P Q R : PresheafWithTransfers.{u + 1} k} (η : P ⟶ Q) (θ : Q ⟶ R) :
    (singularSheafFunctor k).map (η ≫ θ) =
      (singularSheafFunctor k).map η ≫ (singularSheafFunctor k).map θ :=
  (singularSheafFunctor k).map_comp η θ

/-- Low weight two degree one is actual sheafification of singular chain degree one. -/
def weightTwoOne (P : PresheafWithTransfers.{u + 1} k) :
    (singularSheafCochainComplex k P 2).X 1 ≅
      (nisnevichSheafify k).obj ((singularComplex P).X 1) :=
  singularSheafCochainXIso k P 2 1

/-- Low weight two degree two is actual sheafification of singular chain degree zero. -/
def weightTwoTwo (P : PresheafWithTransfers.{u + 1} k) :
    (singularSheafCochainComplex k P 2).X 2 ≅
      (nisnevichSheafify k).obj ((singularComplex P).X 0) :=
  singularSheafCochainXIso k P 2 0

example (P : PresheafWithTransfers.{u + 1} k) :
    (singularSheafCochainComplex k P 2).d 1 2 =
      (weightTwoOne P).hom ≫ (nisnevichSheafify k).map ((singularComplex P).d 1 0) ≫
        (weightTwoTwo P).inv :=
  singularSheafCochainComplex_d k P 2 0

example (P : PresheafWithTransfers.{u + 1} k) :
    (singularSheafCochainComplex k P 2).X (-4) ≅
      (nisnevichSheafify k).obj ((singularComplex P).X 6) :=
  singularSheafCochainXIso k P 2 6

example (P : PresheafWithTransfers.{u + 1} k) :
    IsZero ((singularSheafCochainComplex k P 2).X 3) :=
  isZero_singularSheafCochainComplex_X k P 2 3 (by norm_num)

/-- Forgetting transfers gives genuine ordinary sheafification in every chain degree. -/
def ordinaryComparison (P : PresheafWithTransfers.{u + 1} k) :=
  singularSheafUnderlyingIso k P

/-- The complete ordinary singular comparison, not merely a termwise sheaf identity. -/
def ordinarySingularComparison (P : PresheafWithTransfers.{u + 1} k) :=
  singularSheafOrdinaryIso k P

/-- An odd-weight component has the actual negative sign after sheafification. -/
theorem weightOne_odd_sign (P : PresheafWithTransfers.{u + 1} k) :
    (singularSheafCochainShiftIso k P 1).hom.f 0 =
      (-1 : ℤ) • ((singularSheafCochainXIso k P 1 1).hom ≫
        (singularSheafShiftedCochainXIso k P 1 1).inv) := by
  simpa [singularDegree] using
    singularSheafCochainShiftIso_hom_f k P 1 1

example (P : PresheafWithTransfers.{u + 1} k) (r : ℕ) :
    (singularSheafCochainShiftIso k P 2).hom.f (singularDegree 2 r) =
      (singularSheafCochainXIso k P 2 r).hom ≫
        (singularSheafShiftedCochainXIso k P 2 r).inv :=
  singularSheafCochainShiftIso_two_hom_f k P r

example (P : PresheafWithTransfers.{u + 1} k) :
    ((singularSheafCochainComplex k P 0)⟦(-2 : ℤ)⟧).d 1 2 =
      (singularSheafShiftedCochainXIso k P 2 1).hom ≫
        (nisnevichSheafify k).map ((singularComplex P).d 1 0) ≫
          (singularSheafShiftedCochainXIso k P 2 0).inv := by
  have h := singularSheafShiftedCochain_d k P 2 1 0
  change ((singularSheafCochainComplex k P 0)⟦(-2 : ℤ)⟧).d 1 2 =
    (1 : ℤ) • ((singularSheafShiftedCochainXIso k P 2 1).hom ≫
      (nisnevichSheafify k).map ((singularComplex P).d 1 0) ≫
        (singularSheafShiftedCochainXIso k P 2 0).inv) at h
  simpa only [one_zsmul] using h

open Lean in
run_cmd do
  for name in #[``singularSheafFunctor, ``singularSheafUnit, ``singularSheafCochainFunctor,
      ``singularSheafCochainXIso, ``singularSheafCochainComplex_d,
      ``singularSheafCochainUnit, ``isZero_singularSheafCochainComplex_X,
      ``singularSheafUnderlyingIso, ``allDegrees, ``unit_transfer_naturality,
      ``weightTwoOne, ``weightTwoTwo, ``ordinaryComparison, ``ordinarySingularComparison,
      ``singularSheafCochainShiftNatIso, ``singularSheafCochainShiftIso_hom_f,
      ``singularSheafShiftedCochain_d, ``weightOne_odd_sign] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Sheafified actual transfer singular complexes use only standard Lean foundations."

end MotivicTest.TransferSheafifiedSingularComplex
