/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteTorusBaseChange
public import Mathlib.Data.ZMod.Basic
public import Lean.Util.CollectAxioms

/-! # Literal Cartesian torus, scalar, unit and identity-axis consumers -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic.SmoothSite
open AlgebraicGeometry.Scheme.PolynomialLaurent CommRingCat.PolynomialLaurent

universe u

namespace Motivic.MotivicTest.SmoothSiteTorusBaseChange

variable {R S : CommRingCat.{u}}

example (c : R ⟶ S) :
    IsPullback (Spec.map (laurentMap c)) (laurentProjection S)
      (laurentProjection R) (Spec.map c) := torus_isPullback c

/-- The Cartesian comparison does not require even flatness of the coefficient map. -/
example :
    (baseChange (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod 6))))).obj
        (torus (CommRingCat.of ℤ)) ≅ torus (CommRingCat.of (ZMod 6)) :=
  torusBaseChangeIso _

example (c : R ⟶ S) :
    (torusBaseChangeIso c).hom.left ≫ Spec.map (laurentMap c) =
      pullback.fst (laurentProjection R) (Spec.map c) :=
  torusBaseChangeIso_hom_coefficientMap c

example (c : R ⟶ S) :
    (torusBaseChangeIso c).hom.left ≫ laurentProjection S =
      pullback.snd (laurentProjection R) (Spec.map c) :=
  torusBaseChangeIso_hom_projection c

example (c : R ⟶ S) :
    Units.map (torusBaseChangeIso c).hom.left.appTop.hom.toMonoidHom
      (laurentGlobalUnit S) =
        Units.map (pullback.fst (laurentProjection R) (Spec.map c)).appTop.hom.toMonoidHom
          (laurentGlobalUnit R) := torusBaseChangeIso_globalUnit c

example (c : R ⟶ S) :
    (baseChange (Spec.map c)).map (torusOne R) ≫ (torusBaseChangeIso c).hom =
      (baseChangeBaseIso (Spec.map c)).hom ≫ torusOne S :=
  torusBaseChangeIso_one c

example (c : R ⟶ S) (q : ℕ) (i : Fin q) :
    (torusPowerBaseChangeIso c q).hom ≫ torusCoordinate S q i =
      (baseChange (Spec.map c)).map (torusCoordinate R q i) ≫ (torusBaseChangeIso c).hom :=
  torusPowerBaseChangeIso_coordinate c q i

example (c : R ⟶ S) (q : ℕ) (i : Fin (q + 1)) :
    (baseChange (Spec.map c)).map (torusInsertOne R q i) ≫
        (torusPowerBaseChangeIso c (q + 1)).hom =
      (torusPowerBaseChangeIso c q).hom ≫ torusInsertOne S q i :=
  torusPowerBaseChangeIso_insertOne c q i

example (c : R ⟶ S) (q : ℕ) (i : Fin (q + 1)) :
    (baseChange (Spec.map c)).map (torusDeleteCoordinate R q i) ≫
        (torusPowerBaseChangeIso c q).hom =
      (torusPowerBaseChangeIso c (q + 1)).hom ≫ torusDeleteCoordinate S q i :=
  torusPowerBaseChangeIso_deleteCoordinate c q i

example {K L : Type u} [Field K] [Field L] (c : K →+* L) (q : ℕ) :
    (fieldBaseChange c).obj (torusPower (CommRingCat.of K) q) ≅
      torusPower (CommRingCat.of L) q := torusPowerFieldBaseChangeIso c q

open Lean in
run_cmd do
  for name in #[``torus_isPullback, ``torusBaseChangeIso,
      ``torusBaseChangeIso_inv_fst, ``torusBaseChangeIso_inv_snd,
      ``torusBaseChangeIso_hom_coefficientMap, ``torusBaseChangeIso_hom_projection,
      ``laurentEvalOne_coefficient, ``laurentOneSection_coefficient,
      ``torusBaseChangeIso_globalUnit, ``torusBaseChangeIso_one,
      ``torusPowerBaseChangeIso, ``torusPowerBaseChangeIso_coordinate,
      ``torusPowerBaseChangeIso_toBase, ``torusPowerBaseChangeIso_insertOne,
      ``torusPowerBaseChangeIso_deleteCoordinate, ``torusFieldBaseChangeIso,
      ``torusPowerFieldBaseChangeIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end Motivic.MotivicTest.SmoothSiteTorusBaseChange
