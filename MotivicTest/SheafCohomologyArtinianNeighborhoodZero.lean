/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Cohomology.Sheaf.ArtinianNeighborhoodZero
import Lean
/-! # Direct original-cohomology consumer and foundation audit -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open _root_.AlgebraicGeometry.Scheme.SmoothSite (nisnevichTopology)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Motivic
open _root_.CategoryTheory.Sheaf.LargeCohomology _root_.Motivic.SheafCohomology
universe w u

example {S : Scheme.{u}} [IsNoetherian S]
    [HasExt.{w} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})]
    (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
    (n : ℕ) (X : SmoothSite S)
    (e : H.{w, u + 1, u, u + 1} (nisnevichTopology S) F (n + 1) X)
    {Z : Scheme.{u}} (z : Z ⟶ X.left) [IsClosedImmersion z] [IsLocallyArtinian Z] :
    ∃ (Y : SmoothSite S) (p : Y ⟶ X), Etale p.left ∧
      IsIso (pullback.snd p.left z) ∧
      (presheaf.{w, u + 1, u, u + 1} (nisnevichTopology S)
        F (n + 1)).map p.op e = 0 :=
  exists_etale_neighborhood_restriction_eq_zero F n X e z

open Lean in
run_cmd do
  for a in ← collectAxioms ``exists_etale_neighborhood_restriction_eq_zero do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "Unsupported assumption: {a}"
  logInfo "Actual positive ordinary Artinian-neighborhood zero: standard foundations only."
