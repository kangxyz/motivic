/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Motivic.Cohomology.Sheaf.H1.AffineLineLocalLifts

/-! # Direct consumers and axiom audit for actual affine-line local lifts -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open _root_.AlgebraicGeometry.Scheme.SmoothSite (affineLine nisnevichTopology)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic
open _root_.CategoryTheory.Sheaf.LargeCohomology
open _root_.Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme.AffineLineReducedComplement

universe w u

variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives
    (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

example
    (F : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (x : H.{w, u + 1, u, u + 1} (nisnevichTopology (Spec (.of k)))
      F 1 (affineLine (.of k))) :
    ∃ (s : (cokernel (Injective.ι F)).obj.obj (op (affineLine (.of k)))),
      injectiveSectionBoundary (nisnevichTopology (Spec (.of k)))
        F (affineLine (.of k)) s = x ∧
    ∃ (U : (line k).Opens), genericPoint (line k) ∈ U ∧
    ∃ (lU : (Injective.under F).obj.obj (op (openObject U))),
      (cokernel.π (Injective.ι F)).hom.app (op (openObject U)) lU =
        (cokernel (Injective.ι F)).obj.map (openInclusion U).op s ∧
    ∃ (Y : SmoothSite (Spec (.of k))) (p : Y ⟶ affineLine (.of k)),
      Etale p.left ∧ IsIso (pullback.snd p.left (inclusion U)) ∧
    ∃ lY : (Injective.under F).obj.obj (op Y),
      (cokernel.π (Injective.ι F)).hom.app (op Y) lY =
        (cokernel (Injective.ι F)).obj.map p.op s :=
  exists_affineLine_local_lifts_of_h_one F x


section

variable {S : Scheme.{u}} [IsNoetherian S]

example
    {I Q : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}}
    (φ : I ⟶ Q) [Epi φ] (X : SmoothSite S) (s : Q.obj.obj (op X))
    {Z : Scheme.{u}} (z : Z ⟶ X.left) [IsClosedImmersion z] [IsLocallyArtinian Z] :
    ∃ (Y : SmoothSite S) (p : Y ⟶ X), Etale p.left ∧
      IsIso (pullback.snd p.left z) ∧
      ∃ l : I.obj.obj (op Y), φ.hom.app (op Y) l = Q.obj.map p.op s :=
  exists_etale_neighborhood_lift φ X s z

end

open Lean in
run_cmd do
  for name in #[``exists_affineLine_local_lifts_of_h_one,
      ``exists_etale_neighborhood_lift,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.exists_open_iso_over_artinian_closed] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual affine-line local lifts use only standard Lean foundations."
