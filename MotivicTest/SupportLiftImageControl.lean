/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.SupportLiftImageControl
public import Lean.Util.CollectAxioms

/-! # Consumers of literal closed-support control for actual lift-image generators -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic Motivic.FiniteCorrespondenceGenerator

universe u

section Image

variable {D V Z C : Scheme.{u}} (m : D ⟶ V) (t : V ⟶ Z)
  (j : C ⟶ Z) [IsClosedImmersion j] (a : D ⟶ C) (h : a ≫ j = m ≫ t)

example : m.toImage ≫ m.imageToClosedFactor t j a h = a :=
  m.toImage_imageToClosedFactor t j a h

example : m.imageToClosedFactor t j a h ≫ j = m.imageι ≫ t :=
  m.imageToClosedFactor_comp t j a h

example (r : m.image ⟶ C) (hr : r ≫ j = m.imageι ≫ t) :
    r = m.imageToClosedFactor t j a h := m.imageToClosedFactor_unique t j a h r hr

end Image

section Generator

variable (k : Type u) [Field k] {U V Y : SmoothSite (Spec (.of k))}
  (D : Scheme.{u}) [IsIntegral D] (m : D ⟶ pullback U.hom V.hom) [IsFinite m]
  (hm : Set.range (m ≫ pullback.fst U.hom V.hom) ∈ irreducibleComponents U.left)
  [IsFinite (m ≫ pullback.fst U.hom V.hom)]
  (q : V ⟶ Y) (C : Scheme.{u}) (j : C ⟶ pullback U.hom Y.hom) [IsClosedImmersion j]
  (a : D ⟶ C)
  (ha₁ : a ≫ j ≫ pullback.fst U.hom Y.hom = m ≫ pullback.fst U.hom V.hom)
  (ha₂ : a ≫ j ≫ pullback.snd U.hom Y.hom =
    m ≫ pullback.snd U.hom V.hom ≫ q.left)

example : ∃ r : (supportLiftImageGenerator k D m hm).scheme ⟶ C,
    m.toImage ≫ r = a ∧
    r ≫ j = (supportLiftImageGenerator k D m hm).graphPostcompositionMap
      q.left (MorphismProperty.Over.w q) :=
  exists_supportLiftImageGenerator_closed_factor k D m hm q C j a ha₁ ha₂

end Generator

open Lean in
run_cmd do
  for name in #[``AlgebraicGeometry.Scheme.Hom.imageι_comp_ker_eq,
      ``AlgebraicGeometry.Scheme.Hom.imageToClosedFactor,
      ``AlgebraicGeometry.Scheme.Hom.toImage_imageToClosedFactor,
      ``AlgebraicGeometry.Scheme.Hom.imageToClosedFactor_comp,
      ``Motivic.FiniteCorrespondenceGenerator.exists_supportLiftImageGenerator_closed_factor] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual lift-image support control uses only standard Lean foundations."
