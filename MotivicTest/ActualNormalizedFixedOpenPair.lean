/-
Copyright (c) 2026 Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualNormalizedFixedOpenPair

/-! # Direct normalized fixed-open pair consumer and axiom audit -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Scheme.AffineLineEtaleCompactification
universe u
variable (k : Type u) [Field k] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]

example {R : Type u} [CommRing R]
    [IsNoetherianRing R] (a : Spec (.of R) ⟶ Spec (.of (Polynomial k)))
    [IsOpenImmersion a] (B : Type u) [CommRing B] (z : Polynomial k →+* B)
    (h : Disjoint (Set.range a) (Set.range (Scheme.Hom.boundaryCoordinateMap k B z)))
    [IsClosedImmersion (Scheme.Hom.boundaryCoordinateMap k B z)]
    [IsFinite (Scheme.Hom.boundaryCoordinateMap k B z ≫ Scheme.Hom.boundaryLineProjection k)]
    (s : Spec (.of B) ⟶ Y) (hs : s ≫ p = Scheme.Hom.boundaryCoordinateMap k B z)
    (H : IsPullback s (𝟙 _) p (Scheme.Hom.boundaryCoordinateMap k B z))
    (U : (Spec (.of (Polynomial k))).Opens)
    (hz : Set.range (Scheme.Hom.boundaryCoordinateMap k B z) =
      (U : Set (Spec (.of (Polynomial k))))ᶜ) :
    let C := fixedAmbient k p a
    let zD := fixedBoundaryMap k p a B z s hs
    let E := fixedBoundaryUnit k p a B z h
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      let T := fixedTwistBundle k p a d
      ∃ n t : SheafOfModules.unit C.ringCatSheaf ⟶ T.val,
        pullbackSectionMap zD n = E.hom ≫ pullbackSectionMap zD t ∧
        IsIso (pullbackSectionMap zD n) ∧ IsIso (pullbackSectionMap zD t) ∧
        FixedRetainedSectionFiniteFlat k p a U T n ∧
        FixedRetainedSectionFiniteFlat k p a U T t :=
  exists_actualNormalizedFixedOpenPair k p a B z h s hs H U hz

open Lean in
run_cmd do
  let name := ``exists_actualNormalizedFixedOpenPair
  for axiomName in ← collectAxioms name do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "{name} depends on unsupported assumption {axiomName}"
  logInfo "The actual normalized fixed-open pair uses only standard Lean foundations."
