/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.Normalized.Diagonal.SectionPair

/-! The whole prescribed boundary is constructed on the original compactification. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.AffineLineEtaleCompactification
universe u
example (k : Type u) [Field k] {Y : Scheme.{u}} {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
    (r : Spec (.of R) ⟶ Y) [IsOpenImmersion r]
    (B : Type u) [CommRing B] (z : Polynomial k →+* B)
    [IsClosedImmersion (Scheme.Hom.boundaryCoordinateMap k B z)]
    [IsFinite (Scheme.Hom.boundaryCoordinateMap k B z ≫ Scheme.Hom.boundaryLineProjection k)]
    (s : Spec (.of B) ⟶ Spec (.of R))
    (hs : s ≫ (r ≫ p) = Scheme.Hom.boundaryCoordinateMap k B z)
    (H : IsPullback s (𝟙 _) (r ≫ p) (Scheme.Hom.boundaryCoordinateMap k B z)) :=
  exists_actualDiagonalSectionPair k p r B z s hs H
#print axioms exists_actualDiagonalSectionPair
