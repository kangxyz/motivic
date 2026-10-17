/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualDiagonalBoundary

/-! The whole prescribed boundary is constructed on the original compactification. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.AffineLineEtaleCompactification
universe u
example (k : Type u) [Field k] {Y S : Scheme.{u}}
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
    (r : S ⟶ Y) [IsOpenImmersion r]
    (B : Type u) [CommRing B] (z : Polynomial k →+* B)
    (s : Spec (.of B) ⟶ S)
    (hs : s ≫ (r ≫ p) = Scheme.Hom.boundaryCoordinateMap k B z)
    (H : IsPullback s (𝟙 _) (r ≫ p) (Scheme.Hom.boundaryCoordinateMap k B z)) :=
  exists_actualFullBoundaryDivisorIso k p r B z s hs H
#print axioms exists_actualFullBoundaryDivisorIso
