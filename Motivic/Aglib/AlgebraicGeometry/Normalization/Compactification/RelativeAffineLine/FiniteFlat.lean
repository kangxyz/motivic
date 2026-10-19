/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.Basic
public import Motivic.Aglib.AlgebraicGeometry.Normalization.FiniteCurve.ProjectiveFiniteFlat

/-!
# Finite flat shrinking of an actual étale affine-line compactification

The original source need not be affine. We apply the projective theorem to its
existing generic cover, retaining the exact original compactification map.
The original open inclusion and any whole marked divisor are retained by literal
base change along the same coefficient localization.


Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.FiniteFlat`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.`
Module suffix: `RelativeAffineLine.CommonCoefficientOpen`,
`Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.GraphFreeCover`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

universe u

/-- After one nonzero coefficient localization the original compactification is
finite flat over the entire projective line. No affine-source hypothesis or
replacement normalization is used. -/
theorem exists_finite_flat_baseChange
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] :
    ∃ r : R, r ≠ 0 ∧
      IsFinite (pullback.snd (toProjectiveLine R p)
        (ProjectiveSpace.map (algebraMap R (Localization.Away r)) (ULift.{u} (Fin 2)))) ∧
      Flat (pullback.snd (toProjectiveLine R p)
        (ProjectiveSpace.map (algebraMap R (Localization.Away r)) (ULift.{u} (Fin 2)))) :=
  FiniteEtale.GenericNormalization.exists_finite_flat_projective_baseChange R
    (EtaleCompactification.genericCover (ProjectiveSpace R (ULift.{u} (Fin 2)))
      (projectiveMap R p))

/-- Both canonical whole affine-line charts of the same compactification have
free coordinate modules after one common coefficient localization. The scalar
actions are the literal structural maps; global freeness on P1 is not asserted. -/
theorem exists_free_chart_sections_baseChange
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] :
    ∃ r : R, r ≠ 0 ∧ ∀ i : ULift.{u} (Fin 2),
      let A := Localization.Away r
      let g := RelativeProjectiveLine.chart A i ≫
        ProjectiveSpace.map (algebraMap R A) (ULift.{u} (Fin 2))
      let : Algebra (Polynomial A) Γ(pullback (toProjectiveLine R p) g, ⊤) :=
        (FiniteSchemeNormBaseChange.scalarMap (pullback.snd (toProjectiveLine R p) g)).toAlgebra
      Module.Free (Polynomial A) Γ(pullback (toProjectiveLine R p) g, ⊤) :=
  FiniteEtale.GenericNormalization.exists_free_projective_chart_sections_baseChange R
    (EtaleCompactification.genericCover (ProjectiveSpace R (ULift.{u} (Fin 2)))
      (projectiveMap R p))

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
