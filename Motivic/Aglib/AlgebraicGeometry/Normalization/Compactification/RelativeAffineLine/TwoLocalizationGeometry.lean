/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.BaseChange.TwoLocalizations
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.CoefficientFlat
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NormalStalks

/-!
# Geometry of the same twice-localized relative affine-line normalization

The existing normalization supplies normal stalks, and the original localized
whole-chart freeness witnesses supply flatness. Both are transported to the
literal nested source used by the fixed-witness full-boundary ambient theorem.
Every irreducible component of each native structural fiber has dimension one.
No new normalization, open, free basis, nonempty-source or reducedness premise
is introduced. These are total-space normality and componentwise fiber dimension,
not a complete standard-triple or marked-splitting theorem.

Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.TwoLocalizationGeometry`.
Current consumer: the fixed-witness two-localization standard-triple assembly.
The complete original free-chart scalar maps remain explicit below; the lower
Cartesian squares and finite/open/proper instances specialize directly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

open Scheme.Hom RelativeProjectiveLine
open AlgebraicGeometry.FiniteSchemeNormBaseChange

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  (a : Γ(O.toScheme, ⊤)) (b : Localization.Away a)

/-- The literal two-localization source of the actual normalization has normal
stalks, supplied by that normalization, not by a new normality premise. -/
theorem twoLocalization_normalStalks :
    NormalStalks (TwoLocalizations.source Γ(O.toScheme, ⊤) a b
      (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) (toProjectiveLine R p) O)) :=
  TwoLocalizations.normalStalks Γ(O.toScheme, ⊤) a b _
    (originalCoefficient_normalStalks R p O)

variable (r : R) (hOr : O ≤ PrimeSpectrum.basicOpen r)
  (hfree : ∀ i : ULift.{u} (Fin 2),
    let w := chart (Localization.Away r) i ≫
      ProjectiveSpace.map (algebraMap R (Localization.Away r)) (ULift.{u} (Fin 2))
    let : Algebra (Polynomial (Localization.Away r))
      Γ(pullback (toProjectiveLine R p) w, ⊤) :=
      (scalarMap (pullback.snd (toProjectiveLine R p) w)).toAlgebra
    Module.Free (Polynomial (Localization.Away r)) Γ(pullback (toProjectiveLine R p) w, ⊤))

include hOr hfree in
/-- The same original free-chart witnesses supply flatness after both literal
localizations; no new coefficient or basis choice is made. -/
theorem twoLocalization_projectiveMap_flat :
    Flat (TwoLocalizations.toProjectiveLine Γ(O.toScheme, ⊤) a b
      (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) (toProjectiveLine R p) O)) := by
  let : Flat (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) (toProjectiveLine R p) O) :=
    originalCoefficient_projectiveMap_flat R r O hOr (toProjectiveLine R p) hfree
  infer_instance

include hOr hfree in
/-- Native fiber components on the actual twice-localized normalization have
dimension one, including the vacuous empty-source case. -/
theorem twoLocalization_fiber_component_dimension
    (x : Spec (.of (Localization.Away b)))
    {Z : Set ((TwoLocalizations.projection Γ(O.toScheme, ⊤) a b
      (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) (toProjectiveLine R p) O)).fiber x)}
    (hZ : Z ∈ irreducibleComponents ((TwoLocalizations.projection Γ(O.toScheme, ⊤) a b
      (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) (toProjectiveLine R p) O)).fiber x)) :
    topologicalKrullDim Z = 1 := by
  let : Flat (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) (toProjectiveLine R p) O) :=
    originalCoefficient_projectiveMap_flat R r O hOr (toProjectiveLine R p) hfree
  exact TwoLocalizations.fiber_component_dimension Γ(O.toScheme, ⊤) a b _ x hZ

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
