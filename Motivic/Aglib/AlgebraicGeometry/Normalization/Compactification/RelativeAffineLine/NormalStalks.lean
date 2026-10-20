/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Stalks
public import Motivic.Aglib.AlgebraicGeometry.Properties.Normal.OpenImmersion
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.Basic
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.Compactification

/-!
# Normal stalks on the actual relative affine-line compactification

The original generic finite-etale normalization has normal-domain stalks.
The first and final coefficient restrictions inherit them through their actual
open-immersion projections. No new normalization, coefficient open, free-chart
hypothesis, source nonemptiness or global integrality is introduced. This asserts
normality of the total spaces, not normality of their residue-field fibers.

Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NormalStalks`.
The current consumer is the fixed-witness standard-triple property assembly.
All coefficient and morphism hypotheses are explicit in the signatures below.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

namespace RelativeAffineLineEtaleCompactification

open Scheme.Hom

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p]

/-- The constructed compactification has normal-domain stalks without a global
integral or nonempty source hypothesis. -/
theorem compactification_normalStalks : NormalStalks (compactification R p) := by
  intro x
  exact (FiniteEtale.GenericNormalization.stalk_normal_domain
    (ProjectiveSpace R (ULift.{u} (Fin 2)))
    (EtaleCompactification.genericCover _ (projectiveMap R p)) x).symm

/-- The first actual coefficient restriction inherits the same normal stalks. -/
theorem originalCoefficient_normalStalks (O : (Spec (.of R)).Opens) :
    NormalStalks (boundaryBaseCompactification (projection R p) O) :=
  (compactification_normalStalks R p).of_isOpenImmersion
    (pullback.snd O.ι (projection R p))

/-- The final already selected coefficient open inherits normality through its
literal second projection, not by re-normalizing or assuming normal fibers. -/
theorem finalCoefficient_normalStalks
    (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
    (V : (Spec Γ(O.toScheme, ⊤)).Opens) :
    NormalStalks (boundaryBaseCompactification
      (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) (toProjectiveLine R p) O ≫
        ProjectiveSpace.toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2))) V) :=
  (originalCoefficient_normalStalks R p O).of_isOpenImmersion
    (pullback.snd V.ι
      (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) (toProjectiveLine R p) O ≫
        ProjectiveSpace.toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2))))

end RelativeAffineLineEtaleCompactification

end AlgebraicGeometry.Scheme
