/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.RestrictedMarkedSquare
/-! # The final original source remains open in the one canonical normalization

Both coefficient restrictions are the existing ones. This gives the exact open
map needed for stalk normality and integral-component arguments, without asserting
that the whole finite covering source is integral.

Intended upstream module under the prefix `Aglib.AlgebraicGeometry`:
`Normalization.Compactification.RelativeAffineLine.RestrictedSourceInclusion`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Norm.NativeSectionPairParameterComponents`.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom RelativeProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]

local notation "F₁" => boundaryBaseProjectiveMap R (ULift (Fin 2)) (toProjectiveLine R p) O
local notation "J₁" => boundaryBaseCoverInclusion (boundaryLineProjection R) p (projection R p)
  (inclusion R p) (inclusion_projection R p) ⊤ O
local notation "p₁" => sourceNativeCoverMap R O p

/-- The first unchanged restriction supplies the precise projection equation. -/
@[reassoc]
theorem originalRestrictedSource_projection :
    J₁ ≫ (F₁ ≫ ProjectiveSpace.toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2))) =
      p₁ ≫ boundaryLineProjection Γ(O.toScheme, ⊤) := by
  rw [← Category.assoc, restricted_inclusion_toProjectiveLine, Category.assoc, chart_toSpec]

variable (V : (Spec Γ(O.toScheme, ⊤)).Opens)

/-- The literal source of the original sections after both coefficient restrictions. -/
abbrev finalOriginalSource :=
  (boundaryBaseCoverOpen (boundaryLineProjection Γ(O.toScheme, ⊤)) p₁ ⊤ V).toScheme

/-- The actual final source inclusion into the original, single normalization. -/
def finalOriginalSourceInclusion : finalOriginalSource R p O V ⟶ compactification R p :=
  (boundaryBaseCoverOpen (boundaryLineProjection Γ(O.toScheme, ⊤)) p₁ ⊤ V).ι ≫
    (boundaryBaseCoverOpen (boundaryLineProjection R) p ⊤ O).ι ≫ inclusion R p

instance finalOriginalSourceInclusion_open [IsSeparated p] :
    IsOpenImmersion (finalOriginalSourceInclusion R p O V) := by
  unfold finalOriginalSourceInclusion
  infer_instance

/-- The final section-record inclusion followed by the two unchanged compactification
projections is exactly the original-source open map above. -/
@[reassoc]
theorem finalOriginalSourceInclusion_eq :
    boundaryBaseCoverInclusion (boundaryLineProjection Γ(O.toScheme, ⊤)) p₁
        (F₁ ≫ ProjectiveSpace.toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2))) J₁
        (originalRestrictedSource_projection R p O) ⊤ V ≫
      pullback.snd V.ι (F₁ ≫ ProjectiveSpace.toSpec Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2))) ≫
      pullback.snd O.ι (projection R p) = finalOriginalSourceInclusion R p O V := by
  rw [← Category.assoc, boundaryBaseCoverInclusion_snd, Category.assoc,
    boundaryBaseCoverInclusion_snd]
  rfl

/-- Every final original-source stalk is canonically the corresponding normalization
stalk. Consumers can transfer normality and domain properties without a global
source-integrality assumption. -/
def finalOriginalSourceStalkIso [IsSeparated p] (y : finalOriginalSource R p O V) :
    (compactification R p).presheaf.stalk (finalOriginalSourceInclusion R p O V y) ≅
      (finalOriginalSource R p O V).presheaf.stalk y :=
  asIso ((finalOriginalSourceInclusion R p O V).stalkMap y)

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
