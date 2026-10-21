/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeMiddleInput
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.OriginalLocalizationInput

/-! # Native endpoints of an abstract localization history

Intended upstream module: `Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.LocalizationHistory`.

The coefficient line and source map are identified while the localization
history and its section witnesses are variables. Concrete representative
adapters use these facts without expanding their entire construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Scheme.Hom RelativeProjectiveLine

universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
namespace OriginalLocalizationHistory.SourceWitnesses

attribute [local instance] OriginalLocalizationSeed.commRing
  OriginalLocalizationSeed.affineO OriginalLocalizationHistory.affineV

local instance localizationHistoryLineSmooth (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

local instance localizationHistorySmoothOfRelativeDimension {X Y : Scheme.{u}}
    (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f

variable {H : OriginalLocalizationHistory.{u}} {B : H.BoundaryWitnesses}
  {k : Type u} [Field k] (W : H.SourceWitnesses B) (T : H.TargetWitnesses)
  (t : Spec Γ(H.V.toScheme, ⊤) ⟶ Spec (.of k)) [Smooth t]

/-- The native line uses the same final coefficient ring and field map. -/
theorem toNative_lineSite_eq :
    (W.toNative T t).nativeLineSite =
      SmoothSite.mk (boundaryLineProjection Γ(H.V.toScheme, ⊤) ≫ t) := rfl

/-- The native source map is the stored second localization map. -/
theorem toNative_sourceMap_eq : (W.toNative T t).p = H.p₂ := rfl

end OriginalLocalizationHistory.SourceWitnesses
end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
