module

import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.ProperQuasiAffine

/-! Direct checks of genuine proper/quasi-affine finiteness and zero-scheme regularity. -/

set_option linter.hashCommand false

open CategoryTheory AlgebraicGeometry

universe u

example {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [X.IsQuasiAffine]
    [IsAffine Y] : IsFinite f :=
  Scheme.isFinite_of_isProper_of_isQuasiAffine f

example {X : Scheme.{u}} (K : Type u) [Field K]
    (p : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 p]
    (L : Scheme.Modules.Invertible.LineBundle X)
    (φ : L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsFinite (Scheme.Modules.Hom.zeroInclusion φ ≫ p)] : Mono φ :=
  Scheme.Modules.Invertible.mono_of_finite_zeroScheme K p L φ

example {X : Scheme.{u}} (K : Type u) [Field K]
    (p : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 p]
    (L : Scheme.Modules.Invertible.LineBundle X)
    (φ : L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsProper (Scheme.Modules.Hom.zeroInclusion φ ≫ p)]
    [(Scheme.Modules.Hom.zeroScheme φ).IsQuasiAffine] : Mono φ :=
  Scheme.Modules.Invertible.mono_of_proper_quasiAffine_zeroScheme K p L φ

#print axioms AlgebraicGeometry.Scheme.isFinite_of_isProper_of_isQuasiAffine
#print axioms AlgebraicGeometry.Scheme.Modules.Invertible.mono_of_zeroScheme_isLocallyArtinian
#print axioms AlgebraicGeometry.Scheme.Modules.Invertible.mono_of_finite_zeroScheme
#print axioms AlgebraicGeometry.Scheme.Modules.Invertible.mono_of_proper_quasiAffine_zeroScheme
#print axioms AlgebraicGeometry.Scheme.Modules.Invertible.mono_and_flat_of_finite_zeroScheme
#print axioms AlgebraicGeometry.Scheme.Modules.Invertible.finite_mono_flat_of_proper_zeroScheme
#print axioms AlgebraicGeometry.Scheme.Modules.Invertible.finite_mono_flat_on_open_of_proper
