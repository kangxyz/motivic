/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Etale
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Quasi-affineness of actual separated quasi-compact étale sources -/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme

universe u

/-- The original étale source is quasi-affine, using its actual relative normalization.
No affine model or compactification is assumed. -/
theorem isQuasiAffine_of_etale_affine_target {Y X : Scheme.{u}} [IsAffine X]
    (f : Y ⟶ X) [Etale f] [QuasiCompact f] [IsSeparated f] : Y.IsQuasiAffine := by
  have : LocallyQuasiFinite f := EtaleCompactification.locallyQuasiFinite_of_etale f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  exact IsQuasiAffine.of_isImmersion f.toNormalization

end AlgebraicGeometry.Scheme
