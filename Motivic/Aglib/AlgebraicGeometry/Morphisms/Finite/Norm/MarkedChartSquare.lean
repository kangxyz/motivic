/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange

/-! # Canonical spectra of the whole marked chart pullback

The marked ring is the actual section ring of the whole inverse image, with
its original scalar action and all nilpotents. Its Cartesian square is proved,
not supplied as an additional comparison premise.


Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.MarkedChartSquare`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.AffineMarkedGraphRegular`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.FiniteSchemeNormBaseChange

/-- The spectrum of the original scalar action is the canonical affine
identification followed by the original structure map. -/
theorem spec_scalarMap {R : Type u} [CommRing R] {T : Scheme.{u}}
    [IsAffine T] (p : T ⟶ Spec (.of R)) :
    Spec.map (CommRingCat.ofHom (scalarMap p)) = T.isoSpec.inv ≫ p := by
  change Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop) = _
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv]
  exact Scheme.isoSpec_inv_naturality p

end AlgebraicGeometry.FiniteSchemeNormBaseChange

namespace AlgebraicGeometry.Scheme

/-- The literal whole marked inverse image, in canonical affine coordinates,
retains the actual Cartesian square required for marked-factor flatness. -/
theorem affineMarkedChart_isPullback {R : Type u} [CommRing R]
    {Z K : Scheme.{u}} (z : Z ⟶ K) [IsAffineHom z]
    (t : Spec (.of R) ⟶ K) :
    IsPullback ((pullback z t).isoSpec.inv ≫ pullback.fst z t)
      (Spec.map (CommRingCat.ofHom
        (FiniteSchemeNormBaseChange.scalarMap (pullback.snd z t)))) z t := by
  rw [FiniteSchemeNormBaseChange.spec_scalarMap]
  apply IsPullback.of_iso_pullback _ (pullback z t).isoSpec.symm rfl rfl
  constructor
  simp only [Category.assoc, pullback.condition]

end AlgebraicGeometry.Scheme
