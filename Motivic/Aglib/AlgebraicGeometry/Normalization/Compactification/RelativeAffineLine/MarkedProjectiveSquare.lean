/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.FullOverlap

/-! # The original marked square in the actual relative normalization

Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.MarkedProjectiveSquare`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.`
Module suffix: `RelativeAffineLine.RestrictedMarkedSquare`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y Z : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p]
  (z : Z ⟶ Spec (.of (Polynomial R))) (s : Z ⟶ Y)

/-- The original marked map satisfies the literal normalization triangle. -/
@[reassoc]
theorem marked_toProjectiveLine (hs : s ≫ p = z) :
    (s ≫ inclusion R p) ≫ toProjectiveLine R p =
      z ≫ RelativeProjectiveLine.chart R 0 := by
  rw [Category.assoc, inclusion_toProjectiveLine, ← Category.assoc, hs]
  congr 2

/-- Postcomposing the original whole marked pullback with the open projective chart
preserves the square. No new marked scheme or pullback witness is selected. -/
theorem marked_projective_isPullback (H : IsPullback s (𝟙 Z) p z) :
    IsPullback s (𝟙 Z) (inclusion R p ≫ toProjectiveLine R p)
      (z ≫ RelativeProjectiveLine.chart R 0) := by
  rw [inclusion_toProjectiveLine]
  have hchart : IsPullback z (𝟙 Z) (RelativeProjectiveLine.chart R 0)
      (z ≫ RelativeProjectiveLine.chart R 0) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have h0 : (⟨0⟩ : ULift.{u} (Fin 2)) = 0 := by decide
  simpa only [Category.id_comp, h0] using H.paste_vert hchart

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
