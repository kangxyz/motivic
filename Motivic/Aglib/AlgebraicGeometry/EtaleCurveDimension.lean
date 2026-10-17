/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.StalkMap
public import Aglib.AlgebraicGeometry.Stalk.Dimension
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Dimension bounds on actual étale curves -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- An étale morphism over a locally Noetherian scheme cannot increase
its source's global dimension. No quasi-compactness or nonemptiness is needed. -/
theorem topologicalKrullDim_le_of_etale
    {V X : Scheme.{u}} [IsLocallyNoetherian X] (p : V ⟶ X) [Etale p] :
    topologicalKrullDim V ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_iSup_stalk, topologicalKrullDim_eq_iSup_stalk]
  apply iSup_le
  intro v
  rw [ringKrullDim_stalk_eq_of_etale p v]
  exact le_iSup (fun x : X => ringKrullDim (X.presheaf.stalk x)) (p v)

/-- Every actual étale scheme over the polynomial affine line has dimension
at most one, over an arbitrary field and without integrality assumptions. -/
theorem topologicalKrullDim_le_one_of_etale_affineLine
    {k : Type u} [Field k] {V : Scheme.{u}}
    (p : V ⟶ Spec (.of (Polynomial k))) [Etale p] :
    topologicalKrullDim V ≤ 1 := by
  apply (topologicalKrullDim_le_of_etale p).trans
  change topologicalKrullDim (PrimeSpectrum (Polynomial k)) ≤ 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← Nat.cast_one,
    ← Ring.krullDimLE_iff]
  infer_instance

end AlgebraicGeometry.Scheme
