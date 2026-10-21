/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.FieldNormal
public import Mathlib.RingTheory.KrullDimension.PID

/-! # Codimension of actual nongeneric projective-line points -/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ProjectiveLine

universe u
variable (k : Type u) [Field k]
attribute [local instance] specializationOrder

/-- Every point other than the actual generic point of the projective line has codimension one. -/
theorem coheight_eq_one_of_ne_genericPoint
    (x : ProjectiveSpace k (ULift.{u} (Fin 2)))
    (hx : x ≠ genericPoint (ProjectiveSpace k (ULift.{u} (Fin 2)))) :
    Order.coheight x = 1 := by
  have hm : x ∈ ⨆ i, (chart k i).opensRange := by rw [iSup_chart_opensRange]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, y, hy⟩ := hm
  have hyne : y ≠ genericPoint (Spec (.of (Polynomial k))) := by
    intro h
    apply hx
    rw [← hy, h, genericPoint_eq_of_isOpenImmersion]
  have hbot : y.asIdeal ≠ ⊥ := by
    intro h
    apply hyne
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext h
  have : y.asIdeal.IsPrime := y.isPrime
  have : y.asIdeal.IsMaximal := IsPrime.to_maximal_ideal hbot
  rw [← hy, coheight_eq_of_isOpenImmersion, ← idealHeight_eq_coheight]
  exact IsPrincipalIdealRing.height_eq_one_of_isMaximal _ (Polynomial.not_isField k)

end AlgebraicGeometry.ProjectiveLine
