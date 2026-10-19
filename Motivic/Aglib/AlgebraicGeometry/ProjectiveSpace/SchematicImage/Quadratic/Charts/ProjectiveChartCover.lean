/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.ImageCoordinates
/-! # The nonzero original quadratic pivots cover the actual global schematic image -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry ProjectiveSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} (g : σ → R)

theorem quadraticProjectiveGenericMap_preimage_coordinateOpen (j : Exponent σ) :
    quadraticProjectiveGenericMap k R g ⁻¹ᵁ coordinateOpen k (Exponent σ) j =
      PrimeSpectrum.basicOpen (algebraMap R (FractionRing R) (monomialFunction k R g j)) := by
  rw [quadraticProjectiveGenericMap, Scheme.Hom.comp_preimage,
    coordinateChart_preimage_coordinateOpen]
  rw [SpecMap_preimage_basicOpen]
  congr 1
  change nativeDehomogenization k R g constantIndex
    (coordinateRatio k (Exponent σ) constantIndex j) = _
  rw [nativeDehomogenization_ratio k R g constantIndex j (by simp)]
  simp [ratio]

/-- An identically zero original monomial gives an empty chart of the actual closure. -/
theorem quadraticProjectiveImage_coordinate_ne_zero (x : quadraticProjectiveImage k R g)
    (j : Exponent σ)
    (hx : (quadraticProjectiveGenericMap k R g).imageι x ∈ coordinateOpen k (Exponent σ) j) :
    monomialFunction k R g j ≠ 0 := by
  intro hj
  have hp : quadraticProjectiveGenericMap k R g ⁻¹ᵁ coordinateOpen k (Exponent σ) j = ⊥ := by
    rw [quadraticProjectiveGenericMap_preimage_coordinateOpen, hj, map_zero]
    exact PrimeSpectrum.basicOpen_zero
  have hcl : (quadraticProjectiveGenericMap k R g).imageι x ∈
      closure (Set.range (quadraticProjectiveGenericMap k R g)) := by
    rw [← Scheme.Hom.support_ker]
    exact Scheme.IdealSheafData.range_subschemeι _ ▸ ⟨x, rfl⟩
  obtain ⟨y, hy, hyU⟩ :=
    (closure_inter_open_nonempty_iff (coordinateOpen k (Exponent σ) j).isOpen).mp
      ⟨_, hcl, hx⟩
  obtain ⟨z, rfl⟩ := hy
  have : z ∈ quadraticProjectiveGenericMap k R g ⁻¹ᵁ coordinateOpen k (Exponent σ) j := hyU
  simp [hp] at this

/-- The actual closure is covered by precisely the original nonzero-pivot charts. -/
theorem quadraticProjectiveImage_exists_chart (x : quadraticProjectiveImage k R g) :
    ∃ j : Exponent σ, monomialFunction k R g j ≠ 0 ∧
      (quadraticProjectiveGenericMap k R g).imageι x ∈ coordinateOpen k (Exponent σ) j := by
  have hx : (quadraticProjectiveGenericMap k R g).imageι x ∈
      (⨆ j, coordinateOpen k (Exponent σ) j) := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨j, quadraticProjectiveImage_coordinate_ne_zero k R g x j hj, hj⟩

end QuadraticIncidence.InfinityChart
