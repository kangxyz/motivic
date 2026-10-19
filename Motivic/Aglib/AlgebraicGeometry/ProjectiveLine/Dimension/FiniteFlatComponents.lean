/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.KrullDimension.PolynomialFiniteFlatComponents
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.Basic
public import Aglib.AlgebraicGeometry.Stalk.Dimension
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.Constructions

/-!
# Component dimension of finite flat projective-line covers

The actual two polynomial charts and their actual pullbacks reduce component
dimension to the affine algebra theorem.
The upper bound uses only finiteness; flatness supplies the lower bound for
each component. No nonempty, reduced, integral-source or positive-rank
assumption is made. No relative-dimension predicate or fiber comparison is
introduced here.

Intended upstream module: `Aglib.AlgebraicGeometry.ProjectiveLine.Dimension.FiniteFlatComponents`.
Standalone API; no current external import consumer.
The interfaces and exact hypotheses are given in the declarations below.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u v

namespace AlgebraicGeometry.FiniteSchemeNormBaseChange

/-- Flatness on actual affine global sections for the literal structural
scalar map, including the inverse `ΓSpecIso` in that map. -/
theorem sections_flat
    {R : Type u} [CommRing R] {T : Scheme.{u}}
    (p : T ⟶ Spec (.of R)) [IsAffine T] [Flat p] :
    let : Algebra R Γ(T, ⊤) := (scalarMap p).toAlgebra
    Module.Flat R Γ(T, ⊤) := by
  let : Algebra R Γ(T, ⊤) := (scalarMap p).toAlgebra
  change (scalarMap p).Flat
  exact (RingHom.Flat.of_bijective
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective).comp
      p.flat_appTop

end AlgebraicGeometry.FiniteSchemeNormBaseChange

namespace AlgebraicGeometry.Scheme

/-- A dimension upper bound on a native open cover bounds the whole scheme.
The proof transports actual stalks and does not require nonempty charts. -/
theorem topologicalKrullDim_le_of_openCover
    {X : Scheme.{u}} (𝒰 : Scheme.OpenCover.{v} X) {n : WithBot ℕ∞}
    (h𝒰 : ∀ i, topologicalKrullDim (𝒰.X i) ≤ n) :
    topologicalKrullDim X ≤ n := by
  rw [topologicalKrullDim_eq_iSup_stalk]
  apply iSup_le
  intro x
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  rw [(asIso ((𝒰.f i).stalkMap y)).commRingCatIsoToRingEquiv.ringKrullDim]
  refine (le_iSup (fun z : 𝒰.X i ↦ ringKrullDim ((𝒰.X i).presheaf.stalk z)) y).trans ?_
  rw [← topologicalKrullDim_eq_iSup_stalk]
  exact h𝒰 i

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.RelativeProjectiveLine

open FiniteSchemeNormBaseChange

/-- The literal inverse images of the two polynomial charts, presented by
their actual affine global sections. No component is selected or discarded. -/
private def polynomialPreimageSpecCover
    (R : Type u) [CommRing R] {C : Scheme.{u}}
    (g : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsAffineHom g] :
    C.OpenCover := by
  refine Scheme.Cover.mkOfCovers (ULift.{u} (Fin 2))
    (fun i ↦ Spec Γ(pullback g (chart R i), ⊤))
    (fun i ↦ (pullback g (chart R i)).isoSpec.inv ≫ pullback.fst g (chart R i)) ?_
  intro x
  have hx : g x ∈ (⨆ i, (chart R i).opensRange) := by
    rw [iSup_chart_opensRange]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hx' : x ∈ Set.range (pullback.fst g (chart R i)) := by
    rw [IsOpenImmersion.range_pullbackFst]
    exact hi
  obtain ⟨y, rfl⟩ := hx'
  refine ⟨i, (pullback g (chart R i)).isoSpec.hom y, ?_⟩
  change ((pullback g (chart R i)).isoSpec.hom ≫
    (pullback g (chart R i)).isoSpec.inv ≫ pullback.fst g (chart R i)) y = _
  rw [Iso.hom_inv_id_assoc]

/-- Every finite scheme over the native projective line over a field has
dimension at most one; the source may be empty, disconnected or nonreduced. -/
theorem topologicalKrullDim_le_one_of_isFinite
    (K : Type u) [Field K] {C : Scheme.{u}}
    (g : C ⟶ ProjectiveSpace K (ULift.{u} (Fin 2))) [IsFinite g] :
    topologicalKrullDim C ≤ 1 := by
  apply Scheme.topologicalKrullDim_le_of_openCover (polynomialPreimageSpecCover K g)
  intro i
  let T := pullback g (chart K i)
  let q : T ⟶ Spec (.of (Polynomial K)) := pullback.snd g (chart K i)
  let : Algebra (Polynomial K) Γ(T, ⊤) := (scalarMap q).toAlgebra
  let : Module.Finite (Polynomial K) Γ(T, ⊤) := sections_finite q
  change topologicalKrullDim (PrimeSpectrum Γ(T, ⊤)) ≤ 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  refine (ringKrullDim_le_of_isIntegral (Polynomial K) Γ(T, ⊤)).trans ?_
  exact (Ring.krullDimLE_iff (R := Polynomial K) (n := 1)).mp inferInstance

/-- Every irreducible component of a finite flat cover of the native
projective line has dimension one. Empty sources satisfy this vacuously. -/
theorem topologicalKrullDim_eq_one_of_mem_irreducibleComponents_of_finite_flat
    (K : Type u) [Field K] {C : Scheme.{u}}
    (g : C ⟶ ProjectiveSpace K (ULift.{u} (Fin 2))) [IsFinite g] [Flat g]
    {Z : Set C} (hZ : Z ∈ irreducibleComponents C) :
    topologicalKrullDim Z = 1 := by
  refine le_antisymm ((topologicalKrullDim_subspace_le C Z).trans
    (topologicalKrullDim_le_one_of_isFinite K g)) ?_
  obtain ⟨x, hx⟩ := hZ.1.1
  let 𝒰 := polynomialPreimageSpecCover K g
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
  have hmeet : (Z ∩ Set.range (𝒰.f i)).Nonempty := ⟨x, hx, y, hy⟩
  have hcomp := preimage_mem_irreducibleComponents hZ (𝒰.f i).isOpenEmbedding hmeet
  let T := pullback g (chart K i)
  let q : T ⟶ Spec (.of (Polynomial K)) := pullback.snd g (chart K i)
  let : Algebra (Polynomial K) Γ(T, ⊤) := (scalarMap q).toAlgebra
  let : Module.Finite (Polynomial K) Γ(T, ⊤) := sections_finite q
  let : Module.Flat (Polynomial K) Γ(T, ⊤) := sections_flat q
  have hdim : topologicalKrullDim ((𝒰.f i) ⁻¹' Z) = 1 :=
    PrimeSpectrum.topologicalKrullDim_eq_one_of_mem_irreducibleComponents_finite_flat_polynomial
      (K := K) hcomp
  have hmaps : Set.MapsTo (𝒰.f i) ((𝒰.f i) ⁻¹' Z) Z := fun _ hz ↦ hz
  have hle := ((𝒰.f i).isOpenEmbedding.isInducing.restrict hmaps).topologicalKrullDim_le
  rwa [hdim] at hle

end AlgebraicGeometry.RelativeProjectiveLine
