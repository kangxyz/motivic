/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Spectrum.Prime.PrincipalNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Source-local principal neighborhoods
-/

@[expose] public noncomputable section

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace AlgebraicGeometry

/-- Source-local properties hold on a union of opens on which they hold. -/
theorem sourceLocal_on_iSup {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, P ((U i).ι ≫ f)) :
    P ((⨆ i, U i).ι ≫ f) := by
  let V : X.Opens := ⨆ i, U i
  let W : ι → V.toScheme.Opens := fun i => V.ι ⁻¹ᵁ U i
  have hW : iSup W = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  apply IsZariskiLocalAtSource.of_iSup_eq_top W hW
  intro i
  let t := V.ι.resLE (U i) (W i) le_rfl
  have : IsOpenImmersion t := by
    dsimp [t, W]
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have ht : t ≫ (U i).ι = (W i).ι ≫ V.ι := Scheme.Hom.resLE_comp_ι _ _
  rw [← Category.assoc, ← ht, Category.assoc]
  exact IsZariskiLocalAtSource.comp (hU i) t

/-- The neighborhood remains the actual principal open of the original affine scheme. -/
theorem exists_principal_neighborhood_of_local_property
    (R : Type u) [CommRing R] {Y : Scheme.{u}} (f : Spec (.of R) ⟶ Y)
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    (J : Ideal R)
    (h : ∀ x : PrimeSpectrum R, J ≤ x.asIdeal →
      ∃ a : R, a ∉ x.asIdeal ∧
        P ((Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen a)) ≫ f)) :
    ∃ r : R, r - 1 ∈ J ∧
      P ((Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r)) ≫ f) := by
  let T := {a : R // P ((Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen a)) ≫ f)}
  let U : T → (Spec (.of R)).Opens := fun a => PrimeSpectrum.basicOpen a.val
  have hU : PrimeSpectrum.zeroLocus (J : Set R) ⊆ (⨆ a, U a).carrier := by
    intro x hx
    obtain ⟨a, ha, hPa⟩ := h x hx
    exact Opens.mem_iSup.mpr ⟨⟨a, hPa⟩, ha⟩
  obtain ⟨r, hr, hrU⟩ := PrimeSpectrum.exists_basicOpen_between_zeroLocus R J _ hU
  refine ⟨r, hr, ?_⟩
  have H := sourceLocal_on_iSup f P U (fun a => a.property)
  have H' := IsZariskiLocalAtSource.comp H ((Spec (.of R)).homOfLE hrU)
  simpa only [← Category.assoc, Scheme.homOfLE_ι] using H'

end AlgebraicGeometry
