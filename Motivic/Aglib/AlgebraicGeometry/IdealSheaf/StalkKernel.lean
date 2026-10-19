/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.IdealSheaf.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Localization.Algebra

/-!
# Stalks of the kernel ideal of a closed immersion

The affine section map of a closed immersion is surjective. Localizing this
map at the corresponding prime ideals identifies the stalk of its actual
kernel ideal with the kernel of its actual map on structure-sheaf stalks.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- For a closed immersion the ideal-sheaf kernel has the actual stalk-map kernel. -/
theorem ker_stalk (x : X) :
    f.ker.stalk (f x) = RingHom.ker (f.stalkMap x).hom := by
  obtain ⟨U, hU, hxU, -⟩ :=
    Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (show f x ∈ (⊤ : Y.Opens) from trivial)
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let p := hU.primeIdealOf ⟨f x, hxU⟩
  let q := hV.primeIdealOf ⟨x, hxU⟩
  let g := (f.app U).hom
  let := Y.presheaf.algebra_section_stalk ⟨f x, hxU⟩
  let := X.presheaf.algebra_section_stalk ⟨x, (show x ∈ V from hxU)⟩
  have := hU.isLocalization_stalk ⟨f x, hxU⟩
  have := hV.isLocalization_stalk ⟨x, (show x ∈ V from hxU)⟩
  have hpq : q.asIdeal.comap g = p.asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV (le_refl V) hxU
    change PrimeSpectrum.comap (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom q = p at h
    rw [f.appLE_eq_app] at h
    exact congrArg PrimeSpectrum.asIdeal h
  have hg : Function.Surjective g := f.app_surjective U hU
  have hT : p.asIdeal.primeCompl.map g = q.asIdeal.primeCompl := by
    have hpc : p.asIdeal.primeCompl = q.asIdeal.primeCompl.comap g := by
      ext r
      change r ∉ p.asIdeal ↔ g r ∉ q.asIdeal
      rw [← hpq]
      rfl
    rw [hpc]
    exact Submonoid.map_comap_eq_of_surjective hg _
  have hmap : IsLocalization.map (X.presheaf.stalk x) g
      (hT.symm ▸ p.asIdeal.primeCompl.le_comap_map) = (f.stalkMap x).hom := by
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    ext s
    exact (IsLocalization.map_eq (S := Y.presheaf.stalk (f x))
      (Q := X.presheaf.stalk x) (g := g)
      (hT.symm ▸ p.asIdeal.primeCompl.le_comap_map) s).trans
      (f.germ_stalkMap_apply U x hxU s).symm
  rw [f.ker.stalk_eq_map ⟨U, hU⟩ hxU, f.ker_apply]
  exact (IsLocalization.ker_map (S := Y.presheaf.stalk (f x))
    (X.presheaf.stalk x) g hT).symm.trans (congrArg RingHom.ker hmap)

end AlgebraicGeometry.Scheme.Hom
