/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Gluing representatives of one rational unit along the whole boundary

The representatives have the same native generic-point germ. Their union is
retained, rather than replaced by an unrelated generic neighborhood. The
boundary morphism has arbitrary source, including nonreduced schemes, and the
boundary equation is an equality of actual sections, not of residue values.


Intended upstream module: `Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.RationalUnitGluing`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme

/-- Unit representatives of the same rational function glue on their actual union.
The original boundary morphism factors through this union, and its pullback of
the glued section is literally one on the original, possibly nonreduced source.
Nonemptiness of the union is explicit, as required by the native rational germ. -/
theorem exists_rationalUnit_boundary_gluing
    {X D : Scheme.{u}} [IsIntegral X] (d : D ⟶ X)
    {ι : Type v} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    [Nonempty (iSup U : X.Opens)] (R : X.functionField)
    (s : ∀ i, Γ(X, U i)) (hs : ∀ i, IsUnit (s i))
    (hR : ∀ i, X.germToFunctionField (U i) (s i) = R)
    (hd : ∀ i, d.app (U i) (s i) = 1)
    (hcover : Set.range d ⊆ ((iSup U : X.Opens) : Set X)) :
    ∃ (f : Γ(X, iSup U)) (e : D ⟶ (iSup U).toScheme),
      e ≫ (iSup U).ι = d ∧ IsUnit f ∧
      X.germToFunctionField (iSup U) f = R ∧
      (∀ i, X.presheaf.map (Opens.leSupr U i).op f = s i) ∧
      d.app (iSup U) f = 1 := by
  have hgeneric (i : ι) : genericPoint X ∈ U i :=
    ((genericPoint_spec X).mem_open_set_iff (U i).isOpen).mpr
      (by simpa using (inferInstance : Nonempty (U i)))
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U s := by
    intro i j
    have : Nonempty (U i ⊓ U j : X.Opens) := ⟨⟨genericPoint X, hgeneric i, hgeneric j⟩⟩
    apply X.germToFunctionField_injective (U i ⊓ U j)
    change X.presheaf.germ _ _ _ (X.presheaf.map _ (s i)) =
      X.presheaf.germ _ _ _ (X.presheaf.map _ (s j))
    rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]
    exact (hR i).trans (hR j).symm
  obtain ⟨f, hf, -⟩ : ∃! f : Γ(X, iSup U),
      ∀ i, X.presheaf.map (Opens.leSupr U i).op f = s i :=
    X.sheaf.existsUnique_gluing U s hcompat
  have hunit : IsUnit f := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    have h := (hs i).map (X.presheaf.germ (U i) x hi).hom
    rw [← hf i] at h
    change IsUnit (X.presheaf.germ (U i) x hi
      (X.presheaf.map (Opens.leSupr U i).op f)) at h
    exact (X.presheaf.germ_res_apply (Opens.leSupr U i) x hi f) ▸ h
  have hrat : X.germToFunctionField (iSup U) f = R := by
    obtain ⟨x, hx⟩ := (inferInstance : Nonempty (iSup U : X.Opens))
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    have h := hR i
    rw [← hf i] at h
    change X.presheaf.germ _ _ _ (X.presheaf.map _ f) = R at h
    exact (X.presheaf.germ_res_apply (Opens.leSupr U i)
      (genericPoint X) (hgeneric i) f).symm.trans h
  have hboundary : d.app (iSup U) f = 1 := by
    apply D.sheaf.eq_of_locally_eq' (fun i => d ⁻¹ᵁ U i) (d ⁻¹ᵁ iSup U)
      (fun i => (Opens.map d.base).map (Opens.leSupr U i))
      (by rw [d.preimage_iSup])
    intro i
    have hn := ConcreteCategory.congr_hom (d.naturality (Opens.leSupr U i).op) f
    change d.app (U i) (X.presheaf.map (Opens.leSupr U i).op f) =
      D.presheaf.map ((Opens.map d.base).map (Opens.leSupr U i)).op
        (d.app (iSup U) f) at hn
    rw [hf i, hd i] at hn
    change D.presheaf.map ((Opens.map d.base).map (Opens.leSupr U i)).op
        (d.app (iSup U) f) =
      D.presheaf.map ((Opens.map d.base).map (Opens.leSupr U i)).op 1
    simpa only [map_one] using hn.symm
  have hfactor : Set.range d ⊆ Set.range (iSup U).ι := by
    simpa only [Opens.range_ι] using hcover
  exact ⟨f, IsOpenImmersion.lift (iSup U).ι d hfactor,
    IsOpenImmersion.lift_fac _ _ hfactor, hunit, hrat, hf, hboundary⟩

end AlgebraicGeometry.Scheme
