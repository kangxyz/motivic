/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Divisors.Order.PrincipalOrderCancellation
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyLocalFraction
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.Invariance

/-!
# Native orders under an original open immersion

The generic-point field map and the original open-stalk isomorphism transport
one prescribed affine fraction. The proof preserves the actual principal
quotient lengths and explicitly handles zero and other codimensions.


Intended upstream module: `Aglib.AlgebraicGeometry.Divisors.Order.OpenImmersion`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyChartSpecialization`,
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.GenericRatioChartCycle`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Order

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] functionField_openImmersion_dominant
  functionField_nonempty_preimage

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (i : X ⟶ Y) [IsOpenImmersion i]

omit [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] in
private theorem open_stalk_quotient_length (x : X) (r : Y.presheaf.stalk (i x)) :
    Module.length (Y.presheaf.stalk (i x))
        ((Y.presheaf.stalk (i x)) ⧸ Ideal.span {r}) =
      Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {i.stalkMap x r}) := by
  let e := (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv
  let I : Ideal (Y.presheaf.stalk (i x)) := Ideal.span {r}
  let J : Ideal (X.presheaf.stalk x) := Ideal.span {e r}
  let E := Ideal.quotientEquiv I J e (by simp [I, J, Ideal.map_span])
  exact (Module.length_eq_of_surjective (Ideal.Quotient.mk_surjective (I := I))).trans
    ((_root_.AlgebraicGeometry.Scheme.ringLength_eq_of_ringEquiv E).trans
      (Module.length_eq_of_surjective (Ideal.Quotient.mk_surjective (I := J))).symm)

private theorem ord_functionFieldMap_germ
    (U : Y.Opens) [Nonempty U] (s : Γ(Y, U)) (hs : s ≠ 0)
    (x : X) (hxU : i x ∈ U) (hx : coheight x = 1) :
    X.ord (functionFieldMap i (Y.germToFunctionField U s)) x =
      Y.ord (Y.germToFunctionField U s) (i x) := by
  have hy : coheight (i x) = 1 := (coheight_eq_of_isOpenImmersion i).trans hx
  have hnat := ConcreteCategory.congr_hom (functionFieldMap_germ_open i U) s
  change functionFieldMap i (Y.germToFunctionField U s) =
    X.germToFunctionField (i ⁻¹ᵁ U) (i.app U s) at hnat
  have hg : Y.presheaf.germ U (i x) hxU s ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral Y (i x) hxU)).mpr hs
  have hg' : X.presheaf.germ (i ⁻¹ᵁ U) x hxU (i.app U s) ≠ 0 := by
    rw [← i.germ_stalkMap_apply U x hxU s]
    exact (map_ne_zero_iff _ (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv.injective).mpr hg
  have hs' : i.app U s ≠ 0 := fun h => hg' (by rw [h, map_zero])
  rw [hnat, X.ord_germ_eq_quotient_length _ _ hs' hxU hx,
    Y.ord_germ_eq_quotient_length _ _ hs hxU hy]
  have hl := open_stalk_quotient_length i x (Y.presheaf.germ U (i x) hxU s)
  rw [i.germ_stalkMap_apply U x hxU s] at hl
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) hl.symm

/-- Orders of the same native rational function agree along an open immersion.
Dominance is derived from the integral open immersion, and no chart comparison
or quotient-length equality is supplied. -/
theorem ord_functionFieldMap_of_isOpenImmersion (r : Y.functionField) (x : X) :
    X.ord (functionFieldMap i r) x = Y.ord r (i x) := by
  by_cases hr : r = 0
  · simp [hr]
  by_cases hx : coheight x = 1
  · obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open
        (TopologicalSpace.Opens.mem_top (i x)) (⊤ : Y.Opens).isOpen
    let : Nonempty U := ⟨⟨i x, hxU⟩⟩
    obtain ⟨a, b, hn, hab⟩ := Y.exists_nonzero_affine_fraction U hU r hr
    have ha : a ≠ 0 := fun h => (hn (i x) hxU).1 (by rw [h, map_zero])
    have hb : b ≠ 0 := fun h => (hn (i x) hxU).2 (by rw [h, map_zero])
    have ha' := (map_ne_zero_iff _ (Y.germToFunctionField_injective U)).mpr ha
    have hb' := (map_ne_zero_iff _ (Y.germToFunctionField_injective U)).mpr hb
    have hia := (map_ne_zero_iff _ (functionFieldMap_injective i)).mpr ha'
    have hib := (map_ne_zero_iff _ (functionFieldMap_injective i)).mpr hb'
    have hY := Y.ord_add_ord_ratio _ _ hb' ha' (i x)
    have hX := X.ord_add_ord_ratio _ _ hib hia x
    rw [ord_functionFieldMap_germ i U b hb x hxU hx,
      ord_functionFieldMap_germ i U a ha x hxU hx, ← map_div₀, hab] at hX
    rw [hab] at hY
    omega
  · have hy : coheight (i x) ≠ 1 := by
      simpa only [coheight_eq_of_isOpenImmersion i] using hx
    rw [ord_eq_zero_of_coheight_neq_one hx, ord_eq_zero_of_coheight_neq_one hy]

end AlgebraicGeometry.Scheme
