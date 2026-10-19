/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Graph.StalkTransport

/-!
# Transport of a common regular stalk equation list

A regular list generating one actual stalk kernel can simultaneously be
transported with regularity of its literal images in a second stalk. The
commuting squares and ring equivalences are explicit. The geometric version
uses the actual stalk maps of open charts, with all point identifications
recorded by stalk congruences. It does not infer regularity from an arbitrary
base change or from the mere existence of a second regular generating list.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace AlgebraicGeometry.Scheme.Graph

set_option backward.isDefEq.respectTransparency false in
/-- Two commuting ring squares transport one common kernel-generating and image-regular list. -/
theorem exists_regular_kernel_and_regular_image_of_ringEquivs
    {R D T R' D' T' : Type*}
    [CommRing R] [CommRing D] [CommRing T] [CommRing R'] [CommRing D'] [CommRing T']
    (i : R →+* D) (q : R →+* T) (i' : R' →+* D') (q' : R' →+* T')
    (eR : R ≃+* R') (eD : D ≃+* D') (eT : T ≃+* T')
    (hi : ∀ r, eD (i r) = i' (eR r)) (hq : ∀ r, eT (q r) = q' (eR r))
    (h : ∃ rs : List R', IsRegular R' rs ∧ RingHom.ker i' = Ideal.ofList rs ∧
      IsRegular T' (rs.map q')) :
    ∃ rs : List R, IsRegular R rs ∧ RingHom.ker i = Ideal.ofList rs ∧
      IsRegular T (rs.map q) := by
  obtain ⟨rs, hrs, hker, hreg⟩ := h
  have hr : IsRegular R (rs.map eR.symm.toRingHom) := by
    let e := eR.symm
    let := RingHomInvPair.of_ringEquiv e
    let := RingHomInvPair.symm (e : R' →+* R) (e.symm : R →+* R')
    exact (e.toSemilinearEquiv.isRegular_congr' rs).mp hrs
  refine ⟨rs.map eR.symm.toRingHom, hr, ?_, ?_⟩
  · have hk : RingHom.ker i = (RingHom.ker i').comap eR := by
      ext r
      change i r = 0 ↔ i' (eR r) = 0
      rw [← hi]
      exact eD.map_eq_zero_iff.symm
    rw [hk, hker, ← Ideal.map_symm eR]
    change (Ideal.ofList rs).map eR.symm.toRingHom = Ideal.ofList (rs.map eR.symm.toRingHom)
    rw [Ideal.map_ofList]
  · have heq : (rs.map eR.symm.toRingHom).map q = (rs.map q').map eT.symm.toRingHom := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro r _
      change q (eR.symm r) = eT.symm (q' r)
      apply eT.injective
      rw [eT.apply_symm_apply, hq, eR.apply_symm_apply]
    rw [heq]
    let e := eT.symm
    let := RingHomInvPair.of_ringEquiv e
    let := RingHomInvPair.symm (e : T' →+* T) (e.symm : T →+* T')
    exact (e.toSemilinearEquiv.isRegular_congr' (rs.map q')).mp hreg

/-- The actual stalk map with its source point identified explicitly. -/
def alignedStalkMap {Q P : Scheme.{u}} (q : Q ⟶ P) (z : Q) (p : P) (h : p = q z) :
    P.presheaf.stalk p ⟶ Q.presheaf.stalk z :=
  (P.presheaf.stalkCongr (.of_eq h)).hom ≫ q.stalkMap z

@[simp]
theorem alignedStalkMap_rfl {Q P : Scheme.{u}} (q : Q ⟶ P) (z : Q) :
    alignedStalkMap q z (q z) rfl = q.stalkMap z := by
  simp [alignedStalkMap]

set_option backward.isDefEq.respectTransparency false in
/-- Actual aligned stalk maps commute with an actual chart square. -/
theorem alignedStalkMap_naturality
    {Q P Q' P' : Scheme.{u}} (q : Q ⟶ P) (q' : Q' ⟶ P')
    (iQ : Q' ⟶ Q) (iP : P' ⟶ P) (hc : q' ≫ iP = iQ ≫ q)
    (z : Q') (p : P') (h' : p = q' z) (h : iP p = q (iQ z)) :
    alignedStalkMap q (iQ z) (iP p) h ≫ iQ.stalkMap z =
      iP.stalkMap p ≫ alignedStalkMap q' z p h' := by
  subst p
  simp only [alignedStalkMap_rfl]
  simp only [alignedStalkMap, Category.assoc, ← Scheme.Hom.stalkMap_comp]
  exact (Scheme.Hom.stalkMap_congr_hom _ _ hc z).symm

/-- Open charts transport a regular kernel list and regularity of that same list's images. -/
theorem exists_regular_kernel_and_regular_image_of_openCharts
    {D Q P D' Q' P' : Scheme.{u}}
    (i : D ⟶ P) (q : Q ⟶ P) (i' : D' ⟶ P') (q' : Q' ⟶ P')
    (iD : D' ⟶ D) (iQ : Q' ⟶ Q) (iP : P' ⟶ P)
    [IsOpenImmersion iD] [IsOpenImmersion iQ] [IsOpenImmersion iP]
    (hi : i' ≫ iP = iD ≫ i) (hq : q' ≫ iP = iQ ≫ q)
    (d : D') (z : Q') (p : P') (hdi : p = i' d) (hzq : p = q' z)
    (hdi' : iP p = i (iD d)) (hzq' : iP p = q (iQ z))
    (h : ∃ rs : List (P'.presheaf.stalk p), IsRegular (P'.presheaf.stalk p) rs ∧
      RingHom.ker (alignedStalkMap i' d p hdi).hom = Ideal.ofList rs ∧
      IsRegular (Q'.presheaf.stalk z) (rs.map (alignedStalkMap q' z p hzq).hom)) :
    ∃ rs : List (P.presheaf.stalk (iP p)), IsRegular (P.presheaf.stalk (iP p)) rs ∧
      RingHom.ker (alignedStalkMap i (iD d) (iP p) hdi').hom = Ideal.ofList rs ∧
      IsRegular (Q.presheaf.stalk (iQ z))
        (rs.map (alignedStalkMap q (iQ z) (iP p) hzq').hom) := by
  apply exists_regular_kernel_and_regular_image_of_ringEquivs
    (alignedStalkMap i (iD d) (iP p) hdi').hom
    (alignedStalkMap q (iQ z) (iP p) hzq').hom
    (alignedStalkMap i' d p hdi).hom (alignedStalkMap q' z p hzq).hom
    (asIso (iP.stalkMap p)).commRingCatIsoToRingEquiv
    (asIso (iD.stalkMap d)).commRingCatIsoToRingEquiv
    (asIso (iQ.stalkMap z)).commRingCatIsoToRingEquiv
    (fun r => ConcreteCategory.congr_hom
      (alignedStalkMap_naturality i i' iD iP hi d p hdi hdi') r)
    (fun r => ConcreteCategory.congr_hom
      (alignedStalkMap_naturality q q' iQ iP hq z p hzq hzq') r) h

end AlgebraicGeometry.Scheme.Graph
