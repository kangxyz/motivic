/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Ideals in the actual stalks of a scheme

The stalk of ideal-sheaf data is the extension of its ideal on an affine
neighborhood along the germ homomorphism. The construction is independent of
the affine neighborhood and uses the actual structure-sheaf stalk ring.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The extensions from any two affine neighborhoods to the actual stalk agree. -/
theorem map_germ_eq {U V : X.affineOpens} {x : X}
    (hxU : x ∈ U.1) (hxV : x ∈ V.1) :
    (I.ideal U).map (X.presheaf.germ U.1 x hxU).hom =
      (I.ideal V).map (X.presheaf.germ V.1 x hxV).hom := by
  obtain ⟨W, hW, hxW, hWU : W ≤ U.1 ⊓ V.1⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ U.1 ⊓ V.1 from ⟨hxU, hxV⟩)
  have h₁ := I.map_ideal (U := ⟨W, hW⟩) (V := U) (hWU.trans inf_le_left)
  have h₂ := I.map_ideal (U := ⟨W, hW⟩) (V := V) (hWU.trans inf_le_right)
  have h := congrArg (fun J : Ideal Γ(X, W) =>
    J.map (X.presheaf.germ W x hxW).hom) (h₁.trans h₂.symm)
  simpa only [Ideal.map_map, ← CommRingCat.hom_comp, X.presheaf.germ_res,
    homOfLE_leOfHom, TopCat.Presheaf.germ_res'] using h

/-- The ideal in the actual stalk ring defined by ideal-sheaf data. -/
noncomputable def stalk (x : X) : Ideal (X.presheaf.stalk x) :=
  (I.ideal ⟨(X.affineCover.f (X.affineCover.idx x)).opensRange,
    isAffineOpen_opensRange _⟩).map
    (X.presheaf.germ _ x (X.affineCover.covers x)).hom

/-- Every affine neighborhood computes the stalk ideal by localization. -/
theorem stalk_eq_map (U : X.affineOpens) {x : X} (hx : x ∈ U.1) :
    I.stalk x = (I.ideal U).map (X.presheaf.germ U.1 x hx).hom :=
  I.map_germ_eq _ hx

/-- Stalk ideals respect transport between equal points. -/
theorem stalk_congr {x y : X} (h : x = y) :
    (I.stalk x).map (X.presheaf.stalkCongr (.of_eq h)).hom.hom = I.stalk y := by
  subst y
  simp [TopCat.Presheaf.stalkCongr]

/-- Pulling back along the equality isomorphism transports the stalk ideal. -/
theorem stalk_congr_comap {x y : X} (h : x = y) :
    (I.stalk y).comap (X.presheaf.stalkCongr (.of_eq h)).hom.hom = I.stalk x := by
  subst y
  simp [TopCat.Presheaf.stalkCongr]

/-- Formation of stalk ideals is monotone. -/
theorem stalk_mono {I J : X.IdealSheafData} (h : I ≤ J) (x : X) :
    I.stalk x ≤ J.stalk x :=
  Ideal.map_mono (h _)

@[simp]
theorem stalk_bot (x : X) : (⊥ : X.IdealSheafData).stalk x = ⊥ := by
  simp [stalk]

@[simp]
theorem stalk_top (x : X) : (⊤ : X.IdealSheafData).stalk x = ⊤ := by
  simp [stalk, Ideal.map_top]

/-- Sums of ideal sheaves give literal sums of ideals in the local ring. -/
@[simp]
theorem stalk_sup (J : X.IdealSheafData) (x : X) :
    (I ⊔ J).stalk x = I.stalk x ⊔ J.stalk x := by
  simp [stalk, Ideal.map_sup]

@[simp]
theorem stalk_iSup {ι : Type*} (I : ι → X.IdealSheafData) (x : X) :
    (⨆ i, I i).stalk x = ⨆ i, (I i).stalk x := by
  simp [stalk, Ideal.map_iSup]

/-- A section belonging to the affine ideal has germ in the stalk ideal. -/
theorem germ_mem_stalk (U : X.affineOpens) {x : X} (hx : x ∈ U.1)
    {s : Γ(X, U)} (hs : s ∈ I.ideal U) :
    X.presheaf.germ U.1 x hx s ∈ I.stalk x := by
  rw [I.stalk_eq_map U hx]
  exact Ideal.mem_map_of_mem _ hs

/-- Ideal-sheaf data can be compared on the actual local rings. -/
theorem le_iff_stalk_le {I J : X.IdealSheafData} :
    I ≤ J ↔ ∀ x, I.stalk x ≤ J.stalk x := by
  refine ⟨fun h x => stalk_mono h x, fun h U => U.2.ideal_le_iff.mpr ?_⟩
  intro x hx
  simpa only [I.stalk_eq_map U hx, J.stalk_eq_map U hx] using h x

/-- Equality of the actual stalk ideals detects equality of ideal-sheaf data. -/
theorem ext_stalk {I J : X.IdealSheafData} (h : ∀ x, I.stalk x = J.stalk x) : I = J :=
  (le_iff_stalk_le.mpr fun x => (h x).le).antisymm
    (le_iff_stalk_le.mpr fun x => (h x).ge)

end AlgebraicGeometry.Scheme.IdealSheafData
