/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PresheafBoundaryEtaleExcision
public import Motivic.Cohomology.A1.PresheafBoundarySheafComparison

/-! # The actual ambient boundary restricts to zero on the open

This coefficient-only argument uses the identity pair after actual étale
localization. It is independent of positive cohomology and marked-point fibers.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.FiniteEtaleSite

section Presheaf

variable {B : Scheme.{u}} (P : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- Restriction for the identity pair is the actual pullback projection isomorphism. -/
theorem presheafBoundaryRestriction_id_isIso (U : SmoothSite B) :
    IsIso (presheafBoundaryRestriction P (𝟙 U)) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro V
  let a := (restrictionProjection (𝟙 U)).app V.unop
  let : IsIso ((SmoothSite.forgetScheme B).map a) :=
    inferInstanceAs (IsIso (pullback.fst V.unop.hom (𝟙 (U.left))))
  let : IsIso a := isIso_of_reflects_iso a (SmoothSite.forgetScheme B)
  change IsIso (P.map a.op)
  infer_instance

/-- The original quotient and its small sheafification both vanish for the identity pair. -/
theorem presheafBoundaryAmbient_id_isZero (U : SmoothSite B) :
    IsZero (presheafBoundaryAmbient P (𝟙 U)) := by
  let := presheafBoundaryRestriction_id_isIso P U
  exact (presheafToSheaf (nisnevichTopology U.left) AddCommGrpCat.{u + 1}).map_isZero
    (isZero_cokernel_of_epi (presheafBoundaryRestriction P (𝟙 U)))

variable {U Y : SmoothSite B} (j : U ⟶ Y) [IsOpenImmersion j.left]
  [QuasiCompact j.left]

/-- The genuine inverse image to the actual open complement of the boundary is zero. -/
theorem inverseImage_open_presheafBoundaryAmbient_isZero :
    IsZero ((inverseImage j.left).obj (presheafBoundaryAmbient P j)) := by
  let : Mono j := (SmoothSite.forgetScheme B).mono_of_mono_map
    (inferInstanceAs (Mono j.left))
  have hpb : IsPullback (𝟙 U) (𝟙 U) j j :=
    IsPullback.of_vert_isIso_mono ⟨by simp only [Category.id_comp]⟩
  exact (presheafBoundaryAmbient_id_isZero P U).of_iso
    ((inverseImageEtaleIso j.left).app (presheafBoundaryAmbient P j) ≪≫
      presheafBoundaryAmbientEtaleIso P j j (𝟙 U) (𝟙 U) hpb)

end Presheaf

section Sheaf

variable {B : Scheme.{u}}
  (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
  {U Y : SmoothSite B} (j : U ⟶ Y) [IsOpenImmersion j.left] [QuasiCompact j.left]

/-- For a genuine coefficient sheaf, the actual ambient sheaf cokernel also
vanishes on the open. The existing comparison preserves its original projection. -/
theorem inverseImage_open_boundaryAmbientCokernel_isZero :
    IsZero ((inverseImage j.left).obj (boundaryAmbientCokernel F j)) :=
  (inverseImage_open_presheafBoundaryAmbient_isZero F.obj j).of_iso
    ((inverseImage j.left).mapIso (presheafBoundaryAmbientSheafIso F j)).symm

end Sheaf

end Motivic.FiniteEtaleSite
