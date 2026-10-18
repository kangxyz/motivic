/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.PrescribedNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Prescribed frames in canonical affine coordinates

This adapter uses the actual global-section quotient of a closed immersion.
The boundary frame is transported only along the canonical affine isomorphisms;
its exact value, including nilpotent boundary data, is retained. The existing
principal-neighborhood producer performs the extension, not a new existence input.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]

/-- The specified frame in the canonical spectra of the original affine schemes. -/
def affineBoundaryFrame (z : Z ⟶ X) (L : LineBundle X)
    (e : (Modules.pullback z).obj L.val ≅ SheafOfModules.unit Z.ringCatSheaf) :
    (Modules.pullback (Spec.map z.appTop)).obj
        (pullbackLineBundle X.isoSpec.inv L).val ≅
      SheafOfModules.unit (Spec Γ(Z, ⊤)).ringCatSheaf :=
  (Modules.pullbackComp (Spec.map z.appTop) X.isoSpec.inv).app L.val ≪≫
    (Modules.pullbackCongr (Scheme.isoSpec_inv_naturality z)).app L.val ≪≫
    ((Modules.pullbackComp Z.isoSpec.inv z).app L.val).symm ≪≫
    (Modules.pullback Z.isoSpec.inv).mapIso e ≪≫ pullbackUnitIso Z.isoSpec.inv

/-- A genuine principal neighborhood carries the extension of the original
specified frame. The quotient and line are canonical, not supplied replacements. -/
theorem exists_affine_prescribed_principal_unitIso (z : Z ⟶ X) [IsClosedImmersion z]
    (L : LineBundle X)
    (e : (Modules.pullback z).obj L.val ≅ SheafOfModules.unit Z.ringCatSheaf) :
    letI : Algebra Γ(X, ⊤) Γ(Z, ⊤) := z.appTop.hom.toAlgebra
    ∃ (r : Γ(X, ⊤)), z.appTop r = 1 ∧
      ∃ (q : Spec Γ(Z, ⊤) ⟶ Spec (.of (Localization.Away r)))
        (hq : q ≫ Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, ⊤) (Localization.Away r))) = Spec.map z.appTop)
        (d : (Modules.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, ⊤) (Localization.Away r))))).obj
            (pullbackLineBundle X.isoSpec.inv L).val ≅
          SheafOfModules.unit (Spec (.of (Localization.Away r))).ringCatSheaf),
        ((Modules.pullbackCongr hq).app (pullbackLineBundle X.isoSpec.inv L).val).symm ≪≫
          ((Modules.pullbackComp q (Spec.map (CommRingCat.ofHom
            (algebraMap Γ(X, ⊤) (Localization.Away r))))).app
              (pullbackLineBundle X.isoSpec.inv L).val).symm ≪≫
          (Modules.pullback q).mapIso d ≪≫ pullbackUnitIso q = affineBoundaryFrame z L e := by
  letI : Algebra Γ(X, ⊤) Γ(Z, ⊤) := z.appTop.hom.toAlgebra
  have hz : Function.Surjective (algebraMap Γ(X, ⊤) Γ(Z, ⊤)) :=
    z.app_surjective ⊤ (isAffineOpen_top X)
  exact exists_prescribed_principal_unitIso Γ(X, ⊤) Γ(Z, ⊤) hz
    (pullbackLineBundle X.isoSpec.inv L) (affineBoundaryFrame z L e)

end AlgebraicGeometry.Scheme.Modules.Invertible
