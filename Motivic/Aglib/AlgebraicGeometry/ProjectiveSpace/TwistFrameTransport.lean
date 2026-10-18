/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting.Frames

/-! # Exact open-equality transport of original twisting frames -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.ProjectiveSpace
universe u
variable (R : Type u) [CommRing R] (ι : Type u)

/-- Frame coefficients commute with the actual presheaf transport along equal opens. -/
theorem twistingSectionsEquiv_eqToHom_opens (n : ℤ) (i : ι)
    {V W : (ProjectiveSpace R ι).Opens} (h : V = W) (hi : W ≤ coordinateOpen R ι i)
    (s : Γ(twistingSheaf R ι n, W)) :
    twistingSectionsEquiv R ι n i (h.le.trans hi)
      ((twistingSheaf R ι n).val.map (eqToHom h).op s) =
      sectionRestrict (ProjectiveSpace R ι) h.le (twistingSectionsEquiv R ι n i hi s) :=
  twistingSectionsEquiv_restrict R ι n i h.le hi s

end AlgebraicGeometry.ProjectiveSpace
