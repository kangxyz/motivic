/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Gluing.TwoOpenCover.Transition
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Signed overlap and refinement consumers of actual module-sheaf gluing

Two principal affine opens D(r) and D(1-r) cover the actual affine spectrum.
A signed, structure-sheaf-linear transition glues actual quotient tilde modules.
Both local inverses, the supplied transition equation and further open
refinements are consumed. No global glued coefficient object is an input.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.OpenCoverGluing

open Scheme.Modules _root_.AlgebraicGeometry.Scheme.Modules.Gluing.TwoOpenCover

/-- Negation is an actual structure-sheaf-linear automorphism. -/
def negationIso {X : Scheme.{u}} (M : X.Modules) : M ≅ M where
  hom := -𝟙 M
  inv := -𝟙 M
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- On every actual section, the chosen transition has its literal sign. -/
theorem negationIso_hom_apply {X : Scheme.{u}} (M : X.Modules) (W : X.Opens)
    (m : Γ(M, W)) : ((negationIso M).hom.app W) m = -m := rfl

/-- Negation is genuinely nonidentity whenever an actual section detects its sign. -/
theorem negationIso_hom_ne_id {X : Scheme.{u}} (M : X.Modules) (W : X.Opens)
    (m : Γ(M, W)) (hm : -m ≠ m) : (negationIso M).hom ≠ 𝟙 M := by
  intro h
  have := congrArg (fun φ : M ⟶ M => φ.app W m) h
  exact hm this

/-- A concrete rank-one module on the rational affine point. -/
abbrev rationalModule : (Spec (CommRingCat.of ℚ)).Modules :=
  SheafOfModules.unit (Spec (CommRingCat.of ℚ)).ringCatSheaf

set_option backward.isDefEq.respectTransparency false in
/-- The actual section one detects that negation is not the identity. -/
theorem rational_negation_ne_id : (negationIso rationalModule).hom ≠ 𝟙 rationalModule := by
  apply negationIso_hom_ne_id rationalModule ⊤ (1 : Γ(Spec (CommRingCat.of ℚ), ⊤))
  intro h
  change (-(1 : Γ(Spec (CommRingCat.of ℚ), ⊤))) = 1 at h
  have hh := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℚ)).hom.hom h
  rw [map_neg, map_one] at hh
  norm_num at hh

/-- A concrete signed transition on the overlapping affine identity cover. -/
def rationalTransition :
    (restrictFunctor (𝟙 (Spec (CommRingCat.of ℚ)))).obj rationalModule ≅
      (restrictFunctor (𝟙 (Spec (CommRingCat.of ℚ)))).obj rationalModule :=
  negationIso _

/-- The actual overlap transition is proved nonidentity on this affine cover. -/
theorem rationalTransition_ne_id : (rationalTransition).hom ≠ 𝟙 _ := by
  intro h
  apply rational_negation_ne_id
  have hh := congrArg (fun φ => (restrictFunctorId.app rationalModule).inv ≫ φ ≫
    (restrictFunctorId.app rationalModule).hom) h
  simpa [rationalTransition, negationIso] using hh

/-- A genuine glued object for the computed nonidentity rational transition. -/
def rationalGlued : (Spec (CommRingCat.of ℚ)).Modules :=
  glued (IsPullback.id_horiz (𝟙 (Spec (CommRingCat.of ℚ))))
    rationalModule rationalModule rationalTransition

/-- The same constructed rational object realizes the nonidentity transition. -/
theorem rational_glued_transition :
    (restrictFunctor (𝟙 (Spec (CommRingCat.of ℚ)))).map
        (gluedRestrictLeftIso (IsPullback.id_horiz (𝟙 (Spec (CommRingCat.of ℚ))))
          rationalModule rationalModule rationalTransition).hom ≫ rationalTransition.hom =
      (overlapRestrictionIso (IsPullback.id_horiz (𝟙 (Spec (CommRingCat.of ℚ))))).hom.app
          rationalGlued ≫
        (restrictFunctor (𝟙 (Spec (CommRingCat.of ℚ)))).map
          (gluedRestrictRightIso (IsPullback.id_horiz (𝟙 (Spec (CommRingCat.of ℚ))))
            rationalModule rationalModule rationalTransition).hom :=
  glued_transition _ _ _ _

variable (R : CommRingCat.{u}) (I : Ideal R) (r : R)

/-- The first genuine affine open. -/
abbrev firstOpen : (Spec R).Opens := PrimeSpectrum.basicOpen r

/-- The second genuine affine open. -/
abbrev secondOpen : (Spec R).Opens := PrimeSpectrum.basicOpen (1 - r)

/-- These two genuine principal opens cover the entire affine spectrum. -/
theorem principal_cover : firstOpen R r ⊔ secondOpen R r = ⊤ := by
  apply top_unique
  intro p _
  change r ∉ p.asIdeal ∨ 1 - r ∉ p.asIdeal
  by_contra h
  push Not at h
  have h₁ : r ∈ p.asIdeal := h.1
  have h₂ : 1 - r ∈ p.asIdeal := h.2
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _
    (by simpa using p.asIdeal.add_mem h₁ h₂) isUnit_one)

/-- Both members of the actual cover are affine. -/
theorem principal_affine : IsAffineOpen (firstOpen R r) ∧ IsAffineOpen (secondOpen R r) :=
  ⟨IsAffineOpen.Spec_basicOpen r, IsAffineOpen.Spec_basicOpen (1 - r)⟩

/-- The actual global quotient tilde module used to supply the local modules. -/
abbrev quotientModule : (Spec R).Modules := tilde (ModuleCat.of R (R ⧸ I))

/-- The first actual local module, retaining its quotient action. -/
abbrev firstModule := (restrictFunctor (firstOpen R r).ι).obj (quotientModule R I)

/-- The second actual local module. -/
abbrev secondModule := (restrictFunctor (secondOpen R r).ι).obj (quotientModule R I)

/-- The specified transition is the negative of the canonical overlap identification. -/
def signedTransition :
    (restrictFunctor ((Spec R).homOfLE (inf_le_left :
      firstOpen R r ⊓ secondOpen R r ≤ firstOpen R r))).obj (firstModule R I r) ≅
    (restrictFunctor ((Spec R).homOfLE (inf_le_right :
      firstOpen R r ⊓ secondOpen R r ≤ secondOpen R r))).obj (secondModule R I r) :=
  (overlapRestrictionIso (isPullback_opens_inf (firstOpen R r) (secondOpen R r))).app
      (quotientModule R I) ≪≫ negationIso _

/-- The transition contains the literal sign, not an assumed compatibility equivalence. -/
theorem signedTransition_hom : (signedTransition R I r).hom =
    -((overlapRestrictionIso (isPullback_opens_inf (firstOpen R r)
      (secondOpen R r))).app (quotientModule R I)).hom := by
  simp [signedTransition, negationIso]

/-- The genuine module sheaf constructed from the signed local quotient data. -/
def signedGlued : (Spec R).Modules :=
  glued (isPullback_opens_inf (firstOpen R r) (secondOpen R r))
    (firstModule R I r) (secondModule R I r) (signedTransition R I r)

/-- The first actual restriction isomorphism of the constructed signed sheaf. -/
def signedLeftIso : (restrictFunctor (firstOpen R r).ι).obj (signedGlued R I r) ≅
    firstModule R I r :=
  gluedRestrictLeftIso _ _ _ _

/-- The second actual restriction isomorphism. -/
def signedRightIso : (restrictFunctor (secondOpen R r).ι).obj (signedGlued R I r) ≅
    secondModule R I r :=
  gluedRestrictRightIso _ _ _ _

/-- The constructed local isomorphisms realize exactly the prescribed signed transition. -/
theorem signed_transition :
    (restrictFunctor ((Spec R).homOfLE inf_le_left)).map (signedLeftIso R I r).hom ≫
        (signedTransition R I r).hom =
      (overlapRestrictionIso (isPullback_opens_inf (firstOpen R r)
        (secondOpen R r))).hom.app (signedGlued R I r) ≫
          (restrictFunctor ((Spec R).homOfLE inf_le_right)).map (signedRightIso R I r).hom :=
  glued_transition _ _ _ _

/-- Every genuine smaller open in the first member inherits the actual restriction inverse. -/
def signedRefinementIso {W : (Spec R).Opens} (hW : W ≤ firstOpen R r) :
    (restrictFunctor ((Spec R).homOfLE hW ≫ (firstOpen R r).ι)).obj (signedGlued R I r) ≅
      (restrictFunctor ((Spec R).homOfLE hW)).obj (firstModule R I r) :=
  gluedRestrictLeftRefinementIso _ _ _ _ ((Spec R).homOfLE hW)

end Motivic.MotivicTest.OpenCoverGluing
