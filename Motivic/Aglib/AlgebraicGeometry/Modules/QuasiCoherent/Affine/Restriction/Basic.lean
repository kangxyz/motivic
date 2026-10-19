/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeBaseChange.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Tilde modules on actual affine opens and their restrictions

The canonical affine chart isomorphisms commute with the original section
restriction map. This geometric square transports the canonical tilde/open
comparison to actual nested affine opens of a scheme. No chart transition
isomorphism is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine.OpenTilde

variable {X : Scheme.{u}} {U V : X.affineOpens}

/-- The actual affine chart square for an inclusion of two affine opens. -/
theorem isoSpec_restriction_square (h : U ≤ V) :
    U.2.isoSpec.hom ≫ Spec.map (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op) =
      X.homOfLE h ≫ V.2.isoSpec.hom :=
  Scheme.Opens.toSpecΓ_SpecMap_presheaf_map U.1 V.1 h

/-- The spectrum of the actual affine restriction is the original open inclusion in charts. -/
theorem specMap_restriction_eq (h : U ≤ V) :
    Spec.map (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op) =
      U.2.isoSpec.inv ≫ X.homOfLE h ≫ V.2.isoSpec.hom := by
  rw [← isoSpec_restriction_square h, Iso.inv_hom_id_assoc]

/-- The actual section restriction defines an open immersion on spectra. -/
instance isOpenImmersion_specMap_restriction (h : U ≤ V) :
    IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op)) := by
  rw [specMap_restriction_eq h]
  infer_instance

/-- Tilde transported to the actual affine open rather than an abstract spectrum. -/
def chartTilde (U : X.affineOpens) : ModuleCat.{u} Γ(X, U) ⥤ U.1.toScheme.Modules :=
  tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom

/-- The actual geometric comparison between the two affine-chart restriction routes. -/
def chartRestrictionSquareIso (h : U ≤ V) :
    letI := isOpenImmersion_specMap_restriction (U := U) (V := V) h
    Scheme.Modules.restrictFunctor V.2.isoSpec.hom ⋙
        Scheme.Modules.restrictFunctor (X.homOfLE h) ≅
      Scheme.Modules.restrictFunctor
        (Spec.map (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op)) ⋙
          Scheme.Modules.restrictFunctor U.2.isoSpec.hom := by
  letI := isOpenImmersion_specMap_restriction (U := U) (V := V) h
  exact (Scheme.Modules.restrictFunctorComp (X.homOfLE h) V.2.isoSpec.hom).symm ≪≫
    Scheme.Modules.restrictFunctorCongr (isoSpec_restriction_square h).symm ≪≫
      Scheme.Modules.restrictFunctorComp U.2.isoSpec.hom _

/-- Restriction on actual affine opens is canonically scalar extension followed by tilde. -/
def restrictionIso (h : U ≤ V) :
    chartTilde V ⋙ Scheme.Modules.restrictFunctor (X.homOfLE h) ≅
      ModuleCat.extendScalars
        (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom ⋙ chartTilde U := by
  letI := isOpenImmersion_specMap_restriction (U := U) (V := V) h
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tilde.functor Γ(X, V)) (chartRestrictionSquareIso h) ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (TildeBaseChange.restrictionIso
            (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op))
          (Scheme.Modules.restrictFunctor U.2.isoSpec.hom) ≪≫
            Functor.associator _ _ _

/-- The actual affine-open comparison is natural in every module morphism. -/
@[reassoc] theorem restrictionIso_naturality (h : U ≤ V)
    {M N : ModuleCat.{u} Γ(X, V)} (f : M ⟶ N) :
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).map ((chartTilde V).map f) ≫
        (restrictionIso h).hom.app N =
      (restrictionIso h).hom.app M ≫
        (chartTilde U).map
          ((ModuleCat.extendScalars
            (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom).map f) :=
  (restrictionIso h).hom.naturality f

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine.OpenTilde
