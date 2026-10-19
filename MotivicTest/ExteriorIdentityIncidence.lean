/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Identity.Incidence
public import Motivic.Aglib.AlgebraicGeometry.Simplex.ExteriorGeometry

/-!
# Actual simplex exterior-incidence consumers

These consumers require no regularity, integrality or reducedness of the
original incidence scheme. Its complete scheme structure is transported.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ExteriorIdentityIncidence
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom) (n : ℕ)

example :
    pullback (A.incidenceSource B ≫ X.hom) (_root_.AlgebraicSimplex.smoothSiteObj k n).hom ≅
      (A.exteriorIdentityGenerator (_root_.AlgebraicSimplex.smoothSiteObj k n)).incidence
        (B.exteriorIdentityGenerator (_root_.AlgebraicSimplex.smoothSiteObj k n)) :=
  A.exteriorIdentityIncidenceIso B _

example (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom] :
    IsPullback
      (A.exteriorIncidenceFirst B T ≫ (A.exteriorIdentitySchemeIso T).hom)
      (A.exteriorIncidenceSecond B T ≫ (B.exteriorIdentitySchemeIso T).hom)
      (A.exteriorIdentityGenerator T).targetProjection
      (B.exteriorIdentityGenerator T).projection :=
  A.exteriorIdentityIncidence_isPullback B T

example (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom] :
    (A.exteriorIdentityIncidenceIso B T).hom ≫
      (A.exteriorIdentityGenerator T).incidenceSource (B.exteriorIdentityGenerator T) ≫
        pullback.fst X.hom T.hom =
      pullback.fst (A.incidenceSource B ≫ X.hom) T.hom ≫ A.incidenceSource B :=
  A.exteriorIdentityIncidenceIso_hom_source_fst B T

example (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom] :
    (A.exteriorIdentityIncidenceIso B T).hom ≫
      (A.exteriorIdentityGenerator T).incidenceTarget (B.exteriorIdentityGenerator T) ≫
        pullback.snd Z.hom T.hom =
      pullback.snd (A.incidenceSource B ≫ X.hom) T.hom :=
  A.exteriorIdentityIncidenceIso_hom_target_snd B T

end MotivicTest.ExteriorIdentityIncidence
