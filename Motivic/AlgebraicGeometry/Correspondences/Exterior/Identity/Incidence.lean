/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Simplex.GraphInterchangeGeometry

/-!
# Full incidence after adjoining an identity parameter

The incidence of two actual exterior generators is the product of the full
original incidence scheme with the parameter. The comparison retains the
complete scheme structure, including all nilpotents and all components.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k)))

/-- The full original incidence with its independent parameter. -/
abbrev exteriorIncidenceSupport := pullback (A.incidenceSource B ≫ X.hom) T.hom

/-- The first support coordinate and the common parameter. -/
def exteriorIncidenceFirst : A.exteriorIncidenceSupport B T ⟶ A.exteriorIdentitySupport T :=
  pullback.lift
    (pullback.fst (A.incidenceSource B ≫ X.hom) T.hom ≫ A.incidenceFst B)
    (pullback.snd (A.incidenceSource B ≫ X.hom) T.hom)
    (by simpa only [Category.assoc, incidenceSource] using
      (pullback.condition (f := A.incidenceSource B ≫ X.hom) (g := T.hom)))

/-- The second support coordinate and that same parameter. -/
def exteriorIncidenceSecond : A.exteriorIncidenceSupport B T ⟶ B.exteriorIdentitySupport T :=
  pullback.lift
    (pullback.fst (A.incidenceSource B ≫ X.hom) T.hom ≫ A.incidenceSnd B)
    (pullback.snd (A.incidenceSource B ≫ X.hom) T.hom) (by
      have hbase : A.incidenceFst B ≫ (A.projection ≫ X.hom) =
          A.incidenceSnd B ≫ (B.projection ≫ Y.hom) := by
        calc
          _ = A.incidenceFst B ≫ (A.targetProjection ≫ Y.hom) :=
            congrArg (A.incidenceFst B ≫ ·) A.projection_base
          _ = _ := by
            simpa only [Category.assoc] using
              congrArg (fun f => f ≫ Y.hom) (A.incidence_condition B)
      rw [Category.assoc, ← hbase]
      simpa only [Category.assoc, incidenceSource] using
        (pullback.condition (f := A.incidenceSource B ≫ X.hom) (g := T.hom)))

@[reassoc (attr := simp)]
theorem exteriorIncidenceFirst_fst :
    A.exteriorIncidenceFirst B T ≫ pullback.fst (A.projection ≫ X.hom) T.hom =
      pullback.fst (A.incidenceSource B ≫ X.hom) T.hom ≫ A.incidenceFst B :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorIncidenceFirst_snd :
    A.exteriorIncidenceFirst B T ≫ pullback.snd (A.projection ≫ X.hom) T.hom =
      pullback.snd (A.incidenceSource B ≫ X.hom) T.hom := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem exteriorIncidenceSecond_fst :
    A.exteriorIncidenceSecond B T ≫ pullback.fst (B.projection ≫ Y.hom) T.hom =
      pullback.fst (A.incidenceSource B ≫ X.hom) T.hom ≫ A.incidenceSnd B :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorIncidenceSecond_snd :
    A.exteriorIncidenceSecond B T ≫ pullback.snd (B.projection ≫ Y.hom) T.hom =
      pullback.snd (A.incidenceSource B ≫ X.hom) T.hom := pullback.lift_snd _ _ _

@[reassoc]
theorem exteriorIncidence_condition :
    A.exteriorIncidenceFirst B T ≫ A.exteriorIdentityTarget T =
      A.exteriorIncidenceSecond B T ≫ B.exteriorIdentitySource T := by
  apply pullback.hom_ext
  · simp only [Category.assoc, exteriorIdentityTarget_fst, exteriorIdentitySource_fst,
      exteriorIncidenceFirst_fst_assoc, exteriorIncidenceSecond_fst_assoc,
      incidence_condition]
  · simp only [Category.assoc, exteriorIdentityTarget_snd, exteriorIdentitySource_snd,
      exteriorIncidenceFirst_snd, exteriorIncidenceSecond_snd]

variable [GeometricallyIntegral T.hom]

/-- The literal exterior incidence maps into the incidence of the actual image generators. -/
def exteriorIncidenceToGenerators : A.exteriorIncidenceSupport B T ⟶
    (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T) :=
  pullback.lift
    (A.exteriorIncidenceFirst B T ≫ (A.exteriorIdentitySchemeIso T).hom)
    (A.exteriorIncidenceSecond B T ≫ (B.exteriorIdentitySchemeIso T).hom) (by
      simpa only [Category.assoc, exteriorIdentitySchemeIso_hom_targetProjection,
        exteriorIdentitySchemeIso_hom_projection] using A.exteriorIncidence_condition B T)

@[reassoc]
theorem exteriorIncidenceToGenerators_fst :
    A.exteriorIncidenceToGenerators B T ≫
      (A.exteriorIdentityGenerator T).incidenceFst (B.exteriorIdentityGenerator T) =
        A.exteriorIncidenceFirst B T ≫ (A.exteriorIdentitySchemeIso T).hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorIncidenceToGenerators_fst_simp :
    A.exteriorIncidenceToGenerators B T ≫
      @FiniteCorrespondenceGenerator.incidenceFst (Spec (.of k))
        (pullback X.hom T.hom) (pullback Y.hom T.hom) (pullback Z.hom T.hom)
        (pullback.fst X.hom T.hom ≫ X.hom)
        (pullback.fst Y.hom T.hom ≫ Y.hom)
        (pullback.fst Z.hom T.hom ≫ Z.hom)
        (A.exteriorIdentityGenerator T) (B.exteriorIdentityGenerator T) =
        A.exteriorIncidenceFirst B T ≫ (A.exteriorIdentitySchemeIso T).hom :=
  exteriorIncidenceToGenerators_fst A B T

@[reassoc]
theorem exteriorIncidenceToGenerators_snd :
    A.exteriorIncidenceToGenerators B T ≫
      (A.exteriorIdentityGenerator T).incidenceSnd (B.exteriorIdentityGenerator T) =
        A.exteriorIncidenceSecond B T ≫ (B.exteriorIdentitySchemeIso T).hom :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem exteriorIncidenceToGenerators_snd_simp :
    A.exteriorIncidenceToGenerators B T ≫
      @FiniteCorrespondenceGenerator.incidenceSnd (Spec (.of k))
        (pullback X.hom T.hom) (pullback Y.hom T.hom) (pullback Z.hom T.hom)
        (pullback.fst X.hom T.hom ≫ X.hom)
        (pullback.fst Y.hom T.hom ≫ Y.hom)
        (pullback.fst Z.hom T.hom ≫ Z.hom)
        (A.exteriorIdentityGenerator T) (B.exteriorIdentityGenerator T) =
        A.exteriorIncidenceSecond B T ≫ (B.exteriorIdentitySchemeIso T).hom :=
  exteriorIncidenceToGenerators_snd A B T

/-- The first exterior support read from the actual generator incidence. -/
abbrev exteriorIncidenceFirstCoordinate :
    (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T) ⟶
      A.exteriorIdentitySupport T :=
  (A.exteriorIdentityGenerator T).incidenceFst (B.exteriorIdentityGenerator T) ≫
    (A.exteriorIdentitySchemeIso T).inv

/-- The second exterior support read from the actual generator incidence. -/
abbrev exteriorIncidenceSecondCoordinate :
    (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T) ⟶
      B.exteriorIdentitySupport T :=
  (A.exteriorIdentityGenerator T).incidenceSnd (B.exteriorIdentityGenerator T) ≫
    (B.exteriorIdentitySchemeIso T).inv

@[reassoc]
theorem exteriorIncidenceCoordinate_condition :
    A.exteriorIncidenceFirstCoordinate B T ≫ A.exteriorIdentityTarget T =
      A.exteriorIncidenceSecondCoordinate B T ≫ B.exteriorIdentitySource T := by
  simpa only [exteriorIncidenceFirstCoordinate, exteriorIncidenceSecondCoordinate,
    Category.assoc, exteriorIdentitySchemeIso_inv_target, exteriorIdentitySchemeIso_inv_source]
    using (A.exteriorIdentityGenerator T).incidence_condition (B.exteriorIdentityGenerator T)

@[reassoc]
theorem exteriorIncidenceCoordinate_middle :
    A.exteriorIncidenceFirstCoordinate B T ≫
        pullback.fst (A.projection ≫ X.hom) T.hom ≫ A.targetProjection =
      A.exteriorIncidenceSecondCoordinate B T ≫
        pullback.fst (B.projection ≫ Y.hom) T.hom ≫ B.projection := by
  simpa only [Category.assoc, exteriorIdentityTarget_fst, exteriorIdentitySource_fst] using
    congrArg (fun f => f ≫ pullback.fst Y.hom T.hom)
      (A.exteriorIncidenceCoordinate_condition B T)

@[reassoc]
theorem exteriorIncidenceCoordinate_parameter :
    A.exteriorIncidenceFirstCoordinate B T ≫ pullback.snd (A.projection ≫ X.hom) T.hom =
      A.exteriorIncidenceSecondCoordinate B T ≫ pullback.snd (B.projection ≫ Y.hom) T.hom := by
  simpa only [Category.assoc, exteriorIdentityTarget_snd, exteriorIdentitySource_snd] using
    congrArg (fun f => f ≫ pullback.snd Y.hom T.hom)
      (A.exteriorIncidenceCoordinate_condition B T)

/-- Forgetting the common parameter gives a point of the full original incidence. -/
def exteriorIncidenceOriginalCoordinate :
    (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T) ⟶ A.incidence B :=
  pullback.lift
    (A.exteriorIncidenceFirstCoordinate B T ≫ pullback.fst (A.projection ≫ X.hom) T.hom)
    (A.exteriorIncidenceSecondCoordinate B T ≫ pullback.fst (B.projection ≫ Y.hom) T.hom)
    (by simpa only [Category.assoc] using A.exteriorIncidenceCoordinate_middle B T)

@[reassoc (attr := simp)]
theorem exteriorIncidenceOriginalCoordinate_fst :
    A.exteriorIncidenceOriginalCoordinate B T ≫ A.incidenceFst B =
      A.exteriorIncidenceFirstCoordinate B T ≫ pullback.fst (A.projection ≫ X.hom) T.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorIncidenceOriginalCoordinate_snd :
    A.exteriorIncidenceOriginalCoordinate B T ≫ A.incidenceSnd B =
      A.exteriorIncidenceSecondCoordinate B T ≫ pullback.fst (B.projection ≫ Y.hom) T.hom :=
  pullback.lift_snd _ _ _

/-- Return from actual generator incidence to full incidence with its shared parameter. -/
def exteriorIncidenceFromGenerators :
    (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T) ⟶
      A.exteriorIncidenceSupport B T :=
  pullback.lift (A.exteriorIncidenceOriginalCoordinate B T)
    (A.exteriorIncidenceFirstCoordinate B T ≫ pullback.snd (A.projection ≫ X.hom) T.hom) (by
      simp only [incidenceSource, ← Category.assoc, exteriorIncidenceOriginalCoordinate_fst]
      simp only [Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
theorem exteriorIncidenceFromGenerators_fst :
    A.exteriorIncidenceFromGenerators B T ≫ pullback.fst (A.incidenceSource B ≫ X.hom) T.hom =
      A.exteriorIncidenceOriginalCoordinate B T := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorIncidenceFromGenerators_snd :
    A.exteriorIncidenceFromGenerators B T ≫ pullback.snd (A.incidenceSource B ≫ X.hom) T.hom =
      A.exteriorIncidenceFirstCoordinate B T ≫ pullback.snd (A.projection ≫ X.hom) T.hom :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem exteriorIncidenceFromGenerators_first :
    A.exteriorIncidenceFromGenerators B T ≫ A.exteriorIncidenceFirst B T =
      A.exteriorIncidenceFirstCoordinate B T := by
  apply pullback.hom_ext <;> simp only [Category.assoc, exteriorIncidenceFirst_fst,
    exteriorIncidenceFirst_snd, exteriorIncidenceFromGenerators_fst_assoc,
    exteriorIncidenceOriginalCoordinate_fst, exteriorIncidenceFromGenerators_snd]

@[reassoc (attr := simp)]
theorem exteriorIncidenceFromGenerators_second :
    A.exteriorIncidenceFromGenerators B T ≫ A.exteriorIncidenceSecond B T =
      A.exteriorIncidenceSecondCoordinate B T := by
  apply pullback.hom_ext
  · simp only [Category.assoc, exteriorIncidenceSecond_fst,
      exteriorIncidenceFromGenerators_fst_assoc, exteriorIncidenceOriginalCoordinate_snd]
  · simp only [Category.assoc, exteriorIncidenceSecond_snd, exteriorIncidenceFromGenerators_snd]
    exact A.exteriorIncidenceCoordinate_parameter B T

omit [GeometricallyIntegral T.hom] in
/-- Both exterior support coordinates jointly determine the full incidence product. -/
theorem exteriorIncidence_hom_ext {W : Scheme.{u}}
    {f g : W ⟶ A.exteriorIncidenceSupport B T}
    (hf : f ≫ A.exteriorIncidenceFirst B T = g ≫ A.exteriorIncidenceFirst B T)
    (hg : f ≫ A.exteriorIncidenceSecond B T = g ≫ A.exteriorIncidenceSecond B T) : f = g := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc, exteriorIncidenceFirst_fst] using
        congrArg (fun h => h ≫ pullback.fst (A.projection ≫ X.hom) T.hom) hf
    · simpa only [Category.assoc, exteriorIncidenceSecond_fst] using
        congrArg (fun h => h ≫ pullback.fst (B.projection ≫ Y.hom) T.hom) hg
  · simpa only [Category.assoc, exteriorIncidenceFirst_snd] using
      congrArg (fun h => h ≫ pullback.snd (A.projection ≫ X.hom) T.hom) hf

/-- The actual generator incidence is the full original incidence times the parameter. -/
def exteriorIdentityIncidenceIso :
    A.exteriorIncidenceSupport B T ≅
      (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T) where
  hom := A.exteriorIncidenceToGenerators B T
  inv := A.exteriorIncidenceFromGenerators B T
  hom_inv_id := by
    apply A.exteriorIncidence_hom_ext B T
    · simp only [Category.assoc, exteriorIncidenceFromGenerators_first,
        exteriorIncidenceFirstCoordinate, exteriorIncidenceToGenerators_fst_assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, exteriorIncidenceFromGenerators_second,
        exteriorIncidenceSecondCoordinate, exteriorIncidenceToGenerators_snd_assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, exteriorIncidenceToGenerators_fst,
        exteriorIncidenceFromGenerators_first_assoc, Iso.inv_hom_id,
        Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, exteriorIncidenceToGenerators_snd,
        exteriorIncidenceFromGenerators_second_assoc, Iso.inv_hom_id,
        Category.comp_id, Category.id_comp]

@[reassoc]
theorem exteriorIdentityIncidenceIso_hom_fst :
    (A.exteriorIdentityIncidenceIso B T).hom ≫
      (A.exteriorIdentityGenerator T).incidenceFst (B.exteriorIdentityGenerator T) =
        A.exteriorIncidenceFirst B T ≫ (A.exteriorIdentitySchemeIso T).hom :=
  A.exteriorIncidenceToGenerators_fst B T

@[reassoc (attr := simp)]
theorem exteriorIdentityIncidenceIso_hom_fst_simp :
    (A.exteriorIdentityIncidenceIso B T).hom ≫
      @FiniteCorrespondenceGenerator.incidenceFst (Spec (.of k))
        (pullback X.hom T.hom) (pullback Y.hom T.hom) (pullback Z.hom T.hom)
        (pullback.fst X.hom T.hom ≫ X.hom)
        (pullback.fst Y.hom T.hom ≫ Y.hom)
        (pullback.fst Z.hom T.hom ≫ Z.hom)
        (A.exteriorIdentityGenerator T) (B.exteriorIdentityGenerator T) =
        A.exteriorIncidenceFirst B T ≫ (A.exteriorIdentitySchemeIso T).hom :=
  exteriorIdentityIncidenceIso_hom_fst A B T

@[reassoc]
theorem exteriorIdentityIncidenceIso_hom_snd :
    (A.exteriorIdentityIncidenceIso B T).hom ≫
      (A.exteriorIdentityGenerator T).incidenceSnd (B.exteriorIdentityGenerator T) =
        A.exteriorIncidenceSecond B T ≫ (B.exteriorIdentitySchemeIso T).hom :=
  A.exteriorIncidenceToGenerators_snd B T

@[reassoc (attr := simp)]
theorem exteriorIdentityIncidenceIso_hom_snd_simp :
    (A.exteriorIdentityIncidenceIso B T).hom ≫
      @FiniteCorrespondenceGenerator.incidenceSnd (Spec (.of k))
        (pullback X.hom T.hom) (pullback Y.hom T.hom) (pullback Z.hom T.hom)
        (pullback.fst X.hom T.hom ≫ X.hom)
        (pullback.fst Y.hom T.hom ≫ Y.hom)
        (pullback.fst Z.hom T.hom ≫ Z.hom)
        (A.exteriorIdentityGenerator T) (B.exteriorIdentityGenerator T) =
        A.exteriorIncidenceSecond B T ≫ (B.exteriorIdentitySchemeIso T).hom :=
  exteriorIdentityIncidenceIso_hom_snd A B T

/-- The displayed product is the actual Cartesian square of the two exterior supports. -/
theorem exteriorIdentityIncidence_isPullback :
    IsPullback
      (A.exteriorIncidenceFirst B T ≫ (A.exteriorIdentitySchemeIso T).hom)
      (A.exteriorIncidenceSecond B T ≫ (B.exteriorIdentitySchemeIso T).hom)
      (A.exteriorIdentityGenerator T).targetProjection
      (B.exteriorIdentityGenerator T).projection :=
  IsPullback.of_iso_pullback
    ⟨by simpa only [Category.assoc, exteriorIdentitySchemeIso_hom_targetProjection,
      exteriorIdentitySchemeIso_hom_projection] using A.exteriorIncidence_condition B T⟩
    (A.exteriorIdentityIncidenceIso B T)
    (A.exteriorIdentityIncidenceIso_hom_fst B T)
    (A.exteriorIdentityIncidenceIso_hom_snd B T)

@[reassoc]
theorem exteriorIdentityIncidenceIso_hom_source_fst :
    (A.exteriorIdentityIncidenceIso B T).hom ≫
      (A.exteriorIdentityGenerator T).incidenceSource (B.exteriorIdentityGenerator T) ≫
        pullback.fst X.hom T.hom =
      pullback.fst (A.incidenceSource B ≫ X.hom) T.hom ≫ A.incidenceSource B := by
  simp only [incidenceSource, Category.assoc, exteriorIdentityIncidenceIso_hom_fst_assoc,
    exteriorIdentitySchemeIso_hom_projection_assoc, exteriorIdentitySource_fst,
    exteriorIncidenceFirst_fst_assoc]

@[reassoc]
theorem exteriorIdentityIncidenceIso_hom_source_snd :
    (A.exteriorIdentityIncidenceIso B T).hom ≫
      (A.exteriorIdentityGenerator T).incidenceSource (B.exteriorIdentityGenerator T) ≫
        pullback.snd X.hom T.hom =
      pullback.snd (A.incidenceSource B ≫ X.hom) T.hom := by
  simp only [incidenceSource, Category.assoc, exteriorIdentityIncidenceIso_hom_fst_assoc,
    exteriorIdentitySchemeIso_hom_projection_assoc, exteriorIdentitySource_snd,
    exteriorIncidenceFirst_snd]

@[reassoc]
theorem exteriorIdentityIncidenceIso_hom_target_fst :
    (A.exteriorIdentityIncidenceIso B T).hom ≫
      (A.exteriorIdentityGenerator T).incidenceTarget (B.exteriorIdentityGenerator T) ≫
        pullback.fst Z.hom T.hom =
      pullback.fst (A.incidenceSource B ≫ X.hom) T.hom ≫ A.incidenceTarget B := by
  simp only [incidenceTarget, Category.assoc, exteriorIdentityIncidenceIso_hom_snd_assoc,
    exteriorIdentitySchemeIso_hom_targetProjection_assoc, exteriorIdentityTarget_fst,
    exteriorIncidenceSecond_fst_assoc]

@[reassoc]
theorem exteriorIdentityIncidenceIso_hom_target_snd :
    (A.exteriorIdentityIncidenceIso B T).hom ≫
      (A.exteriorIdentityGenerator T).incidenceTarget (B.exteriorIdentityGenerator T) ≫
        pullback.snd Z.hom T.hom =
      pullback.snd (A.incidenceSource B ≫ X.hom) T.hom := by
  simp only [incidenceTarget, Category.assoc, exteriorIdentityIncidenceIso_hom_snd_assoc,
    exteriorIdentitySchemeIso_hom_targetProjection_assoc, exteriorIdentityTarget_snd,
    exteriorIncidenceSecond_snd]

end Motivic.FiniteCorrespondenceGenerator
