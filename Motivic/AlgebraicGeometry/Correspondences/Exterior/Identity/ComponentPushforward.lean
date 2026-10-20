/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Identity.Incidence
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.ExteriorPointClosure
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.WholeFiberTorExteriorDecomposition

/-!
# The actual exterior pushforward of an incidence component

The full exterior of an original incidence point closure maps through the
actual finite point-closure map. Its target is identified, over the original
ambient product, with the support of the admissible component generator.
The resulting map is the restriction of the actual exterior incidence map.
Its pushed fundamental cycle retains the original incidence residue degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Cycles.Pushforward

open _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme
open _root_.AlgebraicGeometry.Scheme.Cycles.BaseChange.ComponentDecomposition

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k))) (x : genericPoints (A.incidence B))

local instance componentPushforward_sourceObjectNoetherian :
    IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

local instance componentPushforward_ambientNoetherian :
    IsNoetherian (pullback X.hom Z.hom) :=
  isNoetherian_of_finiteType (pullback.fst X.hom Z.hom)

/-- The genuine component generator is the actual image of the source point closure. -/
def exteriorIncidenceComponentImageIso :
    (A.smoothIncidenceComponentGenerator k B x).scheme ≅
      (pointClosure (A.incidenceMap B x.1)).val.subscheme :=
  pointClosureImageIso (A.incidenceMap B) x.1

@[reassoc (attr := simp)]
theorem exteriorIncidenceComponentImageIso_hom_inclusion :
    (A.exteriorIncidenceComponentImageIso B x).hom ≫
        (pointClosure (A.incidenceMap B x.1)).val.subschemeι =
      (A.smoothIncidenceComponentGenerator k B x).inclusion :=
  pointClosureImageIso_ambient (A.incidenceMap B) x.1

@[reassoc (attr := simp)]
theorem exteriorIncidenceComponentImageIso_inv_inclusion :
    (A.exteriorIncidenceComponentImageIso B x).inv ≫
        (A.smoothIncidenceComponentGenerator k B x).inclusion =
      (pointClosure (A.incidenceMap B x.1)).val.subschemeι := by
  rw [← A.exteriorIncidenceComponentImageIso_hom_inclusion B x,
    Iso.inv_hom_id_assoc]

/-- The original finite point-closure map respects the literal field structure. -/
@[reassoc]
theorem exteriorIncidenceComponentPointClosure_structure :
    pointClosureMap (A.incidenceMap B) x.1 ≫
        ExteriorPointClosure.targetHom (A.incidenceMap B) x.1
          (pullback.fst X.hom Z.hom ≫ X.hom) =
      (pointClosure x.1).val.subschemeι ≫ (A.incidenceSource B ≫ X.hom) := by
  simp only [ExteriorPointClosure.targetHom, Category.assoc,
    pointClosureMap_ambient_assoc, incidenceMap_fst_assoc]

/-- Only the parenthesization and proved structure equality distinguish the source products. -/
def exteriorIncidenceComponentSourceIso :
    componentExterior (A.incidenceSource B ≫ X.hom) T.hom x ≅
      ExteriorPointClosure.source (A.incidenceMap B) x.1
        (pullback.fst X.hom Z.hom ≫ X.hom) T :=
  pullback.congrHom (A.exteriorIncidenceComponentPointClosure_structure B x).symm rfl

@[reassoc (attr := simp)]
theorem exteriorIncidenceComponentSourceIso_fst :
    (A.exteriorIncidenceComponentSourceIso B T x).hom ≫
        pullback.fst
          (pointClosureMap (A.incidenceMap B) x.1 ≫
            ExteriorPointClosure.targetHom (A.incidenceMap B) x.1
              (pullback.fst X.hom Z.hom ≫ X.hom)) T.hom =
      pullback.fst ((pointClosure x.1).val.subschemeι ≫
        (A.incidenceSource B ≫ X.hom)) T.hom := by
  simp only [exteriorIncidenceComponentSourceIso, pullback.congrHom_hom,
    pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
theorem exteriorIncidenceComponentSourceIso_snd :
    (A.exteriorIncidenceComponentSourceIso B T x).hom ≫
        pullback.snd
          (pointClosureMap (A.incidenceMap B) x.1 ≫
            ExteriorPointClosure.targetHom (A.incidenceMap B) x.1
              (pullback.fst X.hom Z.hom ≫ X.hom)) T.hom =
      pullback.snd ((pointClosure x.1).val.subschemeι ≫
        (A.incidenceSource B ≫ X.hom)) T.hom := by
  simp only [exteriorIncidenceComponentSourceIso, pullback.congrHom_hom,
    pullback.map, pullback.lift_snd, Category.comp_id]

/-- Base change the inverse of the actual point-closure image isomorphism. -/
def exteriorIncidenceComponentTargetIso :
    ExteriorPointClosure.target (A.incidenceMap B) x.1
        (pullback.fst X.hom Z.hom ≫ X.hom) T ≅
      (A.smoothIncidenceComponentGenerator k B x).exteriorIdentitySupport T := by
  letI : IsIso (𝟙 ((𝟭 Scheme).obj T.left)) := inferInstanceAs (IsIso (𝟙 T.left))
  let f : ExteriorPointClosure.target (A.incidenceMap B) x.1
      (pullback.fst X.hom Z.hom ≫ X.hom) T ⟶
      (A.smoothIncidenceComponentGenerator k B x).exteriorIdentitySupport T :=
    pullback.map _ _ _ _ (A.exteriorIncidenceComponentImageIso B x).inv
      (𝟙 ((𝟭 Scheme).obj T.left)) (𝟙 (Spec (.of k))) (by
        simp only [ExteriorPointClosure.targetHom, Category.comp_id,
          projection, correspondenceProjection, Category.assoc,
          exteriorIncidenceComponentImageIso_inv_inclusion_assoc]) (by simp)
  haveI : IsIso f := by
    dsimp only [f]
    exact pullback.map_isIso _ _ _ _ _ _ _ _ _
  exact asIso f

@[reassoc (attr := simp)]
theorem exteriorIncidenceComponentTargetIso_fst :
    (A.exteriorIncidenceComponentTargetIso B T x).hom ≫
        pullback.fst ((A.smoothIncidenceComponentGenerator k B x).projection ≫ X.hom)
          T.hom =
      pullback.fst (ExteriorPointClosure.targetHom (A.incidenceMap B) x.1
        (pullback.fst X.hom Z.hom ≫ X.hom)) T.hom ≫
          (A.exteriorIncidenceComponentImageIso B x).inv := by
  simp only [exteriorIncidenceComponentTargetIso, asIso_hom, pullback.map,
    pullback.lift_fst]

@[reassoc (attr := simp)]
theorem exteriorIncidenceComponentTargetIso_snd :
    (A.exteriorIncidenceComponentTargetIso B T x).hom ≫
        pullback.snd ((A.smoothIncidenceComponentGenerator k B x).projection ≫ X.hom)
          T.hom =
      pullback.snd (ExteriorPointClosure.targetHom (A.incidenceMap B) x.1
        (pullback.fst X.hom Z.hom ≫ X.hom)) T.hom := by
  simp only [exteriorIncidenceComponentTargetIso, asIso_hom, pullback.map,
    pullback.lift_snd]
  exact Category.comp_id _

@[reassoc (attr := simp)]
theorem exteriorIncidenceComponentTargetIso_source_fst :
    (A.exteriorIncidenceComponentTargetIso B T x).hom ≫
        (A.smoothIncidenceComponentGenerator k B x).exteriorIdentitySource T ≫
          pullback.fst X.hom T.hom =
      pullback.fst (ExteriorPointClosure.targetHom (A.incidenceMap B) x.1
        (pullback.fst X.hom Z.hom ≫ X.hom)) T.hom ≫
          (pointClosure (A.incidenceMap B x.1)).val.subschemeι ≫
            pullback.fst X.hom Z.hom := by
  rw [exteriorIdentitySource_fst, exteriorIncidenceComponentTargetIso_fst_assoc]
  change _ ≫ (A.exteriorIncidenceComponentImageIso B x).inv ≫
    (A.smoothIncidenceComponentGenerator k B x).inclusion ≫ _ = _
  rw [exteriorIncidenceComponentImageIso_inv_inclusion_assoc]

@[reassoc (attr := simp)]
theorem exteriorIncidenceComponentTargetIso_source_snd :
    (A.exteriorIncidenceComponentTargetIso B T x).hom ≫
        (A.smoothIncidenceComponentGenerator k B x).exteriorIdentitySource T ≫
          pullback.snd X.hom T.hom =
      pullback.snd (ExteriorPointClosure.targetHom (A.incidenceMap B) x.1
        (pullback.fst X.hom Z.hom ≫ X.hom)) T.hom := by
  rw [exteriorIdentitySource_snd, exteriorIncidenceComponentTargetIso_snd]

@[reassoc (attr := simp)]
theorem exteriorIncidenceComponentTargetIso_target_fst :
    (A.exteriorIncidenceComponentTargetIso B T x).hom ≫
        (A.smoothIncidenceComponentGenerator k B x).exteriorIdentityTarget T ≫
          pullback.fst Z.hom T.hom =
      pullback.fst (ExteriorPointClosure.targetHom (A.incidenceMap B) x.1
        (pullback.fst X.hom Z.hom ≫ X.hom)) T.hom ≫
          (pointClosure (A.incidenceMap B x.1)).val.subschemeι ≫
            pullback.snd X.hom Z.hom := by
  rw [exteriorIdentityTarget_fst, exteriorIncidenceComponentTargetIso_fst_assoc]
  change _ ≫ (A.exteriorIncidenceComponentImageIso B x).inv ≫
    (A.smoothIncidenceComponentGenerator k B x).inclusion ≫ _ = _
  rw [exteriorIncidenceComponentImageIso_inv_inclusion_assoc]

@[reassoc (attr := simp)]
theorem exteriorIncidenceComponentTargetIso_target_snd :
    (A.exteriorIncidenceComponentTargetIso B T x).hom ≫
        (A.smoothIncidenceComponentGenerator k B x).exteriorIdentityTarget T ≫
          pullback.snd Z.hom T.hom =
      pullback.snd (ExteriorPointClosure.targetHom (A.incidenceMap B) x.1
        (pullback.fst X.hom Z.hom ≫ X.hom)) T.hom := by
  rw [exteriorIdentityTarget_snd, exteriorIncidenceComponentTargetIso_snd]

/-- The actual component product map to the exterior support of its admissible image. -/
def exteriorIncidenceComponentSupportMap :
    componentExterior (A.incidenceSource B ≫ X.hom) T.hom x ⟶
      (A.smoothIncidenceComponentGenerator k B x).exteriorIdentitySupport T :=
  (A.exteriorIncidenceComponentSourceIso B T x).hom ≫
    ExteriorPointClosure.map (A.incidenceMap B) x.1
      (pullback.fst X.hom Z.hom ≫ X.hom) T ≫
        (A.exteriorIncidenceComponentTargetIso B T x).hom

instance exteriorIncidenceComponentSupportMap_isFinite :
    IsFinite (A.exteriorIncidenceComponentSupportMap B T x) := by
  unfold exteriorIncidenceComponentSupportMap
  infer_instance

/-- Its literal map into the actual exterior correspondence ambient product. -/
def exteriorIncidenceComponentAmbientMap :
    componentExterior (A.incidenceSource B ≫ X.hom) T.hom x ⟶
      pullback (SmoothSite.product X T).hom (SmoothSite.product Z T).hom :=
  A.exteriorIncidenceComponentSupportMap B T x ≫
    (A.smoothIncidenceComponentGenerator k B x).exteriorIdentityInclusion T

instance exteriorIncidenceComponentAmbientMap_isFinite :
    IsFinite (A.exteriorIncidenceComponentAmbientMap B T x) := by
  unfold exteriorIncidenceComponentAmbientMap
  infer_instance

@[reassoc]
theorem exteriorIncidenceComponentAmbientMap_source_fst :
    A.exteriorIncidenceComponentAmbientMap B T x ≫
        pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Z T).hom ≫
          pullback.fst X.hom T.hom =
      pullback.fst ((pointClosure x.1).val.subschemeι ≫
        (A.incidenceSource B ≫ X.hom)) T.hom ≫
          (pointClosure x.1).val.subschemeι ≫ A.incidenceSource B := by
  simp only [exteriorIncidenceComponentAmbientMap, exteriorIncidenceComponentSupportMap,
    Category.assoc, exteriorIdentityInclusion_fst_assoc,
    exteriorIncidenceComponentTargetIso_source_fst,
    _root_.AlgebraicGeometry.Scheme.Cycles.Pushforward.ExteriorPointClosure.map_fst_assoc,
        pointClosureMap_ambient_assoc,
    incidenceMap_fst, exteriorIncidenceComponentSourceIso_fst_assoc]

@[reassoc (attr := simp)]
theorem exteriorIncidenceComponentAmbientMap_source_fst_simp :
    A.exteriorIncidenceComponentAmbientMap B T x ≫
        pullback.fst (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst Z.hom T.hom ≫ Z.hom) ≫
          pullback.fst X.hom T.hom =
      pullback.fst ((pointClosure x.1).val.subschemeι ≫
        (A.incidenceSource B ≫ X.hom)) T.hom ≫
          (pointClosure x.1).val.subschemeι ≫ A.incidenceSource B :=
  exteriorIncidenceComponentAmbientMap_source_fst A B T x

@[reassoc]
theorem exteriorIncidenceComponentAmbientMap_source_snd :
    A.exteriorIncidenceComponentAmbientMap B T x ≫
        pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Z T).hom ≫
          pullback.snd X.hom T.hom =
      pullback.snd ((pointClosure x.1).val.subschemeι ≫
        (A.incidenceSource B ≫ X.hom)) T.hom := by
  simp only [exteriorIncidenceComponentAmbientMap, exteriorIncidenceComponentSupportMap,
    Category.assoc, exteriorIdentityInclusion_fst_assoc,
    exteriorIncidenceComponentTargetIso_source_snd,
    ExteriorPointClosure.map_snd, exteriorIncidenceComponentSourceIso_snd]

@[reassoc (attr := simp)]
theorem exteriorIncidenceComponentAmbientMap_source_snd_simp :
    A.exteriorIncidenceComponentAmbientMap B T x ≫
        pullback.fst (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst Z.hom T.hom ≫ Z.hom) ≫
          pullback.snd X.hom T.hom =
      pullback.snd ((pointClosure x.1).val.subschemeι ≫
        (A.incidenceSource B ≫ X.hom)) T.hom :=
  exteriorIncidenceComponentAmbientMap_source_snd A B T x

@[reassoc]
theorem exteriorIncidenceComponentAmbientMap_target_fst :
    A.exteriorIncidenceComponentAmbientMap B T x ≫
        pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Z T).hom ≫
          pullback.fst Z.hom T.hom =
      pullback.fst ((pointClosure x.1).val.subschemeι ≫
        (A.incidenceSource B ≫ X.hom)) T.hom ≫
          (pointClosure x.1).val.subschemeι ≫ A.incidenceTarget B := by
  simp only [exteriorIncidenceComponentAmbientMap, exteriorIncidenceComponentSupportMap,
    Category.assoc, exteriorIdentityInclusion_snd_assoc,
    exteriorIncidenceComponentTargetIso_target_fst,
    _root_.AlgebraicGeometry.Scheme.Cycles.Pushforward.ExteriorPointClosure.map_fst_assoc,
        pointClosureMap_ambient_assoc,
    incidenceMap_snd, exteriorIncidenceComponentSourceIso_fst_assoc]

@[reassoc (attr := simp)]
theorem exteriorIncidenceComponentAmbientMap_target_fst_simp :
    A.exteriorIncidenceComponentAmbientMap B T x ≫
        pullback.snd (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst Z.hom T.hom ≫ Z.hom) ≫
          pullback.fst Z.hom T.hom =
      pullback.fst ((pointClosure x.1).val.subschemeι ≫
        (A.incidenceSource B ≫ X.hom)) T.hom ≫
          (pointClosure x.1).val.subschemeι ≫ A.incidenceTarget B :=
  exteriorIncidenceComponentAmbientMap_target_fst A B T x

@[reassoc]
theorem exteriorIncidenceComponentAmbientMap_target_snd :
    A.exteriorIncidenceComponentAmbientMap B T x ≫
        pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Z T).hom ≫
          pullback.snd Z.hom T.hom =
      pullback.snd ((pointClosure x.1).val.subschemeι ≫
        (A.incidenceSource B ≫ X.hom)) T.hom := by
  simp only [exteriorIncidenceComponentAmbientMap, exteriorIncidenceComponentSupportMap,
    Category.assoc, exteriorIdentityInclusion_snd_assoc,
    exteriorIncidenceComponentTargetIso_target_snd,
    ExteriorPointClosure.map_snd, exteriorIncidenceComponentSourceIso_snd]

@[reassoc (attr := simp)]
theorem exteriorIncidenceComponentAmbientMap_target_snd_simp :
    A.exteriorIncidenceComponentAmbientMap B T x ≫
        pullback.snd (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst Z.hom T.hom ≫ Z.hom) ≫
          pullback.snd Z.hom T.hom =
      pullback.snd ((pointClosure x.1).val.subschemeι ≫
        (A.incidenceSource B ≫ X.hom)) T.hom :=
  exteriorIncidenceComponentAmbientMap_target_snd A B T x

variable [GeometricallyIntegral T.hom]

/-- The full incidence product maps through its proved isomorphism to actual exterior incidence. -/
def exteriorIncidenceAmbientMap : A.exteriorIncidenceSupport B T ⟶
    pullback (SmoothSite.product X T).hom (SmoothSite.product Z T).hom :=
  (A.exteriorIdentityIncidenceIso B T).hom ≫
    (A.exteriorIdentityGenerator T).incidenceMap (B.exteriorIdentityGenerator T)

instance exteriorIncidenceAmbientMap_isFinite : IsFinite (A.exteriorIncidenceAmbientMap B T) := by
  unfold exteriorIncidenceAmbientMap
  infer_instance

@[reassoc]
theorem exteriorIncidenceAmbientMap_source_fst :
    A.exteriorIncidenceAmbientMap B T ≫
        pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Z T).hom ≫
          pullback.fst X.hom T.hom =
      pullback.fst (A.incidenceSource B ≫ X.hom) T.hom ≫ A.incidenceSource B := by
  dsimp only [exteriorIncidenceAmbientMap]
  rw [Category.assoc, incidenceMap_fst_assoc]
  exact A.exteriorIdentityIncidenceIso_hom_source_fst B T

@[reassoc (attr := simp)]
theorem exteriorIncidenceAmbientMap_source_fst_simp :
    A.exteriorIncidenceAmbientMap B T ≫
        pullback.fst (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst Z.hom T.hom ≫ Z.hom) ≫
          pullback.fst X.hom T.hom =
      pullback.fst (A.incidenceSource B ≫ X.hom) T.hom ≫ A.incidenceSource B :=
  exteriorIncidenceAmbientMap_source_fst A B T

@[reassoc]
theorem exteriorIncidenceAmbientMap_source_snd :
    A.exteriorIncidenceAmbientMap B T ≫
        pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Z T).hom ≫
          pullback.snd X.hom T.hom =
      pullback.snd (A.incidenceSource B ≫ X.hom) T.hom := by
  dsimp only [exteriorIncidenceAmbientMap]
  rw [Category.assoc, incidenceMap_fst_assoc]
  exact A.exteriorIdentityIncidenceIso_hom_source_snd B T

@[reassoc (attr := simp)]
theorem exteriorIncidenceAmbientMap_source_snd_simp :
    A.exteriorIncidenceAmbientMap B T ≫
        pullback.fst (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst Z.hom T.hom ≫ Z.hom) ≫
          pullback.snd X.hom T.hom =
      pullback.snd (A.incidenceSource B ≫ X.hom) T.hom :=
  exteriorIncidenceAmbientMap_source_snd A B T

@[reassoc]
theorem exteriorIncidenceAmbientMap_target_fst :
    A.exteriorIncidenceAmbientMap B T ≫
        pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Z T).hom ≫
          pullback.fst Z.hom T.hom =
      pullback.fst (A.incidenceSource B ≫ X.hom) T.hom ≫ A.incidenceTarget B := by
  dsimp only [exteriorIncidenceAmbientMap]
  rw [Category.assoc, incidenceMap_snd_assoc]
  exact A.exteriorIdentityIncidenceIso_hom_target_fst B T

@[reassoc (attr := simp)]
theorem exteriorIncidenceAmbientMap_target_fst_simp :
    A.exteriorIncidenceAmbientMap B T ≫
        pullback.snd (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst Z.hom T.hom ≫ Z.hom) ≫
          pullback.fst Z.hom T.hom =
      pullback.fst (A.incidenceSource B ≫ X.hom) T.hom ≫ A.incidenceTarget B :=
  exteriorIncidenceAmbientMap_target_fst A B T

@[reassoc]
theorem exteriorIncidenceAmbientMap_target_snd :
    A.exteriorIncidenceAmbientMap B T ≫
        pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Z T).hom ≫
          pullback.snd Z.hom T.hom =
      pullback.snd (A.incidenceSource B ≫ X.hom) T.hom := by
  dsimp only [exteriorIncidenceAmbientMap]
  rw [Category.assoc, incidenceMap_snd_assoc]
  exact A.exteriorIdentityIncidenceIso_hom_target_snd B T

@[reassoc (attr := simp)]
theorem exteriorIncidenceAmbientMap_target_snd_simp :
    A.exteriorIncidenceAmbientMap B T ≫
        pullback.snd (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst Z.hom T.hom ≫ Z.hom) ≫
          pullback.snd Z.hom T.hom =
      pullback.snd (A.incidenceSource B ≫ X.hom) T.hom :=
  exteriorIncidenceAmbientMap_target_snd A B T

/-- Both routes preserve the original outer coordinates and the identical parameter. -/
@[reassoc]
theorem exteriorIncidenceComponentAmbientMap_factorization :
    componentExteriorInclusion (A.incidenceSource B ≫ X.hom) T.hom x ≫
        A.exteriorIncidenceAmbientMap B T =
      A.exteriorIncidenceComponentAmbientMap B T x := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, exteriorIncidenceAmbientMap_source_fst, componentExteriorInclusion,
        exteriorInclusion_fst_assoc, exteriorIncidenceComponentAmbientMap_source_fst]
    · simp only [Category.assoc, exteriorIncidenceAmbientMap_source_snd, componentExteriorInclusion,
        exteriorInclusion_snd, exteriorIncidenceComponentAmbientMap_source_snd]
  · apply pullback.hom_ext
    · simp only [Category.assoc, exteriorIncidenceAmbientMap_target_fst, componentExteriorInclusion,
        exteriorInclusion_fst_assoc, exteriorIncidenceComponentAmbientMap_target_fst]
    · simp only [Category.assoc, exteriorIncidenceAmbientMap_target_snd, componentExteriorInclusion,
        exteriorInclusion_snd, exteriorIncidenceComponentAmbientMap_target_snd]

instance exteriorIncidenceComponentExterior_isNoetherian :
    IsNoetherian (componentExterior (A.incidenceSource B ≫ X.hom) T.hom x) :=
  isNoetherian_of_finiteType (A.exteriorIncidenceComponentSourceIso B T x).hom

/-- Transporting the proved finite point-closure pushforward retains the original degree. -/
theorem exteriorIncidenceComponentSupportMap_fundamentalCycle :
    IntegralCycle.finitePushforward (A.exteriorIncidenceComponentSupportMap B T x)
        (fundamentalCycle (componentExterior (A.incidenceSource B ≫ X.hom) T.hom x)) =
      ((A.incidenceMap B).residueDegree x.1 : ℤ) •
        fundamentalCycle
          ((A.smoothIncidenceComponentGenerator k B x).exteriorIdentitySupport T) := by
  change IntegralCycle.finitePushforward
    ((A.exteriorIncidenceComponentSourceIso B T x).hom ≫
      ExteriorPointClosure.map (A.incidenceMap B) x.1
        (pullback.fst X.hom Z.hom ≫ X.hom) T ≫
          (A.exteriorIncidenceComponentTargetIso B T x).hom) _ = _
  rw [IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply, Scheme.finitePushforward_fundamentalCycle,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    ExteriorPointClosure.finitePushforward_fundamentalCycle,
    map_zsmul, Scheme.finitePushforward_fundamentalCycle]

/-- The actual ambient pushforward is the original degree times the exterior generator cycle. -/
theorem exteriorIncidenceComponentAmbientMap_fundamentalCycle :
    IntegralCycle.finitePushforward (A.exteriorIncidenceComponentAmbientMap B T x)
        (fundamentalCycle (componentExterior (A.incidenceSource B ≫ X.hom) T.hom x)) =
      ((A.incidenceMap B).residueDegree x.1 : ℤ) •
        FiniteCorrespondence.toIntegralCycle
          ((A.smoothIncidenceComponentGenerator k B x).exteriorIdentityGenerator T).cycle := by
  change IntegralCycle.finitePushforward
    (A.exteriorIncidenceComponentSupportMap B T x ≫
      (A.smoothIncidenceComponentGenerator k B x).exteriorIdentityInclusion T) _ = _
  rw [IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply, exteriorIncidenceComponentSupportMap_fundamentalCycle,
    map_zsmul, toIntegralCycle_exteriorIdentityGenerator_cycle]

/-- A source-component term of the whole-fiber cycle pushes through the actual incidence map. -/
theorem exteriorIncidence_finitePushforward_componentFundamentalCycle :
    IntegralCycle.finitePushforward (A.exteriorIncidenceAmbientMap B T)
        (IntegralCycle.finitePushforward
          (componentExteriorInclusion (A.incidenceSource B ≫ X.hom) T.hom x)
          (fundamentalCycle (componentExterior (A.incidenceSource B ≫ X.hom) T.hom x))) =
      ((A.incidenceMap B).residueDegree x.1 : ℤ) •
        FiniteCorrespondence.toIntegralCycle
          ((A.smoothIncidenceComponentGenerator k B x).exteriorIdentityGenerator T).cycle := by
  have hcongr {P Q : Scheme.{u}} (f g : P ⟶ Q) (hf : IsFinite f) (hg : IsFinite g)
      (h : f = g) (c : IntegralCycle P) :
      @IntegralCycle.finitePushforward P Q f hf c =
        @IntegralCycle.finitePushforward P Q g hg c := by
    cases h
    rfl
  rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  exact (hcongr _ _ inferInstance inferInstance
    (A.exteriorIncidenceComponentAmbientMap_factorization B T x) _).trans
      (A.exteriorIncidenceComponentAmbientMap_fundamentalCycle B T x)

end Motivic.FiniteCorrespondenceGenerator
