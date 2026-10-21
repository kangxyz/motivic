/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Simplex.GraphInterchangeGeometry

/-!
# The geometric support of mixed graph and exterior incidence

Changing the parameter on an exterior support identifies its actual incidence
with the compatible graph component. The identification preserves the source
and target maps and requires no flatness of the correspondence support or of
the parameter morphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y T T' : SmoothSite (Spec (.of k))}
  (V : FiniteCorrespondenceGenerator X.hom Y.hom) (u : T ⟶ T')

/-- The original support coordinate is unchanged by a parameter morphism. -/
def exteriorParameterMap : V.exteriorIdentitySupport T ⟶ V.exteriorIdentitySupport T' :=
  pullback.map _ _ _ _ (𝟙 V.scheme) u.left (𝟙 (Spec (.of k)))
    (by simp) (by simp)

@[reassoc (attr := simp)]
theorem exteriorParameterMap_fst :
    V.exteriorParameterMap u ≫ pullback.fst (V.projection ≫ X.hom) T'.hom =
      pullback.fst (V.projection ≫ X.hom) T.hom := by
  simp [exteriorParameterMap, pullback.map]

@[reassoc (attr := simp)]
theorem exteriorParameterMap_snd :
    V.exteriorParameterMap u ≫ pullback.snd (V.projection ≫ X.hom) T'.hom =
      pullback.snd (V.projection ≫ X.hom) T.hom ≫ u.left := by
  simp [exteriorParameterMap, pullback.map]

@[reassoc]
theorem exteriorParameterMap_source :
    V.exteriorParameterMap u ≫ V.exteriorIdentitySource T' =
      V.exteriorIdentitySource T ≫ (SmoothSite.productMap (𝟙 X) u).left := by
  apply pullback.hom_ext <;>
    simp [Category.assoc, SimplexExteriorGraph.productMap_id_fst,
      SimplexExteriorGraph.productMap_id_snd]

@[reassoc]
theorem exteriorParameterMap_target :
    V.exteriorParameterMap u ≫ V.exteriorIdentityTarget T' =
      V.exteriorIdentityTarget T ≫ (SmoothSite.productMap (𝟙 Y) u).left := by
  apply pullback.hom_ext <;>
    simp [Category.assoc, SimplexExteriorGraph.productMap_id_fst,
      SimplexExteriorGraph.productMap_id_snd]

end Motivic.FiniteCorrespondenceGenerator

namespace Motivic.SimplexExteriorGraph
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y T T' : SmoothSite (Spec (.of k))}
  (u : T ⟶ T') (V : FiniteCorrespondenceGenerator X.hom Y.hom)
  [GeometricallyIntegral T'.hom]
  (A : FiniteCorrespondenceGenerator (SmoothSite.product X T).hom
    (SmoothSite.product X T').hom)
  (hA : A.projection ≫ (SmoothSite.productMap (𝟙 X) u).left = A.targetProjection)

/-- The original support coordinate read from the second incidence factor. -/
abbrev incidenceSupportCoordinate : A.incidence (V.exteriorIdentityGenerator T') ⟶ V.scheme :=
  A.incidenceSnd (V.exteriorIdentityGenerator T') ≫
    (V.exteriorIdentitySchemeIso T').inv ≫ pullback.fst (V.projection ≫ X.hom) T'.hom

/-- The parameter coordinate read from the first incidence factor. -/
abbrev incidenceParameterCoordinate : A.incidence (V.exteriorIdentityGenerator T') ⟶ T.left :=
  A.incidenceSource (V.exteriorIdentityGenerator T') ≫ pullback.snd X.hom T.hom

include hA in
@[reassoc]
theorem incidenceSupportCoordinate_projection :
    incidenceSupportCoordinate V A ≫ V.projection =
      A.incidenceSource (V.exteriorIdentityGenerator T') ≫ pullback.fst X.hom T.hom := by
  have h := congrArg (fun f => f ≫ pullback.fst X.hom T'.hom)
    (A.incidence_condition (V.exteriorIdentityGenerator T'))
  rw [← hA, ← V.exteriorIdentitySchemeIso_inv_source T'] at h
  simpa only [Category.assoc, productMap_id_fst, V.exteriorIdentitySource_fst] using h.symm

include hA in
@[reassoc]
theorem incidenceParameterCoordinate_map :
    incidenceParameterCoordinate V A ≫ u.left =
      A.incidenceSnd (V.exteriorIdentityGenerator T') ≫
        (V.exteriorIdentitySchemeIso T').inv ≫
          pullback.snd (V.projection ≫ X.hom) T'.hom := by
  have h := congrArg (fun f => f ≫ pullback.snd X.hom T'.hom)
    (A.incidence_condition (V.exteriorIdentityGenerator T'))
  rw [← hA, ← V.exteriorIdentitySchemeIso_inv_source T'] at h
  simpa only [Category.assoc, productMap_id_snd, V.exteriorIdentitySource_snd] using h

/-- Actual mixed incidence returns to the literal exterior support. -/
def incidenceToExteriorSupport :
    A.incidence (V.exteriorIdentityGenerator T') ⟶ V.exteriorIdentitySupport T :=
  pullback.lift (incidenceSupportCoordinate V A) (incidenceParameterCoordinate V A) (by
    rw [← Category.assoc, incidenceSupportCoordinate_projection u V A hA]
    exact Category.assoc _ _ _ |>.trans
      (congrArg (A.incidenceSource (V.exteriorIdentityGenerator T') ≫ ·) pullback.condition))

@[reassoc (attr := simp)]
theorem incidenceToExteriorSupport_fst :
    incidenceToExteriorSupport u V A hA ≫ pullback.fst (V.projection ≫ X.hom) T.hom =
      incidenceSupportCoordinate V A := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem incidenceToExteriorSupport_snd :
    incidenceToExteriorSupport u V A hA ≫ pullback.snd (V.projection ≫ X.hom) T.hom =
      incidenceParameterCoordinate V A := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem incidenceToExteriorSupport_source :
    incidenceToExteriorSupport u V A hA ≫ V.exteriorIdentitySource T =
      A.incidenceSource (V.exteriorIdentityGenerator T') := by
  apply pullback.hom_ext
  · simpa only [Category.assoc, V.exteriorIdentitySource_fst,
      incidenceToExteriorSupport_fst_assoc] using incidenceSupportCoordinate_projection u V A hA
  · simp only [Category.assoc, V.exteriorIdentitySource_snd, incidenceToExteriorSupport_snd]

@[reassoc (attr := simp)]
theorem incidenceToExteriorSupport_parameter :
    incidenceToExteriorSupport u V A hA ≫ V.exteriorParameterMap u =
      A.incidenceSnd (V.exteriorIdentityGenerator T') ≫ (V.exteriorIdentitySchemeIso T').inv := by
  apply pullback.hom_ext
  · simp only [Category.assoc, V.exteriorParameterMap_fst, incidenceToExteriorSupport_fst]
  · simpa only [Category.assoc, V.exteriorParameterMap_snd,
      incidenceToExteriorSupport_snd_assoc] using incidenceParameterCoordinate_map u V A hA

variable [IsOpenImmersion A.projection]
  (hRange : Set.range (V.exteriorIdentitySource T) ⊆ Set.range A.projection)

/-- Lift the exterior source into the compatible open graph support. -/
def exteriorToGraphSupport : V.exteriorIdentitySupport T ⟶ A.scheme :=
  IsOpenImmersion.lift A.projection (V.exteriorIdentitySource T) hRange

omit [GeometricallyIntegral T'.hom] in
@[reassoc]
theorem exteriorToGraphSupport_projection :
    exteriorToGraphSupport V A hRange ≫ A.projection = V.exteriorIdentitySource T :=
  IsOpenImmersion.lift_fac _ _ _

omit [GeometricallyIntegral T'.hom] in
@[reassoc (attr := simp)]
theorem exteriorToGraphSupport_projection_simp :
    exteriorToGraphSupport V A hRange ≫ @FiniteCorrespondenceGenerator.projection (Spec (.of k))
        (pullback X.hom T.hom) (pullback X.hom T'.hom)
        (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst X.hom T'.hom ≫ X.hom) A =
      V.exteriorIdentitySource T :=
  exteriorToGraphSupport_projection V A hRange

/-- The source lift and the changed exterior parameter define actual incidence. -/
def exteriorSupportToIncidence :
    V.exteriorIdentitySupport T ⟶ A.incidence (V.exteriorIdentityGenerator T') :=
  pullback.lift (exteriorToGraphSupport V A hRange)
    (V.exteriorParameterMap u ≫ (V.exteriorIdentitySchemeIso T').hom) (by
      rw [← hA, ← Category.assoc, exteriorToGraphSupport_projection,
        Category.assoc, V.exteriorIdentitySchemeIso_hom_projection,
        V.exteriorParameterMap_source])

@[reassoc]
theorem exteriorSupportToIncidence_fst :
    exteriorSupportToIncidence u V A hA hRange ≫
      A.incidenceFst (V.exteriorIdentityGenerator T') = exteriorToGraphSupport V A hRange :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorSupportToIncidence_fst_simp :
    exteriorSupportToIncidence u V A hA hRange ≫
      @FiniteCorrespondenceGenerator.incidenceFst (Spec (.of k))
        (pullback X.hom T.hom) (pullback X.hom T'.hom) (pullback Y.hom T'.hom)
        (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst X.hom T'.hom ≫ X.hom)
        (pullback.fst Y.hom T'.hom ≫ Y.hom) A (V.exteriorIdentityGenerator T') =
      exteriorToGraphSupport V A hRange :=
  exteriorSupportToIncidence_fst u V A hA hRange

@[reassoc]
theorem exteriorSupportToIncidence_snd :
    exteriorSupportToIncidence u V A hA hRange ≫
      A.incidenceSnd (V.exteriorIdentityGenerator T') =
        V.exteriorParameterMap u ≫ (V.exteriorIdentitySchemeIso T').hom :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem exteriorSupportToIncidence_snd_simp :
    exteriorSupportToIncidence u V A hA hRange ≫
      @FiniteCorrespondenceGenerator.incidenceSnd (Spec (.of k))
        (pullback X.hom T.hom) (pullback X.hom T'.hom) (pullback Y.hom T'.hom)
        (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst X.hom T'.hom ≫ X.hom)
        (pullback.fst Y.hom T'.hom ≫ Y.hom) A (V.exteriorIdentityGenerator T') =
        V.exteriorParameterMap u ≫ (V.exteriorIdentitySchemeIso T').hom :=
  exteriorSupportToIncidence_snd u V A hA hRange

/-- A compatible open graph support has precisely the original exterior incidence support. -/
def exteriorIncidenceIso :
    V.exteriorIdentitySupport T ≅ A.incidence (V.exteriorIdentityGenerator T') where
  hom := exteriorSupportToIncidence u V A hA hRange
  inv := incidenceToExteriorSupport u V A hA
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, incidenceToExteriorSupport_fst,
        incidenceSupportCoordinate, exteriorSupportToIncidence_snd_assoc,
        Iso.hom_inv_id_assoc, V.exteriorParameterMap_fst, Category.id_comp]
    · simp only [Category.assoc, incidenceToExteriorSupport_snd,
        incidenceParameterCoordinate, FiniteCorrespondenceGenerator.incidenceSource,
        exteriorSupportToIncidence_fst_assoc, exteriorToGraphSupport_projection_assoc,
        V.exteriorIdentitySource_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply (cancel_mono A.projection).mp
      change (incidenceToExteriorSupport u V A hA ≫
        exteriorSupportToIncidence u V A hA hRange) ≫
          A.incidenceFst (V.exteriorIdentityGenerator T') ≫ A.projection = _
      rw [Category.assoc, exteriorSupportToIncidence_fst_assoc,
        exteriorToGraphSupport_projection, incidenceToExteriorSupport_source]
      simp only [Category.id_comp]
    · change (incidenceToExteriorSupport u V A hA ≫
        exteriorSupportToIncidence u V A hA hRange) ≫
          A.incidenceSnd (V.exteriorIdentityGenerator T') = _
      rw [Category.assoc, exteriorSupportToIncidence_snd,
        incidenceToExteriorSupport_parameter_assoc]
      simp

@[reassoc]
theorem exteriorIncidenceIso_hom_source :
    (exteriorIncidenceIso u V A hA hRange).hom ≫
      A.incidenceSource (V.exteriorIdentityGenerator T') = V.exteriorIdentitySource T := by
  change exteriorSupportToIncidence u V A hA hRange ≫
    A.incidenceFst (V.exteriorIdentityGenerator T') ≫ A.projection = _
  rw [exteriorSupportToIncidence_fst_assoc, exteriorToGraphSupport_projection]

@[reassoc (attr := simp)]
theorem exteriorIncidenceIso_hom_source_simp :
    (exteriorIncidenceIso u V A hA hRange).hom ≫
      @FiniteCorrespondenceGenerator.incidenceSource (Spec (.of k))
        (pullback X.hom T.hom) (pullback X.hom T'.hom) (pullback Y.hom T'.hom)
        (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst X.hom T'.hom ≫ X.hom)
        (pullback.fst Y.hom T'.hom ≫ Y.hom) A (V.exteriorIdentityGenerator T') =
      V.exteriorIdentitySource T :=
  exteriorIncidenceIso_hom_source u V A hA hRange

@[reassoc]
theorem exteriorIncidenceIso_hom_target :
    (exteriorIncidenceIso u V A hA hRange).hom ≫
      A.incidenceTarget (V.exteriorIdentityGenerator T') =
        V.exteriorParameterMap u ≫ V.exteriorIdentityTarget T' := by
  change exteriorSupportToIncidence u V A hA hRange ≫
    A.incidenceSnd (V.exteriorIdentityGenerator T') ≫
      (V.exteriorIdentityGenerator T').targetProjection = _
  rw [exteriorSupportToIncidence_snd_assoc, V.exteriorIdentitySchemeIso_hom_targetProjection]

@[reassoc (attr := simp)]
theorem exteriorIncidenceIso_hom_target_simp :
    (exteriorIncidenceIso u V A hA hRange).hom ≫
      @FiniteCorrespondenceGenerator.incidenceTarget (Spec (.of k))
        (pullback X.hom T.hom) (pullback X.hom T'.hom) (pullback Y.hom T'.hom)
        (pullback.fst X.hom T.hom ≫ X.hom) (pullback.fst X.hom T'.hom ≫ X.hom)
        (pullback.fst Y.hom T'.hom ≫ Y.hom) A (V.exteriorIdentityGenerator T') =
        V.exteriorParameterMap u ≫ V.exteriorIdentityTarget T' :=
  exteriorIncidenceIso_hom_target u V A hA hRange

end Motivic.SimplexExteriorGraph

namespace Motivic.SimplexExteriorGraph
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y T T' : SmoothSite (Spec (.of k))}
  (u : T ⟶ T') (V : FiniteCorrespondenceGenerator X.hom Y.hom)
  [GeometricallyIntegral T.hom] [GeometricallyIntegral T'.hom]
  (A : FiniteCorrespondenceGenerator (SmoothSite.product X T).hom
    (SmoothSite.product X T').hom)
  (hA : A.projection ≫ (SmoothSite.productMap (𝟙 X) u).left = A.targetProjection)

include hA in
/-- A graph source component different from the exterior source has empty incidence. -/
theorem incidence_isEmpty_of_source_ne
    (hne : Set.range A.projection ≠ Set.range (V.exteriorIdentitySource T)) :
    IsEmpty (A.incidence (V.exteriorIdentityGenerator T')) := by
  constructor
  intro w
  apply hne
  apply irreducibleComponents_eq_of_mem_of_domain_stalks
    (fun x => SmoothSite.isDomain_stalk k (SmoothSite.product X T) x)
    A.range_projection_mem (V.exteriorIdentitySource_range_mem T)
    (x := A.incidenceSource (V.exteriorIdentityGenerator T') w)
  · exact ⟨A.incidenceFst (V.exteriorIdentityGenerator T') w, rfl⟩
  · refine ⟨incidenceToExteriorSupport u V A hA w, ?_⟩
    exact congrArg (fun f => f w) (incidenceToExteriorSupport_source u V A hA)

include hA in
/-- Incompatible source components contribute zero to the actual mixed Tor cycle. -/
theorem incidenceTorCorrespondence_eq_zero_of_source_ne
    (hne : Set.range A.projection ≠ Set.range (V.exteriorIdentitySource T)) :
    A.incidenceTorCorrespondence k (V.exteriorIdentityGenerator T') = 0 := by
  have : IsEmpty (A.incidence (V.exteriorIdentityGenerator T')) :=
    incidence_isEmpty_of_source_ne u V A hA hne
  exact A.incidenceTorCorrespondence_eq_zero_of_isEmpty k _

variable [IsOpenImmersion A.projection]
  (hRange : Set.range (V.exteriorIdentitySource T) ⊆ Set.range A.projection)

/-- The incidence isomorphism preserves the exact finite map to the source-target product. -/
theorem exteriorIncidenceIso_hom_incidenceMap :
    (exteriorIncidenceIso u V A hA hRange).hom ≫
      A.incidenceMap (V.exteriorIdentityGenerator T') =
        (V.exteriorIdentitySchemeIso T).hom ≫
          (V.exteriorIdentityGenerator T).graphPostcompositionMap
            (SmoothSite.productMap (𝟙 Y) u).left
            (MorphismProperty.Over.w (SmoothSite.productMap (𝟙 Y) u)) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, FiniteCorrespondenceGenerator.incidenceMap_fst,
      exteriorIncidenceIso_hom_source, FiniteCorrespondenceGenerator.graphPostcompositionMap_fst,
      V.exteriorIdentitySchemeIso_hom_projection]
  · simp only [Category.assoc, FiniteCorrespondenceGenerator.incidenceMap_snd,
      exteriorIncidenceIso_hom_target,
      FiniteCorrespondenceGenerator.graphPostcompositionMap_snd,
      V.exteriorIdentitySchemeIso_hom_targetProjection_assoc]
    exact V.exteriorParameterMap_target u

end Motivic.SimplexExteriorGraph

namespace Motivic
open _root_.AlgebraicGeometry.Scheme

/-- The Noetherian instance used in this module. -/
local instance graphInterchangeIncidenceNoetherian
    {k : Type u} [Field k] (T : SmoothSite (Spec (.of k))) :
    IsNoetherian ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsNoetherian T.left)

/-- The reduced scheme instance used in this module. -/
local instance graphInterchangeIncidenceReduced
    {k : Type u} [Field k] (T : SmoothSite (Spec (.of k))) :
    IsReduced ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsReduced T.left)

namespace SimplexExteriorGraph
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y T T' : SmoothSite (Spec (.of k))}
  (u : T ⟶ T') (V : FiniteCorrespondenceGenerator X.hom Y.hom)
  [GeometricallyIntegral T'.hom]
  (C : Set (SmoothSite.product X T).left)
  (hC : C ∈ irreducibleComponents (SmoothSite.product X T).left)
  (hV : Set.range (V.exteriorIdentitySource T) ⊆ C)

/-- The compatible actual component graph has the literal exterior support as its incidence. -/
def componentExteriorIncidenceIso :
    V.exteriorIdentitySupport T ≅
      (componentGraphGeneratorOver (X := (SmoothSite.product X T).left)
        (Y := (SmoothSite.product X T').left) (SmoothSite.productMap (𝟙 X) u).left
        (MorphismProperty.Over.w (SmoothSite.productMap (𝟙 X) u)) C hC).incidence
          (V.exteriorIdentityGenerator T') :=
  exteriorIncidenceIso u V _ (componentGraphGeneratorOver_projection_target _ _ _ _)
    (by simpa only [componentGraphGeneratorOver_range] using hV)

end SimplexExteriorGraph

end Motivic
