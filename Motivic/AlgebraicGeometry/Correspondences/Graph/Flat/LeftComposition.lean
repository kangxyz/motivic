/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.TransverseCycle
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Stalks.Right
public import Motivic.Aglib.AlgebraicGeometry.Graph.Transversality
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Functor

/-!
# Flat-source incidence and actual left-graph fiber cycles

Flatness of the second support's source projection transports one original
smooth diagonal list from its graph ambient stalk to the actual coefficient
stalk. The literal higher incidence Tor groups vanish, and the actual Tor
correspondence equals the whole incidence fundamental correspondence.

For a left graph this incidence is the scheme-theoretic pullback of the
second support. All original generic local lengths are retained, including
nonreduced fibers; no reduced or separable fiber is substituted. The categorical
graph formula uses an integral smooth source, including every base-field point;
the Tor comparison itself holds for arbitrary first generators.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

section Stalks

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

/-- The actual coefficient-to-graph map is flat by base change of the second source. -/
instance supportProductToGraphProduct_flat [Flat B.projection] :
    Flat (A.supportProductToGraphProduct B) := by
  exact MorphismProperty.pullbackMap (P := @Flat) (inferInstanceAs (Flat (𝟙 A.scheme)))
    (inferInstanceAs (Flat B.projection)) (by simp) rfl

/-- The actual graph-to-coefficient stalk map, without an isomorphism assumption. -/
noncomputable def incidenceFlatGraphStalkMap (w : A.incidence B) :
    (pullback (A.targetProjection ≫ g) g).presheaf.stalk
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph A.targetProjection g
          (A.incidenceFst B w)) ⟶
      (A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w) :=
  StalkTransport.pointedMap (A.supportProductToGraphProduct B)
    (A.incidenceToSupportProduct B w)
    (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph A.targetProjection g (A.incidenceFst
      B w))
    (A.incidenceGraphPoint_eq B w)

set_option backward.isDefEq.respectTransparency false in
/-- The two actual paths from the same diagonal stalk to the coefficient stalk agree. -/
theorem incidenceFlatDiagonalStalkMap_comp (w : A.incidence B) :
    Diagonal.baseChangeStalkMap (correspondenceTriple_isPullback f g h)
        (A.incidenceInclusion B w) ≫
      Intersection.coefficientStalkMap
        (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
        (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
        (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w) =
    StalkTransport.pointedMap (graphMiddlePair A.targetProjection g)
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph A.targetProjection g
          (A.incidenceFst B w))
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
        (A.incidenceGraphMiddlePoint_eq B w) ≫
      A.incidenceFlatGraphStalkMap B w := by
  change StalkTransport.pointedMap (correspondenceMiddlePair f g h) _ _
      (congrArg (fun q => q (A.incidenceInclusion B w))
        (correspondenceTriple_isPullback f g h).w) ≫
      StalkTransport.pointedMap (A.supportProductInclusion B) _ _
        (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w) =
    StalkTransport.pointedMap (graphMiddlePair A.targetProjection g) _ _
        (A.incidenceGraphMiddlePoint_eq B w) ≫
      StalkTransport.pointedMap (A.supportProductToGraphProduct B) _ _
        (A.incidenceGraphPoint_eq B w)
  rw [StalkTransport.pointedMap_comp, StalkTransport.pointedMap_comp]
  exact StalkTransport.pointedMap_congr _ _ (A.supportProductInclusion_middlePair B) _ _ _ _

/-- Regularity of a diagonal list in the actual graph stalk gives regularity
of that identical list on the actual support-product coefficient module. -/
theorem incidenceSupportStalkModule_isWeaklyRegular_of_flat_graphImage
    [Flat B.projection] (w : A.incidence B)
    (rs : List ((pullback g g).presheaf.stalk
      (pullback.diagonal g
        (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))))
    (hrs : IsWeaklyRegular
      ((pullback (A.targetProjection ≫ g) g).presheaf.stalk
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph A.targetProjection g
          (A.incidenceFst B w)))
      (rs.map (StalkTransport.pointedMap (graphMiddlePair A.targetProjection g)
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph A.targetProjection g
          (A.incidenceFst B w))
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
        (A.incidenceGraphMiddlePoint_eq B w)).hom)) :
    IsWeaklyRegular (A.incidenceSupportStalkModule B w)
      (rs.map (Diagonal.baseChangeStalkMap (correspondenceTriple_isPullback f g h)
        (A.incidenceInclusion B w)).hom) := by
  apply (Intersection.coefficientStalkModule_isWeaklyRegular_iff _ _ _ _ _ _).mpr
  have hlist :
      (rs.map (Diagonal.baseChangeStalkMap (correspondenceTriple_isPullback f g h)
        (A.incidenceInclusion B w)).hom).map
          (Intersection.coefficientStalkMap
            (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
            (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
            (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w)).hom =
      (rs.map (StalkTransport.pointedMap (graphMiddlePair A.targetProjection g)
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph A.targetProjection g
          (A.incidenceFst B w))
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
        (A.incidenceGraphMiddlePoint_eq B w)).hom).map
          (A.incidenceFlatGraphStalkMap B w).hom := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro r _
    exact ConcreteCategory.congr_hom (A.incidenceFlatDiagonalStalkMap_comp B w) r
  rw [hlist]
  apply isWeaklyRegular_map_of_flat
    (A.incidenceFlatGraphStalkMap B w).hom _ hrs
  unfold incidenceFlatGraphStalkMap StalkTransport.pointedMap
  exact RingHom.Flat.comp
    (RingHom.Flat.of_bijective
      ((pullback (A.targetProjection ≫ g) g).presheaf.stalkCongr
        (.of_eq (A.incidenceGraphPoint_eq B w))).commRingCatIsoToRingEquiv.bijective)
    (Flat.stalkMap (A.supportProductToGraphProduct B) _)

end Stalks

section RegularLists

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)
  [Flat f] [Smooth g] [IsSeparated g] [Flat h] [Flat B.projection]

set_option backward.isDefEq.respectTransparency false in
/-- Smooth graph coordinates give one actual diagonal list whose flat ambient
images generate the triple kernel and are regular on the actual coefficient module. -/
theorem exists_incidence_regular_list_of_flat_projection (w : A.incidence B) :
    ∃ s : List (A.incidenceAmbientStalk B w),
      RingHom.ker ((correspondenceTripleInclusion f g h).stalkMap
        (A.incidenceInclusion B w)).hom = Ideal.ofList s ∧
      IsRegular (A.incidenceAmbientStalk B w) s ∧
      IsWeaklyRegular (A.incidenceSupportStalkModule B w) s := by
  obtain ⟨rs, hrs, hker, hgraph⟩ :
      ∃ rs : List ((pullback g g).presheaf.stalk
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))),
        IsRegular ((pullback g g).presheaf.stalk
          (pullback.diagonal g
            (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))) rs ∧
        RingHom.ker ((pullback.diagonal g).stalkMap
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w))).hom = Ideal.ofList rs ∧
        IsRegular ((pullback (A.targetProjection ≫ g) g).presheaf.stalk
          (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph A.targetProjection g
            (A.incidenceFst B w)))
          (rs.map (StalkTransport.pointedMap (graphMiddlePair A.targetProjection g)
            (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph A.targetProjection g
              (A.incidenceFst B w))
            (pullback.diagonal g
              (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
            (A.incidenceGraphMiddlePoint_eq B w)).hom) := by
    dsimp only [StalkTransport.pointedMap]
    generalize_proofs hp
    revert hp
    rw [A.incidenceTripleMiddle_apply B w]
    intros
    exact Graph.exists_common_regular_list_of_smooth A.targetProjection g (A.incidenceFst B w)
  obtain ⟨hregular, hkernel⟩ := Diagonal.mapped_equations_regular_kernel
    (correspondenceTriple_isPullback f g h) (A.incidenceInclusion B w) hrs hker
  exact ⟨_, hkernel, hregular,
    A.incidenceSupportStalkModule_isWeaklyRegular_of_flat_graphImage B w rs
      hgraph.toIsWeaklyRegular⟩

/-- A flat second source projection has no positive genuine incidence Tor
at every actual incidence point. -/
theorem isZero_incidenceTor_succ_of_flat_projection (w : A.incidence B) (n : ℕ) :
    IsZero (A.incidenceTor B w (n + 1)) := by
  obtain ⟨s, hker, hs, hT⟩ := A.exists_incidence_regular_list_of_flat_projection B w
  exact Intersection.isZero_tor_succ_of_coefficient_regular
    (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
    (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
    (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w) s hker hs hT n

end RegularLists

section TorCycles

variable (k : Type u) [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- Every genuine flat-source incidence Tor coefficient is the full
incidence generic multiplicity. -/
theorem incidenceTorCoefficient_eq_genericMultiplicity_of_flat_projection
    [Flat B.projection] (x : genericPoints (A.incidence B)) :
    A.incidenceTorCoefficient (S := Spec (.of k)) B x = (genericMultiplicity x : ℤ) := by
  obtain ⟨s, hker, hs, hT⟩ := A.exists_incidence_regular_list_of_flat_projection B x.val
  exact A.incidenceTorCoefficient_eq_genericMultiplicity_of_weaklyRegular k B x s hker hs hT

/-- A second support with flat source projection has actual Tor incidence
correspondence equal to its full ordinary fundamental correspondence. -/
theorem incidenceTorCorrespondence_eq_fundamental_of_flat_projection [Flat B.projection] :
    A.incidenceTorCorrespondence k B = A.incidenceFundamentalCorrespondence k B := by
  unfold incidenceTorCorrespondence incidenceFundamentalCorrespondence
  apply congrArg (A.incidenceCycleAssembly k B)
  funext x
  exact A.incidenceTorCoefficient_eq_genericMultiplicity_of_flat_projection k B x

end TorCycles

section GraphPullback

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (B : FiniteCorrespondenceGenerator g h) (φ : X ⟶ Y) (wφ : φ ≫ g = f)

/-- The literal whole scheme-theoretic fiber of a correspondence support. -/
noncomputable abbrev graphPullback : Scheme.{u} := pullback φ B.projection

/-- The whole fiber maps to the source-target product using its original projections. -/
noncomputable def graphPullbackMap : B.graphPullback φ ⟶ pullback f h :=
  pullback.lift (pullback.fst φ B.projection)
    (pullback.snd φ B.projection ≫ B.targetProjection) (by
      rw [← wφ, ← Category.assoc, pullback.condition, Category.assoc, B.projection_base]
      simp only [Category.assoc])

@[reassoc (attr := simp)]
theorem graphPullbackMap_fst :
    B.graphPullbackMap φ wφ ≫ pullback.fst f h = pullback.fst φ B.projection :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graphPullbackMap_snd :
    B.graphPullbackMap φ wφ ≫ pullback.snd f h =
      pullback.snd φ B.projection ≫ B.targetProjection :=
  pullback.lift_snd _ _ _

instance [IsSeparated h] : IsFinite (B.graphPullbackMap φ wφ) := by
  have : IsFinite (B.graphPullbackMap φ wφ ≫ pullback.fst f h) := by
    simpa only [graphPullbackMap_fst] using
      (inferInstance : IsFinite (pullback.fst φ B.projection))
  exact IsFinite.of_comp (B.graphPullbackMap φ wφ) (pullback.fst f h)

instance [IsNoetherian X] : IsNoetherian (B.graphPullback φ) :=
  isNoetherian_of_finiteType (pullback.fst φ B.projection)

variable [IsIntegral X] [IsSeparated g]

/-- The actual graph incidence is the whole unreduced support pullback. -/
noncomputable def leftGraphIncidenceIso :
    (graphGeneratorOver φ wφ).incidence B ≅ B.graphPullback φ :=
  asIso (pullback.map (graphGeneratorOver φ wφ).targetProjection B.projection
    φ B.projection (graphGeneratorOver φ wφ).projection (𝟙 B.scheme) (𝟙 Y)
    (by simpa only [Category.comp_id] using
      (graphGeneratorOver_projection_target φ wφ).symm) (by simp))

@[reassoc (attr := simp)]
theorem leftGraphIncidenceIso_hom_fst :
    (B.leftGraphIncidenceIso φ wφ).hom ≫ pullback.fst φ B.projection =
      (graphGeneratorOver φ wφ).incidenceFst B ≫ (graphGeneratorOver φ wφ).projection := by
  simp only [leftGraphIncidenceIso, asIso_hom, pullback.map, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem leftGraphIncidenceIso_hom_snd :
    (B.leftGraphIncidenceIso φ wφ).hom ≫ pullback.snd φ B.projection =
      (graphGeneratorOver φ wφ).incidenceSnd B := by
  simp only [leftGraphIncidenceIso, asIso_hom, pullback.map, pullback.lift_snd,
    Category.comp_id]

/-- The actual incidence map factors through the whole fiber isomorphism. -/
theorem incidenceMap_graph_left :
    (graphGeneratorOver φ wφ).incidenceMap B =
      (B.leftGraphIncidenceIso φ wφ).hom ≫ B.graphPullbackMap φ wφ := by
  apply pullback.hom_ext
  · simp only [incidenceMap_fst, Category.assoc, graphPullbackMap_fst,
      leftGraphIncidenceIso_hom_fst]
  · simp only [incidenceMap_snd, Category.assoc, graphPullbackMap_snd,
      leftGraphIncidenceIso_hom_snd_assoc]

end GraphPullback

section GraphCycles

/-- The Noetherian instance used in this module. -/
local instance flatLeftCompositionNoetherian
    {k : Type u} [Field k] (T : SmoothSite (Spec (.of k))) :
    IsNoetherian ((𝟭 Scheme).obj T.left) := inferInstanceAs (IsNoetherian T.left)

/-- The reduced scheme instance used in this module. -/
local instance flatLeftCompositionReduced {k : Type u} [Field k] (T : SmoothSite (Spec (.of k))) :
    IsReduced ((𝟭 Scheme).obj T.left) := inferInstanceAs (IsReduced T.left)

local instance {k : Type u} [Field k] (T : SmoothSite (Spec (.of k)))
    [IsIntegral T.left] : IsIntegral ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsIntegral T.left)

variable (k : Type u) [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (φ : X.left ⟶ Y.left) (wφ : φ ≫ Y.hom = X.hom)
  [IsIntegral X.left] [Flat B.projection]

/-- Precomposition by an actual graph gives the complete scheme-theoretic fiber
fundamental cycle, with all original nonreduced generic local lengths. -/
theorem toIntegralCycle_incidenceTorCorrespondence_graph_left :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)
      ((graphGeneratorOver φ wφ).incidenceTorCorrespondence k (Z := Z) B) =
      IntegralCycle.finitePushforward (B.graphPullbackMap φ wφ)
        (fundamentalCycle (B.graphPullback φ)) := by
  rw [(graphGeneratorOver φ wφ).incidenceTorCorrespondence_eq_fundamental_of_flat_projection
    k (Z := Z) B]
  rw [(graphGeneratorOver φ wφ).toIntegralCycle_incidenceFundamentalCorrespondence k B]
  simp only [B.incidenceMap_graph_left φ wφ, IntegralCycle.finitePushforward_comp,
    AddMonoidHom.comp_apply, finitePushforward_fundamentalCycle]

/-- The categorical graph functor and the actual correspondence composition
compute the whole fiber fundamental cycle. -/
theorem toIntegralCycle_graphFunctor_comp (α : X ⟶ Y) :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)
      ((Cor.graphFunctor k).map α ≫
          (show Cor.mk Y ⟶ Cor.mk Z from B.cycle)) =
      IntegralCycle.finitePushforward (B.graphPullbackMap α.left (MorphismProperty.Over.w α))
        (fundamentalCycle (B.graphPullback α.left)) := by
  change FiniteCorrespondence.toIntegralCycle
    (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
      (componentGraphCycleOver α.left (MorphismProperty.Over.w α)) B.cycle) = _
  rw [componentGraphCycleOver_eq_graphGeneratorOver_cycle,
    FiniteCorrespondence.incidenceTorPairing_cycle]
  exact B.toIntegralCycle_incidenceTorCorrespondence_graph_left k α.left (MorphismProperty.Over.w α)

/-- The generic Tor coefficient is the length of the original fiber stalk,
transported only through the actual graph-incidence isomorphism. -/
theorem incidenceTorCoefficient_graph_left_eq_fiberMultiplicity
    (x : genericPoints ((graphGeneratorOver φ wφ).incidence B)) :
    (graphGeneratorOver φ wφ).incidenceTorCoefficient (S := Spec (.of k)) B x =
      (Scheme.genericMultiplicity (mapGenericPoint (B.leftGraphIncidenceIso φ wφ).hom x) : ℤ) := by
  rw [(graphGeneratorOver φ wφ).incidenceTorCoefficient_eq_genericMultiplicity_of_flat_projection
    k B, genericMultiplicity_mapGenericPoint]

end GraphCycles

end Motivic.FiniteCorrespondenceGenerator
