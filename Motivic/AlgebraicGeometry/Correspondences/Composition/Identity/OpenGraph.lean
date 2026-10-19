/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Graph.Stalks.RightTor
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Identity.Left.Tor
public import Motivic.Aglib.AlgebraicGeometry.Intersection.CoefficientStalkTransport

/-!
# Actual graph incidence along open support projections

An open immersion induces an isomorphism of the actual stalk rings at every
incidence point. The support-product maps therefore need only be open
immersions, not global isomorphisms. The same smooth diagonal equation list
is regular in the ambient stalk and weakly regular on the actual coefficient
module. All positive actual incidence Tor vanishes, and the actual finite
Euler coefficient equals the full incidence generic multiplicity.

Both right source projections and left target projections are covered. These
statements do not assert a componentwise identity law or substitute ordinary
cycles before the full Tor comparison has been proved.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace AlgebraicGeometry.Scheme.StalkTransport

variable {X Y : Scheme.{u}}

/- Pointed stalk maps of open immersions are actual ring isomorphisms. -/

/-- Open-immersion stalk transport preserves the identical regular image list. -/
theorem isWeaklyRegular_map_pointedMap_of_isOpenImmersion
    (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) (y : Y) (h : y = f x) {s : List (Y.presheaf.stalk y)}
    (hs : IsWeaklyRegular (Y.presheaf.stalk y) s) :
    IsWeaklyRegular (X.presheaf.stalk x) (s.map (pointedMap f x y h).hom) :=
  isWeaklyRegular_map_of_flat (pointedMap f x y h).hom
    (RingHom.Flat.of_bijective
      (asIso (pointedMap f x y h)).commRingCatIsoToRingEquiv.bijective) hs

end AlgebraicGeometry.Scheme.StalkTransport

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

section Stalks

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

/-- The actual right graph-product map is open when the second source projection is open. -/
instance supportProductToGraphProduct_isOpenImmersion [IsOpenImmersion B.projection] :
    IsOpenImmersion (A.supportProductToGraphProduct B) := by
  unfold supportProductToGraphProduct
  infer_instance

/-- The actual left graph-product map is open when the first target projection is open. -/
instance supportProductToLeftGraphProduct_isOpenImmersion
    [IsOpenImmersion A.targetProjection] :
    IsOpenImmersion (A.supportProductToLeftGraphProduct B) := by
  unfold supportProductToLeftGraphProduct
  infer_instance

/-- The actual graph-product stalk is the support-product stalk by an actual ring isomorphism. -/
noncomputable def incidenceOpenGraphStalkIso [IsOpenImmersion B.projection] (w : A.incidence B) :
    (pullback (A.targetProjection ≫ g) g).presheaf.stalk
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph A.targetProjection g
          (A.incidenceFst B w)) ≅
      (A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w) :=
  asIso (StalkTransport.pointedMap (A.supportProductToGraphProduct B)
    (A.incidenceToSupportProduct B w)
    (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph A.targetProjection g (A.incidenceFst
      B w))
    (A.incidenceGraphPoint_eq B w))

set_option backward.isDefEq.respectTransparency false in
/-- The two actual paths from the same diagonal stalk to the coefficient stalk agree. -/
theorem incidenceOpenDiagonalStalkMap_comp [IsOpenImmersion B.projection] (w : A.incidence B) :
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
      (A.incidenceOpenGraphStalkIso B w).hom := by
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
theorem incidenceSupportStalkModule_isWeaklyRegular_of_openGraphImage
    [IsOpenImmersion B.projection] (w : A.incidence B)
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
          (A.incidenceOpenGraphStalkIso B w).hom.hom := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro r _
    exact ConcreteCategory.congr_hom (A.incidenceOpenDiagonalStalkMap_comp B w) r
  rw [hlist]
  exact StalkTransport.isWeaklyRegular_map_pointedMap_of_isOpenImmersion
    (A.supportProductToGraphProduct B) (A.incidenceToSupportProduct B w)
    (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph A.targetProjection g (A.incidenceFst
      B w))
    (A.incidenceGraphPoint_eq B w) hrs


/-- The actual graph-product stalk is the support-product stalk by an actual ring isomorphism. -/
noncomputable def incidenceOpenLeftGraphStalkIso [IsOpenImmersion A.targetProjection]
    (w : A.incidence B) :
    (pullback (B.projection ≫ g) g).presheaf.stalk
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B
          w)) ≅
      (A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w) :=
  asIso (StalkTransport.pointedMap (A.supportProductToLeftGraphProduct B)
    (A.incidenceToSupportProduct B w)
    (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B w))
    (A.incidenceLeftGraphPoint_eq B w))

set_option backward.isDefEq.respectTransparency false in
/-- The two actual paths from the same diagonal stalk to the coefficient stalk agree. -/
theorem incidenceOpenLeftDiagonalStalkMap_comp [IsOpenImmersion A.targetProjection]
    (w : A.incidence B) :
    Diagonal.baseChangeStalkMap (correspondenceTriple_isPullback f g h)
        (A.incidenceInclusion B w) ≫
      Intersection.coefficientStalkMap
        (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
        (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
        (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w) =
    StalkTransport.pointedMap (leftGraphMiddlePair B.projection g)
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B
          w))
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
        (A.incidenceLeftGraphMiddlePoint_eq B w) ≫
      (A.incidenceOpenLeftGraphStalkIso B w).hom := by
  change StalkTransport.pointedMap (correspondenceMiddlePair f g h) _ _
      (congrArg (fun q => q (A.incidenceInclusion B w))
        (correspondenceTriple_isPullback f g h).w) ≫
      StalkTransport.pointedMap (A.supportProductInclusion B) _ _
        (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w) =
    StalkTransport.pointedMap (leftGraphMiddlePair B.projection g) _ _
        (A.incidenceLeftGraphMiddlePoint_eq B w) ≫
      StalkTransport.pointedMap (A.supportProductToLeftGraphProduct B) _ _
        (A.incidenceLeftGraphPoint_eq B w)
  rw [StalkTransport.pointedMap_comp, StalkTransport.pointedMap_comp]
  exact StalkTransport.pointedMap_congr _ _ (A.supportProductInclusion_leftMiddlePair B) _ _ _ _

/-- Regularity of a diagonal list in the actual graph stalk gives regularity
of that identical list on the actual support-product coefficient module. -/
theorem incidenceSupportStalkModule_isWeaklyRegular_of_openLeftGraphImage
    [IsOpenImmersion A.targetProjection] (w : A.incidence B)
    (rs : List ((pullback g g).presheaf.stalk
      (pullback.diagonal g
        (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))))
    (hrs : IsWeaklyRegular
      ((pullback (B.projection ≫ g) g).presheaf.stalk
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B
          w)))
      (rs.map (StalkTransport.pointedMap (leftGraphMiddlePair B.projection g)
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B
          w))
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
        (A.incidenceLeftGraphMiddlePoint_eq B w)).hom)) :
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
      (rs.map (StalkTransport.pointedMap (leftGraphMiddlePair B.projection g)
        (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B
          w))
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
        (A.incidenceLeftGraphMiddlePoint_eq B w)).hom).map
          (A.incidenceOpenLeftGraphStalkIso B w).hom.hom := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro r _
    exact ConcreteCategory.congr_hom (A.incidenceOpenLeftDiagonalStalkMap_comp B w) r
  rw [hlist]
  exact StalkTransport.isWeaklyRegular_map_pointedMap_of_isOpenImmersion
    (A.supportProductToLeftGraphProduct B) (A.incidenceToSupportProduct B w)
    (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd B w))
    (A.incidenceLeftGraphPoint_eq B w) hrs


end Stalks

section RegularLists

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)
  [Flat f] [Smooth g] [IsSeparated g] [Flat h] [IsOpenImmersion B.projection]

set_option backward.isDefEq.respectTransparency false in
/-- Smooth graph coordinates give one actual diagonal list whose flat ambient
images generate the triple kernel and are regular on the actual coefficient module. -/
theorem exists_incidence_regular_list_of_isOpenImmersion_projection (w : A.incidence B) :
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
    A.incidenceSupportStalkModule_isWeaklyRegular_of_openGraphImage B w rs
      hgraph.toIsWeaklyRegular⟩

/-- A right graph has no positive genuine incidence Tor, at every actual incidence point. -/
theorem isZero_incidenceTor_succ_of_isOpenImmersion_projection (w : A.incidence B) (n : ℕ) :
    IsZero (A.incidenceTor B w (n + 1)) := by
  obtain ⟨s, hker, hs, hT⟩ :=
    A.exists_incidence_regular_list_of_isOpenImmersion_projection B w
  exact Intersection.isZero_tor_succ_of_coefficient_regular
    (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
    (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
    (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w) s hker hs hT n

end RegularLists

section RegularLists

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)
  [Flat f] [Smooth g] [IsSeparated g] [Flat h] [IsOpenImmersion A.targetProjection]

set_option backward.isDefEq.respectTransparency false in
/-- Smooth graph coordinates give one actual diagonal list whose flat ambient
images generate the triple kernel and are regular on the actual coefficient module. -/
theorem exists_incidence_regular_list_of_isOpenImmersion_targetProjection (w : A.incidence B) :
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
        IsRegular ((pullback (B.projection ≫ g) g).presheaf.stalk
          (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g (A.incidenceSnd
            B w)))
          (rs.map (StalkTransport.pointedMap (leftGraphMiddlePair B.projection g)
            (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph B.projection g
              (A.incidenceSnd B w))
            (pullback.diagonal g
              (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
            (A.incidenceLeftGraphMiddlePoint_eq B w)).hom) := by
    dsimp only [StalkTransport.pointedMap]
    generalize_proofs hp
    revert hp
    rw [A.incidenceTripleMiddle_eq_snd B w]
    intros
    exact Graph.exists_common_regular_left_list_of_common B.projection g (A.incidenceSnd B w)
      (Graph.exists_common_regular_list_of_smooth B.projection g (A.incidenceSnd B w))
  obtain ⟨hregular, hkernel⟩ := Diagonal.mapped_equations_regular_kernel
    (correspondenceTriple_isPullback f g h) (A.incidenceInclusion B w) hrs hker
  exact ⟨_, hkernel, hregular,
    A.incidenceSupportStalkModule_isWeaklyRegular_of_openLeftGraphImage B w rs
      hgraph.toIsWeaklyRegular⟩

/-- A first support with open target projection has no positive genuine
incidence Tor, at every actual incidence point. -/
theorem isZero_incidenceTor_succ_of_isOpenImmersion_targetProjection (w : A.incidence B) (n : ℕ) :
    IsZero (A.incidenceTor B w (n + 1)) := by
  obtain ⟨s, hker, hs, hT⟩ :=
    A.exists_incidence_regular_list_of_isOpenImmersion_targetProjection B w
  exact Intersection.isZero_tor_succ_of_coefficient_regular
    (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
    (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
    (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w) s hker hs hT n

end RegularLists

section TorCycles

variable (k : Type u) [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- Every genuine right-graph Tor coefficient is the full incidence generic multiplicity. -/
theorem incidenceTorCoefficient_eq_genericMultiplicity_of_isOpenImmersion_projection
    [IsOpenImmersion B.projection] (x : genericPoints (A.incidence B)) :
    A.incidenceTorCoefficient (S := Spec (.of k)) B x = (genericMultiplicity x : ℤ) := by
  obtain ⟨s, hker, hs, hT⟩ :=
    A.exists_incidence_regular_list_of_isOpenImmersion_projection B x.val
  exact A.incidenceTorCoefficient_eq_genericMultiplicity_of_weaklyRegular k B x s hker hs hT

/-- A second support with open source projection has actual Tor incidence
correspondence equal to its full ordinary fundamental correspondence. -/
theorem incidenceTorCorrespondence_eq_fundamental_of_isOpenImmersion_projection
    [IsOpenImmersion B.projection] :
    A.incidenceTorCorrespondence k B = A.incidenceFundamentalCorrespondence k B := by
  unfold incidenceTorCorrespondence incidenceFundamentalCorrespondence
  apply congrArg (A.incidenceCycleAssembly k B)
  funext x
  exact A.incidenceTorCoefficient_eq_genericMultiplicity_of_isOpenImmersion_projection k B x



/-- Every actual Tor coefficient with an open first target projection is
the full incidence generic multiplicity. -/
theorem incidenceTorCoefficient_eq_genericMultiplicity_of_isOpenImmersion_targetProjection
    [IsOpenImmersion A.targetProjection] (x : genericPoints (A.incidence B)) :
    A.incidenceTorCoefficient (S := Spec (.of k)) B x = (genericMultiplicity x : ℤ) := by
  obtain ⟨s, hker, hs, hT⟩ :=
    A.exists_incidence_regular_list_of_isOpenImmersion_targetProjection B x.val
  exact A.incidenceTorCoefficient_eq_genericMultiplicity_of_weaklyRegular k B x s hker hs hT

/-- A first support with open target projection has actual Tor incidence
correspondence equal to its full ordinary fundamental correspondence. -/
theorem incidenceTorCorrespondence_eq_fundamental_of_isOpenImmersion_targetProjection
    [IsOpenImmersion A.targetProjection] :
    A.incidenceTorCorrespondence k B = A.incidenceFundamentalCorrespondence k B := by
  unfold incidenceTorCorrespondence incidenceFundamentalCorrespondence
  apply congrArg (A.incidenceCycleAssembly k B)
  funext x
  exact A.incidenceTorCoefficient_eq_genericMultiplicity_of_isOpenImmersion_targetProjection k B x


end TorCycles

end Motivic.FiniteCorrespondenceGenerator
