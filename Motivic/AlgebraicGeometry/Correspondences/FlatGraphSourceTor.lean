/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TransverseIncidenceCycle
public import Motivic.AlgebraicGeometry.Correspondences.LeftGraphStalk
public import Motivic.AlgebraicGeometry.Graph.Transversality
public import Motivic.AlgebraicGeometry.Correspondences.GraphFunctor

/-!
# Flat left graph incidence

Flatness of the first target projection kills positive incidence Tor on
the original scheme-theoretic support product, preserving all local lengths.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.FiniteCorrespondenceGenerator

section Stalks

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

/-- The actual coefficient-to-graph map is flat by base change of the first target. -/
instance supportProductToLeftGraphProduct_flat [Flat A.targetProjection] :
    Flat (A.supportProductToLeftGraphProduct B) := by
  unfold supportProductToLeftGraphProduct
  have : Flat (pullback.map (B.projection ≫ g) (A.targetProjection ≫ g)
      (B.projection ≫ g) g (𝟙 B.scheme) A.targetProjection (𝟙 S) (by simp) (by simp)) :=
    MorphismProperty.pullbackMap (P := @Flat) (inferInstanceAs (Flat (𝟙 B.scheme)))
      (inferInstanceAs (Flat A.targetProjection)) (by simp) (by simp)
  infer_instance

/-- The actual graph-to-coefficient stalk map, without an isomorphism assumption. -/
noncomputable def incidenceFlatLeftGraphStalkMap (w : A.incidence B) :
    (pullback (B.projection ≫ g) g).presheaf.stalk
        (correspondenceGraph B.projection g (A.incidenceSnd B w)) ⟶
      (A.supportProduct B).presheaf.stalk (A.incidenceToSupportProduct B w) :=
  StalkTransport.pointedMap (A.supportProductToLeftGraphProduct B)
    (A.incidenceToSupportProduct B w)
    (correspondenceGraph B.projection g (A.incidenceSnd B w))
    (A.incidenceLeftGraphPoint_eq B w)

set_option backward.isDefEq.respectTransparency false in
/-- The two actual paths from the same diagonal stalk to the coefficient stalk agree. -/
theorem incidenceFlatLeftDiagonalStalkMap_comp (w : A.incidence B) :
    Diagonal.baseChangeStalkMap (correspondenceTriple_isPullback f g h)
        (A.incidenceInclusion B w) ≫
      Intersection.coefficientStalkMap
        (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
        (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
        (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w) =
    StalkTransport.pointedMap (leftGraphMiddlePair B.projection g)
        (correspondenceGraph B.projection g (A.incidenceSnd B w))
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
        (A.incidenceLeftGraphMiddlePoint_eq B w) ≫
      A.incidenceFlatLeftGraphStalkMap B w := by
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
theorem incidenceSupportStalkModule_isWeaklyRegular_of_flat_leftGraphImage
    [Flat A.targetProjection] (w : A.incidence B)
    (rs : List ((pullback g g).presheaf.stalk
      (pullback.diagonal g
        (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))))
    (hrs : IsWeaklyRegular
      ((pullback (B.projection ≫ g) g).presheaf.stalk
        (correspondenceGraph B.projection g (A.incidenceSnd B w)))
      (rs.map (StalkTransport.pointedMap (leftGraphMiddlePair B.projection g)
        (correspondenceGraph B.projection g (A.incidenceSnd B w))
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
        (correspondenceGraph B.projection g (A.incidenceSnd B w))
        (pullback.diagonal g
          (correspondenceTripleMiddle f g h (A.incidenceInclusion B w)))
        (A.incidenceLeftGraphMiddlePoint_eq B w)).hom).map
          (A.incidenceFlatLeftGraphStalkMap B w).hom := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro r _
    exact ConcreteCategory.congr_hom (A.incidenceFlatLeftDiagonalStalkMap_comp B w) r
  rw [hlist]
  apply RegularSequence.isWeaklyRegular_map_of_flat
    (A.incidenceFlatLeftGraphStalkMap B w).hom _ hrs
  unfold incidenceFlatLeftGraphStalkMap StalkTransport.pointedMap
  exact RingHom.Flat.comp
    (RingHom.Flat.of_bijective
      ((pullback (B.projection ≫ g) g).presheaf.stalkCongr
        (.of_eq (A.incidenceLeftGraphPoint_eq B w))).commRingCatIsoToRingEquiv.bijective)
    (Flat.stalkMap (A.supportProductToLeftGraphProduct B) _)

end Stalks

section RegularLists

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)
  [Flat f] [Smooth g] [IsSeparated g] [Flat h] [Flat A.targetProjection]

set_option backward.isDefEq.respectTransparency false in
/-- Smooth graph coordinates give one actual diagonal list whose flat ambient
images generate the triple kernel and are regular on the actual coefficient module. -/
theorem exists_incidence_regular_list_of_flat_targetProjection (w : A.incidence B) :
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
          (correspondenceGraph B.projection g (A.incidenceSnd B w)))
          (rs.map (StalkTransport.pointedMap (leftGraphMiddlePair B.projection g)
            (correspondenceGraph B.projection g (A.incidenceSnd B w))
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
    A.incidenceSupportStalkModule_isWeaklyRegular_of_flat_leftGraphImage B w rs
      hgraph.toIsWeaklyRegular⟩

/-- A flat first target projection has no positive genuine incidence Tor
at every actual incidence point. -/
theorem isZero_incidenceTor_succ_of_flat_targetProjection (w : A.incidence B) (n : ℕ) :
    IsZero (A.incidenceTor B w (n + 1)) := by
  obtain ⟨s, hker, hs, hT⟩ := A.exists_incidence_regular_list_of_flat_targetProjection B w
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
theorem incidenceTorCoefficient_eq_genericMultiplicity_of_flat_targetProjection
    [Flat A.targetProjection] (x : genericPoints (A.incidence B)) :
    A.incidenceTorCoefficient (S := Spec (.of k)) B x = (genericMultiplicity x : ℤ) := by
  obtain ⟨s, hker, hs, hT⟩ := A.exists_incidence_regular_list_of_flat_targetProjection B x.val
  exact A.incidenceTorCoefficient_eq_genericMultiplicity_of_weaklyRegular k B x s hker hs hT

/-- A first support with flat source projection has actual Tor incidence
correspondence equal to its full ordinary fundamental correspondence. -/
theorem incidenceTorCorrespondence_eq_fundamental_of_flat_targetProjection
    [Flat A.targetProjection] :
    A.incidenceTorCorrespondence k B = A.incidenceFundamentalCorrespondence k B := by
  unfold incidenceTorCorrespondence incidenceFundamentalCorrespondence
  apply congrArg (A.incidenceCycleAssembly k B)
  funext x
  exact A.incidenceTorCoefficient_eq_genericMultiplicity_of_flat_targetProjection k B x

end TorCycles


end Motivic.FiniteCorrespondenceGenerator
