/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.TransverseCycle
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Stalks.Right
public import Motivic.Aglib.AlgebraicGeometry.Graph.Transversality
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.ClosedSubscheme

/-!
# Right graph and identity incidence multiplicities

A single smooth diagonal equation list is regular in the actual ambient stalk
and, after its literal scalar map, weakly regular on the actual support-product
coefficient stalk. Consequently all positive actual Tor vanish and the genuine
right-graph Tor coefficient is the full incidence generic multiplicity.
The ordinary identity incidence calculation then gives the actual right unit.
The integral-middle hypothesis is used only to represent the identity by a
single graph generator; no smooth scheme is assumed integral in general.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

section RegularLists

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)
  [Flat f] [Smooth g] [IsSeparated g] [Flat h] [IsIso B.projection]

set_option backward.isDefEq.respectTransparency false in
/-- Smooth graph coordinates give one actual diagonal list whose flat ambient
images generate the triple kernel and are regular on the actual coefficient module. -/
theorem exists_incidence_regular_list_of_isIso_projection (w : A.incidence B) :
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
    A.incidenceSupportStalkModule_isWeaklyRegular_of_graphImage B w rs
      hgraph.toIsWeaklyRegular⟩

/-- A right graph has no positive genuine incidence Tor, at every actual incidence point. -/
theorem isZero_incidenceTor_succ_of_isIso_projection (w : A.incidence B) (n : ℕ) :
    IsZero (A.incidenceTor B w (n + 1)) := by
  obtain ⟨s, hker, hs, hT⟩ := A.exists_incidence_regular_list_of_isIso_projection B w
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
theorem incidenceTorCoefficient_eq_genericMultiplicity_of_isIso_projection
    [IsIso B.projection] (x : genericPoints (A.incidence B)) :
    A.incidenceTorCoefficient (S := Spec (.of k)) B x = (genericMultiplicity x : ℤ) := by
  obtain ⟨s, hker, hs, hT⟩ := A.exists_incidence_regular_list_of_isIso_projection B x.val
  exact A.incidenceTorCoefficient_eq_genericMultiplicity_of_weaklyRegular k B x s hker hs hT

/-- A second support with isomorphic source projection has actual Tor incidence
correspondence equal to its full ordinary fundamental correspondence. -/
theorem incidenceTorCorrespondence_eq_fundamental_of_isIso_projection [IsIso B.projection] :
    A.incidenceTorCorrespondence k B = A.incidenceFundamentalCorrespondence k B := by
  unfold incidenceTorCorrespondence incidenceFundamentalCorrespondence
  apply congrArg (A.incidenceCycleAssembly k B)
  funext x
  exact A.incidenceTorCoefficient_eq_genericMultiplicity_of_isIso_projection k B x

/-- Actual right graph generators satisfy the genuine Tor multiplicity comparison. -/
theorem incidenceTorCorrespondence_graph_right
    (ψ : ((𝟭 Scheme).obj Y.left) ⟶ ((𝟭 Scheme).obj Z.left))
    (hw : ψ ≫ Z.hom = Y.hom) [IsIntegral ((𝟭 Scheme).obj Y.left)] :
    A.incidenceTorCorrespondence k (Z := Z)
      (graphGeneratorOver (f := Y.hom) (g := Z.hom) ψ hw) =
      A.incidenceFundamentalCorrespondence k (Z := Z)
      (graphGeneratorOver (f := Y.hom) (g := Z.hom) ψ hw) :=
  A.incidenceTorCorrespondence_eq_fundamental_of_isIso_projection k (Z := Z)
    (graphGeneratorOver (f := Y.hom) (g := Z.hom) ψ hw)

end TorCycles

variable (k : Type u) [Field k]
  {X Y : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)

/-- The full ordinary incidence cycle with a single diagonal generator is the
original integral support, with its literal multiplicity one. -/
theorem incidenceFundamentalCorrespondence_identity_right [IsIntegral ((𝟭 Scheme).obj Y.left)] :
    A.incidenceFundamentalCorrespondence k (identityGenerator Y.hom) = A.cycle := by
  have : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  have : IsNoetherian A.scheme := isNoetherian_of_finiteType A.projection
  have : IsNoetherian (pullback X.hom Y.hom) :=
    isNoetherian_of_finiteType (pullback.fst X.hom Y.hom)
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [A.toIntegralCycle_incidenceFundamentalCorrespondence k]
  simp only [A.incidenceMap_identity_right, IntegralCycle.finitePushforward_comp]
  change IntegralCycle.finitePushforward A.inclusion
    (IntegralCycle.finitePushforward A.rightIdentityIncidenceIso.hom
      (fundamentalCycle (A.incidence (identityGenerator Y.hom)))) =
    FiniteCorrespondence.toIntegralCycle A.cycle
  rw [finitePushforward_fundamentalCycle, FiniteCorrespondenceGenerator.cycle,
    FiniteCorrespondence.toIntegralCycle_single]
  change closedFundamentalCycle A.val =
    Finsupp.single A.toIntegralClosedSubscheme 1
  rw [closedFundamentalCycle_of_isIntegral]
  rfl

/-- The actual diagonal-Tor incidence operation has the genuine single-generator
right unit, obtained from proved coefficient regularity and full stalk multiplicity. -/
theorem incidenceTorCorrespondence_identity_right [IsIntegral ((𝟭 Scheme).obj Y.left)] :
    A.incidenceTorCorrespondence k (identityGenerator Y.hom) = A.cycle := by
  rw [A.incidenceTorCorrespondence_eq_fundamental_of_isIso_projection k,
    A.incidenceFundamentalCorrespondence_identity_right k]

end Motivic.FiniteCorrespondenceGenerator

namespace Motivic.FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}

/-- The biadditive actual diagonal-Tor pairing has the single identity graph
as right unit on every signed finite correspondence cycle. -/
theorem incidenceTorPairing_identity_right [IsIntegral ((𝟭 Scheme).obj Y.left)]
    (α : FiniteCorrespondence X.hom Y.hom) :
    incidenceTorPairing k (X := X) (Y := Y) (Z := Y) α (identityGenerator Y.hom).cycle = α := by
  have heq : (incidenceTorPairing k (X := X) (Y := Y) (Z := Y)).flip
      (identityGenerator Y.hom).cycle = AddMonoidHom.id (FiniteCorrespondence X.hom Y.hom) := by
    apply Finsupp.addHom_ext
    intro A n
    change incidenceTorPairing k (X := X) (Y := Y) (Z := Y)
      (Finsupp.single A n) (Finsupp.single (identityGenerator Y.hom) 1) = Finsupp.single A n
    rw [incidenceTorPairing_single, A.incidenceTorCorrespondence_identity_right k]
    simp [FiniteCorrespondenceGenerator.cycle]
  exact congrArg (fun f => f α) heq

end Motivic.FiniteCorrespondence
