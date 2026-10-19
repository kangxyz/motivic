/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.TransverseCycle
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Stalks.Left
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Identity.Left.Fundamental
public import Motivic.Aglib.AlgebraicGeometry.Graph.LeftPair
public import Motivic.Aglib.AlgebraicGeometry.Graph.Transversality

/-!
# Genuine left-identity diagonal-Tor incidence law

The first support's isomorphic target projection identifies the coefficient
scheme with a transposed graph ambient product. One common smooth diagonal
list is transported through the actual diagonal symmetry, then through the
actual flat ambient and support-product scalar maps. Thus the same ambient
kernel list is weakly regular on the actual coefficient module.

Positive actual Tor vanishes, its Euler coefficient is the full incidence
multiplicity, and actual left identity incidence gives the original cycle.
Integrality of the smooth source is used only to represent its identity by
one genuine generator. The target can remain disconnected; this does not
construct a componentwise identity or a complete correspondence category.
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
  [Flat f] [Smooth g] [IsSeparated g] [Flat h] [IsIso A.targetProjection]

set_option backward.isDefEq.respectTransparency false in
/-- Smooth graph coordinates give one actual diagonal list whose flat ambient
images generate the triple kernel and are regular on the actual coefficient module. -/
theorem exists_incidence_regular_list_of_isIso_targetProjection (w : A.incidence B) :
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
    A.incidenceSupportStalkModule_isWeaklyRegular_of_leftGraphImage B w rs
      hgraph.toIsWeaklyRegular⟩

/-- A first support with isomorphic target projection has no positive genuine
incidence Tor, at every actual incidence point. -/
theorem isZero_incidenceTor_succ_of_isIso_targetProjection (w : A.incidence B) (n : ℕ) :
    IsZero (A.incidenceTor B w (n + 1)) := by
  obtain ⟨s, hker, hs, hT⟩ := A.exists_incidence_regular_list_of_isIso_targetProjection B w
  exact Intersection.isZero_tor_succ_of_coefficient_regular
    (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
    (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
    (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w) s hker hs hT n

end RegularLists

section TorCycles

variable (k : Type u) [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- Every actual Tor coefficient with an isomorphic first target projection is
the full incidence generic multiplicity. -/
theorem incidenceTorCoefficient_eq_genericMultiplicity_of_isIso_targetProjection
    [IsIso A.targetProjection] (x : genericPoints (A.incidence B)) :
    A.incidenceTorCoefficient (S := Spec (.of k)) B x = (genericMultiplicity x : ℤ) := by
  obtain ⟨s, hker, hs, hT⟩ := A.exists_incidence_regular_list_of_isIso_targetProjection B x.val
  exact A.incidenceTorCoefficient_eq_genericMultiplicity_of_weaklyRegular k B x s hker hs hT

/-- A first support with isomorphic target projection has actual Tor incidence
correspondence equal to its full ordinary fundamental correspondence. -/
theorem incidenceTorCorrespondence_eq_fundamental_of_isIso_targetProjection
    [IsIso A.targetProjection] :
    A.incidenceTorCorrespondence k B = A.incidenceFundamentalCorrespondence k B := by
  unfold incidenceTorCorrespondence incidenceFundamentalCorrespondence
  apply congrArg (A.incidenceCycleAssembly k B)
  funext x
  exact A.incidenceTorCoefficient_eq_genericMultiplicity_of_isIso_targetProjection k B x

end TorCycles

variable (k : Type u) [Field k]
  {X Y : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)

/-- The actual diagonal-Tor operation has the genuine single-generator left unit. -/
theorem incidenceTorCorrespondence_identity_left [IsIntegral ((𝟭 Scheme).obj X.left)] :
    (identityGenerator X.hom).incidenceTorCorrespondence k A = A.cycle := by
  rw [(identityGenerator X.hom).incidenceTorCorrespondence_eq_fundamental_of_isIso_targetProjection
      k,
    A.incidenceFundamentalCorrespondence_identity_left k]

end Motivic.FiniteCorrespondenceGenerator

namespace Motivic.FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}

/-- The biadditive actual diagonal-Tor pairing has the single identity graph
as left unit on every signed finite correspondence cycle. -/
theorem incidenceTorPairing_identity_left [IsIntegral ((𝟭 Scheme).obj X.left)]
    (α : FiniteCorrespondence X.hom Y.hom) :
    incidenceTorPairing k (X := X) (Y := X) (Z := Y) (identityGenerator X.hom).cycle α = α := by
  have heq : incidenceTorPairing k (X := X) (Y := X) (Z := Y)
      (identityGenerator X.hom).cycle = AddMonoidHom.id (FiniteCorrespondence X.hom Y.hom) := by
    apply Finsupp.addHom_ext
    intro A n
    change incidenceTorPairing k (X := X) (Y := X) (Z := Y)
      (Finsupp.single (identityGenerator X.hom) 1) (Finsupp.single A n) = Finsupp.single A n
    rw [incidenceTorPairing_single, A.incidenceTorCorrespondence_identity_left k]
    simp [FiniteCorrespondenceGenerator.cycle]
  exact congrArg (fun f => f α) heq

end Motivic.FiniteCorrespondence
