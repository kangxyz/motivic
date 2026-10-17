/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IntegralExteriorClosedFiber
public import Motivic.AlgebraicGeometry.Cycles.FundamentalInvariance
public import Motivic.AlgebraicGeometry.Cycles.GenericFinitePushforward
public import Motivic.AlgebraicGeometry.Cycles.GenericStalkPoints
public import Motivic.AlgebraicGeometry.Intersection.WholeFiberTorGeneric

/-!
# The actual whole-open Tor cycle and its component exteriors

Restrict the unreduced exterior of every original reduced component support to
an actual open of the whole exterior. Their closed immersions partition the
whole-open generic points. The original component index is recovered by the
flat exterior projection, before any finite image is taken.

Generic preservation of these particular support immersions is proved, not
assumed: an ambient generization projects to the same original generic point,
lifts through the Cartesian support square, and then equals the given point
by genericity and the embedding's reflection of specialization. No normality,
separability, unique tensor branch, or generic preservation of arbitrary finite
maps is used.

The actual ambient closed-fiber quotient and the actual open support stalk are
compared using the original immersion and open-stalk maps. The full regular
stalk length is retained. A finite reindexing then identifies the EXISTING
whole first-stage Tor cycle with the restricted Tor-weighted component sum.
This stops before finite-image/open-restriction compatibility, the remaining
diagonal, or identification with an iterated incidence pairing.

SOURCE-ONLY PROPOSAL: no elaboration, compilation, or acceptance is claimed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.WholeFiberTorExteriorDecomposition

/-- A genuine component generic point has no strict generization. -/
theorem eq_of_specializes_generic {P : Scheme.{u}} {x y : P}
    (hy : y ∈ genericPoints P) (h : x ⤳ y) : x = y :=
  (h.antisymm (specializes_iff_closure_subset.mpr
    (hy.2 isIrreducible_singleton.closure h.closure_subset))).eq

variable {P S T : Scheme.{u}} (p : P ⟶ S) (t : T ⟶ S)

/-- The full exterior of one original component's reduced integral support. -/
abbrev componentExterior (z : genericPoints P) : Scheme.{u} :=
  (IntegralClosedSubscheme.pointClosure z.1).exteriorProduct p t

/-- Its literal Cartesian closed immersion, before any open restriction. -/
abbrev componentExteriorInclusion (z : genericPoints P) :
    componentExterior p t z ⟶ pullback p t :=
  (IntegralClosedSubscheme.pointClosure z.1).exteriorInclusion p t

/-- Restriction to the given actual whole-exterior open; nilpotents are retained. -/
abbrev componentOpen (U : (pullback p t : Scheme.{u}).Opens) (z : genericPoints P) :=
  (componentExteriorInclusion p t z ⁻¹ᵁ U).toScheme

/-- The genuine support closed immersion into that same whole open. -/
abbrev componentInclusion (U : (pullback p t : Scheme.{u}).Opens) (z : genericPoints P) :
    componentOpen p t U z ⟶ U.toScheme :=
  componentExteriorInclusion p t z ∣_ U

instance componentInclusion_isClosedImmersion
    (U : (pullback p t : Scheme.{u}).Opens) (z : genericPoints P) :
    IsClosedImmersion (componentInclusion p t U z) := inferInstance

/-- The restricted support and its two actual open inclusions form a Cartesian square. -/
theorem componentInclusion_isPullback
    (U : (pullback p t : Scheme.{u}).Opens) (z : genericPoints P) :
    IsPullback (componentInclusion p t U z)
      (componentExteriorInclusion p t z ⁻¹ᵁ U).ι U.ι
      (componentExteriorInclusion p t z) :=
  isPullback_morphismRestrict _ _

/-- Both routes to the unreduced whole exterior are literally equal. -/
@[reassoc] theorem componentInclusion_ambient
    (U : (pullback p t : Scheme.{u}).Opens) (z : genericPoints P) :
    componentInclusion p t U z ≫ U.ι =
      (componentExteriorInclusion p t z ⁻¹ᵁ U).ι ≫ componentExteriorInclusion p t z :=
  morphismRestrict_ι _ _

variable [Flat t]

/-- A generic of an original-component exterior is genuinely generic in the
whole exterior. The proof uses the original Cartesian support, not finiteness. -/
theorem componentExterior_generic_mem (z : genericPoints P)
    (w : genericPoints (componentExterior p t z)) :
    componentExteriorInclusion p t z w.1 ∈ genericPoints (pullback p t : Scheme.{u}) := by
  let C := IntegralClosedSubscheme.pointClosure z.1
  let b := componentExteriorInclusion p t z
  have hproj : pullback.fst p t (b w.1) = z.1 := by
    calc
      pullback.fst p t (b w.1) = C.point :=
        C.exteriorGeneric_ambientProjection p t w
      _ = z.1 := IntegralClosedSubscheme.point_pointClosure z.1
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro s hs hws
  change closure {b w.1} ⊆ s at hws
  have hy : hs.genericPoint ⤳ b w.1 :=
    hs.isGenericPoint_genericPoint_closure.specializes
      (subset_closure (hws (subset_closure (by simp))))
  have hbase : pullback.fst p t hs.genericPoint = z.1 :=
    eq_of_specializes_generic z.2 (by
      simpa only [hproj] using hy.map (pullback.fst p t).continuous)
  have hpoint : C.val.subschemeι (genericPoint C.val.subscheme) =
      pullback.fst p t hs.genericPoint := by
    change C.point = _
    rw [IntegralClosedSubscheme.point_pointClosure, hbase]
  obtain ⟨y, _, hy'⟩ := Scheme.exists_preimage_of_isPullback
    (C.exteriorInclusion_isPullback p t) (genericPoint C.val.subscheme) hs.genericPoint hpoint
  have hyb : b y = hs.genericPoint := hy'
  have hyw : y ⤳ w.1 :=
    b.isEmbedding.isInducing.specializes_iff.mp (hyb.symm ▸ hy)
  have hyw' : y = w.1 := eq_of_specializes_generic w.2 hyw
  have hsame : hs.genericPoint = b w.1 := hyb.symm.trans (congrArg b hyw')
  rw [← hsame, hs.genericPoint_closure_eq]
  exact subset_closure

variable (U : (pullback p t : Scheme.{u}).Opens)

/-- The original whole-exterior generic point underlying an open generic. -/
def originalGeneric (w : genericPoints U.toScheme) : genericPoints (pullback p t : Scheme.{u}) :=
  ⟨w.1.1, mem_genericPoints_of_generalizing U.ι (Flat.generalizingMap _) w.1 w.2⟩

/-- The unique ORIGINAL component label is computed by the flat projection. -/
def componentGeneric (w : genericPoints U.toScheme) : genericPoints P :=
  ⟨pullback.fst p t w.1.1,
    mem_genericPoints_of_generalizing (pullback.fst p t) (Flat.generalizingMap _)
      w.1.1 (originalGeneric p t U w).2⟩

/-- The support-open generic retains its actual global exterior point. -/
def componentOriginalGeneric (z : genericPoints P)
    (w : genericPoints (componentOpen p t U z)) : genericPoints (componentExterior p t z) :=
  ⟨w.1.1, mem_genericPoints_of_generalizing
    (componentExteriorInclusion p t z ⁻¹ᵁ U).ι (Flat.generalizingMap _) w.1 w.2⟩

/-- These specific restricted closed immersions preserve generic points. -/
theorem componentInclusion_generic_mem (z : genericPoints P)
    (w : genericPoints (componentOpen p t U z)) :
    componentInclusion p t U z w.1 ∈ genericPoints U.toScheme := by
  apply mem_genericPoints_of_preimmersion_image U.ι
  change (componentInclusion p t U z w.1).1 ∈ genericPoints (pullback p t : Scheme.{u})
  rw [morphismRestrict_base_coe]
  exact componentExterior_generic_mem p t z (componentOriginalGeneric p t U z w)

/-- The actual inclusion on generic points, keeping the original component index. -/
def genericInclusion (z : genericPoints P) (w : genericPoints (componentOpen p t U z)) :
    genericPoints U.toScheme :=
  ⟨componentInclusion p t U z w.1, componentInclusion_generic_mem p t U z w⟩

/-- The original pair label of every included branch is precisely its index. -/
@[simp] theorem componentGeneric_genericInclusion (z : genericPoints P)
    (w : genericPoints (componentOpen p t U z)) :
    componentGeneric p t U (genericInclusion p t U z w) = z := by
  apply Subtype.ext
  change pullback.fst p t ((componentInclusion p t U z w.1).1) = z.1
  rw [morphismRestrict_base_coe]
  calc
    pullback.fst p t (componentExteriorInclusion p t z w.1.1) =
        (IntegralClosedSubscheme.pointClosure z.1).point :=
      (IntegralClosedSubscheme.pointClosure z.1).exteriorGeneric_ambientProjection p t
        (componentOriginalGeneric p t U z w)
    _ = z.1 := IntegralClosedSubscheme.point_pointClosure z.1

/-- Every whole-open generic has a lift in its own original component exterior.
This is all-branch coverage, with no chosen branch after finite projection. -/
theorem exists_genericInclusion_eq (w : genericPoints U.toScheme) :
    ∃ v : genericPoints (componentOpen p t U (componentGeneric p t U w)),
      genericInclusion p t U (componentGeneric p t U w) v = w := by
  let z := componentGeneric p t U w
  let C := IntegralClosedSubscheme.pointClosure z.1
  have hpoint : C.val.subschemeι (genericPoint C.val.subscheme) = pullback.fst p t w.1.1 := by
    change C.point = _
    exact IntegralClosedSubscheme.point_pointClosure z.1
  obtain ⟨v, _, hv⟩ := Scheme.exists_preimage_of_isPullback
    (C.exteriorInclusion_isPullback p t) (genericPoint C.val.subscheme) w.1.1 hpoint
  have hmem : componentExteriorInclusion p t z v ∈ U := hv.symm ▸ w.1.2
  let v' : componentOpen p t U z := ⟨v, hmem⟩
  have hinc : componentInclusion p t U z v' = w.1 := by
    apply Subtype.ext
    exact (morphismRestrict_base_coe _ _ v').trans hv
  have hgeneric : v' ∈ genericPoints (componentOpen p t U z) :=
    mem_genericPoints_of_preimmersion_image (componentInclusion p t U z) v'
      (hinc.symm ▸ w.2)
  exact ⟨⟨v', hgeneric⟩, Subtype.ext hinc⟩

/-- The literal disjoint-union map is injective AND surjective. Distinct
original labels cannot overlap at a source generic, even if their images collide. -/
theorem genericInclusion_bijective :
    Function.Bijective (fun a : Σ z : genericPoints P, genericPoints (componentOpen p t U z) =>
      genericInclusion p t U a.1 a.2) := by
  constructor
  · rintro ⟨z, v⟩ ⟨z', v'⟩ h
    have hz : z = z' := by
      simpa only [componentGeneric_genericInclusion] using
        congrArg (componentGeneric p t U) h
    subst z'
    have hv : v = v' := by
      apply Subtype.ext
      apply (componentInclusion p t U z).isEmbedding.injective
      exact congrArg Subtype.val h
    subst v'
    rfl
  · intro w
    obtain ⟨v, hv⟩ := exists_genericInclusion_eq p t U w
    exact ⟨⟨componentGeneric p t U w, v⟩, hv⟩

/-- The complete nonoverlapping actual generic-point partition, before finite image. -/
def genericPartition :
    (Σ z : genericPoints P, genericPoints (componentOpen p t U z)) ≃
      genericPoints U.toScheme :=
  Equiv.ofBijective _ (genericInclusion_bijective p t U)

/-- The inverse partition recovers the literal original flat-projection label. -/
@[simp] theorem genericPartition_symm_fst (w : genericPoints U.toScheme) :
    ((genericPartition p t U).symm w).1 = componentGeneric p t U w := by
  have h := componentGeneric_genericInclusion p t U
    ((genericPartition p t U).symm w).1 ((genericPartition p t U).symm w).2
  change componentGeneric p t U (genericPartition p t U ((genericPartition p t U).symm w)) = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The support immersion's actual open-stalk comparison is an isomorphism of
ARROWS: both structure rings and the original scalar map commute. -/
def componentInclusionStalkArrowIso (z : genericPoints P) (w : componentOpen p t U z) :
    Arrow.mk ((componentInclusion p t U z).stalkMap w) ≅
      Arrow.mk ((componentExteriorInclusion p t z).stalkMap w.1) :=
  morphismRestrictStalkMap _ _ _

/-- The original ambient closed-fiber quotient is the actual restricted support
stalk, via the original support quotient followed by the actual open-stalk map. -/
def closedFiberOpenEquiv (z : genericPoints P)
    (w : genericPoints (componentOpen p t U z)) :
    Koszul.coefficientClosedFiber
        ((pullback.fst p t).stalkMap (componentExteriorInclusion p t z w.1.1)).hom ≃+*
      (componentOpen p t U z).presheaf.stalk w.1 :=
  ((IntegralClosedSubscheme.pointClosure z.1).exteriorGenericClosedFiberEquiv p t
    (componentOriginalGeneric p t U z w)).trans
      ((componentExteriorInclusion p t z ⁻¹ᵁ U).stalkIso w.1).symm.commRingCatIsoToRingEquiv

/-- The quotient comparison retains every original ambient numerator and its
literal support/open scalar maps. In particular it is not an abstract ring choice. -/
theorem closedFiberOpenEquiv_mk (z : genericPoints P)
    (w : genericPoints (componentOpen p t U z))
    (r : (pullback p t : Scheme.{u}).presheaf.stalk
      (componentExteriorInclusion p t z w.1.1)) :
    closedFiberOpenEquiv p t U z w (Ideal.Quotient.mk _ r) =
      ((componentExteriorInclusion p t z ⁻¹ᵁ U).ι.stalkMap w.1)
        (((componentExteriorInclusion p t z).stalkMap w.1.1) r) := by
  change ((componentExteriorInclusion p t z ⁻¹ᵁ U).stalkIso w.1).inv
      ((IntegralClosedSubscheme.pointClosure z.1).exteriorGenericClosedFiberEquiv p t
        (componentOriginalGeneric p t U z w) (Ideal.Quotient.mk _ r)) = _
  rw [IntegralClosedSubscheme.exteriorGenericClosedFiberEquiv_mk,
    Scheme.Opens.stalkIso_inv]
  rfl

/-- The complete scalar square is the actual ambient immersion map followed
by the actual open immersion map, on every numerator. -/
theorem closedFiberOpenEquiv_scalarSquare (z : genericPoints P)
    (w : genericPoints (componentOpen p t U z)) :
    (closedFiberOpenEquiv p t U z w).toRingHom.comp (Ideal.Quotient.mk _) =
      ((componentExteriorInclusion p t z ⁻¹ᵁ U).ι.stalkMap w.1).hom.comp
        ((componentExteriorInclusion p t z).stalkMap w.1.1).hom := by
  ext r
  exact closedFiberOpenEquiv_mk p t U z w r

/-- Length is first computed over the original ambient stalk, then transported
through the genuine open-stalk isomorphism. No nilpotent is discarded. -/
theorem closedFiberOpen_length (z : genericPoints P)
    (w : genericPoints (componentOpen p t U z)) :
    Module.length ((pullback p t : Scheme.{u}).presheaf.stalk
        (componentExteriorInclusion p t z w.1.1))
        (Koszul.coefficientClosedFiber
          ((pullback.fst p t).stalkMap (componentExteriorInclusion p t z w.1.1)).hom) =
      Module.length ((componentOpen p t U z).presheaf.stalk w.1)
        ((componentOpen p t U z).presheaf.stalk w.1) :=
  ((IntegralClosedSubscheme.pointClosure z.1).exteriorGenericClosedFiber_length p t
    (componentOriginalGeneric p t U z w)).trans
      (stalk_length_eq_of_isOpenImmersion
        (componentExteriorInclusion p t z ⁻¹ᵁ U).ι w.1)

variable [IsNoetherian P] [IsNoetherian U.toScheme]

instance componentOpen_isNoetherian (z : genericPoints P) :
    IsNoetherian (componentOpen p t U z) :=
  isNoetherian_of_finiteType (componentInclusion p t U z)

omit [AlgebraicGeometry.IsNoetherian P] in
/-- The closed-fiber length is finite BEFORE any conversion to an integer. -/
theorem closedFiber_length_ne_top (w : genericPoints U.toScheme) :
    Module.length ((pullback p t : Scheme.{u}).presheaf.stalk w.1.1)
      (Koszul.coefficientClosedFiber ((pullback.fst p t).stalkMap w.1.1).hom) ≠ ⊤ := by
  obtain ⟨v, hv⟩ := exists_genericInclusion_eq p t U w
  have hpoint : componentExteriorInclusion p t (componentGeneric p t U w) v.1.1 =
      w.1.1 := (morphismRestrict_base_coe _ _ v.1).symm.trans
        (congrArg (fun q : genericPoints U.toScheme => q.1.1) hv)
  have hlen := closedFiberOpen_length p t U (componentGeneric p t U w) v
  rw [hpoint] at hlen
  rw [hlen]
  exact stalk_length_ne_top_of_mem_genericPoints v.1 v.2

/-- The unreduced original ambient closed-fiber length, with finiteness proved above. -/
def closedFiberMultiplicity (w : genericPoints U.toScheme) : ℤ :=
  LengthEuler.integerLength
    (Koszul.coefficientClosedFiber ((pullback.fst p t).stalkMap w.1.1).hom)
    (closedFiber_length_ne_top p t U w)

omit [AlgebraicGeometry.IsNoetherian P] in
/-- Every actual support-open branch contributes its full generic multiplicity. -/
theorem closedFiberMultiplicity_genericInclusion (z : genericPoints P)
    (w : genericPoints (componentOpen p t U z)) :
    closedFiberMultiplicity p t U (genericInclusion p t U z w) =
      (genericMultiplicity w : ℤ) := by
  have hpoint : (genericInclusion p t U z w).1.1 =
      componentExteriorInclusion p t z w.1.1 :=
    morphismRestrict_base_coe _ _ w.1
  unfold closedFiberMultiplicity LengthEuler.integerLength genericMultiplicity
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
    ((congrArg (fun x : (pullback p t : Scheme.{u}) =>
      Module.length ((pullback p t : Scheme.{u}).presheaf.stalk x)
        (Koszul.coefficientClosedFiber ((pullback.fst p t).stalkMap x).hom)) hpoint).trans
      (closedFiberOpen_length p t U z w))

/-- The genuine whole-open closed-fiber coefficient cycle is the finite sum of
ALL restricted original-component fundamental cycles, with arbitrary signed weights. -/
theorem ofGenericCoefficients_eq_component_sum (c : genericPoints P → ℤ) :
    letI := IntegralCycle.genericPointFintype P
    IntegralCycle.ofGenericCoefficients U.toScheme
        (fun w => c (componentGeneric p t U w) * closedFiberMultiplicity p t U w) =
      ∑ z : genericPoints P, c z •
        IntegralCycle.finitePushforward (componentInclusion p t U z)
          (fundamentalCycle (componentOpen p t U z)) := by
  classical
  let := IntegralCycle.genericPointFintype P
  let := IntegralCycle.genericPointFintype U.toScheme
  let componentGenericFintypes : ∀ z : genericPoints P,
      Fintype (genericPoints (componentOpen p t U z)) :=
    fun z => IntegralCycle.genericPointFintype (componentOpen p t U z)
  rw [IntegralCycle.ofGenericCoefficients_eq_sum]
  rw [← (genericPartition p t U).sum_comp
    (fun w => Finsupp.single (IntegralClosedSubscheme.pointClosure w.1)
      (c (componentGeneric p t U w) * closedFiberMultiplicity p t U w))]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  rw [← IntegralCycle.ofGenericCoefficients_genericMultiplicity,
    IntegralCycle.ofGenericCoefficients_eq_sum, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w _
  change Finsupp.single (IntegralClosedSubscheme.pointClosure
      (componentInclusion p t U z w.1))
      (c (componentGeneric p t U (genericInclusion p t U z w)) *
        closedFiberMultiplicity p t U (genericInclusion p t U z w)) = _
  rw [componentGeneric_genericInclusion, closedFiberMultiplicity_genericInclusion]
  simp only [IntegralCycle.finitePushforward_single,
    IntegralClosedSubscheme.point_pointClosure, IntegralClosedSubscheme.pointClosure_finiteImage,
    residueDegree_of_surjectiveOnStalks, Nat.cast_one, mul_one, Finsupp.smul_single,
    zsmul_eq_mul, Int.cast_id]

end Motivic.WholeFiberTorExteriorDecomposition

namespace Motivic.FiniteCorrespondenceGenerator

open WholeFiberTorExteriorDecomposition

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (V : (F.leftIntermediateImageProduct G H).affineOpens)

local instance wholeExterior_factorFlat : Flat (H.projection ≫ Z.hom) := by
  let : Subsingleton (Spec (.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : IsIntegral (Spec (.of k)) := inferInstance
  exact Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIntegral
    (Y := Spec (.of k)) (H.projection ≫ Z.hom)

/-- Restrict the original pair component exterior to the actual whole inverse-image open. -/
abbrev firstStageComponentExteriorOpen (z : genericPoints (F.incidence G)) :=
  componentOpen (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom)
    ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V) z

/-- Its literal closed immersion into the existing whole-open Tor coefficient scheme. -/
abbrev firstStageComponentExteriorInclusion (z : genericPoints (F.incidence G)) :
    F.firstStageComponentExteriorOpen G H V z ⟶ F.firstStageWholeOpen G H V :=
  componentInclusion (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom)
    ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V) z

/-- The whole-open generic partition is by original pair-incidence generics,
with every exterior branch and no image-component quotienting. -/
def firstStageComponentExteriorGenericPartition :
    (Σ z : genericPoints (F.incidence G),
      genericPoints (F.firstStageComponentExteriorOpen G H V z)) ≃
        genericPoints (F.firstStageWholeOpen G H V) :=
  genericPartition (F.incidenceTarget G ≫ Z.hom) (H.projection ≫ Z.hom)
    ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V)

/-- The partition inverse is the EXISTING original pair label of the whole Tor API. -/
theorem firstStageComponentExteriorGenericPartition_symm_fst
    (w : genericPoints (F.firstStageWholeOpen G H V)) :
    ((F.firstStageComponentExteriorGenericPartition G H V).symm w).1 =
      F.firstStageWholeGenericPair G H V w :=
  genericPartition_symm_fst _ _ _ w

/-- Forward partitioning recovers the same original pair label, before any image map. -/
theorem firstStageWholeGenericPair_component
    (z : genericPoints (F.incidence G))
    (w : genericPoints (F.firstStageComponentExteriorOpen G H V z)) :
    F.firstStageWholeGenericPair G H V
        (F.firstStageComponentExteriorGenericPartition G H V ⟨z, w⟩) = z :=
  componentGeneric_genericInclusion _ _ _ z w

/-- The genuine whole-Tor closed-fiber multiplicity is the full multiplicity
of the corresponding actual restricted component-exterior stalk. -/
theorem firstStageWholeGenericFiberMultiplicity_component
    (z : genericPoints (F.incidence G))
    (w : genericPoints (F.firstStageComponentExteriorOpen G H V z)) :
    F.firstStageWholeGenericFiberMultiplicity G H V
        (F.firstStageComponentExteriorGenericPartition G H V ⟨z, w⟩) =
      (genericMultiplicity w : ℤ) :=
  closedFiberMultiplicity_genericInclusion _ _ _ z w

/-- The genuine all-degree whole-Tor sheaf coefficient equals the original
pair Tor weight times the full restricted exterior generic-stalk multiplicity. -/
theorem firstStageWholeTorGenericCoefficient_component
    (z : genericPoints (F.incidence G))
    (w : genericPoints (F.firstStageComponentExteriorOpen G H V z)) :
    F.firstStageWholeTorGenericCoefficient G H V
        (F.firstStageComponentExteriorGenericPartition G H V ⟨z, w⟩) =
      F.incidenceTorCoefficient (S := Spec (.of k)) G z * (genericMultiplicity w : ℤ) := by
  rw [F.firstStageWholeTorGenericCoefficient_eq_pair_mul G H V,
    F.firstStageWholeGenericPair_component G H V,
    F.firstStageWholeGenericFiberMultiplicity_component G H V]

/-- The existing whole first-stage Tor cycle is IDENTIFIED with the actual
restricted component-fundamental-cycle sum. This is a source cycle identity,
not an identification of an iterated incidence pairing. -/
theorem firstStageWholeTorGenericCycle_eq_componentExterior_sum :
    letI := IntegralCycle.genericPointFintype (F.incidence G)
    F.firstStageWholeTorGenericCycle G H V =
      ∑ z : genericPoints (F.incidence G),
        F.incidenceTorCoefficient (S := Spec (.of k)) G z •
          IntegralCycle.finitePushforward (F.firstStageComponentExteriorInclusion G H V z)
            (fundamentalCycle (F.firstStageComponentExteriorOpen G H V z)) := by
  rw [F.firstStageWholeTorGenericCycle_eq_pair_mul G H V]
  exact ofGenericCoefficients_eq_component_sum _ _ _
    (F.incidenceTorCoefficient (S := Spec (.of k)) G)

end Motivic.FiniteCorrespondenceGenerator
