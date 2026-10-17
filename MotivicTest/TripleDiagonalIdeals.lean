/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleDiagonalIdeals
public import Motivic.AlgebraicGeometry.Correspondences.TripleGenericDominance
public import Motivic.AlgebraicGeometry.Intersection.GenericTor
public import Motivic.Algebra.Homology.KoszulTwoListOrderComparison

/-!
# Actual triple-incidence two-list consumers

At a genuine triple generic point the two lists are constructed on the actual
middle self-products and mapped to the same six-factor stalk. The original
exterior coefficient stalk, actual final kernel and genuine generic support
supply the Artinian quotient and maximal-ideal hypotheses. The two actual
fixed-support replacement sums then agree without a comparison assumption.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.TripleDiagonalIdeals

open Intersection

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The literal six-factor ambient stalk at the actual triple point. -/
abbrev actualAmbient (w : F.tripleIncidence G H) :=
  ambientStalk
    (correspondenceSecondDiagonalInclusion X.hom Y.hom Z.hom W.hom ≫
      correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom)
    (F.tripleIncidenceFourfoldInclusion G H w)

/-- The actual exterior coefficient stalk with its literal six-factor action. -/
abbrev actualCoefficient (w : F.tripleIncidence G H) : ModuleCat (actualAmbient k F G H w) :=
  coefficientStalkModule
    (correspondenceSecondDiagonalInclusion X.hom Y.hom Z.hom W.hom ≫
      correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom)
    (F.tripleIncidenceFourfoldInclusion G H w) (F.tripleSupportProductInclusion G H)
    ((F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateToTripleSupport G H) w)
    (point_eq _ _ _ _ (F.tripleIncidence_sixfold_isPullback G H) w)

instance actualCoefficient_finite (w : F.tripleIncidence G H) :
    Module.Finite (actualAmbient k F G H w) (actualCoefficient k F G H w) :=
  inferInstanceAs (Module.Finite _ (coefficientStalkModule _ _ _ _ _))

/-- The original six-factor ambient is locally Noetherian from actual smooth
finite-type structure maps; no finiteness of a support over another is used. -/
instance actualAmbient_noetherian (w : F.tripleIncidence G H) :
    IsNoetherianRing (actualAmbient k F G H w) := by
  have : IsLocallyNoetherian ((𝟭 Scheme).obj W.left) :=
    inferInstanceAs (IsLocallyNoetherian W.left)
  have : IsLocallyNoetherian (pullback Z.hom W.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Z.hom W.hom)
  have : LocallyOfFiniteType
      (correspondenceAmbientTarget X.hom Y.hom Z.hom ≫ Z.hom) := by
    dsimp only [correspondenceAmbientTarget]
    infer_instance
  have : IsLocallyNoetherian (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd (correspondenceAmbientTarget X.hom Y.hom Z.hom ≫ Z.hom)
        (pullback.fst Z.hom W.hom ≫ Z.hom))
  infer_instance

/-- The coefficient annihilator is the original exterior support ideal at the
same actual ambient point, not the ideal of a reduced support. -/
theorem actualCoefficient_annihilator (w : F.tripleIncidence G H) :
    Module.annihilator (actualAmbient k F G H w) (actualCoefficient k F G H w) =
      (F.tripleSupportProductInclusion G H).ker.stalk
        (F.tripleIncidenceSixfoldInclusion G H w) := by
  dsimp only [actualAmbient, actualCoefficient]
  rw [coefficientStalkModule_annihilator, coefficientStalkMap,
    CommRingCat.hom_comp, ← RingHom.comap_ker,
    ← (F.tripleSupportProductInclusion G H).ker_stalk,
    Scheme.IdealSheafData.stalk_congr_comap]
  · rfl
  · exact point_eq _ _ _ _ (F.tripleIncidence_sixfold_isPullback G H) w

/-- The actual final stalk kernel contains exactly the two middle ideals and
the actual coefficient annihilator, with every term in one ambient ring. -/
theorem actualFinalKernel (w : F.tripleIncidence G H) :
    let p := F.tripleIncidenceSixfoldInclusion G H w
    RingHom.ker ((F.tripleIncidenceSixfoldInclusion G H).stalkMap w).hom =
      (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).ker.stalk p ⊔
        ((correspondenceSecondAmbientInclusion X.hom Y.hom Z.hom W.hom).ker.stalk p ⊔
          Module.annihilator (actualAmbient k F G H w) (actualCoefficient k F G H w)) := by
  rw [actualCoefficient_annihilator]
  exact F.stalkKernel_tripleIncidenceSixfold_eq_threeIdeals G H w

/-- The actual final generic kernel quotient is Artinian before choosing any
middle equations. -/
theorem actualFinalKernelArtinian (w : genericPoints (F.tripleIncidence G H)) :
    IsArtinianRing ((actualAmbient k F G H w.1) ⧸
      RingHom.ker ((F.tripleIncidenceSixfoldInclusion G H).stalkMap w.1).hom) := by
  have : IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsLocallyNoetherian X.left)
  have := LocallyOfFiniteType.isLocallyNoetherian (F.tripleIncidenceSource G H)
  exact stalk_quotient_ker_isArtinian (F.tripleIncidenceSixfoldInclusion G H) w.1 w.2

/-- Genuine triple generic points supply actual common middle lists, a true
Artinian final quotient, both maximal-ideal conditions, and equality of the
two actual fixed-support replacement sums. -/
theorem actualTwoListOrder (w : genericPoints (F.tripleIncidence G H)) :
    ∃ (s t : List (actualAmbient k F G H w.1))
      (hArt : IsArtinianRing ((actualAmbient k F G H w.1) ⧸
        (Ideal.ofList s ⊔ (Ideal.ofList t ⊔ Module.annihilator (actualAmbient k F G H w.1)
          (actualCoefficient k F G H w.1))))),
      (∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal (actualAmbient k F G H w.1)) ∧
      (∀ a ∈ t, a ∈ IsLocalRing.maximalIdeal (actualAmbient k F G H w.1)) ∧
      (letI := hArt
       letI := Koszul.twoList_swappedArtinian (actualCoefficient k F G H w.1) s t
       Koszul.twoListFixedSupportSum (actualCoefficient k F G H w.1) s t =
         Koszul.twoListFixedSupportSum (actualCoefficient k F G H w.1) t s) := by
  let p := F.tripleIncidenceSixfoldInclusion G H w.1
  obtain ⟨t₀, s₀, -, -, ht, hs⟩ := exists_common_middle_diagonalLists
    X.hom Y.hom Z.hom W.hom (F.tripleIncidenceFourfoldInclusion G H w.1)
  let t := t₀.map ((correspondenceSixfoldFirstMiddlePair X.hom Y.hom Z.hom W.hom).stalkMap p).hom
  let s := s₀.map ((correspondenceSixfoldSecondMiddlePair X.hom Y.hom Z.hom W.hom).stalkMap p).hom
  change (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).ker.stalk
    (F.tripleIncidenceSixfoldInclusion G H w.1) = Ideal.ofList t at ht
  change (correspondenceSecondAmbientInclusion X.hom Y.hom Z.hom W.hom).ker.stalk
    (F.tripleIncidenceSixfoldInclusion G H w.1) = Ideal.ofList s at hs
  have hk : RingHom.ker ((F.tripleIncidenceSixfoldInclusion G H).stalkMap w.1).hom =
      Ideal.ofList s ⊔ (Ideal.ofList t ⊔
        Module.annihilator (actualAmbient k F G H w.1) (actualCoefficient k F G H w.1)) := by
    rw [actualFinalKernel k F G H w.1, ht, hs, sup_left_comm]
  have hArt : IsArtinianRing ((actualAmbient k F G H w.1) ⧸
      (Ideal.ofList s ⊔ (Ideal.ofList t ⊔
        Module.annihilator (actualAmbient k F G H w.1) (actualCoefficient k F G H w.1)))) := by
    rw [← hk]
    exact actualFinalKernelArtinian k F G H w
  have hmax := IsLocalRing.le_maximalIdeal
    (RingHom.ker_ne_top ((F.tripleIncidenceSixfoldInclusion G H).stalkMap w.1).hom)
  have hsmax : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal (actualAmbient k F G H w.1) := by
    intro a ha
    apply hmax
    rw [hk]
    exact Ideal.mem_sup_left (Ideal.subset_span ha)
  have htmax : ∀ a ∈ t, a ∈ IsLocalRing.maximalIdeal (actualAmbient k F G H w.1) := by
    intro a ha
    apply hmax
    rw [hk]
    exact Ideal.mem_sup_right (Ideal.mem_sup_left (Ideal.subset_span ha))
  refine ⟨s, t, hArt, hsmax, htmax, ?_⟩
  exact @Koszul.twoListFixedSupportSum_order (actualAmbient k F G H w.1)
    _ _ _ (actualCoefficient k F G H w.1) _ s t hArt hsmax htmax

end Motivic.MotivicTest.TripleDiagonalIdeals
