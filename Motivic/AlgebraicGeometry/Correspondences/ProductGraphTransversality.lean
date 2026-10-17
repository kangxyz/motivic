/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Graph.Transversality
public import Motivic.AlgebraicGeometry.Graph.PointTransport

/-!
# A mixed product pair is a graph after a partial factor swap

The coefficient product `(X × T) × (V × T')` is reordered to
`(V × T) × (X × T')`. Swapping just the two `X` coordinates of the middle
self-product fixes its diagonal and turns the mixed pair into the graph pair
of `(p, u)`. A common regular diagonal list is transported through these
actual scheme isomorphisms. Only the middle scheme is required to be smooth;
the support `V`, the parameter map `u`, and the map `p` need not be flat.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.ProductGraph

section FourFactors

variable {S A B C D : Scheme.{u}}
  (a : A ⟶ S) (b : B ⟶ S) (c : C ⟶ S) (d : D ⟶ S)

/-- The structural morphism of a literal relative product. -/
abbrev productHom := pullback.fst a b ≫ a

/-- Four factors grouped into two literal relative products. -/
abbrev fourProduct := pullback (productHom a b) (productHom c d)

abbrev first : fourProduct a b c d ⟶ A :=
  pullback.fst _ _ ≫ pullback.fst a b

abbrev second : fourProduct a b c d ⟶ B :=
  pullback.fst _ _ ≫ pullback.snd a b

abbrev third : fourProduct a b c d ⟶ C :=
  pullback.snd _ _ ≫ pullback.fst c d

abbrev fourth : fourProduct a b c d ⟶ D :=
  pullback.snd _ _ ≫ pullback.snd c d

theorem first_base_second : first a b c d ≫ a = second a b c d ≫ b := by
  simp only [first, second, Category.assoc, pullback.condition]

theorem first_base_third : first a b c d ≫ a = third a b c d ≫ c := by
  simpa only [first, third, productHom, Category.assoc] using
    (pullback.condition (f := productHom a b) (g := productHom c d))

theorem first_base_fourth : first a b c d ≫ a = fourth a b c d ≫ d := by
  rw [first_base_third]
  simp only [third, fourth, Category.assoc, pullback.condition]

/-- Exchange the first and third factors, leaving both parameter factors fixed. -/
def partialSwap : fourProduct a b c d ⟶ fourProduct c b a d :=
  pullback.lift
    (pullback.lift (third a b c d) (second a b c d)
      ((first_base_third a b c d).symm.trans (first_base_second a b c d)))
    (pullback.lift (first a b c d) (fourth a b c d) (first_base_fourth a b c d))
    (by simp only [productHom, pullback.lift_fst_assoc];
        exact (first_base_third a b c d).symm)

@[reassoc (attr := simp)]
theorem partialSwap_first : partialSwap a b c d ≫ first c b a d = third a b c d := by
  simp only [partialSwap, first, pullback.lift_fst_assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem partialSwap_second : partialSwap a b c d ≫ second c b a d = second a b c d := by
  simp only [partialSwap, second, pullback.lift_fst_assoc, pullback.lift_snd]

@[reassoc (attr := simp)]
theorem partialSwap_third : partialSwap a b c d ≫ third c b a d = first a b c d := by
  simp only [partialSwap, third, pullback.lift_snd_assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem partialSwap_fourth : partialSwap a b c d ≫ fourth c b a d = fourth a b c d := by
  simp only [partialSwap, fourth, pullback.lift_snd_assoc, pullback.lift_snd]

/-- Maps into the four-factor product are determined by its four projections. -/
@[ext] theorem fourProduct_hom_ext {W : Scheme.{u}} {f g : W ⟶ fourProduct a b c d}
    (h₁ : f ≫ first a b c d = g ≫ first a b c d)
    (h₂ : f ≫ second a b c d = g ≫ second a b c d)
    (h₃ : f ≫ third a b c d = g ≫ third a b c d)
    (h₄ : f ≫ fourth a b c d = g ≫ fourth a b c d) : f = g := by
  apply pullback.hom_ext
  · exact pullback.hom_ext (by simpa only [first, Category.assoc] using h₁)
      (by simpa only [second, Category.assoc] using h₂)
  · exact pullback.hom_ext (by simpa only [third, Category.assoc] using h₃)
      (by simpa only [fourth, Category.assoc] using h₄)

@[simp] theorem partialSwap_comp :
    partialSwap a b c d ≫ partialSwap c b a d = 𝟙 _ := by
  apply fourProduct_hom_ext <;> simp

/-- The partial factor exchange is an actual scheme isomorphism. -/
def partialSwapIso : fourProduct a b c d ≅ fourProduct c b a d where
  hom := partialSwap a b c d
  inv := partialSwap c b a d
  hom_inv_id := partialSwap_comp a b c d
  inv_hom_id := partialSwap_comp c b a d

instance : IsIso (partialSwap a b c d) := (partialSwapIso a b c d).isIso_hom

end FourFactors

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary graph pair is the actual base change of the middle diagonal. -/
theorem graphPair_isPullback {S K M : Scheme.{u}} (φ : K ⟶ M) (g : M ⟶ S) :
    IsPullback φ (correspondenceGraph φ g) (pullback.diagonal g) (graphMiddlePair φ g) where
  w := (correspondenceGraph_middlePair φ g).symm
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    have h₁ := congrArg (fun q => q ≫ pullback.fst g g) s.condition
    have h₂ := congrArg (fun q => q ≫ pullback.snd g g) s.condition
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id,
      graphMiddlePair_fst] at h₁
    simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id,
      graphMiddlePair_snd] at h₂
    refine ⟨s.snd ≫ pullback.fst (φ ≫ g) g, ?_, ?_, ?_⟩
    · simpa only [PullbackCone.mk_fst, Category.assoc] using h₁.symm
    · apply pullback.hom_ext
      · simp only [PullbackCone.mk_snd, Category.assoc, correspondenceGraph_fst, Category.comp_id]
      · simpa only [PullbackCone.mk_snd, Category.assoc, correspondenceGraph_snd] using
          h₁.symm.trans h₂
    · intro m _ hm
      have hh := congrArg (fun q => q ≫ pullback.fst (φ ≫ g) g) hm
      simpa only [PullbackCone.mk_snd, Category.assoc, correspondenceGraph_fst,
        Category.comp_id] using hh)⟩

section MixedPair

variable {S X V T T' : Scheme.{u}}
  (f : X ⟶ S) (g : T' ⟶ S) (p : V ⟶ X) (u : T ⟶ T')

abbrev middle := pullback f g
abbrev middleHom := productHom f g
abbrev support := pullback (p ≫ f) (u ≫ g)
abbrev supportHom := productHom (p ≫ f) (u ≫ g)
abbrev coefficient := fourProduct f (u ≫ g) (p ≫ f) g

/-- The map from the arbitrary support times the original parameter to the middle scheme. -/
def supportMap : support f g p u ⟶ middle f g :=
  pullback.map (p ≫ f) (u ≫ g) f g p u (𝟙 S) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem supportMap_fst : supportMap f g p u ≫ pullback.fst f g =
    pullback.fst (p ≫ f) (u ≫ g) ≫ p := by
  simp only [supportMap, pullback.map, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem supportMap_snd : supportMap f g p u ≫ pullback.snd f g =
    pullback.snd (p ≫ f) (u ≫ g) ≫ u := by
  simp only [supportMap, pullback.map, pullback.lift_snd]

@[reassoc (attr := simp)]
theorem supportMap_over : supportMap f g p u ≫ middleHom f g = supportHom f g p u := by
  simp [middleHom, supportHom, productHom]

/-- The mixed pair `((x,u(t)),(p(v),t'))` in the actual middle self-product. -/
def mixedPair : coefficient f g p u ⟶ pullback (middleHom f g) (middleHom f g) :=
  pullback.lift
    (pullback.lift (first f (u ≫ g) (p ≫ f) g)
      (second f (u ≫ g) (p ≫ f) g ≫ u)
      (by simpa only [Category.assoc] using first_base_second f (u ≫ g) (p ≫ f) g))
    (pullback.lift (third f (u ≫ g) (p ≫ f) g ≫ p)
      (fourth f (u ≫ g) (p ≫ f) g)
      (by simpa only [third, fourth, Category.assoc] using
        congrArg (fun q => pullback.snd (productHom f (u ≫ g))
          (productHom (p ≫ f) g) ≫ q) (pullback.condition (f := p ≫ f) (g := g))))
    (by simpa only [middleHom, productHom, pullback.lift_fst_assoc, Category.assoc] using
      first_base_third f (u ≫ g) (p ≫ f) g)

/-- The coefficient reordering with the exact structural map used by the graph API. -/
def coefficientGraphIso : coefficient f g p u ≅
    pullback (supportMap f g p u ≫ middleHom f g) (middleHom f g) :=
  partialSwapIso f (u ≫ g) (p ≫ f) g ≪≫
    pullback.congrHom (supportMap_over f g p u).symm rfl

/-- The mixed incidence point, expressed through the actual graph and coefficient isomorphism. -/
def mixedEmbedding : support f g p u ⟶ coefficient f g p u :=
  correspondenceGraph (supportMap f g p u) (middleHom f g) ≫
    (coefficientGraphIso f g p u).inv

@[reassoc (attr := simp)]
theorem mixedEmbedding_first :
    mixedEmbedding f g p u ≫ first f (u ≫ g) (p ≫ f) g =
      pullback.fst (p ≫ f) (u ≫ g) ≫ p := by
  simp only [mixedEmbedding, coefficientGraphIso, Iso.trans_inv, partialSwapIso,
    Category.assoc, partialSwap_first, third, pullback.congrHom_inv, pullback.map,
    pullback.lift_snd_assoc, Category.comp_id, correspondenceGraph_snd_assoc, supportMap_fst]

@[reassoc (attr := simp)]
theorem mixedEmbedding_second :
    mixedEmbedding f g p u ≫ second f (u ≫ g) (p ≫ f) g =
      pullback.snd (p ≫ f) (u ≫ g) := by
  simp only [mixedEmbedding, coefficientGraphIso, Iso.trans_inv, partialSwapIso,
    Category.assoc, partialSwap_second, second, pullback.congrHom_inv, pullback.map,
    pullback.lift_fst_assoc, Category.comp_id, correspondenceGraph_fst_assoc]

@[reassoc (attr := simp)]
theorem mixedEmbedding_third :
    mixedEmbedding f g p u ≫ third f (u ≫ g) (p ≫ f) g =
      pullback.fst (p ≫ f) (u ≫ g) := by
  simp only [mixedEmbedding, coefficientGraphIso, Iso.trans_inv, partialSwapIso,
    Category.assoc, partialSwap_third, first, pullback.congrHom_inv, pullback.map,
    pullback.lift_fst_assoc, Category.comp_id, correspondenceGraph_fst_assoc]

@[reassoc (attr := simp)]
theorem mixedEmbedding_fourth :
    mixedEmbedding f g p u ≫ fourth f (u ≫ g) (p ≫ f) g =
      pullback.snd (p ≫ f) (u ≫ g) ≫ u := by
  simp only [mixedEmbedding, coefficientGraphIso, Iso.trans_inv, partialSwapIso,
    Category.assoc, partialSwap_fourth, fourth, pullback.congrHom_inv, pullback.map,
    pullback.lift_snd_assoc, Category.comp_id, correspondenceGraph_snd_assoc, supportMap_snd]

/-- The partial swap fixes the actual middle diagonal as a morphism. -/
@[reassoc (attr := simp)]
theorem diagonal_partialSwap :
    pullback.diagonal (middleHom f g) ≫ partialSwap f g f g =
      pullback.diagonal (middleHom f g) := by
  apply fourProduct_hom_ext <;>
    simp only [Category.assoc, partialSwap_first, partialSwap_second,
      partialSwap_third, partialSwap_fourth, first, second, third, fourth,
      pullback.diagonal_fst_assoc, pullback.diagonal_snd_assoc]

@[simp] theorem partialSwap_diagonal_apply (m : middle f g) :
    partialSwap f g f g (pullback.diagonal (middleHom f g) m) =
      pullback.diagonal (middleHom f g) m :=
  congrArg (fun q => q m) (diagonal_partialSwap f g)

/-- Reordering the coefficient factors gives the graph pair after the partial middle swap. -/
@[reassoc]
theorem mixedPair_partialSwap :
    mixedPair f g p u ≫ partialSwap f g f g =
      (coefficientGraphIso f g p u).hom ≫
        graphMiddlePair (supportMap f g p u) (middleHom f g) := by
  apply fourProduct_hom_ext <;>
    simp only [Category.assoc, first, second, third, fourth,
      mixedPair, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
      pullback.lift_fst, pullback.lift_snd, coefficientGraphIso, Iso.trans_hom,
      partialSwapIso, graphMiddlePair_fst_assoc, graphMiddlePair_snd_assoc,
      supportMap_fst, supportMap_snd, pullback.congrHom_hom, pullback.map,
      Category.comp_id, partialSwap]

/-- In the reverse direction the ordinary graph pair becomes the literal mixed pair. -/
@[reassoc]
theorem graphMiddlePair_partialSwap :
    graphMiddlePair (supportMap f g p u) (middleHom f g) ≫ partialSwap f g f g =
      (coefficientGraphIso f g p u).inv ≫ mixedPair f g p u := by
  apply (cancel_epi (coefficientGraphIso f g p u).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← mixedPair_partialSwap, Category.assoc, partialSwap_comp, Category.comp_id]

/-- The mixed embedding maps to exactly the middle diagonal. -/
@[reassoc]
theorem mixedEmbedding_mixedPair :
    mixedEmbedding f g p u ≫ mixedPair f g p u =
      supportMap f g p u ≫ pullback.diagonal (middleHom f g) := by
  rw [mixedEmbedding, Category.assoc, ← graphMiddlePair_partialSwap,
    ← Category.assoc, correspondenceGraph_middlePair, Category.assoc,
    diagonal_partialSwap]

/-- The arbitrary support times the original parameter is the full mixed incidence pullback. -/
theorem mixed_isPullback :
    IsPullback (supportMap f g p u) (mixedEmbedding f g p u)
      (pullback.diagonal (middleHom f g)) (mixedPair f g p u) := by
  apply (graphPair_isPullback (supportMap f g p u) (middleHom f g)).of_iso
    (Iso.refl _) (Iso.refl _) (coefficientGraphIso f g p u).symm
    (partialSwapIso f g f g)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp, mixedEmbedding]
  · simp only [partialSwapIso, diagonal_partialSwap, Iso.refl_hom, Category.id_comp]
  · exact graphMiddlePair_partialSwap f g p u

/-- The actual diagonal-to-mixed-coefficient scalar map, with its point identified. -/
def mixedDiagonalStalkMap (v : support f g p u) :
    (pullback (middleHom f g) (middleHom f g)).presheaf.stalk
      (pullback.diagonal (middleHom f g) (supportMap f g p u v)) ⟶
    (coefficient f g p u).presheaf.stalk (mixedEmbedding f g p u v) :=
  Graph.alignedStalkMap (mixedPair f g p u) (mixedEmbedding f g p u v)
    (pullback.diagonal (middleHom f g) (supportMap f g p u v))
    (congrArg (fun q => q v) (mixedEmbedding_mixedPair f g p u)).symm

set_option backward.isDefEq.respectTransparency false in
/-- One actual diagonal-kernel list is regular on the mixed coefficient product.
Only the middle structural morphism is smooth; `V`, `p`, and `u` are arbitrary. -/
theorem exists_common_regular_list [Smooth (middleHom f g)] (v : support f g p u) :
    ∃ rs : List ((pullback (middleHom f g) (middleHom f g)).presheaf.stalk
      (pullback.diagonal (middleHom f g) (supportMap f g p u v))),
      IsRegular ((pullback (middleHom f g) (middleHom f g)).presheaf.stalk
        (pullback.diagonal (middleHom f g) (supportMap f g p u v))) rs ∧
      RingHom.ker ((pullback.diagonal (middleHom f g)).stalkMap
        (supportMap f g p u v)).hom = Ideal.ofList rs ∧
      IsRegular ((coefficient f g p u).presheaf.stalk (mixedEmbedding f g p u v))
        (rs.map (mixedDiagonalStalkMap f g p u v).hom) := by
  have h := Graph.exists_common_regular_list_of_smooth
    (supportMap f g p u) (middleHom f g) v
  have hp : pullback.diagonal (middleHom f g) (supportMap f g p u v) =
      graphMiddlePair (supportMap f g p u) (middleHom f g)
        (correspondenceGraph (supportMap f g p u) (middleHom f g) v) :=
    (congrArg (fun q => q v)
      (correspondenceGraph_middlePair (supportMap f g p u) (middleHom f g))).symm
  have hm : pullback.diagonal (middleHom f g) (supportMap f g p u v) =
      mixedPair f g p u (mixedEmbedding f g p u v) :=
    (congrArg (fun q => q v) (mixedEmbedding_mixedPair f g p u)).symm
  have ht := Graph.exists_regular_kernel_and_regular_image_of_openCharts
    (pullback.diagonal (middleHom f g)) (mixedPair f g p u)
    (pullback.diagonal (middleHom f g))
      (graphMiddlePair (supportMap f g p u) (middleHom f g))
    (𝟙 (middle f g)) (coefficientGraphIso f g p u).inv (partialSwap f g f g)
    (by simp only [diagonal_partialSwap, Category.id_comp])
    (graphMiddlePair_partialSwap f g p u)
    (supportMap f g p u v)
    (correspondenceGraph (supportMap f g p u) (middleHom f g) v)
    (pullback.diagonal (middleHom f g) (supportMap f g p u v)) rfl hp
    (by simp)
    (by simpa only [partialSwap_diagonal_apply, mixedEmbedding, Scheme.Hom.comp_apply] using hm)
    (by simpa only [Graph.alignedStalkMap_rfl, Graph.diagonalStalkMap] using h)
  have hn := Graph.common_regular_list_congr_points
    (pullback.diagonal (middleHom f g)) (mixedPair f g p u)
    ((𝟙 (middle f g)) (supportMap f g p u v)) (supportMap f g p u v)
    ((coefficientGraphIso f g p u).inv
      (correspondenceGraph (supportMap f g p u) (middleHom f g) v))
    (mixedEmbedding f g p u v)
    (partialSwap f g f g (pullback.diagonal (middleHom f g) (supportMap f g p u v)))
    (pullback.diagonal (middleHom f g) (supportMap f g p u v))
    rfl rfl (partialSwap_diagonal_apply f g (supportMap f g p u v))
    (by simp)
    (by simpa only [partialSwap_diagonal_apply, mixedEmbedding, Scheme.Hom.comp_apply] using hm)
    rfl hm ht
  simpa only [Graph.alignedStalkMap_rfl, mixedDiagonalStalkMap] using hn

end MixedPair

end Motivic.ProductGraph
