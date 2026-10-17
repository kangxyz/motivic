/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.FieldChangeCoherence
public import Motivic.Aglib.AlgebraicGeometry.CorrespondenceIsoTransport
public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGeometry

/-!
# Coherence of the original raw field-change maps

The original field-change cycles and the original simplex and torus comparisons
are retained throughout. The geometric identity and tower comparisons are
attached through the actual graphs of their scheme isomorphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped Simplicial

universe u

namespace Motivic.SmoothSite

variable {k L M : Type u} [Field k] [Field L] [Field M]

/-- The literal identity projection is natural on the original smooth site. -/
@[reassoc]
theorem fieldBaseChangeObjectIdIso_naturality {X Y : overField k} (f : X ⟶ Y) :
    (fieldBaseChange (RingHom.id k)).map f ≫ (fieldBaseChangeObjectIdIso k Y).hom =
      (fieldBaseChangeObjectIdIso k X).hom ≫ f := by
  apply MorphismProperty.Over.Hom.ext
  exact baseChange_map_fst _ f

/-- The original Laurent identity comparison is the literal identity projection. -/
theorem torusBaseChangeIso_id :
    (torusBaseChangeIso (CommRingCat.ofHom (RingHom.id k))).hom =
      (fieldBaseChangeObjectIdIso k (torus (.of k))).hom := by
  apply MorphismProperty.Over.Hom.ext
  change (torusBaseChangeIso (CommRingCat.ofHom (RingHom.id k))).hom.left =
    pullback.fst (laurentProjection (.of k)) (Spec.map (CommRingCat.ofHom (RingHom.id k)))
  have hid : laurentMap (𝟙 (CommRingCat.of k)) = 𝟙 _ := by
    apply CommRingCat.hom_ext
    exact AddMonoidAlgebra.mapRingHom_id
  have h := torusBaseChangeIso_hom_coefficientMap (CommRingCat.ofHom (RingHom.id k))
  simp only [CommRingCat.ofHom_id, hid, Spec.map_id] at h
  exact (Category.comp_id _).symm.trans h

/-- The inverse tower comparison retains the actual original projection for
any two specified parameter comparisons. -/
theorem fieldBaseChangeComparison_inv_original (φ : k →+* L) (ψ : L →+* M)
    {X : overField k} {Y : overField L} {Z : overField M}
    (e : (fieldBaseChange φ).obj X ≅ Y) (d : (fieldBaseChange ψ).obj Y ≅ Z) :
    (d.inv ≫ (fieldBaseChange ψ).map e.inv ≫
        (fieldBaseChangeComp φ ψ).inv.app X).left ≫
          pullback.fst X.hom (Spec.map (CommRingCat.ofHom (ψ.comp φ))) =
      d.inv.left ≫ pullback.fst Y.hom (Spec.map (CommRingCat.ofHom ψ)) ≫
        e.inv.left ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ)) := by
  calc
    _ = d.inv.left ≫ ((fieldBaseChange ψ).map e.inv).left ≫
        pullback.fst ((fieldBaseChange φ).obj X).hom (Spec.map (CommRingCat.ofHom ψ)) ≫
          pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ)) := by
      simpa only [MorphismProperty.Comma.comp_left, Category.assoc] using
        congrArg (fun f => d.inv.left ≫ ((fieldBaseChange ψ).map e.inv).left ≫ f)
          (fieldBaseChangeComp_inv_original φ ψ X)
    _ = _ := by
      simpa only [Category.assoc, fieldBaseChange] using
        congrArg (fun f => d.inv.left ≫ f ≫
          pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ)))
          (baseChange_map_fst (Spec.map (CommRingCat.ofHom ψ)) e.inv)

/-- The original Laurent comparison in a field tower has the original coefficient map. -/
theorem torusBaseChangeIso_comp_inv (φ : k →+* L) (ψ : L →+* M) :
    (torusBaseChangeIso (CommRingCat.ofHom (ψ.comp φ))).inv =
      (torusBaseChangeIso (CommRingCat.ofHom ψ)).inv ≫
        (fieldBaseChange ψ).map (torusBaseChangeIso (CommRingCat.ofHom φ)).inv ≫
          (fieldBaseChangeComp φ ψ).inv.app (torus (.of k)) := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · rw [fieldBaseChangeComparison_inv_original]
    change (torusBaseChangeIso (CommRingCat.ofHom (ψ.comp φ))).inv.left ≫
        pullback.fst (laurentProjection (.of k)) _ =
      ((torusBaseChangeIso (CommRingCat.ofHom ψ)).inv.left ≫
        pullback.fst (laurentProjection (.of L)) _) ≫
          (torusBaseChangeIso (CommRingCat.ofHom φ)).inv.left ≫
            pullback.fst (laurentProjection (.of k)) _
    simp only [torusBaseChangeIso_inv_fst]
    rw [← Spec.map_comp, ← laurentMap_comp]
    rfl
  · exact (MorphismProperty.Over.w
      (torusBaseChangeIso (CommRingCat.ofHom (ψ.comp φ))).inv).trans
        (MorphismProperty.Over.w
          ((torusBaseChangeIso (CommRingCat.ofHom ψ)).inv ≫
            (fieldBaseChange ψ).map (torusBaseChangeIso (CommRingCat.ofHom φ)).inv ≫
              (fieldBaseChangeComp φ ψ).inv.app (torus (.of k)))).symm

/-- The original forward Laurent comparison satisfies the canonical tower law. -/
theorem torusBaseChangeIso_comp (φ : k →+* L) (ψ : L →+* M) :
    (torusBaseChangeIso (CommRingCat.ofHom (ψ.comp φ))).hom =
      (fieldBaseChangeComp φ ψ).hom.app (torus (.of k)) ≫
        (fieldBaseChange ψ).map (torusBaseChangeIso (CommRingCat.ofHom φ)).hom ≫
          (torusBaseChangeIso (CommRingCat.ofHom ψ)).hom := by
  have h : torusBaseChangeIso (CommRingCat.ofHom (ψ.comp φ)) =
      (fieldBaseChangeComp φ ψ).app (torus (.of k)) ≪≫
        (fieldBaseChange ψ).mapIso (torusBaseChangeIso (CommRingCat.ofHom φ)) ≪≫
          torusBaseChangeIso (CommRingCat.ofHom ψ) := by
    apply Iso.ext_inv
    exact torusBaseChangeIso_comp_inv φ ψ
  exact congrArg Iso.hom h

/-- Every original torus power has the literal identity comparison. -/
theorem torusPowerBaseChangeIso_id (q : ℕ) :
    (torusPowerBaseChangeIso (CommRingCat.ofHom (RingHom.id k)) q).hom =
      (fieldBaseChangeObjectIdIso k (torusPower (.of k) q)).hom := by
  apply torusPower_hom_ext
  intro i
  rw [torusPowerBaseChangeIso_coordinate, torusBaseChangeIso_id]
  exact fieldBaseChangeObjectIdIso_naturality (torusCoordinate (.of k) q i)

/-- Every original torus power satisfies the same field-tower comparison. -/
theorem torusPowerBaseChangeIso_comp (φ : k →+* L) (ψ : L →+* M) (q : ℕ) :
    (torusPowerBaseChangeIso (CommRingCat.ofHom (ψ.comp φ)) q).hom =
      (fieldBaseChangeComp φ ψ).hom.app (torusPower (.of k) q) ≫
        (fieldBaseChange ψ).map (torusPowerBaseChangeIso (CommRingCat.ofHom φ) q).hom ≫
          (torusPowerBaseChangeIso (CommRingCat.ofHom ψ) q).hom := by
  apply torusPower_hom_ext
  intro i
  simp only [Category.assoc, torusPowerBaseChangeIso_coordinate, fieldBaseChange]
  rw [← Functor.map_comp_assoc, torusPowerBaseChangeIso_coordinate, Functor.map_comp,
    torusBaseChangeIso_comp]
  simpa only [Category.assoc, Functor.comp_map, fieldBaseChange] using congrArg
    (fun f => f ≫ (fieldBaseChange ψ).map
      (torusBaseChangeIso (CommRingCat.ofHom φ)).hom ≫
        (torusBaseChangeIso (CommRingCat.ofHom ψ)).hom)
    ((fieldBaseChangeComp φ ψ).hom.naturality (torusCoordinate (.of k) q i))

/-- The original barycentric identity comparison is the literal identity projection. -/
theorem simplexBaseChangeIso_id (n : ℕ) :
    (AlgebraicSimplex.smoothSiteBaseChangeIso (RingHom.id k) n).hom =
      (fieldBaseChangeObjectIdIso k (AlgebraicSimplex.smoothSiteObj k n)).hom := by
  apply MorphismProperty.Over.Hom.ext
  have h := AlgebraicSimplex.smoothSiteBaseChangeIso_hom_coefficientMap (RingHom.id k) n
  simp only [AlgebraicSimplex.mapCoefficients_id, CommRingCat.ofHom_id, Spec.map_id] at h
  exact (Category.comp_id _).symm.trans h

/-- The original barycentric inverse comparisons compose through the literal tower. -/
theorem simplexBaseChangeIso_comp_inv (φ : k →+* L) (ψ : L →+* M) (n : ℕ) :
    (AlgebraicSimplex.smoothSiteBaseChangeIso (ψ.comp φ) n).inv =
      (AlgebraicSimplex.smoothSiteBaseChangeIso ψ n).inv ≫
        (fieldBaseChange ψ).map (AlgebraicSimplex.smoothSiteBaseChangeIso φ n).inv ≫
          (fieldBaseChangeComp φ ψ).inv.app (AlgebraicSimplex.smoothSiteObj k n) := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · rw [fieldBaseChangeComparison_inv_original]
    change (AlgebraicSimplex.smoothSiteBaseChangeIso (ψ.comp φ) n).inv.left ≫
        pullback.fst (AlgebraicSimplex.structureMap k n) _ =
      ((AlgebraicSimplex.smoothSiteBaseChangeIso ψ n).inv.left ≫
        pullback.fst (AlgebraicSimplex.structureMap L n) _) ≫
          (AlgebraicSimplex.smoothSiteBaseChangeIso φ n).inv.left ≫
            pullback.fst (AlgebraicSimplex.structureMap k n) _
    simp only [AlgebraicSimplex.smoothSiteBaseChangeIso_inv_fst]
    rw [AlgebraicSimplex.mapCoefficients_comp, CommRingCat.ofHom_comp, Spec.map_comp]
  · exact (MorphismProperty.Over.w
      (AlgebraicSimplex.smoothSiteBaseChangeIso (ψ.comp φ) n).inv).trans
        (MorphismProperty.Over.w
          ((AlgebraicSimplex.smoothSiteBaseChangeIso ψ n).inv ≫
            (fieldBaseChange ψ).map (AlgebraicSimplex.smoothSiteBaseChangeIso φ n).inv ≫
              (fieldBaseChangeComp φ ψ).inv.app (AlgebraicSimplex.smoothSiteObj k n))).symm

/-- The original forward barycentric comparisons satisfy the field-tower law. -/
theorem simplexBaseChangeIso_comp (φ : k →+* L) (ψ : L →+* M) (n : ℕ) :
    (AlgebraicSimplex.smoothSiteBaseChangeIso (ψ.comp φ) n).hom =
      (fieldBaseChangeComp φ ψ).hom.app (AlgebraicSimplex.smoothSiteObj k n) ≫
        (fieldBaseChange ψ).map (AlgebraicSimplex.smoothSiteBaseChangeIso φ n).hom ≫
          (AlgebraicSimplex.smoothSiteBaseChangeIso ψ n).hom := by
  have h : AlgebraicSimplex.smoothSiteBaseChangeIso (ψ.comp φ) n =
      (fieldBaseChangeComp φ ψ).app (AlgebraicSimplex.smoothSiteObj k n) ≪≫
        (fieldBaseChange ψ).mapIso (AlgebraicSimplex.smoothSiteBaseChangeIso φ n) ≪≫
          AlgebraicSimplex.smoothSiteBaseChangeIso ψ n := by
    apply Iso.ext_inv
    exact simplexBaseChangeIso_comp_inv φ ψ n
  exact congrArg Iso.hom h

/-- The original base-times-simplex comparison retains the simplex projection. -/
@[reassoc]
theorem baseSimplexFieldChangeIso_hom_snd (φ : k →+* L) (n : SimplexCategory) :
    (baseSimplexFieldChangeIso φ n).hom ≫
        productSnd (base (Spec (.of L))) ((AlgebraicSimplex.cosimplicialSmoothSite L).obj n) =
      (fieldBaseChange φ).map
        (productSnd (base (Spec (.of k))) ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n)) ≫
          (AlgebraicSimplex.smoothSiteBaseChangeIso φ n.len).hom := by
  dsimp only [baseSimplexFieldChangeIso, Iso.trans_hom, productIso_hom]
  rw [Category.assoc, productMap_snd, baseChangeProductIso_hom_snd_assoc]
  rfl

/-- The exact source comparison used by the raw map has the literal identity projection. -/
theorem baseSimplexFieldChangeIso_id (n : SimplexCategory) :
    (baseSimplexFieldChangeIso (RingHom.id k) n).hom =
      (fieldBaseChangeObjectIdIso k (product (base (Spec (.of k)))
        ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n))).hom := by
  apply product_hom_ext
  · apply torusPower_hom_ext (.of k) 0
    intro i
    exact Fin.elim0 i
  · rw [baseSimplexFieldChangeIso_hom_snd, simplexBaseChangeIso_id]
    exact fieldBaseChangeObjectIdIso_naturality _

/-- The exact source comparison used in every raw singular degree respects the tower. -/
theorem baseSimplexFieldChangeIso_comp (φ : k →+* L) (ψ : L →+* M)
    (n : SimplexCategory) :
    (baseSimplexFieldChangeIso (ψ.comp φ) n).hom =
      (fieldBaseChangeComp φ ψ).hom.app (product (base (Spec (.of k)))
          ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n)) ≫
        (fieldBaseChange ψ).map (baseSimplexFieldChangeIso φ n).hom ≫
          (baseSimplexFieldChangeIso ψ n).hom := by
  apply product_hom_ext
  · apply torusPower_hom_ext (.of M) 0
    intro i
    exact Fin.elim0 i
  · simp only [Category.assoc, baseSimplexFieldChangeIso_hom_snd, fieldBaseChange]
    rw [← Functor.map_comp_assoc, baseSimplexFieldChangeIso_hom_snd,
      Functor.map_comp, simplexBaseChangeIso_comp]
    simpa only [Category.assoc, Functor.comp_map, fieldBaseChange,
      AlgebraicSimplex.cosimplicialSmoothSite] using congrArg
      (fun f => f ≫ (fieldBaseChange ψ).map
        (AlgebraicSimplex.smoothSiteBaseChangeIso φ n.len).hom ≫
          (AlgebraicSimplex.smoothSiteBaseChangeIso ψ n.len).hom)
      ((fieldBaseChangeComp φ ψ).hom.naturality
        (productSnd (base (Spec (.of k))) ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n)))

end Motivic.SmoothSite


namespace Motivic.Cor

variable {k L M : Type u} [Field k] [Field L] [Field M]

/-- The genuine identity-field correspondence is the original signed cycle
under the literal source and target comparison graphs. -/
theorem fieldBaseChange_id_graph {X Y : SmoothSite.overField k} [IsIntegral X.left]
    (α : Cor.mk X ⟶ Cor.mk Y) :
    (graphFunctor k).map (SmoothSite.fieldBaseChangeObjectIdIso k X).inv ≫
        (fieldBaseChange (RingHom.id k)).map α ≫
          (graphFunctor k).map (SmoothSite.fieldBaseChangeObjectIdIso k Y).hom = α := by
  apply FiniteCorrespondence.toIntegralCycle_injective
  have h := toIntegralCycle_graphIso_transport k
    (SmoothSite.fieldBaseChangeObjectIdIso k X)
    (SmoothSite.fieldBaseChangeObjectIdIso k Y)
    ((fieldBaseChange (RingHom.id k)).map α)
  exact h.trans (FiniteCorrespondence.toIntegralCycle_fieldBaseChange_id α)

/-- The genuine composite-field correspondence agrees with the original
iterated map through the canonical tower graphs. -/
theorem fieldBaseChange_comp_graph (φ : k →+* L) (ψ : L →+* M)
    {X Y : SmoothSite.overField k}
    [IsIntegral ((SmoothSite.fieldBaseChange (ψ.comp φ)).obj X).left]
    (α : Cor.mk X ⟶ Cor.mk Y) :
    (graphFunctor M).map ((SmoothSite.fieldBaseChangeComp φ ψ).hom.app X) ≫
        (fieldBaseChange ψ).map ((fieldBaseChange φ).map α) ≫
          (graphFunctor M).map ((SmoothSite.fieldBaseChangeComp φ ψ).inv.app Y) =
      (fieldBaseChange (ψ.comp φ)).map α := by
  apply FiniteCorrespondence.toIntegralCycle_injective
  have h := toIntegralCycle_graphIso_transport M
    ((SmoothSite.fieldBaseChangeComp φ ψ).app X).symm
    ((SmoothSite.fieldBaseChangeComp φ ψ).app Y).symm
    ((fieldBaseChange ψ).map ((fieldBaseChange φ).map α))
  exact h.trans (FiniteCorrespondence.toIntegralCycle_fieldBaseChange_comp φ ψ α)

end Motivic.Cor

namespace Motivic.SmoothSite

/-- The original base-times-simplex source is integral in every singular degree. -/
instance baseSimplex_isIntegral (k : Type u) [Field k] (n : SimplexCategory) :
    IsIntegral (product (base (Spec (.of k)))
      ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n)).left := by
  change IsIntegral (pullback (𝟙 (Spec (.of k))) (AlgebraicSimplex.structureMap k n.len))
  infer_instance

/-- Arbitrary scalar change of that actual source is integral, through its
proved literal simplex comparison. No claim is made for arbitrary smooth sources. -/
instance fieldBaseChange_baseSimplex_isIntegral {k L : Type u} [Field k] [Field L]
    (φ : k →+* L) (n : SimplexCategory) :
    IsIntegral ((fieldBaseChange φ).obj (product (base (Spec (.of k)))
      ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n))).left :=
  IsIntegral.of_isIso (baseSimplexFieldChangeIso φ n).inv.left

end Motivic.SmoothSite


namespace Motivic.SmoothSite

variable {k L M : Type u} [Field k] [Field L] [Field M]

/-- The exact inverse source comparison used by raw singular chains is the
inverse of the proved canonical tower comparison. -/
theorem baseSimplexFieldChangeIso_comp_inv (φ : k →+* L) (ψ : L →+* M)
    (n : SimplexCategory) :
    (baseSimplexFieldChangeIso (ψ.comp φ) n).inv =
      (baseSimplexFieldChangeIso ψ n).inv ≫
        (fieldBaseChange ψ).map (baseSimplexFieldChangeIso φ n).inv ≫
          (fieldBaseChangeComp φ ψ).inv.app (product (base (Spec (.of k)))
            ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n)) := by
  have h : baseSimplexFieldChangeIso (ψ.comp φ) n =
      (fieldBaseChangeComp φ ψ).app (product (base (Spec (.of k)))
        ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n)) ≪≫
          (fieldBaseChange ψ).mapIso (baseSimplexFieldChangeIso φ n) ≪≫
            baseSimplexFieldChangeIso ψ n := by
    apply Iso.ext
    exact baseSimplexFieldChangeIso_comp φ ψ n
  exact congrArg Iso.inv h

/-- The original inverse identity comparison used by raw chains is its literal
source projection inverse. -/
theorem baseSimplexFieldChangeIso_id_inv (n : SimplexCategory) :
    (baseSimplexFieldChangeIso (RingHom.id k) n).inv =
      (fieldBaseChangeObjectIdIso k (product (base (Spec (.of k)))
        ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n))).inv :=
  congrArg Iso.inv (Iso.ext (baseSimplexFieldChangeIso_id n))

end Motivic.SmoothSite

namespace Motivic.PresheafWithTransfers

variable {k L M : Type u} [Field k] [Field L] [Field M]

/-- The original all-degree reduced singular field-change map is the identity
for the identity field homomorphism. -/
theorem reducedTorusSingularFieldChange_id (q : ℕ) :
    reducedTorusSingularFieldChange (RingHom.id k) q = 𝟙 _ := by
  ext n : 1
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  obtain ⟨⟨α⟩, rfl⟩ := toReducedTorus_surjective k q
    (Cor.simplexProduct (Cor.mk (SmoothSite.base (Spec (.of k)))) n) s
  change Cor.simplexProduct (Cor.mk (SmoothSite.base (Spec (.of k)))) n ⟶
    Cor.mk (SmoothSite.torusPower (.of k) q) at α
  change (reducedTorusSingularFieldChange (RingHom.id k) q).f n
    ((toReducedTorus k q).hom.app _ (ULift.up α)) =
      (toReducedTorus k q).hom.app _ (ULift.up α)
  erw [reducedTorusSingularFieldChange_quotient]
  rw [SmoothSite.baseSimplexFieldChangeIso_id_inv, SmoothSite.torusPowerBaseChangeIso_id]
  exact congrArg (fun β => (toReducedTorus k q).hom.app _ (ULift.up β))
    (Cor.fieldBaseChange_id_graph
      (X := SmoothSite.product (SmoothSite.base (Spec (.of k)))
        ((AlgebraicSimplex.cosimplicialSmoothSite k).obj ⦋n⦌))
      (Y := SmoothSite.torusPower (.of k) q) α)

/-- The exact represented cycle formula in every singular degree respects the
field tower before passing to the identity-axis quotient. -/
theorem reducedTorusSingularCycleFieldChange_comp (φ : k →+* L) (ψ : L →+* M)
    (q n : ℕ)
    (α : Cor.simplexProduct (Cor.mk (SmoothSite.base (Spec (.of k)))) n ⟶
      Cor.mk (SmoothSite.torusPower (.of k) q)) :
    (Cor.graphFunctor M).map (SmoothSite.baseSimplexFieldChangeIso (ψ.comp φ) ⦋n⦌).inv ≫
        (Cor.fieldBaseChange (ψ.comp φ)).map α ≫
          (Cor.graphFunctor M).map
            (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (ψ.comp φ)) q).hom =
      (Cor.graphFunctor M).map (SmoothSite.baseSimplexFieldChangeIso ψ ⦋n⦌).inv ≫
        (Cor.fieldBaseChange ψ).map
          ((Cor.graphFunctor L).map (SmoothSite.baseSimplexFieldChangeIso φ ⦋n⦌).inv ≫
            (Cor.fieldBaseChange φ).map α ≫
              (Cor.graphFunctor L).map
                (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) q).hom) ≫
          (Cor.graphFunctor M).map
            (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom ψ) q).hom := by
  rw [SmoothSite.baseSimplexFieldChangeIso_comp_inv,
    SmoothSite.torusPowerBaseChangeIso_comp]
  rw [← Cor.fieldBaseChange_comp_graph φ ψ
    (X := SmoothSite.product (SmoothSite.base (Spec (.of k)))
      ((AlgebraicSimplex.cosimplicialSmoothSite k).obj ⦋n⦌))
    (Y := SmoothSite.torusPower (.of k) q) α]
  simp only [Functor.map_comp, Cor.fieldBaseChange_graph, Category.assoc]
  have hX := ((SmoothSite.fieldBaseChangeComp φ ψ).app
    (SmoothSite.product (SmoothSite.base (Spec (.of k)))
      ((AlgebraicSimplex.cosimplicialSmoothSite k).obj ⦋n⦌))).map_inv_hom_id
        (Cor.graphFunctor M)
  have hY := ((SmoothSite.fieldBaseChangeComp φ ψ).app
    (SmoothSite.torusPower (.of k) q)).map_inv_hom_id (Cor.graphFunctor M)
  simp only [Iso.app_inv, Iso.app_hom] at hX hY
  simp only [reassoc_of% hX, reassoc_of% hY]

/-- The actual reduced singular chain maps compose in every degree, through
the full quotient by all identity axes. -/
theorem reducedTorusSingularFieldChange_comp (φ : k →+* L) (ψ : L →+* M) (q : ℕ) :
    reducedTorusSingularFieldChange (ψ.comp φ) q =
      reducedTorusSingularFieldChange φ q ≫ reducedTorusSingularFieldChange ψ q := by
  ext n : 1
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  obtain ⟨⟨α⟩, rfl⟩ := toReducedTorus_surjective k q
    (Cor.simplexProduct (Cor.mk (SmoothSite.base (Spec (.of k)))) n) s
  change Cor.simplexProduct (Cor.mk (SmoothSite.base (Spec (.of k)))) n ⟶
    Cor.mk (SmoothSite.torusPower (.of k) q) at α
  change (reducedTorusSingularFieldChange (ψ.comp φ) q).f n
    ((toReducedTorus k q).hom.app _ (ULift.up α)) =
      (reducedTorusSingularFieldChange ψ q).f n
        ((reducedTorusSingularFieldChange φ q).f n
          ((toReducedTorus k q).hom.app _ (ULift.up α)))
  erw [reducedTorusSingularFieldChange_quotient, reducedTorusSingularFieldChange_quotient,
    reducedTorusSingularFieldChange_quotient]
  rw [reducedTorusSingularCycleFieldChange_comp]

end Motivic.PresheafWithTransfers

namespace Motivic.RawFieldChange

variable {k L M : Type u} [Field k] [Field L] [Field M]

/-- The original zero-extended components have the actual identity law. -/
theorem component_id (q : ℕ) (i : Option ℕ) :
    component (RingHom.id k) q i = 𝟙 _ := by
  cases i with
  | none =>
    exact ((baseEvaluationFunctor k).map_isZero
      (HomologicalComplex.extend.isZero_X
        (PresheafWithTransfers.singularComplex (PresheafWithTransfers.reducedTorus k q))
        rfl)).eq_of_src _ _
  | some n =>
    exact congrArg (fun f => f.f n)
      (PresheafWithTransfers.reducedTorusSingularFieldChange_id (k := k) q)

/-- The original zero-extended components compose through every field tower. -/
theorem component_comp (φ : k →+* L) (ψ : L →+* M) (q : ℕ) (i : Option ℕ) :
    component (ψ.comp φ) q i = component φ q i ≫ component ψ q i := by
  cases i with
  | none => exact (zero_comp : (0 : _ ⟶ _) ≫ 0 = 0).symm
  | some n =>
    exact congrArg (fun f => f.f n)
      (PresheafWithTransfers.reducedTorusSingularFieldChange_comp φ ψ q)

/-- Identity coherence before the original signed motivic shift. -/
theorem unshiftedMap_id (q : ℕ) : unshiftedMap (RingHom.id k) q = 𝟙 _ := by
  ext i : 1
  exact component_id q ((ComplexShape.embeddingUpIntLE 0).r i)

/-- Tower coherence before the original signed motivic shift. -/
theorem unshiftedMap_comp (φ : k →+* L) (ψ : L →+* M) (q : ℕ) :
    unshiftedMap (ψ.comp φ) q = unshiftedMap φ q ≫ unshiftedMap ψ q := by
  ext i : 1
  exact component_comp φ ψ q ((ComplexShape.embeddingUpIntLE 0).r i)

end Motivic.RawFieldChange

namespace Motivic

variable {k L M : Type u} [Field k] [Field L] [Field M]

/-- The original raw motivic cochain map is the identity for the identity field map. -/
theorem motivicRawBaseComplexMap_id (q : ℕ) :
    motivicRawBaseComplexMap (RingHom.id k) q = 𝟙 _ := by
  unfold motivicRawBaseComplexMap
  rw [RawFieldChange.unshiftedMap_id]
  exact (shiftFunctor (CochainComplex AddCommGrpCat.{u + 1} ℤ) (-(q : ℤ))).map_id _

/-- The original raw motivic maps compose in every degree, with the original signed shift. -/
theorem motivicRawBaseComplexMap_comp (φ : k →+* L) (ψ : L →+* M) (q : ℕ) :
    motivicRawBaseComplexMap (ψ.comp φ) q =
      motivicRawBaseComplexMap φ q ≫ motivicRawBaseComplexMap ψ q := by
  unfold motivicRawBaseComplexMap
  rw [RawFieldChange.unshiftedMap_comp, Functor.map_comp]

/-- The actual evaluated integral motivic complexes have identity field change. -/
theorem motivicBaseComplexMap_id (q : ℕ) :
    motivicBaseComplexMap (RingHom.id k) q = 𝟙 _ := by
  simp only [motivicBaseComplexMap, motivicRawBaseComplexMap_id, Category.id_comp,
    Iso.inv_hom_id]

/-- The actual evaluated integral maps retain the original raw field-tower law. -/
theorem motivicBaseComplexMap_comp (φ : k →+* L) (ψ : L →+* M) (q : ℕ) :
    motivicBaseComplexMap (ψ.comp φ) q =
      motivicBaseComplexMap φ q ≫ motivicBaseComplexMap ψ q := by
  simp only [motivicBaseComplexMap, motivicRawBaseComplexMap_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- The original coefficient-cone map has identity field change at every level. -/
theorem motivicBaseFiniteConeMap_id (q n : ℕ) :
    motivicBaseFiniteConeMap (RingHom.id k) q n = 𝟙 _ := by
  simp only [motivicBaseFiniteConeMap, motivicBaseComplexMap_id, finiteCoefficients.map_id]

/-- The original coefficient-cone maps compose, with no invertibility hypothesis on the level. -/
theorem motivicBaseFiniteConeMap_comp (φ : k →+* L) (ψ : L →+* M) (q n : ℕ) :
    motivicBaseFiniteConeMap (ψ.comp φ) q n =
      motivicBaseFiniteConeMap φ q n ≫ motivicBaseFiniteConeMap ψ q n := by
  simp only [motivicBaseFiniteConeMap, motivicBaseComplexMap_comp, finiteCoefficients.map_comp]

end Motivic

namespace Motivic

universe w

variable {k L M : Type u} [Field k] [Field L] [Field M]

section Identity

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Identity coherence for the original actual derived integral field-change map,
in every cohomological degree and every weight. -/
theorem motivicCohomologyFieldChange_id (p : ℤ) (q : ℕ) :
    motivicCohomologyFieldChange (RingHom.id k) p q = AddMonoidHom.id _ := by
  ext x
  apply (motivicBaseEvaluationComparison k p q).injective
  simp only [motivicCohomologyFieldChange_comparison, motivicBaseComplexMap_id,
    HomologicalComplex.homologyMap_id, ConcreteCategory.id_apply, AddMonoidHom.id_apply]

/-- Identity coherence for the original actual derived finite field-change map,
including coefficient levels divisible by the characteristic. -/
theorem motivicFiniteCohomologyFieldChange_id (p : ℤ) (q n : ℕ) :
    motivicFiniteCohomologyFieldChange (RingHom.id k) p q n = AddMonoidHom.id _ := by
  ext x
  apply (motivicFiniteBaseConeComparison k p q n).injective
  simp only [motivicFiniteCohomologyFieldChange_comparison, motivicBaseFiniteConeMap_id,
    HomologicalComplex.homologyMap_id, ConcreteCategory.id_apply, AddMonoidHom.id_apply]

end Identity

section Tower

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of M))) AddCommGrpCat.{u + 1})]

/-- The original actual derived integral field maps compose in all degrees,
through the proved original raw cochain maps. -/
theorem motivicCohomologyFieldChange_comp (φ : k →+* L) (ψ : L →+* M)
    (p : ℤ) (q : ℕ) :
    motivicCohomologyFieldChange (ψ.comp φ) p q =
      (motivicCohomologyFieldChange ψ p q).comp (motivicCohomologyFieldChange φ p q) := by
  ext x
  apply (motivicBaseEvaluationComparison M p q).injective
  simp only [AddMonoidHom.comp_apply, motivicCohomologyFieldChange_comparison,
    motivicBaseComplexMap_comp, HomologicalComplex.homologyMap_comp,
    ConcreteCategory.comp_apply]

/-- The original actual derived finite field maps compose in all degrees and
all levels, through the same signed coefficient-cone construction. -/
theorem motivicFiniteCohomologyFieldChange_comp (φ : k →+* L) (ψ : L →+* M)
    (p : ℤ) (q n : ℕ) :
    motivicFiniteCohomologyFieldChange (ψ.comp φ) p q n =
      (motivicFiniteCohomologyFieldChange ψ p q n).comp
        (motivicFiniteCohomologyFieldChange φ p q n) := by
  ext x
  apply (motivicFiniteBaseConeComparison M p q n).injective
  simp only [AddMonoidHom.comp_apply, motivicFiniteCohomologyFieldChange_comparison,
    motivicBaseFiniteConeMap_comp, HomologicalComplex.homologyMap_comp,
    ConcreteCategory.comp_apply]

end Tower

end Motivic
