/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalTopDegree
public import Motivic.Cohomology.Motivic.DiagonalMilnorSymbol
public import Motivic.AlgebraicGeometry.Correspondences.BaseFieldGenerators
public import Aglib.KTheory.MilnorK.LowDegree

/-!
# Actual weight-zero field cohomology

The weight-zero reduced torus is the actual base representable. On each
integral simplex its signed correspondences have one geometric generator,
the graph of the structure morphism. Both endpoint restrictions preserve this
generator, so the literal singular boundary is zero. The original derived
comparison therefore identifies `H^{0,0}(k, ℤ)` with `ℤ` for every field.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace Motivic.DiagonalWeightZero

open PresheafWithTransfers DiagonalTopDegree

variable (k : Type u) [Field k]

local instance (X : SmoothSite (Spec (.of k))) [IsIntegral X.left] :
    IsIntegral ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsIntegral X.left)

local instance (X : SmoothSite (Spec (.of k))) :
    IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)

local instance (X : SmoothSite (Spec (.of k))) :
    IsReduced ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsReduced X.left)

/-- The literal structure morphism of a smooth object. -/
def toBase (X : SmoothSite (Spec (.of k))) : X ⟶ SmoothSite.base (Spec (.of k)) :=
  SmoothSite.homMk X.hom (Category.comp_id _)

/-- Its actual single graph support on an integral source. -/
def baseGenerator (X : SmoothSite (Spec (.of k))) [IsIntegral X.left] :
    FiniteCorrespondenceGenerator X.hom (𝟙 (Spec (.of k))) :=
  graphGeneratorOver (X := X.left) (Y := Spec (.of k))
    (f := X.hom) (g := 𝟙 (Spec (.of k))) X.hom (Category.comp_id _)

/-- Every elementary correspondence to the base has this actual graph support. -/
theorem eq_baseGenerator (X : SmoothSite (Spec (.of k))) [IsIntegral X.left]
    (A : FiniteCorrespondenceGenerator X.hom (𝟙 (Spec (.of k)))) :
    A = baseGenerator k X := by
  apply FiniteCorrespondenceGenerator.eq_of_graph_range_eq
    (X := X.left) (Y := Spec (.of k)) X.hom (Category.comp_id _)
  · simpa only [Category.comp_id] using A.projection_base
  · exact graphGeneratorOver_projection_target (X := X.left) (Y := Spec (.of k))
      (f := X.hom) (g := 𝟙 (Spec (.of k))) X.hom (Category.comp_id _)
  · exact (Set.range_eq_univ.mpr A.projection_surjective).trans
      (Set.range_eq_univ.mpr (baseGenerator k X).projection_surjective).symm

/-- The graph functor has coefficient one on the unique structural support. -/
theorem graph_toBase (X : SmoothSite (Spec (.of k))) [IsIntegral X.left] :
    (Cor.graphFunctor k).map (toBase k X) = (baseGenerator k X).cycle := by
  exact componentGraphCycleOver_eq_graphGeneratorOver_cycle
    (X := X.left) (Y := Spec (.of k)) X.hom (Category.comp_id _)

/-- Signed correspondences from an integral smooth object to the base are integers. -/
def correspondenceEquiv (X : SmoothSite (Spec (.of k))) [IsIntegral X.left] :
    (Cor.mk X ⟶ point k) ≃+ ℤ where
  toFun α := Finsupp.toFun α (baseGenerator k X)
  invFun z := z • (Cor.graphFunctor k).map (toBase k X)
  left_inv α := by
    rw [graph_toBase]
    apply Finsupp.ext
    intro A
    rw [eq_baseGenerator k X A]
    change (Finsupp.toFun α (baseGenerator k X) • (baseGenerator k X).cycle)
      (baseGenerator k X) = Finsupp.toFun α (baseGenerator k X)
    simp only [Finsupp.smul_apply, FiniteCorrespondenceGenerator.cycle_self,
      zsmul_eq_mul, mul_one, Int.cast_id]
  right_inv z := by
    rw [graph_toBase]
    change (z • (baseGenerator k X).cycle) (baseGenerator k X) = z
    simp
  map_add' _ _ := rfl

/-- The structural graph corresponds to the integer one. -/
@[simp] theorem correspondenceEquiv_graph (X : SmoothSite (Spec (.of k)))
    [IsIntegral X.left] :
    correspondenceEquiv k X ((Cor.graphFunctor k).map (toBase k X)) = 1 := by
  change Finsupp.toFun _ _ = 1
  rw [graph_toBase]
  exact FiniteCorrespondenceGenerator.cycle_self _

/-- Graph restriction between integral smooth sources preserves the structural degree. -/
theorem correspondenceEquiv_graph_comp {X Y : SmoothSite (Spec (.of k))}
    [IsIntegral X.left] [IsIntegral Y.left] (f : X ⟶ Y) (α : Cor.mk Y ⟶ point k) :
    correspondenceEquiv k X ((Cor.graphFunctor k).map f ≫ α) =
      correspondenceEquiv k Y α := by
  obtain ⟨z, rfl⟩ := (correspondenceEquiv k Y).symm.surjective α
  change correspondenceEquiv k X
    ((Cor.graphFunctor k).map f ≫ (z • (Cor.graphFunctor k).map (toBase k Y))) = _
  rw [Preadditive.comp_zsmul, ← Functor.map_comp]
  have h : f ≫ toBase k Y = toBase k X := by
    apply MorphismProperty.Over.Hom.ext
    exact MorphismProperty.Over.w f
  rw [h, map_zsmul, correspondenceEquiv_graph]
  simpa only [zsmul_eq_mul, mul_one, Int.cast_id] using
    ((correspondenceEquiv k Y).apply_symm_apply z).symm

/-- The original reduced-torus sections are exactly actual correspondences to the base. -/
def sectionsCorrespondenceEquiv (X : SmoothSite (Spec (.of k))) :
    sections (reducedTorus k 0) (Cor.mk X) ≃+ (Cor.mk X ⟶ point k) :=
  (((forget.mapIso (reducedTorusZeroIso k)).app (op (Cor.mk X))).addCommGroupIsoToAddEquiv).trans
    AddEquiv.ulift

/-- This identification retains every literal original graph restriction. -/
theorem sectionsCorrespondenceEquiv_transfer {X Y : SmoothSite (Spec (.of k))}
    (f : X ⟶ Y) (x : sections (reducedTorus k 0) (Cor.mk Y)) :
    sectionsCorrespondenceEquiv k X (transfer (reducedTorus k 0) ((Cor.graphFunctor k).map f) x) =
      (Cor.graphFunctor k).map f ≫ sectionsCorrespondenceEquiv k Y x := by
  have h := ConcreteCategory.congr_hom
    (transfer_naturality (reducedTorusZeroIso k).hom ((Cor.graphFunctor k).map f)) x
  exact congrArg ULift.down h

/-- Integral smooth sources see the constant value `ℤ` in weight zero. -/
def sectionsEquiv (X : SmoothSite (Spec (.of k))) [IsIntegral X.left] :
    sections (reducedTorus k 0) (Cor.mk X) ≃+ ℤ :=
  (sectionsCorrespondenceEquiv k X).trans (correspondenceEquiv k X)

/-- Every graph restriction between integral sources is the identity on this `ℤ`. -/
theorem sectionsEquiv_transfer {X Y : SmoothSite (Spec (.of k))}
    [IsIntegral X.left] [IsIntegral Y.left] (f : X ⟶ Y)
    (x : sections (reducedTorus k 0) (Cor.mk Y)) :
    sectionsEquiv k X (transfer (reducedTorus k 0) ((Cor.graphFunctor k).map f) x) =
      sectionsEquiv k Y x := by
  change correspondenceEquiv k X (sectionsCorrespondenceEquiv k X _) = _
  rw [sectionsCorrespondenceEquiv_transfer, correspondenceEquiv_graph_comp]
  rfl

/-- The actual source of singular chains over the base. -/
abbrev simplexSource (r : ℕ) :=
  SmoothSite.product (SmoothSite.base (Spec (.of k))) (AlgebraicSimplex.smoothSiteObj k r)

instance simplexSource_integral (r : ℕ) : IsIntegral (simplexSource k r).left := by
  change IsIntegral (pullback (𝟙 (Spec (.of k))) (AlgebraicSimplex.structureMap k r))
  infer_instance

/-- Each genuine singular chain group in weight zero is canonically `ℤ`. -/
def chainEquiv (r : ℕ) : chains k 0 r ≃+ ℤ := sectionsEquiv k (simplexSource k r)

/-- Both literal cofaces induce the identity on the unique structural generator. -/
theorem chainEquiv_face (i : Fin 2) (x : chains k 0 1) :
    chainEquiv k 0 (transfer (reducedTorus k 0)
      ((Cor.simplexProductCosimplicial (point k)).δ i) x) = chainEquiv k 1 x :=
  sectionsEquiv_transfer k _ x

/-- The original degree-one singular boundary is zero, by its two equal endpoints. -/
theorem boundary_eq_zero : boundary k 0 = 0 := by
  ext x
  apply (chainEquiv k 0).injective
  rw [boundary_eq_endpoints, map_sub, chainEquiv_face, chainEquiv_face, sub_self]
  exact (map_zero _).symm

/-- The actual boundary subgroup vanishes. -/
theorem boundary_range_eq_bot : (boundary k 0).range = ⊥ := by
  rw [boundary_eq_zero, AddMonoidHom.range_zero]

/-- The literal `C₀ / im(d₁)` of the original reduced torus is `ℤ`. -/
def quotientEquiv : zeroHomology k 0 ≃+ ℤ :=
  (QuotientAddGroup.quotientAddEquivOfEq (boundary_range_eq_bot k)).trans
    (QuotientAddGroup.quotientBot.trans (chainEquiv k 0))

/-- The quotient evaluation retains the original zero-cycle degree. -/
theorem quotientEquiv_mk (x : chains k 0 0) :
    quotientEquiv k (QuotientAddGroup.mk x) = chainEquiv k 0 x := rfl

/-- The actual quotient projection is inverted without changing the represented cycle. -/
theorem sectionsCorrespondenceEquiv_reduced (X : SmoothSite (Spec (.of k)))
    (α : Cor.mk X ⟶ point k) :
    sectionsCorrespondenceEquiv k X
      ((toReducedTorus k 0).hom.app (op (Cor.mk X)) (ULift.up α)) = α :=
  (sectionsCorrespondenceEquiv k X).apply_symm_apply α

/-- The structural graph in the literal singular chain group. -/
def graphChain (r : ℕ) : chains k 0 r :=
  (toReducedTorus k 0).hom.app (op (Cor.simplexProduct (point k) r))
    (ULift.up ((Cor.graphFunctor k).map (toBase k (simplexSource k r))))

/-- The canonical graph generator, before taking any homology, has degree one. -/
@[simp] theorem chainEquiv_graphChain (r : ℕ) : chainEquiv k r (graphChain k r) = 1 := by
  exact (congrArg (correspondenceEquiv k (simplexSource k r))
    (sectionsCorrespondenceEquiv_reduced k (simplexSource k r)
      ((Cor.graphFunctor k).map (toBase k (simplexSource k r))))).trans
        (correspondenceEquiv_graph k (simplexSource k r))

/-- The all-weight rational empty tuple represents exactly the structural graph class. -/
theorem graphSymbol_zero (a : Fin 0 → kˣ) :
    DiagonalCycleSymbols.graphSymbol k 0 a = singularClass k 0 (graphChain k 0) := by
  have h : (WeightOneBoundaryNorm.zeroProductIso k).hom ≫
      (Cor.graphFunctor k).map (DiagonalCycleSymbols.rationalTuple k 0 a) =
        (Cor.graphFunctor k).map (toBase k (simplexSource k 0)) := by
    change (Cor.graphFunctor k).map _ ≫ (Cor.graphFunctor k).map _ = _
    rw [← Functor.map_comp]
    congr 1
    apply SmoothSite.torusPower_hom_ext (.of k) 0
    intro i
    exact Fin.elim0 i
  change singularClass k 0 ((toReducedTorus k 0).hom.app
    (op (Cor.simplexProduct (point k) 0)) (ULift.up (_ ≫ _))) = _
  rw [h]
  rfl

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Actual original derived weight-zero field cohomology is the integers. -/
def motivicEquiv : motivicCohomology k 0 0 (SmoothSite.base (Spec (.of k))) ≃+ ℤ :=
  (quotientToMotivicEquiv k 0).symm.trans (quotientEquiv k)

/-- The original derived class of any actual zero-cycle has its genuine integer degree. -/
theorem motivicEquiv_class (x : chains k 0 0) :
    motivicEquiv k (quotientToMotivicEquiv k 0 (QuotientAddGroup.mk x)) =
      chainEquiv k 0 x := by
  exact congrArg (quotientEquiv k) ((quotientToMotivicEquiv k 0).symm_apply_apply _)

/-- The actual zeroth Milnor group agrees with the original derived weight-zero group. -/
def milnorEquiv : MilnorK.K k 0 ≃+
    motivicCohomology k 0 0 (SmoothSite.base (Spec (.of k))) :=
  (MilnorK.zeroEquiv k).toAddEquiv.trans (motivicEquiv k).symm

/-- The original derived class of the actual base structural graph. -/
def graphClass : motivicCohomology k 0 0 (SmoothSite.base (Spec (.of k))) :=
  quotientToMotivicEquiv k 0 (QuotientAddGroup.mk (graphChain k 0))

/-- The original derived graph generator is sent to the integer one. -/
@[simp] theorem motivicEquiv_graphClass : motivicEquiv k (graphClass k) = 1 := by
  rw [graphClass, motivicEquiv_class, chainEquiv_graphChain]

/-- Every integer represents its actual signed multiple of the original graph class. -/
theorem motivicEquiv_symm_apply (z : ℤ) :
    (motivicEquiv k).symm z = z • graphClass k := by
  apply (motivicEquiv k).injective
  rw [AddEquiv.apply_symm_apply, map_zsmul, motivicEquiv_graphClass,
    zsmul_eq_mul, mul_one, Int.cast_id]

/-- The empty Milnor symbol is the original structural graph class. -/
theorem milnorEquiv_symbol (a : MilnorK.SymbolTuple k 0) :
    milnorEquiv k (MilnorK.symbol a) = graphClass k := by
  change (motivicEquiv k).symm
    (MilnorK.zeroEquiv k (MilnorK.symbol a)) = graphClass k
  rw [MilnorK.zeroEquiv_symbol, motivicEquiv_symm_apply, one_zsmul]

/-- The degree-zero all-weight symbol is precisely the proved canonical equivalence. -/
theorem motivicSymbol_zero [CharZero k] (x : MilnorK.K k 0) :
    DiagonalMilnorSymbol.motivicSymbol k 0 x = milnorEquiv k x := by
  have h : DiagonalMilnorSymbol.motivicSymbol k 0 = (milnorEquiv k).toAddMonoidHom := by
    apply MilnorK.addHom_ext
    intro a
    change DiagonalMilnorSymbol.motivicSymbol k 0 (MilnorK.symbol a) =
      milnorEquiv k (MilnorK.symbol a)
    apply (motivicRawBaseEvaluationComparison k 0 0).injective
    exact (DiagonalMilnorSymbol.motivicSymbol_comparison k 0 (MilnorK.symbol a)).trans
      ((DiagonalMilnorSymbol.rawSymbol_symbol k 0 a).trans
        ((graphSymbol_zero k a).trans
          ((quotientToMotivicEquiv_mk k 0 (graphChain k 0)).symm.trans
            (congrArg (motivicRawBaseEvaluationComparison k 0 0)
              (milnorEquiv_symbol k a).symm))))
  exact DFunLike.congr_fun h x

end Motivic.DiagonalWeightZero
