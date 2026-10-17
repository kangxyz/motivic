/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteUnitHomotopyInvariance
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Algebra.Homology.QuasiIso

/-! # The actual ordinary Gm singular sheaf complex -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology Opposite

universe u

namespace Motivic.SmoothSite

variable (k : Type u) [Field k]

/-- Pullback by the original simplex operator, with the smooth parameter retained. -/
def simplexUnitsMap {m n : SimplexCategory} (f : m ⟶ n) :
    simplexUnitsSheaf k n.len ⟶ simplexUnitsSheaf k m.len where
  hom :=
    { app X := (largeUnitsPresheaf (Spec (.of k))).map
        (productMap (𝟙 X.unop) ((AlgebraicSimplex.cosimplicialSmoothSite k).map f)).op
      naturality X Y g := by
        change (largeUnitsPresheaf _).map _ ≫ (largeUnitsPresheaf _).map _ =
          (largeUnitsPresheaf _).map _ ≫ (largeUnitsPresheaf _).map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        apply Quiver.Hom.unop_inj
        simp only [Functor.op_map, unop_comp, Quiver.Hom.unop_op,
          parameterProduct_map]
        rw [← productMap_comp, ← productMap_comp]
        simp only [AlgebraicSimplex.cosimplicialSmoothSite, Category.id_comp, Category.comp_id] }

/-- The projection-to-base units identification respects every actual simplex map. -/
theorem unitsSimplexPullback_comp_map {m n : SimplexCategory} (f : m ⟶ n) :
    unitsSimplexPullback k n.len ≫ simplexUnitsMap k f = unitsSimplexPullback k m.len := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  change (largeUnitsPresheaf _).map _ ≫ (largeUnitsPresheaf _).map _ =
    (largeUnitsPresheaf _).map _
  rw [← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  change productMap (𝟙 X.unop) ((AlgebraicSimplex.cosimplicialSmoothSite k).map f) ≫
    productFst X.unop ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n) =
      productFst X.unop ((AlgebraicSimplex.cosimplicialSmoothSite k).obj m)
  simpa only [Category.comp_id] using
    productMap_fst (𝟙 X.unop) ((AlgebraicSimplex.cosimplicialSmoothSite k).map f)

/-- The genuine simplicial ordinary sheaf `X ↦ Γ(X × Δⁿ,O)ˣ`. -/
def unitSimplicialSheaf :
    SimplicialObject (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) where
  obj n := simplexUnitsSheaf k n.unop.len
  map f := simplexUnitsMap k f.unop
  map_id n := by
    apply (cancel_epi (unitsSimplexPullback k n.unop.len)).mp
    rw [unitsSimplexPullback_comp_map, Category.comp_id]
  map_comp f g := by
    apply (cancel_epi (unitsSimplexPullback k _)).mp
    rw [unitsSimplexPullback_comp_map, ← Category.assoc,
      unitsSimplexPullback_comp_map, unitsSimplexPullback_comp_map]

/-- The actual simplicial Gm sheaf is naturally isomorphic to constant Gm. -/
def constantUnitSimplicialSheafIso :
    (Functor.const SimplexCategoryᵒᵖ).obj (largeUnitsSheaf (Spec (.of k))) ≅
      unitSimplicialSheaf k :=
  NatIso.ofComponents (fun n => asIso (unitsSimplexPullback k n.unop.len)) (by
    intro m n f
    change 𝟙 _ ≫ _ = _ ≫ simplexUnitsMap k f.unop
    change 𝟙 _ ≫ unitsSimplexPullback k n.unop.len =
      unitsSimplexPullback k m.unop.len ≫ simplexUnitsMap k f.unop
    rw [Category.id_comp, unitsSimplexPullback_comp_map])

/-- The ordinary singular Gm sheaf complex retains all actual face pullbacks. -/
def unitSingularSheafComplex :
    ChainComplex (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) ℕ :=
  (alternatingFaceMapComplex _).obj (unitSimplicialSheaf k)

/-- A genuine all-degree sheaf-chain homotopy equivalence C*Gm ≃ Gm[0]. -/
def unitSingularSheafHomotopyEquiv :
    HomotopyEquiv (unitSingularSheafComplex k)
      ((ChainComplex.single₀ _).obj (largeUnitsSheaf (Spec (.of k)))) :=
  (HomotopyEquiv.ofIso ((alternatingFaceMapComplex _).mapIso
    (constantUnitSimplicialSheafIso k).symm)).trans
      (SimplicialObject.Augmented.ExtraDegeneracy.const
        (largeUnitsSheaf (Spec (.of k)))).homotopyEquiv

instance unitSingularSheafHomotopyEquiv_quasiIso :
    QuasiIso (unitSingularSheafHomotopyEquiv k).hom :=
  (unitSingularSheafHomotopyEquiv k).quasiIso_hom

end Motivic.SmoothSite
