/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Units.UnitComplex
public import Motivic.Aglib.Algebra.Homology.Sheafification.Singular

/-! # The native sheafified singular units complex

The original categorical parameter product is compared with the literal
relative scheme product. The latter terms are already actual sheaves, so the
canonical sheafification counit gives the all-degree chain isomorphism.
No interchange of singular chains and sheafification for arbitrary coefficients
is asserted.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicTopology Opposite
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]

/-- Actual categorical and literal parameter products give the same raw unit presheaf. -/
def unitRawTermIso (n : ℕ) :
    (SingularComplex.presheafObj (_root_.AlgebraicSimplex.cosimplicialSmoothSite k)
      (largeUnitsPresheaf (Spec (.of k)))).X n ≅ (simplexUnitsSheaf k n).obj :=
  isoWhiskerRight (NatIso.op (categoricalParameterProductIso
    (_root_.AlgebraicSimplex.smoothSiteObj k n)).symm) (largeUnitsPresheaf (Spec (.of k)))

/-- The actual product comparison is compatible with every simplex operator. -/
theorem unitRawTermIso_simplex (X : SmoothSite (Spec (.of k)))
    {m n : SimplexCategory} (f : m ⟶ n) :
    (largeUnitsPresheaf (Spec (.of k))).map
        (categoricalProductIso X ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).obj n)).inv.op
            ≫
      (largeUnitsPresheaf (Spec (.of k))).map
        (productMap (𝟙 X) ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).map f)).op =
    (largeUnitsPresheaf (Spec (.of k))).map
        (prod.map (𝟙 X) ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).map f)).op ≫
      (largeUnitsPresheaf (Spec (.of k))).map
        (categoricalProductIso X ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).obj m)).inv.op
            := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  change productMap (𝟙 X) ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).map f) ≫
      (categoricalProductIso X ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).obj n)).inv =
    (categoricalProductIso X ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).obj m)).inv ≫
      prod.map (𝟙 X) ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).map f)
  apply (cancel_mono
    (categoricalProductIso X ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).obj n)).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    categoricalProductIso_naturality, Iso.inv_hom_id_assoc]

/-- The literal sheaf differential retains its actual geometric face formula. -/
theorem unitUnderlying_d_app (n : ℕ) (X : (SmoothSite (Spec (.of k)))ᵒᵖ) :
    (((sheafToPresheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).map
      ((unitSingularSheafComplex k).d (n + 1) n)).app X) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      (largeUnitsPresheaf (Spec (.of k))).map
        (productMap (𝟙 X.unop) ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i)).op := by
  have h := AlternatingFaceMapComplex.obj_d_eq (unitSimplicialSheaf k) n
  have he := congrArg (fun f =>
    ((sheafToPresheaf (nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).map f).app X) h
  simp only [Functor.map_sum, Functor.map_zsmul, NatTrans.app_sum, NatTrans.app_zsmul] at he
  exact he

/-- All actual differentials agree before sheafification, including their alternating signs. -/
def unitRawComplexIso :
    SingularComplex.presheafObj (_root_.AlgebraicSimplex.cosimplicialSmoothSite k)
        (largeUnitsPresheaf (Spec (.of k))) ≅
      ((sheafToPresheaf (nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).mapHomologicalComplex (.down ℕ)).obj
        (unitSingularSheafComplex k) :=
  HomologicalComplex.Hom.isoOfComponents (unitRawTermIso k) (by
    intro i j hij
    have h : j + 1 = i := hij
    subst i
    apply NatTrans.ext
    funext X
    change (unitRawTermIso k (j + 1)).hom.app X ≫
        (((sheafToPresheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).map
          ((unitSingularSheafComplex k).d (j + 1) j)).app X) =
      ((SingularComplex.presheafObj (_root_.AlgebraicSimplex.cosimplicialSmoothSite k)
        (largeUnitsPresheaf (Spec (.of k)))).d (j + 1) j).app X ≫
          (unitRawTermIso k j).hom.app X
    rw [unitUnderlying_d_app, SingularComplex.presheafObj_d_app]
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp]
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    exact unitRawTermIso_simplex k X.unop (SimplexCategory.δ l))

/-- The native aC*Gm complex is the genuine literal-product unit sheaf complex. -/
def unitSheafifiedSingularIso :
    SingularComplex.sheafObj (nisnevichTopology (Spec (.of k)))
        (_root_.AlgebraicSimplex.cosimplicialSmoothSite k) (largeUnitsPresheaf (Spec (.of k))) ≅
      unitSingularSheafComplex k :=
  ((presheafToSheaf (nisnevichTopology (Spec (.of k)))
    AddCommGrpCat.{u + 1}).mapHomologicalComplex (.down ℕ)).mapIso (unitRawComplexIso k) ≪≫
      (NatIso.mapHomologicalComplex
        (asIso (sheafificationAdjunction (nisnevichTopology (Spec (.of k)))
          AddCommGrpCat.{u + 1}).counit) (.down ℕ)).app (unitSingularSheafComplex k)

end AlgebraicGeometry.Scheme.SmoothSite
