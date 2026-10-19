/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Simplex.AffineSchemeUnitProjection
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.SheafIso
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products.ParameterProducts
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Reduced

/-! # Actual Gm homotopy invariance on all smooth objects -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]

/-- Genuine global units on the literal relative product with the n-simplex. -/
def simplexUnitsSheaf (n : ℕ) :
    Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1} :=
  ⟨(parameterProduct (_root_.AlgebraicSimplex.smoothSiteObj k n)).op ⋙
      largeUnitsPresheaf (Spec (.of k)),
    parameterProduct_op_comp_isSheaf _ _ (largeUnitsPresheaf_isSheaf _)⟩

/-- Pullback along the actual projection, as an ordinary Nisnevich sheaf map. -/
def unitsSimplexPullback (n : ℕ) :
    largeUnitsSheaf (Spec (.of k)) ⟶ simplexUnitsSheaf k n where
  hom :=
    { app X := (largeUnitsPresheaf (Spec (.of k))).map
        (productFst X.unop (_root_.AlgebraicSimplex.smoothSiteObj k n)).op
      naturality X Y f := by
        change (largeUnitsPresheaf _).map _ ≫ (largeUnitsPresheaf _).map _ =
          (largeUnitsPresheaf _).map _ ≫ (largeUnitsPresheaf _).map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        apply Quiver.Hom.unop_inj
        exact (productMap_fst f.unop (𝟙 (_root_.AlgebraicSimplex.smoothSiteObj k n))).symm }

/-- Actual affine projection pullback on units is an isomorphism. -/
theorem isIso_unitsSimplexPullback_affine (n : ℕ)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    IsIso ((unitsSimplexPullback k n).hom.app (op X)) := by
  have hi := @_root_.AlgebraicSimplex.isIso_units_affineSchemeProjection k _ X.left
    inferInstance inferInstance X.hom n
  have hf : IsIso (ringUnits.map
      (pullback.fst X.hom (_root_.AlgebraicSimplex.structureMap k n)).appTop) := by
    rw [← pullbackSymmetry_hom_comp_snd X.hom (_root_.AlgebraicSimplex.structureMap k n),
      Scheme.Hom.comp_appTop, ringUnits.map_comp]
    infer_instance
  change IsIso (AddCommGrpCat.uliftFunctor.map (ringUnits.map
    (pullback.fst X.hom (_root_.AlgebraicSimplex.structureMap k n)).appTop))
  infer_instance

/-- Gm is invariant under every actual algebraic simplex over any field,
on all smooth objects, including disconnected and empty ones. -/
instance isIso_unitsSimplexPullback (n : ℕ) : IsIso (unitsSimplexPullback k n) :=
  isIso_of_affine_app _ (isIso_unitsSimplexPullback_affine k n)

end AlgebraicGeometry.Scheme.SmoothSite
