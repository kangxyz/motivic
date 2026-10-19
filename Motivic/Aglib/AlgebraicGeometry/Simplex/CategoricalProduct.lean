/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Simplex.Basic
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products
public import Motivic.Aglib.Algebra.Homology.SingularComplex.Presheaf

/-!
# Categorical products for algebraic simplices
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicSimplex
open _root_.AlgebraicGeometry.Scheme
variable {k : Type u} [Field k]
/-- The literal relative products with the actual all-degree smooth simplex. -/
def productCosimplicialSmoothSite (X : SmoothSite (Spec (.of k))) :
    CosimplicialObject (SmoothSite (Spec (.of k))) where
  obj n := SmoothSite.product X ((cosimplicialSmoothSite k).obj n)
  map f := SmoothSite.productMap (𝟙 X) ((cosimplicialSmoothSite k).map f)
  map_id n := by simp
  map_comp f g := by
    rw [(cosimplicialSmoothSite k).map_comp]
    simpa only [Category.id_comp] using
      SmoothSite.productMap_comp (𝟙 X) (𝟙 X)
        ((cosimplicialSmoothSite k).map f) ((cosimplicialSmoothSite k).map g)

/-- The chosen categorical product simplex is canonically the literal relative product. -/
def categoricalSimplexProductIso (U : SmoothSite (Spec (.of k))) :
    SingularComplex.parameterCosimplicial (AlgebraicSimplex.cosimplicialSmoothSite k) U ≅
      AlgebraicSimplex.productCosimplicialSmoothSite U :=
  NatIso.ofComponents
    (fun n => SmoothSite.categoricalProductIso U
      ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n))
    (fun f => SmoothSite.categoricalProductIso_naturality (𝟙 U)
      ((AlgebraicSimplex.cosimplicialSmoothSite k).map f))


end AlgebraicSimplex
