/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteAffineScalarCoordinates
public import Motivic.AlgebraicGeometry.SmoothSiteAffineLineZeroCoordinates
public import Motivic.AlgebraicGeometry.SmoothSiteFieldBaseChangeA1

/-! # Scalar polynomial coordinates preserve the whole original zero section

The two coordinate models are related through the native scalar cylinder. No
new polynomial algebra, zero scheme, or pointwise replacement is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Motivic.SmoothSiteAffineCoordinates

open AffineTorusPolynomialPresentation RelativePolynomialOpenSpans

variable (k R L : Type u) [Field k] [CommRing R] [Field L]
  [Algebra k R] [Algebra k L] [Algebra.Smooth k R]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance : Algebra.Smooth L (R ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L R)

local instance : Algebra.Smooth k (Polynomial R) := by
  let : Algebra.Smooth R (Polynomial R) := {}
  exact Algebra.Smooth.comp k R (Polynomial R)

local instance : Algebra.Smooth L ((Polynomial R) ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L (Polynomial R))

omit [Algebra.Smooth k R] in
/-- The relative polynomial structure map is the literal polynomial algebra map. -/
theorem polynomial_structure :
    Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R)) =
        Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial R))) := by
  have h : CommRingCat.ofHom (algebraMap k R) ≫
      CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) =
        CommRingCat.ofHom (algebraMap k (Polynomial R)) := by
    ext r
    rfl
  rw [← Spec.map_comp, h]

/-- The relative polynomial object and its affine algebra model have the same
underlying scheme and the same structure morphism. -/
def polynomialAffineIso : lineSite (k := k) (R := R) ≅ affineSite k (Polynomial R) :=
  MorphismProperty.Over.isoMk (Iso.refl (Spec (.of (Polynomial R)))) (by
    change 𝟙 (Spec (.of (Polynomial R))) ≫
      (affineSite k (Polynomial R)).hom = (lineSite (k := k) (R := R)).hom
    exact (Category.id_comp _).trans (polynomial_structure k R).symm)

/-- Scalar extension of the literal relative polynomial line, through its native
cylinder and the canonical tensor coordinates on the base. -/
def scalarLineIso :
    (SmoothSite.fieldBaseChange (algebraMap k L)).obj (lineSite (k := k) (R := R)) ≅
      lineSite (k := L) (R := R ⊗[k] L) :=
  (SmoothSite.fieldBaseChange (algebraMap k L)).mapIso lineCylinderIso ≪≫
    SmoothSite.fieldBaseChangeA1Iso (affineSite k R) ≪≫
      cylinderIso (SmoothSite.affineScalarIso k R L) ≪≫ lineCylinderIso.symm

/-- The actual tensor algebra of the original polynomial ring is identified with
the polynomial line over the actual scalar base, not a replacement presentation. -/
def tensorPolynomialLineIso :
    affineSite L ((Polynomial R) ⊗[k] L) ≅ lineSite (k := L) (R := R ⊗[k] L) :=
  (SmoothSite.affineScalarIso k (Polynomial R) L).symm ≪≫
    (SmoothSite.fieldBaseChange (algebraMap k L)).mapIso
      (polynomialAffineIso k R).symm ≪≫ scalarLineIso k R L

/-- The scalar polynomial coordinate comparison preserves the entire original
zero morphism, before any closed point is selected. -/
@[reassoc]
theorem scalarLineIso_zero :
    (SmoothSite.fieldBaseChange (algebraMap k L)).map
        (SmoothSite.a1Section (.of k) (affineSite k R) 0 ≫
          (lineCylinderIso (k := k) (R := R)).inv) ≫
      (scalarLineIso k R L).hom =
    (SmoothSite.affineScalarIso k R L).hom ≫
      SmoothSite.a1Section (.of L) (affineSite L (R ⊗[k] L)) 0 ≫
        (lineCylinderIso (k := L) (R := R ⊗[k] L)).inv := by
  simp only [scalarLineIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]
  have hz : (SmoothSite.fieldBaseChange (algebraMap k L)).map
      (SmoothSite.a1Section (.of k) (affineSite k R) 0) ≫
        (SmoothSite.fieldBaseChangeA1Iso (L := L) (affineSite k R)).hom =
      SmoothSite.a1Section (.of L)
        ((SmoothSite.fieldBaseChange (algebraMap k L)).obj (affineSite k R)) 0 :=
    SmoothSite.fieldBaseChangeA1Iso_zero (L := L) (affineSite k R)
  rw [← Category.assoc, ← Category.assoc, hz]
  change (SmoothSite.a1Section (.of L) _ 0 ≫
      SmoothSite.a1Map (.of L) (SmoothSite.affineScalarIso k R L).hom) ≫ _ = _
  rw [SmoothSite.a1Section_naturality, Category.assoc]

/-- A section on the whole original base, rather than merely its selected
point, gives the whole scalar zero lift into the native scalar étale source. -/
@[reassoc]
theorem scalarLineIso_wholeSection
    {Y : SmoothSite (Spec (.of k))} (p : Y ⟶ lineSite (k := k) (R := R))
    (s₀ : affineSite k R ⟶ Y)
    (hs₀ : s₀ ≫ p = SmoothSite.a1Section (.of k) (affineSite k R) 0 ≫
      (lineCylinderIso (k := k) (R := R)).inv) :
    (SmoothSite.affineScalarIso k R L).inv ≫
      (SmoothSite.fieldBaseChange (algebraMap k L)).map s₀ ≫
        (SmoothSite.fieldBaseChange (algebraMap k L)).map p ≫
          (scalarLineIso k R L).hom =
      SmoothSite.a1Section (.of L) (affineSite L (R ⊗[k] L)) 0 ≫
        (lineCylinderIso (k := L) (R := R ⊗[k] L)).inv := by
  rw [← Functor.map_comp_assoc, hs₀, scalarLineIso_zero]
  simp

/-- The source of the preceding identity is the literal polynomial evaluation
map, including its complete scheme structure. -/
theorem polynomial_zero_left :
    (SmoothSite.a1Section (.of k) (affineSite k R) 0 ≫
      (lineCylinderIso (k := k) (R := R)).inv).left =
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) := by
  change (SmoothSite.a1Section (.of k) (affineSite k R) 0).left ≫
    (lineCylinderIso (k := k) (R := R)).inv.left = _
  rw [← lineCylinderIso_zero]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom
    (Polynomial.evalRingHom (0 : R))) ≫ f.left)
      (lineCylinderIso (k := k) (R := R)).hom_inv_id

end Motivic.SmoothSiteAffineCoordinates
