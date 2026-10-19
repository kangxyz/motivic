/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.LineCoordinates
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen

/-! # Original relative-line maps under canonical cylinder coordinates

The canonical polynomial presentation preserves coefficient maps and every
actual base-open inclusion. No coefficient sheaf or cohomology group is changed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
variable {k R S : Type u} [Field k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra.Smooth k R] [Algebra k S] [Algebra.Smooth k S]

/-- The actual coefficient restriction is the original cylinder map. -/
@[reassoc] theorem lineCylinderIso_naturality (φ : R →ₐ[k] S) :
    lineMap φ ≫ (lineCylinderIso (k := k) (R := R)).hom =
      (lineCylinderIso (k := k) (R := S)).hom ≫
        a1Map (.of k) (affineMorphism φ) := by
  apply product_hom_ext
  · change (lineMap φ ≫ (lineCylinderIso (k := k) (R := R)).hom) ≫
        a1Projection (.of k) (affineSite k R) =
      ((lineCylinderIso (k := k) (R := S)).hom ≫
        a1Map (.of k) (affineMorphism φ)) ≫
          a1Projection (.of k) (affineSite k R)
    simp only [Category.assoc, a1Map_projection,
      lineCylinderIso_projection_assoc, lineCylinderIso_projection]
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ.toRingHom)) ≫
        polynomialProjection (.of R) =
      polynomialProjection (.of S) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact Polynomial.map_C φ.toRingHom
  · simp only [a1Map, Category.assoc, productMap_snd,
      Category.comp_id]
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ.toRingHom)) ≫
        (ambientIso (algebraMap k R)).hom ≫ pullback.snd _ _ =
      (ambientIso (algebraMap k S)).hom ≫ pullback.snd _ _
    rw [ambientIso_snd, ambientIso_snd, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp

omit [Algebra.Smooth k R] in
/-- Restricting only the base leaves the entire original affine-line product. -/
theorem lineBaseOpen_isPullback (V : (Spec (.of R)).Opens) :
    IsPullback (polynomialProjection (.of R) ∣_ V)
      ((polynomialProjection (.of R) ⁻¹ᵁ V).ι ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k R))))
      (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (polynomialProjection (.of k)) :=
  (isPullback_morphismRestrict (polynomialProjection (.of R)) V).paste_vert
    (ambient_isPullback (algebraMap k R))

/-- The original whole-line base open is the actual cylinder over that base open. -/
def lineBaseOpenCylinderIso (V : (Spec (.of R)).Opens) :
    (opensFunctor (lineSite (k := k) (R := R))).obj
      (polynomialProjection (.of R) ⁻¹ᵁ V) ≅
        a1Cylinder (.of k)
          ((opensFunctor (affineSite k R)).obj V) :=
  MorphismProperty.Over.isoMk (lineBaseOpen_isPullback (k := k) V).isoPullback (by
    change (lineBaseOpen_isPullback (k := k) V).isoPullback.hom ≫
      (pullback.fst _ _ ≫ (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))) = _
    rw [← Category.assoc, IsPullback.isoPullback_hom_fst]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    rfl)

/-- The whole-line comparison preserves the literal original base-open restriction. -/
@[reassoc] theorem lineBaseOpenCylinderIso_comp (V : (Spec (.of R)).Opens) :
    (lineBaseOpenCylinderIso (k := k) V).hom ≫
        a1Map (.of k) (openInclusion (affineSite k R) V) =
      openInclusion (lineSite (k := k) (R := R))
        (polynomialProjection (.of R) ⁻¹ᵁ V) ≫
          (lineCylinderIso (k := k) (R := R)).hom := by
  apply product_hom_ext
  · change ((lineBaseOpenCylinderIso (k := k) V).hom ≫
        a1Map (.of k) (openInclusion (affineSite k R) V)) ≫
          a1Projection (.of k) (affineSite k R) =
        (openInclusion (lineSite (k := k) (R := R))
          (polynomialProjection (.of R) ⁻¹ᵁ V) ≫
            (lineCylinderIso (k := k) (R := R)).hom) ≫
              a1Projection (.of k) (affineSite k R)
    simp only [Category.assoc, a1Map_projection, lineCylinderIso_projection]
    apply MorphismProperty.Over.Hom.ext
    change (lineBaseOpen_isPullback (k := k) V).isoPullback.hom ≫
        pullback.fst _ _ ≫ V.ι = _
    rw [← Category.assoc, IsPullback.isoPullback_hom_fst]
    exact morphismRestrict_ι _ _
  · simp only [a1Map, Category.assoc, productMap_snd,
      Category.comp_id]
    apply MorphismProperty.Over.Hom.ext
    change (lineBaseOpen_isPullback (k := k) V).isoPullback.hom ≫
        pullback.snd _ _ =
      (polynomialProjection (.of R) ⁻¹ᵁ V).ι ≫
        (ambientIso (algebraMap k R)).hom ≫ pullback.snd _ _
    rw [IsPullback.isoPullback_hom_snd, ambientIso_snd]

attribute [local instance] sectionsAlgebra

/-- Canonical affine coordinates preserve the projection to the original base. -/
@[reassoc] theorem affineLineIso_projection
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    (affineLineIso X).hom ≫ a1Projection (.of k) X =
      homMk (polynomialProjection (.of Γ(X.left, ⊤))) rfl ≫ (affineIso X).hom := by
  change ((lineCylinderIso (k := k) (R := Γ(X.left, ⊤))).hom ≫
    a1Map (.of k) (affineIso X).hom) ≫ a1Projection (.of k) X = _
  rw [Category.assoc, a1Map_projection, ← Category.assoc,
    lineCylinderIso_projection]

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
