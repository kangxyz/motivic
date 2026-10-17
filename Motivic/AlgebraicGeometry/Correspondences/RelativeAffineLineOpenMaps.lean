/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.RelativePolynomialOpenSpans
/-! # Literal maps between opens of relative affine lines in the original smooth site -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace Motivic.RelativePolynomialOpenSpans
variable {k R S : Type u} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra.Smooth k R] [Algebra k S] [Algebra.Smooth k S]

/-- An arbitrary original open in the relative line remains an object of Sm/k. -/
abbrev originalOpenSite (U : (Spec (.of R[X])).Opens) : SmoothSite (Spec (.of k)) := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  exact SmoothSite.mk (U.ι ≫ (lineSite (k := k) (R := R)).hom)

/-- The relative coefficient map is the actual polynomial map. -/
def lineMap (φ : R →ₐ[k] S) : lineSite (k := k) (R := S) ⟶ lineSite (k := k) (R := R) :=
  SmoothSite.homMk (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ.toRingHom))) (by
    change Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) = Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change Polynomial.map φ.toRingHom (C (algebraMap k R r)) = C (algebraMap k S r)
    rw [Polynomial.map_C]
    exact congrArg C (φ.commutes r))

/-- Actual target factorization through the given original open. -/
def openMap (φ : R →ₐ[k] S) (U : (Spec (.of R[X])).Opens)
    (V : (Spec (.of S[X])).Opens)
    (h : Set.range (V.ι ≫ (lineMap φ).left) ⊆ (U : Set (Spec (.of R[X])))) :
    originalOpenSite (k := k) V ⟶ originalOpenSite (k := k) U :=
  SmoothSite.homMk (IsOpenImmersion.lift U.ι (V.ι ≫ (lineMap φ).left) (by
    intro x hx
    exact ⟨⟨x, h hx⟩, rfl⟩)) (by
      change IsOpenImmersion.lift _ _ _ ≫ (U.ι ≫ _) = V.ι ≫ _
      rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc]
      exact congrArg (fun z => V.ι ≫ z) (MorphismProperty.Over.w (lineMap φ)))

@[reassoc (attr := simp)] theorem openMap_inclusion (φ : R →ₐ[k] S)
    (U : (Spec (.of R[X])).Opens) (V : (Spec (.of S[X])).Opens) (h) :
    (openMap φ U V h).left ≫ U.ι = V.ι ≫ (lineMap φ).left :=
  IsOpenImmersion.lift_fac _ _ _

/-- Ordinary open restriction, with no chosen affine model. -/
def originalInclusion (U V : (Spec (.of R[X])).Opens) (hVU : V ≤ U) :
    originalOpenSite (k := k) V ⟶ originalOpenSite (k := k) U :=
  SmoothSite.homMk (Scheme.homOfLE _ hVU) (by
    change Scheme.homOfLE _ _ ≫ (U.ι ≫ _) = _
    rw [← Category.assoc, Scheme.homOfLE_ι]
    rfl)

/-- An open containment supplies the same literal factorization. -/
def openMapOfLE (φ : R →ₐ[k] S) (U : (Spec (.of R[X])).Opens)
    (V : (Spec (.of S[X])).Opens) (h : V ≤ (lineMap φ).left ⁻¹ᵁ U) :
    originalOpenSite (k := k) V ⟶ originalOpenSite (k := k) U :=
  openMap φ U V (by
    rintro y ⟨x, rfl⟩
    exact h x.property)

@[reassoc (attr := simp)] theorem openMapOfLE_inclusion (φ : R →ₐ[k] S)
    (U : (Spec (.of R[X])).Opens) (V : (Spec (.of S[X])).Opens) (h) :
    (openMapOfLE φ U V h).left ≫ U.ι = V.ι ≫ (lineMap φ).left :=
  openMap_inclusion _ _ _ _

/-- The original punctured relative line is stable under the actual coefficient map. -/
theorem punctured_preimage (φ : R →ₐ[k] S) :
    principalOpen (X : S[X]) ≤ (lineMap φ).left ⁻¹ᵁ principalOpen (X : R[X]) := by
  intro x hx
  change (Polynomial.mapRingHom φ.toRingHom) X ∉ x.asIdeal
  change X ∉ x.asIdeal at hx
  simpa using hx

/-- The canonical base-change map of the original punctured relative lines. -/
def puncturedBaseMap (φ : R →ₐ[k] S) :
    openSite (k := k) (X : S[X]) ⟶ openSite (k := k) (X : R[X]) :=
  openMapOfLE φ _ _ (punctured_preimage φ)

end Motivic.RelativePolynomialOpenSpans
