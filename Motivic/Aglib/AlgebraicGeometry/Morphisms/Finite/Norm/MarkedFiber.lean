/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.ResidualFiber
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange
public import Motivic.Aglib.RingTheory.Norm.FiniteFree.MarkedFiber

/-! # The norm on an actual whole marked fiber

The canonical sections of the actual residual decomposition give the algebra
product used by determinant norm base change. Freeness is retained only for the
original chart module; no freeness or reducedness is imposed on the residual.


Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.MarkedFiber`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Norm.PrescribedGraphMarked`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphMarkedNorm`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.BoundaryRatio`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.FunctionalRatioBoundary`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u
namespace AlgebraicGeometry.FiniteSchemeNormBaseChange

/-- Global sections of the literal coproduct, with the concrete ring product. -/
def coproductSectionsIso (Z E : Scheme.{u}) :
    Γ(Z ⨿ E, ⊤) ≅ CommRingCat.of (Γ(Z, ⊤) × Γ(E, ⊤)) :=
  Scheme.coprodPresheafObjIso ⊤ ≪≫
    (prodIsProd Γ(Z, ⊤) Γ(E, ⊤)).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit Γ(Z, ⊤) Γ(E, ⊤))

@[reassoc] theorem coproductSectionsIso_fst (Z E : Scheme.{u}) :
    (coproductSectionsIso Z E).hom ≫ CommRingCat.ofHom (RingHom.fst _ _) =
      (coprod.inl : Z ⟶ Z ⨿ E).appTop := by
  dsimp only [coproductSectionsIso, Iso.trans_hom]
  rw [Category.assoc]
  change _ ≫ _ ≫ (CommRingCat.prodFan Γ(Z, ⊤) Γ(E, ⊤)).π.app
    (Discrete.mk WalkingPair.left) = _
  rw [IsLimit.conePointUniqueUpToIso_hom_comp]
  exact Scheme.coprodPresheafObjIso_hom_fst ⊤

@[reassoc] theorem coproductSectionsIso_snd (Z E : Scheme.{u}) :
    (coproductSectionsIso Z E).hom ≫ CommRingCat.ofHom (RingHom.snd _ _) =
      (coprod.inr : E ⟶ Z ⨿ E).appTop := by
  dsimp only [coproductSectionsIso, Iso.trans_hom]
  rw [Category.assoc]
  change _ ≫ _ ≫ (CommRingCat.prodFan Γ(Z, ⊤) Γ(E, ⊤)).π.app
    (Discrete.mk WalkingPair.right) = _
  rw [IsLimit.conePointUniqueUpToIso_hom_comp]
  exact Scheme.coprodPresheafObjIso_hom_snd ⊤

variable {R Q : Type u} [CommRing R] [CommRing Q] {T Y : Scheme.{u}}
  (p : T ⟶ Spec (.of R)) [IsFinite p] (φ : R →+* Q)
  (j : Y ⟶ T) [IsOpenImmersion j] (s : Spec (.of Q) ⟶ Y)
  (hs : (s ≫ j) ≫ p = Spec.map (CommRingCat.ofHom φ))
  (H : IsPullback s (𝟙 _) (j ≫ p) (Spec.map (CommRingCat.ofHom φ)))

/-- The actual fiber's ring decomposition, including its entire residual algebra. -/
def markedFiberSectionsRingEquiv :
    Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) ≃+*
      Q × Γ((Scheme.residualMarkedFiberOpen p j
        (Spec.map (CommRingCat.ofHom φ)) s hs).toScheme, ⊤) :=
  ((asIso (Scheme.markedResidualFiberIso p j (Spec.map (CommRingCat.ofHom φ)) s hs H).hom.appTop) ≪≫
    coproductSectionsIso (Spec (.of Q))
      (Scheme.residualMarkedFiberOpen p j
        (Spec.map (CommRingCat.ofHom φ)) s hs).toScheme).commRingCatIsoToRingEquiv.trans
    (RingEquiv.prodCongr (Scheme.ΓSpecIso (.of Q)).commRingCatIsoToRingEquiv (RingEquiv.refl _))

@[simp] theorem markedFiberSectionsRingEquiv_fst
    (b : Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤)) :
    (markedFiberSectionsRingEquiv p φ j s hs H b).1 =
      (Scheme.ΓSpecIso (.of Q)).hom
        ((Scheme.markedFiberSection p j (Spec.map (CommRingCat.ofHom φ)) s hs).appTop b) := by
  have h := congrArg (fun v =>
    (Scheme.markedResidualFiberIso p j (Spec.map (CommRingCat.ofHom φ)) s hs H).hom.appTop ≫ v)
    (coproductSectionsIso_fst (Spec (.of Q))
      (Scheme.residualMarkedFiberOpen p j (Spec.map (CommRingCat.ofHom φ)) s hs).toScheme)
  rw [← Scheme.Hom.comp_appTop, Scheme.markedResidualFiberIso_inl] at h
  exact congrArg (fun v => (Scheme.ΓSpecIso (.of Q)).hom (v b)) h

@[simp] theorem markedFiberSectionsRingEquiv_snd
    (b : Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤)) :
    (markedFiberSectionsRingEquiv p φ j s hs H b).2 =
      (Scheme.residualMarkedFiberOpen p j (Spec.map (CommRingCat.ofHom φ)) s hs).ι.appTop b := by
  have h := congrArg (fun v =>
    (Scheme.markedResidualFiberIso p j (Spec.map (CommRingCat.ofHom φ)) s hs H).hom.appTop ≫ v)
    (coproductSectionsIso_snd (Spec (.of Q))
      (Scheme.residualMarkedFiberOpen p j (Spec.map (CommRingCat.ofHom φ)) s hs).toScheme)
  rw [← Scheme.Hom.comp_appTop, Scheme.markedResidualFiberIso_inr] at h
  exact congrArg (fun v => v b) h

/-- The decomposition respects precisely the scalar action of the actual projection. -/
def markedFiberSectionsEquiv :
    let : Algebra Q Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
      (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
    let E := (Scheme.residualMarkedFiberOpen p j (Spec.map (CommRingCat.ofHom φ)) s hs)
    let : Algebra Q Γ(E.toScheme, ⊤) :=
      (scalarMap (E.ι ≫ pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
    Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) ≃ₐ[Q] Q × Γ(E.toScheme, ⊤) := by
  let : Algebra Q Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
    (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
  let E := Scheme.residualMarkedFiberOpen p j (Spec.map (CommRingCat.ofHom φ)) s hs
  let : Algebra Q Γ(E.toScheme, ⊤) :=
    (scalarMap (E.ι ≫ pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
  refine { markedFiberSectionsRingEquiv p φ j s hs H with commutes' := ?_ }
  intro a
  ext
  · change (markedFiberSectionsRingEquiv p φ j s hs H
      (algebraMap Q _ a)).1 = a
    rw [markedFiberSectionsRingEquiv_fst]
    change (Scheme.ΓSpecIso (.of Q)).hom
      (((pullback.snd p (Spec.map (CommRingCat.ofHom φ))).appTop ≫
        (Scheme.markedFiberSection p j (Spec.map (CommRingCat.ofHom φ)) s hs).appTop)
          ((Scheme.ΓSpecIso (.of Q)).inv a)) = a
    rw [← Scheme.Hom.comp_appTop, Scheme.markedFiberSection_snd]
    simp
  · change (markedFiberSectionsRingEquiv p φ j s hs H
      (algebraMap Q _ a)).2 = algebraMap Q Γ(E.toScheme, ⊤) a
    rw [markedFiberSectionsRingEquiv_snd]
    rfl

include H in
/-- Full marked and residual restrictions compute the norm of the original
finite map on a free chart. Only this original chart module is assumed free. -/
theorem norm_eq_marked_value
    (b : Γ(T, ⊤)) (a : Q)
    (hmarked : (s ≫ j).appTop b = (Scheme.ΓSpecIso (.of Q)).inv a)
    (hresidual : (Scheme.residualMarkedFiberMap p j
      (Spec.map (CommRingCat.ofHom φ)) s hs).appTop b = 1) :
    let : Algebra R Γ(T, ⊤) := (scalarMap p).toAlgebra
    ∀ [Module.Free R Γ(T, ⊤)], φ (Algebra.norm R b) = a := by
  dsimp only
  let : IsAffine T := isAffine_of_isAffineHom p
  let : Algebra R Q := φ.toAlgebra
  let : Algebra R Γ(T, ⊤) := (scalarMap p).toAlgebra
  let : Algebra Q Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
    (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
  let E := Scheme.residualMarkedFiberOpen p j (Spec.map (CommRingCat.ofHom φ)) s hs
  let : Algebra Q Γ(E.toScheme, ⊤) :=
    (scalarMap (E.ι ≫ pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
  intro hfree
  let := hfree
  let : Module.Finite R Γ(T, ⊤) := sections_finite p
  let e := (sectionsTensorEquiv p φ).trans (markedFiberSectionsEquiv p φ j s hs H)
  apply Algebra.norm_eq_marked_value_of_split_baseChange e b a
  change markedFiberSectionsRingEquiv p φ j s hs H
    (sectionsTensorEquiv p φ ((1 : Q) ⊗ₜ[R] b)) = (a, 1)
  rw [sectionsTensorEquiv_one_tmul]
  ext
  · rw [markedFiberSectionsRingEquiv_fst]
    change (Scheme.ΓSpecIso (.of Q)).hom
      (((pullback.fst p (Spec.map (CommRingCat.ofHom φ))).appTop ≫
        (Scheme.markedFiberSection p j (Spec.map (CommRingCat.ofHom φ)) s hs).appTop) b) = a
    rw [← Scheme.Hom.comp_appTop, Scheme.markedFiberSection_fst, hmarked]
    simp
  · rw [markedFiberSectionsRingEquiv_snd]
    exact hresidual

end AlgebraicGeometry.FiniteSchemeNormBaseChange
