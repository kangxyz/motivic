/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.CoefficientCartesianSquare
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.PencilSites
/-! # The retained native base and line with their original field structures

Intended upstream module:
`Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeOriginalBase`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`AffineLine.NativeOriginalLineRestriction`.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom RelativeProjectiveLine Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {k : Type u} [Field k]
  (U : SmoothSite (Spec (.of k))) [IsAffine U.left]
  (B : (Spec Γ(U.left, ⊤)).Opens) [IsAffine B.toScheme]
  (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]

/-- The initial coefficient field map inherited from the original smooth base. -/
def nativeOriginalInitialFieldMap : Spec Γ(B.toScheme, ⊤) ⟶ Spec (.of k) :=
  B.toScheme.isoSpec.inv ≫ B.ι ≫ U.left.isoSpec.inv ≫ U.hom

instance nativeOriginalInitialFieldMap_smooth :
    Smooth (nativeOriginalInitialFieldMap U B) := by
  unfold nativeOriginalInitialFieldMap
  infer_instance

/-- Literally the nested field map used by the same native section data. -/
def nativeOriginalFinalFieldMap : Spec Γ(V.toScheme, ⊤) ⟶ Spec (.of k) :=
  boundaryBaseFieldMap V (boundaryBaseFieldMap O (nativeOriginalInitialFieldMap U B))

instance nativeOriginalFinalFieldMap_smooth :
    Smooth (nativeOriginalFinalFieldMap U B O V) := by
  unfold nativeOriginalFinalFieldMap
  infer_instance

/-- Only associativity is needed to compare the original-base and native field maps. -/
theorem nativeOriginalCoefficientMap_field :
    nativeOriginalCoefficientMap U B O V ≫ U.hom =
      nativeOriginalFinalFieldMap U B O V := by
  simp only [nativeOriginalCoefficientMap, nativeAffineBaseRestriction,
    nativeOriginalFinalFieldMap, boundaryBaseFieldMap,
    nativeOriginalInitialFieldMap, Category.assoc]

instance nativeOriginalCoefficientMap_open :
    IsOpenImmersion (nativeOriginalCoefficientMap U B O V) := by
  unfold nativeOriginalCoefficientMap nativeAffineBaseRestriction
  infer_instance

/-- The canonical spectrum of exactly the chosen common open. -/
def nativeOriginalBaseSite : SmoothSite (Spec (.of k)) :=
  mk (nativeOriginalFinalFieldMap U B O V)

/-- The actual inclusion into the original smooth base. -/
def nativeOriginalBaseInclusion : nativeOriginalBaseSite U B O V ⟶ U :=
  homMk (nativeOriginalCoefficientMap U B O V)
    (nativeOriginalCoefficientMap_field U B O V)

instance nativeOriginalBaseInclusion_open :
    IsOpenImmersion (nativeOriginalBaseInclusion U B O V).left :=
  nativeOriginalCoefficientMap_open U B O V

/-- The point already retained in the common-open witness proves nonemptiness. -/
theorem nativeOriginalBaseSite_nonempty (x : Spec Γ(O.toScheme, ⊤)) (hx : x ∈ V) :
    Nonempty (nativeOriginalBaseSite U B O V).left :=
  ⟨V.toScheme.isoSpec.hom ⟨x, hx⟩⟩

/-- The full native line with the literal nested field structure. -/
def nativeOriginalLineSite : SmoothSite (Spec (.of k)) :=
  mk (polynomialProjection (.of Γ(V.toScheme, ⊤)) ≫
    nativeOriginalFinalFieldMap U B O V)

/-- The whole-line projection, without a change of coefficient algebra. -/
def nativeOriginalLineProjection :
    nativeOriginalLineSite U B O V ⟶ nativeOriginalBaseSite U B O V :=
  homMk (polynomialProjection (.of Γ(V.toScheme, ⊤))) rfl

/-- The same native source is identified using only its original structure equation.
The statement is kept independent of nested coefficient expressions. -/
def nativeOriginalSourceIso
    {S X Y C : Scheme.{u}} [IsAffine S] [IsAffine Y]
    (t : S ⟶ Spec (.of k)) [Smooth t]
    (q : X ⟶ S) [Smooth q] (p : Y ⟶ X) [Smooth p]
    (π : C ⟶ S) (j : Y ⟶ C) [Smooth (j ≫ π)]
    (hq : j ≫ π = p ≫ q) :
    Scheme.RelativeCurvePencil.lambdaSourceSite k t π j ≅ mk (p ≫ q ≫ t) := by
  refine MorphismProperty.Over.isoMk (Iso.refl Y) ?_
  change 𝟙 Y ≫ (p ≫ q ≫ t) = (j ≫ π) ≫ t
  rw [Category.id_comp, hq, Category.assoc]

@[simp] theorem nativeOriginalSourceIso_hom_left
    {S X Y C : Scheme.{u}} [IsAffine S] [IsAffine Y]
    (t : S ⟶ Spec (.of k)) [Smooth t]
    (q : X ⟶ S) [Smooth q] (p : Y ⟶ X) [Smooth p]
    (π : C ⟶ S) (j : Y ⟶ C) [Smooth (j ≫ π)]
    (hq : j ≫ π = p ≫ q) :
    (nativeOriginalSourceIso t q p π j hq).hom.left = 𝟙 Y := rfl

end AlgebraicGeometry.Scheme.SmoothSite
