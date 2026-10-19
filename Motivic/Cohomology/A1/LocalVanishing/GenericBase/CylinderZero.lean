/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.GenericBase.PositiveZero
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.WholeBase.CylinderTransport
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cartier.CylinderOpenImage

/-! # Positive original cylinder classes vanish over an actual generic base open

Canonical global sections are used only inside the proof. The class, final
base open, generic point and whole-cylinder restriction belong to the original
smooth-site object. The open depends on the class; strict A1 is not asserted.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.PolynomialLaurent
universe w u
namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf.LargeCohomology
open _root_.Algebra.Smooth
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
attribute [local instance] away_smooth

/-- Every positive original cylinder class of an HI Nisnevich sheaf with
transfers becomes zero on the cylinder over an affine open containing the
original generic point. The restriction is literally `a1Map (openInclusion X V)`. -/
theorem exists_generic_base_cylinder_positive_zero
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) (n : ℕ)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (x : H.{w, u + 1, u, u + 1} (nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) (n + 1) (a1Cylinder (.of k) X)) :
    ∃ V : X.left.Opens, IsAffineOpen V ∧ genericPoint X.left ∈ V ∧
      (presheaf.{w, u + 1, u, u + 1} (nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf k).obj F) (n + 1)).map
          (a1Map (.of k) (openInclusion X V)).op x = 0 := by
  let R := Γ(X.left, ⊤)
  let : Algebra k R := sectionsAlgebra X
  let P := presheaf.{w, u + 1, u, u + 1} (nisnevichTopology (Spec (.of k)))
    ((SheafWithTransfers.toSheaf k).obj F) (n + 1)
  let e := affineIso X
  let x' : H.{w, u + 1, u, u + 1} (nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) (n + 1) (lineSite (k := k) (R := R)) :=
    P.map (affineLineIso X).hom.op x
  obtain ⟨r, hr, s, hs, V, hV, hη, hz⟩ :=
    exists_relative_generic_base_positive_zero F hF n x'
  let : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
  let : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
  let φ : R →ₐ[k] Localization.Away r := IsScalarTower.toAlgHom k R (Localization.Away r)
  let ψ : Localization.Away r →ₐ[k] Localization.Away s :=
    IsScalarTower.toAlgHom k (Localization.Away r) (Localization.Away s)
  let Y := (opensFunctor (affineSite k (Localization.Away s))).obj V
  let : IsAffine Y.left := hV
  let : Nonempty Y.left := ⟨⟨genericPoint (Spec (.of (Localization.Away s))), hη⟩⟩
  let j : Y ⟶ X := openInclusion (affineSite k (Localization.Away s)) V ≫
    affineMorphism ψ ≫ affineMorphism φ ≫ e.hom
  have : IsOpenImmersion j.left := by
    change IsOpenImmersion (V.ι ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away r) (Localization.Away s))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ X.left.isoSpec.inv)
    infer_instance
  have hz' : P.map (a1Map (.of k) j).op x = 0 := by
    apply cylinder_restriction_zero_of_lineBaseOpen P e φ ψ V x
    change P.map (openInclusion (lineSite (k := k) (R := Localization.Away s))
      (boundaryBaseSourceOpen (boundaryLineProjection (Localization.Away s)) ⊤ V) ≫
        lineMap ψ ≫ lineMap φ).op
          (P.map (lineCylinderIso (k := k) (R := R) ≪≫ cylinderIso e).hom.op x) = 0 at hz
    have hO : boundaryBaseSourceOpen (boundaryLineProjection (Localization.Away s)) ⊤ V =
        polynomialProjection (.of (Localization.Away s)) ⁻¹ᵁ V := top_inf_eq _
    erw [hO] at hz
    exact hz
  exact exists_affine_generic_open_cylinder_zero_of_openImmersion P j x hz'

end Motivic.SheafCohomology
