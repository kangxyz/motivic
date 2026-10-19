/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.LineOpenMaps

/-! # Native coordinates on the actual original whole cylinder

Intended upstream module:
`Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.CylinderNativeCoordinates`.
Incoming project consumers: `Motivic.Transfers.Presheaf.Actions.Norm.RefinedNormalization`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
variable {k : Type u} [Field k]
  (U T : SmoothSite (Spec (.of k))) [IsAffine U.left]
  (e : T ≅ SmoothSite.a1Cylinder (.of k) U)
attribute [local instance] sectionsAlgebra

/-- Canonical coordinates retain the original target scheme and cylinder isomorphism. -/
def originalCylinderNativeIso : T.left ≅ Spec (.of (Polynomial Γ(U.left, ⊤))) :=
  (SmoothSite.forgetScheme (Spec (.of k))).mapIso (e ≪≫ (affineLineIso U).symm)

/-- The native coordinate projection is exactly the original coefficient map. -/
@[reassoc]
theorem originalCylinderNativeIso_projection :
    (originalCylinderNativeIso U T e).hom ≫ polynomialProjection (.of Γ(U.left, ⊤)) =
      e.hom.left ≫ (SmoothSite.a1Projection (.of k) U).left ≫ U.left.isoSpec.hom := by
  have h := congrArg (fun f => f.left) (affineLineIso_projection U)
  change (affineLineIso U).hom.left ≫ (SmoothSite.a1Projection (.of k) U).left =
    polynomialProjection (.of Γ(U.left, ⊤)) ≫ U.left.isoSpec.inv at h
  have hi : (affineLineIso U).inv.left ≫ polynomialProjection (.of Γ(U.left, ⊤)) =
      (SmoothSite.a1Projection (.of k) U).left ≫ U.left.isoSpec.hom := by
    apply (cancel_epi (affineLineIso U).hom.left).mp
    rw [← Category.assoc]
    have hid := congrArg (fun f => f.left) (affineLineIso U).hom_inv_id
    change (affineLineIso U).hom.left ≫ (affineLineIso U).inv.left = 𝟙 _ at hid
    rw [hid, Category.id_comp, ← Category.assoc, h]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (e.hom.left ≫ (affineLineIso U).inv.left) ≫ _ = _
  rw [Category.assoc, hi]

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
