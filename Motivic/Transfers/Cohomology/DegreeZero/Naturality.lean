/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Cohomology.DegreeZero.Basic

/-!
# Coefficient naturality of degree-zero transfers

The signed transfer action on ordinary `H⁰` commutes with the actual ordinary
cohomology map of every morphism of sheaves with transfers.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe w u

namespace Motivic.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf

variable {k : Type u} [Field k]
variable [HasExt.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The actual ordinary cohomology coefficient map, evaluated on a correspondence object. -/
abbrev degreeZeroMap {F G : SheafWithTransfers.{u + 1} k} (η : F ⟶ G) (X : Cor k) :=
  ((LargeCohomology.presheafFunctor.{w, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) 0).map
      ((toSheaf.{u + 1} k).map η)).app (op X.toSmoothSite)

@[simp]
theorem degreeZeroSectionsEquiv_map {F G : SheafWithTransfers.{u + 1} k}
    (η : F ⟶ G) (X : Cor k)
    (x : LargeCohomology.H.{w, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toSheaf.{u + 1} k).obj F) 0 X.toSmoothSite) :
    degreeZeroSectionsEquiv G X (degreeZeroMap η X x) =
      η.hom.hom.app (op X) (degreeZeroSectionsEquiv F X x) :=
  LargeCohomology.zeroSections_naturality.{w, u + 1} _ ((toSheaf k).map η) _ x

/-- Signed transfers commute with the actual ordinary cohomology coefficient maps. -/
@[reassoc]
theorem degreeZeroTransfer_naturality {F G : SheafWithTransfers.{u + 1} k}
    (η : F ⟶ G) {X Y : Cor k} (α : X ⟶ Y) :
    degreeZeroTransfer F α ≫ degreeZeroMap η X =
      degreeZeroMap η Y ≫ degreeZeroTransfer G α := by
  ext x
  apply (degreeZeroSectionsEquiv G X).injective
  change degreeZeroSectionsEquiv G X (degreeZeroMap η X (degreeZeroTransfer F α x)) =
    degreeZeroSectionsEquiv G X (degreeZeroTransfer G α (degreeZeroMap η Y x))
  rw [degreeZeroSectionsEquiv_map, degreeZeroSectionsEquiv_transfer,
    degreeZeroSectionsEquiv_transfer, degreeZeroSectionsEquiv_map]
  exact ConcreteCategory.congr_hom (PresheafWithTransfers.transfer_naturality η.hom α)
    (degreeZeroSectionsEquiv F Y x)

end Motivic.SheafWithTransfers
