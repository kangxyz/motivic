module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualPencilSites
/-! # The actual three maps at the correcting-homotopy endpoints -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S A X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r] [QuasiCompact r]
  (v : A ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion v]
  (α : X ⟶ S) [IsOpenImmersion α] [QuasiCompact α] (β : X ⟶ A) (h : α ≫ r ≫ p = β ≫ v)
  (U : (Spec (.of (Polynomial k))).Opens)

/-- The original overlap projection to the refined lambda source. -/
def pencilAlpha : commonSourceSite k p r α ⟶ diagonalSourceSite k p r :=
  SmoothSite.homMk α rfl

/-- The original overlap projection to the unchanged open's affine presentation. -/
def pencilBeta : commonSourceSite k p r α ⟶ fixedSourceSite k v :=
  SmoothSite.homMk β (commonSourceProjection_fixed k p r v α β h).symm

/-- The literal original overlap map, retaining both original coordinates. -/
def pencilGraphMap (φ : X ⟶ pullback U.ι p)
    (hφ : φ ≫ retainedInclusion k p U = α ≫ r ≫ inclusion k p) :
    commonSourceSite k p r α ⟶ retainedTargetSite k p U :=
  SmoothSite.homMk φ (by
    change φ ≫ retainedProjection k p U = commonSourceProjection k p r α
    dsimp only [retainedProjection, commonSourceProjection]
    rw [← Category.assoc, hφ]
    simp only [Category.assoc])
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
