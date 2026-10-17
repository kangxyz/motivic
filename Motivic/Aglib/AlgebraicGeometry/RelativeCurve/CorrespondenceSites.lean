module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.CommonRetainedSourceChange
public import Motivic.AlgebraicGeometry.SmoothSite
/-! # Original smooth source and target objects for relative correcting correspondences -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable (k : Type u) [Field k] {S X Y A B C V : Scheme.{u}}
  [IsAffine S] [IsAffine Y] [IsAffine A] [IsAffine B] [IsAffine V]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ S) [Smooth q] (π : C ⟶ S)
  (j : Y ⟶ C) [Smooth (j ≫ π)]
  (a : A ⟶ X) [Smooth a] (α : B ⟶ Y) [Smooth α]
  (v : V ⟶ C) [Smooth (v ≫ π)]

abbrev lambdaSourceSite : SmoothSite (Spec (.of k)) := SmoothSite.mk ((j ≫ π) ≫ t)
abbrev psiSourceSite : SmoothSite (Spec (.of k)) := SmoothSite.mk ((a ≫ q) ≫ t)
abbrev relativeCommonSite : SmoothSite (Spec (.of k)) :=
  SmoothSite.mk (commonProjection π j α ≫ t)
abbrev relativeTargetSite : SmoothSite (Spec (.of k)) := SmoothSite.mk ((v ≫ π) ≫ t)

def relativeAlpha : relativeCommonSite k t π j α ⟶ lambdaSourceSite k t π j :=
  SmoothSite.homMk α (by simp [commonProjection])

def relativeBeta (p : Y ⟶ X) (hq : j ≫ π = p ≫ q)
    (β : B ⟶ A) (h : α ≫ p = β ≫ a) :
    relativeCommonSite k t π j α ⟶ psiSourceSite k t q a :=
  SmoothSite.homMk β (by
    change β ≫ ((a ≫ q) ≫ t) = commonProjection π j α ≫ t
    rw [commonProjection_fixed q π j p hq a α β h]
    simp only [Category.assoc])

def relativeGraphMap (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j) :
    relativeCommonSite k t π j α ⟶ relativeTargetSite k t π v :=
  SmoothSite.homMk φ (by
    change φ ≫ ((v ≫ π) ≫ t) = commonProjection π j α ≫ t
    simpa only [Category.assoc, commonProjection] using
      congrArg (fun f => f ≫ π ≫ t) hφ)

/-- All retained source curves have their actual ordinary smooth-site properties. -/
theorem retainedProduct_site_properties {W : Scheme.{u}} [IsAffine W]
    (b : W ⟶ S) [Smooth b] :
    Smooth (pullback.fst b (v ≫ π) ≫ b ≫ t) ∧
      IsSeparated (pullback.fst b (v ≫ π) ≫ b ≫ t) ∧
      QuasiCompact (pullback.fst b (v ≫ π) ≫ b ≫ t) := by
  have : IsAffine (pullback b (v ≫ π)) := inferInstance
  exact ⟨inferInstance, inferInstance, inferInstance⟩
end AlgebraicGeometry.Scheme.RelativeCurvePencil
