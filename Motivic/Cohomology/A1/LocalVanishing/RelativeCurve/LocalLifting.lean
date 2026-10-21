module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.Serre
public import Motivic.Cohomology.A1.Boundary.SquareDifferenceActions
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.DiagonalSigned
/-! # Relative curve class lifting from genuine framed presentation geometry

Serre constructs the four sections and the original whole finite-flat pencil. No
section, correspondence, endpoint or lifting premise is included. The geometric
frames remain explicit pending the local base/source restriction construction.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible Opposite
universe u
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite
/-- Literal lifting of restrictions of original sections, not all new sections. -/
def HasRestrictionDifferenceLifting {k : Type u} [Field k]
    (P : PresheafWithTransfers.{u + 1} k)
    {X Y T V : SmoothSite (Spec (.of k))} (φ : X ⟶ Y) (β : X ⟶ V) (α : X ⟶ T) : Prop :=
  ∀ d : sections P (Cor.mk Y), ∃ a : sections P (Cor.mk V), ∃ c : sections P (Cor.mk T),
    ((toPresheaf k).obj P).map β.op a - ((toPresheaf k).obj P).map α.op c =
      ((toPresheaf k).obj P).map φ.op d

theorem hasRestrictionDifferenceLifting_of_data {k : Type u} [Field k]
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    {X Y T V : SmoothSite (Spec (.of k))} (φ : X ⟶ Y) (β : X ⟶ V) (α : X ⟶ T)
    (h : Nonempty (GraphDivisorPencil.Data α β φ)) :
    HasRestrictionDifferenceLifting P φ β α := by
  obtain ⟨D⟩ := h
  intro x
  refine ⟨-transfer P D.psi x, -transfer P D.lam x, ?_⟩
  exact restriction_difference_eq_restriction_of_homotopy P hP φ β α
    D.lam D.psi D.correspondence D.endpoints.1 D.endpoints.2 x
end Motivic.PresheafWithTransfers

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
/-- The smoothness instance used in this module. -/
local instance relativeCurveLocalLiftingSmooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
variable (k : Type u) [Field k] (R : Type u) [CommRing R]
  (ι : Type u) (m : ℕ) (eι : ι ≃ Fin (m + 1)) [Finite ι]
  {X Y A B Z C D V : Scheme.{u}}
  [IsAffine Y] [IsAffine A] [IsAffine B] [IsAffine V]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ Spec (.of R)) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j]
  [hY : SmoothOfRelativeDimension 1 (j ≫ (f ≫ toSpec R ι))]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ (f ≫ toSpec R ι) = p ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a]
  (α : B ⟶ Y) [Smooth α] (β : B ⟶ A) [Flat β] (h : α ≫ p = β ≫ a)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))
  [IsNoetherianRing Γ(Y, ⊤)] [IsNoetherianRing Γ(A, ⊤)]
  [IsLocallyNoetherian (pullback (j ≫ (f ≫ toSpec R ι)) (f ≫ toSpec R ι))]
  [IsLocallyNoetherian (pullback (a ≫ q) (f ≫ toSpec R ι))]
  [IsClosedImmersion d] [IsClosedImmersion (s ≫ j)]

include m eι hq H e ha hd hY in
/-- Actual section existence is supplied by Serre, not included in the input data.
The remaining frames are explicit geometric input to this intermediate construction. -/
theorem exists_relativeCurve_lifting_of_boundary_frames
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ (f ≫ toSpec R ι))]
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
    (eA : affineBoundaryTwistFrames R ι (j ≫ (f ≫ toSpec R ι)) f
      (Hom.fullBoundaryProductMap (f ≫ toSpec R ι) j d s))
    (eN : affineBoundaryTwistFrames R ι (a ≫ q) f
      (psiBoundaryInclusion q (f ≫ toSpec R ι) j p hq a z s hs d))
    (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    PresheafWithTransfers.HasRestrictionDifferenceLifting P
      (relativeGraphMap k t (f ≫ toSpec R ι) j α v φ hφ)
      (relativeBeta k t q (f ≫ toSpec R ι) j a α p hq β h)
      (relativeAlpha k t (f ≫ toSpec R ι) j α) :=
  PresheafWithTransfers.hasRestrictionDifferenceLifting_of_data P hP _ _ _
    (exists_dataOfBoundaryFrames k R ι m eι t q f j p hq a α β h
      z s hs H e ha d hd v hc eA eN φ hφ)
end AlgebraicGeometry.Scheme.RelativeCurvePencil
