module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.SerrePencilData
/-! # Actual Serre sections and finite-flat families produce original correcting data -/
set_option linter.hashCommand false
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
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
example
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ (f ≫ toSpec R ι))]
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
    (eA : affineBoundaryTwistFrames R ι (j ≫ (f ≫ toSpec R ι)) f
      (Hom.fullBoundaryProductMap (f ≫ toSpec R ι) j d s))
    (eN : affineBoundaryTwistFrames R ι (a ≫ q) f
      (psiBoundaryInclusion q (f ≫ toSpec R ι) j p hq a z s hs d))
    (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j) :
    Nonempty (DiagonalSignedPencilProducer.Data
      (relativeAlpha k t (f ≫ toSpec R ι) j α)
      (relativeBeta k t q (f ≫ toSpec R ι) j a α p hq β h)
      (relativeGraphMap k t (f ≫ toSpec R ι) j α v φ hφ)) :=
  exists_dataOfBoundaryFrames k R ι m eι t q f j p hq a α β h z s hs H e ha d hd
    v hc eA eN φ hφ
#print axioms exists_dataOfBoundaryFrames
end AlgebraicGeometry.Scheme.RelativeCurvePencil
