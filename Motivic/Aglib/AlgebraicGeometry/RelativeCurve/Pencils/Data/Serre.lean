module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySectionData
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.DivisorPairs.AffineSource
/-! # Actual relative Serre sections produce the original signed-pencil data -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible PolynomialBoundaryPencil
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
open _root_.AlgebraicGeometry.Scheme.SmoothSite
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
/-- Native whole-boundary twist coefficient frames on an unchanged affine source. -/
def affineBoundaryTwistFrames
    (R : Type u) [CommRing R] (ι : Type u) {Y C W : Scheme.{u}} [IsAffine Y]
    (b : Y ⟶ Spec (.of R)) (f : C ⟶ ProjectiveSpace R ι)
    (z : W ⟶ pullback b (f ≫ toSpec R ι)) :=
  ∀ d : ℕ, (moduleTensorLeftFunctor W
    ((Modules.pullback z).obj ((Modules.pullback
      (ConstantCurve.affineSourceToProjectiveSpace R ι b f)).obj
        (ProjectiveSpace.twistingSheaf Γ(Y, ⊤) ι (d : ℤ))))).obj
    ((Modules.pullback z).obj
      (SheafOfModules.unit (pullback b (f ≫ toSpec R ι)).ringCatSheaf)) ≅
        SheafOfModules.unit W.ringCatSheaf

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
theorem exists_boundarySectionData_of_boundaryFrames
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ (f ≫ toSpec R ι))]
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
    (eA : affineBoundaryTwistFrames R ι (j ≫ (f ≫ toSpec R ι)) f
      (Hom.fullBoundaryProductMap (f ≫ toSpec R ι) j d s))
    (eN : affineBoundaryTwistFrames R ι (a ≫ q) f
      (psiBoundaryInclusion q (f ≫ toSpec R ι) j p hq a z s hs d)) :
    Nonempty (BoundarySectionData q (f ≫ toSpec R ι) j p hq a z s hs H e ha d hd) := by
  let iA := retainedProductInclusion (j ≫ (f ≫ toSpec R ι)) (f ≫ toSpec R ι) v
  let iN := retainedProductInclusion (a ≫ q) (f ≫ toSpec R ι) v
  let zA := Hom.fullBoundaryProductMap (f ≫ toSpec R ι) j d s
  let zN := psiBoundaryInclusion q (f ≫ toSpec R ι) j p hq a z s hs d
  have : IsClosedImmersion zA := Hom.fullBoundaryProduct_isClosedImmersion (f ≫ toSpec R ι) j d s hd
  have : IsClosedImmersion zN := psiBoundary_closed q (f ≫ toSpec R ι) j p hq a z s hs d hd
  have : IsAffine (retainedProduct (j ≫ (f ≫ toSpec R ι)) (f ≫ toSpec R ι) v) :=
    retainedProduct_affine (j ≫ (f ≫ toSpec R ι)) (f ≫ toSpec R ι) v
  have : IsAffine (retainedProduct (a ≫ q) (f ≫ toSpec R ι) v) :=
    retainedProduct_affine (a ≫ q) (f ≫ toSpec R ι) v
  have : SmoothOfRelativeDimension 1 (iA ≫ pullback.fst (j ≫ (f ≫ toSpec R ι)) (f ≫ toSpec R ι)) :=
    retainedProduct_smooth (j ≫ (f ≫ toSpec R ι)) (f ≫ toSpec R ι) v
  have : SmoothOfRelativeDimension 1 (iN ≫ pullback.fst (a ≫ q) (f ≫ toSpec R ι)) :=
    retainedProduct_smooth (a ≫ q) (f ≫ toSpec R ι) v
  obtain ⟨BA, hBA⟩ := CoherentGraph.exists_affineSource_normalized_divisor_pair R ι m eι
    (j ≫ (f ≫ toSpec R ι)) f zA eA iA
    (lambdaBoundary_retained_cover (f ≫ toSpec R ι) j s d v hc)
    (dualLineBundle _ (Hom.relativeCompactificationGraphLine (f ≫ toSpec R ι) j))
    (Hom.relativeFullBoundaryFrame q (f ≫ toSpec R ι) j p hq z s hs H e d hd)
  obtain ⟨BN, hBN⟩ := CoherentGraph.exists_affineSource_scalar_divisor_pair R ι m eι
    (a ≫ q) f zN eN iN (psiBoundary_retained_cover q (f ≫ toSpec R ι) j p hq a z s hs d v hc)
    (fixedProductBoundaryFrame q (f ≫ toSpec R ι) a z e ha d)
  obtain ⟨aS, bS, hA, haS, hbS, _, _⟩ := hBA BA le_rfl
  obtain ⟨nS, dS, hN, hnS, hdS, _, _⟩ := hBN BN le_rfl
  dsimp only [zA, Hom.fullBoundaryProductMap] at haS hbS
  dsimp only [zN] at hnS hdS
  let := haS
  let := hbS
  let := hnS
  let := hdS
  exact ⟨{
    T := _
    N := _
    aS := aS
    bS := bS
    nS := nS
    dS := dS
    hA := hA
    hN := hN
    a_unit := haS
    b_unit := hbS
    n_unit := hnS
    d_unit := hdS }⟩

include m eι hq H e ha hd hY in
/-- Actual section existence is supplied by Serre, not included in the input data.
The remaining frames are explicit geometric input to this intermediate construction. -/
theorem exists_dataOfBoundaryFrames
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ (f ≫ toSpec R ι))]
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
    (eA : affineBoundaryTwistFrames R ι (j ≫ (f ≫ toSpec R ι)) f
      (Hom.fullBoundaryProductMap (f ≫ toSpec R ι) j d s))
    (eN : affineBoundaryTwistFrames R ι (a ≫ q) f
      (psiBoundaryInclusion q (f ≫ toSpec R ι) j p hq a z s hs d))
    (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j) :
    Nonempty (GraphDivisorPencil.Data
      (relativeAlpha k t (f ≫ toSpec R ι) j α)
      (relativeBeta k t q (f ≫ toSpec R ι) j a α p hq β h)
      (relativeGraphMap k t (f ≫ toSpec R ι) j α v φ hφ)) := by
  obtain ⟨c⟩ := exists_boundarySectionData_of_boundaryFrames
    (R := R) (ι := ι) (m := m) (eι := eι) (q := q) (f := f) (j := j)
    (p := p) (hq := hq) (a := a) (z := z) (s := s) (hs := hs) (H := H)
    (e := e) (ha := ha) (d := d) (hd := hd) v hc eA eN
  exact ⟨c.toData k t q (f ≫ toSpec R ι) j p hq a α β h z s hs H e ha d hd v hc φ hφ⟩
end AlgebraicGeometry.Scheme.RelativeCurvePencil
