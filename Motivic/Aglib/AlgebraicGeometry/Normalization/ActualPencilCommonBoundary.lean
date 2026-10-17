module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ConstantBoundarySourceChange
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualFixedOpenBoundary
/-! # The same whole boundary for the actual lambda and fixed-U psi products -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S A X : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r] (a : A ⟶ Spec (.of (Polynomial k)))
  (α : X ⟶ S) (β : X ⟶ A) (h : α ≫ r ≫ p = β ≫ a)
  (B : Type u) [CommRing B] (z : Polynomial k →+* B) (s : Spec (.of B) ⟶ S)
  (hs : s ≫ r ≫ p = Hom.boundaryCoordinateMap k B z)

abbrev commonSourceProjection := α ≫ ((r ≫ inclusion k p) ≫ projection k p)
abbrev commonAmbient := pullback (commonSourceProjection k p r α) (projection k p)
abbrev commonInfinity := pullback
  (pullback.snd (commonSourceProjection k p r α) (projection k p)) (infinityInclusion k p)
abbrev commonZero := pullback (commonSourceProjection k p r α)
  (s ≫ (r ≫ inclusion k p) ≫ projection k p)
abbrev commonBoundary := commonInfinity k p r α ⨿ commonZero k p r α B s

include h in
omit [IsSeparated p] [IsOpenImmersion r] in
theorem commonSourceProjection_fixed :
    commonSourceProjection k p r α = β ≫ (a ≫ Hom.boundaryLineProjection k) := by
  simp only [commonSourceProjection, Category.assoc, inclusion_projection]
  simpa only [Category.assoc] using
    congrArg (fun f => f ≫ Hom.boundaryLineProjection k) h

abbrev commonToDiagonal : commonAmbient k p r α ⟶ diagonalAmbient k p r :=
  constantSourceMapOfEq α ((r ≫ inclusion k p) ≫ projection k p)
    (projection k p) (commonSourceProjection k p r α) rfl

abbrev commonToFixed : commonAmbient k p r α ⟶ fixedAmbient k p a :=
  constantSourceMapOfEq β (a ≫ Hom.boundaryLineProjection k) (projection k p)
    (commonSourceProjection k p r α) (commonSourceProjection_fixed k p r a α β h)

def commonZeroInclusion : commonZero k p r α B s ⟶ commonAmbient k p r α :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s ≫ r ≫ inclusion k p)
    (by simpa only [Category.assoc] using (pullback.condition
      (f := commonSourceProjection k p r α)
      (g := s ≫ (r ≫ inclusion k p) ≫ projection k p)))

abbrev commonBoundaryInclusion : commonBoundary k p r α B s ⟶ commonAmbient k p r α :=
  coprod.desc (pullback.fst _ _) (commonZeroInclusion k p r α B s)

/-- The lambda boundary is pulled back along the actual first source leg. -/
def commonBoundaryToDiagonal : commonBoundary k p r α B s ⟶ diagonalBoundary k p r s :=
  coprod.map
    (constantInfinitySourceMap α ((r ≫ inclusion k p) ≫ projection k p)
      (projection k p) (commonSourceProjection k p r α) rfl (infinityInclusion k p))
    (constantSourceMapOfEq α ((r ≫ inclusion k p) ≫ projection k p)
      (s ≫ (r ≫ inclusion k p) ≫ projection k p) (commonSourceProjection k p r α) rfl)

omit [IsOpenImmersion r] in
theorem commonBoundaryToDiagonal_inclusion :
    commonBoundaryToDiagonal k p r α B s ≫ diagonalBoundaryMap k p r s =
      commonBoundaryInclusion k p r α B s ≫ commonToDiagonal k p r α := by
  apply coprod.hom_ext
  · simp [commonBoundaryToDiagonal, diagonalBoundaryMap, Hom.fullBoundaryProductMap,
      Hom.infinityProductMap, commonBoundaryInclusion, commonToDiagonal]
  · simp only [commonBoundaryToDiagonal, diagonalBoundaryMap, Hom.fullBoundaryProductMap,
      coprod.inr_map_assoc, coprod.inr_desc, commonBoundaryInclusion, coprod.inr_desc_assoc]
    apply pullback.hom_ext <;>
      simp [Hom.graphBoundaryRestriction, commonZeroInclusion, commonToDiagonal, Category.assoc]

/-- The same full Z component maps to the unchanged fixed-U boundary. -/
def commonZeroToFixed : commonZero k p r α B s ⟶ fixedZero k a B z :=
  pullback.lift (pullback.fst _ _ ≫ β) (pullback.snd _ _) (by
    have hz : s ≫ (r ≫ inclusion k p) ≫ projection k p =
        Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k := by
      simpa only [Category.assoc, inclusion_projection] using
        congrArg (fun f => f ≫ Hom.boundaryLineProjection k) hs
    rw [Category.assoc, ← commonSourceProjection_fixed k p r a α β h,
      pullback.condition]
    exact congrArg (fun f => pullback.snd (commonSourceProjection k p r α)
      (s ≫ (r ≫ inclusion k p) ≫ projection k p) ≫ f) hz)

/-- No component is removed: both maps share the original whole infinity and Z. -/
def commonBoundaryToFixed : commonBoundary k p r α B s ⟶ fixedBoundary k p a B z :=
  coprod.map
    (constantInfinitySourceMap β (a ≫ Hom.boundaryLineProjection k) (projection k p)
      (commonSourceProjection k p r α) (commonSourceProjection_fixed k p r a α β h)
      (infinityInclusion k p))
    (commonZeroToFixed k p r a α β h B z s hs)

omit [IsOpenImmersion r] in
/-- The fixed-U boundary inclusion commutes with the second actual source leg. -/
theorem commonBoundaryToFixed_inclusion :
    commonBoundaryToFixed k p r a α β h B z s hs ≫
      fixedBoundaryMap k p a B z (s ≫ r) (by simpa only [Category.assoc] using hs) =
    commonBoundaryInclusion k p r α B s ≫ commonToFixed k p r a α β h := by
  apply coprod.hom_ext
  · simp [commonBoundaryToFixed, fixedBoundaryMap, commonBoundaryInclusion, commonToFixed]
  · simp only [commonBoundaryToFixed, fixedBoundaryMap, coprod.inr_map_assoc,
      coprod.inr_desc, commonBoundaryInclusion, coprod.inr_desc_assoc]
    apply pullback.hom_ext
    · simp [commonZeroToFixed, commonZeroInclusion, commonToFixed, Category.assoc]
    · simp [commonZeroToFixed, commonZeroInclusion, commonToFixed, Category.assoc]

omit [IsOpenImmersion r] [IsSeparated p] in
/-- The first ambient source square is Cartesian, before restriction or zero cycles. -/
theorem commonToDiagonal_isPullback :
    IsPullback (commonToDiagonal k p r α)
      (pullback.fst (commonSourceProjection k p r α) (projection k p))
      (pullback.fst ((r ≫ inclusion k p) ≫ projection k p) (projection k p)) α :=
  constantSourceMapOfEq_isPullback α _ _ _ rfl

omit [IsOpenImmersion r] [IsSeparated p] in
/-- The second ambient source square is Cartesian with the same common compactification. -/
theorem commonToFixed_isPullback :
    IsPullback (commonToFixed k p r a α β h)
      (pullback.fst (commonSourceProjection k p r α) (projection k p))
      (pullback.fst (a ≫ Hom.boundaryLineProjection k) (projection k p)) β :=
  constantSourceMapOfEq_isPullback β _ _ _ (commonSourceProjection_fixed k p r a α β h)
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
