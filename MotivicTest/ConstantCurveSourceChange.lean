module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.CurveSourceChange
/-! Both the original target and original graph survive actual source change. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
example {X S B K : Scheme.{u}} (α : X ⟶ S) (π : B ⟶ K) (r : S ⟶ B) :
    IsPullback α (Scheme.constantSourceGraph α π r) (Scheme.Hom.compactificationGraph π r)
      (Scheme.constantSourceMap α (r ≫ π) π) :=
  Scheme.constantSourceGraph_isPullback α π r
#print axioms Scheme.constantSourceMap_isPullback
#print axioms Scheme.constantSourceGraph_isPullback
example {X S B K : Scheme.{u}} (α : X ⟶ S) [Flat α] (π : B ⟶ K) (r : S ⟶ B)
    [IsClosedImmersion (Scheme.Hom.compactificationGraph π r)]
    [(Scheme.Hom.idealModule (Scheme.Hom.compactificationGraph π r)).IsQuasicoherent] :=
  Scheme.constantSourceGraphIdealIso_hom_inclusion α π r
#print axioms Scheme.constantSourceGraphIdealIso_hom_inclusion
