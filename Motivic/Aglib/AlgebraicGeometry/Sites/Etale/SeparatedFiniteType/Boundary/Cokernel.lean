module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Nisnevich
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification

/-! # The actual small-Nisnevich boundary cokernel

The closed inverse image is the left adjoint induced by actual base change of
finite-type separated étale neighborhoods. In particular it is not restriction
along the closed map in the big smooth slice.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {S T : Scheme.{u}}

/-- Direct image along the actual base-change functor of the small Nisnevich sites. -/
def directImage (b : T ⟶ S) :
    Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1} ⥤
      Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1} :=
  (baseChange b).sheafPushforwardContinuous _ _ _

/-- Genuine inverse image: the left adjoint, constructed from left Kan extension
and sheafification, rather than naive precomposition along a closed immersion. -/
def inverseImage (b : T ⟶ S) :
    Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1} :=
  (baseChange b).sheafPullback _ _ _

/-- The actual inverse/direct-image adjunction. -/
def imageAdjunction (b : T ⟶ S) : inverseImage b ⊣ directImage b :=
  (baseChange b).sheafAdjunctionContinuous _ _ _

variable {B : Scheme.{u}} (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
  {U Y Z : SmoothSite B}

/-- The literal projection from an étale base change to its ambient neighborhood. -/
def restrictionProjection (j : U ⟶ Y) :
    baseChange j.left ⋙ toSmoothSite U ⟶ toSmoothSite Y where
  app V := SmoothSite.homMk (pullback.fst V.hom j.left) (by
    change pullback.fst V.hom j.left ≫ (V.hom ≫ Y.hom) =
      pullback.snd V.hom j.left ≫ U.hom
    rw [← Category.assoc, pullback.condition, Category.assoc,
      MorphismProperty.Over.w])
  naturality V W f := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_fst _ _ _

/-- The genuine restriction from an ambient étale neighborhood to its base change. -/
def restrictionToDirectImage (j : U ⟶ Y) :
    (restrict Y AddCommGrpCat).obj F ⟶
      (directImage j.left).obj ((restrict U AddCommGrpCat).obj F) where
  hom := Functor.whiskerRight (NatTrans.op (restrictionProjection j)) F.obj

/-- The actual ambient sheaf cokernel of restriction to the open complement. -/
def boundaryAmbientCokernel (j : U ⟶ Y) :
    Sheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1} :=
  cokernel (restrictionToDirectImage F j)

/-- `B(Y,Z) = i⁻¹ coker(F|Y → j_* F|U)` on the actual small Nisnevich site of `Z`.
The definition retains both maps; the complement geometry belongs to the caller. -/
def boundaryCokernel (j : U ⟶ Y) (i : Z ⟶ Y) :
    Sheaf (nisnevichTopology Z.left) AddCommGrpCat.{u + 1} :=
  (inverseImage i.left).obj (boundaryAmbientCokernel F j)

/-- The native presheaf of section quotients on ambient étale neighborhoods. -/
def neighborhoodQuotient (j : U ⟶ Y) :
    (EtaleSeparatedFiniteType Y.left)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  cokernel (restrictionToDirectImage F j).hom

/-- Canonical map from the genuine neighborhood quotient to the closed inverse
image, using the actual sheaf cokernel projection and adjunction unit. -/
def neighborhoodQuotientToBoundary (j : U ⟶ Y) (i : Z ⟶ Y) :
    neighborhoodQuotient F j ⟶ ((directImage i.left).obj (boundaryCokernel F j i)).obj :=
  cokernel.desc _
    ((cokernel.π (restrictionToDirectImage F j)).hom ≫
      ((imageAdjunction i.left).unit.app (boundaryAmbientCokernel F j)).hom)
    (by
      rw [← Category.assoc]
      have h := congrArg (fun f ↦ f.hom) (cokernel.condition (restrictionToDirectImage F j))
      change (restrictionToDirectImage F j).hom ≫
        (cokernel.π (restrictionToDirectImage F j)).hom = 0 at h
      rw [h, zero_comp])

/-- On a representative the map is exactly quotient projection followed by
restriction to the inverse-image neighborhood, with no replacement quotient. -/
@[reassoc (attr := simp)]
theorem neighborhoodQuotientToBoundary_π (j : U ⟶ Y) (i : Z ⟶ Y) :
    cokernel.π (restrictionToDirectImage F j).hom ≫
      neighborhoodQuotientToBoundary F j i =
      (cokernel.π (restrictionToDirectImage F j)).hom ≫
        ((imageAdjunction i.left).unit.app (boundaryAmbientCokernel F j)).hom :=
  cokernel.π_desc _ _ _

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
