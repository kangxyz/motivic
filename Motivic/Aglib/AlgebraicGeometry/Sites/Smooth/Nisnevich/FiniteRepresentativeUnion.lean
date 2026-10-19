/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Sections
public import Mathlib.Data.Fin.Tuple.Basic

/-! # The actual finite union of two pointed representative families -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood

variable {B : Scheme.{u}} {Y : SmoothSite B} {n m : ℕ}
  (y : Fin n → Y.left) (R : ∀ i, NisnevichNeighborhood Y (y i))
  (z : Fin m → Y.left) (S : ∀ j, NisnevichNeighborhood Y (z j))

/-- Append the actual pointed neighborhoods, including their original base points. -/
def appendPointedFamily : Fin (n + m) → Σ p : Y.left, NisnevichNeighborhood Y p :=
  Fin.append (fun i => ⟨y i, R i⟩) (fun j => ⟨z j, S j⟩)

@[simp]
theorem appendPointedFamily_left (i : Fin n) :
    appendPointedFamily y R z S (Fin.castAdd m i) = ⟨y i, R i⟩ :=
  Fin.append_left _ _ i

@[simp]
theorem appendPointedFamily_right (j : Fin m) :
    appendPointedFamily y R z S (Fin.natAdd n j) = ⟨z j, S j⟩ :=
  Fin.append_right _ _ j

/-- The points in the literal appended family. -/
abbrev appendPoints (l : Fin (n + m)) : Y.left :=
  (appendPointedFamily y R z S l).1

/-- The original neighborhoods in the appended family; no new neighborhoods are chosen. -/
abbrev appendFamily (l : Fin (n + m)) :
    NisnevichNeighborhood Y (appendPoints y R z S l) :=
  (appendPointedFamily y R z S l).2

@[simp]
theorem appendPoints_left (i : Fin n) :
    appendPoints y R z S (Fin.castAdd m i) = y i := by
  simp [appendPoints, appendPointedFamily]

@[simp]
theorem appendPoints_right (j : Fin m) :
    appendPoints y R z S (Fin.natAdd n j) = z j := by
  simp [appendPoints, appendPointedFamily]

/-- The smooth object of an actual point-neighborhood pair. -/
def pointedObject (p : Σ p : Y.left, NisnevichNeighborhood Y p) : SmoothSite B :=
  (nisnevichNeighborhoodFunctor Y p.1).obj p.2

/-- The smooth objects of the appended pointed family. -/
abbrev appendObjects (l : Fin (n + m)) : SmoothSite B :=
  pointedObject (appendPointedFamily y R z S l)

@[simp]
theorem appendObjects_left (i : Fin n) :
    appendObjects y R z S (Fin.castAdd m i) =
      (nisnevichNeighborhoodFunctor Y (y i)).obj (R i) := by
  unfold appendObjects
  rw [appendPointedFamily_left]
  rfl

@[simp]
theorem appendObjects_right (j : Fin m) :
    appendObjects y R z S (Fin.natAdd n j) =
      (nisnevichNeighborhoodFunctor Y (z j)).obj (S j) := by
  unfold appendObjects
  rw [appendPointedFamily_right]
  rfl

/-- The first original object is the corresponding appended object, by only a cast. -/
def appendLeftIso (i : Fin n) :
    (nisnevichNeighborhoodFunctor Y (y i)).obj (R i) ≅
      appendObjects y R z S (Fin.castAdd m i) :=
  eqToIso (appendObjects_left y R z S i).symm

/-- The second original object is the corresponding appended object, by only a cast. -/
def appendRightIso (j : Fin m) :
    (nisnevichNeighborhoodFunctor Y (z j)).obj (S j) ≅
      appendObjects y R z S (Fin.natAdd n j) :=
  eqToIso (appendObjects_right y R z S j).symm

private theorem object_eqToHom_left {V W : SmoothSite B} (h : V = W) :
    (eqToHom h).left = eqToHom (congrArg (fun A : SmoothSite B => A.left) h) := by
  subst W
  rfl

private theorem pointed_eqToHom_toBase
    {p q : Σ p : Y.left, NisnevichNeighborhood Y p} (h : p = q) :
    eqToHom (congrArg (fun p : Σ p : Y.left, NisnevichNeighborhood Y p =>
      (nisnevichNeighborhoodFunctor Y p.1).obj p.2) h) ≫ q.2.toBase = p.2.toBase := by
  subst q
  simp

private theorem pointed_eqToHom_center
    {p q : Σ p : Y.left, NisnevichNeighborhood Y p} (h : p = q) :
    (eqToHom (congrArg (fun p : Σ p : Y.left, NisnevichNeighborhood Y p =>
      (nisnevichNeighborhoodFunctor Y p.1).obj p.2) h)).left p.2.center = q.2.center := by
  subst q
  rfl

/-- On schemes the left comparison is the identity transported along object equality. -/
@[simp]
theorem appendLeftIso_hom_left (i : Fin n) :
    (appendLeftIso y R z S i).hom.left =
      eqToHom (congrArg (fun V : SmoothSite B => V.left)
        (appendObjects_left y R z S i).symm) := by
  exact object_eqToHom_left (appendObjects_left y R z S i).symm

/-- On schemes the right comparison is the identity transported along object equality. -/
@[simp]
theorem appendRightIso_hom_left (j : Fin m) :
    (appendRightIso y R z S j).hom.left =
      eqToHom (congrArg (fun V : SmoothSite B => V.left)
        (appendObjects_right y R z S j).symm) := by
  exact object_eqToHom_left (appendObjects_right y R z S j).symm

@[simp, reassoc]
theorem appendLeftIso_hom_toBase (i : Fin n) :
    (appendLeftIso y R z S i).hom ≫
      (appendFamily y R z S (Fin.castAdd m i)).toBase = (R i).toBase := by
  dsimp only [appendLeftIso, eqToIso]
  exact pointed_eqToHom_toBase
    (p := ⟨y i, R i⟩) (q := appendPointedFamily y R z S (Fin.castAdd m i))
    (appendPointedFamily_left y R z S i).symm

@[simp, reassoc]
theorem appendRightIso_hom_toBase (j : Fin m) :
    (appendRightIso y R z S j).hom ≫
      (appendFamily y R z S (Fin.natAdd n j)).toBase = (S j).toBase := by
  dsimp only [appendRightIso, eqToIso]
  exact pointed_eqToHom_toBase
    (p := ⟨z j, S j⟩) (q := appendPointedFamily y R z S (Fin.natAdd n j))
    (appendPointedFamily_right y R z S j).symm

@[simp↓]
theorem appendLeftIso_hom_center (i : Fin n) :
    (appendLeftIso y R z S i).hom.left (R i).center =
      (appendFamily y R z S (Fin.castAdd m i)).center := by
  dsimp only [appendLeftIso, eqToIso]
  exact pointed_eqToHom_center
    (p := ⟨y i, R i⟩) (q := appendPointedFamily y R z S (Fin.castAdd m i))
    (appendPointedFamily_left y R z S i).symm

@[simp↓]
theorem appendRightIso_hom_center (j : Fin m) :
    (appendRightIso y R z S j).hom.left (S j).center =
      (appendFamily y R z S (Fin.natAdd n j)).center := by
  dsimp only [appendRightIso, eqToIso]
  exact pointed_eqToHom_center
    (p := ⟨z j, S j⟩) (q := appendPointedFamily y R z S (Fin.natAdd n j))
    (appendPointedFamily_right y R z S j).symm

variable (F : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})
  (s : ∀ i, F.obj (op ((nisnevichNeighborhoodFunctor Y (y i)).obj (R i))))
  (t : ∀ j, F.obj (op ((nisnevichNeighborhoodFunctor Y (z j)).obj (S j))))

/-- The two original section families on their actual appended objects. -/
def appendSections : ∀ l, F.obj (op (appendObjects y R z S l)) :=
  Fin.addCases
    (fun i => F.map (appendLeftIso y R z S i).inv.op (s i))
    (fun j => F.map (appendRightIso y R z S j).inv.op (t j))

@[simp]
theorem appendSections_left (i : Fin n) :
    F.map (appendLeftIso y R z S i).hom.op
      (appendSections y R z S F s t (Fin.castAdd m i)) = s i := by
  simp [appendSections, ← Functor.map_comp_apply, ← op_comp]

@[simp]
theorem appendSections_right (j : Fin m) :
    F.map (appendRightIso y R z S j).hom.op
      (appendSections y R z S F s t (Fin.natAdd n j)) = t j := by
  simp [appendSections, ← Functor.map_comp_apply, ← op_comp]

private theorem pointed_eqToHom_represents [IsAffine B]
    (a : ∀ p : Y.left, (nisnevichPointFiberCocone Y p F).pt)
    {p q : Σ p : Y.left, NisnevichNeighborhood Y p} (h : p = q)
    (s₀ : F.obj (op ((nisnevichNeighborhoodFunctor Y p.1).obj p.2)))
    (hs₀ : (nisnevichPointFiberCocone Y p.1 F).ι.app (op p.2) s₀ = a p.1) :
    (nisnevichPointFiberCocone Y q.1 F).ι.app (op q.2)
      (F.map (eqToHom (congrArg (fun p : Σ p : Y.left, NisnevichNeighborhood Y p =>
        (nisnevichNeighborhoodFunctor Y p.1).obj p.2) h.symm)).op s₀) = a q.1 := by
  subst q
  simpa using hs₀

/-- Appending representatives preserves the same original point-fiber tuple.
This is transport of the actual cocone maps and needs no sheaf condition. -/
theorem appendSections_represents [IsAffine B]
    (a : ∀ p : Y.left, (nisnevichPointFiberCocone Y p F).pt)
    (hs : ∀ i, (nisnevichPointFiberCocone Y (y i) F).ι.app (op (R i)) (s i) = a (y i))
    (ht : ∀ j, (nisnevichPointFiberCocone Y (z j) F).ι.app (op (S j)) (t j) = a (z j)) :
    ∀ l, (nisnevichPointFiberCocone Y (appendPoints y R z S l) F).ι.app
      (op (appendFamily y R z S l)) (appendSections y R z S F s t l) =
        a (appendPoints y R z S l) := by
  apply Fin.addCases
  · intro i
    simp only [appendSections, Fin.addCases_left]
    exact pointed_eqToHom_represents F a
      (appendPointedFamily_left y R z S i).symm (s i) (hs i)
  · intro j
    simp only [appendSections, Fin.addCases_right]
    exact pointed_eqToHom_represents F a
      (appendPointedFamily_right y R z S j).symm (t j) (ht j)

end AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood
