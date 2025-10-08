/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Data.Pfun

/-!
# Single-sorted categories

In this file we define the notion of single-sorted $n$-category and
single-sorted $\omega$-category and its corresponding functor notions.

## Notation

Introduces notation in the `SingleSortedCategories` scope:
* `g ♯. f` for the partial composition of `f` and `g` (type as `\#.`),
* `g ♯ f ← composable_gf` for the composition of `f` and `g`, provided a proof
  that `g` and `f` are composable, `composable_gf`, (type as `\#` and `\<-`).
-/

namespace SingleSortedCategories

/-- A preliminare structure for defining a single-sorted category containing
the data about the category and its condition for existence of compositions. -/
class SingleSortedCategoryStruct (Obj : Type*) where
  /-- The source map. -/
  sc : Obj → Obj
  /-- The target map. -/
  tg : Obj → Obj
  /-- The partial composition operator. -/
  pcomp : Obj → Obj →. Obj
  /-- The domain of the partial composition operator. It states that two
  morphisms `g` and `f` are composable if and only if the source of `g`
  is equal to the target of `f`. -/
  pcomp_dom : ∀ {g f : Obj}, (pcomp g f).Dom ↔ sc g = tg f

/-- Notation for partial composition of morphisms. -/
scoped notation:80 g " ♯. " f:80 =>
  SingleSortedCategoryStruct.pcomp g f

/-- The source of a morphism. -/
def sc {Obj : Type*} [SingleSortedCategoryStruct Obj] (f : Obj) : Obj :=
  SingleSortedCategoryStruct.sc f

/-- The target of a morphism. -/
def tg {Obj : Type*} [SingleSortedCategoryStruct Obj] (f : Obj) : Obj :=
  SingleSortedCategoryStruct.tg f

/-- An auxiliary definition that constructs a proposition stating that the
source of a given morphism is equal to the target of another given morphism -/
def sc_is_tg {Obj : Type*} [SingleSortedCategoryStruct Obj]
    (g f : Obj) : Prop :=
  sc g = tg f

/-- A composition operator that, given two morphisms and a proof that the source
of one is the target of the other, returns the composition of the morphisms. -/
def comp {Obj : Type*} [SingleSortedCategoryStruct Obj]
    (g f : Obj) (composable_gf : sc_is_tg g f) : Obj :=
  (g ♯. f).get (SingleSortedCategoryStruct.pcomp_dom.mpr composable_gf)

/-- Notation for the composition of morphisms given a proof that the source of
one is the target of the other. -/
notation:80 g " ♯ " f:80 " ← " composable_gf:80 => comp g f composable_gf

/-- The `SingleSortedCateogry` typeclass, which extends the
`SingleSortedCategoryStruct` typeclass by adding the axioms that
define a single-sorted category. -/
class SingleSortedCategory (Obj : Type*) extends
    SingleSortedCategoryStruct Obj where
  /-- Source is idempotent when applied on itself. -/
  idemp_sc_sc : ∀ {f : Obj}, sc (sc f) = sc f
  /-- Target is idempotent when applied on source. -/
  idemp_tg_sc : ∀ {f : Obj}, tg (sc f) = sc f
  /-- Source is idempotent when applied on target. -/
  idemp_sc_tg : ∀ {f : Obj}, sc (tg f) = tg f
  /-- Target is idempotent when applied on itself. -/
  idemp_tg_tg : ∀ {f : Obj}, tg (tg f) = tg f
  /-- The source of a composition is the source of the first morphism. -/
  sc_comp_is_sc :
    ∀ {f g : Obj} (composable_gf : sc_is_tg g f),
    sc (g ♯ f ← composable_gf) = sc f
  /-- The target of a composition is the target of the second morphism. -/
  tg_comp_is_tg :
    ∀ {f g : Obj} (composable_gf : sc_is_tg g f),
    tg (g ♯ f ← composable_gf) = tg g
  /-- Composition with the source on the right is the morphism itself. -/
  comp_sc_id :
    ∀ {f : Obj},
    (f ♯ (sc f) ← (idemp_tg_sc.symm)) = f
  /-- Composition with the target on the left is the morphism itself. -/
  comp_tg_id :
    ∀ {f : Obj},
    ((tg f) ♯ f ← (idemp_sc_tg)) = f
  /-- Composition is associative. -/
  assoc :
    ∀ {f g h : Obj}
    (composable_gf : sc_is_tg g f) (composable_hg : sc_is_tg h g),
    -- Proof that `h` and `g ♯ f` are composable.
    let composable_h_gf : sc_is_tg h (g ♯ f ← composable_gf) :=
      composable_hg.trans (tg_comp_is_tg composable_gf).symm
    -- Proof that `h ♯ g` and `f` are composable.
    let composable_hg_f : sc_is_tg (h ♯ g ← composable_hg) f :=
      (sc_comp_is_sc composable_hg).trans composable_gf
    (h ♯ (g ♯ f ← composable_gf) ← composable_h_gf) =
    ((h ♯ g ← composable_hg) ♯ f ← composable_hg_f)

/-- A typeclass representing a functor between two single-sorted categories. -/
class SingleSortedFunctor (ObjC ObjD : Type*)
    [SingleSortedCategory ObjC] [SingleSortedCategory ObjD] where
  /-- The map on morphisms. -/
  map : ObjC → ObjD
  /-- The map preserves sources. -/
  map_sc : ∀ {f : ObjC}, map (sc f) = sc (map f)
  /-- The map preserves targets. -/
  map_tg : ∀ {f : ObjC}, map (tg f) = tg (map f)
  /-- The map preserves compositions. -/
  map_comp :
    ∀ {f g : ObjC} (composable_gf : sc_is_tg g f),
    let composable_mg_mf : sc_is_tg (map g) (map f) :=
      ((@map_sc g).symm.trans (congrArg map composable_gf)).trans (@map_tg f)
    map (g ♯ f ← composable_gf) = (map g) ♯ (map f) ← composable_mg_mf

end SingleSortedCategories
