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
-/

class ScFamily {Obj : Type*} {index : Type*} where
  sc : index → Obj → Obj

class TgFamily {Obj : Type*} {index : Type*} where
  tg : index → Obj → Obj

class PCompFamily {Obj : Type*} {index : Type*} where
  pcomp : index → Obj → Obj →. Obj

class SingleSortedStruct (Obj : Type*) (index : Type*)
    extends ScFamily, TgFamily, PCompFamily where
  pcomp_dom : ∀ {i : index} {f g : Obj},
    (pcomp i g f).Dom ↔ sc i g = tg i f

def composable {Obj : Type*} {index : Type*} [SingleSortedStruct Obj index]
    (i : index) (g f : Obj) : Prop :=
  ScFamily.sc i g = TgFamily.tg i f

def comp {Obj : Type*} {index : Type*} [SingleSortedStruct Obj index]
    (i : index) (g f : Obj) (composable_gf : composable i g f) : Obj :=
  (PCompFamily.pcomp i g f).get (SingleSortedStruct.pcomp_dom.mpr composable_gf)

notation:100 g " ♯(" i:100 ")" f:100 " ← " composable_fg:100 =>
  comp i g f composable_fg

class SingleSortedCategoryFamily (Obj : Type*) (index : Type*)
    extends SingleSortedStruct Obj index where
  idemp_sc_sc : ∀ {i : index} {f : Obj},
    sc i (sc i f) = sc i f
  idemp_tg_sc : ∀ {i : index} {f : Obj},
    tg i (sc i f) = sc i f
  idemp_sc_tg : ∀ {i : index} {f : Obj},
    sc i (tg i f) = tg i f
  idemp_tg_tg : ∀ {i : index} {f : Obj},
    tg i (tg i f) = tg i f
  sc_comp_is_sc : ∀ {i : index} {f g : Obj}
      (composable_gf : composable i g f),
    sc i (g ♯(i) f ← composable_gf) = sc i f
  tg_comp_is_tg : ∀ {i : index} {f g : Obj}
      (composable_gf : composable i g f),
    tg i (g ♯(i) f ← composable_gf) = tg i g
  comp_sc_is_id : ∀ {i : index} {f : Obj},
    f ♯(i) (sc i f) ← idemp_tg_sc.symm = f
  comp_tg_is_id : ∀ {i : index} {f : Obj},
    (tg i f) ♯(i) f ← idemp_sc_tg = f
  assoc : ∀ {i : index} {f g h : Obj}
      (composable_gf : composable i g f)
      (composable_hg : composable i h g),
    let composable_h_gf : composable i h (g ♯(i) f ← composable_gf) :=
      composable_hg.trans (tg_comp_is_tg composable_gf).symm
    let composable_hg_f : composable i (h ♯(i) g ← composable_hg) f :=
      (sc_comp_is_sc composable_hg).trans composable_gf
    (h ♯(i) (g ♯(i) f ← composable_gf) ← composable_h_gf) =
      ((h ♯(i) g ← composable_hg) ♯(i) f ← composable_hg_f)

@[ext]
class SingleSortedCategory (Obj : Type*)
    extends SingleSortedCategoryFamily Obj (Fin 1)

instance {index : Nat} {k : Fin index} : CoeOut (Fin k) (Fin index) where
  coe j := Fin.castLE (Nat.le_of_lt k.isLt) j

class SingleSorted2CategoryFamily (Obj : Type*) (index : Nat)
    extends SingleSortedCategoryFamily Obj (Fin index) where
  idemp_sc : ∀ {k : Fin index} {j : Fin k} {f : Obj},
    sc k (sc j f) = sc j f ∧
    sc j f = sc j (sc k f) ∧
    sc j (sc k f) = sc j (tg k f)
  idemp_tg : ∀ {k : Fin index} {j : Fin k} {f : Obj},
    tg k (tg j f) = tg j f ∧
    tg j f = tg j (tg k f) ∧
    tg j (tg k f) = tg j (sc k f)
  -- TODO: Implement remaining axioms
  -- Issue: When trying to call `composable` or `comp` with `j : Fin k` (where
  -- `k : Fin index`), Lean cannot synthesize the
  -- `SingleSortedStruct Obj (Fin k)`
