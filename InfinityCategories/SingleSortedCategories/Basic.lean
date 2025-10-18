/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Data.Pfun
import Mathlib.CategoryTheory.Category.Basic
import InfinityCategories.Data.NatIndex

open CategoryTheory

set_option linter.style.longLine false
set_option linter.style.commandStart false

/-!
# Single-sorted categories

In this file we define the notion of single-sorted $n$-category and
single-sorted $\omega$-category.

## Notation

- `g ♯[i] f ← composable_gf` denotes the composition of `g` and `f` at the
  `i`-th level, where `composable_gf` is a proof that the source of `g` is the
  target of `f` at that level.
-/

-- TODO: Document the file.

universe u

namespace SingleSortedCategories

class SingleSortedStruct (Obj : Type u)
    (index : Type) [NatIndex index] where
  sc : index → Obj → Obj
  tg : index → Obj → Obj
  pcomp : index → Obj → Obj →. Obj
  pcomp_dom : ∀ {i : index} {f g : Obj},
    (pcomp i g f).Dom ↔ sc i g = tg i f

scoped notation:100 g " sc_is_tg[" i:100 "] " f:100 =>
  SingleSortedStruct.sc i g = SingleSortedStruct.tg i f

scoped notation:100 g " ♯[" i:100 "] " f:100 =>
  SingleSortedStruct.pcomp i g f

scoped notation:80 pcomp " ← " prf:80 =>
  Part.get pcomp (SingleSortedStruct.pcomp_dom.mpr prf)

class SingleSortedCategoryFamily (Obj : Type u)
    (index : Type) [NatIndex index]
    extends SingleSortedStruct Obj index where
  scsc : ∀ {i : index} {f : Obj},
    sc i (sc i f) = sc i f
  tgsc : ∀ {i : index} {f : Obj},
    tg i (sc i f) = sc i f
  sctg : ∀ {i : index} {f : Obj},
    sc i (tg i f) = tg i f
  tgtg : ∀ {i : index} {f : Obj},
    tg i (tg i f) = tg i f
  sc_comp_is_sc : ∀ {i : index} {f g : Obj}
      (composable_gf : g sc_is_tg[i] f),
    sc i (g ♯[i] f ← composable_gf) = sc i f
  tg_comp_is_tg : ∀ {i : index} {f g : Obj}
      (composable_gf : g sc_is_tg[i] f),
    tg i (g ♯[i] f ← composable_gf) = tg i g
  comp_sc_is_id : ∀ {i : index} {f : Obj},
    f ♯[i] (sc i f) ← tgsc.symm = f
  comp_tg_is_id : ∀ {i : index} {f : Obj},
    (tg i f) ♯[i] f ← sctg = f
  assoc : ∀ {i : index} {f g h : Obj}
      (composable_gf : g sc_is_tg[i] f)
      (composable_hg : h sc_is_tg[i] g),
    let composable_h_gf : h sc_is_tg[i] (g ♯[i] f ← composable_gf) :=
      composable_hg.trans (tg_comp_is_tg composable_gf).symm
    let composable_hg_f : (h ♯[i] g ← composable_hg) sc_is_tg[i] f :=
      (sc_comp_is_sc composable_hg).trans composable_gf
    (h ♯[i] (g ♯[i] f ← composable_gf) ← composable_h_gf) =
      ((h ♯[i] g ← composable_hg) ♯[i] f ← composable_hg_f)

class SingleSorted2CategoryFamily (Obj : Type u)
    (index : Type) [NatIndex index]
    extends SingleSortedCategoryFamily Obj index where
  sckscj : ∀ {k : index} {j : Fin k} {f : Obj},
    sc k (sc j f) = sc j f
  scjsck : ∀ {k : index} {j : Fin k} {f : Obj},
    sc j (sc k f) = sc j f
  scjtgk : ∀ {k : index} {j : Fin k} {f : Obj},
    sc j (tg k f) = sc j f
  tgktgj : ∀ {k : index} {j : Fin k} {f : Obj},
    tg k (tg j f) = tg j f
  tgjtgk : ∀ {k : index} {j : Fin k} {f : Obj},
    tg j (tg k f) = tg j f
  tgjsck : ∀ {k : index} {j : Fin k} {f : Obj},
    tg j (sc k f) = tg j f
  -- Method for j-sources
  composable_j_sc {k : index} {j : Fin k} {f g : Obj} (composable_j_gf : g sc_is_tg[(j : index)] f) : (sc k g) sc_is_tg[(j : index)] (sc k f) := by
    calc
      sc j (sc k g) = sc j g        := scjsck
      _             = tg j f        := composable_j_gf
      _             = tg j (sc k f) := tgjsck.symm
  -- Method for j-targets
  composable_j_tg {k : index} {j : Fin k} {f g : Obj} (composable_j_gf : g sc_is_tg[(j : index)] f) : (tg k g) sc_is_tg[(j : index)] (tg k f) := by
    calc
      sc j (tg k g) = sc j g        := scjtgk
      _             = tg j f        := composable_j_gf
      _             = tg j (tg k f) := tgjtgk.symm
  sc_comp_is_comp_sc : ∀ {k : index} {j : Fin k} {f g : Obj}
      (composable_j_gf : g sc_is_tg[(j : index)] f),
    sc k (g ♯[(j : index)] f ← composable_j_gf)
    = ((sc k g) ♯[(j : index)] (sc k f)) ← composable_j_sc composable_j_gf
  tg_comp_is_comp_tg : ∀ {k : index} {j : Fin k} {f g : Obj}
      (composable_j_gf : g sc_is_tg[(j : index)] f),
    tg k (g ♯[(j : index)] f ← composable_j_gf)
    = ((tg k g) ♯[(j : index)] (tg k f)) ← composable_j_tg composable_j_gf
  -- Method for left exchange
  composable_k_left {k : index} {j : Fin k} {f₁ f₂ g₁ g₂ : Obj}
      (composable_k_g2g1 : g₂ sc_is_tg[(k : index)] g₁)
      (composable_k_f2f1 : f₂ sc_is_tg[(k : index)] f₁)
      (composable_j_g2f2 : g₂ sc_is_tg[(j : index)] f₂)
      (composable_j_g1f1 : g₁ sc_is_tg[(j : index)] f₁) :
    (g₂ ♯[(j : index)] f₂ ← composable_j_g2f2) sc_is_tg[(k : index)] (g₁ ♯[(j : index)] f₁ ← composable_j_g1f1) := by
      calc
        sc k (g₂ ♯[(j : index)] f₂ ← composable_j_g2f2) = (sc k g₂) ♯[(j : index)] (sc k f₂) ← _           := sc_comp_is_comp_sc composable_j_g2f2
        _                                               = (tg k g₁) ♯[(j : index)] (sc k f₂) ← _           := congrArg (fun x => (x ♯[(j : index)] (sc k f₂)) ← _) composable_k_g2g1
        _                                               = (tg k g₁) ♯[(j : index)] (tg k f₁) ← _           := congrArg (fun x => ((tg k g₁) ♯[(j : index)] x) ← _) composable_k_f2f1
        _                                               = tg k (g₁ ♯[(j : index)] f₁ ← composable_j_g1f1)  := (tg_comp_is_comp_tg composable_j_g1f1).symm
  -- Method for right exchange
  composable_k_right {k : index} {j : Fin k} {f₁ f₂ g₁ g₂ : Obj}
      (composable_k_g2g1 : g₂ sc_is_tg[(k : index)] g₁)
      (composable_k_f2f1 : f₂ sc_is_tg[(k : index)] f₁)
      (composable_j_g2f2 : g₂ sc_is_tg[(j : index)] f₂)
      (composable_j_g1f1 : g₁ sc_is_tg[(j : index)] f₁) :
    (g₂ ♯[(k : index)] g₁ ← composable_k_g2g1) sc_is_tg[(j : index)] (f₂ ♯[(k : index)] f₁ ← composable_k_f2f1) := by
      calc
        sc j (g₂ ♯[(k : index)] g₁ ← composable_k_g2g1) = sc j (sc k (g₂ ♯[(k : index)] g₁ ← composable_k_g2g1))  := sckscj.symm
        _                                               = sc j (sc k g₁)                                          := congrArg (fun x => sc j x) sc_comp_is_sc
        _                                               = sc j g₁                                                 := scjsck
        _                                               = tg j f₁                                                 := composable_j_g1f1
        _                                               = tg j (sc k f₁)                                          := tgjsck.symm
        _                                               = tg j (sc k (f₂ ♯[(k : index)] f₁ ← composable_k_f2f1))  := congrArg (fun x => tg j x) sc_comp_is_sc.symm
        _                                               = tg j (f₂ ♯[(k : index)] f₁ ← composable_k_f2f1)         := tgsck
  exchange : ∀ {k : index} {j : Fin k} {f₁ f₂ g₁ g₂ : Obj}
      (composable_k_g2g1 : g₂ sc_is_tg[(k : index)] g₁)
      (composable_k_f2f1 : f₂ sc_is_tg[(k : index)] f₁)
      (composable_j_g2f2 : g₂ sc_is_tg[(j : index)] f₂)
      (composable_j_g1f1 : g₁ sc_is_tg[(j : index)] f₁),
    ((g₂ ♯[(j : index)] f₂ ← composable_j_g2f2) ♯[(k : index)] (g₁ ♯[(j : index)] f₁ ← composable_j_g1f1)) ← composable_k_left composable_k_g2g1 composable_k_f2f1 composable_j_g2f2 composable_j_g1f1
    = ((g₂ ♯[(k : index)] g₁ ← composable_k_g2g1) ♯[(j : index)]  (f₂ ♯[(k : index)] f₁ ← composable_k_f2f1)) ← composable_k_right composable_k_g2g1 composable_k_f2f1 composable_j_g2f2 composable_j_g1f1

@[ext]
class SingleSortedCategory (Obj : Type*)
    extends SingleSortedCategoryFamily Obj (Fin 1)

@[ext]
class SingleSorted2Category (Obj : Type*)
    extends SingleSorted2CategoryFamily Obj (Fin 2)

@[ext]
class SingleSortedNCategory (Obj : Type*) (index : Nat)
    extends SingleSorted2CategoryFamily Obj (Fin index)

@[ext]
class SingleSortedOmegaCategory (Obj : Type*)
    extends SingleSorted2CategoryFamily Obj Nat where
    cell : ∀ {f : Obj}, ∃ (k : Nat), f = sc k f

@[ext]
structure SingleSortedFunctorFamily (Obj₁ Obj₂ : Type*) (index : Type) [NatIndex index] [SingleSortedCategoryFamily Obj₁ index] [SingleSortedCategoryFamily Obj₂ index] where
  map : Obj₁ → Obj₂
  mapsc : ∀ {i : index} {f : Obj₁}, map (SingleSortedStruct.sc i f) = SingleSortedStruct.sc i (map f)
  maptg : ∀ {i : index} {f : Obj₁}, map (SingleSortedStruct.tg i f) = SingleSortedStruct.tg i (map f)
  composable_map {i : index} {f g : Obj₁} (composable_gf : g sc_is_tg[i] f) : (map g) sc_is_tg[i] (map f) := by
      calc
        SingleSortedStruct.sc i (map g) = map (SingleSortedStruct.sc i g) := mapsc.symm
        _                               = map (SingleSortedStruct.tg i f) := congrArg map composable_gf
        _                               = SingleSortedStruct.tg i (map f) := maptg
  mapcomp : ∀ {i : index} {f g : Obj₁} (composable_gf : g sc_is_tg[i] f),
    map (g ♯[i] f ← composable_gf) = (map (g) ♯[i] map (f)) ← composable_map composable_gf

-- The composition of two SingleSortedFunctorFamilies is a SingleSortedFunctorFamily
def SingleSortedFunctorFamily.comp {Obj₁ Obj₂ Obj₃ : Type*} {index : Type} [NatIndex index]
  [SingleSortedCategoryFamily Obj₁ index] [SingleSortedCategoryFamily Obj₂ index]
  [SingleSortedCategoryFamily Obj₃ index] (G : SingleSortedFunctorFamily Obj₂ Obj₃ index)
  (F : SingleSortedFunctorFamily Obj₁ Obj₂ index) : SingleSortedFunctorFamily Obj₁ Obj₃ index := by
    refine {
      map := by
        intro f
        exact G.map (F.map f)
      mapsc := by
        intro i f
        calc
          G.map (F.map (SingleSortedStruct.sc i f)) = G.map (SingleSortedStruct.sc i (F.map f)) := congrArg G.map F.mapsc
          _                                         = SingleSortedStruct.sc i (G.map (F.map f)) := G.mapsc
      maptg := by
        intro i f
        calc
          G.map (F.map (SingleSortedStruct.tg i f)) = G.map (SingleSortedStruct.tg i (F.map f)) := congrArg G.map F.maptg
          _                                         = SingleSortedStruct.tg i (G.map (F.map f)) := G.maptg
      composable_map := by
        intro i f g composable_gf
        exact G.composable_map (F.composable_map composable_gf)
      mapcomp := by
        intro i f g composable_gf
        calc
          G.map (F.map (g ♯[i] f ← composable_gf)) = G.map ((F.map g) ♯[i] (F.map f) ← (F.composable_map composable_gf)) := congrArg G.map (F.mapcomp composable_gf)
          _ = (G.map (F.map g)) ♯[i] (G.map (F.map f)) ← (G.composable_map (F.composable_map composable_gf)) := G.mapcomp (F.composable_map composable_gf)
    }

-- The composition of SingleSortedFunctorFamilies is associative
theorem SingleSortedFunctorFamily.assoc {Obj₁ Obj₂ Obj₃ Obj₄ : Type*} {index : Type} [NatIndex index]
  [SingleSortedCategoryFamily Obj₁ index] [SingleSortedCategoryFamily Obj₂ index]
  [SingleSortedCategoryFamily Obj₃ index] [SingleSortedCategoryFamily Obj₄ index]
  (F : SingleSortedFunctorFamily Obj₁ Obj₂ index) (G : SingleSortedFunctorFamily Obj₂ Obj₃ index)
  (H : SingleSortedFunctorFamily Obj₃ Obj₄ index) : SingleSortedFunctorFamily.comp H (SingleSortedFunctorFamily.comp G F) =
  SingleSortedFunctorFamily.comp (SingleSortedFunctorFamily.comp H G) F := by
  ext
  rfl

-- The identity SingleSortedFunctorFamily
def SingleSortedFunctorFamily.id (Obj : Type*) (index : Type) [NatIndex index]
  [SingleSortedCategoryFamily Obj index] : SingleSortedFunctorFamily Obj Obj index := by
    refine{
      map := by
        intro f
        exact f
      mapsc := by
        intros
        exact rfl
      maptg := by
        intros
        exact rfl
      composable_map := by
        intro _ _ _ composable_gf
        exact composable_gf
      mapcomp := by
        intros
        exact rfl
    }

-- The identity SingleSortedFunctorFamily is a left identity for composition
theorem SingleSortedFunctorFamily.id_comp {Obj₁ Obj₂ : Type*} {index : Type} [NatIndex index]
  [SingleSortedCategoryFamily Obj₁ index] [SingleSortedCategoryFamily Obj₂ index]
  (F : SingleSortedFunctorFamily Obj₁ Obj₂ index) : (id Obj₂ index).comp F = F := by
    ext
    rfl

-- The identity SingleSortedFunctorFamily is a right identity for composition
theorem SingleSortedFunctorFamily.comp_id {Obj₁ Obj₂ : Type*} {index : Type} [NatIndex index]
  [SingleSortedCategoryFamily Obj₁ index] [SingleSortedCategoryFamily Obj₂ index]
  (F : SingleSortedFunctorFamily Obj₁ Obj₂ index) : F.comp (id Obj₁ index)= F := by
    ext
    rfl


-- The SingleSortedCategoryFamilyCat
structure SingleSortedCategoryFamilyCat (index : Type) [NatIndex index] where
  Obj : Type u
  str : SingleSortedCategoryFamily Obj index


-- The category of SingleSortedFamilies and SingleSortedFunctorFamilies
instance SingleSortedFamilyCat (index : Type) [NatIndex index] : LargeCategory (SingleSortedCategoryFamilyCat index) where
  Hom := by
    intro C1 C2
    let h1 := C1.str
    let h2 := C2.str
    exact (SingleSortedFunctorFamily C1.Obj C2.Obj index)
  id := by
    intro C
    intro h1 h2
    exact SingleSortedFunctorFamily.id C.Obj index
  comp := by
    intro C1 C2 C3 F G hF hG
    let h1 := C1.str
    let h2 := C2.str
    let h3 := C3.str
    exact SingleSortedFunctorFamily.comp G F
  id_comp := by
    intro C1 C2 F
    let h1 := C1.str
    let h2 := C2.str
    exact SingleSortedFunctorFamily.id_comp F
  comp_id := by
    intro C1 C2 F
    let h1 := C1.str
    let h2 := C2.str
    exact SingleSortedFunctorFamily.comp_id F
  assoc := by
    intro C1 C2 C3 C4 F G H
    let h1 := C1.str
    let h2 := C2.str
    let h3 := C3.str
    let h4 := C4.str
    exact SingleSortedFunctorFamily.assoc F G H

@[ext]
structure SingleSortedFunctor (Obj₁ Obj₂ : Type*) [SingleSortedCategory Obj₁] [SingleSortedCategory Obj₂]
    extends SingleSortedFunctorFamily Obj₁ Obj₂ (Fin 1)

@[ext]
structure SingleSorted2Functor (Obj₁ Obj₂ : Type*) [SingleSorted2Category Obj₁] [SingleSorted2Category Obj₂]
    extends SingleSortedFunctorFamily Obj₁ Obj₂ (Fin 2)

@[ext]
structure SingleSortedNFunctor (Obj₁ Obj₂ : Type*) (index : Nat) [SingleSortedNCategory Obj₁ index] [SingleSortedNCategory Obj₂ index]
    extends SingleSortedFunctorFamily Obj₁ Obj₂ (Fin index)

@[ext]
structure SingleSortedOmegaFunctor (Obj₁ Obj₂ : Type*) [SingleSortedOmegaCategory Obj₁] [SingleSortedOmegaCategory Obj₂]
    extends SingleSortedFunctorFamily Obj₁ Obj₂ Nat

def SingleSortedCat := SingleSortedFamilyCat (Fin 1)

def SingleSorted2cat := SingleSortedFamilyCat (Fin 2)

def SingleSortedNCat (index : Nat) := SingleSortedFamilyCat (Fin index)

def SingleSortedOmegaCat := SingleSortedFamilyCat Nat

end SingleSortedCategories
