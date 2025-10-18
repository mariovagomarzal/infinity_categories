/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import InfinityCategories.SingleSortedCategories.Basic

/-!
TODO: Document the file.
-/

set_option linter.style.longLine false

namespace SingleSortedCategories

instance InstTotal (A : Type*) : SingleSortedCategory (A×A) where
  sc := fun _ (y₁, y₂) ↦ (y₂, y₂)
  tg := fun _ (x₁, x₂) ↦ (x₁, x₁)
  pcomp := fun _ (y₁, y₂) (x₁, x₂) ↦ ⟨y₂ = x₁, fun _ ↦ (y₁, x₂)⟩
  pcomp_dom := by
    intro _ (x₁, x₂) (y₁, y₂)
    apply Iff.intro
    · intros
      simpa
    · intro h
      simp at h
      simpa
  scsc := by intros; rfl
  tgsc := by intros; rfl
  sctg := by intros; rfl
  tgtg := by intros; rfl
  sc_comp_is_sc := by intros; rfl
  tg_comp_is_tg := by intros; rfl
  comp_sc_is_id := by intros; rfl
  comp_tg_is_id := by intros; rfl
  assoc := by intros; rfl

class Preorder (A : Type*) where
  R : A → A → Prop
  refl : ∀ {a : A}, R a a
  trans : ∀ {a b c : A}, R a b → R b c → R a c

instance InstPreorder {A : Type*} [Preorder A] : SingleSortedCategory ({ ⟨x, y⟩ : A × A | Preorder.R x y }) where
  sc := fun _ ⟨⟨a1, a2⟩, h⟩ ↦ ⟨⟨a1, a1⟩, Preorder.refl⟩
  tg := fun _ ⟨⟨a1, a2⟩, h⟩ ↦ ⟨⟨a2, a2⟩, Preorder.refl⟩
  pcomp := fun _ ⟨⟨b1, b2⟩, hb⟩ ⟨⟨a1, a2⟩, ha⟩ ↦ ⟨a2 = b1, fun h ↦ ⟨⟨a1, b2⟩, by apply Preorder.trans ha; rw [h]; exact hb⟩⟩
  pcomp_dom := by
    intro _ ⟨⟨b1, b2⟩, hb⟩ ⟨⟨a1, a2⟩, ha⟩
    apply Iff.intro
    --
    · intro h
      simp
      exact h.symm
    --
    · intro h
      simp at h
      simp
      exact h.symm
  scsc := by intros; rfl
  tgsc := by intros; rfl
  sctg := by intros; rfl
  tgtg := by intros; rfl
  sc_comp_is_sc := by intros; rfl
  tg_comp_is_tg := by intros; rfl
  comp_sc_is_id := by intros; rfl
  comp_tg_is_id := by intros; rfl
  assoc := by intros; rfl

class Monoid (A : Type*) where
  comp : A → A → A
  e : A
  comp_e : ∀ {a : A}, comp a e = a
  e_comp : ∀ {a : A}, comp e a = a
  assoc : ∀ {a b c : A}, comp a (comp b c) = comp (comp a b) c

instance InstMonoid {A : Type*} [Monoid A] : SingleSortedCategory A where
  sc := fun _ a ↦ Monoid.e
  tg := fun _ a ↦ Monoid.e
  pcomp := fun _ a b ↦ ⟨True, fun _ ↦ Monoid.comp a b⟩
  pcomp_dom := by
    intro _ a b
    apply Iff.intro
    --
    · intro h
      exact rfl
    --
    · intro h
      trivial
  scsc := by intros; rfl
  tgsc := by intros; rfl
  sctg := by intros; rfl
  tgtg := by intros; rfl
  sc_comp_is_sc := by intros; rfl
  tg_comp_is_tg := by intros; rfl
  comp_sc_is_id := Monoid.comp_e
  comp_tg_is_id := Monoid.e_comp
  assoc := by
    intro _ a b c
    simp
    exact Monoid.assoc

end SingleSortedCategories
