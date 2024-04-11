import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Lattice

import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Init.Classical
import Mathlib.Order.SuccPred.Basic

import Mathlib.Order.WithBot

theorem List.argmax_map [Preorder β] [DecidableRel λ l r : β => l < r] (Γ : List α) (f : α → β)
  : (Γ.argmax f).map f = (Γ.map f).maximum := by
  simp only [map_cons, maximum, argmax, foldl]
  generalize hbase: @none α = base
  have hbase': @none β = base.map f := by simp [<-hbase]
  rw [hbase']
  clear hbase hbase'
  induction Γ generalizing base with
  | nil => rfl
  | cons a Γ I =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, I]
    congr
    cases base with
    | some base =>
      simp only [argAux, id_eq, Option.map_some']
      split <;> rfl
    | none => rfl

theorem List.Disjoint.to_reverse_left {Γ Δ : List α} (h: Disjoint Γ Δ)
  : Disjoint Γ.reverse Δ := λ_ m => h (List.mem_reverse.mp m)

theorem List.Disjoint.to_reverse_right {Γ Δ : List α} (h: Disjoint Γ Δ)
  : Disjoint Γ Δ.reverse := h.symm.to_reverse_left.symm

theorem List.Disjoint.of_reverse_left {Γ Δ : List α} (h: Disjoint Γ.reverse Δ)
  : Disjoint Γ Δ := λ_ m => h (List.mem_reverse.mpr m)

theorem List.Disjoint.of_reverse_right {Γ Δ : List α} (h: Disjoint Γ Δ.reverse)
  : Disjoint Γ Δ := h.symm.of_reverse_left.symm

theorem List.Disjoint.iff_reverse_left {Γ Δ : List α}
  : Disjoint Γ.reverse Δ ↔ Disjoint Γ Δ
  := ⟨List.Disjoint.of_reverse_left, List.Disjoint.to_reverse_left⟩

theorem List.Disjoint.iff_reverse_right {Γ Δ : List α}
  : Disjoint Γ Δ.reverse ↔ Disjoint Γ Δ
  := ⟨List.Disjoint.of_reverse_right, List.Disjoint.to_reverse_right⟩

inductive Option.Subset : Option α → Option α → Prop
  | none (a) : Subset none a
  | some (a : α) : Subset (some a) (some a)

instance Option.instHasSubsetOption : HasSubset (Option α) := ⟨Option.Subset⟩

instance WithBot.instHasSubsetWithBot : HasSubset (WithBot α) := ⟨Option.Subset⟩

inductive WithBot.Cmp : (a b : WithBot α) → Prop
  | bot : Cmp ⊥ ⊥
  | left (a : α) : Cmp (some a) ⊥
  | right (a : α) : Cmp ⊥ (some a)
  | both (a : α) : Cmp (some a) (some a)

theorem WithBot.Cmp.symm {a b : WithBot α} (h : WithBot.Cmp a b) : WithBot.Cmp b a := by
  cases h
  case bot => exact WithBot.Cmp.bot
  case left a => exact WithBot.Cmp.right a
  case right a => exact WithBot.Cmp.left a
  case both a => exact WithBot.Cmp.both a
