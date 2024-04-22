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

@[inline, reducible]
abbrev DecidableTop (α : Type u) [Top α] := DecidablePred (λ a : α => a = ⊤)

instance {α} : DecidableTop (WithTop α) := λa => match a with | ⊤ => isTrue rfl | some _ => isFalse (λh => by cases h)

@[inline, reducible]
abbrev DecidableBot (α : Type u) [Bot α] := DecidablePred (λ a : α => a = ⊥)

instance {α} : DecidableBot (WithBot α) := λa => match a with | ⊥ => isTrue rfl | some _ => isFalse (λh => by cases h)

def Disc (α : Type u) : Type u := α

instance Disc.instPartialOrder {α} : PartialOrder (Disc α) where
  le a b := a = b
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ _ := Eq.symm

class DiscreteOrder (α : Type u) [LE α] : Prop where
  le_eq (a b : α) : a ≤ b → a = b

theorem DiscreteOrder.bddAbove_subsingleton {α} [Preorder α] [DiscreteOrder α]
  (s : Set α) : BddAbove s → s.Subsingleton := by
    intro ⟨a, ha⟩
    intro x hx y hy
    simp only [upperBounds, Set.mem_setOf_eq] at ha
    cases le_eq _ _ (ha hx); cases le_eq _ _ (ha hy); rfl

instance Disc.instDiscreteOrder {α} : DiscreteOrder (Disc α) where
  le_eq _ _ h := h

instance OrderDual.instDiscreteOrder {α} [LE α] [DiscreteOrder α]
  : DiscreteOrder (OrderDual α) where
  le_eq a b h := (DiscreteOrder.le_eq (OrderDual.ofDual b) (OrderDual.ofDual a) h).symm

class DiscreteBotOrder (α : Type u) [LE α] [Bot α] : Prop where
  le_bot_or_eq (a b : α) : a ≤ b → a = ⊥ ∨ a = b

instance {α} [LE α] [Bot α] [DiscreteOrder α] : DiscreteBotOrder α where
  le_bot_or_eq a b h := Or.inr (DiscreteOrder.le_eq a b h)

-- theorem DiscreteOrder.bddAbove_cmp {α} [Preorder α] [Bot α] [DiscreteBotOrder α] (s : Set α)
--   : BddAbove s → ∀a ∈ s, ∀b ∈ s, a = ⊥ ∨ b = ⊥ ∨ a = b := sorry

-- theorem DiscreteOrder.bddAbove_of_cmp {α} [Preorder α] [Bot α] [DiscreteBotOrder α] (s : Set α)
--   : (∀a ∈ s, ∀b ∈ s, a = ⊥ ∨ b = ⊥ ∨ a = b) → BddAbove s := sorry

-- theorem DiscreteOrder.bddAbove_iff {α} [Preorder α] [Bot α] [DiscreteBotOrder α] (s : Set α)
--   : BddAbove s ↔ ∀a ∈ s, ∀b ∈ s, a = ⊥ ∨ b = ⊥ ∨ a = b := ⟨bddAbove_cmp s, bddAbove_of_cmp s⟩

-- TODO: BddAbove of subsingleton, and so on
-- TODO: BddAbove is decidable for finite sets if we have decidable equality
-- Note that bottom does _not_ have to be a real bottom here, this is useful for linearity

theorem DiscreteOrder.bot_coe_le_coe {α} {a b : α} [LE α] [DiscreteOrder α]
  : (a : WithBot α) ≤ (b : WithBot α) → a = b
  := by simp only [WithBot.coe_le_coe]; exact le_eq a b

instance WithBot.instDiscreteBotOrder {α} [LE α] [DiscreteOrder α]
  : DiscreteBotOrder (WithBot α) where
  le_bot_or_eq
    | ⊥, b, _ => Or.inl rfl
    | some a, ⊥, h => by simp at h
    | some a, some b, h => Or.inr (by cases DiscreteOrder.bot_coe_le_coe h; rfl)

class DiscreteTopOrder (α : Type u) [LE α] [Top α] : Prop where
  le_top_or_eq (a b : α) : a ≤ b → b = ⊤ ∨ a = b

-- TODO: BddBelow results for discrete top orders
-- Note that top does _not_ have to be a real top here, this is useful for linearity

instance {α} [LE α] [Top α] [DiscreteOrder α] : DiscreteTopOrder α where
  le_top_or_eq a b h := Or.inr (DiscreteOrder.le_eq a b h)

theorem DiscreteOrder.top_coe_le_coe {α} {a b : α} [LE α] [DiscreteOrder α]
  : (a : WithTop α) ≤ (b : WithTop α) → a = b
  := by simp only [WithTop.coe_le_coe]; exact le_eq a b

instance WithTop.instDiscreteTopOrder {α} [LE α] [DiscreteOrder α]
  : DiscreteTopOrder (WithTop α) where
  le_top_or_eq
    | a, ⊤, _ => Or.inl rfl
    | ⊤, some b, h => by simp at h
    | some a, some b, h => Or.inr (by cases DiscreteOrder.top_coe_le_coe h; rfl)

-- instance {α} [LE α] [Bot α] [DiscreteBotOrder α] : DiscreteTopOrder (OrderDual α) where
--   le_bot_or_eq a b h := Or.inr (DiscreteOrder.le_eq a b h)

class DiscreteBoundedOrder (α : Type u) [LE α] [Bot α] [Top α] : Prop where
  le_bot_or_top_or_eq (a b : α) : a ≤ b → a = ⊥ ∨ b = ⊤ ∨ a = b

instance {α} [LE α] [Bot α] [Top α] [DiscreteTopOrder α] : DiscreteBoundedOrder α where
  le_bot_or_top_or_eq a b h := Or.inr (DiscreteTopOrder.le_top_or_eq a b h)

instance {α} [LE α] [Bot α] [Top α] [DiscreteBotOrder α] : DiscreteBoundedOrder α where
  le_bot_or_top_or_eq a b h := (DiscreteBotOrder.le_bot_or_eq a b h).elim Or.inl (Or.inr ∘ Or.inr)

theorem DiscreteBotOrder.top_coe_le_coe {α} [LE α] [Bot α] [DiscreteBotOrder α] {a b : α}
  : (a : WithTop α) ≤ (b : WithTop α) ↔ a ≤ b
  := by simp

theorem DiscreteTopOrder.bot_coe_le_coe {α} [LE α] [Top α] [DiscreteTopOrder α] {a b : α}
  : (a : WithBot α) ≤ (b : WithBot α) ↔ a ≤ b
  := by simp

instance WithBot.instTop {α} [t : Top α] : Top (WithBot α) where
  top := t.top

instance WithBot.instOrderTop {α} [LE α] [OrderTop α] : OrderTop (WithBot α) where
  le_top | ⊥ => by simp | some a => by simp [instTop, coe_le_coe]

instance WithTop.instBot {α} [b : Bot α] : Bot (WithTop α) where
  bot := b.bot

instance WithTop.instOrderBot {α} [LE α] [OrderBot α] : OrderBot (WithTop α) where
  bot_le | ⊤ => by simp | some a => by simp [instBot, coe_le_coe]

theorem DiscreteBotOrder.withTop_le {α} [LE α] [αb : Bot α] [DiscreteBotOrder α]
  : {a b : WithTop α} → a ≤ b → a = ⊥ ∨ b = ⊤ ∨ a = b
  | ⊤, _ => by aesop
  | _, ⊤ => by simp
  | some a, some b => by
    simp only [WithTop.some_le_some, WithTop.instBot, false_or]
    intro h
    cases DiscreteBotOrder.le_bot_or_eq a b h <;> simp [WithTop.some, *]

theorem DiscreteTopOrder.withBot_le {α} [LE α] [αt : Top α] [DiscreteTopOrder α]
  : {a b : WithBot α} → a ≤ b → a = ⊥ ∨ b = ⊤ ∨ a = b
  | ⊥, _ => by simp
  | _, ⊥ => by aesop
  | some a, some b => by
    simp only [WithBot.some_le_some, WithBot.instTop, false_or]
    intro h
    cases DiscreteTopOrder.le_top_or_eq a b h <;> simp [WithBot.some, *]

instance WithBot.instDiscreteBoundedOrder {α} [LE α] [Top α] [DiscreteTopOrder α]
  : DiscreteBoundedOrder (WithBot α) where
  le_bot_or_top_or_eq _ _ := DiscreteTopOrder.withBot_le

instance WithTop.instDiscreteBoundedOrder {α} [LE α] [Bot α] [DiscreteBotOrder α]
  : DiscreteBoundedOrder (WithTop α) where
  le_bot_or_top_or_eq _ _ := DiscreteBotOrder.withTop_le

-- TODO: needed?
-- instance Disc.instDecidableEq {α} [H : DecidableEq α] : DecidableEq (Disc α) := H

-- TODO: needed?
instance Disc.instDecidableLE {α} [H : DecidableEq α] : DecidableRel (@LE.le (Disc α) _) := H

instance DiscreteOrder.isPartialOrder {α} [o : Preorder α] [DiscreteOrder α] : PartialOrder α where
  toPreorder := o
  le_antisymm _ _ h _ := le_eq _ _ h

instance Disc.instSemilatticeBot {α} [DecidableEq α] : SemilatticeInf (WithBot (Disc α)) where
  inf
    | ⊥, _ => ⊥
    | _, ⊥ => ⊥
    | some a, some b => if a = b then some a else ⊥
  inf_le_left := by aesop
  inf_le_right := by aesop
  le_inf
    | ⊥, _, _ => by simp
    | _, ⊥, _ => λh => by simp only [le_bot_iff] at h; cases h; simp
    | _, _, ⊥ => λ_ h => by simp only [le_bot_iff] at h; cases h; simp
    | some a, some b, some c => λh h' => by
      cases WithBot.coe_le_coe.mp h
      cases WithBot.coe_le_coe.mp h'
      simp

instance Disc.instSemilatticeSup {α} [DecidableEq α] : SemilatticeSup (WithTop (Disc α)) where
  sup
    | ⊤, _ => ⊤
    | _, ⊤ => ⊤
    | some a, some b => if a = b then some a else ⊤
  le_sup_left := by aesop
  le_sup_right := by aesop
  sup_le
    | _, _, ⊤ => by simp
    | ⊤, _, _ => λh _ => by simp only [top_le_iff] at h; cases h; simp
    | _, ⊤, _ => λ_ h => by simp only [top_le_iff] at h; cases h; simp
    | some a, some b, some c => λh h' => by
      cases WithTop.coe_le_coe.mp h
      cases WithTop.coe_le_coe.mp h'
      simp

instance WithTop.WithBot.Disc.instLattice {α} [DecidableEq α] : Lattice (WithTop (WithBot (Disc α))) where
  sup
    | ⊤, _ => ⊤
    | _, ⊤ => ⊤
    | ⊥, a => a
    | a, ⊥ => a
    | some (some a), some (some b) => if a = b then some (some a) else ⊤
  le_sup_left
    | ⊤, a => by aesop
    | some a, ⊤ => by aesop
    | ⊥, some a => by simp
    | some (some a), ⊥ => le_refl _
    | some (some a), some (some b) => by aesop
  le_sup_right
    | ⊤, a => by aesop
    | some a, ⊤ => by aesop
    | ⊥, some (some a) => le_refl _
    | some a, ⊥ => by simp
    | some (some a), some (some b) => by aesop
  sup_le
    | _, _, ⊤ => by simp
    | _, ⊤, _ => by aesop
    | ⊤, _, _ => by aesop
    | ⊥, some (some a), some (some b) => λ_ => id
    | some (some a), ⊥, some b => λh _ => h
    | ⊥, ⊥, some b => λh _ => h
    | a, b, ⊥ => by simp only [le_bot_iff]; intro h h'; cases h; cases h'; rfl
    | some (some a), some (some b), some (some c) => by
      simp only [coe_le_coe]
      intro h h'
      cases WithBot.coe_le_coe.mp h
      cases WithBot.coe_le_coe.mp h'
      simp
  inf_le_left := by aesop
  inf_le_right := by aesop
  le_inf := by aesop

instance WithBot.WithTop.Disc.instLattice {α} [DecidableEq α] : Lattice (WithBot (WithTop (Disc α))) where
  inf
    | ⊥, _ => ⊥
    | _, ⊥ => ⊥
    | ⊤, a => a
    | a, ⊤ => a
    | some (some a), some (some b) => if a = b then some (some a) else ⊥
  le_sup_left := by aesop
  le_sup_right := by aesop
  sup_le := by aesop
  inf_le_left
    | ⊥, a => by aesop
    | some a, ⊥ => by aesop
    | ⊤, ⊤ => le_refl _
    | ⊤, some (some a) => by simp
    | some (some a), ⊤ => le_refl _
    | some (some a), some (some b) => by aesop
  inf_le_right
    | ⊥, a => by aesop
    | some a, ⊥ => by aesop
    | ⊤, ⊤ => le_refl _
    | ⊤, some (some a) => le_refl _
    | some (some a), ⊤ => by aesop
    | some (some a), some (some b) => by aesop
  le_inf
    | ⊥, _, _ => by simp
    | _, ⊥, _ => λh => by simp only [le_bot_iff] at h; cases h; simp
    | _, _, ⊥ => λ_ h => by simp only [le_bot_iff] at h; cases h; simp
    | some (some a), some (some b), ⊤ => λh _ => h
    | some a, ⊤, some (some b) => λ_ h => h
    | some a, ⊤, ⊤ => λ_ _ => le_top
    | ⊤, a, b => by simp only [top_le_iff]; intro h h'; cases h; cases h'; rfl
    | some (some a), some (some b), some (some c) => by
      simp only [coe_le_coe]
      intro h h'
      cases WithTop.coe_le_coe.mp h
      cases WithTop.coe_le_coe.mp h'
      simp

-- Note: these lattices are _not_ distributive!

-- open Classical in
-- noncomputable instance WithTop.WithBot.Disc.instCompleteLattice {α} [DecidableEq α] : CompleteLattice (WithTop (WithBot (Disc α))) where
--   sSup A := if h : A.Nonempty then
--       let a := choose h;
--       if ∃b ∈ A, b ≠ ⊥ ∧ b ≠ a then ⊤ else a
--     else
--       ⊥
--   le_sSup A a h := by
--     simp only
--     split
--     . rename_i h'
--       split
--       . exact le_top
--       . rename_i c
--         rw [Disc.top_bot_le_iff, or_iff_not_and_not]
--         rw [not_or]
--         intro ⟨ha, _, ha'⟩
--         exact c ⟨a, h, ha, ha'⟩
--     . rename_i h'
--       exact (h' ⟨_, h⟩).elim
--   sSup_le A a h := by
--     simp only
--     split
--     . split
--       . rename_i hn h'
--         generalize ce : choose hn = c
--         have hc := h _ (le_sSup sorry)
--         let ⟨b, hb, hbb, hba⟩ := h'
--         have hb' := h _ hb
--         rw [Disc.top_bot_le_iff] at hb'
--         cases hb' with
--         | inl h => exact (hbb h).elim
--         | inr h => cases h with
--         | inl h => cases h; exact le_refl _
--         | inr hb' =>
--           cases hb'
--           have hc := h _ (choose hn)
--           simp only [top_le_iff]
--       . sorry
--     . exact bot_le
--   sInf A := if h : A.Nonempty then
--       let a := choose h;
--       if ∃b ∈ A, a ≠ b then ⊥ else a
--     else
--       ⊤
--   sInf_le := sorry
--   le_sInf := sorry
--   le_top := by simp
--   bot_le := by simp

-- open Classical in
-- noncomputable instance WithBot.WithTop.Disc.instCompleteLattice {α} [DecidableEq α] : CompleteLattice (WithBot (WithTop (Disc α))) where
--   sSup A := if h : A.Nonempty then
--       let a := choose h;
--       if ∃b ∈ A, a ≠ b then ⊤ else a
--     else
--       ⊥
--   le_sSup := sorry
--   sSup_le := sorry
--   sInf A := if h : A.Nonempty then
--       let a := choose h;
--       if ∃b ∈ A, a ≠ b then ⊥ else a
--     else
--       ⊤
--   sInf_le := sorry
--   le_sInf := sorry
--   le_top := by simp
--   bot_le := by simp
