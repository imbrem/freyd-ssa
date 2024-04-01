import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Init.Classical
import Mathlib.Order.SuccPred.Basic

import FreydSSA.Utils
import FreydSSA.Ctx.Var

structure Label (ν κ : Type u) (α : Type v) where
  name : κ
  param : α
  live : Ctx ν α

structure Label.Wk (ℓ ℓ' : Label ν κ α) where
  name : ℓ.name = ℓ'.name
  param : ℓ.param = ℓ'.param
  live : ℓ.live.Wk ℓ'.live

theorem Label.Wk.antisymm {ℓ ℓ' : Label ν κ α} (h : ℓ.Wk ℓ') (h' : ℓ'.Wk ℓ) : ℓ = ℓ'
  := by
    cases ℓ; cases ℓ';
    simp only [Label.mk.injEq]
    exact ⟨h.name, h.param, h.live.antisymm h'.live⟩

theorem Label.Wk.allEq {ℓ ℓ' : Label ν κ α} (D D': ℓ.Wk ℓ') : D = D'
  := by cases D; cases D'; simp only [mk.injEq]; apply Ctx.Wk.allEq

def Label.Wk.refl (ℓ : Label ν κ α) : ℓ.Wk ℓ := ⟨rfl, rfl, Ctx.Wk.refl _⟩

def Label.Wk.comp {ℓ ℓ' ℓ'' : Label ν κ α} (w : ℓ.Wk ℓ') (w' : ℓ'.Wk ℓ'') : ℓ.Wk ℓ''
  := ⟨w.name.trans w'.name, w.param.trans w'.param, w.live.comp w'.live⟩

def Label.Wk.Iso {ℓ₁ ℓ₂ : Label ν κ α} {ℓ₁' ℓ₂' : Label ν' κ' α} (w : ℓ₁.Wk ℓ₂) (w' : ℓ₁'.Wk ℓ₂')
  := w.live.Iso w'.live

def Label.Wk.Iso.comp {ℓ₁ ℓ₂ ℓ₃ : Label ν κ α} {ℓ₁' ℓ₂' ℓ₃' : Label ν' κ' α}
  {l : ℓ₁.Wk ℓ₂}
  {r : ℓ₂.Wk ℓ₃}
  {l' : ℓ₁'.Wk ℓ₂'}
  {r' : ℓ₂'.Wk ℓ₃'}
  (hl : l.Iso l') (hr : r.Iso r')
  : (l.comp r).Iso (l'.comp r')
  := Ctx.Wk.Iso.comp hl hr

def Label.FreshVar (ℓ : Label ν κ α) (n : ν) := ℓ.live.Fresh n

theorem Label.FreshVar.wk {ℓ ℓ' : Label ν κ α} {l : ν}
  (h : ℓ.FreshVar l) (w : ℓ.Wk ℓ') : ℓ'.FreshVar l
  := Ctx.Fresh.wk h w.live

def Label.Fresh (ℓ : Label ν κ α) (l : κ) := ℓ.name ≠ l

theorem Label.Fresh.wk_exit {ℓ ℓ' : Label ν κ α} {l : κ}
  (h : ℓ.Fresh l) (w : ℓ.Wk ℓ') : ℓ'.Fresh l
  := by simp only [<-w.name, Fresh]; exact h

theorem Label.Fresh.rwk_exit {ℓ ℓ' : Label ν κ α} {l : κ}
  (h : ℓ.Fresh l) (w : ℓ'.Wk ℓ) : ℓ'.Fresh l
  := by simp only [w.name, Fresh]; exact h

theorem Label.Fresh.wk_entry {ℓ ℓ' : Label ν κ α} {l : κ}
  (w : ℓ.Wk ℓ') (h : ℓ'.Fresh l) : ℓ.Fresh l
  := by simp only [w.name, Fresh]; exact h

def LCtx (ν κ α) := List (Label ν κ α)

def LCtx.labels {ν κ α} (L : LCtx ν κ α): List κ
  := L.map Label.name

inductive LCtx.FreshVar {ν κ α} (n : ν) : LCtx ν κ α → Prop
  | nil : LCtx.FreshVar n []
  | cons : ℓ.FreshVar n → FreshVar n L → FreshVar n (ℓ::L)

theorem LCtx.FreshVar.head {ν α} {n} {ℓ : Label ν κ α} {L : LCtx ν κ α}
  : FreshVar n (ℓ::L) → ℓ.FreshVar n
  | cons hxn _ => hxn

theorem LCtx.FreshVar.tail {ν α} {n} {ℓ : Label ν κ α} {L : LCtx ν κ α}
  : FreshVar n (ℓ::L) → L.FreshVar n
  | cons _ h => h

inductive LCtx.Fresh {ν κ α} (l : κ) : LCtx ν κ α → Prop
  | nil : LCtx.Fresh l []
  | cons : ℓ.Fresh l → Fresh l L → Fresh l (ℓ::L)

theorem LCtx.Fresh.head {ν κ α} {l : κ} {ℓ : Label ν κ α} {L : LCtx ν κ α}
  : Fresh l (ℓ::L) → ℓ.Fresh l
  | cons hxn _ => hxn

theorem LCtx.Fresh.tail {ν κ α} {l : κ} {ℓ : Label ν κ α} {L : LCtx ν κ α}
  : Fresh l (ℓ::L) → L.Fresh l
  | cons _ h => h

theorem LCtx.Fresh.not_mem {ν κ α} {l : κ} {L : LCtx ν κ α}
  (h : L.Fresh l) : l ∉ L.labels := by induction h with
  | nil => exact List.not_mem_nil _
  | cons hℓ _ I =>
    apply List.not_mem_cons_of_ne_of_not_mem
    exact hℓ.symm
    apply I

theorem LCtx.Fresh.of_not_mem {ν κ α} {l : κ} {L : LCtx ν κ α}
  (h : l ∉ L.labels) : L.Fresh l
  := by induction L with
  | nil => exact Fresh.nil
  | cons ℓ L I =>
    apply Fresh.cons
    apply Ne.symm
    apply List.ne_of_not_mem_cons
    exact h
    apply I
    apply List.not_mem_of_not_mem_cons
    exact h

theorem LCtx.Fresh.not_mem_iff {ν κ α} {l : κ} {L : LCtx ν κ α}
  : L.Fresh l ↔ l ∉ L.labels
  := ⟨LCtx.Fresh.not_mem, LCtx.Fresh.of_not_mem⟩

inductive LCtx.Wk {ν κ α} : LCtx ν κ α → LCtx ν κ α → Type _
  | nil : Wk [] []
  | cons {ℓ ℓ' : Label ν κ α} : ℓ.Wk ℓ' → Wk L K → Wk (ℓ::L) (ℓ'::K)
  | skip {ℓ : Label ν κ α} : L.Fresh ℓ.name → Wk L K → Wk L (ℓ::K)

def LCtx.Wk.refl {ν κ α} : (L : LCtx ν κ α) → L.Wk L
  | [] => nil
  | ℓ::L => cons (Label.Wk.refl ℓ) (refl L)

def LCtx.Wk.zero {ν κ α} : (L : LCtx ν κ α) → Wk [] L
  | [] => nil
  | _::L => skip Fresh.nil (zero L)

theorem LCtx.Fresh.wk {ν κ α} {L K: LCtx ν κ α} {l: κ}
  (w : L.Wk K) (h : K.Fresh l) : L.Fresh l
  := by induction w with
  | nil => exact h
  | cons h _ I =>
    cases h;
    constructor
    apply Label.Fresh.wk_entry
    assumption
    assumption
    apply I
    assumption
  | skip _ _ I =>
    apply I
    cases h
    assumption

theorem LCtx.Wk.antisymm {ν κ α} {L K : LCtx ν κ α} (h : L.Wk K) (h' : K.Wk L)
  : L = K
  := by induction h with
  | nil => cases h'; rfl
  | cons hℓ _ I =>
    cases h' with
    | cons hℓ' h' =>
      congr
      apply Label.Wk.antisymm <;> assumption
      exact I h'
    | skip h' => exact (h'.head hℓ.name.symm).elim
  | skip h => exact ((h.wk h').head rfl).elim

theorem LCtx.Wk.allEq {ν κ α} {L K : LCtx ν κ α} (D D': L.Wk K): D = D'
  := by induction D with
  | nil => cases D'; rfl
  | cons hℓ _ I => cases D' with
    | cons =>
      congr
      apply Label.Wk.allEq
      exact I _
    | skip h => exact (h.head hℓ.name).elim
  | skip h _ I => cases D' with
    | cons hℓ _ => exact (h.head hℓ.name).elim
    | skip h' => congr; exact I _

theorem LCtx.Wk.not_mem {ν κ α} {ℓ : Label ν κ α} {L K : LCtx ν κ α}
  (w : L.Wk K) (h : ℓ.name ∉ K.labels) : ℓ.name ∉ L.labels := by induction w with
  | nil => exact h
  | cons hℓ _ I =>
    apply List.not_mem_cons_of_ne_of_not_mem
    apply List.ne_of_not_mem_cons
    rw [hℓ.name]
    exact h
    apply I
    apply List.not_mem_of_not_mem_cons
    exact h
  | skip _ _ I =>
    apply I
    apply List.not_mem_of_not_mem_cons
    exact h

def LCtx.Wk.comp {L K M : LCtx ν κ α} : L.Wk K → K.Wk M → L.Wk M
  | Wk.nil, w => w
  | Wk.cons h w, Wk.cons h' w' => Wk.cons (h.comp h') (w.comp w')
  | Wk.skip hℓ w, Wk.cons hℓw w' => Wk.skip (hℓw.name ▸ hℓ) (w.comp w')
  | w, Wk.skip hℓ w' => Wk.skip (hℓ.wk w) (w.comp w')

def Ctx.Wk.to_lctx {ν α κ} {Γ Δ : Ctx ν α} (ℓ: κ) (A: α) (w: Γ.Wk Δ)
  : LCtx.Wk [⟨ℓ, A, Γ⟩] [⟨ℓ, A, Δ⟩]
  := LCtx.Wk.cons ⟨rfl, rfl, w⟩ LCtx.Wk.nil

inductive LCtx.Wk.Iso : {L K : LCtx ν κ α} → {L' K' : LCtx ν' κ' α'} → Wk L K → Wk L' K' → Prop
  | nil : Iso nil nil
  | cons : h.Iso h' → Iso w w' → Iso (cons h w) (cons h' w')
  | skip : Iso w w' → Iso (skip hℓ w) (skip hℓ' w')

theorem LCtx.Wk.Iso.refl {L K : LCtx ν κ α} : (w: L.Wk K) → w.Iso w
  | Wk.nil => nil
  | Wk.cons h w => cons h.live.iso_refl (refl w)
  | Wk.skip h w => skip (refl w)

theorem LCtx.Wk.Iso.symm {L K : LCtx ν κ α} {L' K' : LCtx ν' κ' α'}
  {w: L.Wk K} {w': L'.Wk K'} : (h: w.Iso w') → w'.Iso w
  | nil => nil
  | cons h w => cons h.symm w.symm
  | skip w => skip w.symm

theorem LCtx.Wk.Iso.trans {L K : LCtx ν κ α} {L' K' : LCtx ν' κ' α'} {L'' K'' : LCtx ν'' κ'' α''}
  {w: L.Wk K} {w': L'.Wk K'} {w'': L''.Wk K''} : (h: w.Iso w') → (h': w'.Iso w'') → w.Iso w''
  | nil, nil => nil
  | cons h w, cons h' w' => cons (h.trans h') (w.trans w')
  | skip w, skip w' => skip (w.trans w')

theorem LCtx.Wk.Iso.comp {L K M : LCtx ν κ α} {L' K' M' : LCtx ν' κ' α'}
  {l: L.Wk K} {r: K.Wk M} {l': L'.Wk K'} {r': K'.Wk M'}
  (hl: l.Iso l') (hr: r.Iso r'): (l.comp r).Iso (l'.comp r') := by
    induction hr generalizing L <;>
    cases hl <;>
    constructor
    --TODO: probably go clean up or smt
    apply Label.Wk.Iso.comp <;> assumption
    apply_assumption
    assumption
    case cons.skip I _ _ _ _ h =>
      apply_assumption
      assumption
    case skip.cons I =>
      apply_assumption
      constructor <;> assumption
    case skip.skip I =>
      apply_assumption
      constructor
      assumption
    assumption

def Label.Wk.join {ℓ ℓ₁ ℓ₂ : Label ν κ α} (w : ℓ.Wk ℓ₁) (w' : ℓ.Wk ℓ₂) : Label ν κ α where
  name := ℓ.name
  param := ℓ.param
  live := w.live.join w'.live

def Label.Wk.src {ℓ ℓ' : Label ν κ α} (_ : ℓ.Wk ℓ') : Label ν κ α := ℓ
def Label.Wk.trg {ℓ ℓ' : Label ν κ α} (_ : ℓ.Wk ℓ') : Label ν κ α := ℓ'

def LCtx.Wk.shared_entry {L K M : LCtx ν κ α} : L.Wk M → K.Wk M → LCtx ν κ α
  | Wk.nil, _ => []
  | Wk.cons h w, Wk.cons _ w' => h.trg::(shared_entry w w')
  | Wk.skip _ w, Wk.cons h w' => h.trg::(shared_entry w w')
  | Wk.cons h w, Wk.skip _ w' => h.trg::(shared_entry w w')
  | Wk.skip _ w, Wk.skip _ w' => shared_entry w w'

def LCtx.Wk.shared_entry_left {L K M : LCtx ν κ α}
  : (w : L.Wk M) → (w' : K.Wk M) → L.Wk (w.shared_entry w')
  | nil, nil => nil
  | cons h w, cons h' w' => cons h (shared_entry_left w w')
  | skip h w, cons h' w' => skip h (shared_entry_left w w')
  | cons h w, skip _ w' => cons h (shared_entry_left w w')
  | skip _ w, skip _ w' => shared_entry_left w w'

def LCtx.Wk.shared_entry_right {L K M : LCtx ν κ α}
  : (w : L.Wk M) → (w' : K.Wk M) → K.Wk (w.shared_entry w')
  | nil, nil => nil
  | cons _ w, cons h' w' => cons h' (shared_entry_right w w')
  | skip _ w, cons h' w' => cons h' (shared_entry_right w w')
  | cons _ w, skip h' w' => skip h' (shared_entry_right w w')
  | skip _ w, skip _ w' => shared_entry_right w w'

theorem LCtx.Wk.mem_labels_shared_entry_of_mem_labels_left {L K M : LCtx ν κ α}
  (w : L.Wk M) (w' : K.Wk M) (hℓm : ℓ ∈ L.labels)
  : ℓ ∈ (w.shared_entry w').labels
  := match w, w' with
  | nil, nil => by simp [labels] at hℓm
  | cons hℓ w, cons hℓ' w' => by cases hℓm with
    | head =>
      simp only [labels, shared_entry, List.map, Label.Wk.trg]
      rw [hℓ.name]
      exact List.Mem.head _
    | tail _ hℓm =>
      exact List.mem_cons_of_mem _ (mem_labels_shared_entry_of_mem_labels_left w w' hℓm)
  | skip _ w, cons _ w' =>
    List.mem_cons_of_mem _ (mem_labels_shared_entry_of_mem_labels_left w w' hℓm)
  | cons hℓ w, skip _ w' => by cases hℓm with
    | head =>
      simp only [labels, shared_entry, List.map, Label.Wk.trg]
      rw [hℓ.name]
      exact List.Mem.head _
    | tail _ hℓm =>
      exact List.mem_cons_of_mem _ (mem_labels_shared_entry_of_mem_labels_left w w' hℓm)
  | skip _ w, skip _ w' => mem_labels_shared_entry_of_mem_labels_left w w' hℓm

theorem LCtx.Wk.mem_labels_shared_entry_of_mem_labels_right {L K M : LCtx ν κ α}
  (w : L.Wk M) (w' : K.Wk M) (hℓm : ℓ ∈ K.labels)
  : ℓ ∈ (w.shared_entry w').labels
  := match w, w' with
  | nil, nil => by simp [labels] at hℓm
  | cons _ w, cons hℓ' w' => by cases hℓm with
    | head =>
      simp only [labels, shared_entry, List.map, Label.Wk.trg]
      rw [hℓ'.name]
      exact List.Mem.head _
    | tail _ hℓm =>
      exact List.mem_cons_of_mem _ (mem_labels_shared_entry_of_mem_labels_right w w' hℓm)
  | skip _ w, cons hℓ' w' => by cases hℓm with
    | head =>
      simp only [labels, shared_entry, List.map, Label.Wk.trg]
      rw [hℓ'.name]
      exact List.Mem.head _
    | tail _ hℓm =>
      exact List.mem_cons_of_mem _ (mem_labels_shared_entry_of_mem_labels_right w w' hℓm)
  | cons _ w, skip hℓ' w' =>
    List.mem_cons_of_mem _ (mem_labels_shared_entry_of_mem_labels_right w w' hℓm)
  | skip _ w, skip _ w' => mem_labels_shared_entry_of_mem_labels_right w w' hℓm

def LCtx.Wk.mem_shared_entry_labels_left_or_right {L K M : LCtx ν κ α}
  (w : L.Wk M) (w' : K.Wk M) (hℓm : ℓ ∈ (w.shared_entry w').labels)
  : ℓ ∈ L.labels ∨ ℓ ∈ K.labels
  := match w, w' with
  | nil, nil => by simp [labels, shared_entry] at hℓm
  | cons hℓ w, cons hℓ' w' => by
    cases hℓm with
    | head => left; rw [labels, List.map, hℓ.name]; exact List.Mem.head _
    | tail _ hℓm => cases mem_shared_entry_labels_left_or_right w w' hℓm with
      | inl hℓm => left; exact List.mem_cons_of_mem _ hℓm
      | inr hℓm => right; exact List.mem_cons_of_mem _ hℓm
  | skip _ w, cons hℓ' w' => by
    cases hℓm with
    | head => right; rw [labels, List.map, hℓ'.name]; exact List.Mem.head _
    | tail _ hℓm => cases mem_shared_entry_labels_left_or_right w w' hℓm with
      | inl hℓm => left; exact hℓm
      | inr hℓm => right; exact List.mem_cons_of_mem _ hℓm
  | cons hℓ w, skip hℓ' w' => by
    cases hℓm with
    | head => left; rw [labels, List.map, hℓ.name]; exact List.Mem.head _
    | tail _ hℓm => cases mem_shared_entry_labels_left_or_right w w' hℓm with
      | inl hℓm => left; exact List.mem_cons_of_mem _ hℓm
      | inr hℓm => right; exact hℓm
  | skip _ w, skip _ w' => mem_shared_entry_labels_left_or_right w w' hℓm

def LCtx.Wk.shared_entry_exit {L K M : LCtx ν κ α}
  : (w : L.Wk M) → (w' : K.Wk M) → (w.shared_entry w').Wk M
  | nil, nil => nil
  | cons h w, cons h' w' => cons (Label.Wk.refl _) (shared_entry_exit w w')
  | skip _ w, cons h' w' => cons (Label.Wk.refl _) (shared_entry_exit w w')
  | cons h w, skip h' w' => cons (Label.Wk.refl _) (shared_entry_exit w w')
  | skip h w, skip h' w' => skip (by
    apply Fresh.of_not_mem
    intro hℓ
    cases mem_shared_entry_labels_left_or_right w w' hℓ with
    | inl hℓ => exact h.not_mem hℓ
    | inr hℓ => exact h'.not_mem hℓ
  ) (shared_entry_exit w w')

--TODO: LCtx shared properties (e.g. comm...), isos

inductive LCtx.PWk {ν κ α} : LCtx ν κ α → LCtx ν κ α → Type _
  | nil : PWk [] []
  | cons {ℓ ℓ' : Label ν κ α} : ℓ.Wk ℓ' → PWk L K → PWk (ℓ::L) (ℓ'::K)

theorem LCtx.PWk.allEq {ν κ α} {L K : LCtx ν κ α} (D D': L.PWk K): D = D'
  := by induction D with
  | nil => cases D'; rfl
  | cons h _ I => cases D' with
    | cons =>
      congr
      apply Label.Wk.allEq
      exact I _

theorem LCtx.PWk.comp {L K M : LCtx ν κ α} : L.PWk K → K.PWk M → L.PWk M
  | nil, w => w
  | cons h w, PWk.cons h' w' => PWk.cons (h.comp h') (w.comp w')

theorem LCtx.PWk.refl : (L : LCtx ν κ α) → L.PWk L
  | [] => nil
  | ℓ::L => cons (Label.Wk.refl ℓ) (refl L)

def LCtx.PWk.toWk {ν κ α} {L K : LCtx ν κ α} : L.PWk K → L.Wk K
  | PWk.nil => Wk.nil
  | PWk.cons h w => Wk.cons h (toWk w)

theorem LCtx.PWk.labels {ν κ α} {L K : LCtx ν κ α} (w : L.PWk K) : L.labels = K.labels
  := by induction w with
  | nil => rfl
  | cons h w I =>
    simp only [LCtx.labels, List.map]
    rw [h.name]
    congr 1

theorem LCtx.Fresh.pwk {ν κ α} {L K : LCtx ν κ α} {l : κ}
  (w : L.PWk K) : K.Fresh l → L.Fresh l
  := by
    rw [not_mem_iff, not_mem_iff, w.labels]
    exact λx => x

theorem LCtx.Fresh.pwk_r {ν κ α} {L K : LCtx ν κ α} {l : κ}
  (w : L.PWk K) : L.Fresh l → K.Fresh l
  := by
    rw [not_mem_iff, not_mem_iff, w.labels]
    exact λx => x

inductive Ctx.LWk {ν κ α} : Ctx ν α → LCtx ν κ α → Type _
  | nil Γ : LWk Γ []
  | cons : Γ.Wk ℓ.live → LWk Γ L → LWk Γ (ℓ::L)

theorem Ctx.LWk.allEq {ν κ α} {Γ : Ctx ν α} {L : LCtx ν κ α} (w w' : Γ.LWk L)
  : w = w'
  := by induction w with
  | nil => cases w'; rfl
  | cons h _ I => cases w' with
    | cons =>
      congr
      apply Ctx.Wk.allEq
      exact I _

def Ctx.LWk.wk_entry {ν κ α} {Γ Δ : Ctx ν α} {L : LCtx ν κ α} (w : Γ.Wk Δ)
  : Δ.LWk L → Γ.LWk L
  | nil _ => nil Γ
  | cons w' lw => cons (w.comp w') (lw.wk_entry w)

def Ctx.LWk.wk_exit {ν κ α} {Γ : Ctx ν α} {L K : LCtx ν κ α}
  : Γ.LWk L → L.PWk K → Γ.LWk K
  | nil _, LCtx.PWk.nil => nil _
  | cons w lw, LCtx.PWk.cons w' pw => cons (w.comp w'.live) (lw.wk_exit pw)

structure LCtx.LiveComp {ν κ α} (L : LCtx ν κ α) where
  order : Ctx ν α
  w : order.LWk L

inductive Ctx.RWk {ν κ α} : Ctx ν α → LCtx ν κ α → Type _
  | nil Γ : RWk Γ []
  | cons : ℓ.live.Wk Γ → RWk Γ L → RWk Γ (ℓ::L)

theorem Ctx.RWk.allEq {ν κ α} {Γ : Ctx ν α} {L : LCtx ν κ α} (w w' : Γ.RWk L)
  : w = w'
  := by induction w with
  | nil => cases w'; rfl
  | cons h _ I => cases w' with
    | cons =>
      congr
      apply Ctx.Wk.allEq
      exact I _

def Ctx.RWk.wk_entry {ν κ α} {Γ Δ : Ctx ν α} {L : LCtx ν κ α} (w : Γ.Wk Δ)
  : Γ.RWk L → Δ.RWk L
  | nil _ => nil Δ
  | cons w' lw => cons (w'.comp w) (lw.wk_entry w)

def Ctx.RWk.wk_exit {ν κ α} {Γ : Ctx ν α} {L K : LCtx ν κ α}
  : Γ.RWk L → K.PWk L → Γ.RWk K
  | nil _, LCtx.PWk.nil => nil _
  | cons w lw, LCtx.PWk.cons w' pw => cons (w'.live.comp w) (lw.wk_exit pw)

def LCtx.dropAllRWk {ν κ α} : (L : LCtx ν κ α) → Ctx.RWk [] L
  | [] => Ctx.RWk.nil _
  | _::L => Ctx.RWk.cons (Ctx.Wk.drop _) (dropAllRWk L)

inductive Ctx.LEq {ν κ α} : Ctx ν α → LCtx ν κ α → Prop
  | nil Γ : LEq Γ []
  | cons : Γ = ℓ.live → LEq Γ L → LEq Γ (ℓ::L)

structure LCtx.LiveEq {ν κ α} (L : LCtx ν κ α) where
  order : Ctx ν α
  w : order.LEq L

theorem Ctx.LEq.head {ν κ α} {Γ : Ctx ν α} {ℓ : Label ν κ α} {L : LCtx ν κ α}
  : Γ.LEq (ℓ::L) → Γ = ℓ.live
  | cons h _ => h

theorem Ctx.LEq.tail {ν κ α} {Γ : Ctx ν α} {ℓ : Label ν κ α} {L : LCtx ν κ α}
  : Γ.LEq (ℓ::L) → Γ.LEq L
  | cons _ h => h

def Ctx.LEq.toLWk {ν κ α} {Γ : Ctx ν α} {L : LCtx ν κ α} (h : Γ.LEq L) : Γ.LWk L
  := match L with
  | [] => LWk.nil Γ
  | _::_ => LWk.cons (h.head ▸ Wk.refl _) (toLWk h.tail)

def Ctx.LEq.toRWk {ν κ α} {Γ : Ctx ν α} {L : LCtx ν κ α} (h : Γ.LEq L) : Γ.RWk L
  := match L with
  | [] => Ctx.RWk.nil Γ
  | _::_ => RWk.cons (h.head ▸ Wk.refl _) (toRWk h.tail)

def LCtx.LiveEq.toLiveComp {ν κ α} {L : LCtx ν κ α} (h : L.LiveEq) : L.LiveComp
  := ⟨h.order, Ctx.LEq.toLWk h.w⟩

theorem Ctx.LEq.head₂ {ν κ α} {Γ : Ctx ν α} {ℓ₁ ℓ₂ : Label ν κ α} {L K : LCtx ν κ α}
  : Γ.LEq (ℓ₁::L) → Γ.LEq (ℓ₂::K) → ℓ₁.name = ℓ₂.name → ℓ₁.param = ℓ₂.param → ℓ₁ = ℓ₂
  | cons h₁ _, cons h₂ _, hn, hp => by
    cases ℓ₁
    cases ℓ₂
    cases hn
    cases hp
    cases h₁
    cases h₂
    rfl

theorem Ctx.LWk.antisymm {ν κ α} {Γ : Ctx ν α} {L : LCtx ν κ α} (h : Γ.LWk L) (h' : Γ.RWk L)
  : Γ.LEq L
  := by induction h with
  | nil => cases h'; constructor
  | cons h _ I => cases h' with
    | cons =>
      constructor
      apply Ctx.Wk.antisymm <;> assumption
      exact I (by assumption)

theorem Ctx.RWk.antisymm {ν κ α} {Γ : Ctx ν α} {L : LCtx ν κ α} (h : Γ.RWk L) (h' : Γ.LWk L)
  : Γ.LEq L
  := h'.antisymm h

inductive LCtx.SJoin {ν κ α}
  : LCtx ν κ α → LCtx ν κ α → LCtx ν κ α → Type _
  | nil : SJoin [] [] []
  | left : K.Fresh ℓ.name → SJoin L K M → SJoin (ℓ::L) K (ℓ::M)
  | right : L.Fresh ℓ.name → SJoin L K M → SJoin L (ℓ::K) (ℓ::M)
  | both ℓ : SJoin L K M → SJoin (ℓ::L) (ℓ::K) (ℓ::M)

def LCtx.SJoin.comm {ν κ α} {L K M : LCtx ν κ α}
  : L.SJoin K M → K.SJoin L M
  | SJoin.nil => SJoin.nil
  | SJoin.left h j => SJoin.right h j.comm
  | SJoin.right h j => SJoin.left h j.comm
  | SJoin.both _ j => SJoin.both _ j.comm

def LCtx.SJoin.left_wk {ν κ α} {L K M : LCtx ν κ α}
  : L.SJoin K M → L.Wk M
  | SJoin.nil => Wk.nil
  | SJoin.left _ j => Wk.cons (Label.Wk.refl _) (left_wk j)
  | SJoin.right h j => Wk.skip h (left_wk j)
  | SJoin.both _ j => Wk.cons (Label.Wk.refl _) (left_wk j)

def LCtx.SJoin.right_wk {ν κ α} {L K M : LCtx ν κ α}
  : L.SJoin K M → K.Wk M
  | SJoin.nil => Wk.nil
  | SJoin.left h j => Wk.skip h (right_wk j)
  | SJoin.right _ j => Wk.cons (Label.Wk.refl _) (right_wk j)
  | SJoin.both _ j => Wk.cons (Label.Wk.refl _) (right_wk j)

theorem LCtx.SJoin.allEq {ν κ α} {L K M : LCtx ν κ α} (j j': L.SJoin K M): j = j'
  := by induction j with
  | nil => cases j'; rfl
  | left h j I =>
    cases j' with
    | left h' j' => congr; apply I
    | right h' j' => exact (h'.head rfl).elim
    | both _ j' => exact (h.head rfl).elim
  | right h j I =>
    cases j' with
    | left h' j' => exact (h'.head rfl).elim
    | right h' j' => congr; apply I
    | both _ j' => exact (h.head rfl).elim
  | both _ j I =>
    cases j' with
    | left h' j' => exact (h'.head rfl).elim
    | right h' j' => exact (h'.head rfl).elim
    | both _ j' => congr; apply I

theorem LCtx.SJoin.lEq {ν κ α} {Γ : Ctx ν α} {L K M : LCtx ν κ α}
  (j : L.SJoin K M)
  : Γ.LEq L → Γ.LEq K → Γ.LEq M
  := match j with
  | nil => λ_ h' => h'
  | left hl j => λh h' => Ctx.LEq.cons h.head (j.lEq h.tail h')
  | right hl j => λh h' => Ctx.LEq.cons h'.head (j.lEq h h'.tail)
  | both _ j => λh h' => Ctx.LEq.cons h.head (j.lEq h.tail h'.tail)

structure LCtx.Comp {ν κ α} (L K : LCtx ν κ α) where
  base : LCtx ν κ α
  left : L.Wk base
  right : K.Wk base

def LCtx.Wk.uncons₂ {ν κ α}
  {ℓ : Label ν κ α} {L K Ω : LCtx ν κ α}
  : Wk (ℓ::L) Ω → Wk (ℓ::K) Ω → L.Comp K
  | cons _ w, cons _ w' => ⟨_, w, w'⟩
  | skip h w, cons h' w' => by
    rw [Fresh.not_mem_iff, <-h'.name] at h
    simp [labels] at h
  | cons h _, skip h' w' => by
    rw [Fresh.not_mem_iff, <-h.name] at h'
    simp [labels] at h'
  | skip _ w, skip _ w' => uncons₂ w w'

def LCtx.Comp.uncons {ν κ α} {ℓ : Label ν κ α} {L K : LCtx ν κ α}
  (c : Comp (ℓ::L) (ℓ::K)) : Comp L K
  := c.left.uncons₂ c.right

theorem LCtx.Comp.head {ν κ α} {ℓ ℓ' : Label ν κ α} {L K : LCtx ν κ α}
  : Comp (ℓ::L) (ℓ'::K) → ℓ.name = ℓ'.name ∨ L.Fresh ℓ'.name ∨ K.Fresh ℓ.name
  | ⟨_, Wk.cons lw _, Wk.cons lw' _⟩ => Or.inl (lw.name.trans lw'.name.symm)
  | ⟨_, Wk.skip h _, Wk.cons lw' _⟩ => Or.inr (Or.inl (lw'.name ▸ h.tail))
  | ⟨_, Wk.cons lw _, Wk.skip h' _⟩ => Or.inr (Or.inr (lw.name ▸ h'.tail))
  | ⟨_, Wk.skip _ w, Wk.skip _ w'⟩ => head ⟨_, w, w'⟩

theorem LCtx.SJoin.trgEq {ν κ α} {L K M M' : LCtx ν κ α}
  (j : L.SJoin K M) (j' : L.SJoin K M') (oM : M.Comp M') : M = M' := by
  induction j generalizing M' with
  | nil => cases j'; rfl
  | left h j I =>
    cases j' with
    | left h' j' => rw [I j' oM.uncons]
    | right h' j' => match oM.head with
      | Or.inl hn => exact (h'.head hn).elim
      | Or.inr (Or.inl hn) => exact ((hn.wk j.right_wk).head rfl).elim
      | Or.inr (Or.inr hn) => exact ((hn.wk j'.left_wk).head rfl).elim
    | both _ j' => exact (h.head rfl).elim
  | right h j I =>
    cases j' with
    | left h' j' => match oM.head with
      | Or.inl hn => exact (h'.head hn).elim
      | Or.inr (Or.inl hn) => exact ((hn.wk j.left_wk).head rfl).elim
      | Or.inr (Or.inr hn) => exact ((hn.wk j'.right_wk).head rfl).elim
    | right h' j' => rw [I j' oM.uncons]
    | both _ j' => exact (h.head rfl).elim
  | both _ _ I =>
    cases j' with
    | left h' j' => exact (h'.head rfl).elim
    | right h' j' => exact (h'.head rfl).elim
    | both _ j' => rw [I j' oM.uncons]

inductive LCtx.Join {ν κ α}
  : LCtx ν κ α → LCtx ν κ α → LCtx ν κ α → Type _
  | nil : Join [] [] []
  | left : ℓ.Wk ℓ' → K.Fresh ℓ.name → Join L K M → Join (ℓ::L) K (ℓ'::M)
  | right : L.Fresh ℓ.name → ℓ.Wk ℓ' → Join L K M → Join L (ℓ::K) (ℓ'::M)
  | both : ℓ₁.Wk ℓ → ℓ₂.Wk ℓ → Join L K M → Join (ℓ₁::L) (ℓ₂::K) (ℓ::M)

def LCtx.Join.wk_exit {ν κ α} {L K M N : LCtx ν κ α}
  : L.Join K M → M.PWk N → L.Join K N
  | Join.nil, PWk.nil => Join.nil
  | Join.left w h lw, PWk.cons w' pw'
    => Join.left (w.comp w') h (wk_exit lw pw')
  | Join.right h w lw, PWk.cons w' pw'
    => Join.right h (w.comp w') (wk_exit lw pw')
  | Join.both w₁ w₂ lw, PWk.cons w' pw'
    => Join.both (w₁.comp w') (w₂.comp w') (wk_exit lw pw')

def LCtx.Join.wk_left {ν κ α} {L' L K M : LCtx ν κ α}
  : L'.PWk L → L.Join K M → L'.Join K M
  | PWk.nil, Join.nil => Join.nil
  | PWk.cons w pw, Join.left w' h lw => Join.left (w.comp w') (w.name ▸ h) (wk_left pw lw)
  | pw, Join.right h w' lw => Join.right (h.pwk pw) w' (wk_left pw lw)
  | PWk.cons w pw, Join.both w₁ w₂ lw => Join.both (w.comp w₁) w₂ (wk_left pw lw)

def LCtx.Join.wk_right {ν κ α} {K' K L M : LCtx ν κ α}
  : K'.PWk K → L.Join K M → L.Join K' M
  | PWk.nil, Join.nil => Join.nil
  | pw, Join.left w' h lw => Join.left w' (h.pwk pw) (wk_right pw lw)
  | PWk.cons w pw, Join.right h w' lw => Join.right (w.name ▸ h) (w.comp w') (wk_right pw lw)
  | PWk.cons w pw, Join.both w₁ w₂ lw => Join.both w₁ (w.comp w₂) (wk_right pw lw)

def LCtx.Join.comm {ν κ α} {L K M : LCtx ν κ α}
  : L.Join K M → K.Join L M
  | Join.nil => Join.nil
  | Join.left w h lw => Join.right h w lw.comm
  | Join.right h w lw => Join.left w h lw.comm
  | Join.both w₁ w₂ lw => Join.both w₂ w₁ lw.comm

def LCtx.SJoin.toJoin {ν κ α} {L K M : LCtx ν κ α}
  : L.SJoin K M → L.Join K M
  | SJoin.nil => Join.nil
  | SJoin.left h j => Join.left (Label.Wk.refl _) h (toJoin j)
  | SJoin.right h j => Join.right h (Label.Wk.refl _) (toJoin j)
  | SJoin.both _ j => Join.both (Label.Wk.refl _) (Label.Wk.refl _) (toJoin j)

structure LCtx.Join' {ν κ α} (L K M : LCtx ν κ α) where
  left : LCtx ν κ α
  right : LCtx ν κ α
  lPwk : L.PWk left
  rPwk : K.PWk right
  sJoin : left.SJoin right M

--TODO: try hand at uniqueness resuls
--TODO: assoc and friends

def LCtx.Join.factor {ν κ α} {L K M : LCtx ν κ α}
  : L.Join K M → L.Join' K M
  | Join.nil => ⟨[], [], PWk.nil, PWk.nil, SJoin.nil⟩
  | Join.left w h lw => match factor lw with
    | ⟨L', K', pw, pk, j⟩
      => ⟨_::L', K', PWk.cons w pw, pk, SJoin.left (w.name ▸ h.pwk_r pk) j⟩
  | Join.right h w lw => match factor lw with
    | ⟨L', K', pw, pk, j⟩
      => ⟨L', _::K', pw, PWk.cons w pk, SJoin.right (w.name ▸ h.pwk_r pw) j⟩
  | Join.both w₁ w₂ lw => match factor lw with
    | ⟨L', K', pw, pk, j⟩ => ⟨_::L', _::K', PWk.cons w₁ pw, PWk.cons w₂ pk, SJoin.both _ j⟩

def LCtx.Join.lEqFactor {ν κ α} {Γ : Ctx ν α} {L K M : LCtx ν κ α}
  (j : L.Join K M) : Γ.LEq L → Γ.LEq K → (M' : LCtx ν κ α) × L.SJoin K M' × M'.Wk M
  := match j with
  | Join.nil => λ_ _ => ⟨[], SJoin.nil, Wk.nil⟩
  | Join.left w h lw => λhl hr =>
    let lw' := lw.lEqFactor hl.tail hr;
    ⟨_, lw'.2.1.left h, lw'.2.2.cons w⟩
  | Join.right h w lw => λhl hr =>
    let lw' := lw.lEqFactor hl hr.tail;
    ⟨_, lw'.2.1.right h, lw'.2.2.cons w⟩
  | Join.both w₁ w₂ lw => λhl hr =>
    let lw' := lw.lEqFactor hl.tail hr.tail;
    ⟨_,
      hl.head₂ hr (w₁.name.trans w₂.name.symm) (w₁.param.trans w₂.param.symm) ▸ lw'.2.1.both _,
      lw'.2.2.cons w₁⟩

theorem LCtx.Fresh.join_left {ν κ α} {L K M : LCtx ν κ α} {l : κ}
  : L.Join K M → M.Fresh l → L.Fresh l
  | Join.nil, h => h
  | Join.left w _ j, cons hh hl => cons (hh.rwk_exit w) (join_left j hl)
  | Join.right _ _ j, cons _ hl => join_left j hl
  | Join.both w₁ _ j, cons hh hl => cons (hh.rwk_exit w₁) (join_left j hl)

theorem LCtx.Fresh.join_right {ν κ α} {L K M : LCtx ν κ α} {l : κ}
  : L.Join K M → M.Fresh l → K.Fresh l
  | Join.nil, h => h
  | Join.left _ _ j, cons hh hl => join_right j hl
  | Join.right _ w j, cons hh hl => cons (hh.rwk_exit w) (join_right j hl)
  | Join.both _ w₂ j, cons hh hl => cons (hh.rwk_exit w₂) (join_right j hl)

theorem LCtx.Fresh.join {ν κ α} {L K M : LCtx ν κ α} {l : κ}
  : L.Join K M → L.Fresh l → K.Fresh l → M.Fresh l
  | Join.nil, h, _ => h
  | Join.left w _ j, cons hh hl, hk => cons (hh.wk_exit w) (join j hl hk)
  | Join.right _ w j, hl, cons hh hk => cons (hh.wk_exit w) (join j hl hk)
  | Join.both w₁ _ j, cons hh hl, cons hh' hk => cons (hh.wk_exit w₁) (join j hl hk)

--TODO: skipwk, skipjoin, etc...

def LCtx.Join.ofWk {ν κ α} {L K M : LCtx ν κ α}
  : L.Wk M → K.Wk M → (M' : LCtx ν κ α) × L.Join K M' × M'.Wk M
  | Wk.nil, Wk.nil => ⟨[], Join.nil, Wk.nil⟩
  | Wk.cons w lw, Wk.cons w' lw' =>
    let j := ofWk lw lw';
    ⟨_, j.2.1.both w w', j.2.2.cons (Label.Wk.refl _)⟩
  | Wk.skip h lw, Wk.cons w' lw' =>
    let j := ofWk lw lw';
    ⟨_, j.2.1.right (w'.name ▸ h) w', j.2.2.cons (Label.Wk.refl _)⟩
  | Wk.cons w lw, Wk.skip h lw' =>
    let j := ofWk lw lw';
    ⟨_, j.2.1.left w (w.name ▸ h), j.2.2.cons (Label.Wk.refl _)⟩
  | Wk.skip h lw, Wk.skip h' lw' =>
    let j := ofWk lw lw';
    ⟨_, j.2.1, j.2.2.skip (h.join j.2.1 h')⟩

theorem LCtx.Fresh.sJoin {ν κ α} {L K M : LCtx ν κ α} {l : κ}
  : L.SJoin K M → L.Fresh l → K.Fresh l → M.Fresh l
  := λj => join j.toJoin

def LCtx.SJoin.ofWk {ν κ α} {Γ : Ctx ν α} {L K M : LCtx ν κ α}
  (wl : L.Wk M) (wr : K.Wk M) (eql : Γ.LEq L) (eqr : Γ.LEq K)
  : (M' : LCtx ν κ α) × L.SJoin K M' × M'.Wk M
  :=
    let j := Join.ofWk wl wr;
    let j' := j.2.1.lEqFactor eql eqr;
    ⟨j'.1, j'.2.1, j'.2.2.comp j.2.2⟩

def LCtx.Join'.toJoin {ν κ α} {L K M : LCtx ν κ α} (j : L.Join' K M) : L.Join K M
  := (j.sJoin.toJoin.wk_left j.lPwk).wk_right j.rPwk

inductive LCtx.EWk {ν κ α} : LCtx ν κ α → LCtx ν κ α → Type _
  | nil : EWk [] []
  | cons (ℓ) : EWk L K → EWk (ℓ::L) (ℓ::K)
  | skip {ℓ} : L.Fresh ℓ.name → EWk L K → EWk L (ℓ::K)

def LCtx.EWk.toWk {ν κ α} {L K : LCtx ν κ α} : L.EWk K → L.Wk K
  | EWk.nil => Wk.nil
  | EWk.cons _ w => Wk.cons (Label.Wk.refl _) (toWk w)
  | EWk.skip h w => Wk.skip h (toWk w)

def LCtx.EWk.comp {ν κ α} {L K M : LCtx ν κ α} : L.EWk K → K.EWk M → L.EWk M
  | EWk.nil, w => w
  | EWk.cons _ w, EWk.cons _ w' => EWk.cons _ (comp w w')
  | EWk.skip h w, EWk.cons _ w' => EWk.skip h (comp w w')
  | w, EWk.skip h w' => EWk.skip (h.wk w.toWk) (comp w w')

def LCtx.EWk.refl {ν κ α} : (L : LCtx ν κ α) → L.EWk L
  | [] => EWk.nil
  | _::L => EWk.cons _ (refl L)

theorem LCtx.EWk.antisymm {ν κ α} {L K : LCtx ν κ α} (w : L.EWk K) (w' : K.EWk L) : L = K
  := w.toWk.antisymm w'.toWk

theorem LCtx.EWk.allEq {ν κ α} {L K : LCtx ν κ α} : (w w' : L.EWk K) → w = w'
  | EWk.nil, EWk.nil => rfl
  | EWk.cons _ w, EWk.cons _ w' => congrArg _ (allEq w w')
  | EWk.skip _ w, EWk.skip _ w' => congrArg _ (allEq w w')
  | EWk.cons _ _, EWk.skip h _ => (h.head rfl).elim
  | EWk.skip h _, EWk.cons _ _ => (h.head rfl).elim

structure LCtx.Wk' {ν κ α} (L K : LCtx ν κ α) where
  base : LCtx ν κ α
  pWk : L.PWk base
  eWk : base.EWk K

def LCtx.Wk'.toWk {ν κ α} {L K : LCtx ν κ α} (w : L.Wk' K) : L.Wk K
  := w.pWk.toWk.comp w.eWk.toWk

def LCtx.Wk.factor {ν κ α} {L K : LCtx ν κ α} : L.Wk K → L.Wk' K
  | Wk.nil => ⟨[], PWk.nil, EWk.nil⟩
  | Wk.cons w lw =>
    let lw' := factor lw
    ⟨_, lw'.pWk.cons w, lw'.eWk.cons _⟩
  | Wk.skip h lw =>
    let lw' := factor lw
    ⟨_, lw'.pWk, lw'.eWk.skip (h.pwk_r lw'.pWk)⟩

inductive LCtx.SSplit {ν κ α}
  : LCtx ν κ α → LCtx ν κ α → LCtx ν κ α → Type _
  | nil : SSplit [] [] []
  | left {ℓ} : M.Fresh ℓ.name → SSplit L K M → SSplit (ℓ::L) (ℓ::K) M
  | right {ℓ} : K.Fresh ℓ.name → SSplit L K M → SSplit (ℓ::L) K (ℓ::M)

theorem LCtx.SSplit.allEq {ν κ α} {L K M : LCtx ν κ α} (s s' : L.SSplit K M): s = s'
  := by induction s with
  | nil => cases s'; rfl
  | left h j I =>
    cases s' with
    | left h' j' => congr; apply I
    | right h' j' => exact (h'.head rfl).elim
  | right h j I =>
    cases s' with
    | left h' j' => exact (h'.head rfl).elim
    | right h' j' => congr; apply I

def LCtx.SSplit.comm {ν κ α} {L K M : LCtx ν κ α}
  : L.SSplit K M → L.SSplit M K
  | SSplit.nil => SSplit.nil
  | SSplit.left h j => SSplit.right h j.comm
  | SSplit.right h j => SSplit.left h j.comm

def LCtx.SSplit.sJoin {ν κ α} {L K M : LCtx ν κ α}
  : L.SSplit K M → K.SJoin M L
  | SSplit.nil => SJoin.nil
  | SSplit.left h j => SJoin.left h (sJoin j)
  | SSplit.right h j => SJoin.right h (sJoin j)

--TODO: SSplit weakening, dealing with fresh variables...

inductive LCtx.LEq {ν κ α} : LCtx ν κ α → LCtx ν κ α → Prop
  | nil : LEq [] []
  | cons {ℓ ℓ' : Label ν κ α} : ℓ.name = ℓ'.name → ℓ.param = ℓ'.param → LEq L K → LEq (ℓ::L) (ℓ'::K)

theorem LCtx.LEq.symm {ν κ α} {L K : LCtx ν κ α} : L.LEq K → K.LEq L
  | nil => nil
  | cons hn hp h => cons hn.symm hp.symm h.symm

theorem LCtx.LEq.trans {ν κ α} {L K M : LCtx ν κ α} : L.LEq K → K.LEq M → L.LEq M
  | nil, h => h
  | cons hn hp h, cons hn' hp' h' => cons (hn.trans hn') (hp.trans hp') (h.trans h')

theorem LCtx.LEq.refl {ν κ α} : (L : LCtx ν κ α) → L.LEq L
  | [] => nil
  | _::L => cons rfl rfl (refl L)

theorem LCtx.PWk.toLEq {ν κ α} {L K : LCtx ν κ α} (w : L.PWk K) : L.LEq K
  := match w with
  | PWk.nil => LEq.nil
  | PWk.cons h w => LEq.cons h.name h.param (toLEq w)

--TODO: LWk et al...
