import Mathlib.Data.List.Basic
import Std.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Init.Classical

import FreydSSA.Ctx

--TODO: antisymm...

inductive Ty (α: Type u): Type u where
  | base (a : α)
  | pair (a b : Ty α)
  | unit
  | bool

inductive Purity
  | pure
  | impure

instance : OfNat Purity 0 where
  ofNat := Purity.impure

instance : OfNat Purity 1 where
  ofNat := Purity.pure

structure InstSet (α : Type u) : Type _ where
  Op : Purity → α → α → Type
  pure_to_impure : Op 1 a b → Op 0 a b

def InstSet.to_impure {α : Type u} (Φ : InstSet α) {p} {A B : α} (f : Φ.Op p A B)
  : Φ.Op 0 A B
  := match p with
  | Purity.pure => Φ.pure_to_impure f
  | Purity.impure => f

inductive InstSet.Tm {ν : Type u} {α : Type v} (Φ : InstSet (Ty α))
  : Purity → Ctx ν (Ty α) → Ty α → Type (max u v) where
  | var {n a} (p) : Γ.Wk [⟨n, a⟩] → Tm Φ p Γ a
  | op (f: Φ.Op p A B) : Tm Φ 1 Γ A → Tm Φ p Γ B
  | pair (p) : Tm Φ 1 Γ A → Tm Φ 1 Γ B → Tm Φ p Γ (Ty.pair A B)
  | unit (p) : Tm Φ p Γ Ty.unit
  | bool (p) (b: Bool) : Tm Φ p Γ Ty.bool

inductive InstSet.Tm.IsoSh {Φ : InstSet (Ty α)}: Φ.Tm p Γ A → Φ.Tm p' Γ' A' → Prop
  | var (p p') : w.Iso w' → IsoSh (Tm.var p w) (Tm.var p' w')
  | op (f) : Tm.IsoSh e e' → IsoSh (Tm.op f e) (Tm.op f e')
  | pair (p p') : Tm.IsoSh l l' → Tm.IsoSh r r' → IsoSh (Tm.pair p l r) (Tm.pair p' l' r')
  | unit (p p') : IsoSh (Tm.unit p) (Tm.unit p')
  | bool (p p') : IsoSh (Tm.bool p b) (Tm.bool p' b)

inductive InstSet.Tm.Iso {Φ : InstSet (Ty α)}: Φ.Tm p Γ A → Φ.Tm p Γ' A → Prop
  | var {Γ: Ctx ν (Ty α)} {Γ': Ctx ν' (Ty α)} (p)
    {w: Γ.Wk [⟨n, a⟩]} {w': Γ'.Wk [⟨n', a⟩]}: w.Iso w' → Iso (Tm.var p w) (Tm.var p w')
  | op (f) : Tm.Iso e e' → Iso (Tm.op f e) (Tm.op f e')
  | pair (p) : Tm.Iso l l' → Tm.Iso r r' → Iso (Tm.pair p l r) (Tm.pair p l' r')
  | unit (p) : Iso (Tm.unit p) (Tm.unit p)
  | bool (p) : Iso (Tm.bool p b) (Tm.bool p b)

theorem InstSet.Tm.Iso.refl {Φ : InstSet (Ty α)} {Γ : Ctx ν (Ty α)} {A : Ty α} {e : Φ.Tm p Γ A}
  : e.Iso e
  := by induction e with
  | var => constructor; apply Ctx.Wk.Iso.refl
  | _ => constructor <;> apply_assumption

theorem InstSet.Tm.Iso.symm {Φ : InstSet (Ty α)}
  {e : Φ.Tm p Γ A} {e' : Φ.Tm p Γ' A}
  (h : e.Iso e') : e'.Iso e
  := by induction h with
  | var _ I => constructor; exact I.symm
  | _ => constructor <;> apply_assumption

theorem InstSet.Tm.Iso.trans {Φ : InstSet (Ty α)}
  {e : Φ.Tm p Γ A} {e' : Φ.Tm p Γ' A} {e'' : Φ.Tm p Γ'' A}
  (h : e.Iso e') (h' : e'.Iso e'') : e.Iso e''
  := by induction h with
  | var _ I => cases h'; constructor; apply I.trans; assumption
  | _ => cases h'; constructor <;> apply_assumption <;> assumption

def InstSet.Tm.to_impure {Φ : InstSet (Ty α)} {A : Ty α} : Φ.Tm p Γ A → Φ.Tm 0 Γ A
  | var p h => var 0 h
  | op f e => op (Φ.to_impure f) e
  | pair p x y => pair 0 x y
  | unit p => unit 0
  | bool p b => bool 0 b

def InstSet.Tm.wk {Φ : InstSet (Ty α)} {A : Ty α} : Γ.Wk Δ → Φ.Tm p Δ A → Φ.Tm p Γ A
  | h, var p h' => var p (h.comp h')
  | h, op f e => op f (wk h e)
  | h, pair p x y => pair p (wk h x) (wk h y)
  | h, unit p => unit p
  | h, bool p b => bool p b

theorem InstSet.Tm.Iso.wk {Φ : InstSet (Ty α)}
  {Γ Δ : Ctx ν (Ty α)} {Γ' Δ' : Ctx ν' (Ty α)}
  {w : Γ.Wk Δ} {w' : Γ'.Wk Δ'}
  {e : Φ.Tm p Δ A} {e' : Φ.Tm p Δ' A}
  (hw : w.Iso w') (he : e.Iso e') : (e.wk w).Iso (e'.wk w')
  := by induction he with
  | var => simp only [Tm.wk]; constructor; apply Ctx.Wk.Iso.comp <;> assumption
  | _ => simp only [Tm.wk]; constructor <;> apply_assumption <;> assumption

inductive InstSet.Body {ν : Type u} {α : Type v} (Φ : InstSet (Ty α))
  : Purity → Ctx ν (Ty α) → Ctx ν (Ty α) → Type (max u v) where
  | nil (p) : Γ.Wk Δ → Body Φ p Γ Δ
  | let1 : Φ.Tm p Γ a → Body Φ p (⟨x, a⟩::Γ) Δ → Body Φ p Γ Δ
  | let2 : Φ.Tm p Γ (Ty.pair A B)
    → Body Φ p (⟨x, A⟩::⟨y, B⟩::Γ) Δ
    → Body Φ p Γ Δ

inductive InstSet.Body.Iso {Φ : InstSet (Ty α)}: Φ.Body p Γ Δ → Φ.Body p Γ' Δ' → Prop
  | nil (p) : w.Iso w' → Iso (Body.nil p w) (Body.nil p w')
  | let1 : Tm.Iso e e' → Body.Iso b b' → Iso (Body.let1 e b) (Body.let1 e' b')
  | let2 : Tm.Iso e e' → Body.Iso b b' → Iso (Body.let2 e b) (Body.let2 e' b')

theorem InstSet.Body.Iso.refl {Φ : InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)} {p}
  (e : Φ.Body p Γ Δ)
  : e.Iso e
  := by induction e with
  | nil _ I => constructor; exact I.iso_refl
  | _ =>
    constructor
    . apply Tm.Iso.refl
    . apply_assumption

theorem InstSet.Body.Iso.symm {Φ : InstSet (Ty α)}
  {e : Φ.Body p Γ Δ} {e' : Φ.Body p Γ' Δ'}
  (h : e.Iso e') : e'.Iso e
  := by induction h with
  | nil _ I => constructor; exact I.symm
  | _ =>
    constructor
    . apply Tm.Iso.symm; assumption
    . apply_assumption

theorem InstSet.Body.Iso.trans {Φ : InstSet (Ty α)}
  {e : Φ.Body p Γ Δ} {e' : Φ.Body p Γ' Δ'} {e'' : Φ.Body p Γ'' Δ''}
  (h : e.Iso e') (h' : e'.Iso e'') : e.Iso e''
  := by induction h generalizing Γ'' Δ'' with
  | nil _ I => cases h'; constructor; apply I.trans; assumption
  | _ =>
    cases h'
    constructor
    . apply Tm.Iso.trans <;> assumption
    . apply_assumption; assumption

def InstSet.Body.to_impure {Φ : InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)}
  : Φ.Body p Γ Δ → Φ.Body 0 Γ Δ
  | nil _ h => nil 0 h
  | let1 e b => let1 e.to_impure b.to_impure
  | let2 e b => let2 e.to_impure b.to_impure

def InstSet.Body.wk_entry {Φ : InstSet (Ty α)} {Γ Δ Ξ : Ctx ν (Ty α)}
  : Γ.Wk Δ → Φ.Body p Δ Ξ → Φ.Body p Γ Ξ
  | h, nil p h' => nil p (h.comp h')
  | h, let1 e b => let1 (Tm.wk h e) (wk_entry (h.cons _) b)
  | h, let2 e b => let2 (Tm.wk h e) (wk_entry ((h.cons _).cons _) b)

def InstSet.Body.wk_exit {Φ : InstSet (Ty α)} {Γ Δ Ξ : Ctx ν (Ty α)}
  : Φ.Body p Γ Δ → Δ.Wk Ξ → Φ.Body p Γ Ξ
  | nil p h, h' => nil p (h.comp h')
  | let1 e b, h' => let1 e (wk_exit b h')
  | let2 e b, h' => let2 e (wk_exit b h')

def InstSet.Body.comp {Φ : InstSet (Ty α)} {Γ Δ Ξ : Ctx ν (Ty α)}
  : Φ.Body p Γ Δ → Φ.Body p Δ Ξ → Φ.Body p Γ Ξ
  | nil p h, b => wk_entry h b
  | let1 e b, b' => let1 e (comp b b')
  | let2 e b, b' => let2 e (comp b b')

theorem InstSet.Body.Iso.wk_entry {Φ : InstSet (Ty α)}
  {Γ Δ Ξ : Ctx ν (Ty α)} {Γ' Δ' Ξ' : Ctx ν' (Ty α)}
  {w: Γ.Wk Δ} {w': Γ'.Wk Δ'} {b: Φ.Body p Δ Ξ} {b': Φ.Body p Δ' Ξ'}
  (hw: w.Iso w') (hb: b.Iso b')
  : (wk_entry w b).Iso (wk_entry w' b')
  := by induction hb with
  | nil => simp only [Body.wk_entry]; constructor; apply Ctx.Wk.Iso.comp <;> assumption
  | _ =>
    simp only [Body.wk_entry]
    constructor
    . apply Tm.Iso.wk <;> assumption
    . apply_assumption
      repeat constructor
      assumption

theorem InstSet.Body.Iso.wk_exit {Φ : InstSet (Ty α)}
  {Γ Δ Ξ' : Ctx ν (Ty α)} {Γ' Δ' Ξ' : Ctx ν' (Ty α)}
  {b: Φ.Body p Γ Δ} {b': Φ.Body p Γ' Δ'} {w: Δ.Wk Ξ} {w': Δ'.Wk Ξ'}
  (hw: w.Iso w') (hb: b.Iso b')
  : (wk_exit b w).Iso (wk_exit b' w')
  := by induction hb with
  | nil => simp only [Body.wk_exit]; constructor; apply Ctx.Wk.Iso.comp <;> assumption
  | _ =>
    simp only [Body.wk_exit]
    constructor
    . assumption
    . apply_assumption <;> assumption

theorem InstSet.Body.Iso.comp {Φ: InstSet (Ty α)}
  {l: Φ.Body p Γ Δ} {l': Φ.Body p Γ' Δ'}
  {r: Φ.Body p Δ Ξ} {r': Φ.Body p Δ' Ξ'}
  (hl: l.Iso l') (hr: r.Iso r')
  : (l.comp r).Iso (l'.comp r')
  := by induction hl with
  | nil _ hw => simp only [Body.comp]; exact wk_entry hw hr
  | _ =>
    simp only [Body.comp]
    constructor
    . assumption
    . apply_assumption; assumption

def Ctx.Wk.names {ν α} {Γ Δ : Ctx ν α} : Γ.Wk Δ → Δ.names.Sublist Γ.names
  | Wk.nil => List.Sublist.slnil
  | Wk.cons _ h => h.names.cons₂ _
  | Wk.skip _ h => h.names.cons _

def Var.rename {ν ν' α} (ρ : ν → ν') (v : Var ν α) : Var ν' α
  := ⟨ρ v.name, v.ty⟩

theorem Var.rename_eq {ν ν' α} (v: Var ν α) (ρ₁ ρ₂: ν → ν')
  : ρ₁ v.name = ρ₂ v.name → Var.rename ρ₁ v = Var.rename ρ₂ v
  := by cases v; simp [rename]

def Ctx.rename {ν ν' α} (ρ : ν → ν') (Γ : Ctx ν α) : Ctx ν' α
  := Γ.map (Var.rename ρ)

def Ctx.InjOn (ρ : ν → ν') (Γ : Ctx ν α) : Prop
  := Set.InjOn ρ { x : ν | x ∈ Γ.names }

theorem Ctx.injOn_empty (ρ : ν → ν') : Ctx.InjOn ρ (@List.nil (Var ν α))
  := λ _ hx => nomatch hx

theorem Ctx.InjOn.tail {ρ: ν → ν'} {v} {Γ : Ctx ν α} (h: Ctx.InjOn ρ (v::Γ))
  : Ctx.InjOn ρ Γ
  := λ _ hx _ hy hxy => h (hx.tail _) (hy.tail _) hxy

theorem Ctx.InjOn.head {ρ: ν → ν'} {v} {Γ : Ctx ν α} (h: Ctx.InjOn ρ (v::Γ))
  : ∀x ∈ Γ.names, ρ x = ρ v.name → x = v.name
  := λ _ hx hx' => h (hx.tail _) (by simp) hx'

theorem Ctx.InjOn.head_ne {ρ : ν → ν'} {v} {Γ : Ctx ν α} (h : Ctx.InjOn ρ (v::Γ))
  : ∀x ∈ Γ.names, x ≠ v.name → ρ x ≠ ρ v.name
  := λ _ hx hx' => h.ne (hx.tail _) (by simp) hx'

theorem Ctx.InjOn.cons {ρ : ν → ν'} {v : Var ν α} {Γ : Ctx ν α}
  (hv : ∀x ∈ Γ.names, ρ x = ρ v.name → x = v.name) (h : Ctx.InjOn ρ Γ)
  : Ctx.InjOn ρ (v::Γ)
  | _, List.Mem.head _, _, List.Mem.head _, _ => rfl
  | _, List.Mem.head _, _, List.Mem.tail _ ha, hav => (hv _ ha hav.symm).symm
  | _, List.Mem.tail _ ha, _, List.Mem.head _, hav => hv _ ha hav
  | _, List.Mem.tail _ hx, _, List.Mem.tail _ hy, hxy => h hx hy hxy

theorem Ctx.InjOn.cons_ne {ρ : ν → ν'} {v : Var ν α} {Γ : Ctx ν α}
  (hv : ∀x ∈ Γ.names, x ≠ v.name → ρ x ≠ ρ v.name) (h : Ctx.InjOn ρ Γ)
  : Ctx.InjOn ρ (v::Γ)
  := h.cons (λ_ hx hxv => Classical.by_contradiction (λh => hv _ hx h hxv))

theorem Ctx.InjOn.wk {ρ : ν → ν'} {Γ : Ctx ν α} (hΓ : Γ.InjOn ρ) : Γ.Wk Δ → Δ.InjOn ρ
  | Wk.nil => Ctx.injOn_empty _
  | Wk.cons x h => (hΓ.tail.wk h).cons (λ_ hx hxv => hΓ.head _ (h.names.subset hx) hxv)
  | Wk.skip _ h => hΓ.tail.wk h

theorem Ctx.Fresh.rename {ν α} {ρ: ν → ν'} {Γ : Ctx ν α} {n}
  (hΓ : Γ.InjOn ρ) (hn : ∀x ∈ Γ.names, x ≠ n → ρ x ≠ ρ n)
  : Fresh n Γ → Fresh (ρ n) (rename ρ Γ)
  | nil => nil
  | cons hxn hn' => cons (hn _ (by simp) hxn) (hn'.rename hΓ.tail (λ x hx => hn _ (hx.tail _)))

def Ctx.Wk.rename {ν α} {ρ : ν → ν'} {Γ Δ : Ctx ν α} (hΓ : Γ.InjOn ρ)
  : Γ.Wk Δ → (rename ρ Γ).Wk (rename ρ Δ)
  | nil => nil
  | cons x h => cons ⟨ρ x.name, x.ty⟩ (rename hΓ.tail h)
  | skip hxn h => skip
    (hxn.rename (hΓ.wk (skip hxn h)) (hΓ.wk (cons _ h)).head_ne)
    (rename hΓ.tail h)

def Ctx.Wk.rename_iso {Γ Δ : Ctx ν α} {ρ: ν → ν'} (hΓ : Γ.InjOn ρ) (w: Γ.Wk Δ)
  : w.Iso (w.rename hΓ) := match Γ, Δ, w with
  | [], [], nil => Iso.nil
  | _::_, _::_, cons _ w => Iso.cons (w.rename_iso hΓ.tail)
  | _::_, _, skip _ w => Iso.skip (w.rename_iso hΓ.tail)

def InstSet.Tm.rename {Φ : InstSet (Ty α)} {Γ : Ctx ν (Ty α)} {a : Ty α}
  {ρ : ν → ν'} (hρ : Γ.InjOn ρ) : Φ.Tm p Γ a → Φ.Tm p (Γ.rename ρ) a
  | var p h' => @var _ _ _ _ (ρ _) _ p (h'.rename hρ)
  | op f e => op f (e.rename hρ)
  | pair p l r => pair p (l.rename hρ) (r.rename hρ)
  | unit p => unit p
  | bool p b => bool p b

theorem InstSet.Tm.rename_iso {Φ : InstSet (Ty α)} {Γ : Ctx ν (Ty α)} {a : Ty α}
  {ρ : ν → ν'} (hρ : Γ.InjOn ρ) (e: Φ.Tm p Γ a) : e.Iso (e.rename hρ)
  := by induction e with
  | @var Γ n a p w => simp only [rename]; constructor; exact w.rename_iso hρ
  | _ => simp only [rename]; constructor <;> apply_assumption

inductive InstSet.Body.InjOn {Φ : InstSet (Ty α)} (ρ : ν → ν')
  : {Γ Δ: Ctx ν (Ty α)} → Φ.Body p Γ Δ → Prop
  | nil {Γ Δ: Ctx ν (Ty α)} (h: Γ.Wk Δ): Γ.InjOn ρ → Body.InjOn ρ (Body.nil p h)
  | let1 {b: Φ.Body p (⟨x, A⟩::Γ) Δ} (e: Φ.Tm p Γ A): b.InjOn ρ → (b.let1 e).InjOn ρ
  | let2 {b: Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ} (e: Φ.Tm p Γ (Ty.pair A B)):
    b.InjOn ρ → (b.let2 e).InjOn ρ

def InstSet.Body.InjOn.entry {Φ : InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)} {p}
  {b : Φ.Body p Γ Δ} {ρ : ν → ν'} : b.InjOn ρ → Γ.InjOn ρ
  | nil _ h => h
  | let1 _ h => h.entry.tail
  | let2 _ h => h.entry.tail.tail

def InstSet.Body.InjOn.exit {Φ : InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)} {p}
  {b : Φ.Body p Γ Δ} {ρ : ν → ν'} : b.InjOn ρ → Δ.InjOn ρ
  | nil w h => h.wk w
  | let1 _ h => h.exit
  | let2 _ h => h.exit

--TODO: InstSet.InjOn case helpers?
def InstSet.Body.rename {Φ : InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)}
  {ρ : ν → ν'} : {b : Φ.Body p Γ Δ} → b.InjOn ρ → Φ.Body p (Γ.rename ρ) (Δ.rename ρ)
  | nil _ h, hρ => nil _ (h.rename (by cases hρ; assumption))
  | let1 e b, hρ => let1 (e.rename hρ.entry) (b.rename (by cases hρ; assumption))
  | let2 e b, hρ => let2 (e.rename hρ.entry) (b.rename (by cases hρ; assumption))

theorem InstSet.Body.rename_iso {Φ : InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)}
  {ρ : ν → ν'} {b : Φ.Body p Γ Δ} (hb: b.InjOn ρ): b.Iso (b.rename hb)
  := by induction b with
  | nil _ h =>
    simp only [rename]
    constructor
    exact h.rename_iso (hb.entry)
  | let1 e b I =>
    simp only [rename]
    constructor
    exact e.rename_iso (hb.entry)
    apply I
  | let2 e b I =>
    simp only [rename]
    constructor
    exact e.rename_iso (hb.entry)
    apply I

def Ctx.EqOn (ρ₁ ρ₂ : ν → ν') (Γ : Ctx ν α): Prop
  := Set.EqOn ρ₁ ρ₂ { x : ν | x ∈ Γ.names }

theorem Ctx.EqOn.head {ρ₁ ρ₂ : ν → ν'} {v} {Γ : Ctx ν α} (h : Ctx.EqOn ρ₁ ρ₂ (v::Γ))
  : ρ₁ v.name = ρ₂ v.name
  := h (by simp)

theorem Ctx.EqOn.tail {ρ₁ ρ₂ : ν → ν'} {v} {Γ : Ctx ν α} (h : Ctx.EqOn ρ₁ ρ₂ (v::Γ))
  : Ctx.EqOn ρ₁ ρ₂ Γ
  := λ _ hx => h (hx.tail _)

theorem Ctx.rename_id: (Γ : Ctx ν α) → Γ.rename id = Γ
  | [] => rfl
  | _::Γ => congrArg _ (rename_id Γ)

theorem Ctx.EqOn.rename {ρ₁ ρ₂ : ν → ν'} {Γ : Ctx ν α} (hΓ : Γ.EqOn ρ₁ ρ₂)
  : Γ.rename ρ₁ = Γ.rename ρ₂
  := List.map_congr (λ_ hx => Var.rename_eq _ _ _  (hΓ (List.mem_map_of_mem _ hx)))

theorem Ctx.EqOn.rename_id {ρ : ν → ν} {Γ : Ctx ν α} (hΓ : Γ.EqOn ρ id)
  : Γ.rename ρ = Γ
  := hΓ.rename.trans Γ.rename_id

structure InstSet.Body.RnOn {Φ : InstSet (Ty α)} (ρ : ν → ν) {Γ Δ : Ctx ν (Ty α)}
  (b: Φ.Body p Γ Δ) : Prop where
  injOn: b.InjOn ρ
  entry: Γ.EqOn ρ id
  exit: Δ.EqOn ρ id

def InstSet.Body.alpha {Φ : InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)}
  {ρ : ν → ν} {b : Φ.Body p Γ Δ} (hb: b.RnOn ρ): Φ.Body p Γ Δ
  := hb.entry.rename_id ▸ hb.exit.rename_id ▸ b.rename hb.injOn

inductive InstSet.Body.Fresh {Φ : InstSet (Ty α)} (n: ν)
  : {Γ Δ: Ctx ν (Ty α)} → Φ.Body p Γ Δ → Prop
  | nil {Γ Δ: Ctx ν (Ty α)} (h: Γ.Wk Δ): Γ.Fresh n → Body.Fresh n (Body.nil p h)
  | let1 {b: Φ.Body p (⟨x, A⟩::Γ) Δ} (e: Φ.Tm p Γ A): b.Fresh n → (b.let1 e).Fresh n
  | let2 {b: Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ} (e: Φ.Tm p Γ (Ty.pair A B)):
    b.Fresh n → (b.let2 e).Fresh n

theorem InstSet.Body.Fresh.entry {Φ : InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)} {p}
  {b : Φ.Body p Γ Δ} {n} : b.Fresh n → Γ.Fresh n
  | nil _ h => h
  | let1 _ h => h.entry.tail
  | let2 _ h => h.entry.tail.tail

theorem InstSet.Body.Fresh.exit {Φ : InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)} {p}
  {b : Φ.Body p Γ Δ} {n} : b.Fresh n → Δ.Fresh n
  | nil w h => h.wk w
  | let1 _ h => h.exit
  | let2 _ h => h.exit

def InstSet.Body.defs {Φ : InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)}
  : Φ.Body p Γ Δ → List ν
  | nil _ _ => []
  | @let1 _ _ _ _ _ _ x _ _ b => x::b.defs
  | @let2 _ _ _ _ _ _ _ x y _ _ b => x::y::b.defs

inductive InstSet.Body.NotDef {Φ : InstSet (Ty α)} (n: ν)
  : {Γ Δ : Ctx ν (Ty α)} → Φ.Body p Γ Δ → Prop
  | nil {Γ Δ: Ctx ν (Ty α)} (h: Γ.Wk Δ): Body.NotDef n (Body.nil p h)
  | let1 {b: Φ.Body p (⟨x, A⟩::Γ) Δ}: x ≠ n → (e: Φ.Tm p Γ A) →
    b.NotDef n → (b.let1 e).NotDef n
  | let2 {b: Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ}: x ≠ n → y ≠ n →
    (e: Φ.Tm p Γ (Ty.pair A B)) → b.NotDef n → (b.let2 e).NotDef n

theorem InstSet.Body.NotDef.not_mem_defs {Φ: InstSet (Ty α)} {b: Φ.Body p Γ Δ}
  : b.NotDef n → n ∉ b.defs
  | nil _ => by simp [defs]
  | let1 hx e b => by
    simp only [defs, List.mem_cons, not_or]
    exact ⟨hx.symm, b.not_mem_defs⟩
  | let2 hx hy e b => by
    simp only [defs, List.mem_cons, not_or]
    exact ⟨hx.symm, hy.symm, b.not_mem_defs⟩

theorem InstSet.Body.NotDef.of_not_mem_defs {Φ: InstSet (Ty α)} {b: Φ.Body p Γ Δ}
  : n ∉ b.defs → b.NotDef n
  := by induction b with
  | nil => exact λ_ => NotDef.nil _
  | let1 _ _ I =>
    simp only [defs, List.mem_cons, not_or, and_imp]
    intro hx hn
    constructor
    exact Ne.symm hx
    exact I hn
  | let2 _ _ I =>
    simp only [defs, List.mem_cons, not_or, and_imp]
    intro hx hy hn
    constructor
    exact Ne.symm hx
    exact Ne.symm hy
    exact I hn

theorem InstSet.Body.NotDef.iff_not_mem_defs {Φ: InstSet (Ty α)} {b: Φ.Body p Γ Δ}
  : b.NotDef n ↔ n ∉ b.defs
  := ⟨not_mem_defs, of_not_mem_defs⟩

theorem InstSet.Body.Fresh.notDef {Φ : InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)} {p}
  {b : Φ.Body p Γ Δ} {n} : b.Fresh n → b.NotDef n
  | nil _ h => NotDef.nil _
  | let1 _ h => NotDef.let1 h.entry.head _ h.notDef
  | let2 _ h => NotDef.let2 h.entry.head h.entry.tail.head _ h.notDef

theorem InstSet.Body.NotDef.toFresh {Φ: InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)} {p}
  {b: Φ.Body p Γ Δ} {n} (hb: b.NotDef n) (hΓ: Γ.Fresh n): b.Fresh n
  := by induction hb with
  | _ =>
    constructor
    apply_assumption
    repeat first | apply Ctx.Fresh.cons | assumption

inductive InstSet.Body.SSA {Φ: InstSet (Ty α)}
  : {Γ Δ: Ctx ν (Ty α)} → Φ.Body p Γ Δ → Prop
  | nil {Γ Δ: Ctx ν (Ty α)} (h: Γ.Wk Δ): Body.SSA (Body.nil p h)
  | let1 {b: Φ.Body p (⟨x, A⟩::Γ) Δ}:
    Ctx.Fresh x Γ → (e: Φ.Tm p Γ A) → b.SSA → (b.let1 e).SSA
  | let2 {b: Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ}:
      x ≠ y →
      Ctx.Fresh x Γ →
      Ctx.Fresh y Γ →
      (e: Φ.Tm p Γ (Ty.pair A B)) →
      b.SSA →
      (b.let2 e).SSA

def InstSet.Body.αSSA {Φ: InstSet (Ty α)} (b: Φ.Body p Γ Δ): Prop
  := ∃b' : Φ.Body p Γ Δ, b'.SSA ∧ b.Iso b'

structure InstSet.Body.Renaming {Φ: InstSet (Ty α)}
  {Γ Δ : Ctx ν (Ty α)} (b: Φ.Body p Γ Δ) (Γ' Δ': Ctx ν' (Ty α))
  where
  val : Φ.Body p Γ' Δ'
  isIso : b.Iso val

structure InstSet.Body.SSAForm {Φ: InstSet (Ty α)}
  {Γ Δ : Ctx ν (Ty α)} (b: Φ.Body p Γ Δ) (Γ' Δ': Ctx ν' (Ty α))
  extends Renaming b Γ' Δ' where
  isSSA : val.SSA

structure InstSet.SSABody {Φ: InstSet (Ty α)} (p: Purity) (Γ Δ: Ctx ν (Ty α)) where
  val : Φ.Body p Γ Δ
  isSSA : val.SSA

-- TODO: every body, w/ de-Bruijn indices, can be placed into SSA...

-- TODO: in particular, if ν is infinite (or actually, just > |b| + |Γ|), then every body from Γ to
--Δ is in αSSA

inductive InstSet.Terminator
  (Φ : InstSet (Ty α)) (Γ : Ctx ν (Ty α)) (L : LCtx ν (Ty α))
  : Type _
  | br : Φ.Tm 1 Γ A → LCtx.Wk [⟨⟨n, A⟩, Γ⟩] L → Φ.Terminator Γ L
  | ite : Φ.Tm 1 Γ Ty.bool → Φ.Terminator Γ L → Φ.Terminator Γ L → Φ.Terminator Γ L

def InstSet.Terminator.wk_entry {Φ : InstSet (Ty α)}
  (w: Γ.Wk Δ): Φ.Terminator Δ L → Φ.Terminator Γ L
  | br e h => br (e.wk w) --TODO: clean this up
    (@LCtx.Wk.comp _ _ [⟨_, Γ⟩] [⟨_, Δ⟩] _
      (LCtx.Wk.cons ⟨rfl, w⟩ LCtx.Wk.nil) h)
  | ite e t f => ite (e.wk w) (t.wk_entry w) (f.wk_entry w)

def InstSet.Terminator.wk_exit {Φ: InstSet (Ty α)}
  : Φ.Terminator Γ L → L.Wk K → Φ.Terminator Γ K
  | br e h, w => br e (h.comp w)
  | ite e t f, w => ite e (t.wk_exit w) (f.wk_exit w)

structure InstSet.BB (Φ : InstSet (Ty α)) (Γ : Ctx ν (Ty α)) (L : LCtx ν (Ty α)) where
  body: Φ.Body p Γ Δ
  -- Issue: underspecified: can change Δ, so must quotient somehow
  terminator: Φ.Terminator Δ L

def InstSet.BB.wk_entry {Φ : InstSet (Ty α)}
  (w: Γ.Wk Δ) (β: Φ.BB Δ L): Φ.BB Γ L where
  body := β.body.wk_entry w
  terminator := β.terminator

def InstSet.BB.wk_exit {Φ : InstSet (Ty α)}
  (β: Φ.BB Γ L) (w: L.Wk K): Φ.BB Γ K where
  body := β.body
  terminator := β.terminator.wk_exit w

inductive InstSet.ICFG
  (Φ : InstSet (Ty α))
  : (L K : LCtx ν (Ty α)) -> Type _
  | nil : L.Wk K → InstSet.ICFG Φ L K
  | cons : InstSet.ICFG Φ L (⟨x, Γ⟩::K) → Φ.BB (x::Γ) L → InstSet.ICFG Φ L K

def InstSet.ICFG.wk_exit
  {Φ : InstSet (Ty α)} {L K M : LCtx ν (Ty α)}
  : (κ: Φ.ICFG L K) → K.Wk M → Φ.ICFG L M
  | nil w, w' => nil (w.comp w')
  | cons κ β, w' => cons (κ.wk_exit (w'.cons (Label.Wk.refl _))) β

structure InstSet.CFG (Φ : InstSet (Ty α)) (L K : LCtx ν (Ty α))
  where
  looped : L.Wk W
  inner : Φ.ICFG W K

def InstSet.CFG.wk_exit
  {Φ : InstSet (Ty α)} {L K M : LCtx ν (Ty α)}
  (κ: Φ.CFG L K) (w: K.Wk M): Φ.CFG L M where
  looped := κ.looped
  inner := κ.inner.wk_exit w

def InstSet.CFG.wk_entry
  {Φ : InstSet (Ty α)} {L K M : LCtx ν (Ty α)}
  (w: L.Wk K) (κ: Φ.CFG K M): Φ.CFG L M where
  looped := w.comp κ.looped
  inner := κ.inner

structure InstSet.Region (Φ : InstSet (Ty α)) (Γ : Ctx ν (Ty α)) (L : LCtx ν (Ty α)) where
  entry : Φ.BB Γ K
  -- Issue: underspecified: can change K, so must quotient somehow
  cfg : Φ.ICFG K L

inductive GCtx (ν : Type u) (α : Type v) where
  | ctx : Ctx ν α → GCtx ν α
  | lctx : LCtx ν α → GCtx ν α

inductive InstSet.GRegion (Φ : InstSet (Ty α)) : GCtx ν (Ty α) → LCtx ν (Ty α) → Type _
  | br : Φ.Tm 1 Γ A → LCtx.Wk [⟨⟨n, A⟩, Γ⟩] L → Φ.GRegion (GCtx.ctx Γ) L
  | ite : Φ.Tm 1 Γ Ty.bool
    → Φ.GRegion (GCtx.ctx Γ) L
    → Φ.GRegion (GCtx.ctx Γ) L
    → Φ.GRegion (GCtx.ctx Γ) L
  | dom : Φ.GRegion (GCtx.ctx Γ) K → Φ.GRegion (GCtx.lctx L) K → Φ.GRegion (GCtx.ctx Γ) L
  | nil : L.Wk K → Φ.GRegion (GCtx.lctx L) K
  | cons : Φ.GRegion (GCtx.lctx L) (⟨x, Γ⟩::K) → Φ.BB (x::Γ) L → Φ.GRegion (GCtx.lctx L) K

inductive InstSet.UTm {α : Type v} (Φ : InstSet (Ty α)) (ν : Type u)
  : Type (max u v) where
  | var : ν → Φ.UTm ν
  | op : Φ.Op p A B → Φ.UTm ν
  | pair : Φ.UTm ν → Φ.UTm ν → Φ.UTm ν
  | unit : Φ.UTm ν
  | bool : Bool → Φ.UTm ν

inductive InstSet.UBody {α : Type v} (Φ : InstSet (Ty α)) (ν : Type u)
  : Type (max u v) where
  | nil : Φ.UBody ν
  | let1 : Φ.UTm ν → Φ.UBody ν → Φ.UBody ν
  | let2 : Φ.UTm ν → Φ.UBody ν → Φ.UBody ν

inductive InstSet.UTerminator {α : Type v} (Φ : InstSet (Ty α)) (ν : Type u)
  : Type (max u v) where
  | br : Φ.UTm ν → List ν → Φ.UTerminator ν
  | ite : Φ.UTm ν → Φ.UTerminator ν → Φ.UTerminator ν → Φ.UTerminator ν

structure InstSet.UBB {α : Type v} (Φ : InstSet (Ty α)) (ν : Type u)
  : Type (max u v) where
  body : Φ.UBody ν
  terminator : Φ.UTerminator ν

inductive InstSet.UCFG {α : Type v} (Φ : InstSet (Ty α)) (ν : Type u)
  : Type (max u v) where
  | nil : Φ.UCFG ν
  | cons : Φ.UCFG ν → Φ.UBB ν → Φ.UCFG ν

structure InstSet.URegion {α : Type v} (Φ : InstSet (Ty α)) (ν : Type u)
  : Type (max u v) where
  entry : Φ.UBB ν
  cfg : Φ.UCFG ν

inductive InstSet.UGRegion {α : Type v} (Φ : InstSet (Ty α)) (ν : Type u)
  : Type (max u v) where
  | br : Φ.UTm ν → List ν → Φ.UGRegion ν
  | ite : Φ.UTm ν → Φ.UGRegion ν → Φ.UGRegion ν → Φ.UGRegion ν
  | dom : Φ.UGRegion ν → Φ.UGRegion ν → Φ.UGRegion ν
  | nil : List ν → Φ.UGRegion ν
  | cons : Φ.UGRegion ν → Φ.UBB ν → Φ.UGRegion ν
