import FreydSSA.Ctx
import FreydSSA.InstSet
import FreydSSA.Utils

--TODO: map_inst

inductive UTm (φ : Type _) (ν  : Type _)
   : Type _ where
  | var : ν → UTm φ ν
  | op : φ → UTm φ ν → UTm φ ν
  | pair : UTm φ ν → UTm φ ν → UTm φ ν
  | unit : UTm φ ν
  | bool : Bool → UTm φ ν

def UTm.rename {ν ν'}
  (σ : ν → ν') : UTm φ ν → UTm φ ν'
  | var x => var (σ x)
  | op f e => op f (e.rename σ)
  | pair l r => pair (l.rename σ) (r.rename σ)
  | unit => unit
  | bool b => bool b

def UTm.rewrite {ν ν'}
  (σ : ν → UTm φ ν') : UTm φ ν → UTm φ ν'
  | var x => σ x
  | op f e => op f (e.rewrite σ)
  | pair l r => pair (l.rewrite σ) (r.rewrite σ)
  | unit => unit
  | bool b => bool b

inductive UBody (φ : Type _) (ν  : Type _)
   : Type _ where
  | nil : UBody φ ν
  | let1 : ν → UTm φ ν → UBody φ ν → UBody φ ν
  | let2 : ν → ν → UTm φ ν → UBody φ ν → UBody φ ν

def UBody.rename {φ ν ν'}
  (σ : ν → ν') : UBody φ ν → UBody φ ν'
  | nil => nil
  | let1 x e b => let1 (σ x) (e.rename σ) (b.rename σ)
  | let2 x y e b => let2 (σ x) (σ y) (e.rename σ) (b.rename σ)

--TODO: define capture avoiding substitution?
def UBody.rewrite {φ ν}
  (σ : ν → UTm φ ν) : UBody φ ν → UBody φ ν
  | nil => nil
  | let1 x e b => let1 x (e.rewrite σ) (b.rewrite σ)
  | let2 x y e b => let2 x y (e.rewrite σ) (b.rewrite σ)

def UBody.rewrite' {φ ν}
  (σ : ν → ν' ⊕ UTm φ ν') : UBody φ ν → UBody φ ν'
  | nil => nil
  | let1 x e b => match σ x with
    | Sum.inl x' => let1 x' (e.rewrite (λz => (σ z).elim UTm.var id)) (b.rewrite' σ)
    | Sum.inr _ => (b.rewrite' σ)
  | let2 x y e b => match σ x, σ y with
    | Sum.inl x', Sum.inl y'
      => let2 x' y' (e.rewrite (λz => (σ z).elim UTm.var id)) (b.rewrite' σ)
    | _, _ => (b.rewrite' σ)

def UBody.defs {φ ν}
  : UBody φ ν → List ν
  | nil => []
  | let1 x _ b => x :: b.defs
  | let2 x y _ b => x :: y :: b.defs

def UBody.comp {φ ν}
  : UBody φ ν → UBody φ ν → UBody φ ν
  | nil, b => b
  | let1 x e b, b' => let1 x e (b.comp b')
  | let2 x y e b, b' => let2 x y e (b.comp b')

theorem UBody.nil_comp {φ ν} (b : UBody φ ν)
  : UBody.comp UBody.nil b = b := rfl

theorem UBody.comp_nil {φ ν} (b : UBody φ ν)
  : UBody.comp b UBody.nil = b := by induction b <;> simp [UBody.comp, *]

theorem UBody.comp_assoc {φ ν} (b₁ b₂ b₃ : UBody φ ν)
  : UBody.comp (UBody.comp b₁ b₂) b₃ = UBody.comp b₁ (UBody.comp b₂ b₃)
  := by induction b₁ <;> simp [UBody.comp, *]

def UBody.comp_defs {φ ν}
  (b₁ b₂ : UBody φ ν) : (b₁.comp b₂).defs = b₁.defs ++ b₂.defs
  := by induction b₁ <;> simp [defs, comp, *]

def UBody.SSA {φ ν} (Γ : List ν) (b : UBody φ ν) : Prop
  := Γ.Disjoint b.defs ∧ b.defs.Nodup

theorem UBody.SSA.of_let1 {φ ν}
  {Γ : List ν} {x : ν} {e : UTm φ ν} {b : UBody φ ν}
  (h : UBody.SSA Γ (let1 x e b)) : UBody.SSA (x :: Γ) b
  := ⟨
    List.disjoint_cons_left.mpr ⟨h.2.not_mem, (List.disjoint_cons_right.mp h.1).2⟩,
    h.2.of_cons
  ⟩

theorem UBody.SSA.of_let2 {φ ν}
  {Γ : List ν} {x y : ν} {e : UTm φ ν} {b : UBody φ ν}
  (h : UBody.SSA Γ (let2 x y e b)) : UBody.SSA (x :: y :: Γ) b
  := ⟨
    List.disjoint_cons_left.mpr
      ⟨List.not_mem_of_not_mem_cons h.2.not_mem,
        List.disjoint_cons_left.mpr ⟨h.2.of_cons.not_mem,
        (List.disjoint_cons_right.mp (List.disjoint_cons_right.mp h.1).2).2⟩⟩,
    h.2.of_cons.of_cons
  ⟩

theorem UBody.SSA.of_let1' {φ ν}
  {Γ : Ctx ν α} {x : Var ν α} {e : UTm φ ν} {b : UBody φ ν}
  (h : UBody.SSA Γ.names (let1 x.name e b)) : UBody.SSA (Ctx.names (x :: Γ)) b
  := h.of_let1

theorem UBody.SSA.of_let1'' {φ ν}
  {Γ : Ctx ν α} {x A} {e : UTm φ ν} {b : UBody φ ν}
  (h : UBody.SSA Γ.names (let1 x e b)) : UBody.SSA (Ctx.names (⟨x, A⟩ :: Γ)) b
  := h.of_let1

theorem UBody.SSA.of_let2' {φ ν}
  {Γ : Ctx ν α} {x y : Var ν α} {e : UTm φ ν} {b : UBody φ ν}
  (h : UBody.SSA Γ.names (let2 x.name y.name e b)) : UBody.SSA (Ctx.names (x :: y :: Γ)) b
  := h.of_let2

theorem UBody.SSA.of_let2'' {φ ν}
  {Γ : Ctx ν α} {x A y B} {e : UTm φ ν} {b : UBody φ ν}
  (h : UBody.SSA Γ.names (let2 x y e b)) : UBody.SSA (Ctx.names (⟨x, A⟩ :: ⟨y, B⟩ :: Γ)) b
  := h.of_let2

def UBody.NSSA {φ ν}
  (Γ : List ν) (b : UBody φ ν) : Prop
  := (Γ ++ b.defs).Nodup

theorem UBody.NSSA.toSSA {φ ν}
  {Γ : List ν} {b : UBody φ ν} (h : UBody.NSSA Γ b) : UBody.SSA Γ b
  := ⟨List.disjoint_of_nodup_append h, h.of_append_right⟩

theorem UBody.SSA.entry_nodup {φ ν}
  {Γ : List ν} {b : UBody φ ν} (h : UBody.SSA Γ b) (h' : Γ.Nodup) : UBody.NSSA Γ b
  := h'.append h.2 h.1

theorem UBody.SSA.comp {φ ν}
  {Γ : List ν} {b₁ b₂ : UBody φ ν}
  (h₁ : UBody.SSA Γ b₁) (h₂ : UBody.SSA (b₁.defs.reverse ++ Γ) b₂)
  : UBody.SSA Γ (b₁.comp b₂)
  := by
    simp only
      [SSA, List.disjoint_append_left, comp_defs, List.disjoint_append_right,
        List.Disjoint.iff_reverse_left] at *
    exact ⟨⟨h₁.1, h₂.1.2⟩, h₁.2.append h₂.2 h₂.1.1⟩

theorem UBody.NSSA.comp {φ ν}
  {Γ : List ν} {b₁ b₂ : UBody φ ν}
  (h₂ : UBody.NSSA (b₁.defs.reverse ++ Γ) b₂)
  : UBody.NSSA Γ (b₁.comp b₂)
  := by
    simp only [NSSA, List.nodup_append, List.append_assoc, List.nodup_reverse,
      List.disjoint_append_right, List.Disjoint.iff_reverse_left, comp_defs] at *
    exact ⟨h₂.2.1.1, ⟨h₂.1, h₂.2.1.2.1, h₂.2.2.2⟩, h₂.2.2.1.symm, h₂.2.1.2.2⟩

inductive UTerminator (φ : Type _) (ν : Type _) (κ : Type _)
   : Type _ where
  | br : κ → UTm φ ν → UTerminator φ ν κ
  | ite : UTm φ ν → UTerminator φ ν κ → UTerminator φ ν κ → UTerminator φ ν κ

def UTerminator.rename {φ ν ν' κ}
  (σ : ν → ν') : UTerminator φ ν κ → UTerminator φ ν' κ
  | br ℓ e => br ℓ (e.rename σ)
  | ite c t f => ite (c.rename σ) (t.rename σ) (f.rename σ)

def UTerminator.rename_label {φ ν}
  (σ : κ → κ') : UTerminator φ ν κ → UTerminator φ ν κ'
  | br ℓ e => br (σ ℓ) e
  | ite c t f => ite c (t.rename_label σ) (f.rename_label σ)

structure UBB (φ : Type _) (ν : Type _) (κ : Type _)
  : Type _ where
  body : UBody φ ν
  terminator : UTerminator φ ν κ

def UBB.rename {φ ν ν' κ}
  (σ : ν → ν') (β : UBB φ ν κ) : UBB φ ν' κ where
  body := β.body.rename σ
  terminator := β.terminator.rename σ

def UBB.rename_label {φ ν κ κ'}
  (σ : κ → κ') (β : UBB φ ν κ) : UBB φ ν κ' where
  body := β.body
  terminator := β.terminator.rename_label σ

inductive UCFG (φ : Type _) (α : Type _) (ν : Type _) (κ : Type _)
  : Type _ where
  | nil : UCFG φ α ν κ
  | cons : UCFG φ α ν κ → κ → ν → α → UBB φ ν κ → UCFG φ α ν κ

def UCFG.rename {φ α ν ν' κ}
  (σ : ν → ν') : UCFG φ α ν κ → UCFG φ α ν' κ
  | nil => nil
  | cons Φ κ x t b => cons (Φ.rename σ) κ (σ x) t (b.rename σ)

def UCFG.rename_label {φ α ν κ κ'}
  (σ : κ → κ') : UCFG φ α ν κ → UCFG φ α ν κ'
  | nil => nil
  | cons Φ κ x t b => cons (Φ.rename_label σ) (σ κ) x t (b.rename_label σ)

def UCFG.labels {φ α ν κ}
  : UCFG φ α ν κ → List κ
  | nil => []
  | cons Φ κ _ _ _ => κ :: Φ.labels

def UCFG.defs {φ α ν κ}
  : UCFG φ α ν κ → List ν
  | nil => []
  | cons Φ _ x _ _ => x :: Φ.defs

def UCFG.comp {φ α ν κ}
  : UCFG φ α ν κ → UCFG φ α ν κ → UCFG φ α ν κ
  | nil, Φ => Φ
  | cons Φ κ x t b, Φ' => cons (Φ.comp Φ') κ x t b

def UCFG.nil_comp {φ α ν κ} (Φ : UCFG φ α ν κ)
  : UCFG.nil.comp Φ = Φ := rfl

def UCFG.comp_nil {φ α ν κ}
  (Φ : UCFG φ α ν κ) : Φ.comp UCFG.nil = Φ
  := by induction Φ <;> simp [comp, *]

def UCFG.comp_labels {φ α ν κ}
  (Φ Φ' : UCFG φ α ν κ) : (Φ.comp Φ').labels = Φ.labels ++ Φ'.labels
  := by induction Φ <;> simp [labels, comp, *]

def UCFG.comp_defs {φ α ν κ}
  (Φ Φ' : UCFG φ α ν κ) : (Φ.comp Φ').defs = Φ.defs ++ Φ'.defs
  := by induction Φ <;> simp [defs, comp, *]

def UCFG.SSA {φ α ν κ}
  (Γ : List ν) (Φ : UCFG φ α ν κ) : Prop
  := Γ.Disjoint Φ.defs ∧ Φ.defs.Nodup

def UCFG.NSSA {φ α ν κ}
  (Γ : List ν) (Φ : UCFG φ α ν κ) : Prop
  := (Γ ++ Φ.defs).Nodup

def UCFG.NSSA.toSSA {φ α ν κ}
  {Γ : List ν} {Φ : UCFG φ α ν κ} (h : UCFG.NSSA Γ Φ) : UCFG.SSA Γ Φ
  := ⟨List.disjoint_of_nodup_append h, h.of_append_right⟩

def UCFG.SSA.entry_nodup {φ α ν κ}
  {Γ : List ν} {Φ : UCFG φ α ν κ} (h : UCFG.SSA Γ Φ) (h' : Γ.Nodup) : UCFG.NSSA Γ Φ
  := h'.append h.2 h.1

structure URegion (φ : Type _) (α : Type _) (ν : Type _) (κ : Type _)
  : Type _ where
  entry : UBB φ ν κ
  cfg : UCFG φ α ν κ

def URegion.rename {φ α ν ν' κ}
  (σ : ν → ν') (β : URegion φ α ν κ) : URegion φ α ν' κ where
  entry := β.entry.rename σ
  cfg := β.cfg.rename σ

def URegion.rename_label {φ α ν κ κ'}
  (σ : κ → κ') (β : URegion φ α ν κ) : URegion φ α ν κ' where
  entry := β.entry.rename_label σ
  cfg := β.cfg.rename_label σ

inductive UGRegion (φ : Type _) (α : Type _) (ν : Type _) (κ : Type _)
  : Type _ where
  | let1 : ν → UTm φ ν → UGRegion φ α ν κ → UGRegion φ α ν κ
  | let2 : ν → ν → UTm φ ν → UGRegion φ α ν κ → UGRegion φ α ν κ
  | br : κ → UTm φ ν → UGRegion φ α ν κ
  | ite : UTm φ ν → UGRegion φ α ν κ → UGRegion φ α ν κ → UGRegion φ α ν κ
  | dom : UGRegion φ α ν κ → UGRegion φ α ν κ → UGRegion φ α ν κ
  | nil : UGRegion φ α ν κ
  | cons : UGRegion φ α ν κ → κ → ν → α → UGRegion φ α ν κ → UGRegion φ α ν κ

def UGRegion.rename {φ α ν ν' κ}
  (σ : ν → ν') : UGRegion φ α ν κ → UGRegion φ α ν' κ
  | let1 x e b => let1 (σ x) (e.rename σ) (b.rename σ)
  | let2 x y e b => let2 (σ x) (σ y) (e.rename σ) (b.rename σ)
  | br ℓ e => br ℓ (e.rename σ)
  | ite c t f => ite (c.rename σ) (t.rename σ) (f.rename σ)
  | dom d r => dom (d.rename σ) (r.rename σ)
  | nil => nil
  | cons r ℓ x t b => cons (r.rename σ) ℓ (σ x) t (b.rename σ)

def UGRegion.rename_label {φ α ν κ κ'}
  (σ : κ → κ') : UGRegion φ α ν κ → UGRegion φ α ν κ'
  | let1 x e b => let1 x e (b.rename_label σ)
  | let2 x y e b => let2 x y e (b.rename_label σ)
  | br ℓ e => br (σ ℓ) e
  | ite c t f => ite c (t.rename_label σ) (f.rename_label σ)
  | dom d r => dom (d.rename_label σ) (r.rename_label σ)
  | nil => nil
  | cons r ℓ x t b => cons (r.rename_label σ) (σ ℓ) x t (b.rename_label σ)

--TODO: map_ty for UGRegion

def UTerminator.toUGRegion {φ α ν κ}
  (t : UTerminator φ ν κ) : UGRegion φ α ν κ
  := match t with
    | UTerminator.br ℓ e => UGRegion.br ℓ e
    | UTerminator.ite c t f => UGRegion.ite c (t.toUGRegion) (f.toUGRegion)

def UBody.comp_region {φ α ν κ}
  (b : UBody φ ν) (r : UGRegion φ α ν κ) : UGRegion φ α ν κ
  := match b with
    | UBody.nil => r
    | UBody.let1 x e b => UGRegion.let1 x e (b.comp_region r)
    | UBody.let2 x y e b => UGRegion.let2 x y e (b.comp_region r)

def UBB.toUGRegion {φ α ν κ}
  (b : UBB φ ν κ) : UGRegion φ α ν κ
  := b.body.comp_region b.terminator.toUGRegion

def UCFG.toUGRegion {φ α ν κ}
  (Φ : UCFG φ α ν κ) : UGRegion φ α ν κ
  := match Φ with
    | UCFG.nil => UGRegion.nil
    | UCFG.cons Φ κ x t b => UGRegion.cons (Φ.toUGRegion) κ x t (b.toUGRegion)
