import FreydSSA.Ctx
import FreydSSA.InstSet

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
  | br : κ → UTm φ ν → UGRegion φ α ν κ
  | ite : UTm φ ν → UGRegion φ α ν κ → UGRegion φ α ν κ → UGRegion φ α ν κ
  | dom : UGRegion φ α ν κ → UGRegion φ α ν κ → UGRegion φ α ν κ
  | nil : UGRegion φ α ν κ
  | cons : UGRegion φ α ν κ → κ → ν → α → UGRegion φ α ν κ → UGRegion φ α ν κ

def UGRegion.rename {φ α ν ν' κ}
  (σ : ν → ν') : UGRegion φ α ν κ → UGRegion φ α ν' κ
  | br ℓ e => br ℓ (e.rename σ)
  | ite c t f => ite (c.rename σ) (t.rename σ) (f.rename σ)
  | dom d r => dom (d.rename σ) (r.rename σ)
  | nil => nil
  | cons r ℓ x t b => cons (r.rename σ) ℓ (σ x) t (b.rename σ)

def UGRegion.rename_label {φ α ν κ κ'}
  (σ : κ → κ') : UGRegion φ α ν κ → UGRegion φ α ν κ'
  | br ℓ e => br (σ ℓ) e
  | ite c t f => ite c (t.rename_label σ) (f.rename_label σ)
  | dom d r => dom (d.rename_label σ) (r.rename_label σ)
  | nil => nil
  | cons r ℓ x t b => cons (r.rename_label σ) (σ ℓ) x t (b.rename_label σ)

--TODO: map_ty for UGRegion
