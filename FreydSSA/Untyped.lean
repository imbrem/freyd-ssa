import FreydSSA.Ctx
import FreydSSA.InstSet

inductive InstSet.UTm {α : Type v} (Φ : InstSet α) (ν : Type u)
  : Type (max u v) where
  | var : ν → Φ.UTm ν
  | op : Φ.Op p A B → Φ.UTm ν → Φ.UTm ν
  | pair : Φ.UTm ν → Φ.UTm ν → Φ.UTm ν
  | unit : Φ.UTm ν
  | bool : Bool → Φ.UTm ν

def InstSet.UTm.rename {α : Type v} {Φ : InstSet α} {ν ν'}
  (σ : ν → ν') : Φ.UTm ν → Φ.UTm ν'
  | var x => var (σ x)
  | op f e => op f (e.rename σ)
  | pair l r => pair (l.rename σ) (r.rename σ)
  | unit => unit
  | bool b => bool b

def InstSet.UTm.rewrite {α : Type v} {Φ : InstSet α} {ν ν'}
  (σ : ν → Φ.UTm ν') : Φ.UTm ν → Φ.UTm ν'
  | var x => σ x
  | op f e => op f (e.rewrite σ)
  | pair l r => pair (l.rewrite σ) (r.rewrite σ)
  | unit => unit
  | bool b => bool b

inductive InstSet.UBody {α : Type v} (Φ : InstSet α) (ν : Type u)
  : Type (max u v) where
  | nil : Φ.UBody ν
  | let1 : ν → Φ.UTm ν → Φ.UBody ν → Φ.UBody ν
  | let2 : ν → ν → Φ.UTm ν → Φ.UBody ν → Φ.UBody ν

def InstSet.UBody.rename {α : Type v} {Φ : InstSet α} {ν ν'}
  (σ : ν → ν') : Φ.UBody ν → Φ.UBody ν'
  | nil => nil
  | let1 x e b => let1 (σ x) (e.rename σ) (b.rename σ)
  | let2 x y e b => let2 (σ x) (σ y) (e.rename σ) (b.rename σ)

--TODO: define capture avoiding substitution?
def InstSet.UBody.rewrite {α : Type v} {Φ : InstSet α} {ν}
  (σ : ν → Φ.UTm ν) : Φ.UBody ν → Φ.UBody ν
  | nil => nil
  | let1 x e b => let1 x (e.rewrite σ) (b.rewrite σ)
  | let2 x y e b => let2 x y (e.rewrite σ) (b.rewrite σ)

def InstSet.UBody.rewrite' {α : Type v} {Φ : InstSet α} {ν}
  (σ : ν → ν' ⊕ Φ.UTm ν') : Φ.UBody ν → Φ.UBody ν'
  | nil => nil
  | let1 x e b => match σ x with
    | Sum.inl x' => let1 x' (e.rewrite (λz => (σ z).elim UTm.var id)) (b.rewrite' σ)
    | Sum.inr _ => (b.rewrite' σ)
  | let2 x y e b => match σ x, σ y with
    | Sum.inl x', Sum.inl y'
      => let2 x' y' (e.rewrite (λz => (σ z).elim UTm.var id)) (b.rewrite' σ)
    | _, _ => (b.rewrite' σ)

inductive InstSet.UTerminator {α : Type v} (Φ : InstSet α) (ν κ : Type u)
  : Type (max u v) where
  | br : κ → Φ.UTm ν → Φ.UTerminator ν κ
  | ite : Φ.UTm ν → Φ.UTerminator ν κ → Φ.UTerminator ν κ → Φ.UTerminator ν κ

def InstSet.UTerminator.rename {α : Type v} {Φ : InstSet α} {ν ν'}
  (σ : ν → ν') : Φ.UTerminator ν κ → Φ.UTerminator ν' κ
  | br ℓ e => br ℓ (e.rename σ)
  | ite c t f => ite (c.rename σ) (t.rename σ) (f.rename σ)

def InstSet.UTerminator.rename_label {α : Type v} {Φ : InstSet α} {ν}
  (σ : κ → κ') : Φ.UTerminator ν κ → Φ.UTerminator ν κ'
  | br ℓ e => br (σ ℓ) e
  | ite c t f => ite c (t.rename_label σ) (f.rename_label σ)

structure InstSet.UBB {α : Type v} (Φ : InstSet α) (ν κ : Type u)
  : Type (max u v) where
  body : Φ.UBody ν
  terminator : Φ.UTerminator ν κ

def InstSet.UBB.rename {α : Type v} {Φ : InstSet α} {ν ν' κ}
  (σ : ν → ν') (β : Φ.UBB ν κ) : Φ.UBB ν' κ where
  body := β.body.rename σ
  terminator := β.terminator.rename σ

def InstSet.UBB.rename_label {α : Type v} {Φ : InstSet α} {ν κ κ'}
  (σ : κ → κ') (β : Φ.UBB ν κ) : Φ.UBB ν κ' where
  body := β.body
  terminator := β.terminator.rename_label σ

inductive InstSet.UCFG {α : Type v} (Φ : InstSet α) (ν κ : Type u)
  : Type (max u v) where
  | nil : Φ.UCFG ν κ
  | cons : Φ.UCFG ν κ → κ → ν → α → Φ.UBB ν κ → Φ.UCFG ν κ

def InstSet.UCFG.rename {α : Type v} {Φ : InstSet α} {ν ν' κ}
  (σ : ν → ν') : Φ.UCFG ν κ → Φ.UCFG ν' κ
  | nil => nil
  | cons Φ κ x t b => cons (Φ.rename σ) κ (σ x) t (b.rename σ)

def InstSet.UCFG.rename_label {α : Type v} {Φ : InstSet α} {ν κ κ'}
  (σ : κ → κ') : Φ.UCFG ν κ → Φ.UCFG ν κ'
  | nil => nil
  | cons Φ κ x t b => cons (Φ.rename_label σ) (σ κ) x t (b.rename_label σ)

structure InstSet.URegion {α : Type v} (Φ : InstSet α) (ν κ : Type u)
  : Type (max u v) where
  entry : Φ.UBB ν κ
  cfg : Φ.UCFG ν κ

def InstSet.URegion.rename {α : Type v} {Φ : InstSet α} {ν ν' κ}
  (σ : ν → ν') (β : Φ.URegion ν κ) : Φ.URegion ν' κ where
  entry := β.entry.rename σ
  cfg := β.cfg.rename σ

def InstSet.URegion.rename_label {α : Type v} {Φ : InstSet α} {ν κ κ'}
  (σ : κ → κ') (β : Φ.URegion ν κ) : Φ.URegion ν κ' where
  entry := β.entry.rename_label σ
  cfg := β.cfg.rename_label σ

inductive InstSet.UGRegion {α : Type v} (Φ : InstSet α) (ν κ : Type u)
  : Type (max u v) where
  | br : Φ.UTm ν → List ν → Φ.UGRegion ν κ
  | ite : Φ.UTm ν → Φ.UGRegion ν κ → Φ.UGRegion ν κ → Φ.UGRegion ν κ
  | dom : Φ.UGRegion ν κ → Φ.UGRegion ν κ → Φ.UGRegion ν κ
  | nil : Φ.UGRegion ν κ
  | cons : Φ.UGRegion ν κ → κ → ν → α → Φ.UBB ν κ → Φ.UGRegion ν κ

def InstSet.UGRegion.rename {α : Type v} {Φ : InstSet α} {ν ν' κ}
  (σ : ν → ν') : Φ.UGRegion ν κ → Φ.UGRegion ν' κ
  | br e xs => br (e.rename σ) (xs.map σ)
  | ite c t f => ite (c.rename σ) (t.rename σ) (f.rename σ)
  | dom d r => dom (d.rename σ) (r.rename σ)
  | nil => nil
  | cons r ℓ x t b => cons (r.rename σ) ℓ (σ x) t (b.rename σ)

def InstSet.UGRegion.rename_label {α : Type v} {Φ : InstSet α} {ν κ κ'}
  (σ : κ → κ') : Φ.UGRegion ν κ → Φ.UGRegion ν κ'
  | br e xs => br e xs
  | ite c t f => ite c (t.rename_label σ) (f.rename_label σ)
  | dom d r => dom (d.rename_label σ) (r.rename_label σ)
  | nil => nil
  | cons r ℓ x t b => cons (r.rename_label σ) (σ ℓ) x t (b.rename_label σ)
