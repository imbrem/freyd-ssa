inductive Ty (α: Type u): Type u where
  | base (a : α)
  | pair (a b : Ty α)
  | unit
  | bool

inductive Purity
  | pure
  | impure

-- TODO: think about this annotation
@[reducible]
instance : OfNat Purity 0 where
  ofNat := Purity.impure

@[reducible]
instance : OfNat Purity 1 where
  ofNat := Purity.pure

class InstSet (φ: Type u) (α : Type v) : Type _ where
  Op : φ → Purity → α → α → Prop
  pure_to_impure : Op f 1 A B → Op f 0 A B

def InstSet.to_impure [InstSet φ α] {p} {f : φ} {A B : α}
  (h : Op f p A B) : Op f 0 A B
  := match p with
  | Purity.pure => pure_to_impure h
  | Purity.impure => h

def InstSet.from_pure [InstSet φ α] {p} {f : φ} {A B : α}
  (h : Op f 1 A B) : Op f p A B
  := match p with
  | Purity.pure => h
  | Purity.impure => pure_to_impure h

open InstSet

class CohInstSet (φ α) [InstSet φ α] : Type _ where
  coh_trg {f : φ} {A B B' : α} : Op f p A B → Op f p' A B' → B = B'

def CohInstSet.coh_trg' [InstSet φ α] [CohInstSet φ α] {f : φ} {A B A' B' : α}
  (h : Op f p A B) (h' : Op f p' A' B') (h'' : A = A') : B = B'
  := CohInstSet.coh_trg h (h''.symm ▸ h')
