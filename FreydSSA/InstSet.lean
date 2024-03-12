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
