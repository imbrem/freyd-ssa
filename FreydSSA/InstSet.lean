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
