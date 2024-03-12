import Mathlib.Data.List.Basic
import Mathlib.Data.List.DropRight
import Std.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Init.Classical

import FreydSSA.Ctx
import FreydSSA.InstSet
import FreydSSA.Tm

inductive InstSet.Subst (Φ : InstSet (Ty α)) : Ctx ν (Ty α) → Ctx ν (Ty α) → Type _
| nil (Γ) : Subst Φ Γ []
| cons {Γ Δ} :
  Φ.Tm 1 Γ A →
  Subst Φ Γ Δ →
  Subst Φ Γ (⟨x, A⟩::Δ)

def InstSet.Subst.fromTuple {Φ : InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)}
  (f: (i : Fin Δ.length) → Φ.Tm 1 Γ (Δ.get i).ty) : Φ.Subst Γ Δ
  := match Δ with
  | [] => nil _
  | v::Δ => cons (f ⟨0, by simp⟩) (fromTuple (λi => f i.succ))

def InstSet.Subst.get {Φ : InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)}
  : Φ.Subst Γ Δ → (i : Fin Δ.length) → Φ.Tm 1 Γ (Δ.get i).ty
  | cons e _, ⟨0, _⟩ => e
  | cons _ σ, ⟨n + 1, hn⟩ => σ.get ⟨n, Nat.lt_of_succ_lt_succ hn⟩

theorem InstSet.Subst.fromTuple_get {Φ : InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)}
  : (σ : Φ.Subst Γ Δ) → fromTuple (σ.get) = σ
  | nil _ => rfl
  | cons e σ => by simp only [fromTuple, get, Fin.succ, fromTuple_get σ]

theorem InstSet.Subst.get_fromTuple {Φ : InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)}
  (σ : (i : Fin Δ.length) → Φ.Tm 1 Γ (Δ.get i).ty) : get (fromTuple σ) = σ
  := by induction Δ with
  | nil => funext i; nomatch i
  | cons v Δ I =>
    funext ⟨i, hi⟩
    cases i <;> simp only [fromTuple, get, Fin.succ, *]

theorem InstSet.Subst.ext {Φ : InstSet (Ty α)} {Γ Δ : Ctx ν (Ty α)}
  (σ τ : Φ.Subst Γ Δ)
  (h : (i : Fin Δ.length) → σ.get i = τ.get i)
  : σ = τ
  := by rw [<-fromTuple_get σ, <-fromTuple_get τ]; congr; apply funext; apply h

def InstSet.Subst.wk_entry {Φ : InstSet (Ty α)}
  {Γ Δ Ξ : Ctx ν (Ty α)} (w: Γ.Wk Δ) : Φ.Subst Δ Ξ → Φ.Subst Γ Ξ
  | nil _ => nil _
  | cons e σ => cons (e.wk w) (σ.wk_entry w)

def InstSet.Subst.wk_exit {Φ : InstSet (Ty α)}
  {Γ Δ Ξ : Ctx ν (Ty α)} : Φ.Subst Γ Δ → Δ.Wk Ξ → Φ.Subst Γ Ξ
  | nil _, Ctx.Wk.nil => nil _
  | cons e σ, Ctx.Wk.cons _ w  => cons e (σ.wk_exit w)
  | cons _ σ, Ctx.Wk.skip _ w  => σ.wk_exit w

def InstSet.Subst.var {Φ : InstSet (Ty α)}
  {Γ Δ : Ctx ν (Ty α)} (σ : Φ.Subst Γ Δ) (hx : Δ.Wk [⟨x, A⟩])
  : Φ.Tm 1 Γ A := match σ.wk_exit hx with
  | cons e _ => e

def InstSet.Tm.subst {Φ : InstSet (Ty α)} {p : Purity}
  {Γ Δ : Ctx ν (Ty α)} {A : Ty α} (σ : Φ.Subst Γ Δ)
  : Φ.Tm p Δ A → Φ.Tm p Γ A
  | var _ w => σ.var w
  | op f e => op f (e.subst σ)
  | pair p l r => pair p (l.subst σ) (r.subst σ)
  | unit p => unit p
  | bool p b => bool p b

def InstSet.Subst.comp {Φ : InstSet (Ty α)}
  {Γ Δ Ξ : Ctx ν (Ty α)} (σ: Φ.Subst Γ Δ) : Φ.Subst Δ Ξ → Φ.Subst Γ Ξ
  | nil _ => nil _
  | cons e τ => cons (e.subst σ) (σ.comp τ)

theorem InstSet.Subst.comp_nil {Φ : InstSet (Ty α)}
  {Γ Δ : Ctx ν (Ty α)} (σ: Φ.Subst Γ Δ)
  : σ.comp (nil _) = nil _
  := rfl

theorem InstSet.Tm.subst_nil' {Φ: InstSet (Ty α)} {p : Purity} {A : Ty α}
  {Γ : Ctx ν (Ty α)}
  {σ : Φ.Subst Γ Γ}
  (hΓ : Γ = [])
  (t : Φ.Tm p Γ A) : t.subst σ = t := by induction t with
  | var _ w => cases hΓ; cases w
  | _ => simp [subst, *]

theorem InstSet.Tm.subst_nil {Φ: InstSet (Ty α)} {p : Purity} {A : Ty α}
  {σ : Φ.Subst (@List.nil (Var ν _)) []}
  (t : Φ.Tm p [] A) : t.subst σ = t
  := subst_nil' rfl t

theorem InstSet.Subst.nil_comp {Φ : InstSet (Ty α)}
  {Γ : Ctx ν (Ty α)}
  : (σ: Φ.Subst [] Γ) → (nil _).comp σ = σ
  | nil _ => rfl
  | cons e σ => by simp [comp, σ.nil_comp, Tm.subst_nil]

def InstSet.Subst.id {Φ : InstSet (Ty α)}
  {Γ : Ctx ν (Ty α)} (h : Γ.Nodup) : Φ.Subst Γ Γ
  := fromTuple (λi => Tm.var 1 (h.get i))

def InstSet.Subst.ofWk {Φ : InstSet (Ty α)}
  {Γ Δ : Ctx ν (Ty α)} (w : Γ.Wk Δ) (hΔ : Δ.Nodup) : Φ.Subst Γ Δ
  := fromTuple (λi => Tm.var 1 (w.comp (hΔ.get i)))

def InstSet.Subst.cons2 {Φ : InstSet (Ty α)}
  {Γ Δ : Ctx ν (Ty α)} {x : Var ν (Ty α)} (σ : Φ.Subst Γ Δ) (hx : Γ.Fresh x.name)
  : Φ.Subst (x::Γ) (x::Δ)
  := (σ.wk_entry (Ctx.Wk.skip hx (Ctx.Wk.refl Γ))).cons (Tm.var 1 (Ctx.Wk.head _ _))

def InstSet.Subst.cons2' {Φ : InstSet (Ty α)}
  {Γ Δ : Ctx ν (Ty α)} {x : Var ν (Ty α)} (σ : Φ.Subst Γ Δ) (hx : x.name ∉ Γ.names)
  : Φ.Subst (x::Γ) (x::Δ)
  := (σ.wk_entry (Ctx.Wk.skip (Ctx.Fresh.of_not_mem_names hx) (Ctx.Wk.refl Γ))).cons
    (Tm.var 1 (Ctx.Wk.head _ _))

theorem InstSet.Subst.ofWk_refl {Φ : InstSet (Ty α)}
  {Γ : Ctx ν (Ty α)} (hΓ : Γ.Nodup)
  : @ofWk _ _ Φ _ _ (Ctx.Wk.refl Γ) hΓ = Subst.id hΓ
  := by simp only [id, ofWk]; congr; funext i; congr; apply Ctx.Wk.allEq

-- theorem InstSet.Subst.wk_comp_wk {Φ : InstSet (Ty α)}
--   {Γ Δ Ξ : Ctx ν (Ty α)} (w : Γ.Wk Δ) (w' : Δ.Wk Ξ) (hΔ : Δ.Nodup)
--   : (@ofWk _ _ Φ _ _ w hΔ).comp (ofWk w' (hΔ.wk w')) = (ofWk (w.comp w') sorry)
--   := by induction w with
--   | nil => cases w'; rfl
--   | cons v w I => cases w' with
--     | cons _ w' => simp [comp, ofWk, fromTuple, Tm.subst]
--     | skip hx w' => sorry
--   | skip hx w I => sorry

-- theorem InstSet.Subst.comp_wk {Φ : InstSet (Ty α)}
--   {Γ Δ Ξ : Ctx ν (Ty α)} (σ : Φ.Subst Γ Δ) (w : Δ.Wk Ξ) (hΞ : Ξ.Nodup)
--   : σ.comp (ofWk w hΞ) = σ.wk_exit w
--   := by induction w with
--   | nil => cases σ; rfl
--   | cons v w I => cases σ with
--     | cons e σ =>
--       rw [wk_exit, <-I _ hΞ.of_cons]
--       apply ext
--       intro ⟨i, hi⟩
--       sorry
--   | skip hx w I => sorry

--TODO: Subst.comp_wk, Subst.wk_comp, Subst.wk_comp_wk, etc. for _Nodup_...

--TODO: Subst.comp_id, Tm.subst_id

-- def InstSet.Tm.subst_comp {Φ : InstSet (Ty α)} {p : Purity}
--   {Γ Δ Ξ : Ctx ν (Ty α)} {A : Ty α} (σ : Φ.Subst Γ Δ) (τ : Φ.Subst Δ Ξ)
--   (t : Φ.Tm p Ξ A)
--   : (t.subst τ).subst σ = t.subst (σ.comp τ)
--   := by induction t with
--   | var p w => cases p with
--     | pure => simp [subst]; sorry
--     | impure => simp [subst]; sorry
--   | _ => simp [subst, *]

-- theorem InstSet.Subst.comp_assoc {Φ : InstSet (Ty α)}
--   {Γ Δ Ξ Ω : Ctx ν (Ty α)} (σ: Φ.Subst Γ Δ) (τ: Φ.Subst Δ Ξ) (υ: Φ.Subst Ξ Ω)
--   : (σ.comp τ).comp υ = σ.comp (τ.comp υ)
--   := by induction υ with
--   | nil _ => simp [comp]
--   | cons e υ I =>
--     simp [comp, I]
--     sorry

--TODO: Subst.Iso for alpha conversion...

--TODO: Isomorphic substitutions for the same input/output contexts are equal

--TODO: Isomorphic terms can be substituted for each other

--TODO: Substitution for bodies, terminators, blocks, CFGs, regions, and generalized regions
