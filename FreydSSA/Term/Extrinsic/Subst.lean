import FreydSSA.Term.Extrinsic.Basic

variable {φ ν α} [Φ : InstSet φ (Ty α)] [Φc : CohInstSet φ (Ty α)]

inductive InstSet.USubst [Φ : InstSet φ (Ty α)] (σ : ν → UTm φ ν)
  : Ctx ν (Ty α) → Ctx ν (Ty α) → Type _
| nil (Γ) : Φ.USubst σ Γ []
| cons {Γ Δ} :
  (σ x).Wf 1 Γ A →
  Φ.USubst σ Γ Δ →
  Φ.USubst σ Γ (⟨x, A⟩::Δ)

theorem InstSet.USubst.allEq {Γ Δ : Ctx ν (Ty α)} {σ}
  : (hσ hσ' : Φ.USubst σ Γ Δ) → hσ = hσ'
  | nil _, nil _ => rfl
  | cons e hσ, cons e' hσ' => by
    rw [InstSet.USubst.allEq hσ hσ']
    congr
    exact UTm.Wf.allEq e e'

def InstSet.USubst.fromTuple {Γ Δ : Ctx ν (Ty α)}
  (f: (i : Fin Δ.length) → (σ (Δ.get i).name).Wf 1 Γ (Δ.get i).ty) : Φ.USubst σ Γ Δ
  := match Δ with
  | [] => nil _
  | v::Δ => cons (f ⟨0, by simp⟩) (fromTuple (λi => f i.succ))

def InstSet.USubst.get {Γ Δ : Ctx ν (Ty α)}
  : Φ.USubst σ Γ Δ → (i : Fin Δ.length) → (σ (Δ.get i).name).Wf 1 Γ (Δ.get i).ty
  | cons e _, ⟨0, _⟩ => e
  | cons _ σ, ⟨n + 1, hn⟩ => σ.get ⟨n, Nat.lt_of_succ_lt_succ hn⟩

theorem InstSet.USubst.fromTuple_get {Γ Δ : Ctx ν (Ty α)}
  : (hσ : Φ.USubst σ Γ Δ) → fromTuple (hσ.get) = hσ
  | nil _ => rfl
  | cons e hσ => by
    simp only [fromTuple, get, Fin.succ]
    rw [<-fromTuple_get hσ]
    congr
    funext i
    rw [fromTuple_get hσ]
    rfl

theorem InstSet.USubst.get_fromTuple {Γ Δ : Ctx ν (Ty α)}
  {σ : ν → UTm φ ν}
  (hσ : (i : Fin Δ.length) → (σ (Δ.get i).name).Wf 1 Γ (Δ.get i).ty) : get (fromTuple hσ) = hσ
  := by induction Δ with
  | nil => funext i; nomatch i
  | cons v Δ I =>
    funext ⟨i, hi⟩
    cases i <;> simp only [fromTuple, get, Fin.succ, *]

def InstSet.USubst.wk_entry {Γ Γ' Δ : Ctx ν (Ty α)} {σ}
  : Γ'.Wk Γ → Φ.USubst σ Γ Δ → Φ.USubst σ Γ' Δ
  | _, nil _ => nil _
  | w, cons e hσ => cons (e.wk w) (wk_entry w hσ)

def InstSet.USubst.wk_exit {Γ Δ Δ' : Ctx ν (Ty α)} {σ}
  : Φ.USubst σ Γ Δ → Δ.Wk Δ' → Φ.USubst σ Γ Δ'
  | nil _, Ctx.Wk.nil => nil _
  | cons _ hσ, Ctx.Wk.skip _ w => hσ.wk_exit w
  | cons e hσ, Ctx.Wk.cons _ w => cons e (hσ.wk_exit w)

def InstSet.USubst.tensor {Γ Δ : Ctx ν (Ty α)} {σ}
  (hx : x.name ∉ Γ.names)
  (hx' : σ x.name = UTm.var x.name)
  (hσ : Φ.USubst σ Γ Δ) : Φ.USubst σ (x::Γ) (x::Δ)
  := cons
    (hx' ▸ (UTm.Wf.var _ (Ctx.Wk.head _ _)))
    (hσ.wk_entry (Ctx.Wk.skip (Ctx.Fresh.of_not_mem_names hx) (Ctx.Wk.refl _)))

def UTm.Wf.subst {σ : ν → UTm φ ν} {Γ Δ : Ctx ν (Ty α)}
  {e : UTm φ ν} (hσ : Φ.USubst σ Γ Δ) : e.Wf p Δ A → (e.rewrite σ).Wf p Γ A
  | var x w => match hσ.wk_exit w with | InstSet.USubst.cons e _ => e.of_pure
  | op f e => op f (e.subst hσ)
  | pair p l r => pair p (l.subst hσ) (r.subst hσ)
  | unit p => unit p
  | bool p b => bool p b

def InstSet.USubst.wk_meet {Γ₁ Γ₂ Γ Δ : Ctx ν (Ty α)} {σ}
  (w : Γ.Wk Γ₁) (w' : Γ.Wk Γ₂)
  : Φ.USubst σ Γ₁ Δ → Φ.USubst σ Γ₂ Δ → Φ.USubst σ (w.meet w') Δ
  | nil _, nil _ => nil _
  | cons e hσ, cons e' hσ' => cons (e.wk_meet w w' e') (wk_meet w w' hσ hσ')
