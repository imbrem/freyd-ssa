import FreydSSA.Term.Extrinsic.Basic

inductive InstSet.USubst [Φ : InstSet φ (Ty α)] (σ : ν → UTm φ ν)
  : Ctx ν (Ty α) → Ctx ν (Ty α) → Type _
| nil (Γ) : Φ.USubst σ Γ []
| cons {Γ Δ} :
  (σ x).Wf 1 Γ A →
  Φ.USubst σ Γ Δ →
  Φ.USubst σ Γ (⟨x, A⟩::Δ)

def InstSet.USubst.fromTuple [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)}
  (f: (i : Fin Δ.length) → (σ (Δ.get i).name).Wf 1 Γ (Δ.get i).ty) : Φ.USubst σ Γ Δ
  := match Δ with
  | [] => nil _
  | v::Δ => cons (f ⟨0, by simp⟩) (fromTuple (λi => f i.succ))

def InstSet.USubst.get [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)}
  : Φ.USubst σ Γ Δ → (i : Fin Δ.length) → (σ (Δ.get i).name).Wf 1 Γ (Δ.get i).ty
  | cons e _, ⟨0, _⟩ => e
  | cons _ σ, ⟨n + 1, hn⟩ => σ.get ⟨n, Nat.lt_of_succ_lt_succ hn⟩

theorem InstSet.USubst.fromTuple_get [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)}
  : (hσ : Φ.USubst σ Γ Δ) → fromTuple (hσ.get) = hσ
  | nil _ => rfl
  | cons e hσ => by
    simp only [fromTuple, get, Fin.succ]
    rw [<-fromTuple_get hσ]
    congr
    funext i
    rw [fromTuple_get hσ]
    rfl

theorem InstSet.USubst.get_fromTuple [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)}
  {σ : ν → UTm φ ν}
  (hσ : (i : Fin Δ.length) → (σ (Δ.get i).name).Wf 1 Γ (Δ.get i).ty) : get (fromTuple hσ) = hσ
  := by induction Δ with
  | nil => funext i; nomatch i
  | cons v Δ I =>
    funext ⟨i, hi⟩
    cases i <;> simp only [fromTuple, get, Fin.succ, *]
