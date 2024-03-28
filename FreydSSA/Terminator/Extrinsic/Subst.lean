import FreydSSA.Terminator.Extrinsic.Basic
import FreydSSA.Term.Extrinsic.Subst

--TODO: reroot USubst et all to be part of _context_...
--TODO: make inductives nicer?

variable {φ ν α} [Φ : InstSet φ (Ty α)] [Φc : CohInstSet φ (Ty α)]

def Ctx.Subst.src {σ : ν → UTm φ ν} {Γ Δ : Ctx ν (Ty α)}  (_ : Subst σ Γ Δ)
  : Ctx ν (Ty α) := Γ

def Ctx.Subst.trg {σ : ν → UTm φ ν} {Γ Δ : Ctx ν (Ty α)}  (_ : Subst σ Γ Δ)
  : Ctx ν (Ty α) := Δ

inductive LCtx.Subst (σ : ν → UTm φ ν)
  : LCtx ν κ (Ty α) → LCtx ν κ (Ty α) → Type _
  | nil : Subst σ [] []
  | cons (n A) : Γ.Subst σ Δ → Subst σ L K → Subst σ (⟨n, A, Γ⟩ :: L) (⟨n, A, Δ⟩ :: K)
  | skip : L.Fresh ℓ.name → Subst σ L K → Subst σ L (ℓ :: K)

def LCtx.Subst.ofEmpty
  (σ : ν → UTm φ ν)
  {L : LCtx ν κ (Ty α)}
  : (LCtx.Wk [] L) → Subst σ [] L
  | LCtx.Wk.nil => nil
  | LCtx.Wk.skip hℓ w => skip hℓ (ofEmpty σ w)

def LCtx.Subst.ofVar {σ : ν → UTm φ ν}
  {Γ Δ : Ctx ν (Ty α)} {n A} (hσ : Γ.Subst σ Δ)
  : {L : LCtx ν κ (Ty α)} → LCtx.Wk [⟨n, A, Δ⟩] L → Subst σ [⟨n, A, Γ⟩] L
  | ⟨_, _, _Δ'⟩::_, LCtx.Wk.cons ⟨rfl, rfl, wΔ⟩ w => cons _ _ (hσ.wk_exit wΔ) (ofEmpty σ w)
  | _::_, LCtx.Wk.skip hℓ w => skip (LCtx.Fresh.of_not_mem hℓ.not_mem) (ofVar hσ w)

theorem LCtx.Fresh.subst {σ : ν → UTm φ ν} {L K : LCtx ν κ (Ty α)}
  : Subst σ L K → K.Fresh ℓ → L.Fresh ℓ
  | Subst.nil, nil => nil
  | Subst.cons _ _ _ hσL, cons h f => cons h (subst hσL f)
  | Subst.skip _ hσL, cons h' f => subst hσL f

def LCtx.Subst.wk_exit {σ : ν → UTm φ ν} {L K K' : LCtx ν κ (Ty α)}
  : Subst σ L K → LCtx.Wk K K' → Subst σ L K'
  | nil, LCtx.Wk.nil => nil
  | cons n A h hσ, @LCtx.Wk.cons _ _ _ _ _ ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨hn, hp, w⟩ w'
    => by cases hn; cases hp; exact cons n A (h.wk_exit w) (wk_exit hσ w')
  | skip h hσ, LCtx.Wk.cons hℓ w' => skip (hℓ.name ▸ h) (wk_exit hσ w')
  | hσ, LCtx.Wk.skip h' w => skip (h'.subst hσ) (wk_exit hσ w)

theorem LCtx.Subst.allEq {σ : ν → UTm φ ν} {L K : LCtx ν κ (Ty α)}
  : (hσ hσ': Subst σ L K) → hσ = hσ'
  | nil, nil => rfl
  | cons n A h hσ, cons _ _ h' hσ' => by
    cases h.allEq h'
    cases hσ.allEq hσ'
    rfl
  | skip _ hσ, skip _ hσ' => by
    cases hσ.allEq hσ'
    rfl
  | cons _ _ _ _, skip h _ => (h.head rfl).elim
  | skip h _, cons _ _ _ _ => (h.head rfl).elim

inductive LCtx.PSubst [Φ : InstSet φ (Ty α)] (σ : ν → UTm φ ν)
  : LCtx ν κ (Ty α) → LCtx ν κ (Ty α) → Type _
  | nil : PSubst σ [] []
  | cons (n A) : Γ.Subst σ Δ → PSubst σ L K → PSubst σ (⟨n, A, Γ⟩ :: L) (⟨n, A, Δ⟩ :: K)

theorem LCtx.PSubst.allEq {σ : ν → UTm φ ν} {L K : LCtx ν κ (Ty α)}
  : (hσ  hσ': PSubst σ L K) → hσ = hσ'
  | nil, nil => rfl
  | cons n A h hσ, cons _ _ h' hσ' => by
    cases h.allEq h'
    cases hσ.allEq hσ'
    rfl

def LCtx.PSubst.pwk_exit {σ : ν → UTm φ ν} {L K K' : LCtx ν κ (Ty α)}
  : PSubst σ L K → LCtx.PWk K K' → PSubst σ L K'
  | nil, LCtx.PWk.nil => nil
  | cons n A h hσ, @LCtx.PWk.cons _ _ _ _ _ ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨hn, hp, w'⟩ w =>
    by cases hn; cases hp; exact cons n A (h.wk_exit w') (hσ.pwk_exit w)

def LCtx.PSubst.toSubst {σ : ν → UTm φ ν} {L K : LCtx ν κ (Ty α)}
  : PSubst σ L K → Subst σ L K
  | nil => Subst.nil
  | cons n A h hσ => Subst.cons n A h (toSubst hσ)

theorem LCtx.Fresh.psubst {σ : ν → UTm φ ν} {L K : LCtx ν κ (Ty α)}
  : PSubst σ L K → K.Fresh ℓ → L.Fresh ℓ
  | PSubst.nil, nil => nil
  | PSubst.cons _ _ _ hσL, cons h f => cons h (psubst hσL f)

theorem LCtx.Fresh.psubst_r {σ : ν → UTm φ ν} {L K : LCtx ν κ (Ty α)}
  : PSubst σ L K → L.Fresh ℓ → K.Fresh ℓ
  | PSubst.nil, nil => nil
  | PSubst.cons _ _ _ hσL, cons h f => cons h (psubst_r hσL f)

def LCtx.PSubst.antiSJoin {σ : ν → UTm φ ν}
  {Γ : Ctx ν (Ty α)} {L K M L' K' : LCtx ν κ (Ty α)}
  : PSubst σ L' L → PSubst σ K' K → L.SJoin K M
    → Γ.LEq L' → Γ.LEq K'
    → (M' : LCtx ν κ (Ty α)) ×' L'.SJoin K' M' × PSubst σ M' M
  | nil, nil, LCtx.SJoin.nil => λ_ _ => ⟨[], LCtx.SJoin.nil, nil⟩
  | cons n A hσ hσL, hσK, LCtx.SJoin.left h j => λhL hK =>
    let j' := antiSJoin hσL hσK j hL.tail hK;
    ⟨_, j'.2.1.left (h.psubst hσK), j'.2.2.cons _ _ hσ⟩
  | hσL, cons n A hσ' hσK, LCtx.SJoin.right h j => λhL hK =>
    let j' := antiSJoin hσL hσK j hL hK.tail;
    ⟨_, j'.2.1.right (h.psubst hσL), j'.2.2.cons _ _ hσ'⟩
  | cons n A _ hσL, cons _ _ hσ' hσK, LCtx.SJoin.both _ j => λhL hK  =>
    let j' := antiSJoin hσL hσK j hL.tail hK.tail;
    have hΓ := hL.head.symm.trans hK.head;
    ⟨_, (by cases hΓ; exact j'.2.1.both _), j'.2.2.cons _ _ hσ'⟩

def UTerminator.WfM.subst {t : UTerminator φ ν κ}
  {σ : ν → UTm φ ν}
  (hσ : Γ.Subst σ Δ)
  : t.WfM Δ K → (L : LCtx ν κ (Ty α)) ×' (t.rewrite σ).WfM Γ L × L.PSubst σ K
  | br ℓ de => ⟨_, br ℓ (de.subst hσ), LCtx.PSubst.nil.cons _ _ hσ⟩
  | ite dc dt df j =>
    let ⟨_, dt', hLt⟩ := subst hσ dt;
    let ⟨_, df', hLf⟩ := subst hσ df;
    let ⟨L, j', hL⟩ := hLt.antiSJoin hLf j dt'.lEq df'.lEq;
    ⟨L, ite (dc.subst hσ) dt' df' j', hL⟩

structure LCtx.Subst' [Φ : InstSet φ (Ty α)]
  (σ : ν → UTm φ ν) (L K : LCtx ν κ (Ty α)) where
  mapped : LCtx ν κ (Ty α)
  pSubst : PSubst σ L mapped
  wk : mapped.EWk K

def LCtx.Subst.factor [Φ : InstSet φ (Ty α)]
  {σ : ν → UTm φ ν} {L K : LCtx ν κ (Ty α)}
  : Subst σ L K → Subst' σ L K
  | nil => ⟨[], PSubst.nil, LCtx.EWk.nil⟩
  | cons n A hσ' hσL =>
    let hσL' := factor hσL;
    ⟨_, hσL'.pSubst.cons n A hσ', hσL'.wk.cons _⟩
  | skip h hσL =>
    let hσL' := factor hσL;
    ⟨_, hσL'.pSubst, hσL'.wk.skip (h.psubst_r hσL'.pSubst)⟩

def LCtx.Subst'.toSubst [Φ : InstSet φ (Ty α)]
  {σ : ν → UTm φ ν} {L K : LCtx ν κ (Ty α)}
  (hσ : Subst' σ L K) : Subst σ L K
  := hσ.pSubst.toSubst.wk_exit hσ.wk.toWk

--TODO: USubstL'.allEq...

def UTerminator.Wf'.subst
  {t : UTerminator φ ν κ}
  (hσ : Γ.Subst σ Δ)
  (dt : t.Wf' Δ K) : (L : LCtx ν κ (Ty α)) ×' (t.rewrite σ).Wf' Γ L × L.Subst' σ K :=
  let dt' := dt.wfM.subst hσ;
  let wk' := dt.wk.factor
  ⟨_, dt'.2.1.toWf', ⟨_, dt'.2.2.pwk_exit wk'.pWk, wk'.eWk⟩⟩

def UTerminator.Wf.subst
  {t : UTerminator φ ν κ}
  (hσ : Γ.Subst σ Δ)
  (dt : t.Wf Δ K) : (L : LCtx ν κ (Ty α)) ×' (t.rewrite σ).Wf Γ L × L.Subst σ K :=
  let dt' := dt.factor.subst hσ;
  ⟨dt'.1, dt'.2.1.toWf, dt'.2.2.toSubst⟩
