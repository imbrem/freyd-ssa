import FreydSSA.Terminator.Extrinsic.Basic
import FreydSSA.Term.Extrinsic.Subst

--TODO: reroot USubst et all to be part of _context_...
--TODO: make inductives nicer?

variable {φ ν α} [Φ : InstSet φ (Ty α)] [Φc : CohInstSet φ (Ty α)]

def InstSet.USubst.src {σ : ν → UTm φ ν} {Γ Δ : Ctx ν (Ty α)}  (_ : Φ.USubst σ Γ Δ)
  : Ctx ν (Ty α) := Γ

def InstSet.USubst.trg {σ : ν → UTm φ ν} {Γ Δ : Ctx ν (Ty α)}  (_ : Φ.USubst σ Γ Δ)
  : Ctx ν (Ty α) := Δ

inductive InstSet.USubstL (σ : ν → UTm φ ν)
  : LCtx ν κ (Ty α) → LCtx ν κ (Ty α) → Type _
  | nil : USubstL σ [] []
  | cons (n A) : USubst σ Γ Δ → USubstL σ L K → USubstL σ (⟨n, A, Γ⟩ :: L) (⟨n, A, Δ⟩ :: K)
  | skip : L.Fresh ℓ.name → USubstL σ L K → USubstL σ L (ℓ :: K)

def InstSet.USubstL.ofEmpty
  (σ : ν → UTm φ ν)
  {L : LCtx ν κ (Ty α)}
  : (LCtx.Wk [] L) → USubstL σ [] L
  | LCtx.Wk.nil => nil
  | LCtx.Wk.skip hℓ w => skip hℓ (ofEmpty σ w)

def InstSet.USubstL.ofVar {σ : ν → UTm φ ν}
  {Γ Δ : Ctx ν (Ty α)}
  {n A}
  (hσ : USubst σ Γ Δ)
  : {L : LCtx ν κ (Ty α)} → LCtx.Wk [⟨n, A, Δ⟩] L → USubstL σ [⟨n, A, Γ⟩] L
  | ⟨_, _, _Δ'⟩::_, LCtx.Wk.cons ⟨rfl, rfl, wΔ⟩ w => cons _ _ (hσ.wk_exit wΔ) (ofEmpty σ w)
  | _::_, LCtx.Wk.skip hℓ w => skip (LCtx.Fresh.of_not_mem hℓ.not_mem) (ofVar hσ w)

theorem LCtx.Fresh.subst {L K : LCtx ν κ (Ty α)}
  : Φ.USubstL σ L K → K.Fresh ℓ → L.Fresh ℓ
  | InstSet.USubstL.nil, nil => nil
  | InstSet.USubstL.cons _ _ _ hσL, cons h f => cons h (subst hσL f)
  | InstSet.USubstL.skip _ hσL, cons h' f => subst hσL f

def InstSet.USubstL.wk_exit {σ : ν → UTm φ ν}
  {L K K' : LCtx ν κ (Ty α)}
  : USubstL σ L K → LCtx.Wk K K' → USubstL σ L K'
  | nil, LCtx.Wk.nil => nil
  | cons n A h hσ, @LCtx.Wk.cons _ _ _ _ _ ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨hn, hp, w⟩ w'
    => by cases hn; cases hp; exact cons n A (h.wk_exit w) (wk_exit hσ w')
  | skip h hσ, LCtx.Wk.cons hℓ w' => skip (hℓ.name ▸ h) (wk_exit hσ w')
  | hσ, LCtx.Wk.skip h' w => skip (h'.subst hσ) (wk_exit hσ w)

theorem InstSet.USubstL.allEq {σ : ν → UTm φ ν} {L K : LCtx ν κ (Ty α)}
  : (hσ  hσ': Φ.USubstL σ L K) → hσ = hσ'
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

inductive InstSet.USubstLP [Φ : InstSet φ (Ty α)] (σ : ν → UTm φ ν)
  : LCtx ν κ (Ty α) → LCtx ν κ (Ty α) → Type _
  | nil : USubstLP σ [] []
  | cons (n A) : USubst σ Γ Δ → USubstLP σ L K → USubstLP σ (⟨n, A, Γ⟩ :: L) (⟨n, A, Δ⟩ :: K)

theorem InstSet.USubstLP.allEq {σ : ν → UTm φ ν} {L K : LCtx ν κ (Ty α)}
  : (hσ  hσ': Φ.USubstLP σ L K) → hσ = hσ'
  | nil, nil => rfl
  | cons n A h hσ, cons _ _ h' hσ' => by
    cases h.allEq h'
    cases hσ.allEq hσ'
    rfl

def InstSet.USubstLP.pwk_exit {σ : ν → UTm φ ν} {L K K' : LCtx ν κ (Ty α)}
  : Φ.USubstLP σ L K → LCtx.PWk K K' → Φ.USubstLP σ L K'
  | nil, LCtx.PWk.nil => InstSet.USubstLP.nil
  | cons n A h hσ, @LCtx.PWk.cons _ _ _ _ _ ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨hn, hp, w'⟩ w =>
    by cases hn; cases hp; exact cons n A (h.wk_exit w') (hσ.pwk_exit w)

def InstSet.USubstLP.toUSubstL {σ : ν → UTm φ ν} {L K : LCtx ν κ (Ty α)}
  : Φ.USubstLP σ L K → Φ.USubstL σ L K
  | InstSet.USubstLP.nil => InstSet.USubstL.nil
  | InstSet.USubstLP.cons n A h hσ => InstSet.USubstL.cons n A h (toUSubstL hσ)

theorem LCtx.Fresh.substP {L K : LCtx ν κ (Ty α)}
  : Φ.USubstLP σ L K → K.Fresh ℓ → L.Fresh ℓ
  | InstSet.USubstLP.nil, nil => nil
  | InstSet.USubstLP.cons _ _ _ hσL, cons h f => cons h (substP hσL f)

theorem LCtx.Fresh.rsubstP {L K : LCtx ν κ (Ty α)}
  : Φ.USubstLP σ L K → L.Fresh ℓ → K.Fresh ℓ
  | InstSet.USubstLP.nil, nil => nil
  | InstSet.USubstLP.cons _ _ _ hσL, cons h f => cons h (rsubstP hσL f)

def InstSet.USubstLP.antiSJoin {σ : ν → UTm φ ν}
  {Γ : Ctx ν (Ty α)} {L K M L' K' : LCtx ν κ (Ty α)}
  : Φ.USubstLP σ L' L → Φ.USubstLP σ K' K → L.SJoin K M
    → Γ.LEq L' → Γ.LEq K'
    → (M' : LCtx ν κ (Ty α)) ×' L'.SJoin K' M' × Φ.USubstLP σ M' M
  | nil, nil, LCtx.SJoin.nil => λ_ _ => ⟨[], LCtx.SJoin.nil, nil⟩
  | cons n A hσ hσL, hσK, LCtx.SJoin.left h j => λhL hK =>
    let j' := antiSJoin hσL hσK j hL.tail hK;
    ⟨_, j'.2.1.left (h.substP hσK), j'.2.2.cons _ _ hσ⟩
  | hσL, cons n A hσ' hσK, LCtx.SJoin.right h j => λhL hK =>
    let j' := antiSJoin hσL hσK j hL hK.tail;
    ⟨_, j'.2.1.right (h.substP hσL), j'.2.2.cons _ _ hσ'⟩
  | cons n A _ hσL, cons _ _ hσ' hσK, LCtx.SJoin.both _ j => λhL hK  =>
    let j' := antiSJoin hσL hσK j hL.tail hK.tail;
    have hΓ := hL.head.symm.trans hK.head;
    ⟨_, (by cases hΓ; exact j'.2.1.both _), j'.2.2.cons _ _ hσ'⟩

def UTerminator.WfM.subst {t : UTerminator φ ν κ}
  {σ : ν → UTm φ ν}
  (hσ : Φ.USubst σ Γ Δ)
  : t.WfM Δ K → (L : LCtx ν κ (Ty α)) ×' (t.rewrite σ).WfM Γ L × Φ.USubstLP σ L K
  | br ℓ de => ⟨_, br ℓ (de.subst hσ), InstSet.USubstLP.nil.cons _ _ hσ⟩
  | ite dc dt df j =>
    let ⟨_, dt', hLt⟩ := subst hσ dt;
    let ⟨_, df', hLf⟩ := subst hσ df;
    let ⟨L, j', hL⟩ := hLt.antiSJoin hLf j dt'.lEq df'.lEq;
    ⟨L, ite (dc.subst hσ) dt' df' j', hL⟩

structure InstSet.USubstL' [Φ : InstSet φ (Ty α)]
  (σ : ν → UTm φ ν) (L K : LCtx ν κ (Ty α)) where
  mapped : LCtx ν κ (Ty α)
  uSubstLP : Φ.USubstLP σ L mapped
  wk : mapped.EWk K

def InstSet.USubstL.factor [Φ : InstSet φ (Ty α)]
  {σ : ν → UTm φ ν} {L K : LCtx ν κ (Ty α)}
  : Φ.USubstL σ L K → Φ.USubstL' σ L K
  | nil => ⟨[], USubstLP.nil, LCtx.EWk.nil⟩
  | cons n A hσ' hσL =>
    let hσL' := factor hσL;
    ⟨_, hσL'.uSubstLP.cons n A hσ', hσL'.wk.cons _⟩
  | skip h hσL =>
    let hσL' := factor hσL;
    ⟨_, hσL'.uSubstLP, hσL'.wk.skip (h.rsubstP hσL'.uSubstLP)⟩

def InstSet.USubstL'.toUSubstL [Φ : InstSet φ (Ty α)]
  {σ : ν → UTm φ ν} {L K : LCtx ν κ (Ty α)}
  (hσ : Φ.USubstL' σ L K) : Φ.USubstL σ L K
  := hσ.uSubstLP.toUSubstL.wk_exit hσ.wk.toWk

--TODO: USubstL'.allEq...

def UTerminator.Wf'.subst
  {t : UTerminator φ ν κ}
  (hσ : Φ.USubst σ Γ Δ)
  (dt : t.Wf' Δ K) : (L : LCtx ν κ (Ty α)) ×' (t.rewrite σ).Wf' Γ L × Φ.USubstL' σ L K :=
  let dt' := dt.wfM.subst hσ;
  let wk' := dt.wk.factor
  ⟨_, dt'.2.1.toWf', ⟨_, dt'.2.2.pwk_exit wk'.pWk, wk'.eWk⟩⟩

def UTerminator.Wf.subst
  {t : UTerminator φ ν κ}
  (hσ : Φ.USubst σ Γ Δ)
  (dt : t.Wf Δ K) : (L : LCtx ν κ (Ty α)) ×' (t.rewrite σ).Wf Γ L × Φ.USubstL σ L K :=
  let dt' := dt.factor.subst hσ;
  ⟨dt'.1, dt'.2.1.toWf, dt'.2.2.toUSubstL⟩
