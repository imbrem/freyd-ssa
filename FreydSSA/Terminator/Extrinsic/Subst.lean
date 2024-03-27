import FreydSSA.Terminator.Extrinsic.Basic
import FreydSSA.Term.Extrinsic.Subst

variable {φ ν α} [Φ : InstSet φ (Ty α)] [Φc : CohInstSet φ (Ty α)]

def InstSet.USubst.src {σ : ν → UTm φ ν} {Γ Δ : Ctx ν (Ty α)}  (_ : Φ.USubst σ Γ Δ)
  : Ctx ν (Ty α) := Γ

def InstSet.USubst.trg {σ : ν → UTm φ ν} {Γ Δ : Ctx ν (Ty α)}  (_ : Φ.USubst σ Γ Δ)
  : Ctx ν (Ty α) := Δ

inductive InstSet.USubstL [Φ : InstSet φ (Ty α)] (σ : ν → UTm φ ν)
  : LCtx ν κ (Ty α) → LCtx ν κ (Ty α) → Type _
  | nil : USubstL σ [] []
  | cons (n A) : USubst σ Γ Δ → USubstL σ L K → USubstL σ (⟨n, A, Γ⟩ :: L) (⟨n, A, Δ⟩ :: K)
  | skip : L.Fresh ℓ.name → USubstL σ L K → USubstL σ L (ℓ :: K)

def InstSet.USubstL.ofEmpty [Φ : InstSet φ (Ty α)]
  (σ : ν → UTm φ ν)
  {L : LCtx ν κ (Ty α)}
  : (LCtx.Wk [] L) → USubstL σ [] L
  | LCtx.Wk.nil => nil
  | LCtx.Wk.skip hℓ w => skip hℓ (ofEmpty σ w)

def InstSet.USubstL.ofVar [Φ : InstSet φ (Ty α)] {σ : ν → UTm φ ν}
  {Γ Δ : Ctx ν (Ty α)}
  {n A}
  (hσ : USubst σ Γ Δ)
  : {L : LCtx ν κ (Ty α)} → LCtx.Wk [⟨n, A, Δ⟩] L → USubstL σ [⟨n, A, Γ⟩] L
  | ⟨_, _, _Δ'⟩::_, LCtx.Wk.cons ⟨rfl, rfl, wΔ⟩ w => cons _ _ (hσ.wk_exit wΔ) (ofEmpty σ w)
  | _::_, LCtx.Wk.skip hℓ w => skip (LCtx.Fresh.of_not_mem hℓ.not_mem) (ofVar hσ w)

def InstSet.USubstL.shared  {σ : ν → UTm φ ν}
  {L K M : LCtx ν κ (Ty α)}
  : USubstL σ L M → USubstL σ K M → LCtx ν κ (Ty α)
  | nil, nil => []
  | cons n A hσ w, cons _ _ _ w'
    => ⟨n, A, hσ.src⟩ :: shared w w'
  | skip _ w, cons _ _ _ w' => shared w w'
  | cons _ _ _ w, skip _ w' => shared w w'
  | skip _ w, skip _ w' => shared w w'

inductive InstSet.USubstLP [Φ : InstSet φ (Ty α)] (σ : ν → UTm φ ν)
  : LCtx ν κ (Ty α) → LCtx ν κ (Ty α) → Type _
  | nil : USubstLP σ [] []
  | cons (n A) : USubst σ Γ Δ → USubstLP σ L K → USubstLP σ (⟨n, A, Γ⟩ :: L) (⟨n, A, Δ⟩ :: K)

def LCtx.Fresh.substP {L K : LCtx ν κ (Ty α)}
  : Φ.USubstLP σ L K → L.Fresh ℓ → K.Fresh ℓ
  | InstSet.USubstLP.nil, nil => nil
  | InstSet.USubstLP.cons _ _ _ hσL, cons h f => cons h (substP hσL f)

def LCtx.Fresh.rsubstP {L K : LCtx ν κ (Ty α)}
  : Φ.USubstLP σ L K → K.Fresh ℓ → L.Fresh ℓ
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
    ⟨_, j'.2.1.left (h.rsubstP hσK), j'.2.2.cons _ _ hσ⟩
  | hσL, cons n A hσ' hσK, LCtx.SJoin.right h j => λhL hK =>
    let j' := antiSJoin hσL hσK j hL hK.tail;
    ⟨_, j'.2.1.right (h.rsubstP hσL), j'.2.2.cons _ _ hσ'⟩
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

-- structure InstSet.USubstL' [Φ : InstSet φ (Ty α)]
--   (σ : ν → UTm φ ν) (L K : LCtx ν κ (Ty α)) where
--   mapped : LCtx ν κ (Ty α)
--   uSubstLP : USubstLP σ L mapped
--   wk : mapped.Wk K --TODO: ExtWk or smt...

-- theorem LCtx.Fresh.shared_of_left {L K M : LCtx ν κ (Ty α)}
--   (w : Φ.USubstL σ L M)
--   (w' : Φ.USubstL σ K M)
--   (f : L.Fresh ℓ) : (w.shared w').Fresh ℓ
--   := by induction f with
--   | nil => sorry
--   | cons => sorry

-- --TODO: why are these not defeq :(
-- def InstSet.USubstL.sharedOfLeftRight {σ : ν → UTm φ ν}
--   {L K M : LCtx ν κ (Ty α)} : (w : USubstL σ L M) → (w' : USubstL σ K M)
--     → USubstL σ (shared w w') M
--   | nil, nil => nil
--   | cons _ _ hσ w, cons _ _ _ w'
--     => by
--       simp only [shared, USubst.src]
--       exact cons _ _ hσ (sharedOfLeftRight w w')
--   | skip _ w, cons _ _ _ w'
--     => skip sorry (by simp only [shared]; exact sharedOfLeftRight w w')
--   | cons _ _ _ w, skip _ w'
--     => skip sorry (by simp only [shared]; exact sharedOfLeftRight w w')
--   | skip hx w, skip hx' w'
--     => skip sorry (by simp only [shared]; exact sharedOfLeftRight w w')

-- def InstSet.USubstL.union {σ : ν → UTm φ ν}
--   {L K Ω M : LCtx ν κ (Ty α)}
--   : L.Wk Ω → K.Wk Ω → USubstL σ L M → USubstL σ K M → LCtx ν κ (Ty α)
--   | _, _, nil, nil => []
--   | LCtx.Wk.cons _ oL, LCtx.Wk.cons _ oK, cons n A hσ w, cons _ _ hσ' w'
--     => ⟨n, A, hσ.src⟩ :: union oL oK w w'
--   | LCtx.Wk.skip _ oL, LCtx.Wk.cons _ oK, skip _ w, cons n A hσ w'
--     => ⟨n, A, hσ.src⟩ :: union oL oK w w'
--   | _, _, cons n A hσ w, skip _ w' => ⟨n, A, hσ.src⟩ :: union w w'
--   | _, _, skip _ w, skip _ w' => union w w'

-- theorem LCtx.Fresh.union_of_left_right {L K M : LCtx ν κ (Ty α)}
--   (w : Φ.USubstL σ L M)
--   (w' : Φ.USubstL σ K M)
--   (f : L.Fresh ℓ) (f' : K.Fresh ℓ) : (w.union w').Fresh ℓ
--   := match w, w' with
--   | InstSet.USubstL.nil, InstSet.USubstL.nil => nil
--   | InstSet.USubstL.cons _ _ hσ w, InstSet.USubstL.cons _ _ _ w' => by
--     simp only [InstSet.USubstL.union]
--     cases f; cases f';
--     constructor
--     assumption
--     apply union_of_left_right <;> assumption
--   | InstSet.USubstL.skip _ w, InstSet.USubstL.cons _ _ _ w' => by
--     simp only [InstSet.USubstL.union]
--     cases f'
--     constructor
--     assumption
--     apply union_of_left_right <;> assumption
--   | InstSet.USubstL.cons _ _ _ w, InstSet.USubstL.skip _ w' => by
--     simp only [InstSet.USubstL.union]
--     cases f
--     constructor
--     assumption
--     apply union_of_left_right <;> assumption
--   | InstSet.USubstL.skip _ w, InstSet.USubstL.skip _ w' => by
--     simp only [InstSet.USubstL.union]
--     apply union_of_left_right <;> assumption

-- --TODO: buggy unused variables...
-- theorem LCtx.Fresh.left_of_union {L K M : LCtx ν κ (Ty α)}
--   (w : Φ.USubstL σ L M)
--   (w' : Φ.USubstL σ K M)
--   (_f: (w.union w').Fresh ℓ) : L.Fresh ℓ
--   := match w, w' with
--   | InstSet.USubstL.nil, InstSet.USubstL.nil => nil
--   | InstSet.USubstL.cons _ _ hσ w, InstSet.USubstL.cons _ _ _ w' => by
--     simp only [InstSet.USubstL.union] at *
--     cases _f
--     constructor
--     assumption
--     apply left_of_union <;> assumption
--   | InstSet.USubstL.skip _ w, InstSet.USubstL.cons _ _ _ w' => by
--     simp only [InstSet.USubstL.union] at *
--     cases _f
--     apply left_of_union <;> assumption
--   | InstSet.USubstL.cons _ _ _ w, InstSet.USubstL.skip _ w' => by
--     simp only [InstSet.USubstL.union] at *
--     cases _f
--     constructor
--     assumption
--     apply left_of_union <;> assumption
--   | InstSet.USubstL.skip _ w, InstSet.USubstL.skip _ w' => by
--     simp only [InstSet.USubstL.union] at *
--     apply left_of_union <;> assumption

-- --TODO: buggy unused variables...
-- theorem LCtx.Fresh.right_of_union {L K M : LCtx ν κ (Ty α)}
--   (w : Φ.USubstL σ L M)
--   (w' : Φ.USubstL σ K M)
--   (_f: (w.union w').Fresh ℓ) : K.Fresh ℓ
--   := match w, w' with
--   | InstSet.USubstL.nil, InstSet.USubstL.nil => nil
--   | InstSet.USubstL.cons _ _ hσ w, InstSet.USubstL.cons _ _ _ w' => by
--     simp only [InstSet.USubstL.union] at *
--     cases _f
--     constructor
--     assumption
--     apply right_of_union <;> assumption
--   | InstSet.USubstL.skip _ w, InstSet.USubstL.cons _ _ _ w' => by
--     simp only [InstSet.USubstL.union] at *
--     cases _f
--     constructor
--     assumption
--     apply right_of_union <;> assumption
--   | InstSet.USubstL.cons _ _ _ w, InstSet.USubstL.skip _ w' => by
--     simp only [InstSet.USubstL.union] at *
--     cases _f
--     apply right_of_union <;> assumption
--   | InstSet.USubstL.skip _ w, InstSet.USubstL.skip _ w' => by
--     simp only [InstSet.USubstL.union] at *
--     apply right_of_union <;> assumption

-- def InstSet.USubstL.unionOfLeftRight {σ : ν → UTm φ ν}
--   {L K M : LCtx ν κ (Ty α)} : (w : USubstL σ L M) → (w' : USubstL σ K M)
--     → USubstL σ (union w w') M
--   | nil, nil => nil
--   | cons _ _ hσ w, cons _ _ _ w' => by
--     simp only [union, USubst.src]
--     exact cons _ _ hσ (unionOfLeftRight w w')
--   | skip _ w, cons _ _ hσ w' => by
--     simp only [union, USubst.src]
--     exact cons _ _ hσ (unionOfLeftRight w w')
--   | cons _ _ hσ w, skip _ w' => by
--     simp only [union, USubst.src]
--     exact cons _ _ hσ (unionOfLeftRight w w')
--   | skip hx w, skip hx' w' => by
--     simp only [union, USubst.src]
--     exact skip (hx.union_of_left_right w w' hx') (unionOfLeftRight w w')

-- def InstSet.USubstL.leftUnionWk {σ : ν → UTm φ ν}
--   {L K M : LCtx ν κ (Ty α)}
--   : (w : USubstL σ L M) → (w' : USubstL σ K M) → L.Wk (union w w')
--   | nil, nil => LCtx.Wk.nil
--   | cons _ _ hσ w, cons _ _ _ w' => by
--     simp only [union, USubst.src]
--     exact LCtx.Wk.cons (Label.Wk.refl _) (leftUnionWk w w')
--   | skip f w, cons _ _ hσ w' => by
--     simp only [union, USubst.src]
--     exact LCtx.Wk.skip f (leftUnionWk w w')
--   | cons _ _ hσ w, skip _ w' => by
--     simp only [union, USubst.src]
--     exact LCtx.Wk.cons (Label.Wk.refl _) (leftUnionWk w w')
--   | skip hx w, skip hx' w' => by
--     simp only [union, USubst.src]
--     exact leftUnionWk w w'

-- def InstSet.USubstL.rightUnionWk {σ : ν → UTm φ ν}
--   {L K M : LCtx ν κ (Ty α)}
--   : (w : USubstL σ L M) → (w' : USubstL σ K M) → K.Wk (union w w')
--   | nil, nil => LCtx.Wk.nil
--   | cons _ _ _ w, cons _ _ _ w' => by
--     simp only [union, USubst.src]
--     --TODO: need term meeting...
--     exact LCtx.Wk.cons ⟨rfl, rfl, sorry⟩ (rightUnionWk w w')
--   | skip f w, cons _ _ hσ w' => by
--     simp only [union, USubst.src]
--     exact LCtx.Wk.cons (Label.Wk.refl _) (rightUnionWk w w')
--   | cons _ _ hσ w, skip hx w' => by
--     simp only [union, USubst.src]
--     exact LCtx.Wk.skip hx (rightUnionWk w w')
--   | skip hx w, skip hx' w' => by
--     simp only [union, USubst.src]
--     exact rightUnionWk w w'

-- def UTerminator.Wf.subst
--   {t : UTerminator φ ν κ}
--   (hσ : Φ.USubst σ Γ Δ)
--   : t.Wf Δ K → (L : LCtx ν κ (Ty α)) ×' (t.rewrite σ).Wf Γ L × Φ.USubstL σ L K
--   | br hℓ de => ⟨[⟨_, _, _⟩], br (LCtx.Wk.refl _) (de.subst hσ), InstSet.USubstL.ofVar hσ hℓ⟩
--   | ite dc dt df =>
--     let ⟨_, dt', hLt⟩ := subst hσ dt;
--     let ⟨_, df', hLf⟩ := subst hσ df;
--     ⟨hLt.union hLf,
--       ite (dc.subst hσ)
--         (dt'.wk_exit (hLt.leftUnionWk hLf))
--         (df'.wk_exit (hLt.rightUnionWk hLf)),
--       hLt.unionOfLeftRight hLf⟩
