import Mathlib.Logic.Lemmas

import FreydSSA.Ctx.Var.Fun
import FreydSSA.InstSet
import FreydSSA.Untyped.Basic

variable {φ ν α} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)] [Φi : InjInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq α]

--TODO: since this is quotiented, should this be a Prop? Can then do decidability and everything, and indexed contexts for the rest...

inductive UTm.FWf : Purity → FCtx ν (Ty α) → UTm φ ν → Ty α → Type _
  | var {x} {A : Ty α} (p)  : Γ x = (A : WithTop _) → FWf p Γ (var x) A
  | op : Φ.Op f p A B → FWf 1 Γ e A → FWf p Γ (op f e) B
  | pair (p) : FWf 1 Γ l A → FWf 1 Γ r B → FWf p Γ (pair l r) (A.pair B)
  | unit (p) : FWf p Γ unit Ty.unit
  | bool (p b) : FWf p Γ (bool b) Ty.bool

inductive UTm.FWfP : Purity → FCtx ν (Ty α) → UTm φ ν → Ty α → Prop
  | var {x} {A : Ty α} (p)  : Γ x = (A : WithTop _) → FWfP p Γ (var x) A
  | op : Φ.Op f p A B → FWfP 1 Γ e A → FWfP p Γ (op f e) B
  | pair (p) : FWfP 1 Γ l A → FWfP 1 Γ r B → FWfP p Γ (pair l r) (A.pair B)
  | unit (p) : FWfP p Γ unit Ty.unit
  | bool (p b) : FWfP p Γ (bool b) Ty.bool

-- TODO: need that type inference... :(
-- def UTm.FWfP.toFWf {Γ : FCtx ν (Ty α)} {e : UTm φ ν} (de : e.FWfP p Γ A) : e.FWf p Γ A
--   := match e with
--   | UTm.var x => FWf.var p (by cases de; assumption)
--   | UTm.op f e => @FWf.op _ _ _ _ f p _ A Γ e sorry (toFWf (match de with | op hf de => de))
--   | UTm.pair l r => pair p (dl.toFWf) (dr.toFWf)
--   | UTm.unit => λh => unit p
--   | UTm.bool b => λh => bool p b

variable {Γ Δ : FCtx ν (Ty α)}

def UTm.FWf.of_pure {e : UTm φ ν} : e.FWf 1 Γ A → e.FWf p Γ A
  | var _ w => var p w
  | op hf de => op hf.of_pure (de.of_pure)
  | pair _ dl dr => pair p (dl.of_pure) (dr.of_pure)
  | unit _ => unit p
  | bool _ b => bool p b

theorem FCtx.Cmp.tyEq {Γ Δ : FCtx ν (Ty α)} {e : UTm φ ν}
  (c : Γ.Cmp Δ) (de : UTm.FWf p Γ e A) (de' : UTm.FWf p' Δ e A') : A = A'
  := by induction de generalizing p' Δ A' with
  | var _ w => cases de' with | var _ w' => exact c.var_eq _ _ _ w w'
  | op hf _ I => cases de' with | op hf' de' => exact Φc.coh_trg' hf hf' (I c de')
  | pair _ _ _ I1 I2 => cases de' with | pair _ dl' dr' => rw [I1 c dl', I2 c dr']
  | _ => cases de'; rfl

theorem UTm.FWf.tyEq {e : UTm φ ν} (de : e.FWf p Γ A) (de' : e.FWf p' Γ A')
  : A = A' := (FCtx.Cmp.refl Γ).tyEq de de'

theorem UTm.FWf.allEq {e : UTm φ ν}
  (de : e.FWf p Γ A) (de' : e.FWf p Γ A) : de = de' := by induction de with
  | var _ w => cases de' with | var _ w' => rfl
  | op hf de I => cases de' with | op hf' de' =>
    cases de.tyEq de'
    rw [I de']
  | pair _ dl dr Il Ir => cases de' with | pair _ dl' dr' => rw [Il dl', Ir dr']
  | _ => cases de'; rfl

theorem UTm.FWf.allHeq {e : UTm φ ν}
  (de : e.FWf p Γ A) (de' : e.FWf p Γ A') : HEq de de'
  := by cases de.tyEq de'; apply Eq.heq; apply allEq

def UTm.FWf.wk {e : UTm φ ν} (w : Γ.Wk Δ) : e.FWf p Δ A → e.FWf p Γ A
  | var p w' => var p (w.var _ _ w')
  | op hf de => op hf (de.wk w)
  | pair p dl dr => pair p (dl.wk w) (dr.wk w)
  | unit p => unit p
  | bool p b => bool p b

def UTm.FWf.lsup {e : UTm φ ν} : e.FWf p Γ A → e.FWf p' Δ A' → e.FWf p (Γ.lsup Δ) A
  | var p w, var _ w' => var p (by rw [FCtx.lsup_right_var_eq_left _ _ w']; exact w)
  | op hf de, op _ de' => op hf (de.lsup de')
  | pair p dl dr, pair _ dl' dr' => pair p (dl.lsup dl') (dr.lsup dr')
  | unit p, _ => unit p
  | bool p b, _ => bool p b

def UTm.FWf.rsup {e : UTm φ ν} : e.FWf p Γ A → e.FWf p' Δ A' → e.FWf p' (Γ.rsup Δ) A'
  | var _ w, var p' w' => var p' (by rw [FCtx.rsup_left_var_eq_right _ _ w]; exact w')
  | op _ de, op hf' de' => op hf' (de.rsup de')
  | pair _ dl dr, pair p' dl' dr' => pair p' (dl.rsup dl') (dr.rsup dr')
  | _, unit p' => unit p'
  | _, bool p' b => bool p' b

def FCtx.Cmp.wfSup {e : UTm φ ν} (c : Γ.Cmp Δ) : e.FWf p Γ A → e.FWf p' Δ A' → e.FWf p (Γ.sup Δ) A
  | UTm.FWf.var p w, UTm.FWf.var _ w' => UTm.FWf.var p
    (by rw [c.sup_eq_lsup, lsup_right_var_eq_left _ _ w']; exact w)
  | UTm.FWf.op hf de, UTm.FWf.op _ de' => UTm.FWf.op hf (c.wfSup de de')
  | UTm.FWf.pair p dl dr, UTm.FWf.pair _ dl' dr' => UTm.FWf.pair p (c.wfSup dl dl') (c.wfSup dr dr')
  | UTm.FWf.unit p, _ => UTm.FWf.unit p
  | UTm.FWf.bool p b, _ => UTm.FWf.bool p b

def UTm.FWf.restrict {e : UTm φ ν} : e.FWf p Γ A → e.FWf p (Γ.restrict e.vars) A
  | var p w => var p (by simp [vars, FCtx.restrict_app, w])
  | op hf de => op hf de.restrict
  | pair p dl dr => pair p
    (dl.restrict.wk (FCtx.Wk.restrict_union_left _ _ _))
    (dr.restrict.wk (FCtx.Wk.restrict_union_right _ _ _))
  | unit p => unit p
  | bool p b => bool p b

def UTm.FWf.vars_sub_support {e : UTm φ ν} : e.FWf p Γ A → e.vars ⊆ Γ.support
  | var p w => by simp [vars, FCtx.mem_support, w]
  | op hf de => de.vars_sub_support
  | pair p dl dr => Finset.union_subset dl.vars_sub_support dr.vars_sub_support
  | unit p => by simp [vars]
  | bool p b => by simp [vars]

def UTm.FWf.src_eq_on {e : UTm φ ν} (de : e.FWf p Γ A) (de' : e.FWf p' Γ' A)
  : ∀x ∈ e.vars, Γ x = Γ' x := by induction de generalizing Γ' p' with
  | var _ w => cases de' with | var _ w' => simp [vars, w, w']
  | op hf _ I => cases de' with | op hf' de' =>
    intro x hx
    cases Φi.coh_src hf hf'
    exact I de' x hx
  | pair _ _ _ Il Ir => cases de' with | pair _ dl' dr' =>
    simp only [vars, Finset.mem_union]
    intro x hx
    cases hx with
    | inl hx => exact Il dl' x hx
    | inr hx => exact Ir dr' x hx
  | _ => simp [vars, FCtx.restrict_empty]

def UTm.FWf.src_restrict_eq {e : UTm φ ν} (de : e.FWf p Γ A) (de' : e.FWf p' Γ' A)
  : Γ.restrict e.vars = Γ'.restrict e.vars
  := Γ.restrict_eq_of_eq_on Γ' e.vars (src_eq_on de de')

--TODO: cmp ==> inf = linf without alleq, rinf with
