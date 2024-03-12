import FreydSSA.Body.Intrinsic.Basic
import FreydSSA.Term.Intrinsic.Subst

def InstSet.Body.SSA.subst [Φ : InstSet φ (Ty α)] {Γ Δ Ξ : Ctx ν (Ty α)} (σ: Φ.Subst Γ Δ)
  : {b: Φ.Body p Δ Ξ} → b.SSA → Γ.names.Disjoint b.defs
    → (Ξ' : Ctx ν (Ty α)) × Φ.Body p Γ Ξ' × Φ.Subst Ξ' Ξ
  | Body.nil _ w, _, _ => ⟨Γ, Body.nil p (Ctx.Wk.refl _), σ.wk_exit w⟩
  | Body.let1 e b, h, h' =>
    let e' := e.subst σ;
    let ⟨Ξ', b', σ'⟩ := h.of_let1.subst
      (σ.cons2' (by simp only [defs, List.disjoint_cons_right] at h'; exact h'.1))
      (by
        simp only [Ctx.names, List.map, List.disjoint_cons_left]
        constructor
        exact h.notdef'
        simp only [defs, List.disjoint_cons_right] at h'; exact h'.2
      );
    ⟨Ξ', Body.let1 e' b', σ'⟩
  | Body.let2 e b, h, h' =>
    let e' := e.subst σ;
    let ⟨Ξ', b', σ'⟩ := h.of_let2.subst
      ((σ.cons2'
        (by simp only [defs, List.disjoint_cons_right] at h'; exact h'.1)).cons2'
        (by
          simp only [defs, List.disjoint_cons_right] at h'
          apply List.not_mem_cons_of_ne_of_not_mem
          exact h.l_ne_r
          exact h'.2.1
        ))
      (by
        simp only [Ctx.names, List.map, List.disjoint_cons_left]
        constructor
        exact h.notdefl'
        constructor
        exact h.notdefr'
        simp only [defs, List.disjoint_cons_right] at h'; exact h'.2.2
      );
    ⟨Ξ', Body.let2 e' b', σ'⟩

--TODO: subst comp eq...

--TODO: subst α...
