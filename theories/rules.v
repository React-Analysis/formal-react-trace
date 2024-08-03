From Coq Require Import ZArith String Program.Tactics.
From stdpp Require Import base list tactics.
From theories Require Import fold syntax domains react_notations.
From Hammer Require Import Hammer Tactics.
Import ListNotations.

Notation "'|' l '|'" := (length l) (at level 10).

Record some_expr := {
  tag: hook_tag;
  expr: expr tag
}.

Notation "e '@' t" := {| tag := t; expr := e |} (at level 10).

Definition vs_of_value (v : value) : option view_spec :=
  match v with
  | Unit => Some Vs_null
  | Int i => Some (Vs_int i)
  | Comp_spec t => Some (Vs_comp t)
  | _ => None
  end.

Definition value_of_vs (vs : view_spec) : value :=
  match vs with
  | Vs_null => Unit
  | Vs_int i => Int i
  | Vs_comp t => Comp_spec t
  end.

Lemma value_of_vs_inj v1 v2 : value_of_vs v1 = value_of_vs v2 → v1 = v2.
Proof. sauto lq: on rew: off. Qed.

Class BigStep :=
  big_step : tree_mem → env.t value → path → phase → some_expr → value → tree_mem → Prop.

Notation "'{' m ',' σ '⊢' e '⇓_' p '^' ϕ v ',' m' '}'" := (big_step m σ p ϕ e v m')
  (at level 10, p at next level, ϕ at next level).

Definition big_step_leq `(B : BigStep) `(B' : BigStep) :=
  ∀ m σ p ϕ e v m', B m σ p ϕ e v m' → B' m σ p ϕ e v m'.

Infix "⊑" := big_step_leq (at level 70).

Module big_step_fold.
  Variant big_step_f `(BigStep) (m : tree_mem) (σ : env.t value) (p : path) :
    phase → some_expr → value → tree_mem → Prop :=
    | Var ϕ t (x : string) v:
        σ !! x = Some v →
        { m, σ ⊢ <{ x }> @ t ⇓_p^ϕ v, m }
    | Unit ϕ t:
{ m, σ ⊢ <{ () }> @ t ⇓_p^ϕ unit, m }
    | True ϕ t:
        { m, σ ⊢ <{ true }> @ t ⇓_p^ϕ true, m }
    | False ϕ t:
        { m, σ ⊢ <{ false }> @ t ⇓_p^ϕ false, m }
    | Int ϕ t (n : Z):
        { m, σ ⊢ <{ n }> @ t ⇓_p^ϕ Int n, m }
    | ViewSpec ϕ t (es : list _) vss evss m':
      (map fst evss = es) →
      (map snd evss = vss) →
      (foldl (λ (Mi : tree_mem → Prop) evsi,
        λ (mSi : tree_mem),
          ∃ mi,
            Mi mi ∧
            { mi, σ  ⊢ evsi.1 @ Hook_free ⇓_p^ϕ value_of_vs evsi.2, mSi }
        ) (λ m1, m1 = m) evss m') →
      { m, σ ⊢ View es @ t ⇓_p^ϕ View_spec vss, m' }
    | CondT ϕ t e1 e2 e3 v m' m'':
        { m, σ ⊢ e1 @ _ ⇓_p^ϕ true, m' } →
        { m', σ ⊢ e2 @ _ ⇓_p^ϕ v, m'' } →
        { m, σ ⊢ <{ if e1 then e2 else e3 }> @ t ⇓_p^ϕ v, m'' }
    | CondF ϕ t e1 e2 e3 v m' m'':
        { m, σ ⊢ e1 @ _ ⇓_p^ϕ false, m' } →
        { m', σ ⊢ e3 @ _ ⇓_p^ϕ v, m'' } →
        { m, σ ⊢ <{ if e1 then e2 else e3 }> @ t ⇓_p^ϕ v, m'' }
    | Func ϕ t x e:
        { m, σ ⊢ <{ fun x ⇒ e }> @ t ⇓_p^ϕ Clos {| param := x; body := e; env := σ |}, m }
    | AppFunc ϕ t e1 e2 v1 λ1 v2 v' m1 m2 m':
        { m, σ ⊢ e1 @ _ ⇓_p^ϕ v1, m1 } →
        v1 = Clos λ1 →
        { m1, σ ⊢ e2 @ _ ⇓_p^ϕ v2, m2 } →
        { m2, <[ λ1.(param) := v2 ]> λ1.(env) ⊢ e2 @ _ ⇓_p^ϕ v', m' } →
        { m, σ ⊢ <{ e1 e2 }> @ t ⇓_p^ϕ v', m' }
    | AppComp ϕ t e1 e2 v1 cλ1 v2 m1 m2:
        { m, σ ⊢ e1 @ _ ⇓_p^ϕ v1, m1 } →
        v1 = Comp_clos cλ1 →
        { m1, σ ⊢ e2 @ _ ⇓_p^ϕ v2, m2 } →
        { m, σ ⊢ <{ e1 e2 }> @ t ⇓_p^ϕ Comp_spec {| cs_comp := cλ1.(cc_comp); cs_env := cλ1.(cc_env); cs_arg := v2 |}, m2 }
    | AppSetStt ϕ t e1 e2 v1 sλ1 v2 λ2 ent' (m1 m2 : tree_mem) :
        { m, σ ⊢ e1 @ _ ⇓_p^ϕ v1, m1 } →
        v1 = Set_clos sλ1 →
        { m1, σ ⊢ e2 @ _ ⇓_p^ϕ v2, m2 } →
        v2 = Clos λ2 →
        (Some ent' =
          ent ← m2 !! sλ1.(pt);
          match ent.(π) with
          | Node nd =>
            sq ← nd.(ρ_s) !! sλ1.(ℓ) ;
            let s := sq.1 in
            let q := sq.2 in
            let nd' := {|
              cs := nd.(cs);
              dec := if decide (p = sλ1.(pt) ∧ ϕ ≠ P_effect) then Retry else Update;
              ρ_s := <[ sλ1.(ℓ) := (s, q ++ [ λ2 ]) ]> nd.(ρ_s);
              eff_q := nd.(eff_q)
            |} in
            Some {| π := Node nd'; children := ent.(children) |}
          | _ => None
          end) →
        { m, σ ⊢ <{ e1 e2 }> @ t ⇓_p^ϕ unit, <[ sλ1.(pt) := ent' ]> m2 }
    | StReBind ϕ t ℓ x set_x init e vi vf v q mf mf' m' σ' :
        (ϕ ∈ [P_update; P_retry]) →
        (Some (vi, q) =
          ent ← m !! p;
match ent.(π) with
          | Node nd => nd.(ρ_s) !! ℓ
          | _ => None
          end) →
        (foldl (λ VMk λk,
          λ vmSk,
            ∃ vmk,
              VMk vmk ∧
              { vmk.2, <[λk.(param) := vmk.1]>λk.(env) ⊢ λk.(body) @ Hook_free ⇓_p^ϕ vmSk.1, vmSk.2 }
          ) (λ vm1, vm1 = (vi, m)) q (vf, mf)) →
        (Some (mf', σ') =
          ent ← mf !! p;
          match ent.(π) with
          | Node nd =>
            let nd' :=
              let d := nd.(dec) in
              let ρ := nd.(ρ_s) in
              {|
                cs := nd.(cs);
                dec := if negb (value_eqb vi vf) then Update else d;
                ρ_s := <[ ℓ := (vf, []) ]>ρ;
                eff_q := nd.(eff_q);
              |} in
            let mf' := <[ p := {| π := Node nd'; children := ent.(children) |} ]>mf in
            let σ' := <[ set_x := Set_clos {| ℓ := ℓ; pt := p |} ]> $ <[ x := vf ]>σ in
            Some (mf', σ')
          | _ => None
          end) →
        { mf', σ' ⊢ e @ Hook_full ⇓_p^ϕ v, m' } →
        { m, σ ⊢ <{ let (x, set_x) = useState@ℓ init in e }> @ t ⇓_p^ϕ v, m' }.
End big_step_fold.

Module big_step_idx.
  Variant big_step_f `(BigStep) (m : tree_mem) (σ : env.t value) (p : path) :
    phase → some_expr → value → tree_mem → Prop :=
    | Var ϕ t (x : string) v:
        σ !! x = Some v →
        { m, σ ⊢ <{ x }> @ t ⇓_p^ϕ v, m }
    | Unit ϕ t:
        { m, σ ⊢ <{ () }> @ t ⇓_p^ϕ unit, m }
    | True ϕ t:
        { m, σ ⊢ <{ true }> @ t ⇓_p^ϕ true, m }
    | False ϕ t:
        { m, σ ⊢ <{ false }> @ t ⇓_p^ϕ false, m }
    | Int ϕ t (n : Z):
        { m, σ ⊢ <{ n }> @ t ⇓_p^ϕ Int n, m }
    | ViewSpec ϕ t (es : list _) vss evss m' (rev_ms : list _):
        (map fst evss = es) →
        (map snd evss = vss) →
        (rev_ms !! 0 = Some m') →
        (rev_ms !! |evss| = Some m) →
        (∀ k,
          k < |evss| →
          ∃ mk evsk mSk,
            rev evss !! k = Some evsk ∧
            rev_ms !! k = Some mSk ∧
            rev_ms !! (S k) = Some mk ∧
            { mk, σ ⊢ evsk.1 @ _ ⇓_p^ϕ value_of_vs evsk.2, mSk }
        ) →
        { m, σ ⊢ <{ view es }> @ t ⇓_p^ϕ View_spec vss, m' }
    | CondT ϕ t e1 e2 e3 v m' m'':
        { m, σ ⊢ e1 @ _ ⇓_p^ϕ true, m' } →
        { m', σ ⊢ e2 @ _ ⇓_p^ϕ v, m'' } →
        { m, σ ⊢ <{ if e1 then e2 else e3 }> @ t ⇓_p^ϕ v, m'' }
    | CondF ϕ t e1 e2 e3 v m' m'':
        { m, σ ⊢ e1 @ _ ⇓_p^ϕ false, m' } →
        { m', σ ⊢ e3 @ _ ⇓_p^ϕ v, m'' } →
        { m, σ ⊢ <{ if e1 then e2 else e3 }> @ t ⇓_p^ϕ v, m'' }
    | Func ϕ t x e:
        { m, σ ⊢ <{ fun x ⇒ e }> @ t ⇓_p^ϕ Clos {| param := x; body := e; env := σ |}, m }
    | AppFunc ϕ t e1 e2 v1 λ1 v2 v' m1 m2 m':
        { m, σ ⊢ e1 @ _ ⇓_p^ϕ v1, m1 } →
        v1 = Clos λ1 →
        { m1, σ ⊢ e2 @ _ ⇓_p^ϕ v2, m2 } →
        { m2, <[ λ1.(param) := v2 ]> λ1.(env) ⊢ e2 @ _ ⇓_p^ϕ v', m' } →
        { m, σ ⊢ <{ e1 e2 }> @ t ⇓_p^ϕ v', m' }
    | AppComp ϕ t e1 e2 v1 cλ1 v2 m1 m2:
        { m, σ ⊢ e1 @ _ ⇓_p^ϕ v1, m1 } →
        v1 = Comp_clos cλ1 →
        { m1, σ ⊢ e2 @ _ ⇓_p^ϕ v2, m2 } →
        { m, σ ⊢ <{ e1 e2 }> @ t ⇓_p^ϕ Comp_spec {| cs_comp := cλ1.(cc_comp); cs_env := cλ1.(cc_env); cs_arg := v2 |}, m2 }
    | AppSetStt ϕ t e1 e2 v1 sλ1 v2 λ2 ent' (m1 m2 : tree_mem) :
        { m, σ ⊢ e1 @ _ ⇓_p^ϕ v1, m1 } →
        v1 = Set_clos sλ1 →
        { m1, σ ⊢ e2 @ _ ⇓_p^ϕ v2, m2 } →
        v2 = Clos λ2 →
        (Some ent' =
          ent ← m2 !! sλ1.(pt);
          match ent.(π) with
          | Node nd =>
            sq ← nd.(ρ_s) !! sλ1.(ℓ) ;
            let s := sq.1 in
            let q := sq.2 in
            let nd' := {|
              cs := nd.(cs);
              dec := if decide (p = sλ1.(pt) ∧ ϕ ≠ P_effect) then Retry else Update;
              ρ_s := <[ sλ1.(ℓ) := (s, q ++ [ λ2 ]) ]> nd.(ρ_s);
              eff_q := nd.(eff_q)
            |} in
            Some {| π := Node nd'; children := ent.(children) |}
          | _ => None
          end) →
        { m, σ ⊢ <{ e1 e2 }> @ t ⇓_p^ϕ unit, <[ sλ1.(pt) := ent' ]> m2 }
    | StReBind ϕ t ℓ x set_x init e vi vf v (q : job_q) mf mf' m' σ' (rev_vms : list _) :
        (ϕ ∈ [P_update; P_retry]) →
        (Some (vi, q) =
          ent ← m !! p;
          match ent.(π) with
          | Node nd => nd.(ρ_s) !! ℓ
          | _ => None
          end) →
        (rev_vms !! |q| = Some (vi, m)) →
        (rev_vms !! 0 = Some (vf, mf)) →
        (∀ k,
          k < |q| →
          ∃ λk vmk vmSk,
            rev q !! k = Some λk ∧
            rev_vms !! (S k) = Some vmk ∧
            rev_vms !! k = Some vmSk ∧
            { vmk.2, <[λk.(param) := vmk.1]>λk.(env) ⊢ λk.(body) @ Hook_free ⇓_p^ϕ vmSk.1, vmSk.2 }) →
        (Some (mf', σ') =
          ent ← mf !! p;
          match ent.(π) with
          | Node nd =>
            let nd' :=
              let d := nd.(dec) in
              let ρ := nd.(ρ_s) in
              {|
                cs := nd.(cs);
                dec := if negb (value_eqb vi vf) then Update else d;
                ρ_s := <[ ℓ := (vf, []) ]>ρ;
                eff_q := nd.(eff_q);
              |} in
            let mf' := <[ p := {| π := Node nd'; children := ent.(children) |} ]>mf in
            let σ' := <[ set_x := Set_clos {| ℓ := ℓ; pt := p |} ]> $ <[ x := vf ]>σ in
            Some (mf', σ')
          | _ => None
          end) →
        { mf', σ' ⊢ e @ Hook_full ⇓_p^ϕ v, m' } →
        { m, σ ⊢ <{ let (x, set_x) = useState@ℓ init in e }> @ t ⇓_p^ϕ v, m' }.

  Lemma big_step_equiv `(P : BigStep) :
    big_step_f P ⊑ big_step_fold.big_step_f P ∧
    big_step_fold.big_step_f P ⊑ big_step_f P.
  Proof.
    split; intros m σ p ϕ e v m'.
    - inv 1;
        match goal with
        | _ : context [true] |- _ => eapply big_step_fold.CondT
        | _ : context [false] |- _ => eapply big_step_fold.CondF
        | _ : context [Set_clos] |- context [App] => eapply big_step_fold.AppSetStt
        | _ : context [Clos] |- context [App] => eapply big_step_fold.AppFunc
        | _ : context [Comp_clos] |- context [App] => eapply big_step_fold.AppComp
        | _ => econstructor
        end;
        try rewrite foldl_idx;
        eauto; sauto lq: on rew: off.
    - inv 1;
        try match goal with
        | H : context [foldl] |- _ =>
          rewrite foldl_idx in H;
            repeat (let H' := fresh H in destruct H as (H' & H))
        end;
          match goal with
          | H : context [true] |- _ => eapply CondT
          | H : context [false] |- _ => eapply CondF
          | H : context [Set_clos] |- context [App] => eapply AppSetStt
          | H : context [Clos] |- context [App] => eapply AppFunc
          | H : context [Comp_clos] |- context [App] => eapply AppComp
          | H : _ |- _ => econstructor
          end;
          eauto; hauto lq: on rew: off.
  Qed.

  Lemma big_step_f_mono `(B : BigStep) `(B' : BigStep) : B ⊑ B' → big_step_f B ⊑ big_step_f B'.
  Proof.
    intros HB_B' m σ p ϕ e v m'.
    inv 1; econstructor; unfold big_step in *; naive_solver.
  Defined.

  Local Unset Elimination Schemes.

  Inductive least_big_step : tree_mem → env.t value → path → phase → some_expr → value → tree_mem → Prop :=
    | big_step_fix : big_step_f least_big_step ⊑ least_big_step.

  Local Set Elimination Schemes.

  (*Check least_big_step_ind.*)

  Definition least_big_step_ind `(P : BigStep)
      (* big_step_f P ⊑ P, i.e., P is a prefixed point of big_step_f *)
      (H : ∀ m σ p ϕ e v m' (IH : big_step_f P m σ p ϕ e v m'), P m σ p ϕ e v m') :
    (* least_big_step ⊑ P, i.e., P holds for all big_step derivations *)
    ∀ m σ p ϕ e v m', least_big_step m σ p ϕ e v m' → P m σ p ϕ e v m' :=
    fix go m σ p ϕ e v m' (L : least_big_step m σ p ϕ e v m') : P m σ p ϕ e v m' :=
      match L with
      | big_step_fix m σ p ϕ e v m' F =>
        H m σ p ϕ e v m' $ big_step_f_mono least_big_step P go m σ p ϕ e v m' F
      end.

  #[export] Instance LeastBigStep : BigStep := least_big_step.
End big_step_idx.

Ltac simp :=
  repeat match goal with
  | _ => progress (simpl in *; simplify_eq)
  | _ => solve [eauto]
  end.

Section det.
  Import big_step_idx.

  Lemma big_step_deterministic : ∀ m σ p ϕ e v1 m1 v2 m2,
    { m, σ ⊢ e ⇓_p^ϕ v1, m1 } ∧ { m, σ ⊢ e ⇓_p^ϕ v2, m2 } → v1 = v2 ∧ m1 = m2.
  Proof.
    unfold big_step in *. unfold LeastBigStep in *.
    intros m σ p ϕ e v1 m1 v2 m2 (P1 & P2).
    generalize dependent v2. generalize dependent m2.
    induction P1. rename v into v1, m' into m1.
    apply big_step_equiv in IH.
    inv IH; intros;
      match goal with
      | P : context[least_big_step] |- _ =>
        inv P;
          match goal with
          | H : context[least_big_step] |- _ =>
            apply big_step_equiv in H; inv H; eauto
          end
      end;
      try rewrite forward_backward' in *;
      unfold big_step in *;
      repeat match goal with
      | H : context [least_big_step _ _ _ _ _ _ _ → _] |- _ =>
        hexploit H; eauto; intros (? & ?); clear H; simplify_eq; hauto l: on
      end.
    - rename evss into evss1, evss0 into evss2.
      generalize dependent evss2. generalize dependent m.
      induction evss1 as [|[e1 vs1] evss1' IHevss1];
        intros m H1 evss2 Hmap_fst_evss2 H2;
        destruct evss2 as [|[e2 vs2] evss2']; simp.
      destruct H1 as (mS1 & H1). destruct H2 as (mS2 & H2).
      assert (value_of_vs vs1 = value_of_vs vs2 ∧ mS1 = mS2) as (? & ?) by hauto l: on.
      assert (vs1 = vs2) by eauto using value_of_vs_inj. simp.
      hauto l: on.
    - clear t0. rename e0 into e.
      rename vi into vi1, vf into vf1, q into q1, mf into mf1, mf' into mf'1, σ' into σ'1.
      rename vi0 into vi2, vf0 into vf2, q0 into q2, mf0 into mf2, mf'0 into mf'2, σ'0 into σ'2.
      assert (vi1 = vi2 ∧ q1 = q2) as (? & ?) by hauto l: on. simp. clear_dup.
      cut (vf1 = vf2 ∧ mf1 = mf2).
      + intros (? & ?). simp.
        assert (mf'1 = mf'2 ∧ σ'1 = σ'2) as (? & ?) by hauto l: on. hauto l: on.
      + repeat match goal with
        | H : context [mbind] |- _ => clear H
        end.
        generalize dependent vi2. generalize dependent m.
        induction q2 as [|λ_ q2' IHq2]; intros m vi2 H1 H2; simp.
        hauto q: on.
  Qed.
End det.
