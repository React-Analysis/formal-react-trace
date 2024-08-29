From stdpp Require Import base list.
From theories Require Import notations.
From Hammer Require Import Hammer Tactics.

Definition bin_rel R A := R -> A -> A -> Prop.

(* x -[r]→ x' means : ℛ x r x' *)
(* xi = x1 -[r1]→ x2 -[r2]→ x3 → ⋯ -[rn]→ xSn = xf  *)
(* xs = [xSn; ⋯; x1] *)
(* rs = [rn; ⋯; r1] *)
Lemma foldr_idx_1 {A R} (rs : list R) (xi xf : A) (ℛ : bin_rel R A) :
  foldr (λ rk Ik, λ xSk, ∃xk, Ik xk ∧ ℛ rk xk xSk) (λ x, x = xi) rs xf →
  ∃ (xs : list A),
    xs !! |rs| = Some xi ∧
    xs !! 0 = Some xf ∧
    ∀ k,
      k < |rs| →
      ∃ rk xk xSk,
        rs !! k = Some rk ∧
        xs !! (S k) = Some xk ∧
        xs !! k = Some xSk ∧
        ℛ rk xk xSk.
Proof.
  revert xf.
  induction rs as [|r rs IHrs]; intros xf Hfoldr.
  - unfold foldr in Hfoldr.
    exists [xi]. sauto lq: on.
  - destruct Hfoldr as (x & Hfoldr & Hr_x_xf).
    specialize (IHrs x).
    apply IHrs in Hfoldr. destruct Hfoldr as (xs & Hxs_at_rs & Hxs_at_0 & Hfoldr).
    exists (xf :: xs).
    repeat split; auto.
    intros k Hk_lt.
    destruct k; simpl in *; fcrush.
Qed.

Lemma foldr_idx_2 {A R} (rs : list R) (xi xf : A) (ℛ : bin_rel R A) :
  (∃ (xs : list A),
    xs !! |rs| = Some xi ∧
    xs !! 0 = Some xf ∧
    ∀ k,
      k < |rs| →
      ∃ rk xk xSk,
        rs !! k = Some rk ∧
        xs !! (S k) = Some xk ∧
        xs !! k = Some xSk ∧
        ℛ rk xk xSk) →
  foldr (λ rk Ik, λ xSk, ∃xk, Ik xk ∧ ℛ rk xk xSk) (λ x1, x1 = xi) rs xf.
Proof.
  revert xf.
  induction rs as [|r rs IHrs]; intros xf; simpl in *.
  - naive_solver.
  - destruct 1 as (xs & Hxs_at_Srs & Hxs_at_0 & Hidx).
    destruct (Hidx 0) as (rk & xk & xf' & Hr_eq_rk & Hxs_at_1 & Hxf_eq_xf' & Hxk_xSk); [lia|].
    inv Hr_eq_rk.
    exists xk. split; auto.
    specialize (IHrs xk). apply IHrs.
    destruct xs as [|x xs']; [discriminate|]; simpl in *. inv Hxs_at_0.
    exists xs'. repeat split; auto.
    intros k Hk_lt_rs.
    destruct (Hidx (S k)); hauto l: on.
Qed.

Lemma foldr_idx {A R} (rs : list R) (xi xf : A) (ℛ : bin_rel R A) :
  foldr (λ rk Ik, λ xSk, ∃xk, Ik xk ∧ ℛ rk xk xSk) (λ x1, x1 = xi) rs xf ↔
  ∃ (xs : list A),
    xs !! |rs| = Some xi ∧
    xs !! 0 = Some xf ∧
    ∀ k,
      k < |rs| →
      ∃ rk xk xSk,
        rs !! k = Some rk ∧
        xs !! (S k) = Some xk ∧
        xs !! k = Some xSk ∧
        ℛ rk xk xSk.
Proof.
  split.
  - apply foldr_idx_1.
  - apply foldr_idx_2.
Qed.

Definition flip_prop {A B C} (f : A → B → C → Prop) x y := f y x.

Lemma foldl_foldr_equiv {A B}
    (f : (A → Prop) → B → A → Prop) (I : A → Prop) (x : A) (l : list B) :
  foldl f I l x ↔ foldr (flip_prop f) I (rev l) x.
Proof.
  split;
    revert I;
    induction l as [|b l IHl]; auto; simpl in *;
    intro I;
    rewrite foldr_app; naive_solver.
Qed.

Lemma foldl_idx {A R} (rs : list R) (xi xf : A) (ℛ : bin_rel R A) :
  foldl (λ Ik rk, λ xSk, ∃xk, Ik xk ∧ ℛ rk xk xSk) (λ x1, x1 = xi) rs xf ↔
  ∃ (xs : list A),
    xs !! |rs| = Some xi ∧
    xs !! 0 = Some xf ∧
    ∀ k,
      k < |rs| →
      ∃ rk xk xSk,
        rev rs !! k = Some rk ∧
        xs !! (S k) = Some xk ∧
        xs !! k = Some xSk ∧
        ℛ rk xk xSk.
Proof.
  rewrite foldl_foldr_equiv.
  rewrite <- rev_length.
  apply foldr_idx.
Qed.

(* modus ponens *)
Lemma mp: ∀ P Q: Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.

Ltac hexploit x := eapply mp; [eapply x|].

Lemma forward_backward {A R}
    (rs : list R) (Ii If : A → Prop) (ℛ : bin_rel R A) :
  (∃ xf, If xf ∧ foldl (λ Ik rk, λ xSk, ∃ xk, Ik xk ∧ ℛ rk xk xSk) Ii rs xf) ↔
  (∃ xi, Ii xi ∧ foldr (λ rk ISk, λ xk, ∃ xSk, ISk xSk ∧ ℛ rk xk xSk) If rs xi).
Proof.
  revert Ii If.
  induction rs as [|r rs IHrs]; simpl in *; [naive_solver|].
  intros. split.
  - intros (xf & HIf_xf & Hfoldl).
    match goal with
    | Hfoldl : foldl _ ?Ii _ _ |- _ => specialize (IHrs Ii If)
    end.
    hexploit IHrs. naive_solver.
  - sauto lq: on.
Qed.

Lemma forward_backward' {A R} (rs : list R) (xi xf : A) (ℛ : bin_rel R A) :
  foldl (λ Ik rk, λ xSk, ∃ xk, Ik xk ∧ ℛ rk xk xSk) (λ x1, x1 = xi) rs xf ↔
  foldr (λ rk ISk, λ xk, ∃ xSk, ISk xSk ∧ ℛ rk xk xSk) (λ xSn, xSn = xf) rs xi.
Proof.
  match goal with
  | |- foldl _ ?Ii _ _ ↔ foldr _ ?If _ _ => pose proof forward_backward rs Ii If ℛ
  end.
  qauto l: on.
Qed.
