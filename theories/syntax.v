From Coq Require Import ZArith String.
From stdpp Require Import base.

Variant hook_tag := Hook_free | Hook_full.
Variant const := Unit | Bool : bool → const | Int : Z → const.
Variant uop := Not | Uplus | Uminus.
Variant bop := Eq | Lt | Gt | Ne | Le | Ge | And | Or | Plus | Minus | Times.

Inductive expr : hook_tag → Type :=
  | Const {tag} (c : const) : expr tag
  | Var {tag} (x : string) : expr tag
  | View {tag} (es : list (expr Hook_free)) : expr tag
  | Cond {tag} (pred con alt : expr Hook_free) : expr tag
  | Fn {tag} (param : string) (body : expr Hook_free) : expr tag
  | App {tag} (fn arg : expr Hook_free) : expr tag
  | Let {tag} (id : string) (bound body : expr Hook_free) : expr tag
  | Stt {tag} (lbl : nat) (stt set : string) (init : expr Hook_free) (stt_body : expr Hook_full) : expr tag
  | Eff (e : expr Hook_free) : expr Hook_full
  | Seq {tag} (e1 e2 : expr tag) : expr tag
  | Uop {tag} (op : uop) (arg : expr Hook_free) : expr tag
  | Bop {tag} (op : bop) (left right : expr Hook_free) : expr tag.

Record comp := {
  comp_name : string;
  comp_param : string;
  comp_body : expr Hook_full
}.

Inductive prog :=
  | Expr : expr Hook_free → prog
  | Comp : comp → prog → prog.
