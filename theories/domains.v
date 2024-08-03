From Coq Require Import ZArith String.
From stdpp Require Import base gmap.
From theories Require Import syntax.

Module env.
  Definition t value := gmap string value.
End env.

Section RecordDefs.
  Context {value : Type}.

  Record comp_spec := {
    cs_comp : comp;
    cs_env : env.t value;
    cs_arg : value;
  }.

  Record clos := {
    param : string;
    body : expr Hook_free;
    env : env.t value;
  }.

  Record comp_clos := {
    cc_comp : comp;
    cc_env : env.t value;
  }.
End RecordDefs.

Global Arguments comp_spec : clear implicits.
Global Arguments clos : clear implicits.
Global Arguments comp_clos : clear implicits.

Definition label := nat.
Definition path := nat.

Record set_clos := {
  ℓ : label;
  pt : path;
}.

Inductive value :=
  | Unit : value
  | Bool : bool → value
  | Int : Z → value
  | View_spec : list view_spec → value
  | Clos : clos value → value
  | Set_clos : set_clos → value
  | Comp_clos : comp_clos value → value
  | Comp_spec : comp_spec value → value
with view_spec :=
  | Vs_null : view_spec
  | Vs_int : Z → view_spec
  | Vs_comp : comp_spec value → view_spec.

Notation "'unit'" := Unit (at level 0).
Coercion Bool : bool >-> value.

Definition value_eqb (x y : value) : bool :=
  match x, y with
  | Unit, Unit => true
  | Bool b1, Bool b2 => Bool.eqb b1 b2
  | Int i1, Int i2 => Z.eqb i1 i2
  | _, _ => false
  end.

Definition job_q := list (clos value).
Definition st_store := gmap label (value * job_q).

Variant phase := P_init | P_update | P_retry | P_effect.
Variant decision := Idle | Retry | Update.

#[export] Instance PhaseEqDec : EqDecision phase.
Proof.
  unfold EqDecision. unfold Decision. decide equality.
Defined.

#[export] Instance DecisionEqDec : EqDecision decision.
Proof.
  unfold EqDecision. unfold Decision. decide equality.
Defined.

Record node := mk_node {
  cs : comp_spec value;
  dec : decision;
  ρ_s : st_store;
  eff_q : job_q;
}.

Variant part_view :=
  | Root
  | Node : node → part_view.

Variant tree :=
  | Leaf_null
  | Leaf_int : Z → tree
  | Path : path → tree.

Record entry := {
  π : part_view;
  children : list tree;
}.

Definition tree_mem := gmap path entry.
