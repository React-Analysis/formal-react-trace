Set Warnings "-uniform-inheritance".
From Coq Require Import ZArith String.
From stdpp Require Import base gmap.
From theories Require Import syntax.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Declare Custom Entry react.
Declare Scope react_scope.
Bind Scope react_scope with expr.
Delimit Scope react_scope with react.

Notation "'<{' e '}>'" := e%react (e custom react at level 99).

Notation "'(' x ')'" := x (in custom react, x at level 99) : react_scope.
Notation "x" := x (in custom react at level 0, x constr at level 0) : react_scope.

Notation "'()'" := (Const Unit) (in custom react at level 0) : react_scope.
Coercion Bool : bool >-> const.
Coercion Int : Z >-> const.
Coercion Const : const >-> expr.

Notation "'true'" := (Const true%react) (in custom react at level 0) : react_scope.
Notation "'false'" := (Const false%react) (in custom react at level 0) : react_scope.

Coercion Var : string >-> expr.
Coercion View : list >-> expr.
Notation "'view' es" := (View (es : list (expr Hook_free))) (in custom react at level 89, es constr at level 99) : react_scope.
Notation "'view' '[' ']'" := (View [ ]) (in custom react at level 89) : react_scope.
Notation "'view' '[' x ']'" := (View [ x : expr Hook_free ]) (in custom react at level 89, x custom react at level 99) : react_scope.
Notation "'view' '[' x ; y ; .. ; z ']'" := (View (cons (x : expr Hook_free) (cons (y : expr Hook_free) .. (cons (z : expr Hook_free) nil) ..)))
  (in custom react at level 89, x custom react at level 99, y custom react at level 99, z custom react at level 99) : react_scope.
Notation "f x" := (App f x) (in custom react at level 1, left associativity) : react_scope.
Notation "'fun' x '⇒' e" := (Fn x e)
  (in custom react at level 90, x at level 99, e custom react at level 99, left associativity) : react_scope.

Notation "'if' pred 'then' con 'else' alt" := (Cond pred con alt)
  (in custom react at level 89, pred custom react at level 99, con custom react at level 99, alt custom react at level 99, left associativity) :
  react_scope.
Notation "'let' '(' stt ',' set ')' '=' 'useState' '@' ℓ  init 'in' e" := (Stt ℓ%nat stt set init e)
  (in custom react at level 89, stt custom react at level 99, set custom react at level 99, ℓ custom react at level 0, init custom react at level 99, e custom react at level 99, left associativity) :
  react_scope.

Module examples.
  Check <{ if "x" then "y" else "z" }>.
  Check <{ view [ "x"; "y"; 3 ] }>.
  Definition es : list (expr Hook_free) := [ <{ if "x" then "y" else "z" }> ].
  Check <{ view es }>.
  Check <{ if true then view [ "y" ] else "x" }>.
  Check <{ fun "x" ⇒ "x" }>.
  Check <{ let ("stt", "set") = useState@0 "init" in "e" }>.
End examples.
