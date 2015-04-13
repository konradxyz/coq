Require Import CpdtTactics.

(** ** Source Language *)

Inductive binop : Set := Plus | Times.

Definition var := nat.

Inductive exp : Set :=
| Var : nat -> exp
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
    | Plus => plus
    | Times => mult
  end.

Fixpoint expDenote (val : var -> nat) (e : exp) : nat :=
  match e with
    | Var v => val v 
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote val e1) (expDenote val e2)
  end.

Definition val (n : nat) := n.

Eval simpl in expDenote val (Const 42).
(** [= 42 : nat] *)

Eval simpl in expDenote val (Binop Plus (Const 2) (Const 2)).
(** [= 4 : nat] *)

Eval simpl in expDenote val (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).
(** [= 28 : nat] *)

Eval simpl in expDenote val (Binop Times (Binop Plus (Var 5) (Const 2)) (Const 7)).
(** [= 49 : nat] *)


Fixpoint cf (e : exp) : exp :=
  match e with
    | Binop b e1 e2 => 
        let e1' := cf e1 in
        let e2' := cf e2 in
        match e1', e2' with
        | Const c1, Const c2 => Const (binopDenote b c1 c2)
        | _, _ => Binop b e1' e2'
        end
    | e' => e'
  end.

Eval simpl in (cf (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))).

Eval simpl in (cf (Binop Times (Binop Plus (Var 5) (Const 2)) (Const 7))).

Eval simpl in (cf (Binop Times (Binop Plus (Const 2) (Const 2)) (Var 7))).

Lemma cf_good : forall v e, expDenote v (cf e) = expDenote v e.
induction e; simpl.
+ trivial.
+ trivial.
+ destruct (cf e1); destruct (cf e2).
 crush.
(*
Hint Extern 1 (expDenote ?V (match ?E with Var _ => _ | Const _ => _ | Binop _ _ _ => _ end) = _) => 
 destruct E; crush.
induction e; crush.
*)

Qed.

