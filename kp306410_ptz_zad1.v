(*Konrad Paziewski*)
(*kp306410@students.mimuw.edu.pl*)
(*Programowanie z typami zależnymi i dowodzenie twierdzeń 2015*)
(*Zadanie 1*)
Require Import Utf8.
Require Import Arith.
Require Import CpdtTactics.

(* a *)
Definition var := nat.

(* b *)
Inductive exp : Set :=
  | Var : var -> exp
  | Const : nat -> exp
  | Add : exp -> exp -> exp
  | MakePair : exp -> exp -> exp
  | Fst : exp -> exp
  | Snd : exp -> exp.

(* c *)
Inductive cmd : Set :=
  | Return : exp -> cmd
  | Assignment : var -> exp -> cmd -> cmd.

(* d *)
Inductive val : Set :=
  | Nat : nat -> val
  | Pair : val -> val -> val.

(* e *)
Definition map (T:Type) := var -> T.
Definition varAssignment := map val.

Definition insert T (v:var) (t:T) (m : map T) : map T := 
  fun vr => if eq_nat_dec v vr then t else m vr.


(* f *)
Fixpoint eval (e : exp) (va : varAssignment) (r:val) : Prop := 
  match e, r with
  | Var v, _ => eq (va v) r
  | Const n, Nat rn => eq_nat n rn
  | Add el er, Nat rn =>  ∃ vl vr : nat, (eq_nat (plus vl vr) rn /\ eval el va (Nat vl) /\ eval er va (Nat vr))  
  | MakePair el er, Pair vl vr => eval el va vl /\ eval er va vr
  | Fst e, _ => ∃ vr:val, eval e va (Pair r vr)
  | Snd e, _ => ∃ vl:val, eval e va (Pair vl r)
  | _, _ => False
end.

(* g *)
Fixpoint run (c:cmd) (va : varAssignment) (r:val) : Prop :=
  match c with
  | Assignment v e next => ∃ ve:val, eval e va ve /\ run next (insert val v ve va) r
  | Return e => eval e va r
end.

(* h *)
Inductive type : Set :=
  | NatType : type
  | PairType : type -> type -> type.

Definition varTypings := map type.

Fixpoint valType (v:val) : type :=
  match v with
  | Nat _ => NatType
  | Pair l r => PairType (valType l) (valType r)
end.

Fixpoint expType (e:exp) (vt:varTypings) (r:type) : Prop :=
  match e, r with
  | Var v, _ => eq (vt v) r
  | Const _, NatType => True
  | Add el er, NatType =>  expType el vt NatType /\ expType er vt NatType
  | MakePair el er, PairType tl tr => expType el vt tl /\ expType er vt tr
  | Fst e, _ => ∃ tr:type, expType e vt (PairType r tr)
  | Snd e, _ => ∃ tl:type, expType e vt (PairType tl r)
  | _, _ => False
end.

Fixpoint cmdType (c:cmd) (vt : varTypings) (r:type) : Prop :=
  match c with
  | Assignment v e next => ∃ et:type, expType e vt et /\ cmdType next (insert type v et vt) r
  | Return e => expType e vt r
end.

(* j *)
Definition varsType (va : varAssignment) (vt : varTypings) : Prop :=
  ∀ v : var, eq (valType (va v)) (vt v).

(* k *)
Lemma expCorrect: ∀ va: varAssignment, ∀ vt: varTypings, varsType va vt -> 
         ∀ e : exp, ∀ t: type, (expType e vt t -> ∃ v, eval e va v /\ eq (valType v) t).
induction e; crush.
(* Var _ *)
exists (va v); crush.

(*Const n*)
exists (Nat n); destruct t; crush.

(*Add _ _ *)
destruct t; crush.
assert (N1: ∃ v : val, eval e2 va v ∧ valType v = NatType).
crush.
destruct N1.
destruct x; crush.

assert (N2: ∃ v : val, eval e1 va v ∧ valType v = NatType).
crush.
destruct N2.
destruct x; crush.

exists (Nat (n0 + n)).
crush.
exists n0.
exists n.
crush.

(*MakePair _ _*)
destruct t; crush.
assert (N1: ∃ v : val, eval e2 va v ∧ valType v = t2).
crush.
destruct N1.

assert (N2: ∃ v : val, eval e1 va v ∧ valType v = t1).
crush.
destruct N2.

exists (Pair x0 x).
crush.

(*Left*)
assert (N: ∃ v : val, eval e va v ∧ valType v = (PairType t x)).
crush.
destruct N; crush.
destruct x0; crush.
exists x0_1.
crush.
exists x0_2.
crush.

(*Right*)
assert (N: ∃ v : val, eval e va v ∧ valType v = (PairType x t)).
crush.
destruct N; crush.
destruct x0; crush.
exists x0_2.
crush.
exists x0_1.
crush.
Qed.

(* l *)
Lemma insertCorrect : ∀ va: varAssignment, ∀ vt: varTypings, varsType va vt ->
   ∀ v : val, ∀ x : var, varsType (insert val x v va) (insert type x (valType v) vt). 
crush.
unfold varsType.
crush.
unfold insert.
simpl.
destruct (eq_nat_dec); crush.
Qed.

Lemma cmdCorrect' : ∀ c: cmd, ∀ va: varAssignment, ∀ vt: varTypings, varsType va vt -> 
   ∀ t: type, (cmdType c vt t -> ∃ v, run c va v /\ eq (valType v) t).
induction c; crush.
(* Return *)
apply (expCorrect va vt); crush.
(* Assignment *)
assert (N : ∃ ve, eval e va ve /\ eq (valType ve) x).
apply (expCorrect va vt); crush.
destruct N.
assert (M: varsType (insert val v x0 va) (insert type v (valType x0) vt)).
apply (insertCorrect va vt); crush.
assert (P : ∃ v0 : val, run c (insert val v x0 va) v0 ∧ valType v0 = t).
apply (IHc (insert val v x0 va) (insert type v (valType x0) vt)); crush.
destruct P.
exists x1.
crush.
exists x0.
crush.
Qed.

Lemma cmdCorrect: ∀ va: varAssignment, ∀ vt: varTypings, varsType va vt -> 
   ∀ c: cmd, ∀ t: type, (cmdType c vt t -> ∃ v, run c va v /\ eq (valType v) t).
crush.
apply (cmdCorrect' c va vt); crush.
Qed.