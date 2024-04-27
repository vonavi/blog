(*|
===================================
Simply typed lambda-calculus (STLC)
===================================

http://adam.chlipala.net/cpdt/html/Hoas.html

- First-order abstract syntax (FOAS)
- Higher-order abstract syntax (HOAS)
- Weak HOAS
- Parametric HOAS (PHOAS)
|*)


(*
Require Import PeanoNat.

Definition var : Type := nat.

Lemma var_eq : forall v1 v2 : var, {v1 = v2} + {v1 <> v2}.
Proof. apply Nat.eq_dec. Qed.
*)

Parameters var : Type.

Inductive term : Type :=
| Var : var -> term
| Const : nat -> term
| Lam : (var -> term) -> term
| App : term -> term -> term.

(* Make weak HOAS looking as HOAS. *)
(* Coercion Var : var >-> term. *)

Declare Custom Entry term.
Notation "[ e ]" := e (e custom term at level 2).
Notation "( e )" := e (in custom term, e at level 2).
Notation "x" := (Var x) (in custom term, x ident).
Notation "{ c }" := (Const c) (in custom term, c constr).
Notation "\ x , e" :=
  (Lam (fun x => e)) (in custom term at level 2, x name).
Notation "e1 e2" :=
  (App e1 e2) (in custom term at level 1, left associativity).


Definition subst (e1 : term) (e2 : term) := App e1 e2.

Inductive denote : term -> nat -> Prop :=
| denote_const : forall c, denote (Const c) c
| denote_app : forall c e1 e2, App e1 e2 -> denote (App e1 e2) c.

Goal denote [{5}] 5.
Proof. constructor. Qed.


Goal [\x , x x] = [\y , y y].
Proof. reflexivity. Qed.

Create HintDb lambda.

(*|
Taking into account that all functions in Coq are total, we
firstly should answer the question: is `eval_cbv` total or
not? If not, we use predicates (inductive type). Cases with no
values correspond to `False` (empty constructor).
|*)

Inductive cbv_value : term -> Type :=
| cbv_value_var : forall x, cbv_value (Var x)
| cbv_value_const : forall b, cbv_value (Const b)
| cbv_value_abs : forall e, cbv_value (Lam e).
#[local] Hint Constructors cbv_value : lambda.

Inductive cbv_spec : term -> Type :=
| cbv_value_spec : forall e, cbv_value e -> cbv_spec e
| cbv_app_spec : forall e1 e2, cbv_spec (App e1 e2).
#[local] Hint Constructors cbv_spec : lambda.

Lemma cbvP (e : term) : cbv_spec e.
Proof. destruct e; auto with lambda. Qed.



Inductive cbn_value : term -> Type :=
| cbn_value_const : forall b, cbn_value (Const b)
| cbn_value_abs : forall e, cbn_value (Lam e).
#[local] Hint Constructors cbn_value : lambda.

Inductive cbn_spec : term -> Type :=
| cbn_value_spec : forall e, cbn_value e -> cbn_spec e
| cbn_var_spec : forall x, cbn_spec (Var x)
| cbn_app_spec : forall e1 e2, cbn_spec (App e1 e2).
#[local] Hint Constructors cbn_spec : lambda.

Lemma cbnP (e : term) : cbn_spec e.
Proof. destruct e; auto with lambda. Qed.



Fixpoint cbv_interp (e : term) : term.
Proof.
  refine (
      match cbvP e with
      | cbv_value_spec _ H => _
      | cbv_app_spec e0 e1 => _
      end).
  - refine (
        match H with
        | cbv_value_var x => Var x
        | cbv_value_const b => Const b
        | cbv_value_abs e0 => Lam (fun x => cbv_interp (e0 x))
        end).
  - refine (
        Lam (fun k =>
               App (cbv_interp e0)
                 (Lam (fun y0 => App (cbv_interp e1)
                                     (Lam (fun y1 => _)))))
      ).
    exact (App (App (Var y0) (Var y1)) (Var k)).



Parameter interp_v' : Values_v -> term.

Import SigTNotations.

Definition interp_v : term -> term.
Proof.
  intro e. pose (e; isvalue_v e).



Parameter interp_v : term -> term.


Definition interp_v' (s : Values_v) : term :=
  (match s.1 as v return isvalue_v v -> term with
   | Var x => fun _ => Var x
   | Const c => fun _ => Const c
   | Lam x a => fun _ => Lam x (interp_v a)
   | App a b => fun H => match H with end
   end) s.2.

Parameter interp_n : term -> term.

Definition interp_n' (s : Values_n) : term :=
  (match s.1 as v return isvalue_n v -> term with
   | Var x => fun H => match H with end
   | Const c => fun _ => Const c
   | Lam x a => fun _ => Lam x (interp_n a)
   | App a b => fun H => match H with end
   end) s.2.


(*|
A term is a **value** iff it is not a combination.
|*)

Inductive isvalue : term -> Prop :=
| isvalue_var : forall x, isvalue (Var x)
| isvalue_const : forall c, isvalue (Const c)
| isvalue_abs : forall x a, isvalue (Lam x a).

Definition subst (x : var) (b : term) (a : term) : term :=
  match a with
  | Var y => if var_eq x y then b else Var y
  | Const c => Const c
  | Lam x a => Lam x a
  | App a b => App a b
  end.

(*|
Taking into account that all functions in Coq are total, we
firstly should answer the question: is `eval_cbv` total or
not? If not, we use predicates (inductive type). Cases with no
values correspond to `False` (empty constructor).
|*)

Inductive eval_cbv : term -> term -> Prop :=
| cbv_const : forall c, eval_cbv (Const c) (Const c)
| cbv_abs : forall x a, eval_cbv (Lam x a) (Lam x a)
| cbv_app : eval_cbv (App a b)

Fixpoint eval_by_value (t : term) : term :=
  match t with
  | Con c => Con c
  | Var v =>



Fixpoint call_by_value (t : term) : term :=
  match t with
  | Con c => Con c
  end.

Fixpoint call_by_name (t : term) : nat :=
  match t with
  | Con c => c
  end.

Lemma equiv : forall t,
    call_by_value t = call_by_name t.
Proof.
  intro t. unfold call_by_value, call_by_name.
  now destruct t.
Qed.
