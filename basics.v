
Module Playground1.

Inductive bool : Type :=
  | False
  | True
.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat
.

Definition one := S O.

Definition pred (n: nat) := 
  match n with 
  | O => O
  | S n => n
  end.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.


Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Notation "x + y" := (plus x y) 
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x - y" := (minus x y) 
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x * y" := (mult x y) 
                       (at level 40, left associativity) 
                       : nat_scope.


Fixpoint eq (n m : nat) : bool :=
  match n, m with
  | O, O => True
  | O, S _ => False
  | S _, O => False
  | S n', S m' => eq n' m'
  end.

Fixpoint leq (n m : nat) : bool :=
  match n,m with 
  | O, O => True
  | O, S _ => True
  | S _, O => False
  | S n', S m' => leq n' m'
  end.

Definition andb ( n m : bool) : bool := 
  match n,m with
  | True, True => True
  | _, _ => False
  end.
Definition notb (n:bool) : bool :=
  match n with
  | True => False
  | False => True
  end.
Definition orb (n m: bool) : bool :=
  match n,m with
    |False,False => False
    |_,_ => True
  end.

Definition less (n m: nat) : bool :=
  andb  (leq n m) (notb (eq n m ) ).  


Example test_less: (less (S(S(S(S O)))) (S(S(S O) ))) = False.
Proof.
simpl.
compute.
reflexivity.
Qed.


(*Now, the real deal!*)

Theorem zero_absorption_l: forall n: nat , O + n = n.
Proof.
intros n.
reflexivity.
Qed.

Theorem one_absorption_l: forall n: nat ,
                            mult  O n = O.
Proof.
intros n.
simpl.
compute.
reflexivity.
Qed.

Theorem plus_id_example: forall n m : nat , 
                           n = m -> n + n = m + m.
Proof.
intros n m.
intros H.
rewrite <- H.
reflexivity.
Qed.

(* Exercise *)


Theorem plus_id_exercise: forall n m o: nat, 
                            n=m -> m = o -> n + m = m + o.
intros n m o.
intros H1 H2.
rewrite -> H1.
rewrite -> H2.
reflexivity.
Qed.

(* Exercise *)


Theorem mult_S_1 : forall n m : nat,
                     m = S n -> 
                     m * (S O + n) = m * m.
Proof.
intros n m H.
simpl.
rewrite -> H.
reflexivity.
Qed.


Theorem plus_1_neq_0: forall n : nat, 
                        eq  (n + one) O = False.
Proof.
intros n.
destruct n as [| n'].
simpl.
reflexivity.
simpl.
reflexivity.
Qed.


Theorem double_negation: forall b : bool,
                           notb (notb b) = b.
Proof.
destruct b as [|b'].
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

(* Exercise *)
Theorem identity_fn_applied_twice: forall 
                                     ( f : bool -> bool ), 
                                     ( forall (x:bool), f x = x ) ->
                                     forall (b: bool), f (f b) = b.
Proof.
intros f H b.
rewrite -> H.
rewrite -> H.
reflexivity.
Qed.

(* Exercise *)

Theorem not_fn_applied_twice: forall 
                                     ( f : bool -> bool ), 
                                     ( forall (x:bool), f x = notb x ) ->
                                     forall (b: bool), f (f b) = b.
Proof.
intros f H b.
rewrite -> H.
rewrite -> H.
destruct b as [|b'].
reflexivity.
reflexivity.
Qed.


(* Exercise  i  failed

Lemma and_with_false: forall (b: bool), 
                        and False b = False.
Proof.
intro b.
reflexivity.
Qed.




Lemma or_with_true: forall (b: bool),
                      or True b = True.
Proof.
intro b.
reflexivity.
Qed.


Theorem andb_eq_orb :   forall (b c : bool),
                          (and b c = or b c) ->
                          b = c.

Proof.
  destruct b.
  intros c.
  intros H.
  rewrite <- or_with_true with c.
  rewrite <- H.
  destruct c.
  reflexivity.
  reflexivity.
  intros c.
  intros H.
  rewrite <- andb_always_false with c.
  rewrite -> H.
  destruct c.
  reflexivity.
  reflexivity.
Qed.

Proof.
  destruct b.
intros c H.
rewrite <- and_with_false with c.


  intros b c.
  destruct b. destruct c.
  reflexivity.
  simpl.
  intro H.
reflexivity.
  intro H. 
  rewrite H.
reflexivity.
simpl.

reflexivity.

Theorem zero_absorption_r: forall n: nat, n + O = n.
intros n.

compute.
reflexivity.
Qed.

Theorem plus_comm: forall (n m: nat), n + m = m + n.
Proof.

intros n m.*)




End Playground1.
