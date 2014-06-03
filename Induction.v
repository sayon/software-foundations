Require Export basics.
Module Induction.
Theorem andb_true_elim1: forall b c : bool, 
                           andb b c = true -> b = true.

Proof.
  intros b c. 
  destruct b, c.
  reflexivity.
  reflexivity.
  intro H.
  rewrite <- H.
  reflexivity.
  intro H.
  rewrite <- H.
  reflexivity.
Qed.


Lemma plus_0_l : forall n: nat,
                   0 + n = n.
Proof.
reflexivity.
Qed.

Theorem plus_0_r: forall n: nat,
                    n + 0 = n.
Proof.
  intros n.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.


Theorem minus_diag: forall n:nat,
                      n - n = 0.
Proof.
  intro n.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.


(* Exercise basic_induction *)

Theorem mult_0_r : forall n:nat,
                     n * 0 = 0.
Proof.
intro n.
induction n.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, 
                      S (n + m) = n + (S m).
Proof.
intros n m.
induction n, m.
reflexivity.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.


Lemma helper: forall m n : nat,
                 m + S n = S (m + n).
Proof.
  intros n m.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.


Theorem plus_comm : forall n m : nat,
                      n + m = m + n.
Proof.
  intros n m.
  induction n.
  rewrite plus_0_r.
  reflexivity.

  simpl.
  
  rewrite helper.
  rewrite IHn.
  reflexivity.
Qed.

Lemma succ_images: forall a b : nat,
                         a = b -> S a = S b.
Proof.
  intros a b H.
  rewrite H.
  reflexivity.
Qed.

Lemma plus_assoc_helper: forall a b x: nat,
                           a + b = x -> S a + b = S x.
Proof.
intros a b x.
induction b.
rewrite plus_0_r.
rewrite plus_0_r.
intro H.
rewrite H.
reflexivity.
intro H.
simpl.
rewrite H.
reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
                       n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.


(* Exercise double_plus *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus_helper: forall n: nat,
                            S (n + n) = (S n) + n.
Proof.
  intro n.
  induction n.  reflexivity.
  reflexivity.
Qed.


  
Lemma double_plus: forall n : nat,
                     double n = n + n.
Proof.
  intro n.
  induction n.
  reflexivity.
  simpl.
  rewrite plus_comm.
  rewrite <- double_plus_helper.
  rewrite IHn.
  reflexivity.
Qed.


Theorem plus_swap : forall n m p : nat, 
                      n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite plus_assoc.
  rewrite plus_assoc.
  assert ( H: m + n = n + m  ).
  rewrite plus_comm.  reflexivity.
  rewrite H. reflexivity.
Qed.

Theorem zero_no_successor : forall n:nat, 0 <> S n.
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

Theorem succ_injective : forall n m:nat, S n = S m -> n = m.
Proof.
intros.
replace (n=m) with (pred (S n) = pred (S m) ).
rewrite H.
reflexivity.
auto.
Qed.

Theorem succ_not_same: forall a: nat,
                         S a <> a.
Proof.
  intros.
  destruct a.
  unfold not.
  intro H.
  inversion H.
  assert (H' : S a <> 0 ).
  unfold not.
  intro H.
  inversion H.
  auto.
Qed.


Lemma mult_one: forall a:nat, a * 1 = a.
Proof.
  intro.
  induction a.
  reflexivity.
  simpl.
  rewrite IHa.
  reflexivity.
Qed.

Lemma plus_one_is_s: forall n: nat, n + 1 = S n.
Proof.
  intro.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem succ_plus: forall a b: nat, 
                     a + S b = S( a + b).
Proof.
intros.
rewrite plus_comm.
simpl.
rewrite plus_comm.
reflexivity.
Qed.


Theorem mult_plus_assoc_helper : forall a b: nat,
                                   a * S b = a *b + a.
Proof.
intros.
induction a.
reflexivity.
simpl.
rewrite IHa.
simpl.
rewrite plus_assoc.
rewrite succ_plus.
reflexivity.
Qed.

Theorem mult_plus_assoc: forall a b: nat,
                           a * (b + 1) = a*b + a.
Proof.
intros.
induction b.
rewrite plus_0_l, mult_0_r, mult_one.
reflexivity.
simpl.
rewrite mult_plus_assoc_helper.
rewrite plus_one_is_s.
reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
                      m * n = n * m.
Proof.
  intros m n.
  induction m.
  rewrite mult_0_r.
  reflexivity.
  simpl.
 
  replace (S m) with (m + 1).
  rewrite mult_plus_assoc.
  rewrite IHm.
  rewrite plus_comm.
  reflexivity.

  rewrite plus_one_is_s.
  reflexivity.
Qed.


Fixpoint even (n : nat) : bool :=
  match n with
      | 0 => true
      | S 0 => false
      | S (S n') => even n'
  end.

Definition notb (b : bool) : bool :=
  match b with
      | true=> false
      | false => true 
  end.

Theorem double_negation: forall  b: bool,
                           notb (notb b) = b.
Proof.
induction b.
reflexivity.
reflexivity.
Qed.


(*
Theorem even_change: forall n: nat,
                       even (S n ) = notb (even n).
Proof.
intro.
induction n.
reflexivity.
case (even( S n) ).
simpl.
 
rewrite IHn.

simpl.
destruct n.
reflexivity.




Theorem even_change_2: forall n: nat,
                       even (S ( S n) ) =  even n.
Proof.
intro.
induction n.
reflexivity.

simpl.
rewrite IHn.
rewrite double_negation.



Qed.

Theorem evenb_n__oddb_Sn : forall n : nat,
  even n = notb (even (S n)).
Proof.
intro n.
induction n.
reflexivity.
assert (even_change: forall x, even (S x) = notb (even x)).
intro x.
induction x.
induction n.
reflexivity.

intro not_prop.

rewrite 
assert (noteven: even n = false ).


case n.
reflexivity.
intros.
case (even (S (S n0))).
simpl.
case n.
*)
End Induction.

