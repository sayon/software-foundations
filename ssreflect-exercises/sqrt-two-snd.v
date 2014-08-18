Require Import ssreflect ssrbool eqtype ssrnat.

Section SqrtTwoNotInQ.

Lemma or_b_b: forall b, b || b = b.
Proof.
  move=> b. 
  by case b.
Qed.

Lemma and_a_a: forall b, b && b = b.
Proof.
  move => b.
  by case b.
Qed.

Lemma odd_injective: forall n m, n = m -> (odd n = odd m).
Proof.
  move => n m.
  by move => ->.
Qed.

Lemma eq_half n: odd n = false -> n = n./2.*2.
Proof.
  move => Hodd.
  move: (odd_double_half n) => Hn.
  by   rewrite Hodd in Hn.
Qed.


Lemma double_eq n m: n.*2 = m.*2 -> n = m.
Proof.
  rewrite <- !mul2n.
  move /eqP.
  rewrite  eqn_mul2l.
  by move /eqP.
Qed.

Lemma eq_halving: forall n m, n = m -> odd n = false -> odd m = false -> n./2 = m./2.
Proof.
  move => n m Hnm Hneven Hmeven .
  move: (eq_half n) (eq_half m) => Hn Hm.
  rewrite Hn in Hnm.   
  rewrite Hm in Hnm. 
  by apply double_eq in Hnm.   
  by []. by [].
Qed.
Lemma odd_sq m: odd m = odd (m * m).
Proof.
  rewrite odd_mul.
  by rewrite and_a_a.
Qed.

Lemma odd_even_eq m: forall n, odd m -> m = 2 * n -> False.
Proof.
  move => n Hodd Heq.
  apply odd_injective in Heq.
  rewrite odd_mul in Heq. 
  by rewrite Hodd in Heq.
Qed.


Lemma even_div_2 n: odd n = false -> n = (n./2).*2.
Proof.
  move : (odd_double_half n) => Hn Hoddn.
  rewrite Hoddn in Hn.
  by symmetry.
Qed.

Lemma square_div_square n m d: n = d * m -> d != 0-> n*n = d * d * (m * m).
  move=> -> =>Hd.
  rewrite - mulnA.
  rewrite - mulnA.
  apply /eqP.
  rewrite (eqn_mul2l d ).
  case (d == 0). by [].
  simpl.
  rewrite mulnA mulnCA.
  by rewrite mulnA.
Qed.

Lemma even_mul_2 n m: n = 2 * m -> odd n = false.
Proof.
  rewrite mul2n => ->.
  exact: odd_double.
Qed.
    

Lemma trans n m: n*n = 2*(m*m) -> (n./2) * (n./2) = 2*((m./2) * (m./2)).
Proof.
  move => Hnm.
  assert( Heven: odd n = false ).
  apply odd_injective in Hnm.
  by rewrite !odd_mul  !and_a_a in Hnm.
  
  assert( Hn: n = 2 * n./2).
  rewrite mul2n.
  by apply even_div_2.
  
  move: (square_div_square n n./2 2 Hn) => Hn'.
  rewrite Hn' in Hnm ; last by [].
  move/eqP in Hnm.
  rewrite -mulnA eqn_mul2l in Hnm.
  simpl in Hnm.
  
  assert (Hm: m = 2* (m./2)).
  move/eqP in Hnm.
  symmetry in Hnm.
  apply even_mul_2 in Hnm.
  rewrite -odd_sq in Hnm.
  rewrite mul2n.
  by apply (even_div_2 m).

  rewrite  Hm -mulnA eqn_mul2l in Hnm.
  simpl in Hnm.
  move/eqP in Hnm. symmetry in Hnm.
  rewrite mulnC -mulnA in Hnm.  
  by symmetry.
Qed.

Lemma leq_n_succ n: n <= n.+1.
  by  elim n => //=. 
Qed.

Lemma half_succ_leq n:  (n.+1)./2 <= n.
Proof.
  move: (odd_double_half n) =>Hodd.
  symmetry in Hodd.
  rewrite {2} Hodd.
  simpl.
  rewrite uphalf_half leq_add2l -addnn.
  assert (H: n./2 + 0 <= n./2 + n./2).
  by rewrite leq_add2l.
  by rewrite addn0 in H.
Qed.

Lemma leq_split n m: n <= m.+1 -> (n == m.+1) || (n <= m).
  rewrite (leq_eqVlt n (m.+1) ).
  by  case (n == m.+1).
Qed.
Lemma leq_n_half n : n./2 <= n.
  induction n.
    by [].
  simpl.
  rewrite uphalf_half.

  case( odd n).
  by rewrite add1n.
  apply leq_trans with n; first by rewrite add0n.
  by [].
Qed.

  
Lemma leq_succ_half_leq n m: n <= m.+1 -> n./2 <= m.
Proof.
  move => Hnm; apply leq_split in Hnm. 
  move/orP in Hnm.
  inversion Hnm.
  move /eqP in H. rewrite H.
  by apply half_succ_leq.
  apply leq_trans with n./2.
  by [].
  apply leq_trans with n.
  by apply leq_n_half.
  exact: H.
Qed.

Lemma half_0 n: n./2 = 0 <-> n == 0 \/ n == 1.
Proof.
  split.
  move: (odd_double_half n) => Hodd.
  move=> Hn. 
  rewrite Hn  double0 addn0 in Hodd.
  move:   ( leq_b1 (odd n)) => Hrange.
  destruct n.
  by left.
  destruct n.
  by right.
  by destruct n.
  
  move=> Hn. inversion Hn; move /eqP in H; by rewrite H.
Qed.

Lemma mul_greater a b c: a * b = c -> ( a <= c )  && (b <= c).
Proof.
move: (leq_total a c) => Hac. 
move: (leq_total b c) => Hbc.
move /orP in Hac.
move /orP in Hbc.
 inversion Hac; inversion Hbc; try rewrite H; try rewrite H0; try simpl.
  by [].
  induction a.
    by [].
simpl.

     by rewrite H H0.
  
by [].

Lemma aux n p:  n * n = 2 * p * p  -> p = 0 .
  elim:  n {1 3 4}n (leqnn n) p.

  (* base *)
  move => n. rewrite leqn0.
  move /eqP => ->. by case => p.
  
  (* trans *)
  move=> n H m Hleq p Hmp.
  rewrite -mulnA in Hmp.
  move: (trans m p Hmp) => Hmptr.
  assert (Hm: m./2 <= n). by apply leq_succ_half_leq in Hleq.
    
  assert(Hp:  p./2 = 0).
  apply ( H (m./2) Hm (p./2) ).
  by rewrite mulnA in Hmptr.
  apply half_0 in Hp.
  inversion Hp; move /eqP in H0; first by [].
  rewrite H0 !muln1 in Hmp.
  rewrite H0 in Hmptr.
  simpl in Hmptr.
  rewrite !muln0 in Hmptr.

  compute in Hmp.
  
  by apply/eqP.
  move /eqP
  apply H with m./2.
.

  by  apply leq_succ_half_leq.
    
  assert(Hmhalf:  m./2 <= n ).
  by apply leq_succ_half_leq.
  apply H with (m./2) p  in Hmhalf .
  rewrite Hmhalf in Hmp. rewrite Hmhalf.
  by [].
  apply H with (m./2) p in Hmhalf.
 
  apply leq_succ_half_leq.

  rewrite /leq.
  rewrite /leq in Hleq.
  case Hm: (m == n.+1).
  move /eqP in Hm.
    
  induction m.
  by [].
    


  assert (Heven_m: odd m = false). by rewrite  (odd_sq m) Hmp !odd_mul.

  assert (Heven_p: odd p = false). rewrite odd_sq. 
    
  rewrite (odd_even_eq m p) in Hmp.

  apply (odd_even_eq (m*m) (p*p)).  [ contradiction | rewrite -mulnA in Hmp].
  move: (helper m p Hmp Hmodd) => Hhalf.
  



    
  apply Hmoddeven in (odd_sq m).
    
 
  move => n H m Hleq p Hnm.
  case Hn_odd: (odd n).
  move: (helper n p) => Haux.
  assert (Hs: (n.+1 * n.+1)./2 = p * p).
  apply Haux; by [].
  
  
  subst.

  apply (H m).
  rewrite leq_eqVlt in Hleq.
  move /orP in Hleq.
  inversion Hleq.
  move /eqP in H0.
  rewrite <-H0 in Hnm.
  
  assert( m = 0).

  apply (H m).
    

  apply (H m).
  

(*

 forall n0 : nat,
 (forall n1 : nat, n1 <= n0 -> forall p : nat, n0 * n0 = 2 * p * p -> p = 0) ->
 forall n1 : nat,
 n1 <= n0.+1 -> forall p : nat, n0.+1 * n0.+1 = 2 * p * p -> p = 0*)



(*
Theorem lt_le_trans : forall n m p, n < m -> m <= p -> n < p.
Proof.
  move => n m p Hnm.
  rewrite leq_eqVlt.
  move/orP.  move => Hmp. inversion Hmp.
  move/eqP in H.
  by rewrite <- H.
  by apply ltn_trans with m.
Qed.


Variable f: nat -> nat.


Definition ltof (a b:nat) := f a < f b.


Theorem well_founded_ltof : well_founded ltof.
Proof.
  red in |- *.
  cut (forall n (a:nat), f a < n -> Acc ltof a).
  intros H a; apply (H (S (f a))); auto with arith.
  induction n.
  intros; absurd (f a < 0); auto with arith.
  intros a ltSma.
  apply Acc_intro.
  unfold ltof in |- *; intros b ltfafb.
  apply IHn.
  apply lt_le_trans with (f a); auto with arith.
Qed.

Check well_founded_ltof.

Definition lt_wf := well_founded_ltof nat (fun m : nat => m).

Print lt_wf.

Lemma lt_wf : well_founded lt.
Proof.
  exact (well_founded_ltof (fun m => m)).

  unfold well_founded.

        lt_wf = well_founded_ltof nat (fun m : nat => m).



Lemma lt_wf_ind :
  forall n (P:nat -> Prop), (forall n, (forall m, lt m  n -> P m) -> P n) -> P n.
Proof.
  intro p; intros; elim (lt_wf p); auto with arith.
Qed.




Theorem well_founded_ltof : well_founded ltof.

Variable A : Type.
Variable R : A -> A -> Prop.
Variable f : A -> nat.


Inductive Acc (x: A) : Prop :=
     Acc_intro : (forall y:A, R y x -> Acc y) -> Acc x.

Definition well_founded := forall a:A, Acc a.

 
Check Acc_rect.

Check 
  

Theorem well_founded_ltof : well_founded ltof.
Proof.
  red in |- *.
  cut (forall n (a:A), f a < n -> Acc ltof a).
  intros H a; apply (H (S (f a))); auto with arith.
  induction n.
  intros; absurd (f a < 0); auto with arith.
  intros a ltSma.
  apply Acc_intro.
  unfold ltof in |- *; intros b ltfafb.
  apply IHn.
  apply lt_le_trans with (f a); auto with arith.
Defined.





Lemma lt_wf_ind :
  forall n (P:nat -> Prop), (forall n, (forall m, m < n -> P m) -> P n) -> P n.
Proof.
  intro p; intros; elim (lt_wf p); auto with arith.
Qed.

T
heorem wf_ind: forall n (P:nat -> Prop), (forall n, (forall m, m < n -> P m) -> P n) -> P n.
Proof.
  move => n P H.
  apply H.
  move => m Hmn. 
  induction m; first by ( apply H;  move => n0 HPn0).
x0.
      


Theorem well_founded_ltof : well_founded ltof.
Proof.
  red in |- *.
  cut (forall n (a:A), f a < n -> Acc ltof a).
  intros H a; apply (H (S (f a))); auto with arith.
  induction n.
  intros; absurd (f a < 0); auto with arith.
  intros a ltSma.
  apply Acc_intro.
  unfold ltof in |- *; intros b ltfafb.
  apply IHn.
  apply lt_le_trans with (f a); auto with arith.
Defined.

Definition ltof (a b:A) := f a < f b.




Lemma lt_wf_ind :
  forall n (P:nat -> Prop), (forall n, (forall m, m < n -> P m) -> P n) -> P n.
Proof.
  move=> n P H.
  
      
  auto with arith.
 



Theorem nat_wf_ind: forall (n : nat) (P : nat -> Prop),                                                              
       (forall n0 : nat, (forall m : nat, m < n0 -> P m) -> P n0) -> P n .
Proof.
  intros.
  elim n.
  apply H;  by move=>  m mlt0.

  
  clear n.
  assert ( forall n0 : nat, (forall m : nat, m < n0 -> P m)).
  intros.
  apply H.
  intros.
  
  
  apply H.
  intros.
  induction m.
  apply H.
  by move => m Hm.
  apply H.
    

  move: (H n.+2) =>  H'.
  


  apply H.
  induction m.
  move => H'.
  apply H.
  by move=> m Hm.
  move=> Hm.
  apply H.
  move=>  m0 Hm0.
  
  move: (H (n.+1)) => H0.
  move: (H n) => H1.
  apply H0.
  intros.
  
  generalize dependent n.
H.

  move: (H (n.+1)) => HSn.
  generalize dependent n.

Theorem nat_lt_ind: forall n, (forall m, m < n -> (forall p, m^2 = 2 *p^2 -> p =

Lemma nat_wf_ind
*)