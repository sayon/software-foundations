Require Import ssreflect ssrbool eqtype ssrnat.

Section SqrtTwoNotInQ.

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

Lemma mul_greater a c: a <> 0 -> a * a = c -> ( a <= c ).
Proof.
move => Ha => <-.
apply leq_pmulr.
move /eqP in Ha.
by rewrite lt0n.
Qed.

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
  case Hmz: (m == 0 );move /eqP in Hmz. by rewrite Hmz in Hmp.
  move: (mul_greater m 2 Hmz Hmp) => Hm'.
  by do 3! destruct m => //.
Qed.
