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

Lemma odd_injective: forall n m, n = m -> odd n = odd m.
Proof.
  move => n m Heq.
by   rewrite Heq.
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



Lemma helper n p:  n * n = 2 * p * p  -> p = 0 .
  move: p.
  move: (leqnn n).
  move: {1}n.
  elim n.
  (* base *)
  move => n0 Hn p H.
  symmetry in H.                                                                                                                         move:  H.                                                                                                                              rewrite -[0*0]/0 .                                                                                                                     move/eqP.                                                                                                                              do 2! rewrite muln_eq0.                                                                                                                simpl.                                                                                                                                 rewrite or_b_b.      
  by move/eqP.

  move => n0 H n1 p H0 .


  rewrite   double_eq0.




  elim n.
  intros.
  split ; apply / eqP; rewrite leqn0 in leqnn; first by [].
  move/eqP in leqnn.
  symmetry in H.
  move:  H.  
  rewrite leqnn.
  rewrite -[0*0]/0 .
  move/eqP.
  do 2! rewrite muln_eq0.
  simpl. 
  by rewrite or_b_b.  
  intros.
  assert (odd( n1 * n1) = odd( 2 * m0 * m0) ).
  by  apply odd_injective in H0. 

  assert ( odd( 2 * m0 * m0 ) = false ).  by rewrite ! odd_mul.
  assert ( odd( n1 * n1) = odd n1 ). rewrite odd_mul. by rewrite and_a_a.
  case Hoddn1:( odd n1 ).
  by  rewrite H3 H2 Hoddn1 in H1.
  apply eq_halving in H0 => //=.
  

  move: (H 
  

  
  assert( n1* n1    


  assert ( odd (n1 * n1) ).  rewrite odd_mul. by rewrite H oddn1.

  case Hoddm0:( odd m0 ).

  by rewrite H1 H2 in H0.
  


t.

  apply H ; try  by [].



  case Hns:(  n1 == n0.+1).
  move/eqP in Hns.
  rewrite Hns.  
  .

inversion leqnn.
  inversion H2.
  
 

  rewrite leqn0 in leqnn0.
    
  elim n; elim m; try by [].
  intros.   
 


  elim => n0  => [m' | Hm m'] .
  
