Require Export Lists.   

Fixpoint beq_nat ( n m: nat) : bool :=
  match n,m with 
    | 0, 0 => true 
    | S n', S m' => beq_nat n' m'
    | _, _ => false 
  end. 
  



Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length X t)
  end.

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil      => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil      => nil X
  | cons h t => snoc X (rev X t) h
  end.


Fixpoint app' X l1 l2 : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app' X t l2)
  end.

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length' _ t)
  end.
Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X} _ _.  
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l. 
Arguments snoc {X} l v.


Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length'' t)
  end.
Definition mynil : list nat := nil.
Definition mynil' := @nil nat.
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).



Definition list123''' := [1; 2; 3].


Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
    match count with 
        | 0 => nil 
        | S c => n :: repeat n c
    end. 


Theorem nil_app : forall X:Type, forall l:list X,
  app [] l = l.
Proof.
  intros.
  destruct l.
  reflexivity.
  reflexivity.
Qed.


Theorem rev_snoc : forall X : Type,
                     forall v : X,
                     forall s : list X,
  rev (snoc s v) = v :: (rev s).
Proof.
  intros.
  induction s.
  reflexivity.
  simpl.
  rewrite IHs.
  reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite rev_snoc.
  rewrite IHl.
  reflexivity.
Qed.


Theorem snoc_with_append : forall X : Type,
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros.
  induction l1.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
Qed.




Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match (lx,ly) with
  | ([],_) => []
  | (_,[]) => []
  | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.

Fixpoint split
           {X Y : Type} (l : list (X*Y))
           : (list X) * (list Y) :=
  match l with 
      | nil => (nil,nil)
      | (x, y)::rest => match split rest  with
                          | (nil, nil) => (x::nil,y::nil)
                          | (rxs, rys) => (x::rxs, y::rys)
                          end
      end.


Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _. 
Arguments None {X}. 
Fixpoint index {X : Type} (n : nat)
               (l : list X) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.
Definition hd_opt {X : Type} (l : list X)  : option X :=
  match l with
      | x :: xs => Some x
      | nil => None
  end.




Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  match p with
      | (x, y) => f x y 
  end.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros.
  reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                               (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros.
  destruct p.
  reflexivity.
Qed.






Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

Fixpoint evenb ( n:nat ) : bool :=
  match n with 
      | 0 => true 
      | 1 => false  
      | S (S n') => evenb n'
  end.

Definition notb (b:bool): bool := if (b) then false else true .

Definition oddb (n:nat) : bool := notb (evenb n).

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.


Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).


Fixpoint gt (n m : nat ) : bool := 
  match n,m with
      | S n', S m' => gt n' m'
      | S n', 0 => true
      | _, _ => false 
  end.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) (gt n 7)) l.



Definition partition {X : Type} (test : X -> bool) (l : list X)
                     : list X * list X :=
(filter test l, filter (fun n => notb (test n)) l).


Fixpoint map {X Y:Type} (f:X->Y) (l:list X)
             : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.


Lemma map_snoc: forall (X Y: Type) (f: X -> Y) (l: list X) (x: X),
                  map f (snoc l x) = snoc (map f l) (f x).
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.


Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros. 
  induction l.
  reflexivity.
  simpl.
  rewrite map_snoc.
  rewrite IHl.
  reflexivity.
Qed.



Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) :=
  match l with 
      | nil => nil
      | x::xs => f x ++ flat_map f xs
  end.


Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.


Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Definition override {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if beq_nat k k' then x else f k'.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Theorem beq_nat_refl: forall n: nat,
                        true = beq_nat  n n.
Proof.
induction n.
reflexivity.
simpl.
exact IHn.
Qed.

Theorem override_eq : forall {X:Type} x k (f:nat->X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.  Qed.


Theorem override_neq : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  intros.
  unfold override.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.  
  
Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.


Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
intros.
induction l.
reflexivity.
simpl.
rewrite <- IHl.
reflexivity.
Qed.

