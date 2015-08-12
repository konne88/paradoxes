(* Based on "An intuitionistic theory of types" by Per Martin-Loef, 1972 *)

(* 
Some intuition for noChains:

~exists f, forall n, f (S n) < f n
~exists f, forall n, ~(f (S n) >= f n)
~exists f, ~exists n, f (S n) >= f n
forall f, exists n, f n =< f (S n)

one cannot arrange the elements in A, from left to right,
in such a way that they get monotonocally smaller as one 
goes the to right.
*)

Class ordering := {
  A : Type;
  lt : A -> A -> Type;
  transitive x y z : lt x y -> lt y z -> lt x z;
  noChains (f:nat -> A) : (forall n, lt (f (S n)) (f n)) -> False
}.

Notation "x < y" := (lt x y).

Lemma irreflexive `{ordering} a : a < a -> False.
  intro h.
  apply (noChains (fun _ => a) (fun _ => h)).
Qed. 

Class orderingLe (o:ordering) (o':ordering) : Type := {
  map : @A o -> @A o'; 
  max : @A o';
  mapOk x y : x < y -> map x < map y; 
  maxOk x : map x < max
}.

Notation "x << y" := (orderingLe x y) (at level 45).

Lemma orderingLeTransitive o o' o'' : o << o' -> o' << o'' -> o << o''.
  intros h h'.
  refine {| map := fun x => map (map x) ; max := max |}.
  - intros x y h''.
    apply mapOk.
    apply mapOk.
    apply h''.
  - intro x.
    apply maxOk.
Qed.

Lemma orderingLeNoChains f : (forall n, f (S n) << f n) -> False.
  intro h.
  refine (
    let fix rec n' := match n' as n'' return @A (f n'') -> @A (f 0) with 
    | 0 => fun a => a
    | S n'' => fun a => rec n'' (map a)
    end in _).
  refine (@noChains (f 0) (fun n => rec n (@max _ _ (h n))) _).
  cbn.
  intro n.
  enough (forall x y, x < y -> rec n x < rec n y) as h'. {
    apply h'.
    apply maxOk.
  }
  intros x y.
  induction n; cbn in *.
  - exact (fun a => a).
  - intro h'. 
    apply IHn.
    apply mapOk.
    apply h'.
Qed.

(* this is where we get the universe inconsistency 
   and have to run Coq with flag -type-in-type *)
Instance orderingOfOrderings : ordering.
  refine {| A := ordering; lt := orderingLe |}.
  - apply orderingLeTransitive.
  - apply orderingLeNoChains.
Defined.

Instance subOrdering (o:ordering) (a:@A o): ordering.
  refine {| 
    A := {x:@A o & x < a}; 
    lt := fun x y => projT1 x < projT1 y
  |}.
  - intros [x ?] [y ?] [z ?].
    cbn.
    apply transitive.
  - intros f h.
    apply (noChains (fun n => projT1 (f n))).
    intro n.
    specialize (h n).
    apply h.
Defined.

Lemma orderingOfOrderingsMax o : o < orderingOfOrderings.
  cbn.
  refine {| 
    map := fun a => subOrdering o a;
    max := o
  |}.
  - intros a b h.
    cbn.
    refine {| 
      map := fun x => _;
      max := _
    |}.
    + cbn in *.
      refine (existT _ (projT1 x) _).
      specialize (projT2 x); intro h'.
      revert h.
      revert h'.
      apply transitive.
    + refine (existT _ a h).
    + cbn in *.
      intros [x ?] [y ?].
      cbn.
      exact (fun a => a).
    + cbn in *.
      intros [x h'].
      cbn.
      apply h'.
  - intro a.
    cbn.
    refine {| 
      map := _;
      max := a
    |}.
    + exact (fun x => projT1 x).
    + intros [x ?] [y ?].
      cbn.
      exact (fun a => a).
    + intros [x h].
      cbn.
      apply h.
Qed.      

Lemma orderingOfOrderingsReflexive : orderingOfOrderings < orderingOfOrderings.
  apply orderingOfOrderingsMax.
Qed.

Theorem false : False.
  apply (@irreflexive orderingOfOrderings orderingOfOrderings).
  apply orderingOfOrderingsReflexive.
Qed.