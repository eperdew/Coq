Require Import Coq.Unicode.Utf8.
Require Import Arith.

(* Eric Perdew - April 11, 2015 *)

(* Some background: I wanted to define a Turing complete language in Coq.
   I am slightly disgruntled with the idea floating around that Coq being
   subrecursive means that it is unable to represent or compute with
   functions that are not provably total. Therefore, I went on esolangs.org,
   found the description of Bitwise Cyclic Tag, and implemented an
   intepreter in Coq. ( https://esolangs.org/wiki/Bitwise_Cyclic_Tag ) *)

(* I decided to implement most of the data structures in this file, to keep
   the meat of it here. *)
CoInductive stream (A : Type) : Type :=
| Nil : stream A
| Cons : A → stream A → stream A.

Arguments Nil {A}.
Arguments Cons {A} _ _.

Notation "[]" := Nil.
Notation "x :: y" := (Cons x y) (at level 60, right associativity).

(* Here, I made the unfortunate choice of making [bit_string] an inductive
   set rather than just using lists of bits or bool. This doesn't matter in
   the end, but it makes case analysis more tedious. *)
Inductive bit_string : Set :=
| Empty : bit_string
| One : bit_string → bit_string
| Zero : bit_string → bit_string.

Notation "#" := Empty.
Notation "'I' ^ x" := (One x) (at level 80).
Notation "'O' ^ x" := (Zero x) (at level 80).

(* Some helper functions for the interpreter *)
Fixpoint append (xs ys : bit_string) : bit_string :=
  match xs with
    | # => ys
    | I^xs' => I ^ (append xs' ys)
    | O^xs' => O ^ (append xs' ys)
  end.

Fixpoint cycle_bit (bs : bit_string) : bit_string :=
  match bs with
    | # => #
    | I^tl => append tl (I^#)
    | O^tl => append tl (O^#)
  end.

Fixpoint copy_bit (bs bs' : bit_string) : bit_string :=
  match bs with
    | # => bs'
    | I^_ => append bs' (I^#)
    | O^_ => append bs' (O^#)
  end.

(* I could have made this much smaller by choosing better datatypes to
   begin with. Regardless, here is the interpreter. It takes in two
   bit strings and evaluates to a (potentially infinite) stream holding
   the data bit string at each step of computation. *)
CoFixpoint BCT_eval (prog data : bit_string) : stream bit_string :=
  match prog,data with
    | #,_ | _,# => data :: []
    | I^_,I^_ => let n_prog := cycle_bit prog in
                data :: (BCT_eval (cycle_bit n_prog) (copy_bit n_prog data))
    | I^_,O^_ => let n_prog := cycle_bit prog in
                data :: (BCT_eval (cycle_bit n_prog) data)
    | O^_,I^data' | O^_,O^data' => data :: (BCT_eval (cycle_bit prog) data')
  end.

(* Here is the set of my previous design decisions coming to bite me *)
Inductive List (A : Type) : Type :=
| Nil_L : List A
| Cons_L : A → List A → List A.

Arguments Nil_L {A}.
Arguments Cons_L {A} _ _.

Notation "x :> y" := (Cons_L x y) (at level 70, right associativity).
Notation "[-]" := Nil_L.

(* Take does exactly what you expect it to do. It takes the first n
   elements of the stream s, if they exist. If it runs off the end of
   the stream, it stops. *)
Fixpoint take {A : Type} (n : nat) (s : stream A) : List A :=
  match n,s with
    | 0,_ => [-]
    | _,[] => [-]
    | S n',hd::tl => hd :> (take n' tl)
  end.

(* Example from esolangs *)
Eval compute in (take 12 (BCT_eval (O^O^I^I^I^#) (I^O^I^#))).

(* Take is the normal endpoint for modeling Turing complete languages
   in a subrecursive language. However, we can go one step further. *)

(* Here's where the fun begins. This is a silly lemma to help Coq deal
   with cofix. *)
Lemma stream_destruct :
  forall (A : Type) (s : stream A),
    s = match s with | [] => [] | hd :: tl => hd :: tl end.
Proof.
  destruct s; reflexivity.
Qed.

Inductive is_finite {A : Type} : stream A → Prop :=
| nil_finite : is_finite []
| cons_finite : forall (s : stream A) (a : A), is_finite s → is_finite (a :: s).

(* Now, Coq's tactics system has the interesting and slightly amusing
   property of nontermination. Now that means that for a semideciable
   property such as termination, we can use the tactics language to
   define one tactic that will halt iff the property is true. Therefore,
   it is possible to use automation to prove semidecidable properties
   affirmatively. *)
Ltac prove_finite := repeat (rewrite stream_destruct; simpl;
                            constructor); try (constructor).

Example empty_start_is_finite :
  is_finite (BCT_eval # #).
Proof.
  prove_finite.
Qed.

Example harder_one :
  is_finite (BCT_eval (I^O^I^O^I^O^I^O^O^#) (I^I^I^I^I^I^I^I^I^I^I^I^I^#)).
Proof.
  prove_finite.
Qed.