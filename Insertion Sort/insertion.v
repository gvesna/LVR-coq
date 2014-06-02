
(*Algoritem za sortiranje po principu insertion sort *)

Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import Sorting. (*podpora od Bauerja*)
Require Import Recdef.
Local Open Scope list_scope.

(*Funkcija, ki vstavi dan element na pravo mesto v že urejejn seznam*)
Fixpoint vstavi (x : Z) (l : list Z) : list Z :=
  match l with
    | nil => x :: nil
    | y :: l' => if Z.leb x y
                 then x :: y :: l'
                 else y :: vstavi x l'
  end.

Eval compute in (vstavi 6 (1 :: 2 :: 4 :: 5 :: 7 :: nil)%Z).


Fixpoint insertion (l : list Z) : list Z :=
  match l with
    | nil => nil
    | x :: l' => vstavi x (insertion l')
 end.

Eval compute in (insertion (3 :: 2 :: 4 :: 7 :: 1 :: 5 :: nil)%Z).