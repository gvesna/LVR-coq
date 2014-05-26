(*Algoritem za sortiranje po principu selection sort*)

Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import sort. (*podpora od Bauerja*)
Require Import Recdef.
Local Open Scope list_scope.

(*Funkcija, ki v danem seznamu L najde najmanši element minL in vrne (minL, L-minL)*)
Fixpoint najmanjsi_brez (x : Z) (l : list Z) : Z * list Z :=
  match l with
    | nil => (x , nil)
    | y :: l' => let (z , l'') := najmanjsi_brez y l'
      in
        if Z.leb x z
        then (x , l)
        else (z , x :: l'')
  end.

Eval compute in (najmanjsi_brez 3 (5 :: 4 :: 1 :: 2 :: 7 :: nil)%Z).

(*Pomožna lema. Dokazujemo lahko katerokoli od spodnjih trditev:
- let (y , l') := najmanjsi_brez x l in length l = length l'.
- length (snd (najmanjsi_brez x l)) = length l.
*)
Lemma najmanjsi_dolzina (x : Z) (l : list Z): length (snd (najmanjsi_brez x l)) = length l. 
Proof.
  induction l.
  -simpl.
   reflexivity.
  - simpl.
    rewrite <- IHl.
    (*To je treba še dokazati*)
Qed.

(*Funkcija, ki uredi dani seznam po principu selection sort.*)
Function selection (l : list Z) {measure length l} : list Z :=
  match l with
    | nil => nil
    | x :: l' => let (y , l'') := najmanjsi_brez x l' in
      y :: selection l''
  end.
Proof.
  intros.
  replace (length (x :: l')) with (length (x :: l'')).
  - admit.
  - simpl.
    f_equal.
    replace (l'') with (snd (najmanjsi_brez x l')).
    + admit.
    + admit.
    (*To je treba še dokazati.*)
Qed.

Eval compute in (selection (5 :: 4 :: 1 :: 2 :: 7 :: nil)%Z).
  
    
  