(*Algoritem za sortiranje po principu insertion sort *)

Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import Sorting. (*podpora od prof. Bauerja*)
Require Import Recdef.

Local Open Scope list_scope.
Local Open Scope Z_scope.

(*Funkcija, ki vstavi dan element na pravo mesto v že urejen seznam*)
Fixpoint vstavi (x : Z) (l : list Z) : list Z :=
  match l with
    | nil => x :: nil
    | y :: l' => if Z.leb x y
                 then x :: y :: l'
                 else y :: vstavi x l'
  end.

Eval compute in (vstavi 6 (1 :: 2 :: 4 :: 5 :: 7 :: nil)%Z).

(*Insertion sort*)
Fixpoint insertion (l : list Z) : list Z :=
  match l with
    | nil => nil
    | x :: l' => vstavi x (insertion l')
 end.

Eval compute in (insertion (3 :: 2 :: 4 :: 7 :: 1 :: 5 :: nil)%Z).

(*Pomozne leme*)
Lemma pojavi_vstavi_neq (x y : Z) (l : list Z): (x =? y = false) -> pojavi x l = pojavi x (vstavi y l).
Proof.
  intro.
  induction l.
  - simpl.
    rewrite H ; auto.
  - simpl.
    case_eq (x =? a).
    + intro G.
      case_eq (y <=? a).
      * intro G1.
        simpl.
        rewrite H,G ; auto.
      * intro G2.
        simpl.
        rewrite G.
        f_equal.
        rewrite IHl ; auto.
    + intro G.
      case_eq (y <=? a).
      * intro G1.
        simpl.
        rewrite H,G ; auto.
      * intro G2.
        simpl.
        rewrite G, IHl ; auto.
Qed.

Lemma pojavi_vstavi_eq (x : Z) (l : list Z): pojavi x (vstavi x l) = S (pojavi x l).
Proof.
  induction l.
  - simpl.
    rewrite Z.eqb_refl ; auto.
  - simpl.
    case_eq (x <=? a).
    + intro G.
      case_eq (x =? a) ; intro G1.
      * rewrite Z.eqb_sym, Z.eqb_eq in G1.
        rewrite G1.
        simpl.
        rewrite Z.eqb_refl ; auto.
      * simpl.
        rewrite Z.eqb_refl, G1 ; auto.
   + intro G.
     simpl.
     case_eq (x =? a) ; intro G1.
     *  f_equal.
        apply IHl.
     *  apply IHl.
Qed.

Lemma urejen_vstavi (x : Z) (l : list Z): urejen l -> urejen (vstavi x l).
Proof.
  intro.
  induction l ; simpl ; auto.
   simpl.
    case_eq (x <=? a).
    + intro G.
      simpl.
      split.
      * apply Zle_is_le_bool in G ; tauto.
      * apply H.
    + intro G.
      simpl.
      destruct l.
      * simpl.
        firstorder.
        apply Z.lt_le_incl.
        assert (C := Zle_cases x a).
        rewrite G in C.
        firstorder.
      * simpl.
        apply Z.leb_gt in G.
        case_eq (x <=? z).
        - intro L.
          apply Z.leb_le in L.
          split ; firstorder.
        - intro K.
          apply Z.leb_gt in K.
          split ; [ firstorder | idtac ].
          replace (z :: vstavi x l) with (vstavi x (z :: l)).
          proof.
            apply IHl.
            apply (urejen_tail a (z :: l)).
            assumption.
          end proof.
          proof.
            simpl.
            apply Z.leb_gt in K.
            rewrite K ; auto.
          end proof.
Qed.
   
(*Teorem o delovanju insertion sorta*)
Theorem delovanje_algoritma (l : list Z): urejen (insertion l).
Proof.
 induction l.
 - simpl ; auto.
 - simpl.
   apply urejen_vstavi.
   assumption.
Qed.

(*Teorem o ohranjanju seznamov*)
Theorem ohranjanje (l : list Z): l ~~ insertion l.
Proof.
 intro.
 induction l.
 - auto.
 - case_eq (x =? a).
   + intro.
     simpl.
     rewrite H, IHl.
     rewrite Z.eqb_sym, Z.eqb_eq in H.
     rewrite H.
     rewrite <- (pojavi_vstavi_eq x (insertion l)) ; auto.
  + intro.
    simpl.
    rewrite H, IHl, (pojavi_vstavi_neq x a (insertion l)).
    * reflexivity.
    * assumption.
Qed.