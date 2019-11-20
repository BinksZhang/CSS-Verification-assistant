Require Import CSSsVerification.
Import ListNotations.

Definition Create :=
  CFcreate f1 (BKNum 11);;
  CFcontentAppend f1 (BKNum 12).

Definition Copy :=
  i ::= (ANum 1);;
  WHILE (BLe (AId i) (AFsize f1)) DO
    CBlookup bc (BKAddr f1 (AId i));;
    CFcontentAppend f2 (BKId bc);;
    i ::= (APlus (AId i) (ANum 1))
  END.

Definition no4_eq (n1 n2 n3 n4 : nat) :=
   n2 <> n1 /\ n1 <> n3 /\ n1 <> n4 
/\ n2 <> n3 /\ n2 <> n4 /\ n3 <> n4
.

Fact Copy_Correct :
forall n1 n2 n3 n4,
 no4_eq n1 n2 n3 n4 ->
empty_st =[
    Create;;
    Copy 
  ]=> St (
    (i !sv-> 3; emp_sV),
    (bc !sb-> 12; emp_sB),
    (f2 !sf-> [n3; n4]; f1 !sf-> [n1;n2]; emp_sF),
    (emp_heapV),
    (n4 !hv-> 12; n3 !hv-> 11; 
     n2 !hv-> 12; n1 !hv-> 11; emp_heapB)
    ).
Proof.
  unfold no4_eq.
  intros n1 n2 n3 n4
  [H1[H2[H3[H4[H5 H6]]]]].
  eapply E_Seq.
  - eapply E_Seq.
    + eapply E_Fcreate with (loc :=n1);
      try reflexivity.
    + eapply E_FcontentAppend with (loc := n2);
      try reflexivity.
      try rewrite hB_update_neq; trivial.
  - eapply E_Seq.
    + apply E_Ass. auto.
    + eapply E_WhileLoop.
      * auto.
      * eapply E_Seq.
        -- eapply E_Blookup.
           ++ reflexivity.
           ++ rewrite hB_update_neq,hB_update_eq.
           reflexivity. apply neq_comm. trivial.
        -- eapply E_Seq.
           eapply E_FcontentAppend with (loc := n3);
           try reflexivity.
           repeat rewrite hB_update_neq;
           try apply neq_comm; trivial.
           ++ apply E_Ass. auto.
      * eapply E_WhileLoop.
        ** reflexivity.
        ** eapply E_Seq.
        --- eapply E_Blookup.
            reflexivity.
            rewrite hB_update_neq,hB_update_eq.
            reflexivity. trivial.
        --- eapply E_Seq.
           +++ eapply E_FcontentAppend with (loc := n4);
               try reflexivity.
               repeat rewrite hB_update_neq;
               try apply neq_comm; trivial.
           +++ apply E_Ass.
               reflexivity.
        ** simpl.
           rewrite sV_update_shadow,sV_update_shadow,sB_update_shadow.
           repeat rewrite sF_update_shadow.
           repeat rewrite hB_update_shadow.
           eapply E_WhileEnd.
           reflexivity.
Qed.





