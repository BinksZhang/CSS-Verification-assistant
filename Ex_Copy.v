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
  (*no4_eq定义了4个地址变量间互不相等*)
  unfold no4_eq.
  (*H1-H6是no4_eq拆分出的前提*)
  intros n1 n2 n3 n4
  [H1[H2[H3[H4[H5 H6]]]]].
  eapply E_Seq.
  - (***先证明创建f1的环节***)
    eapply E_Seq.
    + (*令n1代表块内容11的存储地址*)
      eapply E_Fcreate with (loc :=n1);
      try reflexivity.
    + (*令n2代表块内容12的存储地址*)
      eapply E_FcontentAppend with (loc := n2);
      try reflexivity.
      try rewrite hB_update_neq; trivial.
  - (***接下来证明拷贝的环节***)
    eapply E_Seq.
    + (*循环变量i初始值等于1*)
      apply E_Ass. auto.
    + (*下面进入第一次循环*)
      eapply E_WhileLoop.
      * (*确认循环条件为真*) auto.
      * (*下面执行循环体*)
        eapply E_Seq.
        -- (*下面读取f1中块的内容,暂存到bc*)
           eapply E_Blookup.
           ++ (*确认为已分配的块*)reflexivity.
           ++ (*确认块中的值*)
           rewrite hB_update_neq,hB_update_eq.
           reflexivity. apply neq_comm. trivial.
        -- (*下面将bc中的内容,存到f2中*)
           eapply E_Seq.
           (*令n3为新建的存储地址*)
           eapply E_FcontentAppend with (loc := n3);
           try reflexivity.
           (*确认n3未被分配*)
           repeat rewrite hB_update_neq;
           try apply neq_comm; trivial.
           ++ (*确认循环变量i更新为2*)
           apply E_Ass. auto.
      * (*第二次循环和第一次循环证明过程类似*)
        eapply E_WhileLoop.
        ** reflexivity.
        ** eapply E_Seq.
        --- eapply E_Blookup.
            reflexivity.
            rewrite hB_update_neq,hB_update_eq.
            reflexivity. trivial.
        --- eapply E_Seq.
           +++ (*令n4为新建的存储地址*)
               eapply E_FcontentAppend with (loc := n4);
               try reflexivity.
               (*确认n4未被分配*)
               repeat rewrite hB_update_neq;
               try apply neq_comm; trivial.
           +++ apply E_Ass.
               reflexivity.
        ** simpl.
           (*将所得状态进行化简*)
           rewrite sV_update_shadow.
           rewrite sV_update_shadow.
           rewrite sB_update_shadow.
           repeat rewrite sF_update_shadow.
           repeat rewrite hB_update_shadow.
           (*确认循环可终止*)
           eapply E_WhileEnd.
           (*确认前后状态一致*)
           reflexivity.
Qed.





