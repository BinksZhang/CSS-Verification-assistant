Require Import CSSsVerification.
Import ListNotations.

(*证明删除文件会引发系统报错*)
Definition DeleteF :=
  CFcreate f1 (BKNum 1012);;
  CFdelete f1;;
  CBlookup bc (BKAddr f1 (AId i)).

Example Delete_corr :
  empty_st =[ 
    DeleteF
  ]=> Abt.
Proof.
  eapply E_Seq.
  - eapply E_Fcreate with (loc :=3000);
    try reflexivity.
  - eapply E_Seq.
    + apply E_Fdelete.
    + eapply E_Blookup_AbtBK.
      reflexivity.
Qed.