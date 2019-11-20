Require Export Coq.omega.Omega.
Require Export Coq.Bool.Bool.
Require Export Coq.Arith.Arith.
Require Export Coq.Arith.EqNat.
Require Export Coq.Lists.List.
Require Export Coq.Logic.FunctionalExtensionality.
Import ListNotations.

(* export all bindings *)
Require Export util.
Require Export language.
Require Export semantic.
Require Export state.
Require Export Logic.


(*Some variables*)
Definition i  : id := Id "i".
Definition f1 : id := Id "f1".
Definition f2 : id := Id "f2".
Definition f3 : id := Id "f3".
Definition f4 : id := Id "f4".
Definition f5 : id := Id "f5".
Definition f6 : id := Id "f6".
Definition f7 : id := Id "f7".
Definition bc : id := Id "bc".
Definition bk1 : id := Id "bk1".
Definition bk2 : id := Id "bk2".
Definition tv : id := Id "tv".

(*The definition of empty state*)
Definition emp_sV : storeV :=
  fun (n : id) => 0.

Definition emp_sB : storeB :=
  fun (n : id) => 0.

Definition emp_sF : storeF :=
  fun (n : id) => [].

Definition empty_st : state := 
  (emp_sV, emp_sB, emp_sF, emp_heapV, emp_heapB).


