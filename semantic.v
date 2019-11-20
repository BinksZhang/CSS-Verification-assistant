Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import language.
Require Import state.
Require Import util.
Import ListNotations.

Fixpoint aeval (stoV: storeV) (stoF: storeF) (a:aexp) : nat :=
match a with
| ANum n => n
| AId name => stoV name
| APlus a1 a2 => (aeval stoV stoF a1) + (aeval stoV stoF a2)
| AMult a1 a2 => (aeval stoV stoF a1) * (aeval stoV stoF a2)
| AMinus a1 a2 => (aeval stoV stoF a1) - (aeval stoV stoF a2)
| AFsize fname => length (stoF fname)
end.


Fixpoint findbk (li:list nat) (loc:nat): option nat :=
match li with
| [] => None
| x::xli => if (beq_nat loc 1) then Some x else (findbk xli (loc-1))
end.

Fixpoint bkeval (stoV:storeV) (stoB:storeB) 
                (stoF:storeF) (bk:bkexp) : option nat :=
match bk with
| BKNum n => Some n
| BKId name => Some (stoB name)
| BKAddr fname a => findbk (stoF fname) (aeval stoV stoF a)
end.
 

Fixpoint beval stoV stoB stoF (b:bexp) : option bool :=
match b with
| BTrue   => Some true
| BFalse  => Some false
| BEq a1 a2 => Some (beq_nat (aeval stoV stoF a1) (aeval stoV stoF a2))
| BLe a1 a2 => Some (leb (aeval stoV stoF a1) (aeval stoV stoF a2))
| BNot b1   =>(match (beval stoV stoB stoF b1) with
               | None => None
               | Some x => Some (negb x)
               end)
| BAnd b1 b2  =>(match (beval stoV stoB stoF b1), (beval stoV stoB stoF b2) with
                 | None,_ => None
                 | _,None => None
                 | Some x1,Some x2 => Some (andb x1 x2)
                 end)
| BOr  b1 b2  =>(match (beval stoV stoB stoF b1), (beval stoV stoB stoF b2) with
                 | None,_ => None
                 | _,None => None
                 | Some x1, Some x2 => Some (orb x1 x2)
                 end)
| BKeq bk1 bk2  =>(match (bkeval stoV stoB stoF bk1),
                         (bkeval stoV stoB stoF bk2) 
                   with
                   | None,_ => None
                   | _,None => None
                   | Some a1, Some a2 => (Some (beq_nat a1 a2))
                   end)
| BKle bk1 bk2  => (match (bkeval stoV stoB stoF bk1),
                          (bkeval stoV stoB stoF bk2) 
                   with
                   | None,_ => None
                   | _,None => None
                   | Some a1, Some a2 => (Some (leb a1 a2))
                   end)
end.


(* auxiliary function *)
(*可选类型的nat比较*)
Definition beq_op_nat (x y: option nat) : bool :=
match x,y with
| None,None => true
| Some n1,Some n2 => beq_nat n1 n2
| _,_ => false
end.

Fixpoint in_list (li:list (option nat)) (x:option nat) : bool :=
match li with
| [] => false
| t::xli => if beq_op_nat t x then true else in_list xli x
end.

Definition get_content (nli:list (option nat)) : list nat :=
let f := fun t => match t with
                 | Some n => n
                 | None => 0
                 end
in (map f nli).

Fixpoint all_none (opli:list (option nat)) : bool :=
match opli with
| [] => true
| x::li => if beq_op_nat x None then all_none li
           else false
end.

Fixpoint h_unionB_many (hB:heapB) (locli nli:list nat) : heapB :=
match locli,nli with
| loc::locs,n::ns => h_unionB_many (hB_update hB loc n) locs ns
| [],[] => hB
| _,_ => hB
end.











Inductive ceval: command -> state -> ext_state -> Prop :=
(**旧指令集**)
| E_Skip  : forall stat,
              ceval CSkip stat (St stat)

| E_Ass   : forall stoV stoB stoF hV hB x a n, (aeval stoV stoF a) = n ->
              ceval (CAss x a) (stoV,stoB,stoF,hV,hB)
                       (St ((x !sv-> n; stoV),stoB,stoF,hV,hB))

| E_Seq   : forall c1 c2 st0 st1 opst,
              ceval c1 st0 (St st1) ->
              ceval c2 st1 opst ->
              ceval (CSeq c1 c2) st0 opst
| E_Seq_Ab: forall c1 c2 st0,
              ceval c1 st0 Abt ->
              ceval (CSeq c1 c2) st0 Abt
| E_IfTure: forall stoV stoB stoF hV hB opst b c1 c2,
              beval stoV stoB stoF b = Some true ->
              ceval c1 (stoV,stoB,stoF,hV,hB) opst ->
              ceval (CIf b c1 c2) (stoV,stoB,stoF,hV,hB) opst
| E_IfFalse: forall stoV stoB stoF hV hB opst b c1 c2,
              beval stoV stoB stoF b = Some false ->
              ceval c2 (stoV,stoB,stoF,hV,hB) opst ->
              ceval (CIf b c1 c2) (stoV,stoB,stoF,hV,hB) opst
| E_If_Ab : forall stoV stoB stoF hV hB b c1 c2,
              beval stoV stoB stoF b = None ->
              ceval (CIf b c1 c2) (stoV,stoB,stoF,hV,hB) Abt


| E_WhileEnd : forall b stoV stoB stoF hV hB c,
                 beval stoV stoB stoF b = Some false ->
                 ceval (CWhile b c) (stoV,stoB,stoF,hV,hB) (St (stoV,stoB,stoF,hV,hB))

| E_WhileLoop : forall stoV stoB stoF hV hB opst b c st,
                  beval stoV stoB stoF b = Some true ->
                  ceval c (stoV,stoB,stoF,hV,hB) (St st) ->
                  ceval (CWhile b c) st opst ->
                  ceval (CWhile b c) (stoV,stoB,stoF,hV,hB) opst
| E_WhileLoop_Ab : forall stoV stoB stoF hV hB b c,
                  beval stoV stoB stoF b = Some true ->
                  ceval c (stoV,stoB,stoF,hV,hB) Abt ->
                  ceval (CWhile b c) (stoV,stoB,stoF,hV,hB) Abt
| E_While_Ab :  forall stoV stoB stoF hV hB b c,
                  beval stoV stoB stoF b = None ->
                  ceval (CWhile b c) (stoV,stoB,stoF,hV,hB) Abt

(**分离逻辑的指令集**)
| E_Cons : forall stoV stoB stoF hV hB a n x l,
              aeval stoV stoF a = n ->
              hV l = None ->
              ceval  (CCons x a) (stoV,stoB,stoF,hV,hB)
                       (St ((x !sv-> l; stoV),stoB,stoF,
                            (l !hv-> n; hV), hB))

| E_Lookup : forall stoV stoB stoF hV hB x a1 l n,
                aeval stoV stoF a1 = l ->
                hV l = Some n ->
                ceval (CLookup x a1) (stoV,stoB,stoF,hV,hB) 
                         (St ((x !sv-> n; stoV),stoB,stoF,hV,hB))

| E_Lookup_Ab : forall stoV stoB stoF hV hB x a1 l,
                   aeval stoV stoF a1 = l ->
                   hV l = None ->
                   ceval (CLookup x a1) (stoV,stoB,stoF,hV,hB) Abt

| E_Mutat : forall stoV stoB stoF hV hB a1 a2 n1 n2,
                  aeval stoV stoF a1 = n1 ->
                  aeval stoV stoF a2 = n2 ->
                  in_domV n1 hV ->
                  ceval (CMutat a1 a2) (stoV,stoB,stoF,hV,hB) 
                           (St (stoV,stoB,stoF,(n1 !hv-> n2; hV),hB))

| E_Mutat_Ab : forall stoV stoB stoF hV hB a1 a2 n1,
                     aeval stoV stoF a1 = n1 ->
                     hV n1 = None ->
                     ceval (CMutat a1 a2) (stoV,stoB,stoF,hV,hB) Abt

| E_Dispose : forall stoV stoB stoF hV hB a1 n1,
                 aeval stoV stoF a1 = n1 ->
                 in_domV n1 hV ->
                 ceval
                   (CDispose a1) (stoV,stoB,stoF,hV,hB)
                   (St (stoV,stoB,stoF,(hV_remove hV n1),hB))

| E_Dispose_Ab : forall stoV stoB stoF hV hB a1 n1,
                    aeval stoV stoF a1 = n1 ->
                    hV n1 = None ->
                    ceval (CDispose a1) (stoV,stoB,stoF,hV,hB) Abt

(**新指令集**)
(*文件指令 *)
| E_Fcreate : forall stoV stoB stoF hV hB f bk n loc,
                 bkeval stoV stoB stoF bk = Some n ->
                 hB loc = None ->
                 ceval (CFcreate f bk) (stoV,stoB,stoF,hV,hB)
                          (St (stoV,stoB,(f !sf-> [loc]; stoF),hV,
                              (loc !hb-> n;hB)))
| E_Fcreate_Abt : forall stoV stoB stoF hV hB f bk,
                 bkeval stoV stoB stoF bk = None ->
                 ceval (CFcreate f bk) (stoV,stoB,stoF,hV,hB) Abt

| E_FcontentAppend : forall stoV stoB stoF hV hB f bk ff n loc,
                        bkeval stoV stoB stoF bk = Some n ->
                        hB loc = None ->
                        ff = stoF f ->
                        ceval (CFcontentAppend f bk) (stoV,stoB,stoF,hV,hB)
                                 (St (stoV,stoB,
                                     (f !sf-> (ff ++ [loc]); stoF),hV,
                                     (loc !hb-> n;hB)))

| E_FcontentAppend_Abt : forall stoV stoB stoF hV hB f bk,
                          bkeval stoV stoB stoF bk = None ->
                          ceval (CFcontentAppend f bk) 
                                   (stoV,stoB,stoF,hV,hB) Abt

| E_FaddressAppend : forall stoV stoB stoF hV hB f1 f2 bk n ff2,
                        bkeval stoV stoB stoF bk = Some n ->
                        ff2 = stoF f2 ->
                        hB n = None ->
                        ceval (CFaddressAppend f1 f2 bk) (stoV,stoB,stoF,hV,hB)
                                 (St (stoV,stoB,
                                     (f1 !sf-> (ff2 ++ [n]); stoF),hV,hB))

| E_FaddressAppend_Abt : forall stoV stoB stoF hV hB f1 f2 bk,
                          (bkeval stoV stoB stoF) bk = None ->
                          ceval (CFaddressAppend f1 f2 bk) 
                                   (stoV,stoB,stoF,hV,hB) Abt

| E_Fdelete : forall stoV stoB stoF hV hB f,
                ceval (CFdelete f) (stoV,stoB,stoF,hV,hB)
                         (St (stoV,stoB,(f !sf-> nil;stoF),hV,hB))

(*块指令*)
| E_Blookup : forall stoV stoB stoF hV hB b bk n v,
                (bkeval stoV stoB stoF bk) = Some n->
                hB n = Some v ->
                ceval (CBlookup b bk) (stoV,stoB,stoF,hV,hB)
                         (St (stoV,(b !sb-> v; stoB),stoF,hV,hB))

| E_Blookup_AbtBK : forall stoV stoB stoF hV hB b bk,
                      (bkeval stoV stoB stoF bk) = None ->
                      ceval (CBlookup b bk) (stoV,stoB,stoF,hV,hB) Abt

| E_Blookup_AbtHp : forall stoV stoB stoF hV hB b bk n,
                      (bkeval stoV stoB stoF bk) = Some n ->
                      hB n = None ->
                      ceval (CBlookup b bk) (stoV,stoB,stoF,hV,hB) Abt

| E_Bass : forall stoV stoB stoF hV hB b bk n,
              (bkeval stoV stoB stoF bk) = Some n ->
              ceval (CBass b bk) (stoV,stoB,stoF,hV,hB)
                       (St (stoV,(b !sb-> n; stoB),stoF,hV,hB))

| E_Bass_Abt : forall stoV stoB stoF hV hB b bk,
                (bkeval stoV stoB stoF bk) = None ->
                ceval (CBass b bk) (stoV,stoB,stoF,hV,hB) Abt

| E_Bmutat : forall stoV stoB stoF hV hB bk1 bk2 n1 n2,
                (bkeval stoV stoB stoF bk1) = Some n1 ->
                (bkeval stoV stoB stoF bk2) = Some n2 ->
                ceval (CBmutat bk1 bk2) (stoV,stoB,stoF,hV,hB)
                         (St (stoV,stoB,stoF,hV,(n1 !hb-> n2; hB)))

| E_Bmutat_AbtBk1 : forall stoV stoB stoF hV hB bk1 bk2,
                      (bkeval stoV stoB stoF bk1) = None ->
                      ceval (CBmutat bk1 bk2) (stoV,stoB,stoF,hV,hB) Abt

| E_Bmutat_AbtBk2 : forall stoV stoB stoF hV hB bk1 bk2 n1,
                      (bkeval stoV stoB stoF bk1) = Some n1 ->
                      (bkeval stoV stoB stoF bk2) = None ->
                      ceval (CBmutat bk1 bk2) (stoV,stoB,stoF,hV,hB) Abt

| E_Bdelete : forall stoV stoB stoF hV hB lbk bk,
                 bkeval stoV stoB stoF bk = Some lbk ->
                 in_domB lbk hB ->
                 ceval
                   (CBdelete bk) (stoV,stoB,stoF,hV,hB)
                         (St (stoV,stoB,stoF,hV,(hB_remove hB lbk)))

| E_BdeleteAbs : forall stoV stoB stoF hV hB bk,
                 bkeval stoV stoB stoF bk = None ->
                 ceval
                   (CBdelete bk) (stoV,stoB,stoF,hV,hB) Abt

| E_BdeleteAbh : forall stoV stoB stoF hV hB lbk bk,
                 bkeval stoV stoB stoF bk = Some lbk ->
                 not_in_domB lbk hB ->
                 ceval
                   (CBdelete bk) (stoV,stoB,stoF,hV,hB) Abt.


Notation "st '=[' c ']=>' st'" := (ceval c st st') 
                                  (at level 40).



