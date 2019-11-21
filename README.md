# 基于Coq的云存储系统辅助证明工具

（*注意，目前本工具基于Coq 8.8.0编译*)

这是一个基于Coq的云存储系统辅助验证工具，支持用户验证针对以HDFS为代表的块云存储系统的可靠性。用户可以根据云存储系统对文件和块的后台操作，编写与之对应的模拟程序，并在工具中验证该程序的正确性。

本工具的建模语言由操作语义定义，因此建议用户在Coq的交互模式，也就是Coqide中形式化验证程序（当然同时支持编译模式）。

## 使用环境

[下载8.8.0版本的CoqIde]( https://github.com/coq/coq/releases/tag/V8.8.0 )，可以直接应用本工具。

对于[不同版本的CoqIde](https://coq.inria.fr/news/)，需要先对每个.v文件进行编译（Compile Buffer），之后同样可以使用。

## 工具组成

本工具由以下几个部分构成：

- Logic.v      ：证明过程中所用的辅助定理
- language.v   ：包含表达式和命令的语法
- state.v       ： 定义系统状态
- semantic.v  ：定义表达式和命令的操作语义，包含了命令的规则
- CSSsVerification.v  ：整合所有部件并声明部分变量
- Ex_deletef.v  ：例子—证明读取已删除文件引发的报错
- Ex_Copy.v :例子：证明创建以及拷贝文件程序的正确性

## 使用示范

工具中附有Ex_Copy.v，展示对于云存储系统中，用户创建文件和拷贝文件操作的验证。

```Coq
(*下面是示例程序*)
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
```

在本工具中，我们以细粒度的方式描述云存储系统中程序的执行过程，因此创建文件被分为了“新建”和“追加”两个环节，每个环节只对一个数据块进行操作。如果被追加的文件若不在当前系统中，系统会对应创建一个新文件存储该块，从而避免数据的丢失。

```Coq
(*下面是待证目标：我们以n1-n4表示4个数据块的地址*)
(*no4_eq代表了4个间互不相等*)
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
```
下面图片展示了用户在以Coq的交互模式（Coqide）对目标进行证明时的效果![Proving](https://github.com/BinksZhang/HDFS-Verification-assistant/blob/master/Proving.png)

左侧为用户构造的证明策略，右侧为Coq随策略执行自动生成的待证目标以及系统状态。

