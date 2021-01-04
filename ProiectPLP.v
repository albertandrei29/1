(* Perechi de numere naturale *)

Import Nat.
Module Type Int.

Inductive natpair : Type :=
| pair (n1 n2 : nat).

Notation "( x , y )" := (pair x y).

Definition first' (p : natpair) : nat :=
  match p with
  | (x,y) => x
  end.

Definition second' (p : natpair) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natpair) : natpair :=
  match p with
  | (x,y) => (y,x)
  end.

Check (pair 10 12).
Compute first'(10, 12).
Compute second'(10, 12).
Compute swap_pair(10, 12).

(* Arbori binari *)

Inductive BinTree : Type := 
 | leaf : BinTree
 | node : nat -> BinTree -> BinTree -> BinTree.

Definition ArbEx :=
(           node 10
        (node 11 (node 12 leaf leaf) (node 13 leaf leaf))
    (node 14 leaf leaf) 
).

Definition root (b : BinTree) : nat :=
  match b with
    | leaf => 0
    | node n ltree rtree => n
  end.

Definition maximnat (x y : nat) : nat := 
  match ltb x y with
    | true => y
    | false => x
  end. 

Fixpoint mirror (b : BinTree) : BinTree :=
  match b with
    | leaf => leaf
    | node n ltree rtree => node n (mirror rtree) (mirror ltree)
  end.

Fixpoint BST (b : BinTree) : bool :=
  match b with 
    | leaf => true
    | node n ltree rtree =>if(eqb (root ltree) 0)
                              then if(eqb (root rtree) 0)
                                then true
                              else BST(rtree)
                           else 
                              if (eqb (root rtree) 0) then BST(ltree)
                              else andb (BST ltree) (BST rtree)
         
  end.  

Fixpoint levels (b : BinTree) : nat :=
  match b with  
    | leaf => 0
    | node n ltree rtree => if(eqb (root ltree) 0)
                              then if(eqb (root rtree) 0)
                                then 0
                              else 0
                            else if(ltb (levels ltree) (levels rtree))
                              then 1 + levels rtree
                                else 1 + levels ltree
  end.

Definition height (b:BinTree) : nat :=
  match b with
  | leaf => 0
  | node n ltree rtree => levels b + 1
  end.

Fixpoint BS (x:nat) (b:BinTree) : bool :=
 match b with
  | leaf => false
  | node n ltree rtree => if eqb n x then true
                          else if ltb n x then BS x ltree
                          else BS x rtree
  end.

Fixpoint BSTminval (b : BinTree) : nat :=
  match b with
  | leaf => 0
  | node n ltree rtree => if eqb (root ltree) 0 then n
                          else BSTminval ltree
  end. 

Fixpoint BSTmaxval (b : BinTree) : nat :=
  match b with
  | leaf => 0
  | node n ltree rtree => if eqb (root rtree) 0 then n
                          else BSTmaxval rtree
  end. 


Compute (maximnat 12 0).
Compute ArbEx.
Compute root(ArbEx).
Compute (mirror ArbEx).
Compute BST(ArbEx).
Compute levels(ArbEx).
Compute height(ArbEx). 
Compute (BS 12 ArbEx).
Compute BSTminval(ArbEx).
Compute BSTmaxval(ArbEx).

(* Liste de numere naturale *)

Inductive List : Type := 
| empty_list
| element (n : nat) (l : List).  

Fixpoint count_elements (l : List) : nat := 
  match l with
  | empty_list => 0
  | element n empty_list => 1
  | element n remaining => 1 + (count_elements remaining)
  end.

Definition first_element (l : List) : nat :=
  match l with
  | empty_list => 0
  | element n remaining => n
  end.

Notation "x :: l" := (element x l) (at level 60, right associativity).
Notation "[ ]" := empty_list.
Notation "[ x ; .. ; y ]" := (element x .. (element y empty_list) ..).

Definition head (l : List) : nat :=
  match l with
  | empty_list => 0
  | a :: b => a
  end.

Fixpoint tail (l : List) : List :=
  match l with
  | empty_list => empty_list
  | n :: empty_list => [n]
  | h :: t => tail t
  end.

Fixpoint append (l1 l2 : List) : List :=
  match l1 with
  | empty_list => l2
  | h :: t => h :: (append t l2)
  end.

Notation "x ++ y" := (append x y) (right associativity, at level 60).

Definition ListEx1 := (element 5(element 2(element 3(element 7(empty_list))))).
Definition ListEx2 := 10::20::30::empty_list.
Definition ListEx3 := [1;2;3;4;5;6;7;8;9].

Compute empty_list.
Compute ListEx1.
Compute first_element ListEx2.
Compute count_elements ListEx3.
Compute head ListEx3.
Compute tail ListEx3.

Example test_append1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof.
reflexivity.
Qed.

Example test_append2: empty_list ++ [4;5] = [4;5].
Proof.
reflexivity.
Qed.

Example test_append3: [1;2;3] ++ empty_list = [1;2;3].
Proof.
reflexivity.
Qed.

Example test_head1: head [1;2;3] = 1.
Proof.
reflexivity.
Qed.

Example test_head2: head [] = 0.
Proof.
reflexivity.
Qed.

Example test_tail1: tail [1;2;3] = [3].
Proof.
reflexivity.
Qed.

Example test_tail2 : tail [] = [].
Proof.
reflexivity.
Qed.




Require Import String.
Definition bvar := string.
Definition ivar := string.
Definition lvar := string.
Definition btvar := string. 

Inductive AExp : Type := 
  | avar : ivar -> AExp
  | anum : nat -> AExp
  | aplus : AExp -> AExp -> AExp
  | amin : AExp -> AExp -> AExp
  | amul : AExp -> AExp -> AExp
  | adiv : AExp -> AExp -> AExp
  | amod : AExp -> AExp -> AExp.

Inductive BExp : Type :=
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp
| bequal: AExp -> AExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp.

Inductive LExp : Type :=
| LExp_empty : LExp
| LExp_tail : LExp -> LExp
| listapp : LExp -> LExp -> LExp.

Inductive BTExp : Type :=
| BTExp_leaf : BTExp
| BTmirr : BTExp -> BTExp.

Inductive Stmt :=
| bool_declaration : string -> Stmt
| int_declaration : string -> Stmt
| list_declaration: string -> Stmt
| btree_declaration: string -> Stmt
| assignment_bool : bvar -> BExp -> Stmt
| assignment_int : ivar -> AExp -> Stmt
| assignment_list : lvar -> LExp -> Stmt
| assignment_btree : btvar -> BTExp -> Stmt 
| sequence : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| forr : Stmt -> BExp -> Stmt -> Stmt -> Stmt
| break : Stmt
| continue : Stmt.

Notation "'If' B 'Then' S" := (ifthen B S) (at level 97).
Notation "'If' B 'Then' S1 'Else' S2" := (ifthenelse B S1 S2) (at level 97).
Notation "'bool' A" := (bool_declaration A) (at level 90).
Notation "'int' A" := (int_declaration A) (at level 90).
Notation "'List' A" := (list_declaration A) (at level 90).
Notation "'BinTree' A" := (btree_declaration A) (at level 90).
Notation "A b= B" := (assignment_bool A B) (at level 90).
Notation "A i= B" := (assignment_int A B) (at level 90).
Notation "A l= B" := (assignment_list A B) (at level 90).
Notation "A bt= B" := (assignment_btree A B) (at level 90).
Notation "S ;; S'" := (sequence S S') (at level 93, right associativity).
Notation "'For' S1 ;; B ;; S2 '{' S3 '}' " := (forr S1 B S2 S3) (at level 99).

Definition Env := 
| 

(*Fixpoint BinTreeToList (b : BinTree) : List :=
  match b with
  | leaf => empty_list
  | node n ltree rtree => n :: (BinTreeToList ltree) :: (BinTreeToList rtree) 
  end.

Fixpoint ListToBinTree (l : List) : BinTree := 
  match l with
  | empty_list => leaf
  | element 3 => 3 (leaf leaf)
  | h ++ t => node   
  end.
*)






