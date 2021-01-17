Import Nat.
Module Type Int.

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

Fixpoint nth_element (l : List) (x : nat) : nat := 
  match l with
  | empty_list => 0
  | a :: b => nth_element b x-1
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
Compute nth_element ListEx3 3.

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

Require Import Strings.String.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Scheme Equality for string.

Inductive TypeVar := 
| int : nat -> TypeVar
| boolean : bool -> TypeVar
| lists : List -> TypeVar
| btree : BinTree -> TypeVar
| undeclared : TypeVar. 

Scheme Equality for TypeVar.

Inductive Pair (T1 T2 : Type) :=
  | pair (t1 : T1) (t2 : T2).

Definition Env := string -> TypeVar.
Definition env : Env := 
  fun x => undeclared.
Compute env "x".

Definition updateEnv (env : Env) (x : string) (r : TypeVar) : Env := 
  fun y => if(string_eq_dec y x) then r else (env y).

Inductive AExp : Type := 
  | avar : string -> AExp
  | anum : nat -> AExp
  | aplus : AExp -> AExp -> AExp
  | amin : AExp -> AExp -> AExp
  | amul : AExp -> AExp -> AExp
  | adiv : AExp -> AExp -> AExp
  | amod : AExp -> AExp -> AExp.

Coercion anum : nat >-> AExp.
Coercion avar : string >-> AExp.
Notation "A +' B" := (aplus A B) (at level 11).
Notation "A *' B" := (amul A B) (at level 8).
Notation "A /' B" := (adiv A B) (at level 8).
Notation "A %' B" := (amod A B) (at level 9).
Notation "A -' B" := (amin A B) (at level 11).

Reserved Notation "A =[ S ]=> N" (at level 60).

Inductive aeval : AExp -> Env -> nat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n
| var : forall v sigma, avar v =[ sigma ]=>  match (sigma v) with
                                              | int x => x
                                              | _ => 0
                                              end
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (i1 + i2) ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (i1 * i2) ->
    a1 *' a2 =[sigma]=> n
| substract : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (i1 - i2) ->
    a1 -' a2 =[sigma]=> n
| division : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (i1 / i2) ->
    a1 /' a2 =[sigma]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (Nat.modulo i1 i2) ->
    a1 %' a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

(*exemple*)

Example aevalEx : "a" +' "a" *' 2 =[updateEnv env "a" (int 10)]=> 30.
Proof.
-  eapply add.
   eapply var.
   eapply times.
   eapply var.
   eapply const.
   eauto.
   eauto.
Qed.

Inductive BExp : Type :=
| bvar : string -> BExp 
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp
| bequal: AExp -> AExp -> BExp
| blessthan : AExp -> AExp -> BExp.

Notation "A ==' B" := (bequal A B) (at level 70).
Notation "A <' B" := (blessthan A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).

Reserved Notation "B ={ S }=> B'" (at level 70).

Inductive beval : BExp -> Env -> bool -> Prop :=
| b_true : forall sigma, btrue ={ sigma }=> true
| b_false : forall sigma, bfalse ={ sigma }=> false
| b_var : forall v sigma, bvar v ={ sigma }=>   match (sigma v) with
                                              | boolean x => x
                                              | _ => false
                                              end
| b_equal : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (Nat.eqb i1 i2) ->
    a1 ==' a2 ={ sigma }=> b
| b_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (Nat.leb i1 i2) ->
    a1 <' a2 ={ sigma }=> b
| b_not : forall a1 i1 sigma b,
    a1 ={ sigma }=> i1 ->
    b = (negb i1) ->
    !'a1 ={ sigma }=> b
| b_and : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (andb i1 i2) ->
    (a1 &&' a2) ={ sigma }=> b 
| b_or : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (orb i1 i2) ->
    (a1 ||' a2) ={ sigma }=> b 
where "B ={ S }=> B'" := (beval B S B').

(*exemple*)

Example bevalEx : band btrue ("z" <' 9) ={ updateEnv env "z" (int 7) }=> true.
Proof.
- eapply b_and.
  eapply b_true.
  eapply b_lessthan.
  eapply var.
  eapply const.
  eauto.
  eauto.
Qed.  

Inductive Stmt :=
| bool_declaration : string -> BExp -> Stmt
| int_declaration : string -> AExp -> Stmt
(*| list_declaration: string -> Stmt
| btree_declaration: string -> Stmt*)
(*| assignment_list : lvar -> LExp -> Stmt
| assignment_btree : btvar -> BTExp -> Stmt*) 
| sequence : Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| forr : Stmt -> BExp -> Stmt -> Stmt -> Stmt
| switch : string -> list(Pair TypeVar Stmt) -> Stmt
| break : Stmt.

Notation "'If' B 'Then' S" := (ifthen B S) (at level 97).
Notation "'If' B 'Then' S1 'Else' S2" := (ifthenelse B S1 S2) (at level 97).
Notation "X :b= A" := (bool_declaration X A) (at level 90).
Notation "X :i= A" := (int_declaration X A) (at level 90).
(*Notation "'List' A" := (list_declaration A) (at level 90).
Notation "'BinTree' A" := (btree_declaration A) (at level 90).
Notation "A l= B" := (assignment_list A B) (at level 90).
Notation "A bt= B" := (assignment_btree A B) (at level 90).*)
Notation "S ;; S'" := (sequence S S') (at level 93, right associativity).

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

Fixpoint evalSwitch (s : string)(env : Env)(l : (list(Pair TypeVar Stmt))) :=
match l with
| nil => break
| ((pair _ _ x y) :: l') => match (env s) with
                              | z => if(TypeVar_beq z x) then y 
                                     else (evalSwitch s env l')
                            end
end.

Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_int_decl: forall a i x sigma sigma',
   a =[ sigma ]=> i ->
   sigma' = (updateEnv sigma x (int i)) ->
   (x :i= a) -{ sigma }-> sigma'
| e_bool_decl: forall a i x sigma sigma',
   a ={ sigma }=> i ->
   sigma' = (updateEnv sigma x (boolean i)) ->
   (x :b= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_if_then : forall b s sigma,
    ifthen b s -{ sigma }-> sigma
| e_if_then_elsetrue : forall b s1 s2 sigma sigma',
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_if_then_elsefalse : forall b s1 s2 sigma sigma',
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
| e_break : forall sigma,
    (break) -{ sigma }-> sigma
| e_switch : forall s1 sigma sigma' list s,
    s1 = (evalSwitch s sigma list) ->
    s1 -{ sigma }-> sigma' ->
    (switch s list) -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').

(*exemple*)

Example bool_decl_example : exists sigma, ("x" :b= btrue)-{ env }-> sigma /\(sigma "x" = (boolean true)).
Proof.
eexists.
split.
- eapply e_bool_decl.
  eapply b_true. 
  eauto. 
- eauto.
Qed.

Example ifthenelsefalse : exists sigma, (If bfalse Then break Else "a" :i= 5) -{ env }-> sigma /\ (sigma "a" = (int 5)).
Proof.
eexists.
split.
- eapply e_if_then_elsefalse.
  eapply b_false.
  eapply e_int_decl.
  eapply const.
  eauto.
-eauto.
Qed.

Example whiletrue_example : exists sigma, while(!'("x" ==' 3))("z" :i= "z" +' 1 ;; "x" :i= "x" +' 1) -{ updateEnv (updateEnv env "z" (int 11)) "x" (int 2)}-> sigma /\ (sigma "z" = (int 12)).
Proof.
  eexists.
  split.
  eapply e_whiletrue.
  eapply b_not.
  eapply b_equal.
  eapply var.
  eapply const.
  eauto.
  eauto.
  eapply e_seq.
  eapply e_seq.
  eapply e_int_decl.
  eapply add.
  eapply var.
  eapply const.
  eauto.
  eauto.
  eapply e_int_decl.
  eapply add.
  eapply var.
  eapply const.
  eauto.
  eauto.
  (*a doua iteratie*)
  eapply e_whilefalse.
  eapply b_not.
  eapply b_equal.
  eapply var.
  eapply const.
  eauto.
  eauto.
  eauto.
Qed.

Example switch_example : exists sigma, ("x" :i= 7 ;; switch "x" ((pair _ _ (int 29) ("bb" :b= bfalse)) :: (pair _ _ (int 3) ("bb" :b= bfalse)) :: (pair _ _ (int 7) ("bb" :b= btrue)) :: nil)) -{ env }-> sigma /\ (sigma "bb" = (boolean true)).
Proof.
eexists.
split.
- eapply e_seq.
  eapply e_int_decl.
  eapply const.
  eauto.
  eapply e_switch.
  eauto.
  simpl.
  eapply e_bool_decl.
  eapply b_true.
  eauto.
- eauto.
Qed.





