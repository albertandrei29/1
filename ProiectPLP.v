Import Nat.
Module Type Int.

Inductive BinTree := 
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

Definition maxim (x y : nat) : nat := 
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

Compute (maxim 12 0).
Compute ArbEx.
Compute root(ArbEx).
Compute (mirror ArbEx).
Compute BST(ArbEx).
Compute levels(ArbEx).
Compute height(ArbEx). 
Compute (BS 12 ArbEx).
Compute BSTminval(ArbEx).
Compute BSTmaxval(ArbEx).
























