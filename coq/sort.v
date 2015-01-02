Require Import List.
Require Import Coq.Arith.Arith_base.
Import ListNotations.

  
Fixpoint Partition (x : nat) (l : list nat) :=
  match l with
    | nil => (nil, nil)
    | h :: t => match (Partition x t) with
                  | (less, greater) => if (lt_dec h x) then
                                         (h :: less, greater)
                                       else
                                         (less, h :: greater)
                end
  end.
                    

m
  Program Fixpoint SortList (l : list nat) :=
  match l with
    | nil => nil
    | h :: t => dest (Partition h t) as (less, greater) in
                   (SortList less) ++ [h] ++ (SortList greater)
  end.