Require Import Bool Arith List CpdtTactics SfLib LibTactics.
Require Import Coq.Program.Equality.


Set Implicit Arguments.


Ltac remove_duplicate_hypothesis := repeat
  match goal with 
    | [ H : ?orig, H' : ?orig |- _ ] => clear H'
  end.

Ltac destruct_split :=
  match goal with 
    | [ H : _ /\ _  |- _ ] => destruct H
    | [ H : _ \/ _  |- _ ] => destruct H
    | [ H : exists _,_ |- _ ] => destruct H
    | [ |- _ /\ _ ] => split
    | [ |- _ \/ _ ] => split
    | [ |- _ -> _ ] => intros     

  end.


Ltac super_destruct_split :=
  repeat (destruct_split; subst; auto).



Ltac clear_nq_facts:=

  match goal with 
    |   [  H  : ?X <> ?Y -> _ , 
           H' : ?X = ?Y |- _] =>
        clear H
    |   [  H  :  ?X = ?Y -> _ , 
           H' : ?X <> ?YL |- _] =>
        clear H                     
  end.
                





Ltac super_destruct := 
      repeat 
        match goal with  [ H : context [ _ /\ _ ] |- _ ] => 
                         destruct H 
        end.



Ltac subst_trivial:=
  repeat match goal 
         with [ H : ?a = ?a -> _ |- _] =>
              let H' := fresh in
              assert (a = a) as H' by auto;
                specialize (H H'); clear H'
         end; subst.



Ltac clear_impossible:=
  repeat match goal with 
             [ H : ?X <> ?X -> _ |- _ ] => clear H
               end.



Ltac specialize_gen:=
  match goal with 
    | [  H  : ?F -> _ , 
              H' : ?F |- _] =>
      specialize (H H')
    | [ H : ?X = ?X -> _ |- _ ] =>
      let h := fresh "H" 
      in
      assert (X = X) by auto;
        specialize (H h);
        clear h
                          
                          
  end.



Ltac cleanup := subst; subst_trivial; clear_impossible.
Ltac duplicate H := 
  let H' := fresh in assert (H' := H).


Ltac destruct_exists_conj:= 
  repeat 
    match goal with 
      | [ H: context [exists _,_ ] |- _] => destruct H
      | [ H: context [ _ /\ _ ] |- _] => destruct H
    end.



Ltac destruct_conj := 
            repeat match goal with 
                     | [ H: _ /\ _ |- _ ] => destruct H 
              end.


Ltac destruct_exists := 
            repeat match goal with 
                       | [ H : exists _, _ |- _ ] => destruct H
                   end.
