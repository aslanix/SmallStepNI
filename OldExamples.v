
(*

Module Example.

Definition x := Id 1.
Definition y := Id 2.
Definition z := Id 3.

Definition m1 := 
   update_st (update_st (update_st empty_state x 0) y 1) z 2.

Definition m2 := 
   update_st (update_st (update_st empty_state x 0) y 6) z 9.

Definition Γ :=
   update_env (update_env (update_env empty_env x Low) y High) z High.

Lemma only_x_is_low_in_gamma:
  forall var, Γ var = Some Low -> var = x.  
Proof.
  intros. 
  unfold Γ in H.
  unfold update_env in H.
  repeat (destruct eq_id_dec; [ crush | ]).
  assert (@empty_env level var = None) by crush.
  rewrite H0 in H.
  crush.
Qed.

Example ex4:
  state_low_eq Γ m1 m2.
  unfold state_low_eq.

  unfold var_low_eq.
  intros.

  induction ℓ.

  apply only_x_is_low_in_gamma in H.

  rewrite H in H0,H1.
 
  assert (m1 x = Some 0) by crush.
  assert (m2 x = Some 0) by crush.
  assert (u = 0) by crush.
  assert (v = 0) by crush.
  rewrite H4, H5.

  apply VLEqL. crush.
  apply VLEqH. 
Qed.

End Example.

*)
