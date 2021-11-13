From LF Require Export Lists.
Import NatList.

Fixpoint drop (n: nat) (l: natlist) : natlist :=
  match n, l with
  | 0, _ => l
  | _, [] => []
  | S n', m :: l' => drop n' l'
  end.

Example test_drop_1: drop 0 [] = [].
Proof. reflexivity. Qed.

Example test_drop_2: drop 5 [] = [].
Proof. reflexivity. Qed.

Example test_drop_3: drop 0 [1;2;6] = [1;2;6].
Proof. reflexivity. Qed.

Example test_drop_4: drop 1 [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Example test_drop_5: drop 3 [1;2;3] = [].
Proof. reflexivity. Qed.

Example test_drop_6: drop 3 [1;2;3;4] = [4].
Proof. reflexivity. Qed.

Example test_drop_7: drop 5 [1;2;3;4] = [].
Proof. reflexivity. Qed.

Example test_drop_8: drop 7 [1;2;3;4] = [].
Proof. reflexivity. Qed.
(*
Theorem list_empty: forall (l: natlist),
  ((length l) = 0) -> l = [].
Proof.
  intros l. destruct l as [| n l'].
  - reflexivity.
  - simpl. discriminate.
Qed.

Theorem drop_0: forall (l: natlist),
  drop 0 l = l.
Proof.
  intros l. reflexivity.
Qed.
*)
Theorem drop_empty: forall (n: nat),
  drop n [] = [].
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity.
Qed.
(*
Theorem drop_len_leq_n: forall (l: natlist) (n: nat),
  ((length l <=? n) = true) -> (drop n l = []).
Proof.
  intros l. induction l as [| nl' l' IHl'].
  - intros n. rewrite -> drop_empty. reflexivity.
  - simpl. intros n. destruct n as [| n'].
    + discriminate.
    + simpl. intros Hll_leb_n'.
      rewrite -> IHl'. reflexivity.
      exact Hll_leb_n'.
      (* this also works: simpl. apply IHl'. *)
Qed.

Theorem drop_len_eq_n: forall (l: natlist) (n: nat),
  (length(l) = n) -> (drop n l = []).
Proof.
  intros l n. intros H_l_len_n.
  rewrite -> drop_len_leq_n. reflexivity.
  rewrite -> H_l_len_n. rewrite -> leb_refl. reflexivity.
Qed.
*)

Theorem drop_app_split: forall (l1 l2: natlist) (n: nat),
  ((length l1 <? n) = false) -> ((drop n (l1 ++ l2)) = (drop n l1) ++ l2).
Proof.
  (*
    Not introducing l2 and n causes the induction hypothesis to be stronger:
    it can be used with any l2 and n, not just the particular one we would have introduced.
    Therefore, when decreasing l complexity, we're still able to use the induction hypothesis.
  *)
  intros l1. induction l1 as [| nl1' l1' IHl1'].
  - (* l = [] *)
    intros l2 n.
    rewrite -> drop_empty.
    simpl. destruct n as [| n'] eqn:En.
    + (* n = 0 *)
      reflexivity.
    + (*
        n > 0.
        impossible case: length l1 = 0 and n > 0. Thus: length l1 <? n = true
      *)
      assert (H_nlt: (0 <? S n') = true).
        { reflexivity. }
      rewrite -> H_nlt. discriminate.
  - (* l = nl1' :: l' *)
    intros l2 n. simpl. destruct n as [| n'] eqn:En.
    + (* n = 0 *)
      reflexivity.
    + (* n > 0 *)
      simpl.
      (* isolate (length l') and n' by removing the Ss *)
      assert (H_S_len_l': (S (length l1') <? S n') = ((length l1') <? n')).
        { reflexivity. }
      rewrite -> H_S_len_l'.
      (*
        Now we can use the induction hypothesis.
        Except we will need to prove it's precondition later.
        The precondition to it is exactly the precondition of the current goal.
      *)
      intros len_l1'_lt_n'. rewrite -> IHl1'.
      reflexivity. exact len_l1'_lt_n'.
Qed.