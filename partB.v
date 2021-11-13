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

(* Check the drop_app_split theorem. *)

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
  This is the one to check. The others were for
  experimantation on which one to choose and for fun.
*)
Theorem drop_app_split: forall (l1 l2: natlist) (n: nat),
  ((drop n (l1 ++ l2)) = (drop n l1) ++ (drop (n - length(l1)) l2)).
Proof.
  (*
    Not introducing l2 and n causes the induction hypothesis to be stronger:
    it can be used with any l2 and n, not just the particular one we would have introduced.
    Therefore, when decreasing l complexity, we're still able to use the induction hypothesis.
  *)
  intros l1. induction l1 as [| nl1' l1' IHl1'].
  - (* l = [] *)
    intros l2 n.
    rewrite -> drop_empty. destruct n as [| n'].
    + reflexivity.
    + reflexivity.
  - (* l = nl1' :: l' *)
    intros l2 n. simpl. destruct n as [| n'].
    + (* n = 0 *)
      reflexivity.
    + (* n > 0 *)
      simpl. rewrite -> IHl1'. reflexivity.
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

Theorem minus_n_le_m: forall (n m: nat),
  ((n <=? m) = true) -> ((n - m) = 0).
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - destruct m as [| m'] eqn:Em.
    + simpl. discriminate.
    + simpl. apply IHn'.
Qed.

Theorem minus_n_nlt_m_leq: forall (n m: nat),
  ((n <? m) = false) -> ((m <=? n) = true).
Proof.
  intros n. induction n as [| n' IHn'].
  - intros m. destruct m as [| m'].
    + reflexivity.
    + replace (0 <? S m') with true. discriminate.
      reflexivity.
  - intros m. destruct m as [| m'].
    + reflexivity.
    + simpl. replace (S n' <? S m') with (n' <? m').
      apply IHn'. reflexivity.
Qed.

Theorem drop_app_split2: forall (l1 l2: natlist) (n: nat),
  ((length l1 <? n) = false) -> ((drop n (l1 ++ l2)) = (drop n l1) ++ l2).
Proof.
  intros l1 l2 n.
  destruct (length(l1) <? n) as [|] eqn:l_l1_n.
  - discriminate.
  - intros _H. rewrite -> drop_app_split.
    apply minus_n_nlt_m_leq in l_l1_n as n_leq_len_l1.
    apply minus_n_le_m in n_leq_len_l1 as n_minus_len_l1_eq_0.
    rewrite -> n_minus_len_l1_eq_0.
    reflexivity.
Qed.
*)