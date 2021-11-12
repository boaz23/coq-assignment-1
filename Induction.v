(** * Induction: Proof by Induction *)

(* ################################################################# *)
(** * Separate Compilation *)

(** Before getting started on this chapter, we need to import
    all of our definitions from the previous chapter: *)

From LF Require Export Basics.

(** For this [Require Export] command to work, Coq needs to be
    able to find a compiled version of [Basics.v], called [Basics.vo],
    in a directory associated with the prefix [LF].  This file is
    analogous to the [.class] files compiled from [.java] source files
    and the [.o] files compiled from [.c] files.

    First create a file named [_CoqProject] containing the following
    line (if you obtained the whole volume "Logical Foundations" as a
    single archive, a [_CoqProject] should already exist and you can
    skip this step):

      -Q . LF

    This maps the current directory ("[.]", which contains [Basics.v],
    [Induction.v], etc.) to the prefix (or "logical directory")
    "[LF]".  Proof General and CoqIDE read [_CoqProject]
    automatically, so they know to where to look for the file
    [Basics.vo] corresponding to the library [LF.Basics].

    Once [_CoqProject] is thus created, there are various ways to
    build [Basics.vo]:

     - In Proof General or CoqIDE, the compilation should happen
       automatically when you submit the [Require] line above to PG.

     - If you want to compile from the command line, generate a
       [Makefile] using the [coq_makefile] utility, which comes
       installed with Coq (if you obtained the whole volume as a
       single archive, a [Makefile] should already exist and you can
       skip this step):

         coq_makefile -f _CoqProject *.v -o Makefile

       Note: You should rerun that command whenever you add or remove
       Coq files to the directory.

       Now you can compile [Basics.v] by running [make] with the
       corresponding [.vo] file as a target:

         make Basics.vo

       All files in the directory can be compiled by giving no
       arguments:

         make

       Under the hood, [make] uses the Coq compiler, [coqc].  You can
       also run [coqc] directly:

         coqc -Q . LF Basics.v

       But [make] also calculates dependencies between source files to
       compile them in the right order, so [make] should generally be
       preferred over explicit [coqc].

    If you have trouble (e.g., if you get complaints about missing
    identifiers later in the file), it may be because the "load path"
    for Coq is not set up correctly.  The [Print LoadPath.] command
    may be helpful in sorting out such issues.

    In particular, if you see a message like

        Compiled library Foo makes inconsistent assumptions over
        library Bar

    check whether you have multiple installations of Coq on your
    machine.  It may be that commands (like [coqc]) that you execute
    in a terminal window are getting a different version of Coq than
    commands executed by Proof General or CoqIDE.

    - Another common reason is that the library [Bar] was modified and
      recompiled without also recompiling [Foo] which depends on it.
      Recompile [Foo], or everything if too many files are
      affected.  (Using the third solution above: [make clean; make].)

    One more tip for CoqIDE users: If you see messages like [Error:
    Unable to locate library Basics], a likely reason is
    inconsistencies between compiling things _within CoqIDE_ vs _using
    [coqc] from the command line_.  This typically happens when there
    are two incompatible versions of [coqc] installed on your
    system (one associated with CoqIDE, and one associated with [coqc]
    from the terminal).  The workaround for this situation is
    compiling using CoqIDE only (i.e. choosing "make" from the menu),
    and avoiding using [coqc] directly at all. *)

(* ################################################################# *)
(** * Proof by Induction *)

(** We can prove that [0] is a neutral element for [+] on the _left_
    using just [reflexivity].  But the proof that it is also a neutral
    element on the _right_ ... *)

Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.

(** ... can't be done in the same simple way.  Just applying
  [reflexivity] doesn't work, since the [n] in [n + 0] is an arbitrary
  unknown number, so the [match] in the definition of [+] can't be
  simplified.  *)

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

(** And reasoning by cases using [destruct n] doesn't get us much
    further: the branch of the case analysis where we assume [n = 0]
    goes through fine, but in the branch where [n = S n'] for some [n'] we
    get stuck in exactly the same way. *)

Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl.       (* ...but here we are stuck again *)
Abort.

(** We could use [destruct n'] to get one step further, but,
    since [n] can be arbitrarily large, we'll never get all the there
    if we just go on like this. *)

(** To prove interesting facts about numbers, lists, and other
    inductively defined sets, we often need a more powerful reasoning
    principle: _induction_.

    Recall (from high school, a discrete math course, etc.) the
    _principle of induction over natural numbers_: If [P(n)] is some
    proposition involving a natural number [n] and we want to show
    that [P] holds for all numbers [n], we can reason like this:
         - show that [P(O)] holds;
         - show that, for any [n'], if [P(n')] holds, then so does
           [P(S n')];
         - conclude that [P(n)] holds for all [n].

    In Coq, the steps are the same: we begin with the goal of proving
    [P(n)] for all [n] and break it down (by applying the [induction]
    tactic) into two separate subgoals: one where we must show [P(O)]
    and another where we must show [P(n') -> P(S n')].  Here's how
    this works for the theorem at hand: *)

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Like [destruct], the [induction] tactic takes an [as...]
    clause that specifies the names of the variables to be introduced
    in the subgoals.  Since there are two subgoals, the [as...] clause
    has two parts, separated by [|].  (Strictly speaking, we can omit
    the [as...] clause and Coq will choose names for us.  In practice,
    this is a bad idea, as Coq's automatic choices tend to be
    confusing.)

    In the first subgoal, [n] is replaced by [0].  No new variables
    are introduced (so the first part of the [as...] is empty), and
    the goal becomes [0 = 0 + 0], which follows by simplification.

    In the second subgoal, [n] is replaced by [S n'], and the
    assumption [n' + 0 = n'] is added to the context with the name
    [IHn'] (i.e., the Induction Hypothesis for [n']).  These two names
    are specified in the second part of the [as...] clause.  The goal
    in this case becomes [S n' = (S n') + 0], which simplifies to
    [S n' = S (n' + 0)], which in turn follows from [IHn']. *)

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** (The use of the [intros] tactic in these proofs is actually
    redundant.  When applied to a goal that contains quantified
    variables, the [induction] tactic will automatically move them
    into the context as needed.) *)

(** **** Exercise: 2 stars, standard (basic_induction)

    Prove the following using induction. You might need previously
    proven results. *)

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. rewrite -> add_0_r. reflexivity.
  - rewrite <- plus_n_Sm. rewrite <- IHn'. simpl. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (double_plus)

    Consider the following function, which doubles its argument: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (even_S)

    One inconvenient aspect of our definition of [even n] is the
    recursive call on [n - 2]. This makes proofs about [even n]
    harder when done by induction on [n], since we may need an
    induction hypothesis about [n - 2]. The following lemma gives an
    alternative characterization of [even (S n)] that works better
    with induction: *)

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
   intros n. induction n as [| n' IHn'].
  - reflexivity.
  - rewrite IHn'. rewrite negb_involutive. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (destruct_induction)

    Briefly explain the difference between the tactics [destruct]
    and [induction].

(* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_destruct_induction : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Proofs Within Proofs *)

(** In Coq, as in informal mathematics, large proofs are often
    broken into a sequence of theorems, with later proofs referring to
    earlier theorems.  But sometimes a proof will involve some
    miscellaneous fact that is too trivial and of too little general
    interest to bother giving it its own top-level name.  In such
    cases, it is convenient to be able to simply state and prove the
    needed "sub-theorem" right at the point where it is used.  The
    [assert] tactic allows us to do this. *)

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.

(** The [assert] tactic introduces two sub-goals.  The first is
    the assertion itself; by prefixing it with [H:] we name the
    assertion [H].  (We can also name the assertion with [as] just as
    we did above with [destruct] and [induction], i.e., [assert (n + 0
    + 0 = n) as H].)  Note that we surround the proof of this
    assertion with curly braces [{ ... }], both for readability and so
    that, when using Coq interactively, we can see more easily when we
    have finished this sub-proof.  The second goal is the same as the
    one at the point where we invoke [assert] except that, in the
    context, we now have the assumption [H] that [n + 0 + 0 = n].
    That is, [assert] generates one subgoal where we must prove the
    asserted fact and a second subgoal where we can use the asserted
    fact to make progress on whatever we were trying to prove in the
    first place. *)

(** As another example, suppose we want to prove that [(n + m)
    + (p + q) = (m + n) + (p + q)]. The only difference between the
    two sides of the [=] is that the arguments [m] and [n] to the
    first inner [+] are swapped, so it seems we should be able to use
    the commutativity of addition ([add_comm]) to rewrite one into the
    other.  However, the [rewrite] tactic is not very smart about
    _where_ it applies the rewrite.  There are three uses of [+] here,
    and it turns out that doing [rewrite -> add_comm] will affect only
    the _outer_ one... *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like add_comm should do the trick! *)
  rewrite add_comm.
  (* Doesn't work... Coq rewrites the wrong plus! :-( *)
Abort.

(** To use [add_comm] at the point where we need it, we can introduce
    a local lemma stating that [n + m = m + n] (for the _particular_ [m]
    and [n] that we are talking about here), prove this lemma using
    [add_comm], and then use it to do the desired rewrite. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.  Qed.

(* ################################################################# *)
(** * Formal vs. Informal Proof *)

(** "_Informal proofs are algorithms; formal proofs are code_." *)

(** What constitutes a successful proof of a mathematical claim?
    The question has challenged philosophers for millennia, but a
    rough and ready definition could be this: A proof of a
    mathematical proposition [P] is a written (or spoken) text that
    instills in the reader or hearer the certainty that [P] is true --
    an unassailable argument for the truth of [P].  That is, a proof
    is an act of communication.

    Acts of communication may involve different sorts of readers.  On
    one hand, the "reader" can be a program like Coq, in which case
    the "belief" that is instilled is that [P] can be mechanically
    derived from a certain set of formal logical rules, and the proof
    is a recipe that guides the program in checking this fact.  Such
    recipes are _formal_ proofs.

    Alternatively, the reader can be a human being, in which case the
    proof will be written in English or some other natural language,
    and will thus necessarily be _informal_.  Here, the criteria for
    success are less clearly specified.  A "valid" proof is one that
    makes the reader believe [P].  But the same proof may be read by
    many different readers, some of whom may be convinced by a
    particular way of phrasing the argument, while others may not be.
    Some readers may be particularly pedantic, inexperienced, or just
    plain thick-headed; the only way to convince them will be to make
    the argument in painstaking detail.  But other readers, more
    familiar in the area, may find all this detail so overwhelming
    that they lose the overall thread; all they want is to be told the
    main ideas, since it is easier for them to fill in the details for
    themselves than to wade through a written presentation of them.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that is guaranteed to
    convince every conceivable reader.

    In practice, however, mathematicians have developed a rich set of
    conventions and idioms for writing about complex mathematical
    objects that -- at least within a certain community -- make
    communication fairly reliable.  The conventions of this stylized
    form of communication give a fairly clear standard for judging
    proofs good or bad.

    Because we are using Coq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can
    completely forget about informal ones!  Formal proofs are useful
    in many ways, but they are _not_ very efficient ways of
    communicating ideas between human beings. *)

(** For example, here is a proof that addition is associative: *)

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite IHn'. reflexivity.  Qed.

(** Coq is perfectly happy with this.  For a human, however, it
    is difficult to make much sense of it.  We can use comments and
    bullets to show the structure a little more clearly... *)

Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity.   Qed.

(** ... and if you're used to Coq you might be able to step
    through the tactics one after the other in your mind and imagine
    the state of the context and goal stack at each point, but if the
    proof were even a little bit more complicated this would be next
    to impossible.

    A (pedantic) mathematician might write the proof something like
    this: *)

(** - _Theorem_: For any [n], [m] and [p],

      n + (m + p) = (n + m) + p.

    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show that

        0 + (m + p) = (0 + m) + p.

      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where

        n' + (m + p) = (n' + m) + p.

      We must now show that

        (S n') + (m + p) = ((S n') + m) + p.

      By the definition of [+], this follows from

        S (n' + (m + p)) = S ((n' + m) + p),

      which is immediate from the induction hypothesis.  _Qed_. *)

(** The overall form of the proof is basically similar, and of
    course this is no accident: Coq has been designed so that its
    [induction] tactic generates the same sub-goals, in the same
    order, as the bullet points that a mathematician would write.  But
    there are significant differences of detail: the formal proof is
    much more explicit in some ways (e.g., the use of [reflexivity])
    but much less explicit in others (in particular, the "proof state"
    at any given point in the Coq proof is completely implicit,
    whereas the informal proof reminds the reader several times where
    things stand). *)

(** **** Exercise: 2 stars, advanced, especially useful (add_comm_informal)

    Translate your solution for [add_comm] into an informal proof:

    Theorem: Addition is commutative.

    Proof: (* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_add_comm_informal : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (eqb_refl_informal)

    Write an informal proof of the following theorem, using the
    informal proof of [add_assoc] as a model.  Don't just
    paraphrase the Coq tactics into English!

    Theorem: [(n =? n) = true] for any [n].

    Proof: (* FILL IN HERE *)
*)
(** [] *)

(* ################################################################# *)
(** * More Exercises *)

(** **** Exercise: 3 stars, standard (mul_comm)

    Use [assert] to help prove [add_shuffle3].  You don't need to
    use induction yet. *)

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  (* Move parenthesis around so that m and n are together *)
  rewrite -> add_assoc. rewrite -> add_assoc.

  (* swap their position *)
  assert (H: m + n = n + m).
    { rewrite add_comm. reflexivity. }
  rewrite -> H. reflexivity.
Qed.

(*
  'mult_n_Sm' was found by searching.
  I could not find a proof for it even though it does not seem to belong to a standard library of Coq (or is it?).
  I think it was referenced in Basics.v but not proved.
  Regardless, just to stay clear, see a proof for that theorem here.
*)
Theorem mult_n_Sm' : forall (n m : nat),
  n * m + n = n * S m.
Proof.
  (* Feels like I wrote a too complex proof than necessary *)
  intros n m. induction n as [| n' IHn'].
  - (* n = 0 *)
    (*
      All of the constants are on the side that the definitions match on,
      so reflexivity will do here.
    *)
    reflexivity.

  - (* n = S n' *)
    (* Open up the definitions which use the S to get rid of it *)
    simpl.
    (* Group the n's together *)
    rewrite add_comm. rewrite -> add_shuffle3.
    (*
      Move the S on the left side to the outside
      so it encloses the left-side expression.
    *)
    simpl. rewrite add_comm. simpl. rewrite add_comm.
    (* Swap the order of these specific addends so it matches the induction hypothesis *)
    assert (H_swap: n' + (n' * m) = (n' * m) + n').
      { rewrite add_comm. reflexivity. }
    rewrite -> H_swap. rewrite -> IHn'. reflexivity.
Qed.

(** Now prove commutativity of multiplication.  You will probably want
    to look for (or define and prove) a "helper" theorem to be used in
    the proof of this one. Hint: what is [n * (1 + k)]? *)

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - rewrite -> mul_0_r. reflexivity.
  - (* Open up operations to get rid of the Ss *)
    simpl. rewrite <- mult_n_Sm.
    rewrite add_comm. rewrite -> IHn'. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (more_exercises)

    Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before you hack!) *)

Check leb.

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  intros n. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. destruct b as [|].
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p. intros H_n_leb_m. induction p as [| p' IHp'].
  - simpl. exact H_n_leb_m.
  - simpl. exact IHp'.
Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  intros n. reflexivity.
Qed.

Search plus outside Nat PeanoNat Mult ArithRing Nnat Pnat Minus Peano Gt Plus List BinPos.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n. simpl. rewrite -> add_0_r. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c. destruct b as [|].
  - destruct c as [|].
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Theorem add_shuffle4_2w3: forall (n1 n2 n3 n4 : nat),
  (n1 + n2) + (n3 + n4) = (n1 + n3) + (n2 + n4).
Proof.
  intros n1 n2 n3 n4.
  (* move the n2 closer to n4 *)
  rewrite <- add_assoc.
  assert (H_swap': n2 + (n3 + n4) = n3 + (n2 + n4)).
    { rewrite -> add_shuffle3. reflexivity. }
  rewrite -> H_swap'.
  (* Now, just need to reorder the parenthesis. *)
  rewrite <- add_assoc. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* Feels like I wrote a too complex proof than necessary *)
  intros n m p. induction p as [| p' IHp'].
  - (*
      The zero is not on the side the definitions match on,
      so a helper lemma is needed.
    *)
    rewrite ! mul_0_r. reflexivity.

  - (* Open up the Ss by using the distributive property *)
    rewrite <- ! mult_n_Sm.
    (*
      Just need to set the right order of operations
      so we can use the induction hypothesis.
    *)
    rewrite -> add_shuffle4_2w3. rewrite <- IHp'. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (*
      All of the constants are on the side that the definitions match on,
      so reflexivity will do here.
    *)
    reflexivity.

  - (* Open up the definitions which use the S to get rid of it *)
    simpl.
    (* distribute the p to have (m*p) and be able to use the induction hypothesis *)
    rewrite -> mult_plus_distr_r.
    rewrite <- IHn'. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (eqb_refl) *)

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (add_shuffle3')

    The [replace] tactic allows you to specify a particular subterm to
   rewrite and what you want it rewritten to: [replace (t) with (u)]
   replaces (all copies of) expression [t] in the goal by expression
   [u], and generates [t = u] as an additional subgoal. This is often
   useful when a plain [rewrite] acts on the wrong part of the goal.

   Use the [replace] tactic to do a proof of [add_shuffle3'], just like
   [add_shuffle3] but without needing [assert]. *)

Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  (* Move parenthesis around so that m and n are together *)
  rewrite -> add_assoc. rewrite -> add_assoc.

  (* swap their position *)
  replace (m + n) with (n + m). reflexivity.

  (* The main goal is done. Left to prove the swapping was legal *)
  rewrite add_comm. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (binary_commute)

    Recall the [incr] and [bin_to_nat] functions that you
    wrote for the [binary] exercise in the [Basics] chapter.  Prove
    that the following diagram commutes:

                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

    That is, incrementing a binary number and then converting it to
    a (unary) natural number yields the same result as first converting
    it to a natural number and then incrementing.

    Before you start working on this exercise, copy the definitions of
    [incr] and [bin_to_nat] from your solution to the [binary]
    exercise here so that this file can be graded on its own.  If you
    want to change your original definitions to make the property
    easier to prove, feel free to do so! *)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin)
.

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 n => B1 n
  | B1 n => B0 (incr n)
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => 0
  | B0 n => 0 + (2 * (bin_to_nat n))
  | B1 n => 1 + (2 * (bin_to_nat n))
  end.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b. induction b as [| n IHn | n IHn].
  - reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite -> ! add_0_r. rewrite -> IHn.
    rewrite -> add_shuffle4_2w3. simpl. reflexivity.
Qed.

(** [] *)

(** **** Exercise: 5 stars, advanced (binary_inverse)

    This is a further continuation of the previous exercises about
    binary numbers.  You may find you need to go back and change your
    earlier definitions to get things to work smoothly here.

    (a) First, write a function to convert natural numbers to binary
        numbers. *)

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | 0 => Z
  | S n' => incr (nat_to_bin n')
  end.

Example test_nat_to_bin1: nat_to_bin 0 = Z.
Proof.
  reflexivity.
Qed.

Example test_nat_to_bin2: nat_to_bin 1 = B1 Z.
Proof.
  reflexivity.
Qed.

Example test_nat_to_bin3: nat_to_bin 2 = B0 (B1 Z).
Proof.
  reflexivity.
Qed.

Example test_nat_to_bin4: nat_to_bin 6 = B0 (B1 (B1 Z)).
Proof.
  reflexivity.
Qed.

(** Prove that, if we start with any [nat], convert it to binary, and
    convert it back, we get the same [nat] we started with.  (Hint: If
    your definition of [nat_to_bin] involved any extra functions, you
    may need to prove a subsidiary lemma showing how such functions
    relate to [nat_to_bin].) *)

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> bin_to_nat_pres_incr.
    rewrite -> IHn'. reflexivity.
Qed.

(** (b) One might naturally expect that we could also prove the
        opposite direction -- that starting with a binary number,
        converting to a natural, and then back to binary should yield
        the same number we started with.  However, this is not the
        case!  Explain (in a comment) what the problem is.  (Your
        explanation will not be graded, but it's important that you
        get it clear in your mind before going on to the next
        part.) *)

(*
  (I looked at the theorm before writing this.)
  The problem seems to be that the roundtrip from bin to nat back to bin
  also normalizes the binary number (removes leading zeroeos).
  So if the binary number had a leading zero, the roundtrip will not
  be exactly the same representation (no leading zero).
*)

(** (c) Define a normalization function -- i.e., a function
        [normalize] going directly from [bin] to [bin] (i.e., _not_ by
        converting to [nat] and back) such that, for any binary number
        [b], converting [b] to a natural and then back to binary
        yields [(normalize b)].  Prove it.

        Warning: This part is a bit tricky -- you may end up defining
        several auxiliary lemmas.  One good way to find out what you
        need is to start by trying to prove the main statement, see
        where you get stuck, and see if you can find a lemma --
        perhaps requiring its own inductive proof -- that will allow
        the main proof to make progress.

        Hint 1: Don't define [normalize] using [nat_to_bin] and
        [bin_to_nat].

        Hint 2 (this will probably only make sense after you've
        thought about the exercise for a while by yourself): There are
        multiple ways of defining the [normalize] function, and some
        lead to substantially smoother proofs than others.  In
        particular, one way to define [normalize] is to try to "cut
        off" the normalization early, by checking whether all
        remaining digits are zero before every recursive call, while
        another strategy is to recurse all the way to the end of the
        binary number and then treat zero as a special case on the
        _result_ of the recursive call at each level.  The latter
        seems to work more smoothly, perhaps because it examines each
        digit of the binary number just once, while the former
        involves repeatedly "looking ahead" at the remaining bits to
        see if they are all zero.

        More generally, the shape of a proof by induction will match the
        recursive structure of the program you are verifying, so a good
        strategy for designing algorithms that are easy to verify is to
        make your recursions as simple as possible. *)

Fixpoint normalize (b:bin) : bin :=
  match b with
  | Z => Z
  | B0 b' => (
    let nb' := normalize b' in
      match nb' with
      | Z => Z
      | _ => B0 nb'
      end
  )
  | B1 b' => B1 (normalize b')
  end.

Example test_normalize_1: normalize Z = Z.
Proof. reflexivity. Qed.

Example test_normalize_2: normalize (B0 (B0 Z)) = Z.
Proof. reflexivity. Qed.

Example test_normalize_3: normalize (B1 (B0 (B0 Z))) = B1 Z.
Proof. reflexivity. Qed.

Example test_normalize_4: normalize (B1 (B0 (B1 (B0 (B0 Z))))) = B1 (B0 (B1 Z)).
Proof. reflexivity. Qed.

Example test_normalize_5: normalize (B0 (B0 (B0 (B0 (B1 Z))))) = B0 (B0 (B0 (B0 (B1 Z)))).
Proof. reflexivity. Qed.

Example test_normalize_6: normalize (B1 (B0 (B0 (B0 (B0 (B1 Z)))))) = B1 (B0 (B0 (B0 (B0 (B1 Z))))).
Proof. reflexivity. Qed.

Theorem normalize_Z_is_0: forall (b: bin),
  (normalize b = Z) -> (bin_to_nat b) = 0.
Proof.
  intros b. induction b as [| b' IHb' | b IHb'].
  - reflexivity.
  - simpl. rewrite -> add_0_r.
    destruct (normalize b') as [| _b | _b] eqn:Eb'nZ.
    + intros _H. rewrite -> ! IHb'. reflexivity. tauto.
    + discriminate.
    + discriminate.
  - simpl. discriminate.
Qed.

Theorem nat_double: forall (n: nat),
  n + n = 2 * n.
Proof.
  intros n. simpl.
  rewrite -> add_0_r. reflexivity.
Qed.

Theorem double_n_neq_0: forall (n: nat),
  (n <> 0) -> (n + n <> 0).
Proof.
  intros n. rewrite -> nat_double. intros H.
  destruct n as [| n'].
  - contradiction.
  - discriminate.
Qed.

Theorem bin_norm_not_Z: forall (b: bin),
  (normalize b <> Z) -> (bin_to_nat b <> 0).
Proof.
  intros b. induction b as [| b' IHb' | b IHb'].
  - simpl. contradiction.
  - simpl. rewrite -> add_0_r.
    destruct (normalize b') as [| _b | _b] eqn:Eb'nZ.
    + contradiction.
    + intros _H. apply double_n_neq_0.
      apply IHb'. discriminate.
    + intros _H. apply double_n_neq_0.
      apply IHb'. discriminate.
  - simpl. discriminate.
Qed.

Theorem nat_to_bin_double: forall (n: nat),
  (n <> 0) -> (nat_to_bin(2 * n) = B0 (nat_to_bin n)).
Admitted.
(* Proof.
  intros n. intros H. induction n as [| n' IHn'].
  - contradiction.
  - simpl.
Qed. *)

Theorem roundtrip_double: forall (b: bin),
  (normalize b <> Z) ->
  (nat_to_bin((bin_to_nat b) + ((bin_to_nat b) + 0)) = B0 (nat_to_bin (bin_to_nat b))).
Proof.
  intros b. intros H. rewrite -> add_0_r.
  rewrite -> nat_double. rewrite -> nat_to_bin_double.
  reflexivity.
  (* prove bin_to_nat b <> 0 *)
  (* inspired by https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.htm *)
  apply bin_norm_not_Z. exact H.
Qed.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intros b. induction b as [| b' IHb' | b' IHb'].
  (* Z *)
  - (* only constructors. reflexivity can take care of it. *)
    reflexivity.
  (* B0 *)
  - (* need to open up the (B0 b') to isolate b' *)
    simpl.
    (*
      as per the definition of normalize,
      the result depends on the result of the recursion.
      destruct here to match the "match" in normalize.
    *)
    destruct (normalize b') as [| _b | _b] eqn:Eb'nZ.
    (* Z *)
    + rewrite -> ! normalize_Z_is_0. reflexivity.
      (*
        using the normalize_Z_is_0 caused Coq to generate
        a goal to make sure the condition of the implies
        clause of the theorem holds.
        This is the proof it is true
        The proof is the exact assumption the destruct gave us:
        (normalize b') = Z.
      *)
      exact Eb'nZ.
    (* B0 *)
    + (*
        Extract B0 outside on the left to match the right.
        Then, we will be able to use the induction hypothesis.
      *)
      rewrite -> roundtrip_double. rewrite -> IHb'. reflexivity.
      (* prove that (normalize b') <> Z *)
      rewrite -> Eb'nZ. discriminate.
    (* B1 *)
    (* same case as B0 (as in the definition of normalize) *)
    + rewrite -> roundtrip_double. rewrite -> IHb'. reflexivity.
      rewrite -> Eb'nZ. discriminate.
  - (* need to open up the (B0 b') to isolate b' *)
    simpl.
    destruct (normalize b') as [| _b | _b] eqn:Eb'nZ.
    + rewrite -> ! normalize_Z_is_0. reflexivity.
      exact Eb'nZ.
    + (*
        Extract B0 outside on the left to match
        the B1 on the outside of the right.
      *)
      rewrite -> roundtrip_double. simpl.
      rewrite -> IHb'. reflexivity.
      rewrite -> Eb'nZ. discriminate.
    + (* same case as B0 (as in the definition of normalize) *)
      rewrite -> roundtrip_double. simpl.
      rewrite -> IHb'. reflexivity.
      rewrite -> Eb'nZ. discriminate.
Qed.

(** [] *)

(* 2021-11-10 18:33 *)
