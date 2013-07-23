(** * Imp: Simple Imperative Programs *)

(* $Date: 2012-09-08 20:51:57 -0400 (Sat, 08 Sep 2012) $ *)

(** In this chapter, we begin a new direction that will
    continue for the rest of the course.  Up to now we've been mostly
    studying Coq itself, but from now on we'll mostly be using Coq to
    formalize other things.

    Our first case study is a _simple imperative programming language_
    called Imp.  Here is a familiar mathematical function written in
    Imp.
     Z ::= X;
     Y ::= 1;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;
       Z ::= Z - 1
     END
*)

(** This chapter looks at how to define the _syntax_ and _semantics_
    of Imp; the chapters that follow develop a theory of _program
    equivalence_ and introduce _Hoare Logic_, the best-known logic for
    reasoning about imperative programs. *)

(* ####################################################### *)
(** *** Sflib *)

(** A minor technical point: Instead of asking Coq to import our
    earlier definitions from chapter [Logic], we import a small library
    called [Sflib.v], containing just a few definitions and theorems
    from earlier chapters that we'll actually use in the rest of the
    course.  This change should be nearly invisible, since most of what's
    missing from Sflib has identical definitions in the Coq standard
    library.  The main reason for doing it is to tidy the global Coq
    environment so that, for example, it is easier to search for
    relevant theorems. *)

Require Export SfLib.

(* ####################################################### *)
(** * Arithmetic and Boolean Expressions *)

(** We'll present Imp in three parts: first a core language of
    _arithmetic and boolean expressions_, then an extension of these
    expressions with _variables_, and finally a language of _commands_
    including assignment, conditions, sequencing, and loops. *)

(* ####################################################### *)
(** ** Syntax *)

Module AExp.

(** These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)

Inductive aexp : Type := 
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type := 
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(** In this chapter, we'll elide the translation from the
    concrete syntax that a programmer would actually write to these
    abstract syntax trees -- the process that, for example, would
    translate the string ["1+2*3"] to the AST [APlus (ANum
    1) (AMult (ANum 2) (ANum 3))].  The optional chapter [ImpParser]
    develops a simple implementation of a lexical analyzer and parser
    that can perform this translation.  You do _not_ need to
    understand that file to understand this one, but if you haven't
    taken a course where these techniques are covered (e.g., a
    compilers course) you may want to skim it. *)

(** For comparison, here's a conventional BNF (Backus-Naur Form)
    grammar defining the same abstract syntax: 
    aexp ::= nat
           | aexp '+' aexp
           | aexp '-' aexp
           | aexp '*' aexp

    bexp ::= true
           | false
           | aexp '=' aexp
           | aexp '<=' aexp
           | bexp 'and' bexp
           | 'not' bexp 
*)

(** Compared to the Coq version above...

       - The BNF is more informal -- for example, it gives some
         suggestions about the surface syntax of expressions (like the
         fact that the addition operation is written [+] and is an
         infix symbol) while leaving other aspects of lexical analysis
         and parsing (like the relative precedence of [+], [-], and
         [*]) unspecified.  Some additional information -- and human
         intelligence -- would be required to turn this description
         into a formal definition (when implementing a compiler, for
         example).

         The Coq version consistently omits all this information and
         concentrates on the abstract syntax only.

       - On the other hand, the BNF version is lighter and 
         easier to read.  Its informality makes it flexible, which is
         a huge advantage in situations like discussions at the
         blackboard, where conveying general ideas is more important
         than getting every detail nailed down precisely. 

         Indeed, there are dozens of BNF-like notations and people
         switch freely among them, usually without bothering to say which
         form of BNF they're using because there is no need to: a
         rough-and-ready informal understanding is all that's
         needed. *)

(** It's good to be comfortable with both sorts of notations: informal
    ones for communicating between humans and formal ones for carrying
    out implementations and proofs. *)

(* ####################################################### *)
(** ** Evaluation *)

(** _Evaluating_ an arithmetic expression produces a number. *)

Fixpoint aeval (e : aexp) : nat :=
  match e with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1: 
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(** Similarly, evaluating a boolean expression yields a boolean. *)

Fixpoint beval (e : bexp) : bool :=
  match e with 
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2   => ble_nat (aeval a1) (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* ####################################################### *)
(** ** Optimization *)

(** We haven't defined very much yet, but we can already get
    some mileage out of the definitions.  Suppose we define a function
    that takes an arithmetic expression and slightly simplifies it,
    changing every occurrence of [0+e] (i.e., [(APlus (ANum 0) e])
    into just [e]. *)
Fixpoint my_optimize_0plus (e:aexp) : aexp :=
         match e with
         | ANum n => ANum n
         | APlus a1 a2 =>match (aeval a1) with
                        | 0 => my_optimize_0plus a2
                        |S n =>APlus (my_optimize_0plus a1) (my_optimize_0plus a2)
                        end
         | AMinus a1 a2 => AMinus (my_optimize_0plus a1) (my_optimize_0plus a2)
         | AMult a1 a2 => AMult (my_optimize_0plus a1)(my_optimize_0plus a2)
         end.
Example test_my_optimize_0plus1: 
        my_optimize_0plus (APlus (ANum 0) (ANum 1)) = ANum 1.
Proof. simpl. reflexivity. Qed.
Example test_my_optimize_0plus2:
        my_optimize_0plus (APlus (APlus (ANum 0)(ANum 0))(AMult (ANum 2)(ANum 8)))=AMult (ANum 2)(ANum 8).
Proof. simpl. reflexivity. Qed.
Example test_my_optimize_0plus3:
        my_optimize_0plus (AMult (APlus (ANum 0)(ANum 8))(ANum 2)) = AMult (ANum 8)(ANum 2).
Proof. simpl. reflexivity. Qed.
Example test_my_optimize_0plus4: 
  my_optimize_0plus (APlus (ANum 2) 
                        (APlus (ANum 0) 
                               (APlus (ANum 0) (ANum 1)))) 
  = APlus (ANum 2) (ANum 1).
Proof. simpl. reflexivity. Qed.
Example test_my_optimize_0plus5:
        my_optimize_0plus (APlus (AMult (ANum 0)(ANum 9))(ANum 8))=ANum 8.
Proof. simpl. reflexivity. Qed.
Fixpoint optimize_0plus (e:aexp) : aexp := 
  match e with
  | ANum n => 
      ANum n
  | APlus (ANum 0) e2 => 
      optimize_0plus e2
  | APlus e1 e2 => 
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => 
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => 
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

(** To make sure our optimization is doing the right thing we
    can test it on some examples and see if the output looks OK. *)

Example test_optimize_0plus: 
  optimize_0plus (APlus (ANum 2) 
                        (APlus (ANum 0) 
                               (APlus (ANum 0) (ANum 1)))) 
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed. 
Example test_optimize_0plus_compare:
        optimize_0plus (APlus (AMult (ANum 0)(ANum 9))(ANum 8))=APlus (AMult (ANum 0)(ANum 9))(ANum 8).
Proof. simpl. reflexivity. Qed.

(**
Note that example [test_optimize_0plus_compare] and [test_my_optimize_0plus5]
show that [my_optimize_0plus] is different from [optimize_0plus].
*)

(** But if we want to be sure the optimization is correct --
    i.e., that evaluating an optimized expression gives the same
    result as the original -- we should prove it. *)
Theorem my_optimize_0plus_sound1: forall e,
aeval (my_optimize_0plus e) = aeval e.
Proof.
intros. induction e. 
Case ("1"). reflexivity.
Case ("2"). simpl. destruct (aeval e1).
     SCase ("0"). simpl. apply IHe2.
     SCase ("S n"). simpl. rewrite->IHe1. rewrite->IHe2. simpl.
                    reflexivity.
Case ("3"). simpl. rewrite->IHe1. rewrite->IHe2. reflexivity.
Case ("4"). simpl.  rewrite->IHe1. rewrite->IHe2. reflexivity.
Qed.

Theorem my_optimize_0plus_sound1': forall e,
aeval (my_optimize_0plus e) = aeval e.
Proof.
intros.
induction e; try (simpl;rewrite->IHe1;rewrite->IHe2;reflexivity);try (reflexivity).
Case ("2"). simpl. destruct (aeval e1); try(simpl;rewrite->IHe1;rewrite->IHe2;simpl;reflexivity);try (simpl;apply IHe2).
Qed.
          
Lemma my_optimize_0plus_sound2_1: forall e1 e2 e3 e4:aexp,
     (aeval e1) + (aeval e2) = (aeval e3) + (aeval e4)->aeval (APlus e1 e2)=(aeval e3)+(aeval e4).
Proof.
intros. simpl. apply H. Qed.
Theorem my_optimize_0plus_sound2: forall e,
aeval (optimize_0plus e) = aeval e.
Proof.
intros e. induction e.
Case ("ANum"). simpl. reflexivity.
Case ("APlus"). simpl. destruct e1.
    SCase ("ANum"). destruct n.
          SSCase ("0"). simpl. rewrite->IHe2. reflexivity.
          SSCase ("S"). simpl. rewrite->IHe2. reflexivity.
    SCase ("APlus").  apply my_optimize_0plus_sound2_1. rewrite->IHe1. rewrite->IHe2.
                     reflexivity.
    SCase ("AMinus"). apply my_optimize_0plus_sound2_1.  rewrite->IHe1. rewrite->IHe2.
                     reflexivity.
    SCase ("AMult").  apply my_optimize_0plus_sound2_1.  rewrite->IHe1. rewrite->IHe2.
                     reflexivity.
Case ("AMinus"). simpl. rewrite ->IHe1. rewrite->IHe2. reflexivity.
Case ("AMult"). simpl. rewrite->IHe1. rewrite->IHe2. reflexivity.
Qed.

Theorem my_optimize_0plus_sound2': forall e,
aeval (optimize_0plus e) = aeval e.
Proof.
intros e. induction e; try (simpl;rewrite->IHe1;rewrite->IHe2;reflexivity);try(reflexivity).
Case ("APlus"). simpl. destruct e1; try (apply my_optimize_0plus_sound2_1;rewrite->IHe1;rewrite->IHe2;reflexivity).
SCase ("ANum"). destruct n; try (simpl;rewrite->IHe2;reflexivity).
Qed.

Theorem optimize_0plus_sound: forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e. induction e.
  Case "ANum". reflexivity.
  Case "APlus". destruct e1.
    SCase "e1 = ANum n". destruct n.
      SSCase "n = 0".  simpl. apply IHe2. 
      SSCase "n <> 0". simpl. rewrite IHe2. reflexivity.
    SCase "e1 = APlus e1_1 e1_2". 
      simpl. simpl in IHe1. rewrite IHe1. 
      rewrite IHe2. reflexivity.
    SCase "e1 = AMinus e1_1 e1_2". 
      simpl. simpl in IHe1. rewrite IHe1. 
      rewrite IHe2. reflexivity.
    SCase "e1 = AMult e1_1 e1_2". 
      simpl. simpl in IHe1. rewrite IHe1. 
      rewrite IHe2. reflexivity.
  Case "AMinus".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  Case "AMult".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.  Qed.

(* ####################################################### *)
(** * Coq Automation *)

(** The repetition in this last proof is starting to be a little
    annoying.  If either the language of arithmetic expressions or the
    optimization being proved sound were significantly more complex,
    it would begin to be a real problem.
 
    So far, we've been doing all our proofs using just a small handful
    of Coq's tactics and completely ignoring its powerful facilities
    for constructing parts of proofs automatically.  This section
    introduces some of these facilities, and we will see more over the
    next several chapters.  Getting used to them will take some
    energy -- Coq's automation is a power tool -- but it will allow us
    to scale up our efforts to more complex definitions and more
    interesting properties without becoming overwhelmed by boring,
    repetitive, low-level details. *)

(* ####################################################### *)
(** ** Tacticals *)

(** _Tacticals_ is Coq's term for tactics that take other tactics as
    arguments -- "higher-order tactics," if you will.  *)

(* ####################################################### *)
(** *** The [repeat] Tactical *)

(** The [repeat] tactical takes another tactic and keeps applying
    this tactic until the tactic fails. Here is an example showing
    that [100] is even using repeat. *)

Theorem ev100 : ev 100.
Proof.
  apply ev_SS.
  repeat (apply ev_SS). (* applies ev_SS 50 times,
                           then [apply ev_SS] fails *)
  apply ev_0.           
Qed.
(* Print ev100. *)

(** The [repeat T] tactic never fails; if the tactic [T] doesn't apply
    to the original goal, then repeat still succeeds without changing
    the original goal (it repeats zero times). *)

Theorem ev100' : ev 100.
Proof.
  repeat (apply ev_0). (* doesn't fail, applies ev_0 zero times *)
  repeat (apply ev_SS). apply ev_0. (* we can continue the proof *)
Qed.
(**
Theorem infinite_loop:
        6 = 6.
Proof.
repeat simpl. reflexivity. Qed.
 *)

(** The [repeat T] tactic does not have any bound on the number of
    times it applies [T]. If [T] is a tactic that always succeeds then
    repeat [T] will loop forever (e.g. [repeat simpl] loops forever
    since [simpl] always succeeds). While Coq's term language is
    guaranteed to terminate, Coq's tactic language is not. *)


(* ####################################################### *)
(** *** The [try] Tactical *)

(** A similar tactical is [try]: If [T] is a tactic, then [try T]
    is a tactic that is just like [T] except that, if [T] fails, 
    [try T] _successfully_ does nothing at all (instead of failing). *)

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. (* this just does [reflexivity] *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* just [reflexivity] would have failed *)
  apply HP. (* we can still finish the proof in some other way *)
Qed.

(** Using [try] in a completely manual proof is a bit silly, but we'll
    see below that [try] is very useful for doing automated proofs
    in conjunction with the [;] tactical. *)

(* ####################################################### *)
(** *** The [;] Tactical (Simple Form) *)

(** In its simplest and most commonly used form, the [;] tactical
    takes 2 tactics as argument: [T;T'] first performs the tactic [T]
    and then performs the tactic [T'] on _each subgoal_ generated by
    [T]. *)

(** For example, consider the following trivial lemma: *)

Lemma foo : forall n, ble_nat 0 n = true. 
Proof. 
  intros.
  destruct n. 
    (* Leaves two subgoals...  *) 
    Case "n=0". simpl. reflexivity.
    Case "n=Sn'". simpl. reflexivity.
    (* ... which are discharged similarly *)
Qed.

(** We can simplify this proof using the [;] tactical: *)

Lemma foo' : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n; (* [destruct] the current goal *)
  simpl; (* then [simpl] each resulting subgoal *)
  reflexivity. (* then do [reflexivity] on each resulting subgoal *)
Qed.

(** Using [try] and [;] together, we can get rid of the repetition in
    the proof that was bothering us a little while ago. *)

Theorem optimize_0plus_sound': forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  induction e; 
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity).
  (* The remaining cases -- ANum and APlus -- are more
     interesting... *)
  Case "ANum". reflexivity.
  Case "APlus". 
    destruct e1; 
      (* Again, most cases follow directly by the IH *)
      try (simpl; simpl in IHe1; rewrite IHe1; 
           rewrite IHe2; reflexivity).
    (* The interesting case, on which the [try...] does nothing, 
       is when [e1 = ANum n]. In this case, we have to destruct 
       [n] (to see whether the optimization applies) and rewrite 
       with the induction hypothesis. *)
    SCase "e1 = ANum n". destruct n;
      simpl; rewrite IHe2; reflexivity.   Qed.

(** Coq experts often use this "[...; try... ]" idiom after a
    tactic like [induction] to take care of many similar cases all at
    once.  Naturally, this practice has an analog in informal
    proofs. *)
(** Here is an informal proof of this theorem that
    matches the structure of the formal one:
    
    _Theorem_: For all arithmetic expressions [e],
       aeval (optimize_0plus e) = aeval e.
    _Proof_: By induction on [e].  The [AMinus] and [AMult] cases
    follow directly from the IH.  The remaining cases are as follows:

      - Suppose [e = ANum n] for some [n].  We must show 
          aeval (optimize_0plus (ANum n)) = aeval (ANum n).
        This is immediate from the definition of [optimize_0plus].
    
      - Suppose [e = APlus e1 e2] for some [e1] and [e2].  We
        must show
          aeval (optimize_0plus (APlus e1 e2)) 
        = aeval (APlus e1 e2).
        Consider the possible forms of [e1].  For most of them,
        [optimize_0plus] simply calls itself recursively for the
        subexpressions and rebuilds a new expression of the same form
        as [e1]; in these cases, the result follows directly from the
        IH.

        The interesting case is when [e1 = ANum n] for some [n].
        If [n = ANum 0], then
          optimize_0plus (APlus e1 e2) = optimize_0plus e2
        and the IH for [e2] is exactly what we need.  On the other
        hand, if [n = S n'] for some [n'], then again [optimize_0plus]
        simply calls itself recursively, and the result follows from
        the IH.  [] *)
    
(** This proof can still be improved: the first case (for [e = ANum
    n]) is very trivial -- even more trivial than the cases that we
    said simply followed from the IH -- yet we have chosen to write it
    out in full.  It would be better and clearer to drop it and just
    say, at the top, "Most cases are either immediate or direct from
    the IH.  The only interesting case is the one for [APlus]..."  We
    can make the same improvement in our formal proof too.  Here's how
    it looks: *)

Theorem optimize_0plus_sound'': forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e. 
  induction e; 
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when e = APlus e1 e2. *)
  Case "APlus". 
    destruct e1; try (simpl; simpl in IHe1; rewrite IHe1; 
                      rewrite IHe2; reflexivity).
    SCase "e1 = ANum n". destruct n;
      simpl; rewrite IHe2; reflexivity. Qed.

(* ####################################################### *)
(** *** The [;] Tactical (General Form) *)

(** The [;] tactical has a more general than the simple [T;T'] we've
    seen above, and which is sometimes also useful.
    If [T], [T1], ..., [Tn] are tactics, then
      T; [T1 | T2 | ... | Tn] 
   is a tactic that first performs [T] and then performs [T1] on the
   first subgoal generated by [T], performs [T2] on the second
   subgoal, etc.

   So [T;T'] is just special notation for the case when all of the
   [Ti]'s are the same tactic; i.e. [T;T'] is just a shorthand for:
      T; [T' | T' | ... | T'] 
  The form [T;T'] is used most often in practice. *)

(* ####################################################### *)
(** ** Defining New Tactic Notations *)

(** Coq also provides several ways of "programming" tactic scripts. 

      - The [Tactic Notation] idiom illustrated below gives a handy
        way to define "shorthand tactics" that bundle several tactics
        into a single command.

      - For more sophisticated programming, Coq offers a small
        built-in programming language called [Ltac] with primitives
        that can examine and modify the proof state.  The details are
        a bit too complicated to get into here (and it is generally
        agreed that [Ltac] is not the most beautiful part of Coq's
        design!), but they can be found in the reference manual, and
        there are many examples of [Ltac] definitions in the Coq
        standard library that you can use as examples.

      - There is also an OCaml API, which can be used to build tactics
        that access Coq's internal structures at a lower level, but
        this is seldom worth the trouble for ordinary Coq users.

The [Tactic Notation] mechanism is the easiest to come to grips with,
and it offers plenty of power for many purposes.  Here's an example. 
*)

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

(** This defines a new tactical called [simpl_and_try] which
    takes one tactic [c] as an argument, and is defined to be
    equivalent to the tactic [simpl; try c].  For example, writing
    "[simpl_and_try reflexivity.]" in a proof would be the same as
    writing "[simpl; try reflexivity.]" *)

(** The next subsection gives a more sophisticated use of this
    feature... *)

(* ####################################################### *)
(** *** Bulletproofing Case Analyses *)

(** Being able to deal with most of the cases of an [induction]
    or [destruct] all at the same time is very convenient, but it can
    also be a little confusing.  One problem that often comes up is
    that _maintaining_ proofs written in this style can be difficult.
    For example, suppose that, later, we extended the definition of
    [aexp] with another constructor that also required a special
    argument.  The above proof might break because Coq generated the
    subgoals for this constructor before the one for [APlus], so that,
    at the point when we start working on the [APlus] case, Coq is
    actually expecting the argument for a completely different
    constructor.  What we'd like is to get a sensible error message
    saying "I was expecting the [AFoo] case at this point, but the
    proof script is talking about [APlus]."  Here's a nice trick (due
    to Aaron Bohannon) that smoothly achieves this. *)

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

(** ([Case_aux] implements the common functionality of [Case],
    [SCase], [SSCase], etc.  For example, [Case "foo"] is defined as
    [Case_aux Case "foo".) *)

(** For example, if [e] is a variable of type [aexp], then doing
      aexp_cases (induction e) Case
    will perform an induction on [e] (the same as if we had just typed
    [induction e]) and _also_ add a [Case] tag to each subgoal
    generated by the [induction], labeling which constructor it comes
    from.  For example, here is yet another proof of
    [optimize_0plus_sound], using [aexp_cases]: *)

Theorem optimize_0plus_sound''': forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  aexp_cases (induction e) Case;
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
    try reflexivity.
  (* At this point, there is already an ["APlus"] case name
     in the context.  The [Case "APlus"] here in the proof 
     text has the effect of a sanity check: if the "Case" 
     string in the context is anything _other_ than ["APlus"]
     (for example, because we added a clause to the definition
     of [aexp] and forgot to change the proof) we'll get a 
     helpful error at this point telling us that this is now
     the wrong case. *)
  Case "APlus". 
    aexp_cases (destruct e1) SCase; 
      try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
    SCase "ANum". destruct n;
      simpl; rewrite IHe2; reflexivity.  Qed.


(** **** Exercise: 3 stars (optimize_0plus_b) *)
(* EXPECTED *)
(** Since the [optimize_0plus] tranformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)
(* FILL IN HERE *)
(**
Note that since I have two definitions, [optimize_0plus] and [my_optimize_0plus],
two cases are analysed as follows,
*)
(*Case one-[my_optimize_0plus]*)

Fixpoint my_optimize_0plus_b (e:bexp) : bexp :=
         match e with
         | BTrue => BTrue
         | BFalse => BFalse
         | BEq a1 a2 => BEq (my_optimize_0plus a1)(my_optimize_0plus a2)
         | BLe a1 a2 => BLe (my_optimize_0plus a1)(my_optimize_0plus a2)
         | BNot a => BNot (my_optimize_0plus_b a)
         | BAnd a1 a2 => BAnd (my_optimize_0plus_b a1)(my_optimize_0plus_b a2)
         end.

Example test_my_optimize_0plus_b1:
        my_optimize_0plus_b (BEq (APlus (ANum 0)(ANum 2)) (ANum 2))=BEq (ANum 2)(ANum 2).
Proof. simpl. reflexivity. Qed.

Example test_my_optimize_0plus_b2:
        my_optimize_0plus_b (BLe (APlus (ANum 0)(ANum 3))(APlus (ANum 0)(ANum 4)))=BLe (ANum 3)(ANum 4).
Proof. simpl. reflexivity. Qed.

Example test_my_optimize_0plus_b3:
        my_optimize_0plus_b (BEq (APlus (AMult (ANum 0)(ANum 8))(ANum 3))(ANum 3)) = BEq (ANum 3)(ANum 3).
Proof. simpl. reflexivity. Qed.

(*soundness proof*)
Theorem my_optimize_0plus_b_sound: forall e:bexp,
beval (my_optimize_0plus_b e) = beval e.
Proof.
intros e. induction e.
Case ("BTrue"). reflexivity.
Case ("BTrue"). reflexivity.
Case ("BEq"). simpl. rewrite my_optimize_0plus_sound1. rewrite my_optimize_0plus_sound1.
              reflexivity.
Case ("BLe"). simpl.  rewrite my_optimize_0plus_sound1. rewrite my_optimize_0plus_sound1.
              reflexivity.
Case ("BNot"). simpl. rewrite IHe. reflexivity.
Case ("BAnd"). simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Theorem my_optimize_0plus_b_sound': forall e:bexp,
beval (my_optimize_0plus_b e) = beval e.
Proof.
intros. induction e; try (reflexivity);try (simpl;repeat rewrite my_optimize_0plus_sound1;reflexivity);
        try(simpl;rewrite IHe;reflexivity);try(simpl;rewrite IHe1;rewrite IHe2;reflexivity).
Qed.
(*Case two-[optimize_0plus]*)

Fixpoint optimize_0plus_b (e:bexp) : bexp :=
         match e with
         | BTrue => BTrue
         | BFalse => BFalse
         | BEq a1 a2 => BEq (optimize_0plus a1)(optimize_0plus a2)
         | BLe a1 a2 => BLe (optimize_0plus a1)(optimize_0plus a2)
         | BNot a => BNot (optimize_0plus_b a)
         | BAnd a1 a2 => BAnd (optimize_0plus_b a1)(optimize_0plus_b a2)
         end.

Example test_optimize_0plus_b1:
        optimize_0plus_b (BEq (APlus (ANum 0)(ANum 2)) (ANum 2))=BEq (ANum 2)(ANum 2).
Proof. simpl. reflexivity. Qed.

Example test_optimize_0plus_b2:
        optimize_0plus_b (BLe (APlus (ANum 0)(ANum 3))(APlus (ANum 0)(ANum 4)))=BLe (ANum 3)(ANum 4).
Proof. simpl. reflexivity. Qed.

Example test_optimize_0plus_b3:
        optimize_0plus_b (BEq (APlus (AMult (ANum 0)(ANum 8))(ANum 3))(ANum 3)) = BEq (APlus (AMult (ANum 0)(ANum 8))(ANum 3))(ANum 3).
Proof. simpl. reflexivity. Qed.

(*soundness proof*)
Theorem optimize_0plus_b_sound: forall e:bexp,
beval (optimize_0plus_b e) = beval e.
Proof.
intros e. induction e.
Case ("BTrue"). reflexivity.
Case ("BTrue"). reflexivity.
Case ("BEq"). simpl. repeat rewrite optimize_0plus_sound. reflexivity.
Case ("BLe"). simpl. repeat rewrite optimize_0plus_sound. reflexivity.
Case ("BNot"). simpl. rewrite IHe. reflexivity.
Case ("BAnd"). simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Theorem optimize_0plus_b_sound': forall e:bexp,
beval (optimize_0plus_b e) = beval e.
Proof.
intros. induction e; try (reflexivity);try (simpl;repeat rewrite optimize_0plus_sound;reflexivity);
        try(simpl;rewrite IHe;reflexivity);try(simpl;rewrite IHe1;rewrite IHe2;reflexivity).
Qed.
(** [] *)

(** **** Exercise: 4 stars, optional (optimizer) *)
(* NO SOLUTION *)
(** _Design exercise_: The optimization implemented by our
    [optimize_0plus] function is only one of many imaginable
    optimizations on arithmetic and boolean expressions.  Write a more
    sophisticated optimizer and prove it correct.

*)
(**
Arithmetic optimizer,
    [AMult (ANum a)(APlus (ANum b)(ANum c))] = 
    [APlus (AMult (ANum a)(ANum b))(AMult (ANum a)(ANum c))]
*)
Fixpoint my_optimize_mult_d (e:aexp) : aexp :=
         match e with
         | ANum a => ANum a
         | APlus a1 a2 => APlus (my_optimize_mult_d a1)(my_optimize_mult_d a2)
         | AMinus a1 a2 =>AMinus(my_optimize_mult_d a1)(my_optimize_mult_d a2)
         | AMult a1 (APlus a2 a3) => APlus (AMult (my_optimize_mult_d a1) (my_optimize_mult_d a2))(AMult (my_optimize_mult_d a1) (my_optimize_mult_d a3))
         | AMult a1 a2 =>AMult (my_optimize_mult_d a1) (my_optimize_mult_d a2)
         end.
Example test_my_optimize_mult_d1:
        my_optimize_mult_d (AMult (ANum 2)(APlus (ANum 1)(ANum 3))) = APlus (AMult (ANum 2)(ANum 1))(AMult (ANum 2)(ANum 3)).
Proof. simpl. reflexivity. Qed.
Example test_my_optimize_mult_d2:
        my_optimize_mult_d (APlus (AMult (ANum 2)(APlus (ANum 1)(ANum 3)))(ANum 4))=
        APlus (APlus (AMult (ANum 2)(ANum 1))(AMult (ANum 2)(ANum 3)))(ANum 4).
Proof. simpl. reflexivity. Qed.
Example test_my_optimize_mult_d3:
        my_optimize_mult_d (AMult (ANum 0)(AMult (ANum 2)(APlus (ANum 1)(ANum 3))))=
        AMult (ANum 0)(APlus (AMult (ANum 2)(ANum 1))(AMult (ANum 2)(ANum 3))).
Proof. simpl. reflexivity. Qed.
(*proof of soundness*)
Theorem my_optimize_mult_d_soundness: forall e:aexp,
       aeval (my_optimize_mult_d e) = aeval e.
Proof.
intros e. induction e.
Case ("ANum"). reflexivity.
Case ("APlus"). simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Case ("AMinus"). simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Case ("AMult"). simpl. destruct e2.
     SCase ("ANum"). simpl. rewrite IHe1. reflexivity.
     SCase ("APlus"). simpl. simpl in IHe2. rewrite IHe1. 
                     rewrite<-mult_plus_distr_l. rewrite IHe2.
                    reflexivity.
     SCase ("AMinus"). simpl. simpl in IHe2. rewrite IHe1. 
                      rewrite IHe2. reflexivity.
     SCase ("AMult"). simpl. simpl in IHe2. rewrite IHe1.
                      rewrite IHe2. reflexivity.
Qed.

Theorem my_optimize_mult_d_soundness': forall e:aexp,
        aeval (my_optimize_mult_d e) = aeval e.
Proof.
intros e. induction e; try (reflexivity);try(simpl;rewrite IHe1;rewrite IHe2;reflexivity);
 try(simpl;destruct e2;try(simpl;rewrite IHe1;reflexivity);try(simpl;simpl in IHe2;rewrite IHe1;rewrite IHe2;reflexivity)).
Case ("AMult"). SCase ("AMult"). simpl. simpl in IHe2. rewrite IHe1.
 rewrite<-mult_plus_distr_l. rewrite IHe2. reflexivity.
Qed.
(** [] *)

(* ####################################################### *)
(** ** The [omega] Tactic *)

(** The [omega] tactic implements a decision procedure for a subset of
    first-order logic called _Presburger arithmetic_.  It is based on
    the Omega algorithm invented in 1992 by William Pugh.

    If the goal is a universally quantified formula made out of

      - numeric constants, addition ([+] and [S]), subtraction ([-]
        and [pred]), and multiplication by constants (this is what
        makes it Presburger arithmetic), 

      - equality ([=] and [<>]) and inequality ([<=]), and

      - the logical connectives [/\], [\/], [~], and [->],

    then invoking [omega] will either solve the goal or tell you that
    it is actually false. *)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega. 
Qed.

(** Andrew Appel calls this the "Santa Claus tactic."  We'll see
    examples of its use below. *)

(* ####################################################### *)
(** ** A Few More Handy Tactics *)

(** Finally, here are some miscellaneous tactics that you may find
    convenient.

     - [clear H]: Delete hypothesis [H] from the context.

     - [subst x]: Find an assumption [x = e] or [e = x] in the
       context, replace [x] with [e] throughout the context and
       current goal, and clear the assumption.

     - [subst]: Substitute away _all_ assumptions of the form [x = e]
       or [e = x].

     - [rename... into...]: Change the name of a hypothesis in the
       proof context.  For example, if the context includes a variable
       named [x], then [rename x into y] will change all occurrences
       of [x] to [y].

     - [assumption]: Try to find a hypothesis [H] in the context that
       exactly matches the goal; if one is found, behave just like
       [apply H].

     - [contradiction]: Try to find a hypothesis [H] in the current
       context that is logically equivalent to [False].  If one is
       found, solve the goal.

     - [constructor]: Try to find a constructor [c] (from some
       [Inductive] definition in the current environment) that can be
       applied to solve the current goal.  If one is found, behave
       like [apply c].

    We'll see many examples of these in the proofs below. *)

(* ####################################################### *)
(** * Evaluation as a Relation *)

(** We have presented [aeval] and [beval] as functions defined by
    [Fixpoints].  Another way to think about evaluation, one that we
    will see is often more flexible, is as a _relation_ between
    expressions and their values.  This leads naturally to [Inductive]
    definitions like the following one for arithmetic
    expressions... *)
Inductive my_aeval: aexp -> nat -> Prop:=
| anum: forall n:nat, my_aeval (ANum n) n 
| aplus: forall (a1 a2:aexp)(e:nat),e=(aeval a1)+(aeval a2) -> my_aeval (APlus a1 a2) e
| aminus:forall (a1 a2:aexp)(e:nat),e=(aeval a1)-(aeval a2) -> my_aeval (AMinus a1 a2) e
| amult:forall (a1 a2:aexp)(e:nat), e=(aeval a1)*(aeval a2) -> my_aeval (AMult a1 a2) e
.

Example test_my_aeval1:
    my_aeval (APlus (ANum 2) (ANum 3)) 5.
Proof. apply aplus. simpl. reflexivity. Qed.
Example test_my_aeval2:
    my_aeval (ANum 3) 3.
Proof. apply anum. Qed.
Example test_my_aeval3:
    my_aeval (AMinus (APlus (ANum 2)(ANum 1))(ANum 1)) 2.
Proof. apply aminus. simpl. reflexivity. Qed.

Inductive my_beval: bexp -> bool -> Prop:=
|btrue: my_beval BTrue true
|bfalse: my_beval BFalse false
|beq: forall (a1 a2:aexp)(e:bool), e= beq_nat (aeval a1)(aeval a2) -> my_beval (BEq a1 a2) e
|ble: forall (a1 a2:aexp)(e:bool), e= ble_nat (aeval a1)(aeval a2) -> my_beval (BLe a1 a2) e
|bnot: forall (a:bexp)(e:bool), e=negb (beval a) -> my_beval (BNot a) e
|band:forall (a1 a2:bexp)(e:bool), e= andb (beval a1)(beval a2) -> my_beval (BAnd a1 a2) e
.

Example test_my_beval1:
     my_beval BTrue true.
Proof. apply btrue. Qed.
Example test_my_beval2:
     my_beval (BEq (ANum 2)(ANum 2)) true.
Proof. apply beq. simpl. reflexivity. Qed.
Example test_my_beval3:
     my_beval (BAnd BTrue BFalse) false.
Proof. apply band. simpl. reflexivity. Qed.
Example test_my_beval4:
     my_beval (BNot BTrue) false.
Proof. apply bnot. simpl. reflexivity. Qed.
Example test_my_beval5:
     my_beval (BLe (ANum 3)(ANum 2)) false.
Proof. apply ble. simpl. reflexivity. Qed.


Module aevalR_first_try. 

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum  : forall (n: nat), 
      aevalR (ANum n) n
  | E_APlus : forall (e1 e2: aexp) (n1 n2: nat), 
      aevalR e1 n1 -> 
      aevalR e2 n2 -> 
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat), 
      aevalR e1 n1 -> 
      aevalR e2 n2 -> 
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2: nat), 
      aevalR e1 n1 -> 
      aevalR e2 n2 -> 
      aevalR (AMult e1 e2) (n1 * n2).
Example test_aevalR1:
    aevalR (APlus (ANum 2) (ANum 3)) 5.
Proof. assert (A:5=2+3). reflexivity. rewrite A. apply E_APlus; 
       apply E_ANum.  Qed.
Example test_aevalR2:
    aevalR (ANum 3) 3.
Proof. apply E_ANum. Qed.
Example test_aevalR3:
    aevalR (AMinus (APlus (ANum 2)(ANum 1))(ANum 1)) 2.
Proof. assert (A:2=3-1). reflexivity. rewrite A. 
apply E_AMinus. assert (B:3=2+1). reflexivity. rewrite B.
apply E_APlus; try (simpl;apply E_ANum);try(apply E_ANum).
apply E_ANum. Qed.
(**
Note that as compared with [my_aeval] defined above, [aevalR] is
harder to work with, involving too many tedious steps.
*)
(** As is often the case with relations, we'll find it
    convenient to define infix notation for [aevalR].  We'll write [e
    || n] to mean that arithmetic expression [e] evaluates to value
    [n].  (This notation is one place where the limitation to ASCII
    symbols becomes a little bothersome.  The standard notation for
    the evaluation relation is a double down-arrow.  We'll typeset it
    like this in the HTML version of the notes and use a double
    vertical bar as the closest approximation in [.v] files.)  *)

Notation "e '||' n" := (aevalR e n) : type_scope.

End aevalR_first_try. 

(** In fact, Coq provides a way to use this notation in the definition
    of [aevalR] itself.  This avoids situations where we're working on
    a proof involving statements in the form [e || n] but we have to
    refer back to a definition written using the form [aevalR e n].

    We do this by first "reserving" the notation, then giving the
    definition together with a declaration of what the notation
    means. *)

Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat), 
      (ANum n) || n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat), 
      (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2) 
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat), 
      (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2) 
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat), 
      (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)

  where "e '||' n" := (aevalR e n) : type_scope. 

Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_ANum" | Case_aux c "E_APlus"
  | Case_aux c "E_AMinus" | Case_aux c "E_AMult" ].

(** It is straightforward to prove that the relational and functional
    definitions of evaluation agree on all possible arithmetic
    expressions... *)
Theorem my_aeval_iff_aevalR: forall a n,
(a || n) <-> aeval a = n.
Proof.
intros a. induction a.
Case ("ANum"). intros. split. 
     SCase ("->"). intros. inversion H. reflexivity.
     SCase ("<-"). intros. simpl in H. rewrite H. apply E_ANum.
Case ("APlus"). intros. split.
     SCase ("->"). intros. simpl. inversion H. apply IHa1 in H2.
                   apply IHa2 in H4. rewrite H2. rewrite H4.
                   reflexivity.
     SCase ("<-"). intros. simpl in H. rewrite <-H. apply E_APlus.
                   apply IHa1. reflexivity. apply IHa2. reflexivity.
Case ("AMinus"). intros. split.
     SCase ("->"). intros. simpl. inversion H. apply IHa1 in H2. apply IHa2 in H4.
                  rewrite H2. rewrite H4. reflexivity.
     SCase ("<-"). intros. simpl in H. rewrite<-H. apply E_AMinus. apply IHa1.
                  reflexivity. apply IHa2. reflexivity.
Case ("AMult"). intros. split.
     SCase ("->"). intros. simpl. inversion H. apply IHa1 in H2. apply IHa2 in H4.
                  rewrite H2. rewrite H4. reflexivity.
     SCase ("<-"). intros. simpl in H. rewrite<-H. apply E_AMult.
                   apply IHa1. reflexivity. apply IHa2. reflexivity.
Qed.

Theorem my_aeval_iff_aevalR': forall a n,
(a || n) <-> aeval a = n.
Proof.
intros a. induction a; 
intros;split;
try (intros;simpl;inversion H;apply IHa1 in H2;apply IHa2 in H4;
                  rewrite H2;rewrite H4;reflexivity);
try (intros;simpl in H; rewrite<-H).
Case ("ANum"). SCase ("->"). intros. inversion H. reflexivity.
Case ("ANum"). SCase ("<-"). apply E_ANum.
Case ("APlus"). SCase ("<-"). apply E_APlus. apply IHa1. reflexivity. apply IHa2.
reflexivity.
Case ("AMinus"). SCase ("<-"). apply E_AMinus. apply IHa1. reflexivity.
 apply IHa2. reflexivity.
Case ("AMult"). SCase ("<-"). apply E_AMult. apply IHa1. reflexivity.
apply IHa2. reflexivity.
Qed.

Theorem aeval_iff_aevalR : forall a n,
  (a || n) <-> aeval a = n.
Proof.
 split.
 Case "->". 
   intros H. 
   aevalR_cases (induction H) SCase; simpl. 
   SCase "E_ANum". 
     reflexivity. 
   SCase "E_APlus".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   SCase "E_AMinus".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   SCase "E_AMult".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 Case "<-".
   generalize dependent n.
   aexp_cases (induction a) SCase; 
      simpl; intros; subst. 
   SCase "ANum".
     apply E_ANum. 
   SCase "APlus".
     apply E_APlus. 
      apply IHa1. reflexivity.
      apply IHa2. reflexivity. 
   SCase "AMinus". 
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity. 
   SCase "AMult".
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity. 
Qed.

(** We can make the proof quite a bit shorter by making more
    aggressive use of tacticals... *)

Theorem aeval_iff_aevalR' : forall a n,
  (a || n) <-> aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  Case "->". 
    intros H; induction H; subst; reflexivity. 
  Case "<-".
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity. 
Qed.
(**
Now it is time for us to prove that [my_aeval] is equivalent to
[aeval],
*)
Theorem aeval_iff_my_aeval: forall a n,
my_aeval a n <-> aeval a = n.
Proof.
split.
Case ("->"). intros. induction H.
     SCase ("ANum"). reflexivity.
     SCase ("APlus"). simpl. subst. reflexivity.
     SCase ("AMinus"). simpl. subst. reflexivity.
     SCase ("AMult"). simpl. subst. reflexivity.
Case ("<-"). generalize dependent n. induction a.
     SCase ("ANum"). intros. simpl in H. subst. constructor.
     SCase ("APlus"). intros. simpl in H. subst. constructor.
                     reflexivity.
     SCase ("AMinus"). intros. simpl in H. subst. constructor.
                      reflexivity.
     SCase ("AMult"). intros. simpl in H. subst. constructor.
                      reflexivity.
Qed.

Theorem aeval_iff_my_aeval':forall a n,
my_aeval a n <-> aeval a = n.
Proof.
split.
Case ("->"). intros. induction H;try reflexivity;try(simpl;subst;reflexivity).
Case ("<-"). generalize dependent n. induction a;intros;simpl in H;subst;
             constructor; try reflexivity.
Qed.


(** **** Exercise: 3 stars  (bevalR) *)
(* EXPECTED *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)
(**
It's been defined above as,
Inductive my_beval: bexp -> bool -> Prop:=
|btrue: my_beval BTrue true
|bfalse: my_beval BFalse false
|beq: forall (a1 a2:aexp)(e:bool), e= beq_nat (aeval a1)(aeval a2) -> my_beval (BEq a1 a2) e
|ble: forall (a1 a2:aexp)(e:bool), e= ble_nat (aeval a1)(aeval a2) -> my_beval (BLe a1 a2) e
|bnot: forall (a:bexp)(e:bool), e=negb (beval a) -> my_beval (BNot a) e
|band:forall (a1 a2:bexp)(e:bool), e= andb (beval a1)(beval a2) -> my_beval (BAnd a1 a2) e
.
*)
(* 
Inductive bevalR:
*)
(* FILL IN HERE *)
Theorem beval_iff_my_beval:forall a n,
my_beval a n <-> beval a = n.
Proof.
split.
Case ("->"). intros. induction H.
     SCase ("BTrue"). reflexivity.
     SCase ("BTrue"). reflexivity.
     SCase ("BEq"). simpl. subst. reflexivity.
     SCase ("BLe"). simpl. subst. reflexivity.
     SCase ("BNot"). simpl. subst. reflexivity.
     SCase ("BAnd"). simpl. subst. reflexivity.
Case ("<-"). generalize dependent n. induction a.
     SCase ("BTrue"). intros. simpl in H. subst. constructor.
     SCase ("BFalse"). intros. simpl in H. subst. constructor.
     SCase ("BEq"). intros. simpl in H. subst. constructor. reflexivity.
     SCase ("BLe"). intros. simpl in H. subst. constructor. reflexivity.
     SCase ("BNot"). intros. simpl in H. subst. constructor. reflexivity.
     SCase ("BAnd"). intros. simpl in H. subst. constructor. reflexivity.
Qed.

Theorem beval_iff_my_beval':forall a n,
my_beval a n <-> beval a = n.
Proof.
split.
Case ("->"). intros. induction H; try simpl;try subst;reflexivity.
Case ("<-"). generalize dependent n. induction a; intros;simpl in H;subst;
constructor;try reflexivity.
Qed.





(** [] *)

(** For the definitions of evaluation for arithmetic and boolean
    expressions, the choice of whether to use functional or relational
    definitions is mainly a matter of taste.  In general, Coq has
    somewhat better support for working with relations.  On the other
    hand, in some sense function definitions carry more information,
    because functions are necessarily deterministic and defined on all
    arguments; for a relation we have to show these properties
    explicitly if we need them. Functions also take advantage of Coq's
    computational mechanism.

    However, there are circumstances where relational definitions of
    evaluation are greatly preferable to functional ones, as we'll see
    shortly. *)

(* ####################################################### *)
(** ** Inference Rule Notation *)

(** In informal discussions, it is convenient write the rules for
    [aevalR] and similar relations in the more readable "graphical"
    form of _inference rules_, where the premises above the line
    justify the conclusion below the line.  For example, the
    constructor [E_APlus]...
      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat), 
          aevalR e1 n1 -> 
          aevalR e2 n2 -> 
          aevalR (APlus e1 e2) (n1 + n2)
    ...would be written like this as an inference rule:
                               e1 || n1
                               e2 || n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 || n1+n2
    Formally, there is nothing very deep about inference rules: they
    are just implications.  You can read the rule name on the right as
    the name of the constructor and read each of the linebreaks
    between the premises above the line and the line itself as [->].
    All the variables mentioned in the rule ([e1], [n1], etc.) are
    implicitly bound by universal quantifiers at the beginning.  The
    whole collection of rules is understood as being wrapped in an
    [Inductive] declaration (informally, this is either elided or else
    indicated by saying something like "Let [aevalR] be the smallest
    relation closed under the following rules...").

    For example, [||] is the smallest relation closed under these
    rules:
                             -----------                               (E_ANum)
                             ANum n || n

                               e1 || n1
                               e2 || n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 || n1+n2

                               e1 || n1
                               e2 || n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 || n1-n2

                               e1 || n1
                               e2 || n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 || n1*n2
*)

End AExp.

(* ####################################################### *)
(** * Expressions With Variables *)

(** Let's turn our attention back to defining Imp.  The next thing we
    need to do is to enrich our arithmetic and boolean expressions
    with variables.  To keep things simple, we'll assume that all
    variables are global and that they only hold numbers. *)

(* ##################################################### *)
(** ** Identifiers *)

(** To begin, we'll need to formalize _identifiers_ such as program
    variables.  We could use strings for this -- or, in a real
    compiler, fancier structures like pointers into a symbol table.
    But for simplicity let's just use natural numbers as identifiers.

    (We hide this section in a module because these definitions are
    actually in [SfLib], but we want to repeat them here so that we
    can explain them.) *)

Module Id.

(** We define a new inductive datatype [Id] so that we won't confuse
    identifiers and numbers. *)

Inductive id : Type := 
  Id : nat -> id.

Definition beq_id X1 X2 :=
  match (X1, X2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.
Example test_beq_id1:
      beq_id (Id 1) (Id 2) = false.
Proof. reflexivity. Qed.
Example test_beq_id2:
      beq_id (Id 2)(Id 2) = true.
Proof. reflexivity. Qed.
Definition my_beq_id (X1 X2: id): bool :=
    match (X1 , X2) with
    (Id n1, Id n2) => beq_nat n1 n2
    end.
Example test_my_beq_id1:
    beq_id (Id 1)(Id 2) = false.
Proof. reflexivity. Qed.
Example test_my_beq_id2:
    beq_id (Id 1)(Id 1) = true.
Proof. reflexivity. Qed.
(** After we "wrap" numbers as identifiers in this way, it is
    convenient to recapitulate a few properties of numbers as
    analogous properties of identifiers, so that we can work with
    identifiers in definitions and proofs abstractly, without
    unwrapping them to expose the underlying numbers.  Since all we
    need to know about identifiers is whether they are the same or
    different, just a few basic facts are all we need. *)

Theorem my_beq_id_refl: forall X,
  true = beq_id X X.
Proof.
intros X. destruct X.  unfold beq_id. 
 apply beq_nat_refl. Qed.

Theorem beq_id_refl : forall X,
  true = beq_id X X.
Proof.
  intros. destruct X.
  apply beq_nat_refl.  Qed.

(** **** Exercise: 1 star, optional (beq_id_eq) *)
(* EXPECTED *)
(** For this and the following exercises, do not use induction, but
    rather apply similar results already proved for natural numbers.
    Some of the tactics mentioned above may prove useful. *)
Theorem beq_id_eq : forall i1 i2,
  true = beq_id i1 i2 -> i1 = i2.
Proof.
(* FILL IN HERE *) 
intros. unfold beq_id in H. destruct i1. destruct i2. symmetry in H.
apply beq_nat_true in H. subst. reflexivity.
Qed.  
(** [] *)

(** **** Exercise: 1 star, optional (beq_id_false_not_eq) *)
(* EXPECTED *)
Theorem beq_id_false_not_eq : forall i1 i2,
  beq_id i1 i2 = false -> i1 <> i2.
Proof.
(* FILL IN HERE *)
intros. unfold beq_id in H. destruct i1. destruct i2.
apply beq_nat_false in H. intros contra. inversion contra.
apply H. apply H1.
Qed.
(** [] *)

(** **** Exercise: 1 star, optional (not_eq_beq_id_false) *)
Theorem not_eq_beq_id_false : forall i1 i2,
  i1 <> i2 -> beq_id i1 i2 = false.
Proof.
(* FILL IN HERE *) 
intros. unfold beq_id. destruct i1. destruct i2.  apply beq_nat_false_iff.
intros C. apply H. subst. reflexivity.
Qed.

Theorem beq_id_false_not_eq_iff : forall i1 i2,
  i1 <> i2 <-> beq_id i1 i2 = false.
Proof.
split.
Case ("->"). apply not_eq_beq_id_false. 
Case ("<-"). apply beq_id_false_not_eq.
Qed.

(** [] *)

(** **** Exercise: 1 star, optional (beq_id_sym) *)
Theorem beq_id_sym: forall i1 i2,
  beq_id i1 i2 = beq_id i2 i1.
Proof.
(* FILL IN HERE *) 
intros. destruct i1. destruct i2. unfold beq_id.
apply beq_nat_sym.
Qed.
(** [] *)

End Id.

(* ####################################################### *) 
(** ** States *)

(** A _state_ represents the current values of all the variables at
    some point in the execution of a program. *)
(** For simplicity (to avoid dealing with partial functions), we
    let the state be defined for _all_ variables, even though any
    given program is only going to mention a finite number of them. *)

Definition state := id -> nat.

Definition empty_state : state := 
  fun _ => 0.
 
Definition update (st : state) (X:id) (n : nat) : state :=
  fun X' => if beq_id X X' then n else st X'.

(** For proofs involving states, we'll need several simple properties
    of [update]. *)

(** **** Exercise: 1 star (update_eq) *)
Theorem update_eq : forall n X st,
  (update st X n) X = n.
Proof.
(* FILL IN HERE *)
intros. unfold update. rewrite<-beq_id_refl. reflexivity. 
Qed.
(** [] *)

(** **** Exercise: 1 star (update_neq) *)
Theorem update_neq : forall V2 V1 n st,
  beq_id V2 V1 = false ->
  (update st V2 n) V1 = (st V1).
Proof.
(* FILL IN HERE *) 
intros. unfold update. rewrite H. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, recommended (update_shadow) *)
Theorem update_shadow : forall x1 x2 k1 k2 (f : state),
   (update  (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
Proof.
(* FILL IN HERE *) 
intros. unfold update. destruct (beq_id k2 k1). reflexivity.
reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars (update_same) *)
Theorem update_same : forall x1 k1 k2 (f : state),
  f k1 = x1 ->
  (update f k1 x1) k2 = f k2.
Proof.
(* FILL IN HERE *) 
intros. unfold update. remember (beq_id k1 k2) as D. destruct D.
Case ("true"). apply beq_id_eq in HeqD. subst. reflexivity.
reflexivity.
Qed. 

(** [] *)

(** **** Exercise: 3 stars (update_permute) *)
Theorem update_permute : forall x1 x2 k1 k2 k3 f,
  beq_id k2 k1 = false -> 
  (update (update f k2 x1) k1 x2) k3 = (update (update f k1 x2) k2 x1) k3.
Proof.
(* FILL IN HERE *) 
intros. unfold update. remember (beq_id k1 k3) as D1. remember (beq_id k2 k3) as D2.
destruct D1.
Case ("D1=true"). destruct D2.
      SCase ("D2=true"). apply beq_id_false_not_eq in H.  apply beq_id_eq in HeqD1.
                         apply beq_id_eq in HeqD2. rewrite<-HeqD2 in HeqD1.
                         unfold not in H. symmetry in HeqD1. apply H in HeqD1.
                         inversion HeqD1.
      SCase ("D2=false"). reflexivity.
Case ("D1=false"). destruct D2.
      SCase ("D2=true"). reflexivity.
      SCase ("D2=false"). reflexivity.
Qed. 
(** [] *)

(* ################################################### *)
(** ** Syntax  *)

(** We can add variables to the arithmetic expressions we had before by
    simply adding one more constructor: *)

Inductive aexp : Type := 
  | ANum : nat -> aexp
  | AId : id -> aexp                (* <----- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

(** (This convention for naming program variables ([X], [Y],
    [Z]) clashes a bit with our earlier use of uppercase letters for
    types.  Since we're not using polymorphism heavily in this part of
    the course, this overloading should not cause confusion.) *)

(** The definition of [bexp]s is the same as before (using the new
    [aexp]s): *)

Inductive bexp : Type := 
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].

(* ################################################### *)
(** ** Evaluation  *)

(** The arith and boolean evaluators can be extended to handle
    variables in the obvious way: *)

Fixpoint aeval (st : state) (e : aexp) : nat :=
  match e with
  | ANum n => n
  | AId X => st X                                        (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (e : bexp) : bool :=
  match e with 
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Example aexp1 : 
  aeval (update empty_state X 5) 
        (APlus (ANum 3) (AMult (AId X) (ANum 2))) 
  = 13.
Proof. reflexivity. Qed.

Example aexp2 :
  aeval (update empty_state X 5)
        (APlus (ANum 3)(AMult (AId Y)(ANum 10)))
  = 3.
Proof. reflexivity. Qed.
Example bexp1 :
  beval (update empty_state X 5) 
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity. Qed.

Example bexp2 :
  beval (update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId Y)(ANum 4))))
  =false.
Proof. reflexivity. Qed.
(**
Note that, as before some [optimizer]s canbe defined and 
then proved to be sound.
*)

(* ####################################################### *)
(** * Commands *)

(** Now we are ready define the syntax and behavior of Imp
    _commands_ (or _statements_). *)

(* ################################################### *)
(** ** Syntax *)

(** Informally, commands are described by the following BNF
    grammar: 
     com ::= 'SKIP'
           | X '::=' aexp
           | com ';' com
           | 'WHILE' bexp 'DO' com 'END'
           | 'IFB' bexp 'THEN' com 'ELSE' com 'FI'
    For example, here's the factorial function in Imp. 
     Z ::= X;
     Y ::= 1;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;
       Z ::= Z - 1
     END
   When this command terminates, the variable [Y] will contain the
   factorial of the initial value of [X].
*)

(** Here is the formal definition of the syntax of commands: *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

(** As usual, we can use a few [Notation] declarations to make things
    more readable.  We need to be a bit careful to avoid conflicts
    with Coq's built-in notations, so we'll keep this light -- in
    particular, we won't introduce any notations for [aexps] and
    [bexps] to avoid confusion with the numerical and boolean
    operators we've already defined.  We use the keyword [IFB] for
    conditionals instead of [IF], for similar reasons. *)

Notation "'SKIP'" := 
  CSkip.
Notation "X '::=' a" := 
  (CAss X a) (at level 60).
Notation "c1 ; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).

(** For example, here is the factorial function again, written as a
    formal definition to Coq: *)

Definition fact_in_coq : com :=
  Z ::= AId X;
  Y ::= ANum 1;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);
    Z ::= AMinus (AId Z) (ANum 1)
  END.

(* ####################################################### *)
(** ** Examples *)

(** Assignment: *)

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;
  X ::= AMinus (AId X) (ANum 1).

(** Loops: *)

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;
  Z ::= ANum 5 ;
  subtract_slowly.

(** An infinite loop: *)

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

(** Factorial again (broken up into smaller pieces this time, for
    convenience when we come back to proving things about it
    later).  *)

Definition fact_body : com :=
  Y ::= AMult (AId Y) (AId Z) ;
  Z ::= AMinus (AId Z) (ANum 1).

Definition fact_loop : com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    fact_body
  END.

Definition fact_com : com :=
  Z ::= AId X ;
  Y ::= ANum 1 ;
  fact_loop.

(* ################################################################ *)
(** * Evaluation *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [WHILE] loops don't necessarily terminate makes defining
    an evaluation function tricky ... *)

(* #################################### *)
(** ** Evaluation Function (Failed Attempt) *)

(** Here's an attempt at defining an evaluation function for commands,
    omitting the [WHILE] case. *)

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with 
    | SKIP => 
        st
    | l ::= a1 => 
        update st l (aeval st a1)
    | c1 ; c2 => 
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI => 
        if (beval st b) 
          then ceval_fun_no_while st c1 
          else ceval_fun_no_while st c2
    | WHILE b1 DO c1 END => 
        st  (* bogus *)
  end.
(**
Note that it is also equivalent to the following,
*)
Fixpoint my_ceval_fun_no_while (st:state)(c:com):state:=
  match c with
    | SKIP =>
       st
    | l ::= a1 =>
      update st l (aeval st a1)
    | c1 ; c2 =>
      my_ceval_fun_no_while (my_ceval_fun_no_while st c1) c2
    | IFB b THEN c1 ELSE c2 FI =>
      match (beval st b) with
       | true => my_ceval_fun_no_while st c1
       | false => my_ceval_fun_no_while st c2
      end
    | WHILE b1 DO c1 END =>
      st (*bogus*)
   end.
(**
Alternatively, it can be defined as a relation as follows,
*)
Inductive ceval_r: state -> com -> state -> Prop:=
| r_cskip: forall st:state, ceval_r st SKIP st
| r_cass: forall (st st':state)(l:id)(a:aexp), st' = update st l (aeval st a) -> ceval_r st (l::=a) st'
| r_cseq: forall (st st' st'':state)(c1 c2:com), ceval_r st c1 st' -> ceval_r st' c2 st'' -> ceval_r st (c1;c2) st''
| r_cif_t: forall (b:bexp)(c1 c2 :com)(st st':state), beval st b =true ->ceval_r st c1 st' ->ceval_r st (IFB b THEN c1 ELSE c2 FI) st'
| r_cif_f: forall (b:bexp)(c1 c2 :com)(st st':state), beval st b =false->ceval_r st c2 st' ->ceval_r st (IFB b THEN c1 ELSE c2 FI) st'
| r_cwhile_c:forall (b:bexp)(c:com)(st st' st'':state),  beval st b =true -> ceval_r st c st'  -> ceval_r st' (WHILE b DO c END) st'' ->ceval_r st (WHILE b DO c END) st''     
| r_cwhile_t:forall (b:bexp)(c:com)(st:state), beval st b=false ->ceval_r st (WHILE b DO c END) st
.
(**
A group of tests should be conducted here,
*)
Example test_ceval_r1:
     ceval_r empty_state SKIP empty_state.
Proof. apply r_cskip. Qed.
Example test_ceval_r2:
     ceval_r empty_state (X::=APlus (ANum 7)(ANum 9)) (update empty_state X (aeval empty_state (APlus (ANum 7)(ANum 9)))).
Proof. apply r_cass. reflexivity. Qed.
Example test_ceval_r3:
     ceval_r empty_state (X::=ANum 1;Y::=ANum 2) (update (update empty_state X 1) Y 2).
Proof. apply r_cseq with (st':= update empty_state X 1). apply r_cass. reflexivity.
 apply r_cass. reflexivity.
Qed.
Lemma update_shadow_1 : forall x1 x2 k2 (f : state),
   update  (update f k2 x1) k2 x2  = update f k2 x2.
Proof. (*how to prove it*)
Admitted.
Example test_ceval_r4:
     ceval_r empty_state (X::=ANum 1;X::=ANum 2) (update empty_state X 2).
Proof. apply r_cseq with (st':=update empty_state X 1). apply r_cass. reflexivity.
apply r_cass. simpl. rewrite ->update_shadow_1. reflexivity.
Qed.
Example test_ceval_r5:
    ceval_r empty_state (IFB (BEq (AId X) (ANum 0)) THEN X::= (ANum 4) ELSE SKIP FI) (update empty_state X 4).
Proof. apply r_cif_t. simpl. reflexivity. apply r_cass. reflexivity.
Qed.
Example test_ceval_r6:
    ceval_r (update empty_state X 4) (IFB (BEq (AId X)(ANum 0)) THEN X::=(ANum 5) ELSE SKIP FI)(update empty_state X 4).
Proof. apply r_cif_f. simpl. reflexivity.  apply r_cskip.
Qed.

Example test_ceval_r7:
   ceval_r empty_state (Z::=(ANum 3);WHILE BNot (BEq (AId Z)(ANum 0))DO Z ::= AMinus (AId Z)(ANum 1)END)(update empty_state Z 0).
Proof. apply r_cseq with (st':= update empty_state Z 3). apply r_cass. reflexivity.
       apply r_cwhile_c with (st':=update empty_state Z 2). simpl. reflexivity.
      apply r_cass. simpl. rewrite ->update_shadow_1. reflexivity.
       apply r_cwhile_c with (st':=update empty_state Z 1). simpl. reflexivity.
       apply r_cass. simpl. rewrite ->update_shadow_1. reflexivity.
       apply r_cwhile_c with (st':=update empty_state Z 0). simpl. reflexivity.
       apply r_cass. simpl. rewrite ->update_shadow_1. reflexivity.
       apply r_cwhile_t. simpl. reflexivity.
Qed.
(**
Note that according to the tests, the relation [ceval_r] seems to work well.
It examplifies the advantage of using proposition which allows us to break
a while loop of runs to a small number of runs as long as the loop condition
is satisfied. 
*) 
(** In a traditional functional programming language like ML or
    Haskell we could write the WHILE case as follows:
<<
Fixpoint ceval_fun (st : state) (c : com) : state :=
  match c with 
    ...
    | WHILE b1 DO c1 END => 
        if (beval st b1) 
          then ceval_fun st (c1; WHILE b1 DO c1 END)
          else st 
  end.
>>
    Coq doesn't accept such a definition ([Error: Cannot guess
    decreasing argument of fix]) because the function we want to
    define is not guaranteed to terminate. Indeed, the full version of
    the [ceval_fun] function applied to the [loop] program above would
    never terminate. Since Coq is not just a functional programming
    language, but also a consistent logic, any potentially
    non-terminating function needs to be rejected. Here is an
    invalid(!) Coq program showing what would go wrong if Coq allowed
    non-terminating recursive functions:
<<
     Fixpoint loop_false (n : nat) : False := loop_false n.
>>
    That is, propositions like [False] would become
    provable (e.g. [loop_false 0] would be a proof of [False]), which
    would be a disaster for Coq's logical consistency.

    Thus, because it doesn't terminate on all inputs, the full version
    of [ceval_fun] cannot be written in Coq -- at least not without
    additional tricks, which make everything much more complicated
    (see chapter [ImpCEvalFun] if curious). *)


(* #################################### *)
(** ** Evaluation as a Relation *)

(** Here's a better way: we define [ceval] as a _relation_ rather than
    a _function_ -- i.e., we define it in [Prop] instead of [Type], as
    we did for [aevalR] and [bevalR] above. *)

(** This is an important change.  Besides freeing us from the
    hacks that would be needed to define an evaluation function, it
    gives us a lot more flexibility in the definition.  For example,
    if we added concurrency features to the language, we'd want the
    definition of evaluation to be non-deterministic -- i.e., not only
    would it not be total, it would not even be a partial function! *)

(** We'll use the notation [c / st || st'] for our [ceval] relation,
    that is [c / st || st'] means that executing program [c] in a
    starting state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". 
                           ----------------                            (E_Skip)
                           SKIP / st || st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   X := a1 / st || (update st X n)
        
                           c1 / st || st'
                          c2 / st' || st''
                         -------------------                            (E_Seq)
                         c1;c2 / st || st''

                          beval st b1 = true
                           c1 / st || st'
                -------------------------------------                (E_IfTrue)
                IF b1 THEN c1 ELSE c2 FI / st || st'

                         beval st b1 = false
                           c2 / st || st'
                -------------------------------------               (E_IfFalse)
                IF b1 THEN c1 ELSE c2 FI / st || st'

                         beval st b1 = false
                    ------------------------------                 (E_WhileEnd)
                    WHILE b1 DO c1 END / st || st

                          beval st b1 = true
                           c1 / st || st'
                  WHILE b1 DO c1 END / st' || st''
                  ---------------------------------               (E_WhileLoop)
                    WHILE b1 DO c1 END / st || st''
*)

(** Here is the formal definition.  (Make sure you understand
    how it corresponds to the inference rules.) *)
(**
Note that the idea behind [ceval_r] and [ceval] above is the same.
*)
Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Ass  : forall st a1 n X,
      aeval st a1 = n ->
      (X ::= a1) / st || (update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || st' ->
      c2 / st' || st'' ->
      (c1 ; c2) / st || st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      c1 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      c2 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      c1 / st || st' ->
      (WHILE b1 DO c1 END) / st' || st'' ->
      (WHILE b1 DO c1 END) / st || st''

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)

Example my_ceval_example1:
     ceval_r empty_state (X::=ANum 2;
                          IFB BLe (AId X) (ANum 1)
                              THEN Y ::=ANum 3          
                              ELSE Z ::=ANum 4 FI) (update(update empty_state X 2) Z 4).
Proof. apply r_cseq with (st':= update empty_state X 2). apply r_cass. reflexivity.
       apply r_cif_f. simpl. reflexivity. apply r_cass. simpl. reflexivity.
Qed. 

Example ceval_example1:      
    (X ::= ANum 2; 
     IFB BLe (AId X) (ANum 1) 
       THEN Y ::= ANum 3 
       ELSE Z ::= ANum 4 
     FI) 
   / empty_state 
   || (update (update empty_state X 2) Z 4).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (update empty_state X 2).
  Case "assignment command".
    apply E_Ass. reflexivity.
  Case "if command".
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.  Qed.

(** **** Exercise: 2 stars (ceval_example2) *)
(* EXPECTED *)
Example ceval_example2:
    (X ::= ANum 0; Y ::= ANum 1; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof. 
apply E_Seq with (update empty_state X 0).
apply E_Ass. reflexivity.
apply E_Seq with (update (update empty_state X 0) Y 1).
apply E_Ass. reflexivity.
apply E_Ass. simpl. reflexivity.
Qed.
(* FILL IN HERE *) 
(** [] *)

(** **** Exercise: 3 stars, optional (pup_to_n) *)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].
   Prove that this program executes as intended for X = 2
   (this latter part is trickier than you might expect). *)

Definition pup_to_n : com := 
(* FILL IN HERE *) 
Y::=ANum 0;
WHILE BNot (BLe (AId X)(ANum 0)) DO Y::=APlus (AId X)(AId Y);X::=AMinus (AId X)(ANum 1) END.

Theorem my_pup_to_2_ceval:
   ceval_r (update empty_state X 2) pup_to_n (update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0).
Proof.
apply r_cseq with (st':= update (update empty_state X 2) Y 0).
apply r_cass. reflexivity.
apply r_cwhile_c with (st':=update (update (update (update empty_state X 2) Y 0) Y 2) X 1).
simpl. reflexivity. apply r_cseq with (st':= update (update (update empty_state X 2) Y 0) Y 2).
apply r_cass. reflexivity. apply r_cass. simpl. reflexivity.
apply r_cwhile_c with (st':=update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0). simpl. reflexivity. 
apply r_cseq with (st':=update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3).
apply r_cass. reflexivity. apply r_cass. reflexivity.
apply r_cwhile_t. simpl. reflexivity.
Qed.
Theorem pup_to_2_ceval : 
  pup_to_n / (update empty_state X 2) ||
    update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
apply E_Seq with (st':= update (update empty_state X 2) Y 0).
apply E_Ass. reflexivity.
apply E_WhileLoop with (st':=update (update (update (update empty_state X 2) Y 0) Y 2) X 1).
simpl. reflexivity. apply E_Seq with (st':= update (update (update empty_state X 2) Y 0) Y 2).
apply E_Ass. reflexivity. apply E_Ass. simpl. reflexivity.
apply E_WhileLoop with (st':=update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0). simpl. reflexivity. 
apply E_Seq with (st':=update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3).
apply E_Ass. reflexivity. apply E_Ass. reflexivity.
apply E_WhileEnd. simpl. reflexivity.
Qed.

(* FILL IN HERE *) 

(** [] *)

(* ####################################################### *)
(** ** Determinism of Evaluation *)

(** Changing from a computational to a relational definition of
    evaluation is a good move because it allows us to escape from the
    artificial requirement (imposed by Coq's restrictions on
    [Fixpoint] definitions) that evaluation should be a total
    function.  But it also raises a question: Is the second definition
    of evaluation actually a partial function?  That is, is it
    possible that, beginning from the same state [st], we could
    evaluate some command [c] in different ways to reach two different
    output states [st'] and [st'']?
 
    In fact, this cannot happen: [ceval] is a partial function.
    Here's the proof: *)
(**
Firstly, prove that [ceval_r] is deterministic,
*)

Theorem ceval_r_deterministic: forall c st st1 st2,
   ceval_r st c st1 -> ceval_r st c st2 -> st1 = st2.
Proof.
intros c st st1 st2 H. generalize dependent st2.  induction H.
Case ("r_cskip"). intros. inversion H. reflexivity.
Case ("r_cass"). intros. inversion H0. subst. reflexivity.
Case ("r_cseq"). intros. inversion H1. apply IHceval_r1 in H5.
                 rewrite <-H5 in H7. apply IHceval_r2 in H7. apply H7.
Case ("r_cif_t"). intros. inversion H1. apply IHceval_r in H8. apply H8.
                  rewrite->H in H7. inversion H7.
Case ("r_cif_f"). intros. inversion H1. rewrite->H in H7. inversion H7.
                  apply IHceval_r in H8. apply H8.
Case ("r_cwhile_c"). intros. inversion H2. apply IHceval_r1 in H7.
                  rewrite<-H7 in H9. apply IHceval_r2 in H9. apply H9. 
                  rewrite<-H5 in H7. rewrite->H in H7. inversion H7.
Case ("r_cwhile_t"). intros. inversion H0. rewrite->H in H3. inversion H3.
                  reflexivity.
Qed. 

(**
Note that [ceval_r], seemingly, is much easier to work with.
*)







Theorem ceval_deterministic: forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof. 
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  ceval_cases (induction E1) Case; 
           intros st2 E2; inversion E2; subst. 
  Case "E_Skip". reflexivity.
  Case "E_Ass". reflexivity.
  Case "E_Seq". 
    assert (st' = st'0) as EQ1.
      SCase "Proof of assertion". apply IHE1_1; assumption.
    subst st'0.
    apply IHE1_2. assumption. 
  Case "E_IfTrue". 
    SCase "b1 evaluates to true".
      apply IHE1. assumption.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_IfFalse". 
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H5. inversion H5.
    SCase "b1 evaluates to false".
      apply IHE1. assumption.
  Case "E_WhileEnd". 
    SCase "b1 evaluates to true".
      reflexivity.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H2. inversion H2.
  Case "E_WhileLoop". 
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H4. inversion H4.
    SCase "b1 evaluates to false".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion". apply IHE1_1; assumption.
      subst st'0.
      apply IHE1_2. assumption.  Qed.

(* ####################################################### *)
(** * Reasoning About Programs *)

(** We'll get much deeper into systematic techniques for reasoning
    about Imp programs in the following chapters, but we can do quite
    a bit just working with the bare definitions.  This section
    explores some examples. *)

(** ** Basic Examples *)
Theorem my_plus2_spec: forall st n st',
   st X =n ->
   ceval_r st plus2 st' ->
   st' X = n+2.
Proof.
intros. inversion H0. simpl in H5. rewrite->H in H5.
rewrite->H5. rewrite->update_eq. reflexivity.
Qed.


Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st || st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  (* Inverting Heval essentially forces Coq to expand one 
     step of the ceval computation - in this case revealing 
     that st' must be st extended with the new value of X, 
     since plus2 is an assignment *)
  inversion Heval. subst. clear Heval. simpl.
  apply update_eq.  Qed.

(** **** Exercise: 3 stars, recommended (XtimesYinZ_spec) *)
(* EXPECTED *)
(** State and prove a specification of [XtimesYinZ]. *)
(* FILL IN HERE *)
Theorem my_XtimesYinZ_spec: forall st n m st',
st X = n -> st Y = m ->
ceval_r st XtimesYinZ st' ->
st' Z = n*m.
Proof.
intros. inversion H1. subst. clear H1. simpl.
rewrite->update_eq. reflexivity.
Qed.

Theorem XtimesYinZ_spec : forall st n m st',
  st X = n ->st Y = m ->
  XtimesYinZ / st || st' ->
  st' Z= n*m.
Proof.
intros st n m st' HX HY Heval. inversion Heval. subst.
clear Heval. apply update_eq.
Qed.
(** [] *)

(** **** Exercise: 3 stars, recommended (loop_never_stops) *)
(* EXPECTED *)
Theorem my_loop_never_stops : forall st st',
        ~(ceval_r st loop st').
Proof.
intros st st' contra. unfold loop in contra.
remember (WHILE BTrue DO SKIP END) as loopdef.  induction contra.
inversion Heqloopdef. inversion Heqloopdef. inversion Heqloopdef.
inversion Heqloopdef. inversion Heqloopdef. 
apply  IHcontra2. apply Heqloopdef. inversion Heqloopdef. rewrite->H1 in H.
inversion H.
Qed.



Theorem loop_never_stops : forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef.
  (* Proceed by induction on the assumed derivation showing that
     [loopdef] terminates.  Most of the cases are immediately
     contradictory (and so can be solved in one step with
     [inversion]). *)

(* FILL IN HERE *) 
induction contra;inversion Heqloopdef.
 rewrite->H1 in H. inversion H. apply IHcontra2.
apply Heqloopdef.
Qed.

(** [] *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP       => true
  | _ ::= _    => true
  | c1 ; c2  => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  => false
  end.

(** **** Exercise: 3 stars, optional (no_whilesR) *)
(** The [no_whiles] property yields [true] on just those programs that
    have no while loops.  Using [Inductive], write a property
    [no_whilesR] such that [no_whilesR c] is provable exactly when [c]
    is a program with no while loops.  Then prove its equivalence
    with [no_whiles]. *)
Inductive my_no_whilesR: com ->Prop:=
  | me_skip: my_no_whilesR SKIP
  | me_ass:forall (X:id)(a:aexp), my_no_whilesR (X::=a)
  | me_seq:forall (c1 c2:com), my_no_whilesR c1->my_no_whilesR c2->my_no_whilesR (c1;c2)
  | me_if:forall (b:bexp)(ct cf:com),my_no_whilesR ct->my_no_whilesR cf->my_no_whilesR (IFB b THEN ct ELSE cf FI)
 .
Hint Constructors my_no_whilesR.

Example test_my_no_whilesR1:
   my_no_whilesR SKIP.
Proof. apply me_skip. Qed.
Example test_my_no_whilesR2:
   my_no_whilesR (X::=APlus (AId Y)(ANum 3);SKIP).
Proof.
apply me_seq. apply me_ass. apply me_skip. Qed.
Example test_my_no_whilesR3:
   my_no_whilesR (IFB BTrue THEN X::=ANum 3 ELSE X::=ANum 4 FI).
Proof. 
apply me_if;apply me_ass. Qed.
Example test_my_no_whilesR4:
   ~my_no_whilesR (WHILE BFalse DO X::=ANum 1 END).
Proof.
intros contra. inversion contra. Qed.  

Inductive no_whilesR: com -> Prop := 
(* FILL IN HERE *)
| e_skip: no_whilesR SKIP
| e_ass: forall (X:id)(e:aexp), no_whilesR (X::=e)
| e_seq: forall (c1 c2:com), no_whilesR c1 ->no_whilesR c2 -> no_whilesR (c1;c2)
| e_if: forall (b:bexp)(ct cf:com), no_whilesR ct ->no_whilesR cf ->no_whilesR (IFB b THEN ct ELSE cf FI)
.

(**
Before proving the equivalence between the two,
 a few tests of [no_whilesR] written below,
*)
Example no_whilesR1:
    no_whilesR SKIP.
Proof. apply e_skip. Qed.
Example no_whilesR2:
    no_whilesR (X::=ANum 9).
Proof. apply e_ass. Qed.
Example no_whilesR3:
    no_whilesR (X::=ANum 0;Y::=ANum 9).
Proof. apply e_seq;apply e_ass. Qed.
Example no_whilesR4:
    no_whilesR (IFB BTrue THEN X::=ANum 2 ELSE X::=ANum 0 FI).
Proof. apply e_if;apply e_ass. Qed. 

Lemma my_no_whiles_eqv_1:forall b1 b2:bool,
     b1&&b2=true ->b1=true/\b2=true.
Proof.
intros. destruct b1. destruct b2.
split;reflexivity. split. reflexivity. simpl in H. apply H.
destruct b2. split. simpl in H. apply H. reflexivity. simpl in H.
split;apply H. Qed.

Theorem my_no_whiles_eqv:forall c:com,
       no_whiles c = true <-> my_no_whilesR c.
Proof.
intros. split.
Case ("->"). intros. induction c.
     SCase ("SKIP"). apply me_skip.
     SCase ("X::=a"). apply me_ass.
     SCase ("SEQ"). inversion H. apply my_no_whiles_eqv_1 in H1.
                    inversion H1. apply me_seq. apply IHc1 in H0.
                    apply H0. apply IHc2 in H2. apply H2.
     SCase ("IFB"). inversion H. apply my_no_whiles_eqv_1 in H1.
                    inversion H1. apply me_if. apply IHc1 in H0.
                    apply H0. apply IHc2 in H2. apply H2.
     SCase ("WHILE"). inversion H.
Case ("<-"). intros. induction c.
     SCase ("SKIP"). reflexivity.
     SCase ("X::=a"). reflexivity.
     SCase ("SEQ"). simpl. inversion H. apply IHc1 in H2. apply IHc2 in H3.
                    rewrite->H2. rewrite->H3. reflexivity.
     SCase ("IFB"). simpl. inversion H.  apply IHc1 in H2. apply IHc2 in H4.
                    rewrite->H2. rewrite->H4. reflexivity.
     SCase ("WHILE"). inversion H.
Qed.


Lemma no_whiles_eqv_1: forall b1 b2,
     b1&&b2=true ->b1=true /\ b2=true.
Proof.
intros. destruct b1. destruct b2. split;reflexivity.
split;try reflexivity. simpl in H. inversion H.
destruct b2. split;try reflexivity. simpl in H. apply H.
split;simpl in H;apply H. Qed.
Lemma no_whiles_eqv_2: forall b1 b2,
     b1=true/\b2=true -> b1&&b2=true.
Proof.
intros. inversion H. subst. reflexivity. Qed.
Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
(* FILL IN HERE *) 
split. 
Case ("->"). intros. induction c.
     SCase ("SKIP"). constructor.
     SCase ("i::=a"). constructor.
     SCase ("c1;c2"). constructor. inversion H.
                      apply no_whiles_eqv_1 in H1.
                      inversion H1. apply IHc1.  apply H0.
                      apply IHc2. inversion H. rewrite->H1.
                      apply no_whiles_eqv_1 in H1.
                      inversion H1. apply H2.
     SCase ("IF"). inversion H. apply e_if. apply no_whiles_eqv_1 in H1.
                   inversion H1. apply IHc1 in H0. apply H0.
                   apply no_whiles_eqv_1 in H1. inversion H1.
                   apply IHc2 in H2. apply H2. 
     SCase ("While"). inversion H.
Case ("<-"). intros. induction H;simpl;try reflexivity. 
             apply no_whiles_eqv_2. split. apply IHno_whilesR1.
             apply IHno_whilesR2. apply no_whiles_eqv_2. split.
             apply IHno_whilesR1. apply IHno_whilesR2. 
Qed.
(** [] *)

(** **** Exercise: 4 stars, optional (no_whiles_terminating) *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem that says this. *)
(** (Use either [no_whiles] or [no_whilesR], as you prefer.) *)
(* FILL IN HERE *)
Theorem nowhile_always_stops : forall c st,
         no_whilesR c ->exists st',ceval_r st c st'.
Proof.
intros c st H. generalize dependent st.
induction H.
Case ("SKIP"). intros. exists st. apply r_cskip.
Case ("X0::=e"). intros. exists (update st X0 (aeval st e)).
                apply r_cass. reflexivity.
Case ("c1;c2"). intros.
assert (exists st' : state, ceval_r st c1 st'). auto.
(*specialize (IHno_whilesR1 st)*)
 Admitted.
(** [] *)

(** ** Proving a Program Correct (Optional) *)

(** Recall the factorial program: *)

Print fact_body. Print fact_loop. Print fact_com.

(** Here is an alternative "mathematical" definition of the factorial
    function: *)
Fixpoint my_real_fact (n:nat):nat:=
match n with
|0=>1
|S n'=>n* (my_real_fact n')
end.

Example test_my_real_fact1:
    my_real_fact 0 =1.
Proof. reflexivity. Qed.
Example test_my_real_fact2:
    my_real_fact 2 =2.
Proof. simpl. reflexivity. Qed.
Example test_my_real_fact3:
    my_real_fact 3 = 6.
Proof. reflexivity. Qed.






Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(** We would like to show that they agree -- if we start [fact_com] in
    a state where variable [X] contains some number [x], then it will
    terminate in a state where variable [Y] contains the factorial of
    [x].

    To show this, we rely on the critical idea of a _loop
    invariant_. *)
Definition my_fact_invariant (x:nat)(st:state):=
  (st Y)*(my_real_fact (st Z))=my_real_fact x.
Lemma my_real_fact_1:forall n,
     n<>0 -> my_real_fact n = n * (my_real_fact (n-1)).
Proof.
intros. destruct n. simpl. assert (A: False ->1=0). intros. inversion H0.
apply A. apply H. reflexivity. simpl. rewrite<-minus_n_O.
reflexivity.
Qed.
Theorem my_fact_body_preserves_invariant: forall st st' x,
     my_fact_invariant x st->
     st Z <> 0 ->
     ceval_r st fact_body st'->
     my_fact_invariant x st'.
Proof.
intros. unfold my_fact_invariant. unfold my_fact_invariant in H.
unfold fact_body in H1. inversion H1. inversion H5. inversion H7.
subst. simpl. simpl in H5. simpl in H1. simpl in H7.
assert (A: beq_id Z Y =false). reflexivity. 
apply update_neq with (st:=update st Y (st Y * st Z))(n:=update st Y (st Y * st Z) Z - 1) in A.
rewrite->A. rewrite->update_eq.
rewrite->update_eq. 
assert (B: beq_id Y Z =false). reflexivity.
apply update_neq with (st:=st)(n:=st Y * st Z) in B. rewrite->B.
apply my_real_fact_1 with (n:=st Z) in H0. 
rewrite->mult_assoc_reverse. rewrite<-H0.
apply H.
Qed.

Theorem my_fact_loop_preserves_invariant : forall st st' x,
     my_fact_invariant x st ->
     ceval_r st fact_loop st' ->
     my_fact_invariant x st'.
Proof.
intros. remember fact_loop as FL.  induction H0;inversion HeqFL.
subst. apply IHceval_r2. simpl in H0. 
assert (A:forall b:bool, negb b =true->b=false). intros. destruct b.
inversion H1. reflexivity. apply A in H0. 
assert (B:forall n:nat, beq_nat n 0=false ->n<>0). intros.
destruct n. inversion H1. intros contra. inversion contra.
apply B in H0. 
apply my_fact_body_preserves_invariant with (st':=st') in H.
apply H. apply H0. apply H0_. apply HeqFL. apply H.
Qed.

Theorem my_guard_false_after_loop: forall b c st st',
     ceval_r st (WHILE b DO c END) st' ->
     beval st' b = false.
Proof.
intros. remember (WHILE b DO c END) as BB. induction H;inversion HeqBB.
subst. apply IHceval_r2. reflexivity. subst. apply H.
Qed.

Theorem my_fact_com_correct : forall st st' x,
     st X = x ->
     ceval_r st fact_com st' ->
     st' Y = my_real_fact x.
Proof.
intros. destruct x as [|x'].
Case ("x=0"). simpl. unfold fact_com in H0.
              inversion H0. inversion H4. subst. simpl in H6.
              inversion H6. subst. inversion H5. subst. simpl in H5.
              simpl in H8. inversion H8. subst. simpl in H3.
              assert (A: beq_id Y Z =false). reflexivity.
              apply update_neq with (st:=update st Z (st X))(n:=1) in A.
              rewrite->A in H3. rewrite->update_eq in H3. rewrite->H in H3.
              assert (B:forall b:bool, negb b=true->b=false). intros. destruct b.
              inversion H1. reflexivity. apply B in H3. inversion H3.
              rewrite->update_eq. reflexivity.
Case ("x=S x'"). assert (A: st X = S x' -> st X <>0). intros. intros contra.
               rewrite->contra in H1. inversion H1. rewrite<-H. apply A in H.
               clear A. clear x'. unfold fact_com in H0. inversion H0. subst.
               inversion H4. subst. simpl in H4. simpl in H6. inversion H6.
               subst. inversion H5. subst. simpl in H5. simpl in H8.
              clear H0. clear H4. clear H6. clear H5.
               assert (A: update (update st Z (st X)) Y 1 Y=1). rewrite->update_eq.
               reflexivity.
               assert (B: update (update st Z (st X)) Y 1 Z =st X). 
               assert (B_1:beq_id Y Z=false). reflexivity. 
            apply update_neq with (st:=update st Z (st X))(n:=1)in B_1.
                rewrite->B_1. rewrite->update_eq. reflexivity.
               assert (C:my_fact_invariant (st X)(update (update st Z (st X)) Y 1)).
                unfold my_fact_invariant. rewrite->A. rewrite->B. rewrite->mult_1_l. 
               reflexivity. 
               apply my_fact_loop_preserves_invariant with (st':=st') in C.
               unfold my_fact_invariant in C. 
               assert (H8':ceval_r (update (update st Z (st X)) Y 1) fact_loop st').
               apply H8.              
               apply my_guard_false_after_loop in H8.
               simpl in H8. assert (forall b:bool, negb b=false ->b=true). intros.
                destruct b. inversion H0. reflexivity. inversion H0. apply H0 in H8.
                clear H0. assert (D: forall n:nat, beq_nat n 0 =true->n=0). intros.
                destruct n. reflexivity. inversion H0. apply D in H8.
               rewrite->H8 in C. simpl in C. rewrite->mult_1_r in C. apply C.
               apply H8.
Qed.


(*#########################################################*)

Definition fact_invariant (x:nat) (st:state) :=
  (st Y) * (real_fact (st Z)) = real_fact x.

Theorem fact_body_preserves_invariant: forall st st' x,
     fact_invariant x st ->
     st Z <> 0 ->
     fact_body / st || st' ->
     fact_invariant x st'.
Proof.
  unfold fact_invariant, fact_body.
  intros st st' x Hm HZnz He.
  inversion He; subst; clear He.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  unfold update. simpl.
  (* Show that st Z = S z' for some z' *)
  destruct (st Z) as [| z'].
    apply ex_falso_quodlibet. apply HZnz. reflexivity.
  rewrite <- Hm. rewrite <- mult_assoc.
  replace (S z' - 1) with z' by omega. 
  reflexivity.  Qed.

Theorem fact_loop_preserves_invariant : forall st st' x,
     fact_invariant x st ->
     fact_loop / st || st' ->
     fact_invariant x st'.
Proof.
  intros st st' x H Hce.
  remember fact_loop as c.
  ceval_cases (induction Hce) Case; 
              inversion Heqc; subst; clear Heqc.
  Case "E_WhileEnd".
    (* trivial when the loop doesn't run... *)
    assumption.
  Case "E_WhileLoop".
    (* if the loop does run, we know that fact_body preserves
       fact_invariant -- we just need to assemble the pieces *)
    apply IHHce2. 
      apply fact_body_preserves_invariant with st; 
            try assumption.
      intros Contra. simpl in H0; subst. 
      rewrite Contra in H0. inversion H0. 
      reflexivity.  Qed.

Theorem guard_false_after_loop: forall b c st st',
     (WHILE b DO c END) / st || st' ->
     beval st' b = false.
Proof.
  intros b c st st' Hce.
  remember (WHILE b DO c END) as cloop.
  ceval_cases (induction Hce) Case; 
     inversion Heqcloop; subst; clear Heqcloop.
  Case "E_WhileEnd".
    assumption.
  Case "E_WhileLoop".
    apply IHHce2. reflexivity.  Qed.

(** Patching it all together... *)

Theorem fact_com_correct : forall st st' x,
     st X = x ->
     fact_com / st || st' ->
     st' Y = real_fact x.
Proof.
  intros st st' x HX Hce.
  inversion Hce; subst; clear Hce.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  inversion H1; subst; clear H1.
  rename st' into st''. simpl in H5.
  (* The invariant is true before the loop runs... *)
  remember (update (update st Z (st X)) Y 1) as st'.
  assert (fact_invariant (st X) st').
    subst. unfold fact_invariant, update. simpl. omega.
  (* ...so when the loop is done running, the invariant 
     is maintained *)
  assert (fact_invariant (st X) st'').
    apply fact_loop_preserves_invariant with st'; assumption.
  unfold fact_invariant in H0.
  (* Finally, if the loop terminated, then Z is 0; so Y must be
     factorial of X *)
  apply guard_false_after_loop in H5. simpl in H5.
  destruct (st'' Z).
  Case "st'' Z = 0". simpl in H0. omega. 
  Case "st'' Z > 0 (impossible)". inversion H5.
Qed.

(** One might wonder whether all this work with poking at states and
    unfolding definitions could be ameliorated with some more powerful
    lemmas and/or more uniform reasoning principles... Indeed, this is
    exactly the topic of the upcoming [Hoare] chapter! *)

(** **** Exercise: 4 stars, optional (subtract_slowly_spec) *)
(** Prove a specification for subtract_slowly, using the above
    specification of [fact_com] and the invariant below as
    guides. *)

Definition ss_invariant (x:nat) (z:nat) (st:state) :=
  minus (st Z) (st X) = minus z x.

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars, optional (add_for_loop) *)
(** Add C-style [for] loops to the language of commands, update the
    [ceval] definition to define the semantics of [for] loops, and add
    cases for [for] loops as needed so that all the proofs in this file
    are accepted by Coq.

    A [for] loop should be parameterized by (a) a statement executed
    initially, (b) a test that is run on each iteration of the loop to
    determine whether the loop should continue, (c) a statement
    executed at the end of each loop iteration, and (d) a statement
    that makes up the body of the loop.  (You don't need to worry
    about making up a concrete Notation for [for] loops, but feel free
    to play with this too if you like.) *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, optional (short_circuit) *)  
(** Most modern programming languages use a "short-circuit" evaluation
    rule for boolean [and]: to evaluate [BAnd b1 b2], first evaluate
    [b1].  If it evaluates to [false], then the entire [BAnd]
    expression evaluates to [false] immediately, without evaluating
    [b2].  Otherwise, [b2] is evaluated to determine the result of the
    [BAnd] expression.

    Write an alternate version of [beval] that performs short-circuit
    evaluation of [BAnd] in this manner, and prove that it is
    equivalent to [beval]. *)
(* FILL IN HERE *)

(** **** Exercise: 4 stars, recommended (stack_compiler) *)
(** HP Calculators, programming languages like Forth and Postscript,
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a stack. For instance, the expression
<<
   (2*3)+(3*(4-2))
>>
   would be entered as
<<
   2 3 * 3 4 2 - * +
>>
   and evaluated like this:
<<
  []            |    2 3 * 3 4 2 - * +
  [2]           |    3 * 3 4 2 - * +
  [3, 2]        |    * 3 4 2 - * +
  [6]           |    3 4 2 - * +
  [3, 6]        |    4 2 - * +
  [4, 3, 6]     |    2 - * +
  [2, 4, 3, 6]  |    - * +
  [2, 3, 6]     |    * +
  [6, 6]        |    +
  [12]          | 
>>

  The task of this exercise is to write a small compiler that
  translates [aexp]s into stack machine instructions, and to prove its
  correctness.

  The instruction set for our stack language will consist of the
  following instructions:    
     - [SPush n]: Push the number [n] on the stack.
     - [SLoad X]: Load the identifier [X] from the store and push it
                  on the stack
     - [SPlus]:   Pop the two top numbers from the stack, add them, and
                  push the result onto the stack.
     - [SMinus]:  Similar, but subtract.
     - [SMult]:   Similar, but multiply.
*)

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr. 

(** Write a function to evaluate programs in the stack language. It
    takes as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and returns the stack after
    executing the program. Test your function on the examples below.

    Note that the specification leaves unspecified what to do when
    encountering an [SPlus], [SMinus], or [SMult] instruction if the
    stack contains less than two elements.  In a sense it is
    immaterial, since our compiler will never emit such a malformed
    program. However, when you do the correctness proof you may find
    some choices makes the proof easier than others. *)

Fixpoint s_execute (st : state) (stack : list nat) 
                   (prog : list sinstr) 
                 : list nat :=
(* FILL IN HERE *) admit.

Example s_execute1 : 
     s_execute empty_state [] 
       [SPush 5, SPush 3, SPush 1, SMinus]
   = [2, 5].
(* FILL IN HERE *) Admitted.

Example s_execute2 : 
     s_execute (update empty_state X 3) [3,4] 
       [SPush 4, SLoad X, SMult, SPlus]
   = [15, 4].
(* FILL IN HERE *) Admitted. 

(** Next, write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr :=
(* FILL IN HERE *) admit.

(* 
Example s_compile1 : 
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X, SPush 2, SLoad Y, SMult, SMinus].
Proof. reflexivity. Qed.
*)

(** Finally, prove the following theorem, stating that the [compile]
    function behaves correctly.  You will need to start by stating a
    more general lemma to get a usable induction hypothesis. *)

(* FILL IN HERE *)

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
