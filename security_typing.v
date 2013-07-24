(*Security Typing*)

Require Export Ch10_Smallstep.

(*##########################security types##############################*)
(**
Firstly we define the type "Sec" for the security annotation
of the language as follows,
Sec ::= L
      | H
thus, we have two security labels with [L] standing for
low security and [H] for high security
*)
Inductive Sec : Type :=
| L : Sec
| H : Sec.

(**
Now we define the security type [Ty].
Suppose we have as our basis a type called "int" based upon
which we can construct types as,
a. int^L as a [int] type with label [L]
b. int^H as a [int] type with label [H]
C. (int^L -> int^H)^H as a function type with label [H] whose
   input and output have labels [L] and [H]
d. (int^H -> (int^L -> int^H)^L)^H as a function type with label [H]
   whose input has label [H] and whose body is also a function with
   label [L] and input and output with label [L] and [H]
In conclusion, we not only label our base type,[int], the function
type and its inputs and outputs are also labelled.
*)
(*base type*)
Inductive RawTy : Type :=
| int : RawTy.

(*security type*)
Inductive Ty : Type :=
| an_b : RawTy -> Sec -> Ty
| an_f : Ty -> Ty -> Sec -> Ty.
(**
Having defined our security types, our above examples can be expressed as follows,
a. [an_b int L : Ty]
b. [an_b int H : Ty]
c. [an_f (an_b int L) (an_b int H) H : Ty]
d. [an_f (an_b int H)(an_f (an_b int L)(an_b int H) L) H : Ty]
*)
(**
[RawTy] together with [Ty] above is equivalent to the 
following type system defined in Agda,
"
mutual
 data Ty : Set where
    _^_  : RawTy -> Sec -> Ty
 data RawTy : Set where
    int  : RawTy
    _->_ : Ty -> Ty -> RawTy
"
*)
Check (an_b int L).
Check (an_b int H).
Check (an_f (an_b int L) (an_b int H) H).
Check (an_f (an_b int H)(an_f (an_b int L)(an_b int H) L) H).
(*##########################end##############################*)

(*##########################terms##############################*)
(**
There are four sorts of terms in the system, variables, constants,
abstractions and applications:
t ::= x         variable
    | \x:T. t b abstraction
    | const n b constants
    | t1 t2     application
*)

Inductive tm : Type :=
| tvar  : option Sec -> id -> tm
| tcon  : nat -> Sec -> tm
| tabs  : id -> Ty -> tm -> Sec -> tm
| tapp  : tm -> tm -> tm

.
(**
Consider the following terms,
a. tvar _ (Id 0)
b. tcon 1 H
   tcon 2 L
c. tabs (Id 0) (an_b int L) (tvar _ (Id 0)) H
   tabs (Id 1) (an_f (an_b int H)(an_b int H) L) (tvar _ (Id 1)) H
   tabs (Id 0) (an_b int H) (tabs (Id 1) (an_b int L) (tvar _ (Id 0)) H) H

note since intuitively free variables are allowed in the system we should 
also consider functions with unbounded variables,
   tabs (Id 0) (an_b int H) (tvar _ (Id 1)) H

d. tapp (tabs (Id 0) (an_b int H) (tvar _ (Id 0)) H) (tcon 1 H)
*)
(*Var 0*)
Check tvar None (Id 0).
Check tvar (Some H) (Id 0).
Check tvar (Some L) (Id 0).
(*Const H 1*)
Check tcon 1 H.
(*Const L 2*)
Check tcon 2 L.
(*(\x:int^L. x)^H*)
Check tabs (Id 0) (an_b int L) (tvar None (Id 0)) H.
(*(\x:(int^H -> int^H)^L.x)^H*)
Check tabs (Id 1) (an_f (an_b int H)(an_b int H) L) (tvar None (Id 1)) H.
(*(\x:int^H.(\y:int^L.x)^H)^H*)
Check tabs (Id 0) (an_b int H) (tabs (Id 1) (an_b int L) (tvar None (Id 0)) H) H.
(*(\x:int^H.x)^H (Const H 1)*)
Check tapp (tabs (Id 0) (an_b int H) (tvar None (Id 0)) H) (tcon 1 H).
(*##########################end##############################*)




(*##########################Values of Ty##############################*)
(**
Consider the following evaluation sequences,
a.     (\x:int^L.x)^H (const L 1)
   ==> const L^H 1
   ==> const H 1
   note that when the function [\x:int^L.x] is applied to [const L 1]
   we substitute [const L 1] for the bounded variable in the body and
   join the security label of the function and that of the term after 
   substitution
b.     (\x:int^H. (\y:int^L. x)^L )^H (const H 2)
   ==> (\y:int^L. const H 2)^(L^H)
   ==> (\y:int^L. const H 2)^H
   in case of a function whose body is also a function, that is a function
   with at least two arguments,the resulting term after being applied to 
   just one argument,would again be a function whose label is the join of
   that of the original function and that of its body
b'.    (\x:int^H. (\y:int^L. y)^L )^H (const H 2)
   ==> (\y:int^L.y)^(L^H)
   ==> (\y:int^L.y)^H
c.     (\x:int^L.x)^H (y:int^L)
   ==> join H (lookup y st)
   note that [y] is a free variable of type [int^L] and after application
   the label of the value stored in [y] should be the join of the that of the
   function and that of the value
d.     (\x:(int^L -> int^L)^L. x)^H (\y:int^L. y)^L
   ==> (\y:int^L. y)^(L^H)
   ==> (\y:int^L. y)^H
e. suppose we have the following application,
       (\y:int^L.y)^H (const L 1)
   then apply it to an identity function,
       (\x:int^H.x)^H ((\y:int^L.y)^H (const L 1))
   ==> (\x:int^H.x)^H (const L^H 1)
   ==> (\x:int^H.x)^H const H 1
   ==> const H^H 1
   ==> const H 1

It is worth noticing that the above reductions are beta-reductions in that
we substitute the second argument for the bounded variable in the function only
when the second argument is a value.
This immediately implies that in our system, we have three sorts of values:
1. variables
   [tvar (Id n)]
   note that this is due to the fact that we do not distinguish bounded and free
   variables  syntactically and a well-typed [tvar (Id n)] representing some value
   could well be the second argument of application
2. constants
   [tcon n b]
3. restricted abstractions
   [tabs (Id n) (T:Ty) body (b:Sec)] where
   [body] itself is a value
   reduction stops at abstraction
*)

Inductive value : tm -> Prop :=
(**| v_v : forall n o,
        value (tvar  o (Id n)) *)
| v_c : forall b n,
        value (tcon n b)
| v_f : forall n T e b,
        value (tabs (Id n) T e b).

(*##########################end##############################*)


(*####################substitution###########################*)
(**
Note that the following function [subst] which substitute a term 
for the bounded variables in the function body,
[subst x s t b] is read as "substitute s for the bounded variable x in
expression t where the security label of the function is b"
*)

(**
Before specifying [subst] we define the following 
auxiliary function [update],
*)

Fixpoint upgrade (e:tm) (b:Sec): tm :=
 match b with
 | L => e
 | H => match e with
        | tvar _ x => tvar (Some H) x
        | tcon n _ => tcon n H
        | tabs x T t _ => tabs x T t H
        | tapp f e => tapp (upgrade f H) e
        end
 end.

(*#######tests of [update]##################*)
Example test_upgrade_1:
upgrade (tvar None (Id 0)) H = tvar (Some H) (Id 0).
Proof. simpl. reflexivity. Qed.
Example test_upgrade_2:
upgrade (tvar (Some L) (Id 0)) H = tvar (Some H) (Id 0).
Proof. simpl. reflexivity. Qed.
Example test_upgrade_3:
upgrade (tvar None (Id 0)) L = tvar None (Id 0).
Proof. simpl. reflexivity. Qed.
Example test_upgrade_4:
upgrade (tcon 1 L) H = tcon 1 H.
Proof. simpl. reflexivity. Qed.
Example test_upgrade_5:
upgrade (tcon 1 L) L = tcon 1 L.
Proof. simpl. reflexivity. Qed.
Example test_upgrade_6:
upgrade (tabs (Id 0) (an_b int H) (tvar None (Id 0)) L) H = tabs (Id 0) (an_b int H) (tvar None (Id 0)) H.
Proof. simpl. reflexivity. Qed.
Example test_upgrade_7:
upgrade (tabs (Id 0) (an_b int H) (tvar None (Id 0)) L) L = tabs (Id 0) (an_b int H) (tvar None (Id 0)) L.
Proof. simpl. reflexivity. Qed.
Example test_upgrade_8:
upgrade (tapp (tabs (Id 0) (an_b int L) (tvar None (Id 0)) L) (tcon 1 L)) H =
        tapp (tabs (Id 0) (an_b int L) (tvar None (Id 0)) H) (tcon 1 L).
Proof. simpl. reflexivity. Qed.
Example test_upgrade_9:
upgrade (tapp (tabs (Id 0) (an_b int L) (tvar None (Id 0)) L)(tcon 1 L)) L =
        tapp (tabs (Id 0) (an_b int L) (tvar None (Id 0)) L)(tcon 1 L).
Proof. simpl. reflexivity. Qed.
(*################end############################*)

Fixpoint subst (x:id) (s:tm) (t:tm): tm :=
  match t with
(*variables*)
  | tvar o x' => 
      if beq_id x x' then s else t
(*abstractions*)
  | tabs x' T t1 b => 
      tabs x' T (if beq_id x x' then t1 else (subst x s t1)) b
(*constants*)
  | tcon n b => tcon n b
(*applications*)
  | tapp t1 t2 => 
      tapp (subst x s t1) (subst x s t2)
  end.
Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(*############tests of [subst]##############*)
Example test_subst_1:
[(Id 0) := tcon 1 H] (tvar None (Id 0)) = tcon 1 H.
Proof. simpl. reflexivity. Qed.
Example test_subst_2:
[(Id 0) := (tvar None (Id 2))] (tvar None (Id 1)) = tvar None (Id 1).
Proof. simpl. reflexivity. Qed.
Example test_subst_3:
[(Id 0) := (tcon 1 H)] (tabs (Id 1) (an_b int H) (tvar None (Id 0)) H)
= tabs (Id 1) (an_b int H) (tcon 1 H) H.
Proof. simpl. reflexivity. Qed.
Example test_subst_4:
[(Id 0) := tcon 4 L] (tcon 1 H) = tcon 1 H.
Proof. simpl. reflexivity. Qed.
Example test_subst_5:
[(Id 0) := tcon 1 H] (tapp (tabs (Id 1) (an_b int H) (tvar None (Id 1)) H)(tvar None (Id 0)))
= tapp (tabs (Id 1) (an_b int H) (tvar None (Id 1)) H)(tcon 1 H).
Proof. simpl. reflexivity. Qed.
(*##############end#########################*)

(*########################end################################*)

(*#########################free-variables#############*)
(**
Note that since we have to deal with free variables here, we
must specify the values of these free variables appearing in
our terms.
There are two ways of doing it,
a. referring to [Imp.v]
   we can specify a partial function which takes free variables as inputs and
   returns their corresponding values which are the terms in the language,
   st := id -> tm
b. referring to [Reference.v]
   we can also define a list of terms of the language and each one of them
   corresponding to a specific free variable according to its id,
   st := list tm

We use the former method to deal with free variables.
In what follows, "st" stands for the "value context" for all free variables,
*)
Definition VStore := id -> option tm.

Definition empty_store : VStore := 
  fun _ => None.
 
Definition update (st : VStore) (X:id) (e : option tm) : VStore :=
  fun X' => if beq_id X X' then e else st X'.

(*#######some useful theorems regarding [update]#########*)
Theorem update_eq : forall e X st,
  (update st X e) X = e.
Proof.
intros. unfold update. rewrite<-beq_id_refl. reflexivity. 
Qed.
Theorem update_neq : forall V2 V1 e st,
  beq_id V2 V1 = false ->
  (update st V2 e) V1 = (st V1).
Proof.
intros. unfold update. rewrite H0. reflexivity.
Qed.
Theorem update_shadow : forall e1 e2 x1 x2 (f : VStore),
   (update  (update f x2 e1) x2 e2) x1 = (update f x2 e2) x1.
Proof.
intros. unfold update. destruct (beq_id x2 x1). reflexivity.
reflexivity.
Qed.
Theorem update_same : forall e1 x1 x2 (f : VStore),
  f x1 = e1 ->
  (update f x1 e1) x2 = f x2.
Proof.
intros. unfold update. remember (beq_id x1 x2) as D. destruct D.
Case ("true"). apply beq_id_eq in HeqD. subst. reflexivity.
reflexivity.
Qed. 
Theorem update_permute : forall e1 e2 x1 x2 x3 f,
  beq_id x2 x1 = false -> 
  (update (update f x2 e1) x1 e2) x3 = (update (update f x1 e2) x2 e1) x3.
Proof.
intros. unfold update. remember (beq_id x1 x3) as D1. remember (beq_id x2 x3) as D2.
destruct D1.
Case ("D1=true"). destruct D2.
      SCase ("D2=true"). apply beq_id_false_not_eq in H0.  apply beq_id_eq in HeqD1.
                         apply beq_id_eq in HeqD2. rewrite<-HeqD2 in HeqD1.
                         unfold not in H0. symmetry in HeqD1. apply H0 in HeqD1.
                         inversion HeqD1.
      SCase ("D2=false"). reflexivity.
Case ("D1=false"). destruct D2.
      SCase ("D2=true"). reflexivity.
      SCase ("D2=false"). reflexivity.
Qed.

(*###########################end######################*)

(*######small-step evaluation - part one#######################*)
(**
Note now we are ready to specify the small-step evaluation of the terms in
the language defined above. Let us consider the following instances of evaluation
sequences,
a. tapp (tabs (Id 0)(an_b int L)(tvar None (Id 0)) H)(tcon 1 L)
  ==> tcon 1 H
b. tapp 
   (tapp 
    (tabs (Id 1) (an_b int L)(tabs (Id 0) (an_b int L)(tvar None (Id 0)) L) H)
    (tcon 1 L)
    )
   (tapp
    (tabs (Id 0)(an_b int L)(tvar None (Id 0)) L)
    (tcon 1 L)
   )
==> tapp
    (tabs (Id 0)(an_b int L)(tvar None (Id 0)) H)
    (tapp 
     (tabs (Id 0)(an_b int L)(tvar None (Id 0)) L)
     (tcon 1 L)
    )
==> tapp
     (tabs (Id 0)(an_b int L)(tvar None (Id 0)) H)
     (tcon 1 L)
==> tcon 1 H
*)
(**
We define one auxiliary function "extract" which
upon receiving a term of type [option tm] gives us
the term without [Some] label attached to it,
*)
Definition extract (a : option tm) : tm :=
match a with
| Some e => e
| None   => tcon 1 L
end.
Inductive step : (tm * VStore) -> (tm * VStore) -> Prop :=
| st_varNone: forall n st,
  (exists e:tm, st (Id n) = Some e ) ->
  tvar None (Id n) / st ==> extract (st (Id n)) / st
| st_varLH: forall n st b,
  (exists e:tm, st (Id n) = Some e ) ->
  tvar (Some b) (Id n) / st ==> upgrade (extract (st (Id n))) b / st
| st_appabs: forall x T e b v st,
  value v ->
  tapp (tabs x T e b) v / st ==> upgrade ([x := v]e) b / st
| st_app1: forall t1 t1' t2 st,
  t1 / st ==> t1' / st ->
  tapp t1 t2 / st ==> tapp t1' t2 / st
| st_app2: forall v1 t2 t2' st,
  value v1 ->
  t2 / st ==> t2' / st ->
  tapp v1 t2 / st ==> tapp v1 t2' / st

where "t1 '/' st1 '==>' t2 '/' st2" := (step (t1,st1) (t2,st2)).


Definition multistep := (multi step).
Notation "t1 '/' st '==>*' t2 '/' st'" := (multistep (t1,st) (t2,st')) 
  (at level 40, st at level 39, t2 at level 39).

(*##############tests of [step_one]###########*)
Example test_step_one_a:
tapp (tabs (Id 0)(an_b int L)(tvar None (Id 0)) H)(tcon 1 L) / empty_store
==> tcon 1 H / empty_store.
Proof. apply st_appabs. apply v_c. Qed.
Example test_step_one_b:
tvar None (Id 0) / update empty_store (Id 0) (Some (tcon 1 H)) ==>
tcon 1 H / update empty_store (Id 0) (Some (tcon 1 H)).
Proof. apply st_varNone. exists (tcon 1 H). rewrite->update_eq.
       reflexivity. Qed.
Example test_step_one_c:
tvar (Some H) (Id 0) / update empty_store (Id 0) (Some (tcon 1 L)) ==>
tcon 1 H / update empty_store (Id 0) (Some (tcon 1 L)).
Proof. apply st_varLH. exists (tcon 1 L). apply update_eq.
       Qed.
Example test_step_one_d:
tapp (tabs (Id 0)(an_b int L)(tvar None (Id 0)) H)(tvar None (Id 0)) / update empty_store (Id 0) (Some (tcon 1 L))
==>* tcon 1 H / update empty_store (Id 0) (Some (tcon 1 L)).
Proof. apply multi_step with (y:= (tapp (tabs (Id 0)(an_b int L)(tvar None (Id 0)) H)(tcon 1 L) , update empty_store (Id 0) (Some (tcon 1 L)))).
 apply st_app2. apply v_f. apply st_varNone. exists (tcon 1 L). apply update_eq.
apply multi_step with (y:=(upgrade ([Id 0 := tcon 1 L](tvar None (Id 0))) H , update empty_store (Id 0) (Some (tcon 1 L)))).
apply st_appabs. apply v_c. simpl. apply multi_refl. Qed.
Example test_step_one_e:
tapp (
      tapp 
           (tabs (Id 1)(an_b int L)(tabs (Id 0)(an_b int L)(tvar None (Id 0)) L) H)
           (tcon 1 L) 
     )
     (
      tapp 
           (tabs (Id 0)(an_b int L)(tvar None (Id 0)) L)
           (tcon 1 L)
     ) / empty_store
==>* tcon 1 H / empty_store.
Proof. apply multi_step with (y:=(tapp (upgrade ([(Id 1) := tcon 1 L](tabs (Id 0)(an_b int L)(tvar None (Id 0)) L)) H)(tapp (tabs (Id 0)(an_b int L)(tvar None (Id 0)) L)(tcon 1 L)) , empty_store)).
apply st_app1. apply st_appabs. apply v_c. simpl.
apply multi_step with (y:= (tapp (tabs (Id 0)(an_b int L)(tvar None (Id 0)) H)(upgrade ([(Id 0) := tcon 1 L](tvar None (Id 0))) L) , empty_store)).
apply st_app2. apply v_f.  apply st_appabs. apply v_c. 
simpl.
apply multi_step with (y:= (tcon 1 H , empty_store)). apply st_appabs. apply v_c.
apply multi_refl.
Qed.
Example test_step_one_f:
tapp (tabs (Id 1)(an_b int H)(tabs (Id 0)(an_b int L)(tvar None (Id 0)) L) H)(tcon 1 H) / empty_store
==> tabs (Id 0)(an_b int L)(tvar None (Id 0)) H / empty_store.
Proof. apply st_appabs. apply v_c. Qed.


(*#################end########################*)

(*#####################end#####################################*)

(**
Intuitively, a subset of the terms in the language defined above should be 
able to be reduced to values as specified in [value] and they are of the following
two sorts,
a. constants
b. abstractions

a. tcon 1 H
b. tabs (Id 0) (an_b int H) (tvar None (Id 1)) H.
*)

(*
Note that the introduction of the additional argument in [tvar] is not
without a cost. Consider the following evaluation sequences,
**)
(*########a#########*)
Example counter_intuitive_a:
tapp (tabs (Id 1)(an_b int H)(tvar (Some H) (Id 0)) L) (tcon  1 H) 
/ update empty_store (Id 0) (Some (tcon 1 L))
(*==> tvar (Some H) (Id 0) / update empty_store (Id 0)(Some (tcon 1 L))*)
==>* tcon 1 H / update empty_store (Id 0)(Some (tcon 1 L)).
Proof. apply multi_step with (y:= (tvar (Some H)(Id 0),update empty_store (Id 0)(Some (tcon 1 L)))).
apply st_appabs. apply v_c. 
apply multi_step with (y:=(tcon 1 H , update empty_store (Id 0) (Some (tcon 1 L)))).
apply st_varLH. exists (tcon 1 L). apply update_eq. apply multi_refl.
Qed.
(*
ALthough the above reduction sequence is allowed by [step], it is counter 
intuitive to start off with a free variable where the additional argument is
not [None]**)
(*#######b########*)
Example counter_intuitive_b:
tapp (tabs (Id 0)(an_b int H)(tvar (Some H) (Id 0)) L) (tcon  1 H) 
/ empty_store
==> tcon 1 H / empty_store.
Proof. apply st_appabs. apply v_c. Qed.
(*
Again, if it is counter intuitive to start off with a bounded variable whose
additional argument is not [None]**)

(*####################Typing rules###########################*)
(**
In what follows, we will specify the typing rules of the system.
One intuitive way of doing it is that we suppose that before reduction,
we have a "typing context" as follows,
context := id -> option Ty which maps each free variable in the expression
to be reduced to a type.
In addition, we impose the following condition upon the typing context such that
the types of each free variable match these of the corresponding values,
store (Id n) : context (Id n)
We can call it consistancy condition.
Then we can have the following typing rules given a certain typing context
"Gamma",

a. t_varNone
 Gamma (Id n) = T
-------------------------------(t_varNone)
 Gamma |- tvar None (Id n) : T 

b. t_varLH
 Gamma (Id n) = T
-----------------------------------------(t_varLH)
 Gamma |- tvar (Some b) (Id n) : join T b 
where [join] standing for a function to change the security
label of type [T] such that it is at least as secure as [b]

c. t_con
 Gamma  |- (tcon n b) : int^b

d. t_abs
 update Gamma x T1 |- e : T2
------------------------------------(t_abs)
 Gamma |- tabs x T1 e b : (T1->T2)^b   

e. t_app
  Gamma |- t1 : (T1->T2)^b
  Gamma |- t2 : T1
----------------------------------(t_app)
  Gamma |- tapp t1 t2 : join T2 b

*)
(*############typing context############*)
Definition context := id -> option Ty.

Definition empty_context : context := 
  fun _ => None.
 
Definition Cupdate (St : context) (X:id) (T : option Ty) : context :=
  fun X' => if beq_id X X' then T else St X'.

(*#######some useful theorems regarding [update]#########*)
Theorem Cupdate_eq : forall T X St,
  (Cupdate St X T) X = T.
Proof.
intros. unfold Cupdate. rewrite<-beq_id_refl. reflexivity. 
Qed.
Theorem Cupdate_neq : forall X2 X1 T St,
  beq_id X2 X1 = false ->
  (Cupdate St X2 T) X1 = (St X1).
Proof.
intros. unfold Cupdate. rewrite H0. reflexivity.
Qed.
Theorem Cupdate_shadow : forall T1 T2 X1 X2 (f : context),
   (Cupdate  (Cupdate f X2 T1) X2 T2) X1 = (Cupdate f X2 T2) X1.
Proof.
intros. unfold Cupdate. destruct (beq_id X2 X1). reflexivity.
reflexivity.
Qed.
Theorem Cupdate_same : forall T1 X1 X2 (f : context),
  f X1 = T1 ->
  (Cupdate f X1 T1) X2 = f X2.
Proof.
intros. unfold Cupdate. remember (beq_id X1 X2) as D. destruct D.
Case ("true"). apply beq_id_eq in HeqD. subst. reflexivity.
reflexivity.
Qed. 
Theorem Cupdate_permute : forall T1 T2 X1 X2 X3 f,
  beq_id X2 X1 = false -> 
  (Cupdate (Cupdate f X2 T1) X1 T2) X3 = (Cupdate (Cupdate f X1 T2) X2 T1) X3.
Proof.
intros. unfold Cupdate. remember (beq_id X1 X3) as D1. remember (beq_id X2 X3) as D2.
destruct D1.
Case ("D1=true"). destruct D2.
      SCase ("D2=true"). apply beq_id_false_not_eq in H0.  apply beq_id_eq in HeqD1.
                         apply beq_id_eq in HeqD2. rewrite<-HeqD2 in HeqD1.
                         unfold not in H0. symmetry in HeqD1. apply H0 in HeqD1.
                         inversion HeqD1.
      SCase ("D2=false"). reflexivity.
Case ("D1=false"). destruct D2.
      SCase ("D2=true"). reflexivity.
      SCase ("D2=false"). reflexivity.
Qed.

(*###########################end######################*)
(*##########join#########*)
Definition join (T:Ty) (b:Sec): Ty :=
 match b with
 | L => T
 | H => match T with
        | an_b R b => an_b R H
        | an_f T1 T2 b => an_f T1 T2 H
        end
 end.
Example test_join_1:
 join (an_b int L) H = an_b int H.
Proof. simpl. reflexivity. Qed.
Example test_join_2:
 join (an_f (an_b int L)(an_b int L) L) H = an_f (an_b int L)(an_b int L) H.
Proof. simpl. reflexivity. Qed.
(*###########end#########*)
(*################end###################*)
Inductive has_type : context  -> tm -> Ty -> Prop :=
| t_varNone: forall Gamma n T,
  Gamma (Id n) = Some T ->
  has_type Gamma (tvar None (Id n)) T
| t_varLH: forall Gamma n T T' b,
  Gamma (Id n) = Some T ->
  join T b = T' ->
  has_type Gamma (tvar (Some b) (Id n)) T'
| t_con: forall Gamma n b,
  has_type Gamma (tcon n b) (an_b int b)
| t_abs: forall Gamma T1 T2 b e x,
  has_type (Cupdate Gamma x (Some T1)) e T2 ->
  has_type Gamma (tabs x T1 e b) (an_f T1 T2 b)
| t_app: forall Gamma T1 T2 T2' b t1 t2,
  has_type Gamma t1 (an_f T1 T2 b) ->
  has_type Gamma t2 T1 ->
  join T2 b = T2' ->
  has_type Gamma (tapp t1 t2) T2'.

(*#######some examples of well-typed expressions#############*)
Example has_type_a:
 has_type (Cupdate empty_context (Id 0) (Some (an_b int L))) 
          (tapp (tabs (Id 0)(an_b int L)(tvar None (Id 0)) H)(tvar None (Id 0)))
          (an_b int H).
Proof. apply t_app with (T1:=an_b int L)(T2:=an_b int L)(b:=H).
apply t_abs. apply t_varNone. rewrite->Cupdate_shadow. apply Cupdate_eq.
apply t_varNone. apply Cupdate_eq. simpl. reflexivity.
Qed.
Example has_type_b:
 has_type empty_context (tapp (tabs (Id 0)(an_b int L)(tvar None (Id 0)) H)(tcon 1 L)) (an_b int H).
Proof. apply t_app with (T1:=an_b int L)(T2:=an_b int L)(b:=H).
apply t_abs. apply t_varNone. apply Cupdate_eq. apply t_con.
reflexivity. Qed.
Example has_type_c:
 has_type (Cupdate empty_context (Id 0)(Some (an_b int H)))
          (tvar None (Id 0))
          (an_b int H).
Proof. apply t_varNone. apply Cupdate_eq. Qed.
Example has_type_d:
 has_type (Cupdate empty_context (Id 0)(Some (an_b int L)))
          (tvar (Some H) (Id 0))
          (an_b int H).
Proof. apply t_varLH with (T:= an_b int L). apply Cupdate_eq.
reflexivity. Qed.
Example has_type_e:
 has_type empty_context
         (tapp (
      tapp 
           (tabs (Id 1)(an_b int L)(tabs (Id 0)(an_b int L)(tvar None (Id 0)) L) H)
           (tcon 1 L) 
     )
     (
      tapp 
           (tabs (Id 0)(an_b int L)(tvar None (Id 0)) L)
           (tcon 1 L)
     ))
     (an_b int H).
Proof. apply t_app with (T1:=an_b int L)(T2:=an_b int L)(b:=H).
apply t_app with (T1:=an_b int L)(T2:=an_f (an_b int L)(an_b int L) L)(b:=H).
apply t_abs. apply t_abs. apply t_varNone. apply Cupdate_eq. apply t_con. reflexivity.
apply t_app with (T1:=an_b int L)(T2:=an_b int L)(b:=L). apply t_abs.
apply t_varNone. apply Cupdate_eq. apply t_con. reflexivity. reflexivity.
Qed.
Example has_type_f:
 has_type empty_context
          (tapp (tabs (Id 1)(an_b int H)(tabs (Id 0)(an_b int L)(tvar None (Id 0)) L) H)(tcon 1 H))
          (an_f (an_b int L)(an_b int L) H).
Proof. apply t_app with (T1:=an_b int H)(T2:=an_f (an_b int L)(an_b int L) L)(b:=H).
apply t_abs. apply t_abs. apply t_varNone. apply Cupdate_eq. apply t_con. reflexivity.
Qed.
Example has_type_g:
 has_type (Cupdate empty_context (Id 0) (Some (an_b int L)))
          (tapp (tabs (Id 1)(an_b int H)(tvar (Some H)(Id 0)) L)(tcon 1 H))
          (an_b int H).
Proof. apply t_app with (T1:=an_b int H)(T2:=an_b int H)(b:=L).
apply t_abs. apply t_varLH with (T:=an_b int L). 
assert (A:  beq_id (Id 0) (Id 1) = false ). reflexivity. 
apply Cupdate_permute with (f:=empty_context)(T1:=Some (an_b int L))(T2:=Some (an_b int H))(X3:=(Id 0)) in A.
rewrite->A. apply Cupdate_eq. reflexivity. apply t_con. reflexivity.
Qed.
Example has_type_h:
 has_type empty_context
          (tapp (tabs (Id 0)(an_b int L)(tvar (Some H) (Id 0)) L)(tcon 1 L))
          (an_b int H).
Proof. apply t_app with (T1:=an_b int L)(T2:= an_b int H)(b:=L).
apply t_abs. apply t_varLH with (T:=an_b int L). apply Cupdate_eq. reflexivity.
apply t_con. reflexivity. Qed.

(*############some counter examples##########*)
(**
Case 1: undefined free variables
*)
Example has_type_i:
 ~has_type empty_context
           (tvar None (Id 0))
           (an_b int L).
Proof. intros contra. inversion contra. inversion H2. Qed.
(**
Case 2: ill-typed abstractions whose body contains undefined
        free variables
*)
Example has_type_j:
~has_type empty_context
          (tabs (Id 0) (an_b int L)(tvar None (Id 1)) H)
          (an_f (an_b int L)(an_b int L) H).
Proof. intros contra. inversion contra. subst. inversion H2. 
       inversion H3. Qed.
(**
Case 3: ill-matched applications
*)
Example has_type_k:
~has_type empty_context
          (tapp (tabs (Id 0)(an_b int L)(tcon 2 L) H)(tcon 1 H))
          (an_b int H).
Proof. intros contra. inversion contra. subst. inversion H4. subst.
       inversion H2. Qed.

(**
Case 4: false applications
*)
Example has_type_l:
~has_type empty_context
          (tapp (tcon 1 H)(tcon 2 L))
          (an_b int L).
Proof. intros contra. inversion contra. inversion H2.
Qed.          
(*################end########################################*)

(*#########################end###############################*)





