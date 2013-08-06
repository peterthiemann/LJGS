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

(*security type*)
(**
Inductive RawTy' : Type :=
| int' : RawTy'
| fun' : Ty' -> Ty' -> Sec -> RawTy'
with Ty' : Type :=
| tann : RawTy' -> Sec -> Ty'.
*)

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
(**
Note the first argument is meant for
security updating
*)
(**Note that [Prot] should be used
   here to avoid writing [option Sec]
   explicitly by the programmer
*)
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
(*reduction stops at abstraction*) 

(**
Note that we can not say that all values in the language are 
closed terms for function body can contain "well defined" free 
variables and therefore it is not colsed.
*)

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
 match e , b with
  | e , L => e
  | tvar _ x , H => tvar (Some H) x
  | tcon n _ , H => tcon n H
  | tabs x T t _ , H => tabs x T t H
  | tapp f e , H => tapp (upgrade f H) e
 end.

(*#######tests of [update]##################*)
Example test_upgrade_0: forall e:tm,
 upgrade e L = e.
Proof. intros. destruct e. reflexivity.
reflexivity. reflexivity. reflexivity. Qed.
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
Example test_upgrade_10:
upgrade (tapp (tabs (Id 0)(an_b int L)(tvar None (Id 0)) L)(tcon 1 L)) H =
        tapp (tabs (Id 0)(an_b int L)(tvar None (Id 0)) H)(tcon 1 L).
Proof. simpl. reflexivity. Qed.
(*################end############################*)

Fixpoint subst (x:id) (s:tm) (t:tm): tm :=
  match t with
(*variables*)
  | tvar (Some b) x' => 
      if beq_id x x' then (upgrade s b) else t
  | tvar None x' =>
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
In what follows, "st" stands for the "value context" for all free variables
and all terms in the context are closed terms,
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

(**
Note the following block is about the specification of a function [closed]
which transforms abstractions into closed ones
*)
(*closed abstractions*)
(*###########################################*)
Definition Bregis:= id -> bool.

Definition empty_regis : Bregis := 
  fun _ => false.
 
Definition Bupdate (r : Bregis) (X:id): Bregis :=
  fun X' => if beq_id X X' then true else r X'.
(*#######some useful theorems regarding [Bupdate]#########*)
Theorem Bupdate_eq : forall X r,
  (Bupdate r X) X = true.
Proof.
intros. unfold Bupdate. rewrite<-beq_id_refl. reflexivity. 
Qed.
Theorem Bupdate_neq : forall X2 X1 r,
  beq_id X2 X1 = false ->
  (Bupdate r X2) X1 = (r X1).
Proof.
intros. unfold Bupdate. rewrite H0. reflexivity.
Qed.
Theorem Bupdate_shadow : forall x1 x2 (f : Bregis),
   (Bupdate  (Bupdate f x2) x2) x1 = (Bupdate f x2) x1.
Proof.
intros. unfold Bupdate. destruct (beq_id x2 x1). reflexivity.
reflexivity.
Qed.
Theorem Bupdate_same : forall x1 x2 (f : Bregis),
  f x1 = true ->
  (Bupdate f x1) x2 = f x2.
Proof.
intros. unfold Bupdate. remember (beq_id x1 x2) as D. destruct D.
Case ("true"). apply beq_id_eq in HeqD. subst. symmetry. apply H0.
reflexivity.
Qed. 
Theorem Bupdate_permute : forall x1 x2 x3 f,
  beq_id x2 x1 = false -> 
  (Bupdate (Bupdate f x2) x1) x3 = (Bupdate (Bupdate f x1) x2) x3.
Proof.
intros. unfold Bupdate. remember (beq_id x1 x3) as D1. remember (beq_id x2 x3) as D2.
destruct D1. destruct D2. reflexivity. reflexivity. reflexivity.
Qed.

(*###########################end######################*)
(**
The above definitions give us function which upon the variable id
tells us whether it is bounded or not.
For instance,
we have [Bupdate empty_regis (Id 0)] and a variable [tvar None (Id 0)],
since [Bupdate empty_regis (Id 0) (Id 0) = true] we know that this variable
is bounded
*)
(*the function*)
Fixpoint closed (r : Bregis) (t : tm) (st : VStore): tm :=
match t with
| tvar None x => if (r x) then (tvar None x) else (extract (st x))
| tvar (Some b) x => if (r x) then (tvar (Some b) x) else (upgrade (extract (st x)) b)
| tcon n b => tcon n b
| tabs x T e b => tabs x T (closed (Bupdate r x) e st) b
| tapp t1 t2 => tapp (closed r t1 st) (closed r t2 st)
end.
(*############some examples####################*)
Example test_closed_1:
closed empty_regis (tabs (Id 0) (an_b int H) (tvar None (Id 1)) H)
       (update empty_store (Id 1) (Some (tcon 1 L)))
= tabs (Id 0) (an_b int H) (tcon 1 L) H.
Proof. reflexivity. Qed.
Example test_closed_2:
closed empty_regis (tabs (Id 0) (an_b int H) (tvar (Some H) (Id 1)) H)
       (update empty_store (Id 1) (Some (tcon 1 L)))
= tabs (Id 0) (an_b int H) (tcon 1 H) H.
Proof. reflexivity. Qed.
Example test_closed_3:
closed empty_regis (tabs (Id 0)(an_b int H)(tabs (Id 1)(an_b int L)(tvar None (Id 1)) L) H)
       empty_store
= tabs (Id 0)(an_b int H)(tabs (Id 1)(an_b int L)(tvar None (Id 1)) L) H.
Proof.  reflexivity. Qed.
Example test_closed_4:
closed empty_regis (tabs (Id 0)(an_b int H)(tabs (Id 1)(an_b int L)(tvar None (Id 3)) L) H)
       (update empty_store (Id 3) (Some (tcon 1 L)))
= tabs (Id 0)(an_b int H)(tabs (Id 1)(an_b int L)(tcon 1 L) L) H.
Proof. reflexivity. Qed.
Example test_closed_5:
closed (Bupdate empty_regis (Id 0)) 
       (tapp (tabs (Id 1)(an_b int H)(tvar (Some L) (Id 1)) L)(tvar None (Id 0))) 
       empty_store
= tapp (tabs (Id 1)(an_b  int H)(tvar (Some L)(Id 1)) L)(tvar None (Id 0)).
Proof. simpl. reflexivity. Qed.
Example test_closed_6:
closed (Bupdate empty_regis (Id 0))
       (tapp (tabs (Id 1)(an_b int H)(tvar (Some H)(Id 1)) L)(tvar (Some H) (Id 1)))
       (update empty_store (Id 1) (Some (tcon 1 L)))
= tapp (tabs (Id 1)(an_b int H)(tvar (Some H)(Id 1)) L)(tcon 1 H).
Proof. reflexivity. Qed.
(**
[closed] is essentially a partial function in that it do not consider the case
where [st : VStore] is empty. Therefore it relies on the fact that the terms to
be applied to it is well-typed. This is problematic and should be dealt with
explicitly!
*)
(*###############end###########################*)
(*###########################################*)

Inductive step : (tm * VStore) -> (tm * VStore) -> Prop :=
| st_varNone: forall n st,
  (exists e:tm, st (Id n) = Some e ) ->
  tvar None (Id n) / st ==> extract (st (Id n)) / st
| st_varLH: forall n st b,
  (exists e:tm, st (Id n) = Some e ) ->
  tvar (Some b) (Id n) / st ==> upgrade (extract (st (Id n))) b / st
| st_appabs: forall x T e b v v' v'' st,
  value v ->
  v' = closed empty_regis v st ->
 (*substitution with closed terms*)
  v'' = upgrade ([x := v']e) b ->
  tapp (tabs x T e b) v / st ==> v'' / st
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
Proof. apply st_appabs with (v':=tcon 1 L). apply v_c. reflexivity.
reflexivity. Qed.
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
apply st_appabs with (v':=tcon 1 L). apply v_c. reflexivity. reflexivity. simpl. apply multi_refl. Qed.
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
apply st_app1. apply st_appabs with (v':=tcon 1 L). apply v_c. reflexivity. reflexivity. simpl.
apply multi_step with (y:= (tapp (tabs (Id 0)(an_b int L)(tvar None (Id 0)) H)(upgrade ([(Id 0) := tcon 1 L](tvar None (Id 0))) L) , empty_store)).
apply st_app2. apply v_f.  apply st_appabs with (v':= tcon 1 L). apply v_c. reflexivity. reflexivity. 
simpl.
apply multi_step with (y:= (tcon 1 H , empty_store)). apply st_appabs with (v':= tcon 1 L). apply v_c. reflexivity. reflexivity.
apply multi_refl.
Qed.
Example test_step_one_f:
tapp (tabs (Id 1)(an_b int H)(tabs (Id 0)(an_b int L)(tvar None (Id 0)) L) H)(tcon 1 H) / empty_store
==> tabs (Id 0)(an_b int L)(tvar None (Id 0)) H / empty_store.
Proof. apply st_appabs with (v':=tcon 1 H). apply v_c. reflexivity.
reflexivity. Qed.
Example test_step_one_g:
tapp (tabs (Id 0)(an_f (an_b int L)(an_b int L) L)(tvar None (Id 0)) H)
     (tabs (Id 0)(an_b int L)(tvar None (Id 0)) L) / empty_store
==> tabs (Id 0)(an_b int L)(tvar None (Id 0)) H / empty_store.
Proof. apply st_appabs with (v':=tabs (Id 0)(an_b int L)(tvar None (Id 0)) L).
apply v_f. reflexivity. reflexivity. Qed.
Example test_step_one_h:
tapp (tabs (Id 0)(an_f (an_b int L) (an_b int L) L)(tvar None (Id 0)) H)
     (tabs (Id 0) (an_b int L)(tvar None (Id 1)) L) / update empty_store (Id 1) (Some (tcon 1 L))
==> tabs (Id 0)(an_b int L)(tcon 1 L) H / update empty_store (Id 1) (Some (tcon 1 L)).
Proof. apply st_appabs with (v':=tabs (Id 0)(an_b int L)(tcon 1 L) L).
apply v_f. reflexivity. reflexivity. Qed.


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
apply st_appabs with (v':=tcon 1 H). apply v_c. reflexivity. reflexivity. 
apply multi_step with (y:=(tcon 1 H , update empty_store (Id 0) (Some (tcon 1 L)))).
apply st_varLH. exists (tcon 1 L). apply update_eq. apply multi_refl.
Qed.
(*
ALthough the above reduction sequence is allowed by [step], it is counter 
intuitive to start off with a free variable where the additional argument is
not [None]. If we introduce into the language [Prot] then we should not 
have this problem for we donot require programmer to write down explicitly the 
related label  
**)

(*#######b########*)
Example counter_intuitive_b:
tapp (tabs (Id 0)(an_b int H)(tvar (Some H) (Id 0)) L) (tcon  1 H) 
/ empty_store
==> tcon 1 H / empty_store.
Proof. apply st_appabs with (v':= tcon 1 H). apply v_c. reflexivity. reflexivity.
 Qed.
(*
Again, if it is counter intuitive to start off with a bounded variable whose
additional argument is not [None]**)
(*switch to [Prop]*)

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

(*######Properties########*)
(**
There are two important type safety properties we want to investigate,
a.Progress
 forall Gamma T t t' st, 
 has_type Gamma t T ->
 value t \/ exists t', t / st ==> t' / st
That is well-typed terms never get stuck

b. type preservation
 forall Gamma t t' st T,
 has_type Gamma t T ->
 t / st ==> t' / st ->
 has_type Gamma t' T
  
*)
(*############type preserversion############*)
(**
Consider the following reduction sequence,
tapp
(tabs (Id 1)(an_b int L)(tabs (Id 0)(an_b int L)(tvar None (Id 0)) L) H)
(tcon 1 L) / empty_store 
==>
tabs (Id 0)(an_b int L)(tvar None (Id 0)) H / empty_store
note that,
tabs (Id 0)(an_b int L)(tvar None (Id 0)) L
has type,
empty_context |- (int^L -> int^L)^L
which indicates that the body of the function is a closed term and
it can be typed under any typing context. This illustrates that in
our reduction sequence, the removal of lambda will not require the
expansion of the typing context we start with for the resulting term
is either closed or typable under the original typing context.

Now [Gamma : context] stands for the typing context for both free and 
bounded variables. Before the reduction of any term, it is actually the 
typing context for free-variables. It follows that the typing context  
has to meet the following condition,

a. at the beginning of the reduction, [Gamma] must indicate the types of
   its corresponding value context [st : store].

Now as reduction in progress, [Gamma] always stays the same for 
in our simple language we assume that we begin with a fixed set of 
free-variables whose values and types are not to be changed.
Therefore it is clear that if we begin with a perfectly related typing context
we will end up with the same typing context after reduction.

Clearly we should specify preservation as follows,
forall Gamma t t' st T,
store_well_typed Gamma st ->
has_type Gamma t T ->
t / st ==> t' / st ->
has_type Gamma t' T
)

*)

(**
Note to specify [type preservation] property we have to firstly
clarify what is [store_well_typed] as follows,

given [Gamma : context] and [st : VStore], if
forall n, 
(exists e:tm, st (Id n) = Some e) ->
has_type Gamma (extract (st (Id n))) (extract (Gamma (Id n)))
where [extract] is a function which gets rid of the label [Some].

Since we already have one such function [extract] to help in case
of value context, we specify a similar function in case of typing 
context as follows,
*)
Definition Cextract (T : option Ty) : Ty :=
match T with
| Some e => e
| None   => an_b int H
end.

Definition store_well_typed (Gamma:context) (st:VStore) :=
     forall n, (exists t:Ty, Gamma (Id n) = Some t) -> 
     (forall c, has_type c (extract (st (Id n))) (Cextract (Gamma (Id n)))).
(**
Note that since we assume that all values term in [st : VStore] must be
closed the typing of them is independent of any context
*)

(*####preservation theorem#######*)
(*#################auxiliary theorems##########*)
(*########################################*)
Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.
(*########################################*)
Theorem has_type_H: forall Gamma e T,
has_type Gamma e T ->
has_type Gamma (upgrade e H)(join T H).
Proof.
intros. induction H0. 
Case ("t_varNone").
simpl. apply t_varLH with (T:=T). apply H0.
reflexivity. 
Case ("t_varLH"). 
destruct T. destruct b. simpl in H1. rewrite<-H1.
simpl. apply t_varLH with (T:= an_b r s). apply H0. reflexivity.
simpl in H1. rewrite<-H1. simpl. apply t_varLH with (T:=an_b r s).
apply H0. reflexivity. destruct b. simpl in H1. rewrite<-H1. simpl.
apply t_varLH with (T:=an_f T1 T2 s). apply H0. reflexivity.
simpl in H1. rewrite<-H1. simpl. apply t_varLH with (T:=an_f T1 T2 s).
apply H0. reflexivity.
Case ("t_con").
simpl. apply t_con.
Case ("t_abs").
simpl. apply t_abs. apply H0.
Case ("t_app").
destruct b. destruct T2.  simpl in H0. rewrite<-H0. simpl.
simpl in IHhas_type1. apply t_app with (T1:=T1)(T2:=an_b r s)(b:=H).
apply IHhas_type1. apply H0_0. reflexivity. simpl in H0.
rewrite<-H0. simpl. simpl in IHhas_type1.
apply t_app with (T1:=T1)(T2:=an_f T2_1 T2_2 s)(b:=H). apply IHhas_type1.
apply H0_0. reflexivity. destruct T2. simpl in H0. rewrite<-H0. simpl.
simpl in IHhas_type1. apply t_app with (T1:=T1)(T2:=an_b r s)(b:=H).
apply IHhas_type1. apply H0_0. reflexivity. simpl in H0. rewrite<-H0. simpl.
simpl in IHhas_type1. apply t_app with (T1:=T1)(T2:=an_f T2_1 T2_2 s)(b:=H).
apply IHhas_type1. apply H0_0. reflexivity.
Qed.
  
(*##########s_p_t_1##############*)
(*Firstly we use the following proposition to describe free variables*)
Inductive free_var : id -> tm -> Prop :=
| e_tvar : forall x l,
      free_var x (tvar l x)
| e_tapp1 : forall x e1 e2,
      free_var x e1 ->
      free_var x (tapp e1 e2)
| e_tapp2 : forall x e1 e2,
      free_var x e2 ->
      free_var x (tapp e1 e2)
| e_tabs : forall x y e T b,
      y <> x ->
      free_var x e ->
      free_var x (tabs y T e b).
(*some examples*)
Example test_free_var_1:
free_var (Id 0) (tvar None (Id 0)).
Proof. apply e_tvar. Qed.
Example test_free_var_2:
free_var (Id 0) (tvar (Some H) (Id 0)).
Proof. apply e_tvar. Qed.
Example test_free_var_3:
free_var (Id 1) (tapp (tabs (Id 0)(an_b int L)(tvar None (Id 0)) L)(tvar None (Id 1))) .
Proof. apply e_tapp2. apply e_tvar. Qed.
Example test_free_var_4:
free_var (Id 1)(tabs (Id 0)(an_b int L)(tvar None (Id 1)) L).
Proof. apply e_tabs. intros contra. inversion contra. apply e_tvar. Qed.
Example test_free_var_5:
forall x n b, ~free_var x (tcon n b).
Proof. intros. intros contra. inversion contra. Qed.
Example test_free_var_6:
forall x T e b,~free_var x (tabs x T e b).
Proof. intros. intros contra. inversion contra. subst. apply H3. reflexivity.
Qed.
(*some auxiliary lemmas*)
Theorem beq_id_eq : forall i1 i2,
  true = beq_id i1 i2 -> i1 = i2.
Proof. 
intros. unfold beq_id in H0. destruct i1. destruct i2. symmetry in H0.
apply beq_nat_true in H0. subst. reflexivity.
Qed.  
Theorem not_eq_beq_id_false : forall i1 i2,
  i1 <> i2 -> beq_id i1 i2 = false.
Proof. 
intros. unfold beq_id. destruct i1. destruct i2.  apply beq_nat_false_iff.
intros C. apply H0. subst. reflexivity.
Qed.
Theorem beq_id_refl : forall X,
  true = beq_id X X.
Proof.
  intros. destruct X.
  apply beq_nat_refl.  Qed.
(*end*)
(*####any_term_typable_under_empty context is closed####*)
Lemma term_typable_empty_closed_1:forall x t T Gamma,
free_var x t ->
has_type Gamma t T ->
exists T',Gamma x = Some T'.
Proof. intros. generalize dependent T. generalize dependent Gamma.
induction H0. 
intros. inversion H1. subst. exists T. apply H5. subst. exists T0.
        apply H4.
intros. inversion H1. subst. apply IHfree_var with (T:=an_f T1 T2 b).
        apply H4.
intros.  inversion H1. subst. apply IHfree_var with (T:=T1).
        apply H6.
intros. inversion H2. subst. apply IHfree_var in H9.  apply not_eq_beq_id_false in H0.
        apply Cupdate_neq with (T:=Some T)(St:=Gamma) in H0. rewrite->H0 in H9.
        apply H9.
Qed.




Corollary term_typable_empty_closed: forall t T,
has_type empty t T ->
forall x, ~free_var x t.
Proof. intros t. induction t.
intros. intros contra. inversion H0. subst. inversion H5. subst. inversion H4.
intros. intros contra. inversion contra. 
intros. intros contra. apply term_typable_empty_closed_1 with (T:=T)(Gamma:=empty)in contra .
        inversion contra. inversion H1. apply H0.
intros. inversion H0. subst. intros contra. inversion contra.  subst. apply IHt1 with (x:=x)in H3.
        apply H3 in H4. inversion H4. subst. apply IHt2 with (x:=x) in H5.
        apply H5 in H4. inversion H4.
Qed.

Corollary change_context: forall Gamma Gamma' t T,
has_type Gamma t T ->
(forall x, free_var x t -> Gamma x = Gamma' x) ->
has_type Gamma' t T.
Proof.
intros. generalize dependent Gamma'. induction H0.
intros. apply t_varNone. rewrite<-H0. symmetry. apply H1.
apply e_tvar.
intros. apply t_varLH with (T:=T). rewrite<-H0. symmetry. apply H2.
apply e_tvar. apply H1.
intros. apply t_con.
intros. apply t_abs. apply IHhas_type. intros. remember (beq_id x x0) as BB.
        destruct BB.  apply beq_id_eq in HeqBB. rewrite->HeqBB. rewrite->Cupdate_eq.
        rewrite->Cupdate_eq. reflexivity. inversion HeqBB. symmetry in H4.
        apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in H4. rewrite->H4.
        inversion HeqBB. symmetry in H5. apply Cupdate_neq with (T:=Some T1)(St:=Gamma') in H5.
        rewrite->H5. clear H4. clear H5. apply H1. apply e_tabs. intros contra. rewrite->contra in HeqBB.
        rewrite<-beq_id_refl in HeqBB. inversion HeqBB. apply H2.
intros. apply t_app with (T1:=T1)(T2:=T2)(b:=b). apply IHhas_type1. intros. apply H1. apply e_tapp1.
        apply H2. apply IHhas_type2. intros. apply H1. apply e_tapp2. apply H2.
        apply H0.
Qed.

Theorem s_p_t_1: forall t Gamma T,
has_type empty_context t T ->
has_type Gamma t T.
Proof. intros. apply change_context with (Gamma':=Gamma)in H0.
      apply H0. intros. apply term_typable_empty_closed with (x:=x)in H0.
      apply H0 in H1.  inversion H1.
Qed.

(*################s_p_t_1################*)
Theorem substitution_preserves_typing: forall Gamma x t2 T1 T2 e,
has_type empty_context t2 T1 ->
has_type (Cupdate Gamma x (Some T1)) e T2 ->
has_type Gamma ([x := t2]e) T2.
Proof. intros. generalize dependent Gamma. generalize dependent x.
generalize dependent t2. generalize dependent T1. generalize dependent
T2. induction e.
Case ("tvar").
intros. inversion H1. subst. simpl. remember (beq_id x (Id n)) as BB.
destruct BB. apply beq_id_eq in HeqBB. rewrite->HeqBB in H6.
rewrite->Cupdate_eq in H6. inversion H6. subst. apply s_p_t_1. apply H0.
symmetry in HeqBB. apply Cupdate_neq with (T:=Some T1)(St:=Gamma)in HeqBB.
rewrite->HeqBB in H6. apply t_varNone. apply H6. subst. simpl.
remember (beq_id x (Id n)) as BB. destruct BB. apply beq_id_eq in HeqBB.
rewrite->HeqBB in H5. rewrite->Cupdate_eq in H5. inversion H5. subst.
destruct b. simpl. assert (A: forall e, upgrade e L = e). apply test_upgrade_0.
specialize (A t2).  rewrite->A. clear A. apply s_p_t_1. apply H0.
apply has_type_H. apply s_p_t_1. apply H0. symmetry in HeqBB. 
apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in HeqBB. rewrite->HeqBB in H5.
apply t_varLH with (T:=T).  apply H5. reflexivity.
Case ("tcon").
intros. simpl. inversion H1. subst. apply t_con.
Case ("tabs").
intros. simpl. remember (beq_id x i) as BB. destruct BB. inversion H1.
subst. apply t_abs. apply beq_id_eq in HeqBB. rewrite->HeqBB in H8.
assert (Cupdate Gamma i (Some t) = Cupdate (Cupdate Gamma i (Some T1)) i (Some t)).
apply functional_extensionality. intros. remember (beq_id i x0) as CC. destruct CC.
apply beq_id_eq in HeqCC. rewrite->HeqCC. rewrite->Cupdate_eq.
rewrite->Cupdate_eq. reflexivity. symmetry in HeqCC. inversion HeqCC. inversion HeqCC.
apply Cupdate_neq with (T:= Some t)(St:=Gamma ) in HeqCC. rewrite->HeqCC. 
apply Cupdate_neq with (T:= Some t)(St:=Cupdate Gamma i (Some T1)) in H3.
rewrite->H3. apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in H4. rewrite->H4.
reflexivity. rewrite->H2. apply H8. inversion H1. subst. apply t_abs.
apply IHe with (T1:=T1). apply H0. 
assert (Cupdate (Cupdate Gamma x (Some T1)) i (Some t) = Cupdate (Cupdate Gamma i (Some t)) x (Some T1)).
apply functional_extensionality. intros. remember (beq_id x x0) as AA.
remember (beq_id i x0) as BB. destruct AA. destruct BB. apply beq_id_eq in HeqAA.
apply beq_id_eq in HeqBB0. rewrite->HeqAA in HeqBB. rewrite->HeqBB0 in HeqBB.
rewrite<-beq_id_refl in HeqBB. inversion HeqBB. apply beq_id_eq in HeqAA. rewrite->HeqAA.
rewrite->Cupdate_eq. rewrite->HeqAA in HeqBB. symmetry in HeqBB. apply Cupdate_permute with (T1:=Some T1)(T2:=Some t)(X3:=x0)(f:=Gamma) in HeqBB.
rewrite->HeqBB. rewrite->Cupdate_eq. reflexivity. destruct BB. apply beq_id_eq in HeqBB0. rewrite->HeqBB0. rewrite->Cupdate_eq.
symmetry in HeqAA. apply Cupdate_permute with (T1:=Some T1)(T2:=Some t)(X3:=x0)(f:=Gamma) in HeqAA.
rewrite<-HeqAA. rewrite->Cupdate_eq. reflexivity. symmetry in HeqBB0. inversion HeqBB0.
apply Cupdate_neq with (T:=Some t)(St:=Cupdate Gamma x (Some T1))in HeqBB0.
rewrite->HeqBB0. symmetry in HeqAA. inversion HeqAA.
 apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in HeqAA.
rewrite->HeqAA. apply Cupdate_neq with (T:=Some T1)(St:=Cupdate Gamma i (Some t)) in H4.
rewrite->H4. apply Cupdate_neq with (T:=Some t)(St:=Gamma) in H3. rewrite->H3. reflexivity.
rewrite<-H2. apply H8.
Case ("tapp").
intros. simpl. inversion H1. subst. apply t_app with (T1:=T0)(T2:=T3)(b:=b).
apply IHe1 with (T1:=T1). apply H0. apply H4. apply IHe2 with (T1:=T1). apply H0.
apply H6. reflexivity.
Qed.

(**
Note that if we specify the theorem in the following way then we would
have problems in the proof for we assume that before the substitution
the value term used to replace the bounded variable is always closed,

Theorem substitution_preserves_typing': forall Gamma x t2 T1 T2 e,
has_type empty_context t2 T1 ->
has_type (Cupdate Gamma x (Some T1)) e T2 ->
has_type Gamma ([x:=t2]e) T2.

It seems to be a overly restrictive assumption consider the following case,
tapp 
(tabs (Id 0) (an_f (an_b int L)(an_b int L) L)(tvar None (Id 0)) H)
(tabs (Id 0)(an_b int L)(tvar None (Id 1)) L)
where
[tabs (Id 0)(an_b int L)(tvar None (Id 1)) L] is not a closed term although
it is a value.

However we know that if we start with a well-typed term then 
[tabs (Id 0)(an_b int L)(tvar None (Id 1)) L] must be well typed and can be
"reduced" to a closed term for we can replace the free variable with its value
which is supposed to be a closed term. 

*) 

Lemma preservation_1_1:forall e Gamma st i  T1 T2,
has_type (Cupdate Gamma i (Some T1)) e T2 ->
store_well_typed Gamma st ->
has_type (Cupdate empty_context i (Some T1)) (closed (Bupdate empty_regis i) e st) T2.
Proof. intros e. induction e.
Case ("tvar").
intros. inversion H0. subst. simpl. remember (beq_id i0 (Id n)) as BB. destruct BB.
apply beq_id_eq in HeqBB. rewrite->HeqBB. rewrite->Bupdate_eq. apply t_varNone.
rewrite->Cupdate_eq. rewrite->HeqBB in H6. rewrite->Cupdate_eq in H6. apply H6.
symmetry in HeqBB. inversion HeqBB. apply Bupdate_neq with (r:=empty_regis) in HeqBB. rewrite->HeqBB.
simpl.  assert (A: T2 = Cextract (Cupdate Gamma i0 (Some T1) (Id n))). rewrite->H6. reflexivity.
rewrite->A. clear A. apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in H3.
rewrite->H3. specialize (H1 n). apply H1. exists T2. rewrite->H3 in H6. apply H6.
subst. simpl.  remember (beq_id i0 (Id n)) as BB. destruct BB.
apply beq_id_eq in HeqBB. rewrite->HeqBB. rewrite->Bupdate_eq. apply t_varLH with (T:=T).
rewrite->Cupdate_eq. rewrite->HeqBB in H5. rewrite->Cupdate_eq in H5. apply H5. reflexivity.
symmetry in HeqBB. inversion HeqBB. apply Bupdate_neq with (r:=empty_regis) in HeqBB. rewrite->HeqBB.
simpl. destruct b. simpl.  assert (A: T = Cextract (Cupdate Gamma i0 (Some T1) (Id n))). rewrite->H5. reflexivity.
rewrite->A. clear A. apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in H3.
rewrite->H3. specialize (H1 n). assert (A: forall e, upgrade e L = e). apply test_upgrade_0.
specialize (A (extract (st (Id n)))). rewrite->A. clear A.
apply H1. exists T. rewrite->H3 in H5. apply H5. apply has_type_H.
assert (A: T = Cextract (Cupdate Gamma i0 (Some T1) (Id n))). rewrite->H5. reflexivity.
rewrite->A. clear A. apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in H3. rewrite->H3.
specialize (H1 n). apply H1. exists T. rewrite->H3 in H5. apply H5.
Case ("tcon"). 
intros. inversion H0. subst. simpl. apply t_con.
Case ("tabs"). 
admit. (*stuck here*) 
Case ("tapp"). 
intros. inversion H0. subst. simpl. apply t_app with (T1:=T0)(T2:=T3)(b:=b).
apply IHe1 with (Gamma:=Gamma). apply H4. apply H1. apply IHe2 with (Gamma:=Gamma).
apply H6. apply H1. reflexivity.
Qed.










Lemma preservation_1: forall t Gamma st T,
store_well_typed Gamma st ->
value t ->
has_type Gamma t T ->
has_type empty_context (closed empty_regis t st) T.
Proof. intros t. induction t.
Case ("tvar"). intros. inversion H1.
Case ("tcon"). intros. simpl. inversion H2. subst. apply t_con.
Case ("tabs"). intros. simpl. inversion H2. subst. apply t_abs.
               apply preservation_1_1 with (st:=st) in H9. apply H9.
               apply H0. 
Case ("tapp"). intros. inversion H1. 
Qed.



(*#######################end###################*)
Theorem preservation: forall Gamma t t' st T,
store_well_typed Gamma st ->
has_type Gamma t T ->
t / st ==> t' / st ->
has_type Gamma t' T.
Proof. intros. generalize dependent t'. generalize dependent st.
induction H1.
Case ("t_varNone"). intros. inversion H2. subst.
assert (A: T = Cextract (Gamma (Id n))). rewrite->H0. reflexivity.
rewrite->A. clear A. specialize (H1 n). apply H1. apply H4.
Case ("t_varLH"). intros. inversion H3. subst.
assert (A: T = Cextract (Gamma (Id n))). rewrite->H0. reflexivity.
rewrite->A. clear A. specialize (H2 n). apply H2 with (c:=Gamma)in H5. destruct b.
simpl. assert (A: forall e, upgrade e L = e). apply test_upgrade_0.
specialize (A (extract (st (Id n)))). rewrite->A. clear A. apply H5.
apply has_type_H. apply H5.
Case ("t_con"). intros. inversion H2.
Case ("t_abs"). intros. inversion H2.
Case ("t_app"). intros. inversion H2. subst. inversion H1_. subst.
                destruct b. assert (A: forall e, upgrade e L = e).
                apply test_upgrade_0. specialize (A ([x := closed empty_regis t2 st]e)).
                rewrite->A. clear A. simpl. 
                apply substitution_preserves_typing with (T1:=T1).
                assert (A: has_type Gamma t2 T1 -> has_type empty_context (closed empty_regis t2 st) T1).
                (*#proof of A#*)
                intros. induction t2. inversion H7. simpl. inversion H0. subst. apply t_con.
                inversion H0. subst. simpl. apply t_abs.
                (*#end of proof A#*)
               



                apply A. apply H1_0. 


                apply H4. apply has_type_H.
                apply substitution_preserves_typing with (T1:=T1).
                assert (A: has_type Gamma t2 T1 -> has_type empty_context (closed empty_regis t2 st) T1).
                admit. apply A. 
                apply H1_0. apply H4. 
                subst. apply t_app with (T1:=T1)(T2:=T2)(b:=b).
                apply IHhas_type1 with (t':=t1')in H1. apply H1.
                apply H4. apply H1_0. reflexivity. subst.
                apply t_app with (T1:=T1)(T2:=T2)(b:=b). apply H1_.
                apply IHhas_type2 with (t':=t2') in H1. apply H1.
                apply H8. reflexivity.
Qed.


(*############end################*)
(*##############end#########################*)

(*###########end##########*)



