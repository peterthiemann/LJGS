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
   ==> join H y
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
   reduction stops at abstraction only when the body of the 
   abstraction itself is a value
*)

Inductive value : tm -> Prop :=
| v_v : forall n o,
        value (tvar  o (Id n))
| v_c : forall b n,
        value (tcon n b)
| v_f : forall n T e b,
        value e ->
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

Fixpoint update (e:tm) (b:Sec): tm :=
 match b with
 | L => e
 | H => match e with
        | tvar _ x => tvar (Some H) x
        | tcon n _ => tcon n H
        | tabs x T t _ => tabs x T t H
        | tapp f e => tapp (update f H) e
        end
 end.

(*#######tests of [update]##################*)
Example test_update_1:
update (tvar None (Id 0)) H = tvar (Some H) (Id 0).
Proof. simpl. reflexivity. Qed.
Example test_update_2:
update (tvar (Some L) (Id 0)) H = tvar (Some H) (Id 0).
Proof. simpl. reflexivity. Qed.
Example test_update_3:
update (tvar None (Id 0)) L = tvar None (Id 0).
Proof. simpl. reflexivity. Qed.
Example test_update_4:
update (tcon 1 L) H = tcon 1 H.
Proof. simpl. reflexivity. Qed.
Example test_update_5:
update (tcon 1 L) L = tcon 1 L.
Proof. simpl. reflexivity. Qed.
Example test_update_6:
update (tabs (Id 0) (an_b int H) (tvar None (Id 0)) L) H = tabs (Id 0) (an_b int H) (tvar None (Id 0)) H.
Proof. simpl. reflexivity. Qed.
Example test_update_7:
update (tabs (Id 0) (an_b int H) (tvar None (Id 0)) L) L = tabs (Id 0) (an_b int H) (tvar None (Id 0)) L.
Proof. simpl. reflexivity. Qed.
Example test_update_8:
update (tapp (tabs (Id 0) (an_b int L) (tvar None (Id 0)) L) (tcon 1 L)) H =
        tapp (tabs (Id 0) (an_b int L) (tvar None (Id 0)) H) (tcon 1 L).
Proof. simpl. reflexivity. Qed.
Example test_updaet_9:
update (tapp (tabs (Id 0) (an_b int L) (tvar None (Id 0)) L)(tcon 1 L)) L =
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
Inductive step_one : tm -> tm -> Prop :=
  | st_appabs : forall n T e b v2,
    value v2 ->
    value e  ->
    tapp (tabs (Id n) T e b) v2 ==> update ([(Id n) := v2]e) b
  | st_app1 : forall t1 t1' t2,
        t1 ==> t1' ->
        tapp t1 t2 ==> tapp t1' t2
  | st_app2 : forall v1 t2 t2',
        value v1 ->                      
        t2 ==> t2' ->
        tapp v1 t2 ==> tapp v1 t2'

  where " t '==>' t' " := (step_one t t').

Definition multistep := multi step_one.
Notation " t '==>*' t' " := (multistep t t') (at level 40).

(*##############tests of [step_one]###########*)
Example test_step_one_a:
tapp (tabs (Id 0)(an_b int L)(tvar None (Id 0)) H)(tcon 1 L)
==> tcon 1 H.
Proof. apply st_appabs. apply v_c. apply v_v. Qed.
Example test_step_one_b:
tapp (tabs (Id 0)(an_b int L)(tvar None (Id 0)) H)(tvar None (Id 0))
==> tvar (Some H) (Id 0).
Proof. apply st_appabs. apply v_v. apply v_v. Qed.
Example test_st_one_c:
tapp (
      tapp 
           (tabs (Id 1)(an_b int L)(tabs (Id 0)(an_b int L)(tvar None (Id 0)) L) H)
           (tcon 1 L) 
     )
     (
      tapp 
           (tabs (Id 0)(an_b int L)(tvar None (Id 0)) L)
           (tcon 1 L)
     )
==>* tcon 1 H.
Proof. apply multi_step with (y:=tapp (update ([(Id 1) := tcon 1 L](tabs (Id 0)(an_b int L)(tvar None (Id 0)) L)) H) (tapp (tabs (Id 0)(an_b int L)(tvar None (Id 0)) L)(tcon 1 L))).
apply st_app1. apply st_appabs. apply v_c. apply v_f. apply v_v.
simpl.
apply multi_step with (y:= tapp (tabs (Id 0)(an_b int L)(tvar None (Id 0)) H)(update ([(Id 0) := tcon 1 L](tvar None (Id 0))) L)).
apply st_app2. apply v_f. apply v_v. apply st_appabs. apply v_c. apply v_v.
simpl.
apply multi_step with (y:=tcon 1 H). apply st_appabs. apply v_c.
apply v_v. apply multi_refl.
Qed.

(*#################end########################*)

(*#####################end#####################################*)

(**
Intuitively, a subset of the terms in the language defined above should be 
able to be reduced to values as specified in [value] and they are of the following
three sorts,
a. free-variables
b. constants
c. functions whose body is a value,

a. tvar (Some H) (Id 0)
b. tcon 1 H
c. tabs (Id 0) (an_b int H) (tvar None (Id 0)) H.

In what follows, we will further reduce these value terms to 
the "target" terms we want to have in the first place, which implies that,
1. we have to define "target" terms and their types
2. we have to specify a value context where the corresponding terms of the free
   variables are stored
3. reduce all constants and all free-variables to their corresponding "target"
   terms.
*)






(**
Now we have to define a "typing context" which is essentially a list of length n
whose elements are security types specified above.
Since the length of the list has to be considered together with the type of the 
list, we cannot specify it in Coq as a list type. For the way how type is defined
in Coq does not provide us with such alternative. 
Instead we specify it as a proposition, 
*)
Inductive Ctxt : nat -> Prop :=
| c_nil  : Ctxt 0
| c_cons : forall {n : nat}, Ty -> Ctxt n -> Ctxt (S n).  

(**
Let us consider the following cases to be sure that we successfully 
establishes the right correspondance between the proof object standing for
our typing environment and the proposition which standing for the type of
the context,
a. c_nil : Ctxt 0
b. c_cons (an_b int L) c_nil : Ctxt 1
c. c_cons (an_b int H) (c_cons (an_b int L) c_nil) : Ctxt 2
d. c_cons (an_f (an_b int L)(an_b int H)H) (c_cons (an_b int H) (c_cons (an_b int L) c_nil))
*)
Example test_Ctxt_1 : 
Ctxt 0.
Proof. apply c_nil.
Example test_Ctxt_2 :
Ctxt 1.
Proof. apply (c_cons (an_b int L) c_nil).
Example test_Ctxt_3 :
Ctxt 2.
Proof. apply (c_cons (an_b int H) (c_cons (an_b int L) c_nil)).
Example test_Ctxt_4 :
Ctxt 3.
Proof. apply (
c_cons (an_f (an_b int L) (an_b int H) H) 
(
c_cons (an_b int H)
(
c_cons (an_b int L) c_nil
)
)
).


(*########################################################*)
(*note that the above section needs to be modified*)
(*########################################################*)


(*security types for values*)
(*firstly we define a "ground type" named "N"*)
Inductive gTy : Type :=
| N : gTy.

(*then we define the "high-level type" called "hTy"*)
Inductive hTy : Type :=
| High  : gTy -> hTy
| Low   : gTy -> hTy
| FHigh : hTy -> hTy -> hTy
| FLow  : hTy -> hTy -> hTy.
(**
Some examples of our security types above in terms of the high-level form,
a. int^L
   Low N
b. int^H
   High N
c. (int^L -> int^H)^H
   FHigh (Low N) (High N)
d. (int^H -> int^L)^L
   FLow  (High N) (Low N)
*)
Check (High N).
Check (Low N).
Check (FHigh (Low N)(High N)).
Check (FLow (High N)(Low N)).

(**
Now we can define the terms of the system
*)
Inductive tm : Type :=
| tvar   : nat -> tm
| tconst : Sec -> nat -> tm
| tabs   : Sec -> nat -> hTy -> tm -> tm
| tapp   : tm -> tm -> tm.
(**
Consider the following terms,
a. tvar 1
note that in case of variable,tvar n, n indicates
the corresponding place in the typing context where
the type of the variable is stored
*)

















