

Require Export Ch10_Smallstep.


Inductive Sec : Type :=
| L : Sec
| H : Sec.

Inductive Ty : Type :=
| an : RawTy -> Sec -> Ty
with RawTy : Type :=
     | int : RawTy
     | fn  : Ty -> Ty -> RawTy.

Scheme Ty_mut := Induction for Ty Sort Prop
with RawTy_ := Induction for RawTy Sort Prop.

Check (an int H).
Check (an int L).
Check (an (fn (an int L)(an int H)) L).
Check (an (fn (an int H)(an int H)) H).
Check (an (fn (an int H)(an (fn (an int H)(an int H)) H)) H).
Check (an (fn (an (fn (an int H)(an int H)) H)(an int L)) L).

(*############subtyping#################*)
Inductive subsum_r : Sec -> Sec -> Prop :=
| sub_refl: forall b : Sec, 
          subsum_r b b
| sub_LH: subsum_r L H
.

Lemma subsum_r_trans: forall a b c,
subsum_r a b ->
subsum_r b c ->
subsum_r a c.
Proof. intros. inversion H0. subst. inversion H1. subst.
       apply sub_refl. apply sub_LH. destruct c. apply sub_refl.
       apply sub_LH.
Qed.

Example test_subsum_r_1:
subsum_r L L.
Proof. apply sub_refl. Qed.
Example test_subsum_r_2:
subsum_r H H.
Proof. apply sub_refl. Qed.
Example test_subsum_r_3:
subsum_r L H.
Proof. apply sub_LH. Qed.


Inductive subtyping : Ty -> Ty -> Prop :=
| subt_int: forall b b',
           subsum_r b b' -> 
           (an int b) < (an int b')
| subt_fn: forall b b' T1 T1' T2 T2',
           subsum_r b b' ->
           T1' < T1 ->
           T2 < T2' ->
           (an (fn T1 T2) b) < (an (fn T1' T2') b')
where "t1  '<' t2" := (subtyping t1 t2).

Lemma subtyping_refl: forall T,
T < T.
Proof. apply (Ty_mut (fun T => T < T) (fun RT => forall b, (an RT b) < (an RT b))).
intros. apply H0.
intros. apply subt_int. apply sub_refl.
intros. apply subt_fn. apply sub_refl. apply H0. apply H1. 
Qed. 
       

Lemma subtyping_trans: forall y z x z',
x < y -> z < x -> y < z' ->  z < z'.
Proof. intros.  generalize dependent z. generalize dependent z'. induction H0.
       intros.
       inversion H2. subst. inversion H1. subst. apply subt_int.  apply subsum_r_trans with (a:=b0)(b:=b)(c:=b')in H6.
       apply subsum_r_trans with (a:=b0)(b:=b')(c:=b'0) in H6. apply H6. apply H4. apply H0. 
       intros. inversion H1. subst. inversion H2. subst. 
       apply subt_fn. apply subsum_r_trans with (a:=b0)(b:=b)(c:=b') in H7.
       apply subsum_r_trans with (a:=b0)(b:=b')(c:=b'0) in H7. apply H7. apply H6. apply H0.
       apply IHsubtyping1. apply H8. apply H11.
       apply IHsubtyping2. apply H12. apply H9.
Qed.
      
Example apply_trans: forall x y z,
x < y -> y < z -> x < z.
Proof. intros. apply subtyping_trans with (x:=y)(y:=y).  apply subtyping_refl.
        apply H0. apply H1. Qed.      
         
(*####some tests of [subtyping]########*)     
Example test_subtyping_1:
subtyping (an int L)(an int L).
Proof.  apply subt_int. apply sub_refl. Qed.
Example test_subtyping_2:
~subtyping (an int H)(an int L).
Proof. intros contra. inversion contra. subst. inversion H2. Qed.
Example test_subtyping_3:
subtyping (an (fn (an int H)(an int L)) L)(an (fn (an int L)(an int H)) H).
Proof. apply subt_fn. apply sub_LH. apply subt_int. apply sub_LH. apply subt_int. apply sub_LH.
Qed.
Example test_subtyping_4:
~subtyping (an int L) (an (fn (an int H)(an int H)) H).
Proof. intros contra. inversion contra. Qed.
Example test_subtyping_5:
~subtyping (an (fn (an int L)(an int H)) H)(an int L).
Proof. intros contra. inversion contra. Qed.
Example test_subtyping_6:
subtyping (an (fn (an int H)(an int L)) L)(an (fn (an int L)(an int L)) L).
Proof. apply subt_fn. apply sub_refl. apply subt_int.
       apply sub_LH. apply subt_int. apply sub_refl. 
       Qed.
Example test_subtyping_7:
subtyping (an int L)(an int H).
Proof. apply subt_int. apply sub_LH. Qed.
Example test_subtyping_8:
subtyping (an (fn (an int H)(an int L)) L)(an (fn (an int H)(an int H)) H).
Proof. apply subt_fn. apply sub_LH. apply subt_int.
       apply sub_refl. apply subt_int. apply sub_LH. 
       Qed.
Example test_subtyping_9:
~subtyping (an (fn(an int H)(an int H)) H)(an (fn(an int H)(an int L)) L).
Proof. intros contra. inversion contra. subst. inversion H4. Qed.
Example test_subtyping_10:
~subtyping (an (fn (an int L)(an int L)) L)(an (fn (an int H)(an int H)) H).
Proof. intros contra. inversion contra. subst. inversion H7. inversion H2. Qed. 
Example test_subtyping_11:
subtyping (an (fn (an int L)(an int L)) L)(an (fn (an int L)(an int L)) L).
Proof. apply subt_fn. apply sub_refl. apply subt_int.
       apply sub_refl. apply subt_int. apply sub_refl. Qed.



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

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.

Module SecLang.

Inductive tm : Type :=
| tvar  : id -> tm 
| tprot : Sec -> tm -> tm
| tcon  : nat -> Sec -> tm
| tabs  : id -> Ty -> tm -> Sec -> tm
| tapp  : tm -> tm -> tm
.

Check tvar (Id 0).
Check tcon 1 H.
Check tcon 2 L.
Check tabs (Id 0) (an int L) (tvar (Id 0)) H.
Check tabs (Id 1) (an (fn (an int H)(an int H)) L) (tvar (Id 1)) H.
Check tabs (Id 0) (an int H) (tabs (Id 1) (an int L) (tvar (Id 0)) H) H.
Check tapp (tabs (Id 0) (an int H) (tvar (Id 0)) H) (tcon 1 H).
Check tprot H (tcon 2 L).
Check tprot H (tabs (Id 0)(an int L)(tvar (Id 0)) L).
Check tprot H (tapp (tabs (Id 0)(an int L)(tvar (Id 0)) L)(tcon 1 L)).
Check tabs (Id 0)(an int L)(tprot H (tvar (Id 0))) L.
Check tapp (tabs (Id 0)(an int H)(tvar (Id 0)) H)(tprot H (tcon 2 L)).
Check tapp (tprot H (tabs (Id 0)(an int L)(tvar (Id 0)) L))(tcon 1 L).


Inductive value : tm -> Prop :=
| v_c : forall b n,
        value (tcon n b)
| v_f : forall n T e b,
        value (tabs (Id n) T e b).




Fixpoint subst (x:id) (s:tm) (t:tm): tm :=
  match t with
(*variables*)
  | tvar x' => 
      if beq_id x x' then s  else t
(*protects*)
  | tprot b t' =>
      tprot b (subst x s t')
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
[(Id 0) := (tabs (Id 0)(an int L)(tvar (Id 0)) L)] (tvar (Id 0)) 
= tabs (Id 0)(an int L)(tvar (Id 0)) L.
Proof. simpl. reflexivity. Qed.
Example test_subst_2:
[(Id 0) := tcon 1 H](tvar (Id 1)) = tvar (Id 1).
Proof. simpl. reflexivity. Qed.
Example test_subst_3:
[(Id 0) := (tcon 1 H)] (tabs (Id 1) (an int H) (tvar (Id 0)) H)
= tabs (Id 1) (an int H) (tcon 1 H) H.
Proof. simpl. reflexivity. Qed.
Example test_subst_4:
[(Id 0) := (tcon 1 L)](tabs (Id 0)(an int L)(tvar (Id 0)) L)
= tabs (Id 0)(an int L)(tvar (Id 0)) L.
Proof. simpl. reflexivity. Qed.
Example test_subst_5:
[(Id 0) := tcon 4 L] (tcon 1 H) = tcon 1 H.
Proof. simpl. reflexivity. Qed.
Example test_subst_6:
[(Id 0) := tcon 1 H] (tapp (tabs (Id 0) (an int H) (tvar (Id 0)) H)(tvar (Id 0)))
= tapp (tabs (Id 0) (an int H) (tvar (Id 0)) H)(tcon 1 H).
Proof. simpl. reflexivity. Qed.
Example test_subst_7:
[(Id 0) := tcon 1 L](tprot H (tvar (Id 0))) = tprot H (tcon 1 L).
Proof. simpl. reflexivity. Qed.
Example test_subst_8:
[(Id 0) := tcon 1 H](tprot H (tcon 1 L)) = tprot H (tcon 1 L).
Proof. simpl. reflexivity. Qed.
Example test_subst_9:
[(Id 0) := tcon 1 L](tprot H (tabs (Id 1)(an int L)(tvar (Id 0)) L))
= tprot H (tabs (Id 1)(an int L)(tcon 1 L) L).
Proof. simpl. reflexivity. Qed.
Example test_subst_10:
[(Id 0) := tcon 1 L](tabs (Id 1)(an int H)(tprot H (tvar (Id 0))) L)
= tabs (Id 1)(an int H)(tprot H (tcon 1 L)) L.
Proof. simpl. reflexivity. Qed.
Example test_subst_11:
[(Id 0) := tcon 1 L](tapp (tabs (Id 0)(an int L)(tprot H (tvar (Id 0))) H)(tprot H (tvar (Id 0))))
= tapp (tabs (Id 0)(an int L)(tprot H (tvar (Id 0))) H)(tprot H (tcon 1 L)).
Proof. simpl. reflexivity. Qed.


Inductive step : tm  -> tm  -> Prop :=

| st_prot: forall b t t',
  t ==> t' ->
  tprot b t ==> tprot b t'
| st_protL: forall v,
  value v ->
  tprot L v ==> v
| st_protHf: forall x T e b,
  tprot H (tabs x T e b) ==> tabs x T e H
| st_protHc: forall n b,
  tprot H (tcon n b) ==> tcon n H
| st_appabs: forall x T e b v,
  value v ->
  tapp (tabs x T e b) v ==> tprot b ([x := v]e) 
| st_app1: forall t1 t1' t2,
  t1  ==> t1'  ->
  tapp t1 t2  ==> tapp t1' t2 
| st_app2: forall v1 t2 t2',
  value v1 ->
  t2  ==> t2'  ->
  tapp v1 t2  ==> tapp v1 t2' 

where "t1  '==>' t2 " := (step t1 t2).

Definition multistep := (multi step).
Notation "t1  '==>*' t2" := (multistep t1 t2) 
  (at level 40).

(*##############tests of [step]###########*)
Example test_step_1:
tapp (tabs (Id 0)(an int L)(tvar (Id 0)) H)(tcon 1 L) 
==>* tcon 1 H.
Proof. apply multi_step with (y:= tprot H ([(Id 0) := tcon 1 L](tvar (Id 0)))).
apply st_appabs. apply v_c. simpl. apply multi_step with (y:=tcon 1 H).
apply st_protHc. apply multi_refl.
Qed.

Example test_step_2:
tapp (
      tapp 
           (tabs (Id 1)(an int L)(tabs (Id 0)(an int L)(tvar (Id 0)) L) H)
           (tcon 1 L) 
     )
     (
      tapp 
           (tabs (Id 0)(an int L)(tvar (Id 0)) L)
           (tcon 1 L)
     ) 
==>* tcon 1 H.
Proof. apply multi_step with (y:=(tapp (tprot H ([(Id 1) := tcon 1 L](tabs (Id 0)(an int L)(tvar (Id 0)) L)))(tapp (tabs (Id 0)(an int L)(tvar (Id 0)) L)(tcon 1 L)))).
apply st_app1. apply st_appabs. apply v_c.
apply multi_step with (y:= (tapp (tabs (Id 0)(an int L)(tvar (Id 0)) H)(tapp (tabs (Id 0)(an int L)(tvar (Id 0)) L)(tcon 1 L)))).
apply st_app1. apply st_protHf. 
apply multi_step with (y:= tapp (tabs (Id 0)(an int L)(tvar (Id 0)) H)(tprot L ([(Id 0) := tcon 1 L](tvar (Id 0))))). 
apply st_app2. apply v_f. apply st_appabs. apply v_c.
apply multi_step with (y:= tapp (tabs (Id 0)(an int L)(tvar (Id 0)) H)(tcon 1 L)). apply st_app2. apply v_f.
apply st_protL. apply v_c. 
apply multi_step with (y:= tprot H ([(Id 0) := tcon 1 L](tvar (Id 0)))). apply st_appabs. apply v_c.
apply multi_step with (y:= tcon 1 H). simpl. apply st_protHc. 
apply multi_refl.
Qed.
Example test_step_3:
tapp (tabs (Id 1)(an int H)(tabs (Id 0)(an int L)(tvar (Id 0)) L) H)(tcon 1 H)
==>* tabs (Id 0)(an int L)(tvar (Id 0)) H.
Proof. apply multi_step with (y:= tprot H ([(Id 1) := tcon 1 H](tabs (Id 0)(an int L)(tvar (Id 0)) L))).
apply st_appabs. apply v_c. 
apply multi_step with (y:= tabs (Id 0)(an int L)(tvar (Id 0)) H). simpl. apply st_protHf.
apply multi_refl.
Qed.
Example test_step_4:
tapp (tabs (Id 0)(an (fn (an int L)(an int L)) L)(tvar (Id 0)) H)
     (tabs (Id 0)(an int L)(tvar (Id 0)) L)
==>* tabs (Id 0)(an int L)(tvar (Id 0)) H.
Proof. apply multi_step with (y:= tprot H ([(Id 0) := tabs (Id 0)(an int L)(tvar (Id 0)) L](tvar (Id 0)))).
apply st_appabs. apply v_f. apply multi_step with (y:= tabs (Id 0)(an int L)(tvar (Id 0)) H).
simpl. apply st_protHf. apply multi_refl.
Qed.
Example test_step_5:
tapp (tabs (Id 0)(an (fn (an int L) (an int L)) L)(tvar (Id 0)) H)
     (tabs (Id 0) (an int L)(tvar (Id 1)) L) 
==>* tabs (Id 0)(an int L)(tvar (Id 1)) H.
Proof. apply multi_step with (y:= tprot H ([(Id 0) := tabs (Id 0)(an int L)(tvar (Id 1)) L ](tvar (Id 0)))).
apply st_appabs. apply v_f. 
apply multi_step with (y:= tabs (Id 0)(an int L)(tvar (Id 1)) H). simpl. apply st_protHf. 
apply multi_refl.
 Qed.
Example test_step_6:
tapp (tabs (Id 1)(an int H)(tprot H (tvar (Id 0))) L) (tcon  1 H) 
==> tprot L (tprot H (tvar (Id 0))).
Proof. apply st_appabs. apply v_c.
Qed.
Example test_step_7:
tapp (tabs (Id 0)(an int H)(tprot H (tvar (Id 0))) L) (tcon  1 H) 
==>* tcon 1 H.
Proof. apply multi_step with (y:= tprot L ([(Id 0) := tcon 1 H](tprot H (tvar (Id 0))))).
apply st_appabs. apply v_c. simpl.
apply multi_step with (y:= tprot L (tcon 1 H)). apply st_prot. apply st_protHc.
apply multi_step with (y:= tcon 1 H).  apply st_protL. apply v_c. 
apply multi_refl.
 Qed.
Example test_step_8:
tapp (tabs (Id 0)(an int H)(tvar (Id 0)) H) (tprot H (tcon 1 L))
==>* tcon 1 H.
Proof. apply multi_step with (y:= tapp (tabs (Id 0)(an int H)(tvar (Id 0)) H)(tcon 1 H)).
apply st_app2. apply v_f. apply st_protHc. 
apply multi_step with (y:= tprot H ([(Id 0) := tcon 1 H](tvar (Id 0)))). apply st_appabs.
apply v_c. simpl. apply multi_step with (y:= tcon 1 H). apply st_protHc.
apply multi_refl.
Qed.
Example test_step_9:
tprot H (tapp (tabs (Id 0)(an int L)(tvar (Id 0)) L)(tcon 1 L))
==>* tcon 1 H.
Proof. apply multi_step with (y:= tprot H (tprot L ([(Id 0) := tcon 1 L](tvar (Id 0))))).
apply st_prot. apply st_appabs. apply v_c. 
apply multi_step with (y:= tprot H (tcon 1 L)). apply st_prot. simpl. apply st_protL. apply v_c.
apply multi_step with (y:= tcon 1 H). apply st_protHc.
apply multi_refl.
Qed.
Example test_step_10:
~ tprot H (tvar (Id 0)) ==> tcon 1 H.
Proof. intros contra. inversion contra.
Qed.

(*####################Typing rules###########################*)
(**
In what follows, we will specify the typing rules of the system.
One intuitive way of doing it is that we suppose that before reduction,
we have a "typing context" as follows,
context := id -> option Ty 
which maps each variable to a type.

We have the following typing rules given a certain typing context
"Gamma",

a. t_var
 Gamma (Id n) = T
-------------------------------(t_var)
 Gamma |- tvar (Id n) : T 

b. t_prot
 Gamma | t : T
-----------------------------------------(t_prot)
 Gamma |- tprot b t: join T b 
where [join] is a function whcih upon a security
label [b] and a type [T] returns a type with the
security level at least as high as that of [T].

c. t_con
 Gamma  |- (tcon n b) : an int b

d. t_abs
 update Gamma x T1 |- e : T2
------------------------------------(t_abs)
 Gamma |- tabs x T1 e b : an (fn T1 T2) b  

e. t_app
  Gamma |- t1 : Ann (fn T1 T2) b
  Gamma |- t2 : T1
----------------------------------(t_app)
  Gamma |- tapp t1 t2 : join T2 b

*)





(*##########join#########*)
Definition join (T:Ty) (b:Sec): Ty :=
 match b with
 | L => T
 | H => match T with
        | an R b => an R H
        end
 end.
Example test_join_1:
 join (an int L) H = an int H.
Proof. simpl. reflexivity. Qed.
Example test_join_2:
 join (an (fn (an int L)(an int L)) L) H = an (fn (an int L)(an int L)) H.
Proof. simpl. reflexivity. Qed.

(**
Note:
Add sub-typing relation, referring to Lu's paper...
*)
Inductive has_type : context  -> tm -> Ty -> Prop :=
| t_var: forall Gamma n T,
  Gamma (Id n) = Some T ->
  has_type Gamma (tvar (Id n)) T
| t_prot: forall Gamma t T T' b,
  has_type Gamma t T ->
  join T b = T' ->
  has_type Gamma (tprot b t) T'
| t_con: forall Gamma n b,
  has_type Gamma (tcon n b) (an int b)
| t_abs: forall Gamma T1 T2 b e x,
  has_type (Cupdate Gamma x (Some T1)) e T2 ->
  has_type Gamma (tabs x T1 e b) (an (fn T1 T2) b)
| t_app: forall Gamma T1 T2 T2' b t1 t2,
  has_type Gamma t1 (an (fn T1 T2) b) ->
  has_type Gamma t2 T1 ->
  join T2 b = T2' ->
  has_type Gamma (tapp t1 t2) T2'
| t_sub: forall Gamma t T T',
  has_type Gamma t T ->
  T < T' ->
  has_type Gamma t T'.

(*#######inversions of [has_type]##########*)
(*some auxiliary lemmas*)
 
(*end*)
(*inversion of [has_type Gamma (tvar x) T]*)
Lemma inversion_tvar: forall Gamma x T,
has_type Gamma (tvar x) T ->
exists T0, (Gamma x = Some T0)/\(T0 < T).
Proof. intros. remember (tvar x) as t. induction H0.
inversion Heqt. subst. exists T. split. apply H0. apply subtyping_refl.
subst. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt.
apply IHhas_type in Heqt. inversion Heqt. exists x0. split. inversion H2.
apply H3. inversion H2. apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl.
apply H4. apply H1.
Qed.

(*inversion of [has_type Gamma (tabs x T1 e b) T]*)
(**     
Lemma inversion_tabs: forall Gamma x T1 T e b,
has_type Gamma (tabs x T1 e b) T ->
(exists T1', exists T2', exists b', 
has_type (Cupdate Gamma x (Some T1)) e T2'/\(T1' < T1)/\(subsum_r b b')/\((an (fn T1' T2') b')< T)).
Proof. intros. remember (tabs x T1 e b) as t. induction H0. inversion Heqt. inversion Heqt. inversion Heqt.
inversion Heqt. subst. exists T1. exists T2. exists b. split. apply H0. split. apply subtyping_refl.
split. apply sub_refl. apply subtyping_refl. inversion Heqt.
apply IHhas_type in Heqt. inversion Heqt. exists x0. inversion H2. exists x1. inversion H3. exists x2. inversion H4.
split. apply H5. inversion H6. split. apply H7. split. inversion H8. apply H9.
apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl. inversion H8. apply H10. apply H1.
Qed.

Lemma well_typed_tabs: forall Gamma x T1 e b T,
has_type Gamma (tabs x T1 e b) T ->
exists T1', exists T2', exists b', exists T2, 
(has_type Gamma (tabs x T1 e b) (an (fn T1 T2') b))/\
(an (fn T1' T2) b' < T)/\(T1' < T1)/\(T2'<T2)/\(subsum_r b b').
Proof.  intros. remember (tabs x T1 e b) as t. induction H0. inversion Heqt.
        inversion Heqt. inversion Heqt. inversion Heqt. subst. exists T1. exists T2. exists b.
        exists T2. split. apply t_abs. apply H0.
        split. apply subtyping_refl. split. apply subtyping_refl. split. apply subtyping_refl. apply sub_refl.
        inversion Heqt. apply IHhas_type in Heqt. inversion Heqt. inversion H2. inversion H3. inversion H4.
        inversion H5. exists x0. exists x1. exists x2. exists x3. 
        split. apply  H6. inversion H7. split. apply subtyping_trans with (x:=T)(y:=T).
        apply subtyping_refl. apply H8. apply H1. apply H9. 
Qed.
*)
Lemma inversion_tabs: forall Gamma x T1 T e b,
has_type Gamma (tabs x T1 e b) T ->
exists T1', exists T2, exists T2', exists b',
(has_type Gamma (tabs x T1 e b) (an (fn T1 T2) b)) /\
(has_type (Cupdate Gamma x (Some T1)) e T2) /\
(T1'<T1)/\(T2<T2')/\(subsum_r b b')/\((an (fn T1' T2') b') < T).
Proof. intros. remember (tabs x T1 e b) as t. induction H0. inversion Heqt. inversion Heqt. inversion Heqt.
inversion Heqt. subst. exists T1. exists T2. exists T2. exists b. split. apply t_abs with (b:=b) in H0. apply H0.
split. apply H0. split. apply subtyping_refl. split. apply subtyping_refl. split. apply sub_refl. apply subtyping_refl.
inversion Heqt.  apply IHhas_type in Heqt. inversion Heqt. exists x0. inversion H2. exists x1. inversion H3. exists x2.
inversion H4. exists x3. inversion H5. split. apply H6. inversion H7. split. apply H8. split. inversion H9. apply H10.
split. inversion H9. inversion H11. apply H12. split. inversion H9. inversion H11. inversion H13. apply H14. inversion H9.
inversion H11. inversion H13. apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl. apply H15. apply H1.
Qed.
Lemma inversion_tprot: forall Gamma t T b,
has_type Gamma (tprot b t) T ->
exists T', exists T'', (join T' b < T) /\(has_type Gamma t T'')/\(T'' < T').
Proof. intros. remember (tprot b t) as e. induction H0. subst. inversion Heqe.
       inversion Heqe. subst. exists T. exists T. split. apply subtyping_refl.
       split. apply H0. apply subtyping_refl. inversion Heqe. inversion Heqe.  inversion Heqe.
       apply IHhas_type in Heqe. inversion Heqe. inversion H2. inversion H3. exists x. exists x0. 
       inversion H5. split. apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl.
       apply H4. apply H1. apply H5.
Qed.
(*inversion of [has_type Gamma (tcon n b) T]*)

Lemma inversion_tcon: forall Gamma T n b,
has_type Gamma (tcon n b) T ->
exists T', exists T'', exists b', (T' = an int b)/\(T'' = an int b')/\(subsum_r b b')/\(T'' < T).
Proof. intros. remember (tcon n b) as t. induction H0.
inversion Heqt. inversion Heqt. inversion Heqt. subst. exists (an int b). exists (an int b).
exists b. split. reflexivity. split. reflexivity. split. apply sub_refl. apply subtyping_refl.
inversion Heqt. inversion Heqt.  apply IHhas_type in Heqt. inversion Heqt. exists x. inversion H2.
exists x0. inversion H3. exists x1. 
inversion H4. split. apply H5. inversion H6. split. apply H7. inversion H8. split. apply H9. 
apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl. apply H10. apply H1.
Qed.

(*inversion of [has_type Gamma (tapp t1 t2) T]*)
Lemma inversion_tapp: forall Gamma t1 t2 T2,
has_type Gamma (tapp t1 t2) T2 ->
exists T1', exists T2', exists b', exists T1'', exists T1''', exists T2'', exists b'',
has_type Gamma t1 (an (fn T1' T2') b')/\((an (fn T1' T2') b')<(an (fn T1'' T2'') b''))/\
(has_type Gamma t2 T1''')/\(T1''' < T1'') /\
((join T2'' b'') < T2).
Proof. intros. remember (tapp t1 t2) as t. induction H0.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. subst. exists T1.
exists T2. exists b. exists T1. exists T1. exists T2. exists b.
split. apply H0_. split. apply subtyping_refl. split. apply H0_0. split. apply subtyping_refl. 
apply subtyping_refl.
 apply IHhas_type in Heqt. inversion Heqt. exists x. inversion H2.
exists x0. inversion H3. exists x1. inversion H4. exists x2. inversion H5. exists x3. inversion H6. exists x4.
inversion H7. exists x5. inversion H8.  split. apply H9. inversion H10. split. apply H11. inversion H12.
split. apply H13. inversion H14. split. apply H15. apply subtyping_trans with (x:=T)(y:=T).
apply subtyping_refl. apply H16. apply H1. Qed.



(*#######some examples of well-typed expressions#############*)
Example has_type_1:
 has_type (Cupdate empty_context (Id 0) (Some (an int L))) 
          (tapp (tabs (Id 0)(an int L)(tvar (Id 0)) H)(tvar (Id 0)))
          (an int H).
Proof. apply t_app with (T1:=an int L)(T2:=an int L)(b:=H).
apply t_abs. apply t_var. apply Cupdate_eq.
apply t_var. apply Cupdate_eq. reflexivity.
Qed.
Example has_type_2:
 has_type empty_context (tapp (tabs (Id 0)(an int L)(tvar (Id 0)) H)(tcon 1 L)) (an int H).
Proof. apply t_app with (T1:=an int L)(T2:=an int L)(b:=H).
apply t_abs. apply t_var. apply Cupdate_eq. apply t_con.
reflexivity. Qed.
Example has_type_3:
 has_type (Cupdate empty_context (Id 0)(Some (an int H)))
          (tvar (Id 0))
          (an int H).
Proof. apply t_var. apply Cupdate_eq. Qed.
Example has_type_4:
 has_type (Cupdate empty_context (Id 0)(Some (an int L)))
          (tprot H (tvar (Id 0)))
          (an int H).
Proof. apply t_prot with (T:= an int L). apply t_var. apply Cupdate_eq.
reflexivity. Qed.
Example has_type_5:
 has_type empty_context
         (tapp (
      tapp 
           (tabs (Id 1)(an int L)(tabs (Id 0)(an int L)(tvar (Id 0)) L) H)
           (tcon 1 L) 
     )
     (
      tapp 
           (tabs (Id 0)(an int L)(tvar (Id 0)) L)
           (tcon 1 L)
     ))
     (an int H).
Proof. apply t_app with (T1:=an int L)(T2:=an int L)(b:=H).
apply t_app with (T1:=an int L)(T2:=an (fn (an int L)(an int L)) L)(b:=H).
apply t_abs. apply t_abs. apply t_var. apply Cupdate_eq. apply t_con. reflexivity.
apply t_app with (T1:=an int L)(T2:=an int L)(b:=L). apply t_abs.
apply t_var. apply Cupdate_eq. apply t_con. reflexivity. reflexivity.
Qed.
Example has_type_6:
 has_type empty_context
          (tapp (tabs (Id 1)(an int H)(tabs (Id 0)(an int L)(tvar (Id 0)) L) H)(tcon 1 H))
          (an (fn (an int L)(an int L)) H).
Proof. apply t_app with (T1:=an int H)(T2:=an (fn (an int L)(an int L)) L)(b:=H).
apply t_abs. apply t_abs. apply t_var. apply Cupdate_eq. apply t_con. reflexivity.
Qed.
Example has_type_7:
 has_type (Cupdate empty_context (Id 0) (Some (an int L)))
          (tapp (tabs (Id 1)(an int H)(tprot H (tvar (Id 0))) L)(tcon 1 H))
          (an int H).
Proof. apply t_app with (T1:=an int H)(T2:=an int H)(b:=L).
apply t_abs. apply t_prot with (T:=an int L). apply t_var. 
assert (A:  beq_id (Id 0) (Id 1) = false ). reflexivity. 
apply Cupdate_permute with (f:=empty_context)(T1:=Some (an int L))(T2:=Some (an int H))(X3:=(Id 0)) in A.
rewrite->A. apply Cupdate_eq. reflexivity. apply t_con. reflexivity.
Qed.
Example has_type_8:
 has_type empty_context
          (tapp (tabs (Id 0)(an int L)(tprot H (tvar (Id 0))) L)(tcon 1 L))
          (an int H).
Proof. apply t_app with (T1:=an int L)(T2:= an int H)(b:=L).
apply t_abs. apply t_prot with (T:=an int L). apply t_var.
 apply Cupdate_eq. reflexivity.
apply t_con. reflexivity. Qed.
Example has_type_9:
has_type empty_context (tabs (Id 0)(an int L)(tprot H (tvar (Id 0))) L) (an (fn (an int L)(an int H)) L).
Proof. apply t_abs. apply t_prot with (T:=an int L). apply t_var. apply Cupdate_eq. reflexivity.
Qed.
Example has_type_10:
has_type empty_context (tapp (tabs (Id 0)(an int H)(tvar (Id 0)) L)(tprot H (tcon 1 L)))(an int H).
Proof. apply t_app with (T1:=an int H)(T2:=an int H)(b:= L). apply t_abs. apply t_var. apply Cupdate_eq.
apply t_prot with (T:= an int L). apply t_con. reflexivity. reflexivity.
Qed.
Example has_type_11:
has_type empty_context (tapp (tabs (Id 0)(an int H)(tcon 1 L) H)(tcon 1 L)) (an int H).
Proof. apply t_app with (T1:=an int H)(T2:=an int L)(b:=H). apply t_abs. apply t_con.
       apply t_sub with (T:=an int L). apply t_con. apply subt_int. apply sub_LH. reflexivity.     
Qed.
Example has_type_12:
has_type empty_context (tabs (Id 0)(an int H)(tcon 1 L) L)(an (fn (an int L)(an int H)) H).
Proof. apply t_sub with (T:=an (fn (an int H)(an int L)) L). apply t_abs. apply t_con.
       apply subt_fn. apply sub_LH. apply subt_int. apply sub_LH. apply subt_int. apply sub_LH.
Qed.
Example has_type_13:
has_type empty_context (tcon 1 L) (an int H).
Proof. apply t_sub with (T:=an int L). apply t_con. apply subt_int. apply sub_LH.
Qed.
Example has_type_14:
has_type empty_context (tapp (tabs (Id 0)(an int H)(tcon 1 L) H)(tcon 1 L))(an int H).
Proof. apply t_app with (T1:=an int L)(T2:=an int L)(b:=H). apply t_sub with (T:=an (fn (an int H)(an int L)) H).
       apply t_abs. apply t_con. apply subt_fn. apply sub_refl. apply subt_int. apply sub_LH. apply subt_int.
       apply sub_refl. apply t_con. reflexivity.
Qed.
Example has_type_15:
has_type empty_context (tapp (tabs (Id 0)(an int L)(tvar (Id 0)) H)(tcon 1 L)) (an int H).
Proof. apply t_app with (T1:=an int L)(T2:=an int H)(b:=H). apply t_abs. apply t_sub with (T:=an int L). apply t_var.
       apply Cupdate_eq. apply subt_int. apply sub_LH. apply t_con. reflexivity. Qed.    

Example has_type_16:forall Gamma b n,
has_type Gamma (tcon n b) (an int b).
Proof. intros. apply t_con. Qed.



(*############some counter examples##########*)



(**
Case 1: undefined or ill-defined free variables
*)
Example has_type_i:
 ~has_type empty_context
           (tvar (Id 0))
           (an int L).
Proof. intros contra. apply inversion_tvar in contra. inversion contra.
       inversion H0. inversion H1.
Qed.
Example has_type_i':
~has_type (Cupdate empty_context (Id 0) (Some (an int H)))
         (tvar (Id 0))
         (an (fn (an int L)(an int L)) H).
Proof. intros contra. apply inversion_tvar in contra. inversion contra.
       rewrite->Cupdate_eq in H0. inversion H0. inversion H2. subst.
       inversion H1. Qed.
(**
Case 2: ill-typed abstractions whose body contains undefined
        free variables
*)
Example has_type_j:
~has_type empty_context
          (tabs (Id 0) (an int L)(tvar  (Id 1)) H)
          (an (fn (an int L)(an int L)) H).
Proof. intros contra. apply inversion_tabs in contra. inversion contra.
       inversion H0. inversion H1.  inversion H2. inversion H3. inversion H5.
       apply inversion_tvar in H6. inversion H6. inversion H8. assert (beq_id (Id 0)(Id 1) = false).
       apply not_eq_beq_id_false. intros contra'. inversion contra'.
       apply Cupdate_neq with (T:=Some (an int L))(St:=empty_context) in H11.
       rewrite->H11 in H9. inversion H9. Qed.

Example has_type_j':
~has_type (Cupdate empty_context (Id 1)(Some (an int L))) 
          (tabs (Id 0)(an int L)(tvar (Id 2)) L)
          (an (fn (an int L)(an int H)) L).
Proof. intros contra. apply inversion_tabs in contra. inversion contra.
       inversion H0. inversion H1. inversion H2. inversion H3. inversion H5.
       apply inversion_tvar in H6. inversion H6. 
       assert (beq_id (Id 0)(Id 2) = false). apply not_eq_beq_id_false.
       intros contra'. inversion contra'. apply Cupdate_neq with (T:=Some (an int L))(St:=Cupdate empty_context (Id 1)(Some (an int L))) in H9.
       inversion H8.
       rewrite->H9 in H10. assert (beq_id (Id 1)(Id 2)=false). apply not_eq_beq_id_false.
       intros contra'. inversion contra'.
       apply Cupdate_neq with (T:=Some (an int L))(St:=empty_context) in H12. rewrite->H12 in H10. 
       inversion H10.
Qed.
(**
Case 3: ill-typed abstraction whose type is not a function type
*)
Example has_type_j'':
~has_type empty_context (tabs (Id 0)(an int H)(tvar (Id 1)) H) (an int H).
Proof. intros contra. inversion contra. subst. apply inversion_tabs in H0.
       inversion H0. inversion H2. inversion H3. inversion H4. inversion H5.
       inversion H7. inversion H9. inversion H11. inversion H13. destruct T. destruct r. inversion H15.
       inversion H1.
Qed.
Example has_type_j''':
~has_type  empty_context 
          (tabs (Id 0)(an int L)(tvar (Id 0)) H) (an int H).
Proof. intros contra. inversion contra. subst. apply inversion_tabs in H0.
       inversion H0. inversion H2. inversion H3. inversion H4. inversion H5.
       inversion H7. inversion H9. inversion H11. inversion H13. destruct T. destruct r.
       inversion H15. inversion H1.
Qed. 
(**
Case 4: ill-defined protects
*) 
Example has_type_k:
~has_type empty_context (tprot H (tvar (Id 0))) (an int H).
Proof. intros contra. apply inversion_tprot in contra.
       inversion contra. inversion H0. inversion H1. inversion H3.
       apply inversion_tvar in H4.
       inversion H4. inversion H6. inversion H7. Qed.
Example has_type_k':
~has_type empty_context (tprot H (tabs (Id 0)(an int H)(tvar (Id 1)) L))
          (an (fn (an int H)(an int H)) H).
Proof. intros contra. apply inversion_tprot in contra. inversion contra.
       inversion H0. inversion H1. inversion H3. 
       apply inversion_tabs in H4. inversion H4. inversion H6. inversion H7.
       inversion H8. inversion H9. inversion H11. apply inversion_tvar in H12. 
        inversion H12. inversion H14.
        assert (beq_id (Id 0)(Id 1) = false). apply not_eq_beq_id_false.
       intros contra'. inversion contra'. apply Cupdate_neq with (T:=Some (an int H))(St:=empty_context) in H17.
       rewrite->H17 in H15. inversion H15. Qed. 
Example has_type_k'':
~has_type (Cupdate empty_context (Id 0)(Some (an int L))) (tprot H (tabs (Id 0)(an int L)(tvar (Id 0)) L))
          (an int H).
Proof. intros contra. apply inversion_tprot in contra. inversion contra.
      inversion H0. inversion H1. inversion H3.
      apply inversion_tabs in H4. inversion H4. inversion H6. inversion H7.
      inversion H8. inversion H9. inversion H11. inversion H13. inversion H15.
      inversion H17. 
      destruct x0. destruct r. inversion H19. destruct x. destruct r.
      inversion H5. simpl in H2. inversion H2.
Qed.
Example has_type_k''':
~has_type empty_context (tprot H (tcon 1 L)) (an int L).
Proof. intros contra. apply inversion_tprot in contra. inversion contra.
inversion H0. inversion H1. inversion H3. 
destruct x. destruct r.  simpl in H2. inversion H2. inversion H8. 
simpl in H2. inversion H2.
Qed.
(**
Case 5: ill-typed constants
*)
Example has_type_l:
~has_type empty_context (tprot H (tcon 1 L)) (an int L).
Proof. intros contra. apply inversion_tprot in contra. inversion contra.
inversion H0. inversion H1. inversion H3. destruct x. destruct r.
simpl in H2. inversion H2. inversion H8. simpl in H2. inversion H2.
Qed.
Example has_type_l':forall Gamma n,
~has_type Gamma (tcon n H) (an int L).
Proof. intros. intros contra. apply inversion_tcon in contra.
inversion contra. inversion H0. inversion H1. inversion H2. 
inversion H4. inversion H6. inversion H7. subst. inversion H8.
inversion H9. Qed.
Example has_type_l'':forall Gamma n b,
~has_type Gamma (tcon n b) (an (fn (an int L)(an int L)) L).
Proof. intros. intros contra. apply inversion_tcon in contra.
inversion contra. inversion H0. inversion H1. inversion H2.
inversion H4. inversion H6. subst. inversion H8. Qed.
(**
Case 6: ill-matched applications
*)
Example has_type_m:
~has_type empty_context
          (tapp (tabs (Id 0)(an int L)(tcon 2 L) H)(tcon 1 H))
          (an int H).
Proof. intros contra. apply inversion_tapp in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H4.
inversion H5. inversion H6. apply inversion_tabs in H7. inversion H7.
inversion H9. inversion H10. inversion H11. inversion H12. inversion H14.
inversion H16. inversion H18. inversion H20. inversion H22. subst. destruct x6.
destruct r. destruct s. destruct x. destruct r. destruct s. subst.
destruct x2. destruct r. destruct s. inversion H8. inversion H24. inversion H26.
apply inversion_tcon in H25. inversion H25. inversion H32. inversion H33. inversion H34.
inversion H36. inversion H38. subst. inversion H39. subst. destruct x3. destruct r. destruct s.
inversion H40. inversion H41. inversion H28. inversion H41. inversion H40.
inversion H8. inversion H23. inversion H35. inversion H39. inversion H8.
inversion H23. inversion H35. inversion H30. inversion H25. inversion H30.
inversion H17. inversion H25. inversion H17.
Qed.
 

Example has_type_m':
~has_type empty_context
         (tapp (tabs (Id 0)(an int L)(tvar (Id 0)) L)(tprot H (tcon 1 L)))
          (an int L).
Proof. intros contra. apply inversion_tapp in contra. inversion contra. inversion H0.
       inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion
       H6. inversion H8. inversion H10. apply inversion_tabs in H7. apply inversion_tprot in H11.
       inversion H11. inversion H13. inversion H14. inversion H16. 
       apply inversion_tcon in H17. inversion H17. inversion H19. inversion H20. inversion H21. 
       inversion H23. subst. inversion H21. inversion H24. subst. inversion H27. 
       inversion H29. subst. inversion H18. subst. 
       inversion H7. inversion H30. inversion H33. inversion H34. inversion H35. inversion H37. inversion H39.
       inversion H41. inversion H43. 
       destruct x6. destruct r. destruct s. destruct x. destruct r. destruct s. 
       destruct x2. destruct r. destruct s. inversion H12. destruct x3. destruct r. destruct s. simpl in H15.
       inversion H15. inversion H50. inversion H46. inversion H50. inversion H46. inversion H9. inversion H53.
       inversion H57. inversion H9. inversion H53. inversion H45. inversion H53. inversion H57. inversion H45.
       inversion H53. inversion H40. inversion H48. inversion H40.
Qed.



(**
Case 7: false applications
*)
Example has_type_m'':
~has_type empty_context
          (tapp (tcon 1 H)(tcon 2 L))
          (an int L).
Proof. intros contra. apply inversion_tapp in contra. inversion contra. inversion H0.
       inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6.
       apply inversion_tcon in H7. inversion H7. inversion H9. inversion H10. inversion H11.
       inversion H13. subst. inversion H11. inversion H14. inversion H17. inversion H19.        
Qed.


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


(*#################auxiliary theorems##########*)
(*##########s_p_t_1##############*)
(*Firstly we use the following proposition to describe free variables*)
Inductive free_var : id -> tm -> Prop :=
| e_tvar : forall x,
      free_var x (tvar x)
| e_tprot : forall x b t,
      free_var x t ->
      free_var x (tprot b t)
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
free_var (Id 0) (tvar (Id 0)).
Proof. apply e_tvar. Qed.
Example test_free_var_2:
free_var (Id 0) (tvar (Id 0)).
Proof. apply e_tvar. Qed.
Example test_free_var_3:
free_var (Id 1) (tapp (tabs (Id 0)(an int L)(tvar (Id 0)) L)(tvar (Id 1))) .
Proof. apply e_tapp2. apply e_tvar. Qed.
Example test_free_var_4:
free_var (Id 1)(tabs (Id 0)(an int L)(tvar (Id 1)) L).
Proof. apply e_tabs. intros contra. inversion contra. apply e_tvar. Qed.
Example test_free_var_5:
free_var (Id 0) (tprot H (tvar (Id 0))).
Proof. apply e_tprot. apply e_tvar. Qed.
Example test_free_var_6:
free_var (Id 0) (tprot H (tapp (tabs (Id 0)(an int L)(tvar (Id 0)) L)(tvar (Id 0)))).
Proof. apply e_tprot. apply e_tapp2. apply e_tvar. Qed.
Example test_free_var_7:
free_var (Id 1) (tapp (tabs (Id 0)(an int L)(tvar (Id 1)) L)(tprot H (tcon 1 L))).
Proof. apply e_tapp1. apply e_tabs. intros contra. inversion contra. apply e_tvar.
Qed.
Example test_free_var_8:
forall x n b, ~free_var x (tcon n b).
Proof. intros. intros contra. inversion contra. Qed.
Example test_free_var_9:
forall x T e b,~free_var x (tabs x T e b).
Proof. intros. intros contra. inversion contra. subst. apply H3. reflexivity.
Qed.
Example test_free_var_10:
forall x n b b', ~free_var x (tprot b (tcon n b')).
Proof. intros. intros contra. inversion contra. subst. inversion H2.
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
Case ("tvar").
intros. apply inversion_tvar in H1. inversion H1. inversion H0.
        exists x0. apply H2.
Case ("tprot"). 
intros. apply inversion_tprot in H1. inversion H1. inversion H2.
        inversion H3. inversion H5. 
        apply IHfree_var in H6. inversion H6. exists x2. apply H8.
Case ("tapp1").
intros.  apply inversion_tapp in H1. inversion H1. inversion H2.
inversion H3. inversion H4. inversion H5. inversion H6. inversion H7.
inversion H8. apply IHfree_var in H9. inversion H9. exists x7.
apply H11.
Case ("tapp2").
intros. apply inversion_tapp in H1. inversion H1. inversion H2.
inversion H3. inversion H4. inversion H5. inversion H6. inversion H7.
inversion H8. inversion H10. inversion H12. apply IHfree_var in H13.
inversion H13. exists x7. apply H15.
Case ("tabs").
intros.  apply inversion_tabs in H2. inversion H2. inversion H3. inversion H4.
inversion H5. inversion H6. inversion H8. apply IHfree_var in H9. inversion H9. 
apply not_eq_beq_id_false in H0. apply Cupdate_neq with (T:=Some T)(St:=Gamma)in H0.
rewrite->H0 in H11. exists x4. apply H11.
Qed.

Corollary term_typable_empty_closed: forall t T,
has_type empty_context t T ->
forall x, ~free_var x t.
Proof. intros t. induction t.
Case ("tvar").
intros. intros contra. apply inversion_tvar in H0. inversion H0. inversion H1.
        inversion H2.
Case ("tprot"). 
intros. apply inversion_tprot in H0. inversion H0. inversion H1. inversion H2.
        inversion H4.  apply IHt with (x:=x)in H5.
        intros contra. inversion contra. subst. apply H5 in H9. inversion H9.
Case ("tcon").
intros. intros contra. inversion contra.
Case ("tabs").
intros. apply inversion_tabs in H0. inversion H0. inversion H1. inversion H2. inversion H3.
        inversion H4. inversion H6.
        intros contra. inversion contra.  subst. 
        apply term_typable_empty_closed_1 with (T:=x1)(Gamma:=Cupdate empty_context i (Some t))in H15.
        inversion H15. apply not_eq_beq_id_false in H12. apply Cupdate_neq with (T:=Some t)(St:=empty_context)in H12.
        rewrite->H12 in H9. inversion H9. apply H7.
Case ("tapp").
intros. apply inversion_tapp in H0. inversion H0. inversion H1. inversion H2. inversion H3.
      inversion H4. inversion H5. inversion H6. inversion H7. inversion H9. inversion H11.
      apply IHt1 with (x:=x)in H8. apply IHt2 with(x:=x) in H12. intros contra. inversion contra. 
      subst. apply H8 in H16. inversion H16. subst. apply H12 in H16. inversion H16.
Qed.


Corollary change_context: forall Gamma Gamma' t T,
has_type Gamma t T ->
(forall x, free_var x t -> Gamma x = Gamma' x) ->
has_type Gamma' t T.
Proof.
intros. generalize dependent Gamma'. induction H0.
Case ("t_var").
intros. apply t_var. rewrite<-H0. symmetry. apply H1.
apply e_tvar.
Case ("t_prot").
intros. apply t_prot with (T:=T). apply IHhas_type. intros. apply H2.
apply e_tprot. apply H3. apply H1.
Case ("t_con").
intros. apply t_con.
Case ("t_abs").
intros. apply t_abs. apply IHhas_type. intros. remember (beq_id x x0) as BB.
        destruct BB.  apply beq_id_eq in HeqBB. rewrite->HeqBB. rewrite->Cupdate_eq.
        rewrite->Cupdate_eq. reflexivity. inversion HeqBB. symmetry in H4.
        apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in H4. rewrite->H4.
        inversion HeqBB. symmetry in H5. apply Cupdate_neq with (T:=Some T1)(St:=Gamma') in H5.
        rewrite->H5. clear H4. clear H5. apply H1. apply e_tabs. intros contra. rewrite->contra in HeqBB.
        rewrite<-beq_id_refl in HeqBB. inversion HeqBB. apply H2.
Case ("t_app").
intros. apply t_app with (T1:=T1)(T2:=T2)(b:=b). apply IHhas_type1. intros. apply H1. apply e_tapp1.
        apply H2. apply IHhas_type2. intros. apply H1. apply e_tapp2. apply H2.
        apply H0.
Case ("t_sub").
intros. apply t_sub with (T:=T). apply IHhas_type. apply H2. apply H1.
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
intros. apply inversion_tvar in H1. inversion H1. inversion H2. 
remember (beq_id x i) as BB.
destruct BB. apply beq_id_eq in HeqBB. rewrite->HeqBB in H3.
rewrite->Cupdate_eq in H3. inversion H3. subst. simpl. rewrite<-beq_id_refl.
apply s_p_t_1. apply t_sub with (T:=x0). apply H0. apply H4.
symmetry in HeqBB. simpl. rewrite->HeqBB. destruct i. apply t_sub with (T:=x0).
 apply t_var. apply Cupdate_neq with (T:=Some T1)(St:=Gamma)in HeqBB.
rewrite->HeqBB in H3. apply H3. apply H4.
Case ("tprot").
intros. simpl. apply inversion_tprot in H1. inversion H1. inversion H2. inversion H3.
inversion H5.  apply t_sub with (T:=join x0 s). apply t_prot with (T:=x0) .  apply IHe with (T1:=T1).
apply H0. apply t_sub with (T:=x1). apply H6. apply H7. reflexivity. apply H4. 
Case ("tcon").
intros. simpl. apply inversion_tcon in H1. inversion H1. inversion H2. inversion H3. inversion H4. inversion H6.
inversion H8. subst. destruct T2. destruct r. inversion H10. subst. apply t_sub with (T:=an int s). apply t_con.
apply subt_int. apply subsum_r_trans with (b:=x2). apply H9. apply H11. inversion H10.
Case ("tabs").

intros. simpl. remember (beq_id x i) as BB. destruct BB. apply inversion_tabs in H1. 
inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H7. 
inversion H9. inversion H11. inversion H13. destruct T2. destruct r. inversion H15. apply t_sub with (T:=an (fn t0 t1) x3).
apply t_sub with (T:=an (fn t0 t1) s). apply t_sub with (T:=an (fn x0 t1) s). apply t_sub with (T:=an (fn t t1) s).

apply t_abs.  apply t_sub with (T:=x2). apply t_sub with (T:=x1). apply beq_id_eq in HeqBB. rewrite->HeqBB in H8.
assert (Cupdate Gamma i (Some t) = Cupdate (Cupdate Gamma i (Some T1)) i (Some t)).
apply functional_extensionality. intros. remember (beq_id i x4) as CC. destruct CC.
apply beq_id_eq in HeqCC. rewrite->HeqCC. rewrite->Cupdate_eq.
rewrite->Cupdate_eq. reflexivity. symmetry in HeqCC. inversion HeqCC. inversion HeqCC.
apply Cupdate_neq with (T:= Some t)(St:=Gamma ) in HeqCC. rewrite->HeqCC. 
apply Cupdate_neq with (T:= Some t)(St:=Cupdate Gamma i (Some T1)) in H17.
rewrite->H17. apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in H18. rewrite->H18.
reflexivity. rewrite->H16. apply H8. apply H12. inversion H15. subst. apply H24.
apply subt_fn. apply sub_refl. apply H10. apply subtyping_refl.
inversion H15. subst. apply subt_fn. apply sub_refl. apply H23. apply subtyping_refl. apply subt_fn.
apply H14. apply subtyping_refl. apply subtyping_refl. inversion H15. subst. apply subt_fn. apply H20.
apply subtyping_refl. apply subtyping_refl.
apply inversion_tabs in H1. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5.
inversion H7. inversion H9. inversion H11. inversion H13.  apply t_sub with (T:=an (fn x0 x2) x3). apply t_sub with (T:=an (fn x0 x1) x3).
apply t_sub with (T:=an (fn t x1) x3). apply t_sub with (T:=an (fn t x1) s). apply t_abs. apply IHe with (T1:=T1).  apply H0.

assert (Cupdate (Cupdate Gamma x (Some T1)) i (Some t) = Cupdate (Cupdate Gamma i (Some t)) x (Some T1)).
apply functional_extensionality. intros. remember (beq_id x x4) as AA.
remember (beq_id i x4) as BB. destruct AA. destruct BB. apply beq_id_eq in HeqAA.
apply beq_id_eq in HeqBB0. rewrite->HeqAA in HeqBB. rewrite->HeqBB0 in HeqBB.
rewrite<-beq_id_refl in HeqBB. inversion HeqBB. apply beq_id_eq in HeqAA. rewrite->HeqAA.
rewrite->Cupdate_eq. rewrite->HeqAA in HeqBB. symmetry in HeqBB. apply Cupdate_permute with (T1:=Some T1)(T2:=Some t)(X3:=x4)(f:=Gamma) in HeqBB.
rewrite->HeqBB. rewrite->Cupdate_eq. reflexivity. destruct BB. apply beq_id_eq in HeqBB0. rewrite->HeqBB0. rewrite->Cupdate_eq.
symmetry in HeqAA. apply Cupdate_permute with (T1:=Some T1)(T2:=Some t)(X3:=x4)(f:=Gamma) in HeqAA.
rewrite<-HeqAA. rewrite->Cupdate_eq. reflexivity. symmetry in HeqBB0. inversion HeqBB0.
apply Cupdate_neq with (T:=Some t)(St:=Cupdate Gamma x (Some T1))in HeqBB0.
rewrite->HeqBB0. symmetry in HeqAA. inversion HeqAA.
 apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in HeqAA.
rewrite->HeqAA. apply Cupdate_neq with (T:=Some T1)(St:=Cupdate Gamma i (Some t)) in H18.
rewrite->H18. apply Cupdate_neq with (T:=Some t)(St:=Gamma) in H17. rewrite->H17. reflexivity.
rewrite<-H16. apply H8. 
apply subt_fn. apply H14. apply subtyping_refl. apply subtyping_refl.
apply subt_fn. apply sub_refl. apply H10. apply subtyping_refl.  apply subt_fn.
apply sub_refl. apply subtyping_refl. apply H12. apply H15. 
Case ("tapp").
intros. simpl. apply inversion_tapp in H1. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5.
inversion H6. inversion H7. inversion H8. inversion H10. inversion H12. 
apply t_sub with (T:=join x5 x6).
 apply t_app with (T1:=x3)(T2:=x5)(b:=x6).
apply IHe1 with (T1:=T1). apply H0. apply t_sub with (T:= an (fn x0 x1) x2). apply H9. apply H11.
apply IHe2 with (T1:=T1). apply H0. apply t_sub with (T:=x4). apply H13. inversion H14. apply H15.
reflexivity. inversion H14. apply H16.
Qed.


(*#######################end###################*)
Lemma subtyping_join:forall T b' b,
subsum_r b' b ->
join T b' < join T b.
Proof. intros. inversion H0. apply subtyping_refl. destruct T. simpl.
destruct r. destruct s. apply subt_int. apply sub_LH. apply subtyping_refl.
destruct s. apply subt_fn. apply sub_LH. apply subtyping_refl. apply subtyping_refl.
apply subtyping_refl. Qed.
Theorem preservation: forall t t' T,
has_type empty_context t T ->
t ==> t' ->
has_type empty_context t' T.
Proof. intros. generalize dependent t'. remember (@empty_context) as context.
 induction H0.
Case ("t_var"). intros. inversion H1.  
Case ("t_prot"). intros. inversion H2. subst. apply t_prot with (T:=T).
                 apply IHhas_type in H6. apply H6. reflexivity. reflexivity. 
                 subst. simpl. apply H0. subst.
                 apply inversion_tabs in H0. inversion H0. inversion H1. inversion H3.
                 inversion H4. inversion H5. inversion H7. inversion H9. inversion H11. inversion H13.
                 apply t_sub with (T:=join (an (fn x0 x2) x3) H). simpl. apply t_sub with (T:=an (fn T0 x2) H). 
                  apply t_abs. apply t_sub with (T:=x1). apply H8. apply H12. apply subt_fn. apply sub_refl. apply H10.
                  apply subtyping_refl. destruct T. destruct r. simpl. inversion H15. simpl. apply subt_fn. apply sub_refl.
                 inversion H15. subst. apply H23. inversion H15. subst. apply H24.
                 subst. apply inversion_tcon in H0. inversion H0. inversion H1. inversion H3. inversion H4. inversion H6. subst.
                 inversion H4. inversion H7. inversion H10. inversion H12. subst. simpl. apply t_con.
Case ("t_con"). intros. inversion H1.
Case ("t_abs"). intros. inversion H1.
Case ("t_app"). intros. inversion H1. 
                subst. apply inversion_tabs in H0_.  inversion H0_. inversion H0. inversion H2. inversion H3.
                inversion H4. inversion H7. inversion H9. inversion H11. inversion H13.
                apply t_sub with (T:=join T2 x3). apply t_sub with (T:=join T2 b0). 
                apply t_prot with (T:=T2).
                apply substitution_preserves_typing with (T1:=T). 
                apply t_sub with (T:= x0). apply t_sub with (T:=T1).
                apply H0_0. inversion H15. subst. apply H23. apply H10. apply t_sub with (T:=x2). apply t_sub with (T:=x1).
                apply H8. apply H12. inversion H15. subst. apply H24. reflexivity. apply subtyping_join. apply H14. apply subtyping_join.
                inversion H15. subst. apply H20. 
                subst. apply t_app with (T1:=T1)(T2:=T2)(b:=b).
                apply IHhas_type1 with (t':=t1')in H5. apply H5.
                reflexivity. apply H0_0. reflexivity. subst.
                apply t_app with (T1:=T1)(T2:=T2)(b:=b). apply H0_.
                apply IHhas_type2 with (t':=t2') in H6. apply H6.
                reflexivity. reflexivity.
Case ("t_sub"). subst. intros. apply t_sub with (T:=T).
                apply IHhas_type. reflexivity. apply H2. apply H1.
Qed.

Theorem type_uniqueness:forall T t t',
        has_type empty_context t T ->
        t ==>*t' ->
        has_type empty_context t' T.
Proof. intros. induction H1. apply H0. apply IHmulti.
       apply preservation with (t':=y)in H0. apply H0. 
       apply H1. Qed.
(*###########end##########*)
(*#########progress#########*)
Theorem progress: forall t T,
has_type empty_context t T ->
value t \/ (exists t', t ==> t').
Proof. intros. remember (@empty_context) as context. induction H0.
Case ("t_var"). 
                subst. inversion H0.
Case ("t_prot").
                right. subst. assert (A: empty_context = empty_context). reflexivity.
                apply IHhas_type in A. inversion A. inversion H1. subst. destruct b.
                exists (tcon n b0). apply st_protL. apply v_c. exists (tcon n H).
                apply st_protHc. subst. destruct b. exists (tabs (Id n) T0 e b0).
                apply st_protL. apply v_f. exists (tabs (Id n) T0 e H). apply st_protHf.
                inversion H1. exists (tprot b x). apply st_prot. apply H2.
Case ("t_con").
                left. apply v_c.
Case ("t_abs").
                left. destruct x. apply v_f.
Case ("t_app").
                right. subst.  assert (A: empty_context = empty_context). reflexivity.
                assert (B: empty_context = empty_context). apply A. apply IHhas_type1 in A.
                apply IHhas_type2 in B. inversion A. inversion B. inversion H0. subst.
                inversion H1. subst. apply inversion_tcon in H0_.  inversion H0_. inversion H2.
                inversion H3. inversion H4. inversion H6. inversion H8. rewrite->H7 in H10. inversion H10.
                apply inversion_tcon in H0_. inversion H0_. inversion H3. inversion H4. inversion H5. inversion H7.
                inversion H9. rewrite->H8 in H11. inversion H11.
                inversion H1.
                subst. exists (tprot b0 ([(Id n) := tcon n0 b1](e))). apply st_appabs. apply v_c.
                subst. exists (tprot b0 ([(Id n):= tabs (Id n0) T0 e0 b1](e))). apply st_appabs.
                apply v_f. inversion H1. exists (tapp t1 x). apply st_app2. apply H0. apply H2.
                inversion H0. exists (tapp x t2). apply st_app1. apply H1.
Case ("t_sub"). subst. apply IHhas_type. reflexivity.
                
Qed.
(*##########determinism#########*)
Theorem determinism: forall t t' t'',
t ==> t'  ->
t ==> t'' ->
t' = t''.
Proof. intros t. induction t.
Case ("tvar").
             intros. inversion H0.
Case ("tprot").
             intros. inversion H0. subst.  inversion H1. subst.
             apply IHt with (t':=t')(t'':=t'0)in H6. subst. reflexivity.
             apply H5. subst. inversion H6. subst. inversion H5. subst.
             inversion H5. subst. inversion H5. subst. inversion H5.
             subst. inversion H1. subst. inversion H0. subst.
             apply IHt with (t':=t'1)(t'':=t'0) in H7. subst. reflexivity.
             apply H6. subst. inversion H5. subst. inversion H6. subst. inversion H6.
             reflexivity. subst. inversion H1. subst. inversion H5. reflexivity. subst.
             inversion H1. inversion H5. reflexivity.
Case ("tcon").
             intros. inversion H0.
Case ("tabs"). 
             intros. inversion H0.
Case ("tapp"). 
             intros. inversion H0. inversion H1. subst. inversion H6. subst. reflexivity.
             subst. inversion H9. subst. inversion H5. subst. inversion H10. subst.
             inversion H10. subst. inversion H1. subst. inversion H5. subst.
             apply IHt1 with (t':=t1')(t'':=t1'0) in H5. subst. reflexivity. apply H6.
             subst. inversion H4. subst. inversion H5. subst.  inversion H5. subst.
             inversion H1. subst. subst. inversion H7. subst. inversion H6. subst.
             inversion H6. subst. inversion H4. subst. inversion H7. subst. inversion H7.
             subst. apply IHt2 with (t':=t2')(t'':=t2'0) in H6. subst. reflexivity.
             apply H8. 
Qed.
(*############soundness############*)
Corollary soundness : forall t t' T,
  has_type empty_context t T -> 
  t ==>* t' ->
 ~((~exists t, t' ==> t)/\(~ value t')).
Proof.
intros. remember (@empty_context) as context.  
generalize dependent T. induction H1.
Case ("multi_step").
     intros. subst. intros contra. inversion contra.
     apply progress in H0. inversion H0.
     SCase ("left"). apply H2 in H3. inversion H3.
     SCase ("right"). apply contra in H3. inversion H3.
Case ("multi_ref"). subst. intros. apply IHmulti with (T:=T).
     apply preservation with (t':=y)in H2.  apply H2. 
     apply H0.
Qed.

(*##########################*)

End SecLang.

Module LowLang.

Inductive tm : Type :=
|tvar : id -> tm
|tcon : nat -> tm
|tabs : id -> Ty -> tm -> tm
|tapp : tm -> tm -> tm
(**
tH is used to replace all high security
terms. It can have any high security type
*)
|tH   : tm.

Inductive value : tm -> Prop :=
| v_c : forall n,
       value (tcon n)
| v_f : forall n T e,
       value (tabs (Id n) T e)
| v_H : value tH.

Fixpoint subst (x:id) (s:tm) (t:tm): tm :=
  match t with
(*variables*)
  | tvar x' => 
      if beq_id x x' then s  else t
(*abstractions*)
  | tabs x' T t1  => 
      tabs x' T (if beq_id x x' then t1 else (subst x s t1)) 
(*constants*)
  | tcon n  => tcon n 
(*applications*)
  | tapp t1 t2 => 
      tapp (subst x s t1) (subst x s t2)
(*high security term replacement*)
  | tH => 
      tH
  end.
Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Inductive step : tm  -> tm  -> Prop :=
| st_Happ: forall v,
  value v ->
  tapp tH v ==> tH
| st_appabs: forall x T e v,
  value v ->
  tapp (tabs x T e) v ==>  [x := v]e 
| st_app1: forall t1 t1' t2,
  t1  ==> t1'  ->
  tapp t1 t2  ==> tapp t1' t2 
| st_app2: forall v1 t2 t2',
  value v1 ->
  t2  ==> t2'  ->
  tapp v1 t2  ==> tapp v1 t2' 

where "t1  '==>' t2 " := (step t1 t2).

Definition multistep := (multi step).
Notation "t1  '==>*' t2" := (multistep t1 t2) 
  (at level 40).

Definition join (T:Ty) (b:Sec): Ty :=
 match b with
 | L => T
 | H => match T with
        | an R b => an R H
        end
 end.

Inductive has_type : context  -> tm -> Ty -> Prop :=
| t_H: forall Gamma rt,
  has_type Gamma tH (an rt H)
| t_var: forall Gamma n T,
  Gamma (Id n) = Some T ->
  has_type Gamma (tvar (Id n)) T
| t_con: forall Gamma n,
  has_type Gamma (tcon n) (an int L)
| t_abs: forall Gamma T1 T2 e x,
  has_type (Cupdate Gamma x (Some T1)) e T2 ->
  has_type Gamma (tabs x T1 e) (an (fn T1 T2) L)
| t_app: forall Gamma T1 T2 T2' t1 t2 b,
  has_type Gamma t1 (an (fn T1 T2) b) ->
  has_type Gamma t2 T1 ->
  T2' = join T2 b ->
  has_type Gamma (tapp t1 t2) T2'
| t_sub: forall Gamma t T T',
  has_type Gamma t T ->
  T < T' ->
  has_type Gamma t T'.
(**
Note the [t_sub] in [LowLang] is necessary,
consider the following application:
tapp (tabs (Id 0)(an int H)(tvar (Id 0)))(tcon 1) 
which an application of an abstraction with high level input to 
a low level constant. 
Since there is no obvious reason why this should not disallowed,
we have to introduce "subtyping" into [LowLang]
*)
(*#######inversions of [has_type]##########*)
(*inversion of [has_type Gamma (tvar x) T]*)
Lemma inversion_tvar: forall Gamma x T,
has_type Gamma (tvar x) T ->
exists T0, (Gamma x = Some T0)/\(T0 < T).
Proof. intros. remember (tvar x) as t. induction H0.
inversion Heqt. inversion Heqt. subst. exists T. split. 
apply H0. apply subtyping_refl.
inversion Heqt. inversion Heqt. inversion Heqt. apply IHhas_type in Heqt.
inversion Heqt. exists x0. split. inversion H2. apply H3. inversion H2.
apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl. apply H4.
apply H1.
Qed.

(*inversion of [has_type Gamma (tabs x T1 e b) T]*)
Lemma inversion_tabs: forall Gamma x T1 T e,
has_type Gamma (tabs x T1 e) T ->
exists T1', exists T2, exists T2', exists b',
(has_type Gamma (tabs x T1 e) (an (fn T1 T2) L)) /\
(has_type (Cupdate Gamma x (Some T1)) e T2) /\
(T1'<T1)/\(T2<T2')/\(subsum_r L b')/\((an (fn T1' T2') b') < T).
Proof. intros. remember (tabs x T1 e) as t. induction H0. inversion Heqt. inversion Heqt. inversion Heqt.
inversion Heqt. subst. exists T1. exists T2. exists T2. exists L. split. apply t_abs in H0. apply H0.
split. apply H0. split. apply subtyping_refl. split. apply subtyping_refl. split. apply sub_refl. apply subtyping_refl.
inversion Heqt.  apply IHhas_type in Heqt. inversion Heqt. exists x0. inversion H2. exists x1. inversion H3. exists x2.
inversion H4. exists x3. inversion H5. split. apply H6. inversion H7. split. apply H8. split. inversion H9. apply H10.
split. inversion H9. inversion H11. apply H12. split. inversion H9. inversion H11. inversion H13. apply H14. inversion H9.
inversion H11. inversion H13. apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl. apply H15. apply H1.
Qed.

(*inversion of [has_type Gamma (tcon n b) T]*)

Lemma inversion_tcon: forall Gamma T n,
has_type Gamma (tcon n) T ->
exists T', exists T'', exists b', (T' = an int L)/\(T'' = an int b')/\(subsum_r L b')/\(T'' < T).
Proof. intros. remember (tcon n) as t. induction H0.
inversion Heqt. inversion Heqt. inversion Heqt. subst. exists (an int L). exists (an int L).
exists L. split. reflexivity. split. reflexivity. split. apply sub_refl. apply subtyping_refl.
inversion Heqt. inversion Heqt.  apply IHhas_type in Heqt. inversion Heqt. exists x. inversion H2.
exists x0. inversion H3. exists x1. 
inversion H4. split. apply H5. inversion H6. split. apply H7. inversion H8. split. apply H9. 
apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl. apply H10. apply H1.
Qed.
(*inversion of [has_type Gamma tH T]*)
Lemma inversion_tH:forall Gamma T,
has_type Gamma tH T ->
exists r,
(an r H) < T.
Proof. intros. remember tH as t. induction H0. exists rt. apply subtyping_refl.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. apply IHhas_type in Heqt.
inversion Heqt. exists x. apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl.
apply H2. apply H1. Qed.
(*inversion of [has_type Gamma (tapp t1 t2) T]*)
Lemma inversion_tapp: forall Gamma t1 t2 T2,
has_type Gamma (tapp t1 t2) T2 ->
exists T1', exists T2', exists b', exists T1'', exists T1''', exists T2'', exists b'',
has_type Gamma t1 (an (fn T1' T2') b')/\((an (fn T1' T2') b')<(an (fn T1'' T2'') b''))/\
(has_type Gamma t2 T1''')/\(T1''' < T1'') /\
((join T2'' b'') < T2).
Proof. intros. remember (tapp t1 t2) as t. induction H0.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. subst. exists T1.
exists T2. exists b. exists T1. exists T1. exists T2. exists b.
split. apply H0_. split. apply subtyping_refl. split. apply H0_0. split. apply subtyping_refl. 
apply subtyping_refl.
 apply IHhas_type in Heqt. inversion Heqt. exists x. inversion H2.
exists x0. inversion H3. exists x1. inversion H4. exists x2. inversion H5. exists x3. inversion H6. exists x4.
inversion H7. exists x5. inversion H8.  split. apply H9. inversion H10. split. apply H11. inversion H12.
split. apply H13. inversion H14. split. apply H15. apply subtyping_trans with (x:=T)(y:=T).
apply subtyping_refl. apply H16. apply H1. Qed.



(*some examples*)
Example test_has_type_1:
has_type empty_context (tabs (Id 0)(an int L)(tH)) (an (fn (an int L)(an int H)) L).
Proof. apply t_abs. apply t_H. Qed.
Example test_has_type_2:
has_type empty_context (tabs (Id 0)(an int L)(tcon 4)) (an (fn (an int L)(an int H)) H).
Proof. apply t_sub with (T:=an (fn (an int L)(an int L)) H). apply t_sub with (T:=an (fn (an int L)(an int L)) L).
apply t_abs. apply t_con. apply subt_fn. apply sub_LH. apply subtyping_refl. apply subtyping_refl.
apply subt_fn. apply sub_refl. apply subtyping_refl. apply subt_int. apply sub_LH.
Qed.
Example test_has_type_3:
has_type (Cupdate empty_context (Id 0) (Some (an int L))) (tvar (Id 0)) (an int H).
Proof. apply t_sub with (T:=an int L). apply t_var. rewrite->Cupdate_eq. reflexivity.
apply subt_int. apply sub_LH. Qed.
Example test_has_type_4:
has_type (Cupdate empty_context (Id 0) (Some(an (fn (an int H)(an int L)) L)))
         (tvar (Id 0)) (an (fn (an int L)(an int H)) H).
Proof. apply t_sub with (T:=an (fn (an int H)(an int L)) L). apply t_var. rewrite->Cupdate_eq. reflexivity.
apply subt_fn. apply sub_LH. apply subt_int. apply sub_LH. apply subt_int. apply sub_LH.
Qed.
Example test_has_type_5:
has_type empty_context (tcon 1) (an int H).
Proof. apply t_sub with (T:=an int L). apply t_con. apply subt_int. apply sub_LH.
Qed.
Example test_has_type_6:
has_type empty_context (tapp (tabs(Id 0)(an int H)(tvar (Id 0)))(tcon 1)) (an int H).
apply t_app with (T1:=an int H)(T2:=an int H)(b:=L).
apply t_abs. apply t_var. rewrite->Cupdate_eq. reflexivity. apply t_sub with (T:=an int L).
apply t_con. apply subt_int. apply sub_LH. reflexivity. Qed.
Example test_has_type_7:
has_type empty_context (tapp (tabs (Id 0)(an int H)(tvar (Id 0)))(tcon 1))(an int H).
Proof. apply t_app with (T1:=an int L)(T2:=an int H)(b:=L). apply t_sub with (T:=an (fn (an int H)(an int H)) L).
apply t_abs. apply t_var. rewrite->Cupdate_eq. reflexivity. apply subt_fn. apply sub_refl. apply subt_int. apply sub_LH.
apply subtyping_refl. apply t_con. reflexivity. Qed.
Example test_has_type_8:
has_type empty_context (tapp (tabs (Id 0)(an int L)(tvar (Id 0)))(tcon 1)) (an int H).
Proof. apply t_app with (T1:=an int L)(T2:=an int L)(b:=H). apply t_sub with (T:=an (fn (an int L)(an int L)) L).
apply t_abs. apply t_var. rewrite->Cupdate_eq. reflexivity. apply subt_fn. apply sub_LH. apply subtyping_refl.
apply subtyping_refl. apply t_con. reflexivity. Qed.
Example test_has_type_9:
has_type empty_context (tapp (tabs (Id 0)(an int H)(tvar (Id 0))) tH)(an int H).
Proof. apply t_app with (T1:=an int H)(T2:=an int H)(b:=L). 
apply t_abs. apply t_var. rewrite->Cupdate_eq. reflexivity. apply t_H. reflexivity. Qed.
Example test_has_type_10:
has_type (Cupdate empty_context (Id 0)(Some (an int H)))(tvar (Id 0))(an int H).
Proof. apply t_var. rewrite->Cupdate_eq. reflexivity. Qed.
Example test_has_type_11:
has_type empty_context (tabs (Id 0)(an int H)(tvar (Id 0))) (an (fn (an int H)(an int H)) L).
Proof. apply t_abs. apply t_var. rewrite->Cupdate_eq. reflexivity.
Qed.
Example test_has_type_12:
has_type empty_context (tapp tH (tcon 1)) (an int H).
Proof. apply t_app with (T1:=an int L)(T2:=an int L)(b:=H). apply t_H. apply t_con.
reflexivity. Qed.
Example test_has_type_13:
has_type (Cupdate empty_context (Id 0) (Some (an (fn (an int H)(an int L)) L))) (tapp (tvar (Id 0))(tcon 1))(an int H).
Proof. apply t_app with (T1:=an int L)(T2:=an int L)(b:=H).
       apply t_sub with (T:=an (fn (an int H)(an int L)) L).
       apply t_var. rewrite->Cupdate_eq. reflexivity. apply subt_fn. apply sub_LH.
       apply subt_int. apply sub_LH. apply subtyping_refl. apply t_con.
       reflexivity. Qed.
Example test_has_type_14:
has_type (Cupdate empty_context (Id 0) (Some (an (fn (an int H)(an int L)) L))) (tapp (tvar (Id 0))(tcon 1)) (an int L).
Proof. apply t_app with (T1:=an int H)(T2:=an int L)(b:=L). apply t_var. rewrite->Cupdate_eq.
reflexivity. apply t_sub with (T:=an int L). apply t_con. apply subt_int. apply sub_LH. reflexivity.
Qed.
       
Example test_has_type_15:
has_type empty_context (tapp (tapp tH (tcon 1))(tcon 2)) (an int H).
Proof. apply t_app with (T1:=an int L)(T2:=an int L)(b:=H). 
apply t_app with (T1:=an int L)(T2:=an (fn (an int L)(an int L)) L)(b:=H).
apply t_H. apply t_con. reflexivity. apply t_con. reflexivity.
Qed.
(*some counter examples*)
(*undefined variables*)
Example test_has_type_16:
~has_type empty_context (tvar (Id 0)) (an int L).
Proof. intros contra. apply inversion_tvar in contra. inversion contra.
inversion H0. inversion H1. Qed.
Example test_has_type_17:
~has_type (Cupdate empty_context (Id 1)(Some (an int L))) (tvar (Id 0)) (an int L).
Proof. intros contra. apply inversion_tvar in contra. inversion contra.
remember (beq_id (Id 1)(Id 0)) as BB. destruct BB. apply beq_id_eq in HeqBB. inversion HeqBB.
symmetry in HeqBB. apply Cupdate_neq with (T:=Some (an int L))(St:=empty_context) in HeqBB.
inversion H0. rewrite->HeqBB in H1. inversion H1. Qed.
(*abstractions with undefined variables*)
Example test_has_type_18:
~has_type empty_context (tabs (Id 0)(an int H)(tvar (Id 1))) (an (fn (an int H)(an int L)) L).
Proof. intros contra. apply inversion_tabs in contra. inversion contra. inversion H0. inversion H1.
inversion H2. inversion H3. inversion H5. apply inversion_tvar in H6. inversion H6. inversion H8.
remember (beq_id (Id 0)(Id 1)) as BB. destruct BB. apply beq_id_eq in HeqBB. inversion HeqBB.
symmetry in HeqBB. apply Cupdate_neq with (T:=Some (an int H))(St:=empty_context) in HeqBB. rewrite->HeqBB in H9.
inversion H9. Qed.
(*ill-typed abstractions*)
Example test_has_type_19:
~has_type empty_context (tabs (Id 0)(an int L)(tvar (Id 0))) (an (fn (an int H)(an int H)) H).
Proof. intros contra. apply inversion_tabs in contra. inversion contra. inversion H0. inversion H1.
inversion H2. inversion H3. inversion H5.  inversion H7. inversion H9. inversion H11. destruct x.
destruct r. destruct s. inversion H13. subst. inversion H21. inversion H16. inversion H8. inversion H16.
inversion H8. Qed.
Example test_has_type_20:
~has_type empty_context (tabs (Id 0)(an int H)(tvar (Id 0)))(an (fn (an int L)(an int L)) H).
Proof. intros contra. apply inversion_tabs in contra. inversion contra. inversion H0. inversion H1. inversion H2.
inversion H3. inversion H5. inversion H7. inversion H9. inversion H11. apply inversion_tvar in H6. inversion H6.
inversion H14. rewrite->Cupdate_eq in H15. inversion H15. subst. assert (an int H < x1). apply subtyping_trans with (x:=x0)(y:=x0).
apply subtyping_refl. apply H16. apply H10. destruct x1. destruct r. destruct s. inversion H17. inversion H20. inversion H13. subst.
inversion H26. inversion H20. inversion H17. Qed.
Example test_has_type_21:
~has_type empty_context (tabs (Id 0)(an int L)(tvar (Id 0)))(an int L).
Proof. intros contra. apply inversion_tabs in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H5.
inversion H7. inversion H9. inversion H11. inversion H13. Qed.
(*ill-typed constants*)
Example test_has_type_22:
~has_type empty_context (tcon 1) (an (fn (an int L)(an int L)) L).
Proof. intros contra. apply inversion_tcon in contra. inversion contra. inversion H0. inversion H1. inversion H2.
inversion H4. inversion H6. rewrite->H5 in H8. inversion H8. Qed.
(*ill-typed tH*)
Example test_has_type_23:
~has_type empty_context tH (an int L).
Proof. intros contra. apply inversion_tH in contra. inversion contra. destruct x.
inversion H0. inversion H3. inversion H0. Qed.
(*ill-matched applications*)
Example test_has_type_24:
~has_type empty_context (tapp (tabs (Id 0)(an int L)(tvar (Id 0))) tH) (an int H).
Proof. intros contra. apply inversion_tapp in contra. inversion contra. inversion H0.
       inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6.
       inversion H8. inversion H10. inversion H12. apply inversion_tH in H11. inversion H11.
       assert (an x6 H < x2). apply subtyping_trans with (x:=x3)(y:=x3). apply subtyping_refl.
       apply H15. apply H13. destruct x2. destruct r. destruct s. inversion H16. inversion H18.
       apply inversion_tabs in H7. inversion H7. inversion H17. inversion H18. inversion H19.
       inversion H20. inversion H22. inversion H24. inversion H26. inversion H28. destruct x2.
       destruct r. destruct s. destruct x.  destruct r. destruct s. inversion H9. inversion H38.
       inversion H42. inversion H30. inversion H38. inversion H42. inversion H30. inversion H38.
       inversion H25. inversion H33. inversion H25.   apply inversion_tabs in H7.
       inversion H7. inversion H17. inversion H18. inversion H19. inversion H20. inversion H22.
       inversion H24. inversion H26. inversion H28. destruct x2. destruct r. destruct s0. destruct x.
       destruct r. destruct s0. inversion H9. inversion H38. inversion H30. inversion H38. inversion H42.
       inversion H30. inversion H38. inversion H25. inversion H33. inversion H25.
Qed.
Example test_has_type_25:
~has_type empty_context (tapp (tabs (Id 0)(an int L)(tcon 1))(tabs (Id 0)(an int L)(tvar (Id 0))))(an int L).
Proof. intros contra. apply inversion_tapp in contra. inversion contra. inversion H0. inversion H1. inversion H2.
inversion H3. inversion H4. inversion H5. inversion H6. inversion H8. inversion H10. inversion H12. 
apply inversion_tabs in H7. apply inversion_tabs in H11. inversion H7. inversion H15. inversion H16. inversion H17.
inversion H18. inversion H20. inversion H22. inversion H24. inversion H26. destruct x6. destruct r. destruct s.
destruct x. destruct r. destruct s. destruct x2. destruct r. destruct s. inversion H11. inversion H29. inversion H30.
inversion H31. inversion H32. inversion H34. inversion H36. inversion H38. inversion H40. destruct x3. destruct r. 
inversion H42.  inversion H13. inversion H9. inversion H36. inversion H40. inversion H9. inversion H36. inversion H28.
inversion H36. inversion H40. inversion H28. inversion H36. inversion H23. inversion H31. inversion H23.
Qed.
(*false-applications*)
Example test_has_type_26:
~has_type empty_context (tapp (tcon 1)(tcon 2)) (an int L).
Proof. intros contra. apply inversion_tapp in contra.  inversion contra. inversion H0. inversion H1. inversion H2.
inversion H3. inversion H4. inversion H5. inversion H6. apply inversion_tcon in H7.
inversion H7. inversion H9. inversion H10. inversion H11.  inversion H13. inversion H15. rewrite->H14 in H17.
inversion H17.
Qed.
(*properties of the language*)
(*preservation*)
Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.
(*########################################*)
(*##########s_p_t_1##############*)
(*Firstly we use the following proposition to describe free variables*)
Inductive free_var : id -> tm -> Prop :=
| e_tvar : forall x,
      free_var x (tvar x)
| e_tapp1 : forall x e1 e2,
      free_var x e1 ->
      free_var x (tapp e1 e2)
| e_tapp2 : forall x e1 e2,
      free_var x e2 ->
      free_var x (tapp e1 e2)
| e_tabs : forall x y e T,
      y <> x ->
      free_var x e ->
      free_var x (tabs y T e).

(*some examples*)
Example test_free_var_1:
free_var (Id 0) (tvar (Id 0)).
Proof. apply e_tvar. Qed.
Example test_free_var_2:
free_var (Id 1) (tapp (tabs (Id 0)(an int L)(tvar (Id 0)))(tvar (Id 1))) .
Proof. apply e_tapp2. apply e_tvar. Qed.
Example test_free_var_3:
free_var (Id 1)(tabs (Id 0)(an int L)(tvar (Id 1))).
Proof. apply e_tabs. intros contra. inversion contra. apply e_tvar. Qed.
Example test_free_var_4:
free_var (Id 0) (tapp (tabs (Id 0)(an int L)(tvar (Id 0)))(tvar (Id 0))).
Proof. apply e_tapp2. apply e_tvar. Qed.
Example test_free_var_5:
free_var (Id 1) (tapp (tabs (Id 0)(an int L)(tvar (Id 1)))(tcon 1)).
Proof. apply e_tapp1. apply e_tabs. intros contra. inversion contra. apply e_tvar.
Qed.
Example test_free_var_6:
forall x n, ~free_var x (tcon n).
Proof. intros. intros contra. inversion contra. Qed.
Example test_free_var_7:
forall x,~free_var x tH.
Proof. intros. intros contra. inversion contra. Qed.
Example test_free_var_8:
forall x T e,~free_var x (tabs x T e).
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
Case ("e_tvar"). 
intros. apply inversion_tvar in H1. inversion H1. inversion H0.
        exists x0. apply H2.
Case ("e_tapp1").
intros.  apply inversion_tapp in H1. inversion H1. inversion H2. inversion H3. 
         inversion H4. inversion H5. inversion H6. inversion H7. inversion H8.
        apply IHfree_var with (T:=an (fn x0 x1) x2). apply H9.
Case ("e_tapp2").
intros. apply inversion_tapp in H1. inversion H1. inversion H2. inversion H3. inversion H4.
        inversion H5. inversion H6. inversion H7. inversion H8. inversion H10. inversion H12.
        apply IHfree_var with (T:=x4). apply H13. 
Case ("e_tabs").
intros.  apply inversion_tabs in H2. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6.
         inversion H8. apply IHfree_var in H9. inversion H9. exists x4. 
apply not_eq_beq_id_false in H0. apply Cupdate_neq with (T:=Some T)(St:=Gamma)in H0.
rewrite->H0 in H11. apply H11.
Qed.


Corollary term_typable_empty_closed: forall t T,
has_type empty_context t T ->
forall x, ~free_var x t.
Proof. intros t. induction t.
Case ("tvar").
intros. intros contra. apply inversion_tvar in H0. inversion H0.
        inversion H1. inversion H2.
Case ("tcon").
intros. intros contra. inversion contra.
Case ("tabs").
intros. apply inversion_tabs in H0. inversion H0. inversion H1. inversion H2. inversion H3. inversion H4.
        inversion H6. intros contra. inversion contra.  subst. 
        apply term_typable_empty_closed_1 with (T:=x1)(Gamma:=Cupdate empty_context i (Some t))in H14.
        inversion H14. apply not_eq_beq_id_false in H12. apply Cupdate_neq with (T:=Some t)(St:=empty_context)in H12.
        rewrite->H12 in H9. inversion H9. apply H7.
Case ("tapp").
intros. intros contra. apply inversion_tapp in H0. inversion H0. inversion H1. inversion H2. inversion H3. inversion H4.
        inversion H5. inversion H6. inversion H7. inversion H9. inversion H11.
        inversion contra. subst.  apply IHt1 with (x:=x)in H8. apply H8 in H16.
        inversion H16. subst. apply IHt2 with (x:=x) in H12. apply H12 in H16. inversion H16.
Case ("tH").
intros. intros contra. inversion contra.
Qed.


Corollary change_context: forall Gamma Gamma' t T,
has_type Gamma t T ->
(forall x, free_var x t -> Gamma x = Gamma' x) ->
has_type Gamma' t T.
Proof.
intros. generalize dependent Gamma'. induction H0.
Case ("t_H").
intros. apply t_H.
Case ("t_var").
intros. apply t_var. rewrite<-H0. symmetry. apply H1.
apply e_tvar.
Case ("t_con"). 
intros. apply t_con.
Case ("t_abs").
intros. apply t_abs. apply IHhas_type. intros. remember (beq_id x x0) as BB.
        destruct BB.  apply beq_id_eq in HeqBB. rewrite->HeqBB. rewrite->Cupdate_eq.
        rewrite->Cupdate_eq. reflexivity. inversion HeqBB. symmetry in H4.
        apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in H4. rewrite->H4.
        inversion HeqBB. symmetry in H5. apply Cupdate_neq with (T:=Some T1)(St:=Gamma') in H5.
        rewrite->H5. clear H4. clear H5. apply H1. apply e_tabs. intros contra. rewrite->contra in HeqBB.
        rewrite<-beq_id_refl in HeqBB. inversion HeqBB. apply H2.
Case ("t_app").
intros. apply t_app with (T1:=T1)(T2:=T2)(b:=b). apply IHhas_type1. intros. apply H1. apply e_tapp1.
        apply H2. apply IHhas_type2. intros. apply H1. apply e_tapp2. apply H2. apply H0.
Case ("t_sub"). 
intros. apply t_sub with (T:=T). apply IHhas_type. apply H2. apply H1. 
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
intros. apply inversion_tvar in H1. inversion H1. inversion H2.
simpl. remember (beq_id x i) as BB.
destruct BB. apply beq_id_eq in HeqBB. rewrite->HeqBB in H3.
rewrite->Cupdate_eq in H3. inversion H3. subst. apply t_sub with (T:=x0).
 apply s_p_t_1. apply H0. apply H4.
symmetry in HeqBB. apply Cupdate_neq with (T:=Some T1)(St:=Gamma)in HeqBB.
rewrite->HeqBB in H3. destruct i. apply t_sub with (T:=x0). apply t_var. apply H3.
apply H4. 
Case ("tcon").
intros. simpl. apply inversion_tcon in H1. inversion H1. inversion H2. inversion H3. inversion H4.
inversion H6. inversion H8. rewrite->H7 in H10. destruct T2. destruct r. destruct s. apply t_con.
apply t_sub with (T:=an int L). apply t_con. apply subt_int. apply sub_LH. inversion H10.
Case ("tabs").
intros. simpl. remember (beq_id x i) as BB. destruct BB. apply inversion_tabs in H1.
inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H7.
inversion H9. inversion H11. inversion H13. destruct T2. destruct r. inversion H15.
assert (t0 < t). apply subtyping_trans with (x:=x0)(y:=x0). apply subtyping_refl. inversion H15. apply H23.
apply H10. apply t_sub with (T:=an (fn t t1) s).  destruct s. apply t_abs.
apply beq_id_eq in HeqBB. rewrite->HeqBB in H8.
assert (Cupdate Gamma i (Some t) = Cupdate (Cupdate Gamma i (Some T1)) i (Some t)).
apply functional_extensionality. intros. remember (beq_id i x4) as CC. destruct CC.
apply beq_id_eq in HeqCC. rewrite->HeqCC. rewrite->Cupdate_eq.
rewrite->Cupdate_eq. reflexivity. symmetry in HeqCC. inversion HeqCC. inversion HeqCC.
apply Cupdate_neq with (T:= Some t)(St:=Gamma ) in HeqCC. rewrite->HeqCC. 
apply Cupdate_neq with (T:= Some t)(St:=Cupdate Gamma i (Some T1)) in H18.
rewrite->H18. apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in H19. rewrite->H19.
reflexivity. rewrite->H17. apply t_sub with (T:=x2). apply t_sub with (T:=x1).
 apply H8. apply H12. inversion H15. apply H26. apply t_sub with (T:=an (fn t t1) L).
 apply t_abs. apply beq_id_eq in HeqBB. rewrite->HeqBB in H8.
assert (Cupdate Gamma i (Some t) = Cupdate (Cupdate Gamma i (Some T1)) i (Some t)).
apply functional_extensionality. intros. remember (beq_id i x4) as CC. destruct CC.
apply beq_id_eq in HeqCC. rewrite->HeqCC. rewrite->Cupdate_eq.
rewrite->Cupdate_eq. reflexivity. symmetry in HeqCC. inversion HeqCC. inversion HeqCC.
apply Cupdate_neq with (T:= Some t)(St:=Gamma ) in HeqCC. rewrite->HeqCC. 
apply Cupdate_neq with (T:= Some t)(St:=Cupdate Gamma i (Some T1)) in H18.
rewrite->H18. apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in H19. rewrite->H19.
reflexivity. rewrite->H17. assert (x1 < t1). apply subtyping_trans with (x:=x2)(y:=x2).
apply subtyping_refl. apply H12. inversion H15. apply H26. apply t_sub with (T:=x1).
apply H8. apply H18. apply subt_fn. apply sub_LH. apply subtyping_refl. apply subtyping_refl.
apply subt_fn. apply sub_refl. apply H16. apply subtyping_refl. 

apply inversion_tabs in H1. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5.
inversion H7. inversion H9. inversion H11. inversion H13. destruct T2. destruct r. destruct s.
inversion H15. inversion H15. destruct s. assert (t0<t). apply subtyping_trans with (x:=x0)(y:=x0).
apply subtyping_refl. inversion H15. apply H23. apply H10. apply t_sub with (T:=an (fn t t1) L).
apply t_abs.
apply IHe with (T1:=T1).  apply H0. assert (x1<t1). apply subtyping_trans with (x:=x2)(y:=x2).
apply subtyping_refl. apply H12. inversion H15. apply H25. apply t_sub with (T:=x1).
assert (Cupdate (Cupdate Gamma x (Some T1)) i (Some t) = Cupdate (Cupdate Gamma i (Some t)) x (Some T1)).
apply functional_extensionality. intros. remember (beq_id x x4) as AA.
remember (beq_id i x4) as BB. destruct AA. destruct BB. apply beq_id_eq in HeqAA.
apply beq_id_eq in HeqBB0. rewrite->HeqAA in HeqBB. rewrite->HeqBB0 in HeqBB.
rewrite<-beq_id_refl in HeqBB. inversion HeqBB. apply beq_id_eq in HeqAA. rewrite->HeqAA.
rewrite->Cupdate_eq. rewrite->HeqAA in HeqBB. symmetry in HeqBB. apply Cupdate_permute with (T1:=Some T1)(T2:=Some t)(X3:=x4)(f:=Gamma) in HeqBB.
rewrite->HeqBB. rewrite->Cupdate_eq. reflexivity. destruct BB. apply beq_id_eq in HeqBB0. rewrite->HeqBB0. rewrite->Cupdate_eq.
symmetry in HeqAA. apply Cupdate_permute with (T1:=Some T1)(T2:=Some t)(X3:=x4)(f:=Gamma) in HeqAA.
rewrite<-HeqAA. rewrite->Cupdate_eq. reflexivity. symmetry in HeqBB0. inversion HeqBB0.
apply Cupdate_neq with (T:=Some t)(St:=Cupdate Gamma x (Some T1))in HeqBB0.
rewrite->HeqBB0. symmetry in HeqAA. inversion HeqAA.
 apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in HeqAA.
rewrite->HeqAA. apply Cupdate_neq with (T:=Some T1)(St:=Cupdate Gamma i (Some t)) in H20.
rewrite->H20. apply Cupdate_neq with (T:=Some t)(St:=Gamma) in H19. rewrite->H19. reflexivity.
rewrite<-H18. apply H8. apply H17. apply subt_fn. apply sub_refl. apply H16. apply subtyping_refl.

apply t_sub with (T:=an (fn t0 t1) L). assert (t0<t). apply subtyping_trans with (x:=x0)(y:=x0).
apply subtyping_refl. inversion H15. apply H23. apply H10. apply t_sub with (T:=an (fn t t1) L).
apply t_abs.
apply IHe with (T1:=T1).  apply H0. assert (x1<t1). apply subtyping_trans with (x:=x2)(y:=x2).
apply subtyping_refl. apply H12. inversion H15. apply H25. apply t_sub with (T:=x1).
assert (Cupdate (Cupdate Gamma x (Some T1)) i (Some t) = Cupdate (Cupdate Gamma i (Some t)) x (Some T1)).
apply functional_extensionality. intros. remember (beq_id x x4) as AA.
remember (beq_id i x4) as BB. destruct AA. destruct BB. apply beq_id_eq in HeqAA.
apply beq_id_eq in HeqBB0. rewrite->HeqAA in HeqBB. rewrite->HeqBB0 in HeqBB.
rewrite<-beq_id_refl in HeqBB. inversion HeqBB. apply beq_id_eq in HeqAA. rewrite->HeqAA.
rewrite->Cupdate_eq. rewrite->HeqAA in HeqBB. symmetry in HeqBB. apply Cupdate_permute with (T1:=Some T1)(T2:=Some t)(X3:=x4)(f:=Gamma) in HeqBB.
rewrite->HeqBB. rewrite->Cupdate_eq. reflexivity. destruct BB. apply beq_id_eq in HeqBB0. rewrite->HeqBB0. rewrite->Cupdate_eq.
symmetry in HeqAA. apply Cupdate_permute with (T1:=Some T1)(T2:=Some t)(X3:=x4)(f:=Gamma) in HeqAA.
rewrite<-HeqAA. rewrite->Cupdate_eq. reflexivity. symmetry in HeqBB0. inversion HeqBB0.
apply Cupdate_neq with (T:=Some t)(St:=Cupdate Gamma x (Some T1))in HeqBB0.
rewrite->HeqBB0. symmetry in HeqAA. inversion HeqAA.
 apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in HeqAA.
rewrite->HeqAA. apply Cupdate_neq with (T:=Some T1)(St:=Cupdate Gamma i (Some t)) in H20.
rewrite->H20. apply Cupdate_neq with (T:=Some t)(St:=Gamma) in H19. rewrite->H19. reflexivity.
rewrite<-H18. apply H8. apply H17. apply subt_fn. apply sub_refl. apply H16. apply subtyping_refl.
apply subt_fn. apply sub_LH. apply subtyping_refl. apply subtyping_refl.
Case ("tapp").
intros. simpl. apply inversion_tapp in H1. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6. inversion H7.
inversion H8. inversion H10. inversion H12. inversion H14.  
apply t_sub with (T:=join x5 x6).
apply t_app with (T1:=x3)(T2:=x5)(b:=x6).
apply IHe1 with (T1:=T1). apply H0. apply t_sub with (T:=an (fn x3 x5) x2).
apply t_sub with (T:=an (fn x0 x5) x2). apply t_sub with (T:=an (fn x0 x1) x2).
apply H9. apply subt_fn. apply sub_refl. apply subtyping_refl. inversion H11. apply H25.
apply subt_fn. apply sub_refl. inversion H11. apply H24. apply subtyping_refl. apply subt_fn.
inversion H11. apply H21. apply subtyping_refl. apply subtyping_refl.  
apply IHe2 with (T1:=T1). apply H0. apply t_sub with (T:=x4). apply H13. apply H15.
reflexivity. apply H16. 
Case ("tH").
intros. simpl. apply inversion_tH in H1. inversion H1.
apply t_sub with (T:=an x0 H). apply t_H. apply H2.
Qed.
(*#######################end###################*)
Lemma subtyping_join:forall T b' b,
subsum_r b' b ->
join T b' < join T b.
Proof. intros. inversion H0. apply subtyping_refl. destruct T. simpl.
destruct r. destruct s. apply subt_int. apply sub_LH. apply subtyping_refl.
destruct s. apply subt_fn. apply sub_LH. apply subtyping_refl. apply subtyping_refl.
apply subtyping_refl. Qed.
Theorem preservation: forall t t' T,
has_type empty_context t T ->
t ==> t' ->
has_type empty_context t' T.
Proof. intros. generalize dependent t'. remember (@empty_context) as context.
 induction H0.
Case ("t_H"). intros. inversion H1.
Case ("t_var"). intros. inversion H1.      
Case ("t_con"). intros. inversion H1.
Case ("t_abs"). intros. inversion H1.
Case ("t_app").  intros. inversion H1. subst. apply inversion_tH in H0_. 
                inversion H0_. destruct b. inversion H0. inversion H7.
                destruct T2. simpl. apply t_H.
                subst. 
                apply substitution_preserves_typing with (T1:=T).
                apply inversion_tabs in H0_. inversion H0_.
                inversion H0. inversion H2. inversion H3. inversion H4.
                inversion H7. inversion H9. inversion H11. inversion H13.
                assert (T1<T). apply subtyping_trans with (x:=x0)(y:=x0).
                apply subtyping_refl. inversion H15. apply H23. apply H10.
                apply t_sub with (T:=T1). apply H0_0. apply H16.
                apply inversion_tabs in H0_. inversion H0_.
                inversion H0. inversion H2. inversion H3. inversion H4.
                inversion H7. inversion H9. inversion H11. inversion H13.
                destruct b. simpl. assert (x1<T2). apply subtyping_trans with (x:=x2)(y:=x2).
                apply subtyping_refl. apply H12. inversion H15. apply H24. apply t_sub with (T:=x1).
                apply H8. apply H16. apply t_sub with (T:=join T2 L). simpl.
                assert (x1<T2). apply subtyping_trans with (x:=x2)(y:=x2). apply subtyping_refl.
                apply H12. inversion H15. apply H24. apply t_sub with (T:=x1).
                apply H8. apply H16. apply subtyping_join. apply sub_LH.
                subst. 
                apply t_app with (T1:=T1)(T2:=T2)(b:=b).
                apply IHhas_type1 with (t':=t1')in H5. apply H5.
                reflexivity. apply H0_0. reflexivity.  subst.
                apply t_app with (T1:=T1)(T2:=T2)(b:=b). apply H0_.
                apply IHhas_type2 with (t':=t2') in H6. apply H6.
                reflexivity. reflexivity.
Case ("t_sub"). subst. intros. apply t_sub with (T:=T). apply IHhas_type. reflexivity.
                apply H2. apply H1. 
Qed.
(*###########end##########*)
(*#########progress#########*)
Theorem progress: forall t T,
has_type empty_context t T ->
value t \/ (exists t', t ==> t').
Proof. intros. remember (@empty_context) as context. induction H0.
Case ("t_H").
                left. apply v_H.
Case ("t_var"). 
                subst. inversion H0.
Case ("t_con").
                left. apply v_c.
Case ("t_abs").
                left. destruct x. apply v_f.
Case ("t_app").
                right. subst. assert (A: empty_context = empty_context). reflexivity.
                assert (B: empty_context = empty_context). apply A. apply IHhas_type1 in A.
                apply IHhas_type2 in B. inversion A. inversion B. inversion H0. subst.
                inversion H1. subst. apply inversion_tcon in H0_. inversion H0_. inversion H2.
                inversion H3. inversion H4. inversion H6. inversion H8. rewrite->H7 in H10.
                inversion H10. 
                subst. 
                apply inversion_tcon in H0_. inversion H0_. inversion H2. inversion H3.
                inversion H4. inversion H6. inversion H8. rewrite->H7 in H10. inversion H10.
                subst. 
                apply inversion_tcon in H0_. inversion H0_. inversion H2. inversion H3.
                inversion H4. inversion H6. inversion H8. rewrite->H7 in H10. inversion H10.
                subst.
                exists ([(Id n) := t2]e). apply st_appabs. apply H1.
                subst. exists tH. apply st_Happ. apply H1.
                inversion H1. exists (tapp t1 x). apply st_app2. apply H0. apply H2.
                inversion H0. exists (tapp x t2). apply st_app1. apply H1.
Case ("t_sub"). subst. apply IHhas_type. reflexivity.
Qed.
(*##########determinism#########*)
Theorem determinism: forall t t' t'',
t ==> t'  ->
t ==> t'' ->
t' = t''.
Proof. intros t. induction t.
Case ("tvar").
             intros. inversion H0. 
Case ("tcon").
             intros. inversion H0.
Case ("tabs"). 
             intros. inversion H0.
Case ("tapp"). 
             intros. inversion H0. inversion H1. subst. inversion H6. subst. reflexivity.
             subst. inversion H9. subst. inversion H5. subst. inversion H6. inversion H6.
             inversion H6. subst. inversion H9. subst. inversion H5. subst. inversion H10.
             subst. inversion H10. subst. inversion H10. subst. inversion H1. subst.
             reflexivity. inversion H6. subst. inversion H5. subst. inversion H7. subst.
             inversion H7. subst. inversion H7. subst. inversion H1. subst. inversion H5.
             subst. inversion H5. subst. 
             apply IHt1 with (t':=t1')(t'':=t1'0) in H5. subst. reflexivity. apply H6.
             subst. inversion H4. subst. inversion H5. subst.  inversion H5. subst.
             inversion H5. subst. inversion H1. subst. inversion H7. subst.
             inversion H6. subst. inversion H6. inversion H7. subst. inversion H6.
             subst. inversion H6. subst. inversion H6. subst. inversion H7. subst. inversion H6.
             subst. inversion H6. subst. inversion H6. subst. inversion H4. subst. inversion H7.
             subst. inversion H7. subst. inversion H7. subst.
            apply IHt2 with (t':=t2')(t'':=t2'0) in H6. subst. reflexivity.
             apply H8.
Case ("tH").
             intros. inversion H0. 
Qed.

Theorem determinism_extended:forall e v v',
LowLang.value v  ->
LowLang.value v' ->
multi LowLang.step e v  ->
multi LowLang.step e v' ->
v = v'.
Proof. intros. generalize dependent v'. induction H2.
intros. inversion H0. subst. inversion H3. reflexivity. inversion H2. subst.
inversion H3. reflexivity. inversion H2. subst. inversion H3. reflexivity.
inversion H2.
intros. apply IHmulti. apply H0. apply H3. inversion H4. subst. inversion H3. subst.
inversion H1. subst. inversion H1. subst. inversion H1. subst. apply determinism with (t':=y0)in H1.
subst. apply H6. apply H5. Qed.

(*############soundness############*) 
Corollary soundness : forall t t' T,
  has_type empty_context t T -> 
  t ==>* t' ->
 ~((~exists t, t' ==> t)/\(~ value t')).
Proof.
intros. remember (@empty_context) as context.  
generalize dependent T. induction H1.
Case ("multi_step").
     intros. subst. intros contra. inversion contra.
     apply progress in H0. inversion H0.
     SCase ("left"). apply H2 in H3. inversion H3.
     SCase ("right"). apply contra in H3. inversion H3.
Case ("multi_ref"). subst. intros. apply IHmulti with (T:=T).
     apply preservation with (t':=y)in H2.  apply H2. 
     apply H0.
Qed.

(*some additional lemmas for later use*)
Lemma multi_step_app1: forall t1 t1' t2,
t1 ==>* t1' ->
tapp t1 t2 ==>* tapp t1' t2.
Proof. intros. generalize dependent t2. induction H0.
Case ("multi_refl"). intros. apply multi_refl.
Case ("multi_step"). intros. assert (tapp x t2 ==> tapp y t2). 
                     apply st_app1. apply H0. specialize (IHmulti t2).
                     apply multi_step with (tapp y t2). apply H2. apply IHmulti.
Qed. 

Lemma multi_step_app2: forall v1 t2 t2',
value v1 ->
t2 ==>* t2' ->
tapp v1 t2 ==>* tapp v1 t2'.
Proof. intros. generalize dependent v1. induction H1.
Case ("multi_refl"). intros. apply multi_refl.
Case ("multi_step"). intros. assert (tapp v1 x ==> tapp v1 y). apply st_app2. apply H2.
                     apply H0. apply IHmulti in H2. apply multi_step with (tapp v1 y).
                     apply H3. apply H2.
Qed.
(*##########################*)
End LowLang.

Module Correspondence.

Fixpoint project (e : SecLang.tm) : LowLang.tm :=
match e with
(*variables*)
| SecLang.tvar x => LowLang.tvar x
(*constants*)
| SecLang.tcon n L => LowLang.tcon n
| SecLang.tcon n H => LowLang.tH
(*protects*)
(*| SecLang.tprot L e' => LowLang.tprot (project e')*)
(**
Note that [project (tprot L e')] should not return [tprot (project e')],for the
correspondance between [SecLang.step] and [LowLang.step] breaks down,
in [SecLang],
tapp(tabs x T e L) v ==> tprot L ([x:=v]e)
yet the following reduction relation is not defined in [LowLang]
tapp(tabs x T (project e))(project v) ==>* tprot (project ([x:=v]e))
instead we should have,
tapp (tabs x T (project e))(project v) ==>* [x:=project v](project e).

This is the main reason why "the project of a low protection should not yield another protection".
It leads to the consideration that [tprot] should be completely removed from [LowLang].
*)
(**
Also note that the above change also leads to 
some modification of the auxiliary lemmas specified by Lu
*)
| SecLang.tprot L e' => project e'
| SecLang.tprot H e' => LowLang.tH
(*abstractions*)
| SecLang.tabs x T e L => LowLang.tabs x T (project e) 
| SecLang.tabs x T e H => LowLang.tH
(*applications*)
| SecLang.tapp t1 t2 => LowLang.tapp (project t1)(project t2)
end.

Lemma corresp_typing: forall Gamma e T,
      SecLang.has_type Gamma e T ->
      LowLang.has_type Gamma (project e) T.
(**
Intuition,
a. suppose we have a term in [SecLang] of [H], then by [project],
   [project e] is equal to [tH] which can be typed freely in [LowLang]
b. suppose it is of [L] instead, the typing rule in [LowLang] is not
   different from that in [SecLang] regarding low security terms
Qed. 
*)
Proof. intros. induction H0.
Case ("t_var").
             simpl. apply LowLang.t_var. apply H0.
Case ("t_prot").
             subst. destruct b. simpl. apply IHhas_type. simpl.
             destruct T. apply LowLang.t_H.
Case ("t_con"). destruct b. simpl. apply LowLang.t_con. simpl. apply LowLang.t_H.
Case ("t_abs").
             destruct b. simpl. apply LowLang.t_abs. apply IHhas_type.
             simpl. apply LowLang.t_H.
Case ("t_app").
             subst. simpl. apply LowLang.t_app with (T1:=T1)(T2:=T2)(b:=b).
             apply IHhas_type1. apply IHhas_type2. reflexivity.
Case ("t_sub"). apply LowLang.t_sub with (T:=T). apply IHhas_type.
             apply H1.
Qed.


Lemma project_value:forall v,
SecLang.value v ->
LowLang.value (project v).
Proof. intros. inversion H0.
subst. destruct b. simpl. apply LowLang.v_c. simpl. apply LowLang.v_H.
subst. destruct b. simpl. apply LowLang.v_f. simpl. apply LowLang.v_H. Qed.


Lemma project_subst:forall x v e,
SecLang.value v ->
LowLang.subst x (project v)(project e) = project (SecLang.subst x v e).
Proof. intros. generalize dependent x. generalize dependent v. induction e.
Case ("tvar"). intros. simpl. remember (beq_id x i) as B. destruct B. reflexivity.
              simpl. reflexivity. 
Case ("tprot"). intros. simpl. destruct s. apply IHe. apply H0. simpl. reflexivity.
Case ("tcon"). intros. simpl. destruct s. simpl. reflexivity. simpl. reflexivity.
Case ("tabs"). intros. simpl. destruct s. remember (beq_id x i) as B. destruct B.
               apply beq_id_eq in HeqB. subst. simpl. rewrite<-beq_id_refl. reflexivity.
               simpl. rewrite<-HeqB. apply IHe with (x:=x) in H0. rewrite->H0. reflexivity.
               simpl. reflexivity.
Case ("tapp"). intros. simpl. assert (SecLang.value v). apply H0. apply IHe1 with (x:=x) in H0.
               apply IHe2 with (x:=x) in H1. rewrite->H0. rewrite->H1. 
               reflexivity.
Qed.



Lemma corresp_step : forall t t',
SecLang.step t t' ->
multi LowLang.step (project t)(project t').
Proof. intros. induction H0.
(**
Intuition,
a. according to [st_Happ] and [st_apabs] in [LowLang],
   we do not protect the result of the application with
   the label of the function being applied and as a consequence
   the typing rule w.r.t. [LowLang] is simpler and there are less
   steps regarding [st_appabs]
b. consider the following case,
in [SecLang],
tprot H (tcon n L) ==> tcon n H
while,
project (tprot H (tcon n L)) = tH = project (tcon n H)
thus we have,
in [LowLang],
tH ==>* tH
*)
Case ("prot").
                destruct b. simpl. apply IHstep.
                simpl. apply multi_refl.
Case ("protL").
                simpl. apply multi_refl.
Case ("protHf").
                simpl. apply multi_refl.
Case ("protHc").
                simpl. apply multi_refl.
Case ("appabs").
                destruct b. simpl.  
                apply multi_step with (y:= LowLang.subst x (project v)(project e)).
                apply LowLang.st_appabs. destruct v. inversion H0. inversion H0. simpl.
                destruct s. apply LowLang.v_c. apply LowLang.v_H. simpl. destruct s.
                destruct i. apply LowLang.v_f. apply LowLang.v_H. inversion H0.
                apply project_subst with (x:=x)(e:=e)in H0. rewrite->H0. apply multi_refl.
                simpl. apply multi_step with (y:=LowLang.tH). apply LowLang.st_Happ.
                destruct v. inversion H0. inversion H0. simpl. destruct s. apply LowLang.v_c.
                apply LowLang.v_H. destruct s. simpl. destruct i. apply LowLang.v_f. simpl.
                apply LowLang.v_H. inversion H0. apply multi_refl.
Case ("app1"). 
                simpl. apply LowLang.multi_step_app1 with (t2:=project t2)in IHstep.
                apply IHstep.
Case ("app2"). 
                simpl. apply LowLang.multi_step_app2 with (v1:=project v1)in IHstep.
                apply IHstep. destruct v1. inversion H0. inversion H0. destruct s. simpl. apply LowLang.v_c.
                simpl. apply LowLang.v_H. simpl. destruct s. destruct i. apply LowLang.v_f. apply LowLang.v_H.
                inversion H0.
Qed.


Lemma corresp_eval:forall e v,
SecLang.value v ->
multi SecLang.step e v ->
multi LowLang.step (project e)(project v).
Proof. intros. induction H1. apply multi_refl.
       apply corresp_step in H1. apply multi_trans with (y:=project y).
       apply H1. apply IHmulti. apply H0.
Qed.

(*security level of a term is different from that of its type*)
Lemma LowLang_high_term:forall v rt,
LowLang.value v ->
LowLang.has_type empty_context v (an rt H) ->
~LowLang.has_type empty_context v (an rt L) ->
v = LowLang.tH.
Proof.
intros. inversion H0.
Case ("tcon"). subst. apply LowLang.inversion_tcon in H1. inversion H1. inversion H3.
               inversion H4. inversion H5. inversion H7. inversion H9. rewrite->H8 in H11.
               destruct rt. assert (LowLang.has_type empty_context (LowLang.tcon n)(an int L)).
               apply LowLang.t_con. apply H2 in H12. inversion H12. inversion H11.
Case ("tabs"). subst. apply LowLang.inversion_tabs in H1. inversion H1. inversion H3. inversion H4.
               inversion H5. inversion H6. inversion H8. inversion H10. inversion H12. inversion H14.
               destruct rt. inversion H16. assert (LowLang.has_type empty_context (LowLang.tabs (Id n) T e)(an (fn t t0) L)).
               assert (x0<t0). apply subtyping_trans with (x:=x1)(y:=x1). apply subtyping_refl. apply H13. inversion H16. apply H25.
               apply LowLang.t_sub with (T:=an (fn t x0) L). assert (t<T). apply subtyping_trans with (x:=x)(y:=x). apply subtyping_refl.
               inversion H16. apply H25. apply H11. apply LowLang.t_sub with (T:=an (fn T x0) L). apply H7. apply subt_fn. apply sub_refl.
               apply H18. apply subtyping_refl. apply subt_fn. apply sub_refl. apply subtyping_refl. apply H17. apply H2 in H17. inversion H17.
Case ("tH"). reflexivity.
Qed.

Corollary NI_LowLang:forall e x v1 v2 rt,
LowLang.value v1 ->
LowLang.value v2 ->
LowLang.has_type empty_context v1 (an rt H) ->
LowLang.has_type empty_context v2 (an rt H) ->
~LowLang.has_type empty_context v1 (an rt L) ->
~LowLang.has_type empty_context v2 (an rt L) ->
LowLang.has_type (Cupdate empty_context x (Some (an rt H))) e (an int L) ->
LowLang.subst x v1 e = LowLang.subst x v2 e.
Proof. intros. apply LowLang_high_term with (rt:=rt) in H0. subst.
       apply LowLang_high_term with (rt:=rt) in H1. subst. reflexivity.
       apply H3. apply H5. apply H2. apply H4.
Qed.


Lemma LowLang_canonical_low_int:forall v,
LowLang.value v ->
LowLang.has_type empty_context v (an int L) ->
exists n, v = LowLang.tcon n.
Proof. intros. inversion H0.
Case ("tcon"). subst. exists n. reflexivity.
Case ("tabs"). subst. apply LowLang.inversion_tabs in H1. inversion H1.
               inversion H2. inversion H3. inversion H4. inversion H5.
               inversion H7. inversion H9. inversion H11. inversion H13.
               inversion H15.
Case ("tH"). subst. apply LowLang.inversion_tH in H1. inversion H1. inversion H2.
             inversion H4.
Qed.           

Lemma corresp_project_int:forall e n,
SecLang.value e ->
project e =LowLang.tcon n ->
e = SecLang.tcon n L.
Proof. intros. inversion H0.
Case ("tcon"). subst. destruct b. simpl in H1. inversion H1. 
               reflexivity. simpl in H1. inversion H1.
Case ("tabs"). subst. simpl in H1. destruct b. inversion H1.
               inversion H1.
Qed.

Definition return_sec (t : SecLang.tm) : option Sec :=
match t with
|SecLang.tcon n L =>Some L
|SecLang.tcon n H =>Some H
|SecLang.tabs x T e L =>Some L
|SecLang.tabs x T e H =>Some H
|SecLang.tprot b e =>None
|SecLang.tvar x =>None
|SecLang.tapp t1 t2 =>None
end.

Theorem NI:forall x e v1 v2 w1 w2 rt,
SecLang.value v1 ->
SecLang.value v2 ->
SecLang.value w1 ->
SecLang.value w2 ->
SecLang.has_type empty_context v1 (an rt H) ->
SecLang.has_type empty_context v2 (an rt H) ->
return_sec v1 = Some H ->
return_sec v2 = Some H ->
SecLang.has_type (Cupdate empty_context x (Some (an rt H))) e (an int L) ->
multi SecLang.step (SecLang.subst x v1 e) w1 ->
multi SecLang.step (SecLang.subst x v2 e) w2 ->
w1 = w2.
Proof. 
(**
Step_one: 
prove,
      project (subst x v1 e) = project (subst x v2 e)
Note that by [project_subst], the above goal canbe rearranged as follows,
      subst x (project v1)(project e) = subst x (project v2)(project e)
and by [NI_LowLang] we need the following to prove the goal,
a. value (project v1)
   value (project v2)
b. has_type empty_context (project v1)(an rt H)   
   has_type empty_context (project v2)(an rt H)
C. ~has_type empty_context (project v1) (an rt L)
   ~has_type empty_context (project v2) (an rt L)
d. has_type (Cupdate empty_context x (Some (an rt H))) (project e) (an int L).    
*)             
intros.
assert (SecLang.has_type empty_context v1 (an rt H)). apply H4.
assert (SecLang.has_type empty_context v2 (an rt H)). apply H5.
assert (SecLang.has_type empty_context v1 (an rt H)). apply H4.
assert (SecLang.has_type empty_context v2 (an rt H)). apply H5.
 apply corresp_typing in H4. apply corresp_typing in H5. 
assert (SecLang.has_type (Cupdate empty_context x (Some (an rt H))) e (an int L)).
apply H8.
assert (SecLang.has_type (Cupdate empty_context x (Some (an rt H))) e (an int L)).
apply H8.
 apply corresp_typing in H8.
assert (~LowLang.has_type empty_context (project v1) (an rt L)). intros contra.
destruct v1. simpl in H6. inversion H6. simpl in H6. inversion H6. destruct s.
simpl in H6. inversion H6. simpl in contra. apply LowLang.inversion_tH in contra.
inversion contra. inversion H17. inversion H19. inversion H22. destruct s. simpl in H6.
inversion H6. simpl in contra. apply LowLang.inversion_tH in contra. inversion contra.
inversion H17. inversion H19. inversion H22. simpl in H6. inversion H6.
assert (~LowLang.has_type empty_context (project v2) (an rt L)). intros contra.
destruct v2. simpl in H7. inversion H7. simpl in H7. inversion H7. destruct s. simpl in H7.
inversion H7. simpl in contra. apply LowLang.inversion_tH in contra. inversion contra. inversion H18.
inversion H20. inversion H23. destruct s. simpl in H7. inversion H7. simpl in contra. apply LowLang.inversion_tH in contra.
inversion contra. inversion H18. inversion H20. inversion H23. simpl in H7. inversion H7.
assert (SecLang.value v1). apply H0. assert (SecLang.value v2). apply H1.
apply project_value in H0. apply project_value in H1.
apply NI_LowLang with (e:=project e)(x:=x)(v1:=project v1)(v2:=project v2)(rt:=rt) in H0.
assert (LowLang.subst x (project v1)(project e) = project (SecLang.subst x v1 e)). apply project_subst. apply H19.
assert (LowLang.subst x (project v2)(project e) = project (SecLang.subst x v2 e)). apply project_subst. apply H20.
rewrite->H0 in H21. rewrite->H21 in H22. 
(**now we have,
project (SecLang.subst x v1 e) = project (SecLang.subst x v2 e)
multi LowLang.step (project (SecLang.subst x v1 e))(project w1)
multi LowLang.step (project (SecLang.subst x v2 e))(project w2)
*)

(**
Step two:
show that project w1 =project w2 by determinism in [LowLang]
*)
assert (SecLang.value w1). apply H2. assert (SecLang.value w2). apply H3.
assert (SecLang.value w1). apply H2. assert (SecLang.value w2). apply H3.
assert (SecLang.value w1). apply H2. assert (SecLang.value w2). apply H3.
apply corresp_eval with (e:=SecLang.subst x v1 e)in H2.
apply corresp_eval with (e:=SecLang.subst x v2 e)in H3.
apply project_value in H19. apply project_value in H20. rewrite->H22 in H2.
apply project_value in H23.
apply LowLang.determinism_extended with (e:=project (SecLang.subst x v2 e))(v:=project w1)(v':=project w2)in H23.
(**
Step three:
show that firstly 
exists n1, exists n2,
project w1 = tcon n1 and project w2 = ton n2
*)

apply SecLang.substitution_preserves_typing with (Gamma:=empty_context)(x:=x)(T2:=an int L)(e:=e)in H11.
apply SecLang.type_uniqueness with (t':=w1)in H11. apply corresp_typing in H11. apply project_value in H25.
apply LowLang_canonical_low_int in H25. inversion H25. apply corresp_project_int with (n:=x0)in H27.
rewrite->H27. 
apply SecLang.substitution_preserves_typing with (Gamma:=empty_context)(x:=x)(T2:=an int L)(e:=e)in H12.
apply SecLang.type_uniqueness with (t':=w2)in H12. apply corresp_typing in H12. apply project_value in H24.
apply LowLang_canonical_low_int in H24. inversion H24. apply corresp_project_int with (n:=x1)in H28.
rewrite->H28. 
rewrite->H27 in H23. rewrite->H28 in H23. simpl in H23. inversion H23. reflexivity.
apply H30. apply H12. apply H10. apply H15. apply H29. apply H11. apply H9. 
apply H15. apply project_value. apply H24. apply H2.  apply H3. apply H10. apply H9.
apply H1. apply H4. apply H5. apply H17. apply H18.  apply H8.
Qed. 



End Correspondence.

