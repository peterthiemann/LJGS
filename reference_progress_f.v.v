Require Export Ch10_Smallstep.

Inductive Sec : Type :=
| L : Sec
| H : Sec.

Inductive Ty : Type :=
| an : RawTy -> Sec -> Ty
with RawTy : Type :=
     | int  : RawTy
     | fn   : Ty -> Sec -> Ty -> RawTy
     | unit : RawTy
     | ref  : Ty -> RawTy.

Scheme Ty_mut := Induction for Ty Sort Prop
with RawTy_ := Induction for RawTy Sort Prop.

Check (an (fn (an int L) L (an int L)) L).
Check (an (fn (an int H) H (an int H)) H).
Check (an unit H).
Check (an unit L).
Check (an int H).
Check (an int L).
Check (an (ref (an int H))  L).
Check (an (ref (an unit L)) H).

(*###subtyping###*)
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

Reserved Notation "T '<:' U" (at level 40).
Inductive subtyping : Ty -> Ty -> Prop :=
| subt_int: forall b b',
           subsum_r b b' -> 
           (an int b) <: (an int b')
| subt_fn: forall b b' pc pc' T1 T1' T2 T2',
           subsum_r b b' ->
           subsum_r pc' pc ->
           T1' <: T1 ->
           T2  <: T2' ->
           (an (fn T1 pc T2) b) <: (an (fn T1' pc' T2') b')
| subt_unit: forall b b',
            subsum_r b b' ->
            (an unit b) <: (an unit b')
| subt_ref: forall b b' T,
            subsum_r b b' ->
            (an (ref T) b) <: (an (ref T) b')
where "t1  '<:' t2" := (subtyping t1 t2).

Lemma subtyping_refl: forall T,
T <: T.
Proof. apply (Ty_mut (fun T => T <: T) (fun RT => forall b, (an RT b) <: (an RT b))).
intros. apply H0.
intros. apply subt_int. apply sub_refl.
intros. apply subt_fn. apply sub_refl. apply sub_refl. apply H0. apply H1.
intros. apply subt_unit. apply sub_refl.
intros. apply subt_ref. apply sub_refl. 
Qed. 
       

Lemma subtyping_trans: forall y z x z',
x <: y -> z <: x -> y <: z' ->  z <: z'.
Proof. intros.  generalize dependent z. generalize dependent z'. induction H0.
Case ("int").
      intros. inversion H2. subst. inversion H1. subst. apply subt_int.  apply subsum_r_trans with (a:=b0)(b:=b)(c:=b')in H6.
       apply subsum_r_trans with (a:=b0)(b:=b')(c:=b'0) in H6. apply H6. apply H4. apply H0.
Case ("fn").
      intros. inversion H2. subst. inversion H3. subst. 
       apply subt_fn. apply subsum_r_trans with (a:=b0)(b:=b)(c:=b') in H13.
       apply subsum_r_trans with (a:=b0)(b:=b')(c:=b'0) in H13. apply H13. apply H8. apply H0.
       apply subsum_r_trans with (a:=pc'0)(b:=pc')(c:=pc)in H10.  apply subsum_r_trans with (a:=pc'0)(b:=pc)(c:=pc0)in H10.
       apply H10. apply H14. apply H1.
       apply IHsubtyping1. apply H15. apply H11.
       apply IHsubtyping2. apply H12. apply H16.
Case ("unit").
      intros. inversion H1. subst. inversion H2. subst. apply subt_unit.
      apply subsum_r_trans with (a:=b0)(b:=b)(c:=b')in H5. apply subsum_r_trans with (a:=b0)(b:=b')(c:=b'0)in H5.
      apply H5. apply H4. apply H0.
Case ("ref").
      intros. inversion H2. inversion H1. subst. apply subt_ref. 
      apply subsum_r_trans with (a:=b1)(b:=b)(c:=b')in H9. apply subsum_r_trans with (a:=b1)(b:=b')(c:=b'0)in H9.
      apply H9. apply H6. apply H0. 
Qed.
      
Example apply_trans: forall x y z,
x <: y -> y <: z -> x <: z.
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
subtyping (an (fn (an int H) H (an int L)) L)(an (fn (an int L) L (an int H)) H).
Proof. apply subt_fn. apply sub_LH. apply sub_LH. apply subt_int. apply sub_LH. apply subt_int. apply sub_LH.
Qed.
Example test_subtyping_4:
~subtyping (an int L) (an (fn (an int H) H (an int H)) H).
Proof. intros contra. inversion contra. Qed.
Example test_subtyping_5:
~subtyping (an (fn (an int L) L (an int H)) H)(an int L).
Proof. intros contra. inversion contra. Qed.
Example test_subtyping_6:
subtyping (an (fn (an int H) H (an int L)) L)(an (fn (an int L) L (an int L)) L).
Proof. apply subt_fn. apply sub_refl. apply sub_LH. apply subt_int.
       apply sub_LH. apply subt_int. apply sub_refl. 
       Qed.
Example test_subtyping_7:
subtyping (an unit L)(an unit H).
Proof. apply subt_unit. apply sub_LH. Qed.
Example test_subtyping_8:
~subtyping (an unit H)(an unit L).
Proof. intros contra. inversion contra. subst. inversion H2. 
       Qed.
Example test_subtyping_9:
~subtyping (an (fn(an int H) L (an int H)) H)(an (fn(an int H) H (an int L)) L).
Proof. intros contra. inversion contra. subst. inversion H5. Qed.
Example test_subtyping_10:
subtyping (an (ref (an int L)) L)(an (ref (an int L)) H).
Proof. apply subt_ref. apply sub_LH. Qed. 
Example test_subtyping_11:
~subtyping (an (ref (an int L)) H)(an (ref (an int L)) L).
Proof. intros contra. inversion contra. subst. inversion H1. Qed.
Example test_subtyping_12:
~subtyping (an (ref (an int L)) H)(an (ref (an (fn (an int L) H (an int L)) H)) H).
Proof. intros contra. inversion contra. Qed.



(*###end###*)

Inductive tm : Type :=
| tvar  : id -> tm 
| tprot : Sec -> tm -> tm
| tcon  : nat -> Sec -> tm
| tabs  : id -> Ty -> tm -> Sec -> tm
| tapp  : tm -> tm -> tm
(*#####new terms######*)
| tunit   : Sec -> tm
| tref    : Ty -> tm -> Sec -> tm (*[Ty] as the initial type*)
| tderef  : tm -> tm
| tloc    : Ty -> nat -> Sec -> tm(*[Ty] as the "access type"*)
| tassign : tm -> tm -> tm.
(**
Note: In this version, cast is not considered and 
      "current type" and "access type" are always the same
*)
Check (tvar (Id 0)).
Check (tprot H (tcon 1 L)).
Check (tprot H (tabs (Id 0)(an unit H)(tcon 1 H) L)).
Check (tcon 1 H).
Check (tcon 2 L).
Check (tabs (Id 0)(an (ref (an (fn (an int H) L (an int L)) L)) H)(tderef (tvar (Id 0))) L).
Check (tabs (Id 0)(an int L) (tvar (Id 1)) H).
Check (tabs (Id 0)(an int H)(tvar (Id 0)) L).
Check (tapp (tabs (Id 0)(an (ref (an (fn (an int L) L (an int L) ) L)) L)(tderef (tvar (Id 0))) L)(tloc (an (fn (an int L) L (an int L)) L) 1 L)).
Check (tapp (tabs (Id 0)(an unit L)(tvar (Id 0)) H) (tunit L)).
Check (tapp (tabs (Id 0)(an int H)(tvar (Id 0)) H)(tcon 1 H)).
Check (tunit L).
Check (tunit H).
Check (tref (an (fn (an int L) H (an int L)) L)(tabs (Id 0)(an int L)(tvar (Id 0)) L) H).
Check (tref (an int L)(tcon 1 L) L).
Check (tref (an (ref (an int H)) H)(tloc (an int H) 1 H) L).
Check (tderef (tloc (an (fn (an int L) L (an int L)) L) 1 L)).
Check (tderef (tloc (an int H) 1 H)).
Check (tassign (tloc (an int L) 1 L)(tcon 1 L)).
Check (tassign (tloc (an int L) 1 H)(tcon 1 L)).
Check (tassign (tloc (an int H) 1 L)(tcon 1 L)).
Check (tassign (tloc (an int H) 1 H)(tcon 1 L)).
(*###heaps###*)
Definition heap := list (tm*Ty).
Definition emp_hp:= @nil (tm*Ty).
(*###some useful functions###*)
(*###lookup function and some lemmas###*)
Fixpoint heap_lookup (n:nat)(st:heap):(option (tm*Ty)):=
  match st , n with
  | nil , _ =>None
  | h::t , 0 => Some h
  | h::t , S n' =>heap_lookup n' t
  end.
(*some tests below*)
(*#####################################################*)
Example heap_lookup_test1:
   heap_lookup 0 ((tcon 1 L , an int L)::(tunit H , an unit H)::(tunit L , an unit L)::nil) = 
                 Some (tcon 1 L , an int L).
Proof. simpl. reflexivity. Qed.
Example my_store_lookup_test2:
   heap_lookup 3 ((tcon 1 L, an int L)::(tloc (an int L) 1 H, an (ref (an int L)) H)::(tunit H, an unit H)::nil) 
                      = None.
Proof. simpl. reflexivity. Qed.
Example my_store_lookup_test3:
   heap_lookup 2 ((tcon 1 L, an int L)::(tcon 2 H, an int H)::(tcon 4 L, an int L)::nil) =
                      Some (tcon 4 L, an int L).
Proof. simpl. reflexivity. Qed.
(*extract the result of [heap_lookup]*)
Definition efst (p:option(tm*Ty)) : tm :=
 match p with
 | None => tvar (Id 100)
 | Some (t , T) => t
 end.
Definition esnd (p:option(tm*Ty)) : Ty :=
 match p with
 | None => an unit L
 | Some (t, T) => T
 end.
(*some tests*)
Example test_extract_1:
efst (Some (tcon 1 L , an int L)) = tcon 1 L.
Proof. simpl. reflexivity. Qed.
Example test_extract_2:
esnd (Some (tcon 1 L , an int L)) = an int L.
Proof. simpl. reflexivity. Qed.


Fixpoint snoc {A:Type} (l:list A) (x:A) : list A :=
  match l with
  | nil => x :: nil
  | h :: t => h :: snoc t x
  end.

Lemma length_snoc:forall A (l:list A) x,
  length (snoc l x) = S (length l).
Proof.
intros. generalize dependent x. induction l.
Case ("nil"). intros. simpl. reflexivity.
Case ("h::t"). intros. simpl. specialize (IHl x). rewrite->IHl.
              reflexivity.
Qed.

Lemma lt_snoc_1 : forall n m,
  S n <= S m -> n <= m.
Proof. 
  intros n m.  generalize dependent n.  induction m as [|m'].
Case ("m=0"). intros. destruct n as [|n'].
     SCase ("n=0"). apply le_n. 
     SCase ("n=S n'"). inversion H0. inversion H2.
Case ("m=S m'"). intros. inversion H0. apply le_n. apply le_S. 
                 apply IHm'. apply H2.
Qed.

Lemma lt_snoc: forall (l:heap) x (n:nat),
   n < length l ->
   heap_lookup n l = heap_lookup n (snoc l x).
Proof.
intros l. induction l.
Case ("nil"). intros.  simpl in H0. inversion H0.
Case ("h::t"). intros. simpl. destruct n. reflexivity. simpl. 
               apply IHl. simpl in H0. apply lt_snoc_1 in H0.
               apply H0.
Qed.

Lemma eq_snoc: forall (l:heap) x,
  heap_lookup (length l) (snoc l x) = Some x.
Proof.
intros l. induction l.
Case ("nil"). intros. simpl. reflexivity.
Case ("h::t"). intros. simpl. specialize (IHl x).
              apply IHl.
Qed.
(*###replace function and some lemmas###*)
Fixpoint heap_replace n x (l:heap): heap :=
  match l , n with
  | nil , _ =>nil
  | h::t , 0 => x::t
  | h::t , S n' =>h :: (heap_replace n' x t)
  end.

Lemma replace_nil: forall  n x,
  heap_replace n x nil = nil.
Proof. 
intros. destruct n. simpl. reflexivity. simpl. reflexivity. Qed.

Lemma length_replace: forall n x (l:heap),
  length (heap_replace n x l) = length l.
Proof.
intros. generalize dependent n. generalize dependent x. induction l.
Case ("nil"). intros. simpl.  rewrite->replace_nil. simpl. reflexivity.
Case ("h::t"). intros. simpl. destruct n. simpl. reflexivity. 
              simpl. specialize (IHl x n). rewrite->IHl. reflexivity.
Qed.

Lemma lookup_replace_eq: forall l t st,
  l < length st ->
  heap_lookup l (heap_replace l t st) = Some t.
Proof.
intros. generalize dependent l. generalize dependent t. 
induction st. 
Case ("nil"). intros. destruct l. simpl in H0. inversion H0. simpl in H0. inversion H0.
Case ("h::t"). intros. destruct l. simpl. reflexivity.
               simpl. apply IHst. simpl in H0. unfold lt. unfold lt in H0.
               apply lt_snoc_1 in H0. apply H0.
Qed.

Lemma lookup_replace_neq: forall l1 l2 t st,
  l1 <> l2 ->
  heap_lookup l1 (heap_replace l2 t st) = heap_lookup l1 st.
Proof.
intros. generalize dependent l1. generalize dependent l2. generalize dependent t.
induction st.
Case ("nil"). intros. rewrite->replace_nil. reflexivity.
Case ("h::t"). intros. destruct l2. destruct l1. simpl. assert (0=0). reflexivity.
               apply H0 in H1. inversion H1. simpl. reflexivity. simpl. 
               destruct l1. reflexivity. apply IHst.
               intros T. assert (l1 = l2 -> S l1 = S l2). intros. subst. reflexivity.
               apply H1 in T. apply H0 in T. inversion T.
Qed.
(*###########*)
(*###values###*)
Inductive value : tm -> Prop :=
| v_c : forall b n,
        value (tcon n b)
| v_f : forall n T e b,
        value (tabs (Id n) T e b)
| v_u : forall b,
        value (tunit b)
| v_l : forall n T b,
        value (tloc T n b).

(*###substitution###*)
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
(*units*)
  | tunit b => tunit b
(*tref*)
  | tref T t1 b => tref T (subst x s t1) b
(*tderef*)
  | tderef t1 => tderef (subst x s t1)
(*tloc*)
  | tloc T n b => tloc T n b
(*assignments*)
  | tassign t1 t2 => tassign (subst x s t1)(subst x s t2)
  end.
Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(*###some tests of [subst]###*)
Example test_subst_1:
[(Id 0) := tcon 1 H](tvar (Id 0)) = tcon 1 H.
Proof. simpl. reflexivity. Qed.
Example test_subst_2:
[(Id 0) := tloc (an int L) 0 H](tvar (Id 1)) = tvar (Id 1).
Proof. simpl. reflexivity. Qed.
Example test_subst_3:
[(Id 0) := tunit L](tprot H (tvar (Id 0))) = tprot H (tunit L).
Proof. simpl. reflexivity. Qed.
Example test_subst_4:
[(Id 0) := tabs (Id 0)(an int L)(tvar (Id 0)) L](tprot L (tunit L))
= tprot L (tunit L).
Proof. simpl. reflexivity. Qed.
Example test_subst_5:
[(Id 0) := tloc (an (ref (an int L)) L) 0 H](tcon 0 L) = tcon 0 L.
Proof. simpl. reflexivity. Qed.
Example test_subst_6:
[(Id 0) := tcon 0 H](tabs (Id 1)(an int L)(tvar (Id 0)) L)
= tabs (Id 1)(an int L)(tcon 0 H) L.
Proof. simpl. reflexivity. Qed.
Example test_subst_7:
[(Id 0) := tcon 0 L](tabs (Id 0)(an (ref (an unit H)) L)(tvar (Id 0)) H)
= tabs (Id 0)(an (ref (an unit H)) L)(tvar (Id 0)) H.
Proof. simpl. reflexivity. Qed.
Example test_subst_8:
[(Id 0) := tloc (an int L) 0 H](tapp (tabs (Id 0)(an (ref (an int L)) H)(tderef (tvar (Id 0))) L)(tvar (Id 0)))
= tapp (tabs (Id 0)(an (ref (an int L)) H)(tderef (tvar (Id 0))) L)(tloc (an int L) 0 H).
Proof. simpl. reflexivity. Qed.
Example test_subst_9:
[(Id 0) := tcon 0 H](tapp (tabs (Id 0)(an unit L)(tassign (tloc (an int H) 0 L)(tcon 0 H)) L)(tassign (tloc (an int L) 1 L)(tcon 1 L)))
= tapp (tabs (Id 0)(an unit L)(tassign (tloc (an int H) 0 L)(tcon 0 H)) L)(tassign (tloc (an int L) 1 L)(tcon 1 L)).
Proof. simpl. reflexivity. Qed.
Example test_subst_10:
[(Id 0) := tloc (an unit H) 0 H](tunit H) = tunit H.
Proof. simpl. reflexivity. Qed.
Example test_subst_11:
[(Id 0) := tcon 0 H](tref (an int H) (tvar (Id 0)) L) = tref (an int H) (tcon 0 H) L.
Proof. simpl. reflexivity. Qed.
Example test_subst_12:
[(Id 0) := tunit H](tref (an (ref (an int H)) H)(tloc (an int H) 0 H) L)
= tref (an (ref (an int H)) H) (tloc (an int H) 0 H) L.
Proof. simpl. reflexivity. Qed.
Example test_subst_13: 
[(Id 0) := tloc (an int H) 0 L](tderef (tvar (Id 0))) = tderef (tloc (an int H) 0 L) .
Proof. simpl. reflexivity. Qed.
Example test_subst_14:
[(Id 0) := tloc (an unit L) 0 H](tderef (tvar (Id 1))) = tderef (tvar (Id 1)).
Proof. simpl. reflexivity. Qed.
Example test_subst_15:
[(Id 0) := tcon 0 L](tloc (an int L) 0 L) = tloc (an int L) 0 L.
Proof. simpl. reflexivity. Qed.
Example test_subst_16:
[(Id 0) := tunit L](tassign (tloc (an unit L) 0 L)(tvar (Id 0)))
= tassign (tloc (an unit L) 0 L)(tunit L).
Proof. simpl. reflexivity. Qed.
Example test_subst_17:
[(Id 0) := tloc (an int H) 0 L](tassign (tvar (Id 0))(tcon 0 H)) =
tassign (tloc (an int H) 0 L)(tcon 0 H).
Proof. simpl. reflexivity. Qed.
Example test_subst_18:
[(Id 0) := tref (an int L)(tcon 0 L) L](tassign (tloc (an (ref (an int L)) L) 1 L)(tloc (an int L) 0 L)) =
tassign (tloc (an (ref (an int L)) L)  1 L)(tloc (an int L) 0 L).
Proof. simpl. reflexivity. Qed.

(*###reduction relation###*)
(*###"join" functions###*)
Definition joins (b1:Sec) (b2:Sec): Sec :=
 match b1 with
 | L => b2
 | H => H
 end.
(*some examples*)
Example test_joins_1:
 joins H L = H.
Proof. simpl. reflexivity. Qed.
Example test_joins_2:
 joins L H = H.
Proof. simpl. reflexivity. Qed.

Fixpoint joinVS (T:tm) (b:Sec): option tm :=
 match T , b with
 | tvar x , _ => None
 | tprot b e , _ => None
 | tcon n b , L => Some (tcon n b)
 | tcon n b , H => Some (tcon n H)
 | tabs x T e b , L => Some (tabs x T e b)
 | tabs x T e b , H => Some (tabs x T e H)
 | tapp t1 t2 , _ => None
 | tunit b , L => Some (tunit b)
 | tunit b , H => Some (tunit H)
 | tref T e b , _ => None
 | tderef e , _ => None
 | tloc T n b , L => Some (tloc T n b)
 | tloc T n b , H => Some (tloc T n H)
 | tassign t1 t2 , _ => None
 end.
(*############*)
Definition extract (t:option Ty) : Ty :=
match t with
| Some T => T
| None => an unit L (*default type*)
end.
Example test_Extract_1:
extract (Some (an int L))=an int L.
Proof. simpl. reflexivity. Qed.
Example test_Extract_2:
extract None = an unit L.
Proof. simpl. reflexivity. Qed.
(*############*)
Definition extractT (t:option tm) : tm :=
match t with
| Some e => e
| None => tvar (Id 100)
end.
Definition joinvs (T:tm) (b:Sec): tm :=
extractT (joinVS T b).
(*some examples*)
Example test_joinvs_1:
 joinvs (tcon 1 L) H = tcon 1 H.
Proof. simpl. reflexivity. Qed.
Example test_joinvs_2:
 joinvs (tcon 1 H) L = tcon 1 H.
Proof. simpl. reflexivity. Qed.
Example test_joinvs_3:
 joinvs (tabs (Id 0)(an int L)(tvar (Id 0)) L) H 
= tabs (Id 0)(an int L)(tvar (Id 0)) H.
Proof. simpl. reflexivity. Qed.
Example test_joinvs_4:
joinvs (tabs (Id 0)(an int H)(tvar (Id 0)) H) L =
tabs (Id 0)(an int H)(tvar (Id 0)) H.
Proof. simpl. reflexivity. Qed.
Example test_joinvs_5:
joinvs (tunit L) H = tunit H.
Proof. simpl. reflexivity. Qed.
Example test_joinvs_6:
joinvs (tunit H) L = tunit H.
Proof. simpl. reflexivity. Qed.
Example test_joinvs_7:
joinvs (tloc (an unit L) 0 L) H = tloc (an unit L) 0 H.
Proof. simpl. reflexivity. Qed.
Example test_joinvs_8:
joinvs (tloc (an int L) 0 H) L = tloc (an int L) 0 H.
Proof. simpl. reflexivity. Qed.

Definition joinTs (T:Ty)(b:Sec) : Ty :=
 match T , b with
 | an rt s , L => an rt s
 | an rt s , H => an rt H
 end.
Example test_joinTs_1:
joinTs (an int L) H = an int H.
Proof. simpl. reflexivity. Qed.
Example test_joinTs_2:
joinTs (an unit H) L = an unit H.
Proof. simpl. reflexivity. Qed.
Example test_joinTs_3:
joinTs (an (fn (an int L) L (an int H)) L) H = 
an (fn (an int L) L (an int H)) H.
Proof. simpl. reflexivity. Qed.
Example test_joinTs_4:
joinTs (an (ref (an unit H)) H) L =
an (ref (an unit H)) H.
Proof. simpl. reflexivity. Qed.
(*"get-label" functions*)
Definition Label (t:tm) : option Sec :=
 match t with
 | tvar x => None
 | tprot b t => None
 | tcon n b => Some b
 | tabs x T e b => Some b
 | tapp t1 t2 => None
 | tunit b => Some b
 | tref T e b => None
 | tderef e => None
 | tloc T n b => Some b
 | tassign t1 t2 => None
 end.
Definition eLabel (s:option Sec) : Sec :=
 match s with
 | Some s' => s'
 | None => L
 end.
Definition label (t:tm) : Sec :=
eLabel (Label t).
(*some tests of [label]*)
Example test_label_1:
label (tcon 1 H) = H.
Proof. simpl. reflexivity. Qed.
Example test_label_2:
label (tabs (Id 0)(an int H)(tvar (Id 0)) L) = L.
Proof. simpl. reflexivity. Qed.
Example test_label_3:
label (tunit L) = L.
Proof. simpl. reflexivity. Qed.
Example test_label_4:
label (tloc (an unit H) 0 H) = H.
Proof. simpl. reflexivity. Qed. 

Definition labelT (T:Ty) : Sec:=
match T with
 | an rt b => b
end.
(*some examples of [labelT]*)
Example test_labelT_1:
labelT (an int L) = L.
Proof. simpl. reflexivity. Qed.
Example test_labelT_2:
labelT (an unit H) = H.
Proof. simpl. reflexivity. Qed.
Example test_labelT_3:
labelT (an (fn (an int L) H (an int L)) L) = L.
Proof. simpl. reflexivity. Qed.
Example test_labelT_4:
labelT (an (ref (an unit L)) H) = H.
Proof. simpl. reflexivity. Qed.


(*##########*)
Reserved Notation "t1 '/' hp '==' PC '=>' t2 '/' hp'"
  (at level 40, hp at level 39, t2 at level 39, PC at level 39).

(**
Note: [PC],the security context, indicates the security level of
      information uncovered by merely taking control.
      In the presence of side-effect, just being able to observe an object
      take control can tell for instance the trace of the execution upto now
      and hence open door to security violations.
      To avoid this, [PC] should be considered as the lower bound of any
      side-effect.
*)

Inductive step : tm * heap -> Sec -> tm * heap -> Prop :=
  | st_prot: forall b PC t t' hp hp',
         t / hp == (joins PC b) => t' / hp' ->
        tprot b t / hp == PC => tprot b t' / hp'
 (**
  Note: In the presence of side effects, [tprot] restricts the "lower bound"
        so that it is at least as high as the protected level
 *)
  | st_protv: forall b v hp PC,
         value v ->
         tprot b v / hp == PC => joinvs v b / hp
  | st_appabs: forall x T e b PC hp v,
         value v ->
         tapp (tabs x T e b) v / hp == PC => tprot b ([x := v]e) / hp
  (**
   Note: substitution itself carries zero side-effect and this is why
         the substitution term on the right side of the reduction is not
         protected by [PC]
  *)
  | st_app1: forall t1 t1' t2  PC hp hp',
         t1 / hp == PC => t1' / hp' ->
         tapp t1 t2 / hp == PC => tapp t1' t2 / hp'
  | st_app2: forall v1 t2 t2' PC hp hp',
         value v1 ->
         t2 / hp == PC => t2' / hp' ->
         tapp v1 t2 / hp == PC => tapp v1 t2' / hp'
  | st_refv: forall T v v' b PC hp hp',
         value v ->
         v' = joinvs v PC ->
         hp' = snoc hp (v',T) ->
         tref T v b / hp == PC => tloc T (length hp) b / hp'
  (**
  Note: observe the following points regarding [st_refv],
        a. directly after allocation access type, the one indicated in [tloc],
           is the same as current type stored in the heap. In fact, in the
           absence of cast, they are always the same
        b. the value written into the heap should be guarded by the security 
           context since the cell being written should be at least as secure
           as [PC]
  *)
  | st_ref: forall T t t' b PC hp hp',
          t / hp == PC => t' / hp' ->
          tref T t b / hp == PC => tref T t' b / hp'
  | st_derefloc: forall T n b PC hp t,
          n < length hp ->
          t = efst (heap_lookup n hp) ->
          tderef (tloc T n b) / hp == PC => tprot b t / hp
 (**
  Note: when reading from the heap, the cell being read has to be
        guarded by the security level of the pointer by which it 
        is referred
        also that the type of the cell being read is equal to the
        "access type" indicated in [tloc]
  *)
  | st_deref: forall t t' hp hp' PC,
          t / hp == PC => t' / hp' ->
          tderef t / hp == PC => tderef t' / hp'
  | st_assign: forall v v' T T' n b PC hp hp',
          n < length hp ->
          value v ->
          subsum_r (joins PC b) (label (efst (heap_lookup n hp))) ->
          T' = joinTs T (joins PC b) ->
          v' = joinvs v (joins PC b) ->
          hp' = heap_replace n (v',T') hp ->
          tassign (tloc T n b) v / hp == PC => tunit PC / hp'
  (**
   Note: some important points regarding [st_assign],
         a. the new cell being written is guarded both by the security context 
            and the security level of the pointer
         b. within the pair, since the "current type" should be the same as that
            of the value, the type of the cell being written is also guarded
            by the security context and the security level of the pointer
         c. to prevent "updating a loction under high context", we have to make
            sure that the security level of the original cell before the assignment
            is guarded both by security context and the security level of the pointer
         d. we assume that [PC] is propogated to the result of the reduction. This is 
            just a matter of choice: it is perfectly ok if we let the security level
            of the "current type" in the heap after assignment to be that of [tunit]
  *)
  | st_assign1: forall t1 t1' t2 PC hp hp',
          t1 / hp == PC => t1' / hp' ->
          tassign t1 t2 / hp == PC => tassign t1' t2 / hp'
  | st_assign2: forall v1 t2 t2' PC hp hp',
          value v1 ->
          t2 / hp == PC => t2' / hp' ->
          tassign v1 t2 / hp == PC => tassign v1 t2' / hp'
 

where "t1 '/' hp '==' PC '=>' t2 '/' hp'" := (step (t1,hp) PC (t2,hp')).

(*###multi-step reduction###*)
Definition Relation (X: Type) := X->Sec->X->Prop.
Inductive Multi {X:Type} (R: Relation X) : Relation X :=
  | Multi_refl  : forall (x : X)(b : Sec), Multi R x b x
  | Multi_step : forall (x y z : X)(b : Sec),
                    R x b y ->
                    Multi R y b z ->
                    Multi R x b z.

Definition Multistep := (Multi step).
Notation "t1 '/' hp '==' PC '=>*' t2 '/' hp'" := (Multistep (t1,hp) PC (t2,hp')) 
  (at level 40, hp at level 39, t2 at level 39, PC at level 39).


(*###some tests of [step]###*)
Example test_step_1:
tprot H (tcon 0 L) / emp_hp == H => tcon 0 H / emp_hp.
Proof.
apply st_protv. apply v_c. Qed.
Example test_step_2:
tprot H (tcon 0 L) / ((tunit H, an unit H) :: (tcon 0 H, an int H) :: emp_hp)
== H =>
tcon 0 H / ((tunit H, an unit H) :: (tcon 0 H, an int H) :: emp_hp).
Proof.
apply st_protv. apply v_c. Qed.
Example test_step_3:
tprot L (tcon 0 H) / emp_hp == L => tcon 0 H / emp_hp.
Proof.
apply st_protv. apply v_c. Qed.
Example test_step_4:
tprot H (tderef (tloc (an unit L) 0 H)) / ((tcon 0 L,an int L) :: emp_hp)
== L =>*
tcon 0 H / ((tcon 0 L,an int L) :: emp_hp).
Proof.
apply Multi_step with (y:=(tprot H (tprot H (tcon 0 L)),((tcon 0 L,an int L) :: emp_hp))).
apply st_prot. apply st_derefloc. simpl. apply le_n. reflexivity.
apply Multi_step with (y:=((tprot H (tcon 0 H)),((tcon 0 L,an int L) :: emp_hp))).
apply st_prot. apply st_protv. apply v_c.
apply Multi_step with (y:=((tcon 0 H),((tcon 0 L,an int L) :: emp_hp))). apply st_protv.
apply v_c. apply Multi_refl. Qed.
Example test_step_5:
tprot H (tref (an int L) (tcon 0 L) L) / emp_hp 
== L =>*
tloc (an int L) 0 H / ((tcon 0 H,an int L) :: emp_hp).
Proof.
apply Multi_step with (y:=(tprot H (tloc (an int L) 0 L),((tcon 0 H,an int L) :: emp_hp))).
apply st_prot. apply st_refv with (v':=tcon 0 H). apply v_c. reflexivity. reflexivity.
apply Multi_step with (y:=(tloc (an int L) 0 H,((tcon 0 H,an int L) :: emp_hp))).
apply st_protv. apply v_l.  apply Multi_refl. Qed.
Example test_step_6:
tprot H (tderef (tref (an int L) (tcon 0 L) L)) / emp_hp 
== L =>*
tcon 0 H / ((tcon 0 H,an int L) :: emp_hp).
Proof.
apply Multi_step with (y:=(tprot H (tderef (tloc (an int L) 0 L)),((tcon 0 H,an int L) :: emp_hp))).
apply st_prot. apply st_deref. apply st_refv with (v':=tcon 0 H). apply v_c. reflexivity. reflexivity.
apply Multi_step with (y:=(tprot H (tprot L (tcon 0 H)),((tcon 0 H,an int L) :: emp_hp))).
apply st_prot. apply st_derefloc. simpl. apply le_n. reflexivity.
apply Multi_step with (y:=(tprot H (tcon 0 H),((tcon 0 H,an int L) :: emp_hp))).
apply st_prot. apply st_protv. apply v_c. 
apply Multi_step with (y:=(tcon 0 H,((tcon 0 H,an int L):: emp_hp))).
apply st_protv. apply v_c. apply Multi_refl. Qed.
Example test_step_7:
(tderef (tref (an int L)(tcon 0 L) L)) / emp_hp
== H =>*
tcon 0 H / ((tcon 0 H,an int L) :: emp_hp).
Proof.
apply Multi_step with (y:=(tderef (tloc (an int L) 0 L),((tcon 0 H,an int L) :: emp_hp))).
apply st_deref. apply st_refv with (v':=tcon 0 H). apply v_c. reflexivity. reflexivity.
apply Multi_step with (y:=(tprot L (tcon 0 H),((tcon 0 H,an int L) :: emp_hp))).
apply st_derefloc. simpl. apply le_n. reflexivity.
apply Multi_step with (y:=(tcon 0 H,((tcon 0 H,an int L) :: emp_hp))). apply st_protv. apply v_c.
apply Multi_refl. Qed.
(**
According to the typing system in Lu[1] the above reduction sequence
gives us one example where the type preservation breaks down and 
it seems that [st_refv] is at the root of the problem where the new cell being
written is guarded by [PC].
Yet, if we restrict in the typing system that "the new cell being written has
to be guarded by [PC] in order for the reference to be well-typed" then the
term,[ PC = H | tderef (tref (an int L)(tcon 0 L) L)],we start with in the above example is no longer well-typed and therefore
lies outside of the concern of [preservation]
*)
Example test_step_8:
tprot H (tapp (tabs (Id 0)(an int L)(tvar (Id 0)) L)(tcon 0 L)) / emp_hp 
== L =>*
tcon 0 H / emp_hp.
Proof.
apply Multi_step with (y:=(tprot H (tprot L ([(Id 0) := tcon 0 L](tvar (Id 0)))),emp_hp)).
apply st_prot. apply st_appabs. apply v_c. 
apply Multi_step with (y:=(tprot H (tcon 0 L),emp_hp)). apply st_prot. simpl. apply st_protv. apply v_c. 
apply Multi_step with (y:=(tcon 0 H,emp_hp)). apply st_protv. apply v_c.
apply Multi_refl. Qed.
Example test_step_9:
tprot L (tapp (tabs (Id 0)(an int L)(tvar (Id 0)) L)(tcon 0 L)) / emp_hp
== H =>*
tcon 0 L / emp_hp.
Proof.
apply Multi_step with (y:=(tprot L (tprot L ([(Id 0) := tcon 0 L](tvar (Id 0)))),emp_hp)).
apply st_prot. apply st_appabs. apply v_c. simpl.
apply Multi_step with (y:=(tprot L (tcon 0 L),emp_hp)). apply st_prot. apply st_protv. apply v_c.
apply Multi_step with (y:=(tcon 0 L,emp_hp)). apply st_protv. apply v_c.
apply Multi_refl. Qed.
Example test_step_10:
tprot L (tassign (tloc (an int L) 0 L)(tcon 1 L)) / ((tcon 0 L,an int L) :: emp_hp)
== L =>*
tunit L / ((tcon 1 L,an int L) :: emp_hp).
Proof.
apply Multi_step with (y:=(tprot L (tunit L),((tcon 1 L,an int L) :: emp_hp))).
apply st_prot. simpl. apply st_assign with (v':=tcon 1 L)(T':=an int L). simpl. 
apply le_n. apply v_c. simpl. apply sub_refl. reflexivity. reflexivity.
simpl. reflexivity.
apply Multi_step with (y:=(tunit L,((tcon 1 L,an int L) :: emp_hp))). apply st_protv. apply v_u.
apply Multi_refl. Qed.
(**
Q: How [PC] matters for the reduction sequence in case of [tprot]?
A: It depends upon the sub-term under protection. If it is a value, then it does
   not matter at all for the end result; if it is an appliction then it may only 
   matter when after substitution its body is not a value; if it is a dereference
   it only matters when its body is not a value; in case of assignment and refrence
   the choice of [PC], however,will affect the result we have.
*)
Example test_step_11:
~(
tassign (tloc (an int H) 0 L)(tcon 1 H) / ((tcon 0 L,an int L) :: emp_hp)
== H =>
tunit H / ((tcon 1 H,an int H) :: emp_hp)
).
Proof.
intros contra. inversion contra. subst. simpl in H9.
inversion H9. Qed.
(**
Note that the above example shows us that "updating a low security cell under
high security context is not allowed in our system".
In fact, we need not worry about it at all for in our system, we always expect
that "current type" and "access type" are the same and remines the same after
the cell is being written into heap and there is no updating at all. Our type
system will indeed guarantee this. See below.
*)
Example test_step_12:
tapp (tabs (Id 0)(an int L)(tvar (Id 0)) H)(tcon 0 L) / emp_hp 
== L =>*
tcon 0 H / emp_hp.
Proof.
apply Multi_step with (y:=(tprot H ([(Id 0) := tcon 0 L](tvar (Id 0))),emp_hp)).
apply st_appabs. apply v_c.
apply Multi_step with (y:=(tcon 0 H,emp_hp)). simpl. apply st_protv. apply v_c.
apply Multi_refl. Qed.
Example test_step_13:
tapp (tabs (Id 0)(an int L)(tvar (Id 0)) L)(tcon 0 L) / emp_hp
== H =>*
tcon 0 L / emp_hp.
Proof.
apply Multi_step with (y:=(tprot L ([(Id 0) := tcon 0 L](tvar (Id 0))),emp_hp)).
apply st_appabs. apply v_c. 
apply Multi_step with (y:=(tcon 0 L,emp_hp)). simpl. apply st_protv. apply v_c.
apply Multi_refl. Qed.
Example test_step_14:
tapp (tabs (Id 0)(an (ref (an int L)) L)(tderef (tvar (Id 0))) L) (tref (an int L)(tcon 0 L) L) / emp_hp
== L =>*
tcon 0 L / ((tcon 0 L,an int L) :: emp_hp).
Proof.
apply Multi_step with (y:=(tapp (tabs (Id 0)(an (ref (an int L)) L)(tderef (tvar (Id 0))) L)(tloc (an int L) 0 L),((tcon 0 L,an int L) :: emp_hp))).
apply st_app2. apply v_f. apply st_refv with (v':=tcon 0 L). apply v_c. reflexivity. reflexivity.
apply Multi_step with (y:=(tprot L ([(Id 0) := tloc (an int L) 0 L](tderef (tvar (Id 0)))),((tcon 0 L,an int L) :: emp_hp))).
apply st_appabs. apply v_l. simpl.
apply Multi_step with (y:=(tprot L (tprot L (tcon 0 L)),((tcon 0 L,an int L) :: emp_hp))).
apply st_prot. apply st_derefloc. simpl. apply le_n. reflexivity.
apply Multi_step with (y:=(tprot L (tcon 0 L),((tcon 0 L,an int L) :: emp_hp))).
apply st_prot. apply st_protv. apply v_c. 
apply Multi_step with (y:=(tcon 0 L,((tcon 0 L,an int L) :: emp_hp))).
apply st_protv. apply v_c. apply Multi_refl. Qed.
Example test_step_15:
tapp (tabs (Id 0)(an (ref (an int L)) L)(tderef (tvar (Id 0))) L)(tref (an int L)(tcon 0 L) L) / emp_hp
== H =>*
tcon 0 H / ((tcon 0 H,an int L) :: emp_hp).
Proof.
apply Multi_step with (y:=(tapp (tabs (Id 0)(an (ref (an int L)) L)(tderef (tvar (Id 0))) L)(tloc (an int L) 0 L),((tcon 0 H,an int L) :: emp_hp))).
apply st_app2. apply v_f. apply st_refv with (v':=tcon 0 H). apply v_c. reflexivity. reflexivity.
apply Multi_step with (y:=(tprot L ([(Id 0) := tloc (an int L) 0 L](tderef (tvar (Id 0)))),((tcon 0 H,an int L) :: emp_hp))).
apply st_appabs. apply v_l. simpl.
apply Multi_step with (y:=(tprot L (tprot L (tcon 0 H)),((tcon 0 H,an int L) :: emp_hp))).
apply st_prot. apply st_derefloc. simpl. apply le_n. reflexivity.
apply Multi_step with (y:=(tprot L (tcon 0 H),((tcon 0 H,an int L) :: emp_hp))).
apply  st_prot. apply st_protv. apply v_c.
apply Multi_step with (y:=(tcon 0 H,((tcon 0 H,an int L) :: emp_hp))). apply st_protv. apply v_c.
apply Multi_refl. Qed.
(**
Q: How [PC] affects reduction sequence in case of application?
A:The above two cases,[test_step_14] and [test_step_15],clearly shows how [PC] propogates through 
  the reduction process and under what conditions it can affect the result:
  it matters if the arguments of the application are not values. Moreover, if the
  first argument is abstraction, then [PC] may make a difference if the body after
  substitution is not a value.
*)
Example test_step_16:
tapp (tderef (tloc (an (fn (an int L) L (an int L)) L) 0 L)) (tcon 0 L) / ((tabs (Id 0)(an int L)(tvar (Id 0)) L,an (fn (an int L) L (an int L)) L) :: emp_hp)
== L =>*
tcon 0 L / ((tabs (Id 0)(an int L)(tvar (Id 0)) L,an (fn (an int L) L (an int L)) L) :: emp_hp).
Proof.
apply Multi_step with (y:=(tapp (tprot L (tabs (Id 0)(an int L)(tvar (Id 0)) L))(tcon 0 L),((tabs (Id 0)(an int L)(tvar (Id 0)) L,an (fn (an int L) L (an int L)) L) :: emp_hp))).
apply st_app1. apply st_derefloc. simpl. apply le_n. reflexivity.
apply Multi_step with (y:=(tapp (tabs (Id 0)(an int L)(tvar (Id 0)) L)(tcon 0 L),((tabs (Id 0)(an int L)(tvar (Id 0)) L,an (fn (an int L) L (an int L)) L) :: emp_hp))).
apply st_app1. apply st_protv. apply v_f.
apply Multi_step with (y:=(tprot L (tcon 0 L),((tabs (Id 0)(an int L)(tvar (Id 0)) L,an (fn (an int L) L (an int L)) L) :: emp_hp))).
apply st_appabs. apply v_c. 
apply Multi_step with (y:=(tcon 0 L,((tabs (Id 0)(an int L)(tvar (Id 0)) L,an (fn (an int L) L (an int L)) L) :: emp_hp))).
apply st_protv. apply v_c. apply Multi_refl. Qed.
Example test_step_17:
tref (an unit H)(tunit H) L / emp_hp
== L =>
tloc (an unit H) 0 L / ((tunit H,an unit H) :: emp_hp).
Proof.
apply st_refv with (v':=tunit H). apply v_u. reflexivity. reflexivity. 
Qed.
Example test_step_18:
tref (an int L)(tcon 0 L) H / emp_hp
== H =>
tloc (an int L) 0 H / ((tcon 0 H,an int L) :: emp_hp).
Proof.
apply st_refv with (v':=tcon 0 H). apply v_c. reflexivity.
reflexivity. Qed.
(**
Note:
The above reduction sequence shows that it is possible for
[st_refv] to produce terms which are differently typed from their
reduction predessessors thus giving ways to non-preservation.
We can still,however,with a typing system which consider terms 
like [PC = H | tref (an int L)(tcon 0 L) H] as ill-typed and therefore
exclude them when considering preservation:
we can impose the rule that the new cell being written must be guarded by
the typing context and therefore in the reduction sequence updating the new
cell with typing context will never change its security level and in the
heap the type in the pair always indicates the right type of the value.
*)
Example test_step_19:
tref (an int L) (tapp (tabs (Id 0)(an int L)(tvar (Id 0)) L)(tcon 0 L)) L / emp_hp
== L =>*
tloc (an int L) 0 L / ((tcon 0 L,an int L) :: emp_hp).
Proof.
apply Multi_step with (y:=(tref (an int L)(tprot L (tcon 0 L)) L,emp_hp)).
apply st_ref. apply st_appabs. apply v_c.
apply Multi_step with (y:=(tref (an int L)(tcon 0 L) L,emp_hp)).
apply st_ref. apply st_protv. apply v_c.
apply Multi_step with (y:=(tloc (an int L) 0 L,((tcon 0 L,an int L) :: emp_hp))).
apply st_refv with (v':=tcon 0 L). apply v_c. reflexivity. reflexivity.
apply Multi_refl. Qed.
Example test_step_20:
tref (an int L)(tapp (tabs (Id 0)(an int L)(tvar (Id 0)) L)(tcon 0 L)) L / emp_hp
== H =>*
tloc (an int L) 0 L / ((tcon 0 H,an int L) :: emp_hp).
Proof.
apply Multi_step with (y:=(tref (an int L)(tprot L (tcon 0 L))L,emp_hp)). apply st_ref.
apply st_appabs. apply v_c. 
apply Multi_step with (y:=(tref (an int L)(tcon 0 L)L,emp_hp)). apply st_ref. apply st_protv.
apply v_c. 
apply Multi_step with (y:=(tloc (an int L) 0 L,((tcon 0 H,an int L) :: emp_hp))). 
apply st_refv with (v':=tcon 0 H). apply v_c. reflexivity. reflexivity.
apply Multi_refl. Qed.
(**
Now, in case of references, we can clearly see how security context 
may affect the result of the reduction and potentially give rise to 
in consistent heaps which may lead to violation of preservation.
All those cases,however,can be excluded with a corresponding typing system
where terms as showed in the previous instance are considered ill-typed.
*)
Example test_step_21:
tderef (tloc (an int H) 0 L) / ((tcon 0 H,an int H) :: emp_hp)
== H =>*
tcon 0 H / ((tcon 0 H,an int H) :: emp_hp).
Proof. 
apply Multi_step with (y:=(tprot L (tcon 0 H),((tcon 0 H,an int H) :: emp_hp))).
apply st_derefloc. simpl. apply le_n. reflexivity.
apply Multi_step with (y:=(tcon 0 H,((tcon 0 H,an int H) :: emp_hp))).
apply  st_protv. apply v_c.
apply Multi_refl. Qed.
Example test_step_22:
tderef (tref (an int L)(tcon 0 L) L) / emp_hp
== L =>*
tcon 0 L / ((tcon 0 L,an int L) :: emp_hp).
Proof.
apply Multi_step with (y:=(tderef (tloc (an int L) 0 L),((tcon 0 L,an int L) :: emp_hp))).
apply st_deref. apply st_refv with (v':=tcon 0 L). apply v_c. reflexivity. reflexivity.
apply Multi_step with (y:=(tprot L (tcon 0 L),((tcon 0 L,an int L) :: emp_hp))).
apply st_derefloc. simpl. apply le_n. reflexivity.
apply Multi_step with (y:=(tcon 0 L,((tcon 0 L,an int L) :: emp_hp))).
apply st_protv. apply v_c.
apply Multi_refl. Qed.
Example test_step_23:
tderef (tref (an int L)(tcon 0 L) L) / emp_hp
== H =>*
tcon 0 H / ((tcon 0 H,an int L) :: emp_hp).
Proof.
apply Multi_step with (y:=(tderef (tloc (an int L) 0 L),((tcon 0 H,an int L) :: emp_hp))).
apply st_deref. apply st_refv with (v':=tcon 0 H). apply v_c. reflexivity. reflexivity.
apply Multi_step with (y:=(tprot L (tcon 0 H),((tcon 0 H,an int L) :: emp_hp))).
apply st_derefloc. simpl. apply le_n. reflexivity.
apply Multi_step with (y:=(tcon 0 H,((tcon 0 H,an int L) :: emp_hp))).
apply st_protv. apply v_c. 
apply Multi_refl. Qed.
(**
Note: In case of [tderef], the security context does not matter for the end result
      if the body of de-reference is a value. 
      In case where the body can be further reduced, whether or not [PC] matters depends
      upon the body itself.
*)
Example test_step_24:
tassign (tloc (an int L) 0 L)(tcon 1 L) / ((tcon 0 L,an int L) :: emp_hp)
== L =>
tunit L / ((tcon 1 L,an int L) :: emp_hp).
Proof.
apply st_assign with (v':=tcon 1 L)(T':=an int L). simpl. apply le_n.
apply v_c. simpl. apply sub_refl. reflexivity. reflexivity. reflexivity.
Example test_step_25:
tassign (tloc (an int L) 0 L)(tcon 1 L) / ((tcon 0 H,an int L) :: emp_hp)
== H =>
tunit H / ((tcon 1 H,an int H) :: emp_hp).
Proof.
apply st_assign with (v':=tcon 1 H)(T':=an int H). simpl. apply le_n. apply v_c.
simpl. apply sub_refl. reflexivity. reflexivity. simpl. reflexivity.
Qed.
Example test_step_26:
tassign (tloc (an int L) 0 H)(tcon 1 L) / ((tcon 0 H,an int L) :: emp_hp)
== L => 
tunit L / ((tcon 1 H, an int H) :: emp_hp).
Proof.
apply st_assign with (v':=tcon 1 H)(T':=an int H). simpl. apply le_n.
apply v_c. simpl. apply sub_refl. reflexivity. reflexivity. reflexivity.
Qed.
(**
Note, [test_step_26] shows us one example that even in the absence of cast,
"access tpye" and "current" type can differ due to [st_assign].
In [st_assign], in order to avoid implicit info. flows,we restrict the 
new cell and its type being written into the heap to be guarded both by
the security context and the security level of the pointer. Moreover the
old value to be replaced has to be guarded by them as well.
Therefore in case of either a high context or a high pointer, it is possible 
that the access type is different from the corresponding current type and in
our typing system, this divergence may not be something we would like to have.
Again, the fix is to specify our typing system so as to render terms like
shown above ill-typed. 
*)
Example test_step_27:
tassign (tloc (an int H) 0 L)(tcon 1 H) / ((tcon 0 H,an int H) :: emp_hp)
== L =>
tunit L / ((tcon 1 H,an int H) :: emp_hp).
Proof.
apply st_assign with (v':=tcon 1 H)(T':=an int H). simpl. apply le_n. apply v_c.
simpl. apply sub_LH. reflexivity. reflexivity. reflexivity.
Qed.
(**
Note in [test_step_27],
a. the "access type" indicated in [tloc] is equal to the "current type" shown in
   the heap
b. the  old cell is being guarded by both security context and the security level
   of the pointer
c. the type of the new cell being written is equal to that of the old and the type
   indicates the true type of the value
Indeed in our system without cast operation [a.] is always satisfied and to prevent
implicit flow we further restrict that the old cell is being guarded by both the 
security context and the security level of the pointer and the new cell and
the "access type" being written into the heap are also guarded in the same way.
However there is no guarantee that the new cell's type is equal to that indicated
by the pointer and in the heap values' type is indicated by the corresponding type.
This is not nice and we can fix it by having a typing rule which says,
a. the "access type" should be always the same as the type of the new cell
   being written into the heap
b. the type is being guarded by the typing context and the security level of the 
   pointer
then together with other rules which prevent cases where the values in the heap
have different types than the ones stored in heap, we can guarantee that
"there is no upgrading in a high security context" while still ensures preservation.
*)
Example test_step_28:
tassign (tref (an int H)(tcon 0 H) L)(tcon 1 H) / emp_hp
==H=>*
tunit H / ((tcon 1 H,an int H) :: emp_hp).
Proof.
apply Multi_step with (y:=(tassign (tloc (an int H) 0 L)(tcon 1 H),((tcon 0 H,an int H) :: emp_hp))).
apply st_assign1. apply st_refv with (v':=tcon 0 H). apply v_c. reflexivity. reflexivity.
apply Multi_step with (y:=(tunit H,((tcon 1 H,an int H) :: emp_hp))). 
apply st_assign with (v':=tcon 1 H)(T':=an int H). simpl. apply le_n. apply v_c. simpl. apply sub_refl.
reflexivity. reflexivity. reflexivity.
apply Multi_refl. Qed.
Example test_step_29:
tassign (tloc (an int H) 0 L)(tapp(tabs (Id 0)(an int H)(tvar (Id 0)) L)(tcon 1 H)) / ((tcon 0 H,an int H) :: emp_hp)
==H=>*
tunit H / ((tcon 1 H,an int H) :: emp_hp).
Proof.
apply Multi_step with (y:=(tassign (tloc (an int H) 0 L)(tprot L (tcon 1 H)),((tcon 0 H,an int H) :: emp_hp))).
apply st_assign2. apply v_l. apply st_appabs. apply v_c.
apply Multi_step with (y:=(tassign (tloc (an int H) 0 L)(tcon 1 H),((tcon 0 H,an int H) :: emp_hp))).
apply st_assign2. apply v_l. apply st_protv. apply v_c.
apply Multi_step with (y:=(tunit H,((tcon 1 H,an int H) :: emp_hp))).
apply st_assign with (v':=tcon 1 H)(T':=an int H). simpl. apply le_n. apply v_c.
simpl. apply sub_refl. reflexivity. reflexivity. reflexivity.
apply Multi_refl. Qed.
Example test_step_30:
tassign (tref (an int H)(tcon 0 H) L)(tapp (tabs (Id 0)(an int H)(tvar (Id 0)) L)(tcon 1 H)) / emp_hp
==H=>*
tunit H / ((tcon 1 H,an int H) :: emp_hp).
Proof.
apply Multi_step with (y:=(tassign (tloc (an int H) 0 L)(tapp (tabs (Id 0)(an int H)(tvar (Id 0)) L)(tcon 1 H)),((tcon 0 H,an int H) :: emp_hp))).
apply st_assign1. apply st_refv with (v':=tcon 0 H). apply v_c. reflexivity. reflexivity.
apply Multi_step with (y:=(tassign (tloc (an int H) 0 L)(tprot L (tcon 1 H)),((tcon 0 H,an int H) :: emp_hp))).
apply st_assign2. apply v_l. apply st_appabs. apply v_c. 
apply Multi_step with (y:=(tassign (tloc (an int H) 0 L)(tcon 1 H),((tcon 0 H,an int H) :: emp_hp))). 
apply st_assign2. apply v_l. apply st_protv. apply v_c.
apply Multi_step with (y:=(tunit H,((tcon 1 H,an int H) :: emp_hp))).
apply st_assign with (v':=tcon 1 H)(T':=an int H). simpl. apply le_n. apply v_c.
simpl.  apply sub_refl. reflexivity. reflexivity. reflexivity.
apply Multi_refl. Qed.
(*Some stuck terms in the language*)

Definition stuck_term (s:tm) (hp:heap) (PC:Sec) : Prop :=
 (~exists e', step (s,hp) PC e') /\ (~value s).

Example stuck_term_1:
stuck_term (tassign (tabs (Id 0)(an int L)(tvar (Id 0)) L)(tcon 1 L))(((tcon 0 L,an int L) :: emp_hp))
H.
Proof.
unfold stuck_term. split. intros contra. inversion contra.
inversion H0. subst. inversion H6. subst. inversion H7. 
intros contra. inversion contra. Qed.
(**
Note [stuck_term_1] shows that when the security context
is lifted via [tprot], the term protected may become a stuck term even though
it is well-reducible under a lower security context.
Specifically in our language, if the protected term is an assignment where the 
supposedly to be over-written term has a type with lower security than the security
context, then it will become stuck term when [PC] is lifted.
*)
Example stuck_term_2:forall PC,
stuck_term (tderef (tloc (an int H) 0 L)) emp_hp PC.
Proof.
intros. destruct PC. 
Case ("L"). split. intros contra. inversion contra. inversion H0. subst. inversion H7.
            subst. inversion H5. intros contra. inversion contra.
Case ("H"). split. intros contra. inversion contra. inversion H0. subst. inversion H7.
            subst. inversion H5. intros contra. inversion contra.
Qed.
Example stuck_term_3:forall PC,
stuck_term (tassign (tloc (an int H) 0 L)(tcon 0 H)) emp_hp PC.
Proof.
intros. destruct PC.
Case ("L"). split. intros contra. inversion contra. inversion H0. subst. inversion H6.
            inversion H6. inversion H7. intros contra. inversion contra.
Case ("H"). split. intros contra. inversion contra. inversion H0. subst. inversion H6.
            inversion H6. inversion H7. intros contra. inversion contra.
Qed.
Example stuck_term_4:forall PC,
stuck_term (tderef (tcon 0 H)) emp_hp PC.
Proof.
intros. destruct PC. 
Case ("H"). split. intros contra. inversion contra. inversion H0. inversion H5.
            intros contra. inversion contra.
Case ("L"). split. intros contra. inversion contra. inversion H0. inversion H5.
            intros contra. inversion contra.
Qed.
Example stuck_term_5:forall PC,
stuck_term (tassign (tcon 0 L)(tcon 0 H)) emp_hp PC.
Proof.
intros. destruct PC.
Case ("L"). split. intros contra. inversion contra. inversion H0. inversion H6.
            inversion H7. intros contra. inversion contra.
Case ("H"). split. intros contra. inversion contra. inversion H0. inversion H6.
            inversion H7. intros contra. inversion contra.
Qed.
Example stuck_term_6:forall PC,
stuck_term (tapp (tcon 0 L)(tcon 0 H)) emp_hp PC.
Proof. intros. split. intros contra. inversion contra.  inversion H0. inversion H6.
inversion H7. intros contra. inversion contra.
Qed.
(*generalization of stuck term*)
(**Suppose s is a stuck term then [tprot b s] will also be a stuck term.
Indeed we can also have the following kinds of stuck terms,
a. tapp s s' where both s and s' are stuck terms
b. tref T s b
c. deref s
d. tassign (tloc T n b) s
e. tapp s v where s is a stuck term and v is a value
f. tassign  s s' where both s and s' are stuck terms.
*)
Example stuck_term_7:forall s hp PC,
stuck_term s hp PC ->
stuck_term (tderef s) hp PC.
Proof.
intros. split. intros contra. inversion contra. inversion H1. subst.
assert (~stuck_term (tloc T n b) hp PC). intros contra'. inversion contra'.
assert (value (tloc T n b)). apply v_l. apply H3 in H5. inversion H5.
apply H2 in H0. inversion H0. subst. inversion H0. 
assert (exists e', step (s,hp) PC e'). exists (t',hp'). apply H6. 
apply H2 in H4. inversion H4. intros contra. inversion contra.
Qed.
(*###one useful lemma###*)
Lemma HL_scontext:forall s hp,
(exists e',step (s,hp) H e') ->
exists e',step (s,hp) L e'.
Proof.
intros s. induction s.
Case ("tvar"). intros. inversion H0. inversion H1.
Case ("tprot"). intros. inversion H0. inversion H1. subst. destruct s.
                simpl in H7. assert (exists e',step (s0,hp) H e'). exists (t',hp').
                apply H7. apply IHs in H2. inversion H2. destruct x. exists (tprot L t,h).
                apply st_prot. simpl. apply H3. simpl in H7. exists (tprot H t',hp').
                apply st_prot. simpl. apply H7. subst. exists (joinvs s0 s,hp). apply st_protv.
                apply H7.
Case ("tcon"). intros. inversion H0. inversion H1.
Case ("tabs"). intros. inversion H0. inversion H1.
Case ("tapp"). intros. inversion H0. inversion H1.
               subst. exists (tprot b ([x0:=s2]e),hp). apply st_appabs. apply H7.
               subst. assert (exists e',step (s1,hp) H e'). exists (t1',hp'). 
               apply H7. apply IHs1 in H2. inversion H2. destruct x. 
               exists (tapp t s2,h). apply st_app1. apply H3. subst.
               assert (exists e',step (s2,hp) H e'). exists (t2',hp'). apply H8.
               apply IHs2 in H2. inversion H2. destruct x. exists (tapp s1 t,h).
               apply st_app2. apply H7. apply H3.
Case ("tunit"). intros. inversion H0. inversion H1.
Case ("tref"). intros. inversion H0. inversion H1. subst. exists (tloc t (length hp) s0,snoc hp (joinvs s L,t)).
               apply st_refv with (v':=joinvs s L). apply H8. reflexivity. reflexivity. subst.
               assert (exists e',step (s,hp) H e'). exists (t',hp'). apply H8. apply IHs in H2. inversion H2.
               destruct x. exists (tref t t0 s0,h). apply st_ref. apply H3.
Case ("tderef"). intros. inversion H0. inversion H1. subst. exists (tprot b (efst (heap_lookup n hp)),hp).
               apply st_derefloc. apply H4. reflexivity. subst. assert (exists e',step (s,hp) H e').  exists (t',hp').
               apply H6. apply IHs in H2. inversion H2. destruct x. exists (tderef t,h). apply st_deref. apply H3.
Case ("tloc"). intros. inversion H0. inversion H1.
Case ("tassign"). intros. inversion H0. inversion H1. subst. exists (tunit L,heap_replace n (joinvs s2 (joins L b), joinTs T (joins L b)) hp).
               apply st_assign with (v':=joinvs s2 (joins L b))(T':=joinTs T (joins L b)). apply H5. apply H6. destruct b. simpl in H7. simpl.
               apply subsum_r_trans with (a:=L)(b:=H)(c:=label (efst (heap_lookup n hp))). apply sub_LH. apply H7. simpl. simpl in H7. apply H7.
               reflexivity. reflexivity. reflexivity. subst.
               assert (exists e',step (s1,hp) H e'). exists (t1',hp'). apply H7. apply IHs1 in H2. inversion H2.
               destruct x. exists (tassign t s2,h ). apply st_assign1. apply H3. subst. assert (exists e',step (s2,hp) H e'). exists (t2',hp').
               apply H8. apply IHs2 in H2. inversion H2. destruct x. exists (tassign s1 t,h). apply st_assign2. apply H7. apply H3.
Qed.
             
Lemma prot_scontext:forall s hp PC b, 
(exists e', step (s,hp) (joins PC b) e') ->
exists e',step (s,hp) PC e'.
Proof.
intros. destruct b. 
assert (joins PC L=PC). destruct PC. reflexivity. reflexivity.
rewrite->H1 in H0. apply H0. destruct PC. simpl in H0.
apply HL_scontext in H0. apply H0. simpl in H0. apply H0.
Qed.
(*######################*)
(*Lemma tprot_stuck:forall s hp PC*)
Example stuck_term_8:forall s hp PC,
stuck_term s hp PC -> forall b,
stuck_term (tprot b s) hp PC.
Proof.
intros. split. intros contra. inversion contra. inversion H1.
subst.  inversion H0. assert (exists e',step (s,hp) (joins PC b) e').
exists (t',hp'). apply H7. 
apply prot_scontext in H4. apply H2 in H4. inversion H4. subst. inversion H0. apply H3 in H7. 
inversion H7. intros contra. inversion contra.
Qed.
Example stuck_term_9:forall T s b hp PC,
stuck_term s hp PC -> 
stuck_term (tref T s b) hp PC.
Proof.
intros. inversion H0. split. intros contra. inversion contra. inversion H3.
subst. apply H2 in H10. inversion H10. subst. assert (exists e',step (s,hp) PC e').
exists (t',hp'). apply H10. apply H1 in H4. inversion H4. intros contra. inversion contra.
Qed.
Example stuck_term_10:forall s1 v2 hp PC,
value v2 ->
stuck_term s1 hp PC ->
stuck_term (tapp s1 v2) hp PC.
Proof. intros. split. intros contra. inversion H1. inversion contra. inversion H4.
       subst. assert (value (tabs x0 T e b)). destruct x0. apply v_f. apply H3 in H5.
       inversion H5. subst. assert (exists e',step (s1,hp) PC e'). exists (t1',hp').
       apply H10. apply H2 in H5. inversion H5. subst. apply H3 in H10. inversion H10.
       intros contra. inversion contra.
Qed.
Example stuck_term_11:forall s1 s2 hp PC,
stuck_term s1 hp PC ->
stuck_term s2 hp PC ->
stuck_term (tapp s1 s2) hp PC.
Proof. intros. split. inversion H0. inversion H1. intros contra. inversion contra. inversion H6.
       subst. assert (value (tabs x0 T e b)). destruct x0. apply v_f. apply H3 in H7. inversion H7.
       subst. assert (exists e',step (s1,hp) PC e'). exists (t1',hp'). apply H12. apply H2 in H7.
       inversion H7. subst. apply H3 in H12. inversion H12. intros contra. inversion contra.
Qed.
Example stuck_term_12:forall T n b s hp PC,
stuck_term s hp PC ->
stuck_term (tassign (tloc T n b) s) hp PC.
Proof. intros. split. intros contra. inversion H0. inversion contra. inversion H3.
       subst. apply H2 in H10. inversion H10. subst. inversion H9. subst. assert (exists e',step (s,hp) PC e').
       exists (t2',hp'). apply H10. apply H1 in H4. inversion H4. intros contra. inversion contra.
Qed.
Example stuck_term_13:forall s1 s2 hp PC,
stuck_term s1 hp PC ->
stuck_term s2 hp PC ->
stuck_term (tassign s1 s2) hp PC.
Proof. intros. split. intros contra. inversion contra.  inversion H0. inversion H1. inversion H2. subst.
       assert (value (tloc T n b)). apply v_l. apply H4 in H7. inversion H7. subst. assert (exists e',step (s1,hp) PC e').
       exists (t1',hp'). apply H12. apply H3 in H7. inversion H7. subst. apply H4 in H12. inversion H12.
       intros contra. inversion contra.
Qed.



(*typing rules*)
(*variable environment*)
(*############typing context############*)

Definition context := id -> option Ty.

Definition empty_context : context := 
  fun _ => None.
 
Definition Cupdate (St : context) (X:id) (T : option Ty) : context :=
  fun X' => if beq_id X X' then T else St X'.

(*#######some useful theorems regarding [Cupdate]#########*)
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
(*heap_ty*) 
Definition heap_Ty := list Ty.

Fixpoint heap_Tlookup (n:nat)(ht:heap_Ty): option Ty :=
  match ht , n with
  | nil , _ => None (*default return*)
  | h::t , 0 => Some h
  | h::t , S n' =>heap_Tlookup n' t
  end.
(*some examples of [heap_Tlookup]*)
Example test_heap_Tlookup1:
heap_Tlookup 0 [an int L,an unit H,an (fn (an int L) L (an int L)) L,an (ref (an int H)) H]
= Some (an int L).
Proof. simpl. reflexivity. Qed.
Example test_heap_Tlookup2:
heap_Tlookup 1 [an int H] = None.
Proof. simpl. reflexivity. Qed.
Example test_heap_Tlookup3:
heap_Tlookup 3 [an int H,an unit H,an (fn (an int H) L (an int H)) H,an (ref (an unit H)) H]
=Some (an (ref (an unit H)) H).
Proof. simpl. reflexivity. Qed.

(*typing relation*)

Inductive has_type : Sec -> context -> heap_Ty -> tm -> Ty -> Prop :=
  | t_var : forall pc Gamma HT x T,
      Gamma x = Some T ->
      has_type pc Gamma HT (tvar x) T
  | t_con : forall pc Gamma HT n b,
      has_type pc Gamma HT (tcon n b) (an int b)
  (**
   Note: here,as in all case of values,the constant can be typed under any security
         context for there is no further reduction upon a value term .
  *)
  | t_unit: forall pc Gamma HT b,
      has_type pc Gamma HT (tunit b) (an unit b)
  | t_loc: forall pc Gamma HT T n b,
      heap_Tlookup n HT = Some T ->
      has_type pc Gamma HT (tloc T n b) (an (ref T) b)
 (**
    Note that in the absence of casting, "currrent type" is always equal to
    "access type" for all well-typed addresses. Hence to type them, we need 
    to check whether or not the type indicated in [heap_Ty] is equal to the
    "access type" indicated in [tloc]; in the presence of casting,however,since
    "access type" and "current type" can differ we need to guarantee that they 
     are structurally the same.
*)
  | t_abs: forall pc pc' Gamma HT x T e b T',
    has_type pc' (Cupdate Gamma x (Some T)) HT e T' ->
    has_type pc Gamma HT (tabs x T e b) (an (fn T pc' T') b)
  (**
   Note since we have to consider side-effect when doing security typing
   , we model [PC'] as the lower bound for all cells being written when
   evaluating [e] and together with the expanded typing context by the 
   bounded variable [e] is typed as [T'] which implies the type of the 
   abstraction under any security context.
  *)
  | t_prot: forall pc Gamma HT t b T T',
    has_type (joins pc b) Gamma HT t T ->
    T' = joinTs T b ->
    has_type pc Gamma HT (tprot b t) T'
  (**
   Note [t_prot] says that if the protected term under the security context
   guarded with the security level of the protection has some type then the
   the protection's type should be that type guarded by the security level.
   This is rather consistent with a corresponding rule in [step].
   Recall [st_protv], forall b PC t t' hp hp',
   t / hp ==(joins PC b)=> t'/hp' ->
   tprot b t / hp ==PC=> tprot b t' / hp'
   which says that if the low bound upon the security level of cells being 
   written when evaluating the protected term is [PC] guarded by [b] then
   the same lower bound when evaluating the term protected by [b] should be
   [PC]. 
  *)
  | t_app: forall pc Gamma HT T1 T2 T2' b t1 t2,
  has_type pc Gamma HT t1 (an (fn T1 (joins pc b) T2) b) ->
  has_type pc Gamma HT t2 T1 ->
  joinTs T2 b = T2' ->
  has_type pc Gamma HT (tapp t1 t2) T2'
  (**
  Note that since the side-effect when doing application of an abstruction
  includes that of evaluating the body of the abstraction. Therefore the 
  "lower bound" is guarded by [pc]. Also that the function's identity represented
  by [b] should not be revealed when evaluating, hence "lower bound" is guarded by
  both [pc] and [b].
  [t_app] corresponds to [st_appabs], forall b v hp PC,
  value v ->
  tapp (tabs x T e b) v / hp ==PC=> tprot b [x:=v]e / hp
  which says that under security context,PC,a function application is reduced
  to a protected term by [b] which then is evaluated under security context
  [joins PC b].
  *)
  | t_ref: forall pc Gamma HT t T b,
    has_type pc Gamma HT t T ->
    subsum_r pc (labelT T) ->
    has_type pc Gamma HT (tref T t b) (an (ref T) b)
  (**
  Note when typing a reference there are two preconditions,
  a. the "initial type" has to be in agreement with the type of the new cell
     being written
  b. the type of the new cell being written has to be guarded by the typing
     context
  Recall [st_refv], forall T v v' b PC hp hp',
     value v ->
     v' = joinvs v PC ->
     hp' = snoc hp (v',T) ->
     tref T v b / hp ==PC=> tloc T (length hp) b / hp'
  which says that the value being written into the heap has to be guarded by
  the typing context.
  *)
  | t_deref: forall pc Gamma HT t T T' b,
    has_type pc Gamma HT t (an (ref T) b) ->
    T' = joinTs T b                        ->
    has_type pc Gamma HT (tderef t) T'
  (**
  Note the cell being read from the heap has to be guarded by the 
  security level of the pointer by which it is referred to.
  Recall [st_derefloc],forall T n b PC hp t,
  n < length hp ->
  t = efst (heap-lookup n hp) ->
  tderef (tloc T n b) / hp ==PC=> tprot b t / hp
  which says that the cell being read from the heap under security context [PC]
  is guarded by that of the pointer.
  *)
 | t_assign: forall pc Gamma HT t1 t2 b b' T,
   b' = labelT T ->
   subsum_r (joins pc b) b' ->
   has_type pc Gamma HT t1 (an (ref T) b) ->
   has_type pc Gamma HT t2 T ->
   has_type pc Gamma HT (tassign t1 t2) (an unit b')
 (**
 Note in order for [tassign] to be well-typed, the follows conditions have to be
 satisfied,
 a. the type of the new cell being written is the same as the type referred to
    by the pointer
 b. that type is guarded both by the security context and the security level of 
    the pointer
 c. it is not possible to update the old cell under a high context
 d. the resulting unit type of the assignment has security level which is equal
    to that of the cell being written
 Recall [st_assign],forall v v' T T' n b pc hp hp',
    n < length hp -> 
    value v ->
    subsum_r (joinS PC b)(label (efst (heap_lookup n hp))) ->
    T' = joinTs T (joins PC b) ->
    v' = joinvs v (joins PC b) ->
    hp' = heap_replace n (v',T') hp ->
    tassign (tloc T n b) v / hp ==PC=> tunit PC /hp'
    which says that to have an assignment well-typed, we 
    make sure that,
    a. the old value is guarded by both the security context and the security
       level of the pointer thus preventing "updating a low content under high
       security context"
    b. the resulting unit term has the security context as its label
 *)
 | t_sub: forall pc pc' Gamma HT t T T',
   has_type pc Gamma HT t T ->
   subsum_r pc' pc ->
   T <: T' ->
   has_type pc' Gamma HT t T'
 (**
 Note if a term is typable under a high security context, then it is typable
 under low security context which corresponds well to [HL_scontext],forall s hp,
  exists e',step (s,hp) H e' ->
  exists e',step (s,hp) L e'.
 which says that if a term is reducible under a high security context then it is 
 alos reducible under a low security context
 *)
.


(*some examples of well-typed term*)
(*type of values*)
Example has_type_1:forall pc Gamma HT n b,
has_type pc Gamma HT (tcon n b) (an int b).
Proof. intros. apply t_con. Qed.
Example has_type_1':forall pc pc' Gamma HT n b b',
has_type pc Gamma HT (tcon n b)(an int b) ->
subsum_r b b' ->
subsum_r pc' pc ->
has_type pc' Gamma HT (tcon n b)(an int b').
Proof. intros. apply t_sub with (pc:=pc)(T:=an int b). apply H0.
apply H2. apply subt_int. apply H1. Qed.
Example has_type_2:forall pc Gamma HT b,
has_type pc Gamma HT (tunit b) (an unit b).
Proof. intros. apply t_unit. Qed.
Example has_type_2':forall pc pc' Gamma HT b b',
has_type pc Gamma HT (tunit b)(an unit b) ->
subsum_r b b' ->
subsum_r pc' pc ->
has_type pc' Gamma HT (tunit b)(an unit b').
Proof. intros. apply t_sub with (pc:=pc)(T:=an unit b). apply H0.
apply H2. apply subt_unit. apply H1. Qed.
Example has_type_3:forall pc pc' Gamma HT n T b,
has_type pc Gamma HT (tabs (Id n) T (tvar (Id n)) b) (an (fn T pc' T) b).
Proof. intros. apply t_abs. apply t_var. rewrite->Cupdate_eq. reflexivity.
Qed.
Example has_type_3':forall pc pc' pc'' pc''' Gamma HT n T T' T'' b b',
has_type pc Gamma HT (tabs (Id n)T(tvar (Id n))b)(an (fn T pc' T) b) ->
subsum_r pc'' pc ->
subsum_r pc''' pc' ->
subsum_r b b' ->
T' <: T ->
T <: T'' ->
has_type pc'' Gamma HT (tabs (Id n)T(tvar (Id n)) b)(an (fn T' pc''' T'') b').
Proof. intros. apply t_sub with (pc:=pc)(T:=an (fn T pc' T) b). apply H0. apply H1.
apply subt_fn. apply H3. apply H2. apply H4. apply H5. Qed.
Example has_type_4:forall pc Gamma b,
has_type pc Gamma [an int L] (tloc (an int L) 0 b) (an (ref (an int L)) b).
Proof. intros. apply t_loc. reflexivity. Qed.
Example has_type_4':forall pc pc' Gamma b b',
has_type pc Gamma [an int L] (tloc (an int L) 0 b) (an (ref (an int L)) b) ->
subsum_r b b' ->
subsum_r pc' pc ->
has_type pc' Gamma [an int L] (tloc (an int L) 0 b) (an (ref (an int L)) b').
Proof. intros. apply t_sub with (pc:=pc)(T:=an (ref (an int L)) b). apply H0.
apply H2. apply subt_ref. apply H1. Qed.
(*types of composite terms*) 
Example has_type_5:forall pc Gamma HT b b',
has_type pc Gamma HT (tprot b (tcon 0 b')) (an int (joins b b')).
Proof. intros. apply t_prot with (T:=an int b'). apply t_con. destruct b'.
destruct b. reflexivity. reflexivity. destruct b. reflexivity. reflexivity.
Qed.
Example has_type_5':forall pc pc' Gamma HT b b' b'',
has_type pc Gamma HT (tprot b (tcon 0 b')) (an int (joins b b')) ->
subsum_r pc' pc ->
subsum_r (joins b b') b'' ->
has_type pc' Gamma HT (tprot b (tcon 0 b')) (an int b'').
Proof. intros. apply t_sub with (pc:= pc)(T:=an int (joins b b')). apply H0.
apply H1. apply subt_int. apply H2. Qed.
Example has_type_6:forall pc Gamma b1 b2 b3,
has_type pc Gamma [an unit b2] (tprot b1 (tderef (tloc (an unit b2) 0 b3))) (an unit (joins (joins b2 b3) b1)).
Proof. intros. apply t_prot with (T:=an unit (joins b2 b3)). apply t_deref with (T:=an unit b2)(b:=b3).
apply t_loc. reflexivity. destruct b2. destruct b3. simpl. reflexivity. simpl. reflexivity. simpl. destruct b3.
reflexivity. reflexivity. destruct b2. destruct b3. destruct b1. simpl. reflexivity. simpl. reflexivity.
simpl. destruct b1. reflexivity. reflexivity. simpl. destruct b1. reflexivity. reflexivity. Qed.
Example has_type_6':forall pc pc' Gamma b1 b2 b3 b',
has_type pc Gamma [an unit b2] (tprot b1 (tderef (tloc (an unit b2) 0 b3)))(an unit (joins (joins b2 b3) b1)) ->
subsum_r pc' pc ->
subsum_r (joins (joins b2 b3) b1) b' ->
has_type pc' Gamma [an unit b2](tprot b1 (tderef (tloc (an unit b2) 0 b3)))(an unit b').
Proof. intros. apply t_sub with (pc:=pc)(T:=an unit (joins (joins b2 b3) b1)). apply H0.
apply H1. apply subt_unit. apply H2. Qed.
Example has_type_7:forall Gamma HT b1 b2,
has_type L Gamma HT (tprot L (tref (an int b1)(tcon 0 b1) b2)) (an (ref (an int b1)) b2).
Proof. intros. apply t_prot with (T:=an (ref (an int b1)) b2). apply t_ref. apply t_con. destruct b1.
simpl. apply sub_refl. simpl. apply sub_LH. simpl. reflexivity. Qed.
Example has_type_8:forall pc Gamma HT b1 b2,
has_type pc Gamma HT (tprot b1 (tref (an int H)(tcon 0 H) b2)) (an (ref (an int H)) (joins b1 b2)).
Proof. intros. apply t_prot with (T:=an (ref (an int H)) b2). apply t_ref. apply t_con. simpl.
destruct pc. destruct b1. simpl. apply sub_LH. simpl. apply sub_refl. simpl. apply sub_refl.
destruct b1. destruct b2. simpl. reflexivity. simpl. reflexivity. simpl. reflexivity. Qed.
Example has_type_8':forall pc pc' Gamma HT b1 b2 b',
has_type pc Gamma HT (tprot b1 (tref (an int H)(tcon 0 H) b2))(an (ref (an int H)) (joins b1 b2))->
subsum_r pc' pc ->
subsum_r (joins b1 b2) b' ->
has_type pc' Gamma HT (tprot b1 (tref (an int H)(tcon 0 H) b2))(an (ref (an int H)) b').
Proof. intros. apply t_sub with (pc:=pc)(T:=an (ref (an int H)) (joins b1 b2)). apply H0.
apply H1. apply subt_ref. apply H2. Qed.
Example has_type_9:forall Gamma HT  b2 b3,
has_type L Gamma HT (tprot L (tderef (tref (an int b2)(tcon 0 b2) b3))) (an int (joins b2 b3)).
Proof. intros. apply t_prot with (T:=an int (joins b2 b3)). apply t_deref with (T:=an int b2)(b:=b3).
apply t_ref. apply t_con. simpl. destruct b2. apply sub_refl. apply sub_LH. destruct b2. destruct b3.
reflexivity. reflexivity. destruct b3. reflexivity. reflexivity. simpl. reflexivity. Qed.
Example has_type_10:forall pc Gamma HT b1 b2,
has_type pc Gamma HT (tprot b1 (tderef (tref (an int H)(tcon 0 H) b2))) (an int H).
Proof. intros. apply t_prot with (T:=an int H). apply t_deref with (T:=an int H)(b:=b2).
apply t_ref. apply t_con. destruct pc. destruct b1. simpl. apply sub_LH. simpl. apply sub_refl. simpl. 
apply sub_refl. simpl.  destruct b2. reflexivity. reflexivity. simpl. destruct b1. reflexivity.
reflexivity. Qed.
Example has_type_11:forall Gamma HT b1 b2,
has_type L Gamma HT (tderef (tref (an int b1)(tcon 0 b1) b2)) (an int (joins b1 b2)).
Proof. intros. apply t_deref with (T:=an int b1)(b:=b2). apply t_ref. apply t_con. simpl. destruct b1.
apply sub_refl. apply sub_LH. destruct b1. simpl. destruct b2. reflexivity. reflexivity. simpl.
destruct b2. reflexivity. reflexivity. Qed.
Example has_type_12:forall Gamma HT b,
has_type H Gamma HT (tderef (tref (an int H)(tcon 0 H)b)) (an int H).
Proof. intros. apply t_deref with (T:=an int H)(b:=b). apply t_ref. apply t_con. simpl. apply sub_refl.
simpl. destruct b. reflexivity. reflexivity. Qed.
Example has_type_13:forall pc Gamma HT n b1 b2,
has_type pc Gamma HT (tapp (tabs (Id n)(an int b1)(tvar (Id n)) b2)(tcon 0 b1)) (an int (joins b2 b1)).
Proof. intros. apply t_app with (T1:=an int b1)(T2:=an int b1)(b:=b2). apply t_abs. apply t_var. rewrite->Cupdate_eq.
reflexivity. apply t_con. destruct b1. destruct b2. simpl. reflexivity. simpl.  reflexivity. simpl. destruct b2.
reflexivity. simpl. reflexivity. Qed.
Example has_type_13':forall pc Gamma HT n b1 b2 b3,
subsum_r b3 b1 ->
has_type pc Gamma HT (tapp (tabs (Id n)(an int b1)(tvar (Id n)) b2)(tcon 0 b3))(an int (joins b2 b1)).
Proof. intros. apply t_app with (T1:=an int b1)(T2:=an int b1)(b:=b2). apply t_abs. apply t_var. rewrite->Cupdate_eq.
reflexivity. apply t_sub with (pc:=pc)(T:=an int b3). apply t_con. apply sub_refl. apply subt_int. apply H0.
destruct b1. destruct b2. reflexivity. reflexivity. destruct b2. reflexivity. reflexivity. Qed.
Example has_type_13'':forall pc Gamma HT n b1 b2 b3,
subsum_r b3 b1 ->
has_type pc Gamma HT (tapp (tabs (Id n)(an int b1)(tvar (Id n)) b2)(tcon 0 b3))(an int (joins b2 b1)).
Proof. intros. apply t_app with (T1:=an int b3)(T2:=an int b1)(b:=b2). apply t_sub with (pc:=pc)(T:=an (fn (an int b1)(joins pc b2)(an int b1)) b2).
apply t_abs. apply t_var. rewrite->Cupdate_eq. reflexivity. apply sub_refl. apply subt_fn. apply sub_refl. apply sub_refl. apply subt_int. apply H0.
apply subt_int. apply sub_refl. apply t_con.  destruct b1. destruct b2. reflexivity. reflexivity. destruct b2. reflexivity. reflexivity. Qed.
Example has_type_14:forall pc Gamma HT n b1 b2 b3,
has_type pc Gamma HT (tprot b1 (tapp (tabs (Id n)(an int b2)(tvar (Id n)) b3)(tcon 0 b2))) (an int (joins (joins b2 b3) b1)).
Proof. intros. apply t_prot with (T:=an int (joins b2 b3)). apply t_app with (T1:=an int b2)(T2:=an int b2)(b:=b3). apply t_abs. apply t_var.
rewrite->Cupdate_eq. reflexivity. apply t_con. destruct b2. destruct b3. reflexivity. reflexivity. simpl. destruct b3. reflexivity. reflexivity.
destruct b2. simpl. destruct b1. destruct b3. simpl. reflexivity. reflexivity. destruct b3. reflexivity. reflexivity. simpl. destruct b1. reflexivity.
reflexivity. Qed.
Example has_type_15:forall pc Gamma b n,
has_type pc Gamma [an int H] (tassign (tloc (an int H) 0 b)(tcon n H)) (an unit H).
Proof. intros. apply t_assign with (b:=b)(T:=an int H). reflexivity. destruct pc. destruct b. simpl. apply sub_LH. simpl. apply sub_refl. destruct b. simpl. apply sub_refl.
simpl. apply sub_refl. apply t_loc. reflexivity. apply t_con.
Example has_type_15':forall pc Gamma b n,
has_type pc Gamma [an int H] (tassign (tloc (an int H) 0 b)(tcon n L)) (an unit H).
Proof. intros. apply t_assign with (b:=b)(T:=an int H). reflexivity. destruct pc. destruct b. simpl. apply sub_LH. simpl. apply sub_refl.
destruct b. simpl. apply sub_refl. simpl. apply sub_refl. apply t_loc. reflexivity. apply t_sub with (pc:=pc)(T:=an int L).
apply t_con. apply sub_refl. apply subt_int. apply sub_LH. Qed.
(**
Note: that the above example is very important! It shows that although in our
system the "current type" in the heap and "the access type" in the pointer are
always the same, the current type is also the "right" type of the value stored 
in the heap.
e.g.,
Starting from the term in [has_type_15'], a pair (tcon n L,an int H) is stored in
the heap and in the presence of subtyping the value is correctly typed.
*)
Example has_type_15'':forall pc Gamma b1 b2 b3 n,
subsum_r (joins pc b2) b1 ->
subsum_r b3 b1 ->
has_type pc Gamma [an int b1] (tassign (tloc (an int b1) 0 b2)(tcon n b3))(an unit b1).
Proof. intros. apply t_assign with (b:=b2)(T:=an int b1). reflexivity. apply H0. apply t_loc.
reflexivity. apply t_sub with (pc:=pc)(T:=an int b3). apply t_con. apply sub_refl. apply subt_int. apply H1. Qed.
Example has_type_16:forall Gamma HT n b1 b2 b3,
has_type L Gamma HT (tapp (tabs (Id n)(an (ref (an int b1)) b2)(tderef (tvar (Id n)))b3)(tref (an int b1)(tcon 0 b1) b2))
(an int (joins (joins b1 b2) b3)).
Proof. intros. apply t_app with (T1:=an (ref (an int b1)) b2)(T2:=an int (joins b1 b2))(b:=b3). apply t_abs. apply t_deref with (T:=an int b1)(b:=b2).
apply t_var. rewrite->Cupdate_eq. reflexivity. destruct b1. destruct b2. reflexivity.  reflexivity. destruct b2. reflexivity. reflexivity. apply t_ref.
apply t_con. simpl. destruct b1. apply sub_refl. apply sub_LH. destruct b1. destruct b2. destruct b3. reflexivity. reflexivity. destruct b3. reflexivity.
reflexivity. simpl. destruct b3. reflexivity. reflexivity. Qed.
Example has_type_16':forall pc Gamma HT n b1 b2 b3,
subsum_r b3 b1 ->
has_type pc Gamma HT (tapp (tabs (Id n)(an (ref (an int H)) b1)(tderef (tvar (Id n))) b2)(tref (an int H)(tcon 0 L) b3))
(an int H).
Proof. intros. apply t_app with (T1:=an (ref (an int H)) b1)(T2:=an int H)(b:=b2).
apply t_abs. apply t_deref with (T:=an int H)(b:=b1). apply t_var. rewrite->Cupdate_eq. reflexivity. destruct b1. reflexivity.
reflexivity. apply t_sub with (pc:=pc)(T:=an (ref (an int H)) b3). apply t_ref. apply t_sub with (pc:=pc)(T:=an int L).
apply t_con. apply sub_refl. apply subt_int. apply sub_LH. destruct pc. simpl. apply sub_LH. simpl. apply sub_refl. apply sub_refl.
apply subt_ref. apply H0. destruct b2. reflexivity. reflexivity. Qed.
Example has_type_16'':forall pc Gamma HT n b1 b2 b3,
subsum_r b3 b1 ->
has_type pc Gamma HT (tapp (tabs (Id n)(an (ref (an int H)) b1)(tderef (tvar (Id n))) b2)(tref (an int H)(tcon 0 L) b3))
(an int H).
Proof. intros. apply t_app with (T1:=an (ref (an int H)) b3)(T2:=an int H)(b:=b2). apply t_sub with (pc:=pc)(T:=an (fn (an (ref (an int H)) b1)(joins pc b2)(an int H)) b2).
apply t_abs. apply t_deref with (T:=an int H)(b:=b1). apply t_var. rewrite->Cupdate_eq. reflexivity. destruct b1. reflexivity. reflexivity. apply sub_refl. apply subt_fn.
apply sub_refl. apply sub_refl. apply subt_ref. apply H0. apply subt_int. apply sub_refl.
apply t_ref. apply t_sub with (pc:=pc)(T:=an int L). apply t_con. apply sub_refl. apply subt_int. apply sub_LH.
destruct pc. simpl. apply sub_LH. simpl. apply sub_refl. destruct b2. reflexivity.
reflexivity. Qed.
Example has_type_17:forall Gamma HT n b1 b2 b3 b4 b5,
subsum_r b5 b1 ->
subsum_r b4 b2 ->
has_type L Gamma HT (tapp (tabs (Id n)(an (ref (an int b1)) b2)(tderef (tvar (Id n))) b3)(tref (an int b1)(tcon 0 b5) b4))
(an int (joins (joins b1 b2) b3)).
Proof. intros. apply t_app with (T1:=an (ref (an int b1)) b2)(T2:=an int (joins b1 b2))(b:=b3).
apply t_abs. apply t_deref with (b:=b2)(T:=an int b1). apply t_var. rewrite->Cupdate_eq. reflexivity.
destruct b1. destruct b2. reflexivity. reflexivity. destruct b2. reflexivity. reflexivity. apply t_sub with (pc:=L)(T:=an (ref (an int b1)) b4).
apply t_ref. apply t_sub with (pc:=L)(T:=an int b5). apply t_con. apply sub_refl. apply subt_int. apply H0. destruct b1. simpl. apply sub_refl.
simpl. apply sub_LH. apply sub_refl. apply subt_ref. apply H1. destruct b1. destruct b2. destruct b3. reflexivity. reflexivity. destruct b3. reflexivity.
reflexivity. simpl. destruct b3. reflexivity. reflexivity. Qed.
Example has_type_17':forall Gamma HT n b1 b2 b3 b4 b5,
subsum_r b5 b1 ->
subsum_r b4 b2 ->
has_type L Gamma HT (tapp (tabs (Id n)(an (ref (an int b1)) b2)(tderef (tvar (Id n))) b3)(tref (an int b1)(tcon 0 b5)b4))
(an int (joins (joins b1 b2) b3)).
Proof. intros. apply t_app with (T1:=an (ref (an int b1)) b4)(T2:=an int (joins b1 b2))(b:=b3).
apply t_sub with (pc:=L)(T:=an (fn (an (ref (an int b1)) b2)(joins L b3)(an int (joins b1 b2))) b3).
apply t_abs. apply t_deref with (b:=b2)(T:=an int b1). apply t_var. rewrite->Cupdate_eq. reflexivity.
destruct b1. destruct b2. reflexivity. reflexivity. destruct b2. reflexivity. reflexivity. apply sub_refl.
apply subt_fn. apply sub_refl. apply sub_refl. apply subt_ref. apply H1. apply subt_int. apply sub_refl.
apply t_ref. apply t_sub with (pc:=L)(T:=an int b5). apply t_con. apply sub_refl. apply subt_int. apply H0.
destruct b1. simpl. apply sub_refl. simpl. apply sub_LH. destruct b1. destruct b2. destruct b3.
reflexivity. reflexivity. destruct b3. reflexivity. reflexivity. simpl. destruct b3. reflexivity. reflexivity.
Qed.
Example has_type_18:forall Gamma b1 b2 b4,
subsum_r b4 b1 ->
has_type L Gamma [an (fn (an int b1) L (an int b2)) L]
(tapp (tderef (tloc (an (fn (an int b1) L (an int b2)) L) 0 L))(tcon 0 b4))
(an int b2).
Proof. intros. apply t_app with (T1:=an int b1)(T2:=an int b2)(b:=L). 
 apply t_deref with (b:=L)(T:=an (fn (an int b1) L (an int b2)) L).
apply t_loc. reflexivity. simpl. reflexivity. apply t_sub with (pc:=L)(T:=an int b4).
apply t_con. apply sub_refl. apply subt_int. apply H0. simpl. reflexivity. Qed.
Example has_type_19:forall pc Gamma b1 b2 b3 b4 b5,
subsum_r b5 b1 ->
has_type pc Gamma [an (fn (an int b1) H (an int b2)) b3]
(tapp (tderef (tloc (an (fn (an int b1) H (an int b2)) b3) 0 b4))(tcon 0 b5))
(an int (joins b2 (joins b3 b4))).
Proof. intros. apply t_app with (T1:=an int b1)(T2:=an int b2)(b:=joins b3 b4).
apply t_sub with (pc:=pc)(T:=an (fn (an int b1) H (an int b2)) (joins b3 b4)).
apply t_deref with (b:=b4)(T:=an (fn (an int b1)H(an int b2)) b3). 
apply t_loc. reflexivity. destruct b3. destruct b4. reflexivity. 
reflexivity. destruct b4. reflexivity. reflexivity.  apply sub_refl. apply subt_fn.
apply sub_refl. destruct pc. destruct b3. destruct b4. simpl.  apply sub_LH.
simpl. apply sub_refl. simpl. apply sub_refl. simpl. apply sub_refl. apply subt_int. apply sub_refl.
apply subt_int. apply sub_refl. apply t_sub with (pc:=pc)(T:=an int b5). apply t_con.
apply sub_refl. apply subt_int. apply H0. destruct b2. destruct b3. destruct b4. reflexivity. 
reflexivity. simpl. reflexivity. destruct b3. destruct b4. reflexivity. reflexivity.
simpl. reflexivity. Qed.
Example has_type_20:forall pc Gamma HT b1 b2 b3 b4,
subsum_r b2 b1 ->
subsum_r pc b1 ->
subsum_r b3 b4 ->
has_type pc Gamma HT (tref (an unit b1)(tunit b2) b3) (an (ref (an unit b1)) b4).
Proof. intros. apply t_sub with (pc:=pc)(T:=an (ref (an unit b1)) b3). apply t_ref.
apply  t_sub with (pc:=pc)(T:=an unit b2). apply t_unit. apply sub_refl. apply subt_unit.
apply H0. simpl. apply H1. apply sub_refl. apply subt_ref. apply H2. Qed.
Example has_type_21:forall Gamma HT b1 b2 b3 n,
subsum_r b2 b1 ->
has_type L Gamma HT (tref (an int b1)(tcon n b2) b3)(an (ref (an int b1)) b3).
Proof. intros. apply t_ref. apply t_sub with (pc:=L)(T:=an int b2). apply t_con. apply sub_refl.
apply subt_int. apply H0. simpl. destruct b1. apply sub_refl. apply sub_LH. Qed.
Example has_type_21':forall pc Gamma HT b n,
has_type pc Gamma HT (tref (an int H)(tcon n L) b) (an (ref (an int H)) b).
Proof. intros. apply t_ref. apply t_sub with (pc:=pc)(T:=an int L). apply t_con. apply sub_refl.
apply subt_int. apply sub_LH. simpl. destruct pc. apply sub_LH. apply sub_refl. Qed.
Example has_type_22:forall Gamma HT b1 b2 b3 b4 b5 n,
subsum_r b4 b2 ->
subsum_r (joins b2 b3) b1 ->
has_type L Gamma HT (tref (an int b1)(tapp (tabs (Id n)(an int b2)(tvar (Id n))b3)(tcon n b4)) b5)(an (ref (an int b1)) b5).
Proof. intros. apply t_ref. apply t_sub with (pc:=L)(T:=an int (joins b2 b3)). apply t_app with (T1:=an int b2)(T2:=an int b2)(b:=b3).
apply t_abs. apply t_var. rewrite->Cupdate_eq. reflexivity. apply t_sub with (pc:=L)(T:=an int b4). apply t_con. apply sub_refl.
apply subt_int. apply H0. destruct b2. destruct b3. reflexivity. reflexivity. simpl. destruct b3. reflexivity. reflexivity. apply sub_refl.
apply subt_int. apply H1. simpl. destruct b1. apply sub_refl. apply sub_LH. Qed.
Example has_type_22':forall Gamma HT b1 b2 b3 b4 n,
subsum_r b3 b4 ->
has_type H Gamma HT (tref (an int H)(tapp (tabs (Id n)(an int H)(tvar (Id n)) b1)(tcon n b2))b3)(an (ref (an int H)) b4).
Proof. intros. apply t_sub with (pc:=H)(T:=an (ref (an int H)) b3). apply t_ref. apply t_app with (T1:=an int H)(T2:=an int H)(b:=b1).
apply t_abs. apply t_var. rewrite->Cupdate_eq. reflexivity. apply t_sub with (pc:=H)(T:=an int b2). apply t_con. apply sub_refl.
apply subt_int. destruct b2. apply sub_LH. apply sub_refl. destruct b1. reflexivity. reflexivity. simpl. apply sub_refl. apply sub_refl.
apply subt_ref. apply H0. Qed.
Example has_type_23:forall pc Gamma b1 b2, 
has_type pc Gamma [an int b1] (tderef (tloc (an int b1) 0 b2))
(an int (joins b1 b2)).
Proof. intros. apply t_deref with (b:=b2)(T:=an int b1). apply t_loc. reflexivity. destruct b1. destruct b2. reflexivity. reflexivity.
simpl. destruct b2. reflexivity. reflexivity. Qed.
Example has_type_24:forall Gamma HT b1 b2 b3 n,
subsum_r b2 b1 ->
has_type L Gamma HT (tderef (tref (an int b1)(tcon n b2) b3))(an int (joins b1 b3)).
Proof. intros. apply t_deref with (b:=b3)(T:=an int b1). apply t_ref. apply t_sub with (pc:=L)(T:=an int b2).
apply t_con. apply sub_refl. apply subt_int. apply H0. simpl. destruct b1. apply sub_refl. apply sub_LH.
destruct b1. destruct b3. reflexivity. reflexivity. destruct b3. reflexivity. reflexivity. Qed.
Example has_type_24':forall Gamma HT b n,
has_type H Gamma HT (tderef (tref (an int H)(tcon n L) b))(an int H).
Proof. intros. apply t_deref with (b:=b)(T:=an int H). apply t_ref.
apply t_sub with (pc:=H)(T:=an int L). apply t_con. apply sub_refl. apply subt_int. apply sub_LH. simpl.
apply sub_refl. destruct b. reflexivity. reflexivity. Qed.
Example has_type_25:forall pc Gamma b1 b2 b3 b4 n,
subsum_r (joins pc b2) b1 ->
subsum_r b3 b1 ->
subsum_r b1 b4 ->
has_type pc Gamma [an int b1] (tassign (tloc (an int b1) 0 b2)(tcon n b3)) (an unit b4).
Proof. intros. apply t_sub with (pc:=pc)(T:=an unit b1). apply t_assign with (b:=b2)(T:=an int b1).
reflexivity. apply H0. apply t_loc. reflexivity. apply t_sub with (pc:=pc)(T:=an int b3). apply t_con.
apply sub_refl. apply subt_int. apply H1. apply sub_refl. apply subt_unit. apply H2. Qed.
Example has_type_26:forall Gamma b,
has_type H Gamma [] (tassign (tref (an int H)(tcon 0 L) b)(tcon 0 H))(an unit H).
Proof. intros. apply t_assign with (b:=b)(T:=an int H). reflexivity. simpl. apply sub_refl. apply t_ref.
apply t_sub with (pc:=H)(T:=an int L). apply t_con. apply sub_refl. apply subt_int. apply sub_LH. simpl. apply sub_refl.
apply t_con. Qed.
(**
Note: [has_type_26] seems to suggest that we can have an assignment term 
      updating the old cell under a high security context which as we know from
      [step] would be a stuck term. 
      If it is true then we actually have a well-typed term which is not a value and
      which cannot be reduced. It indicates that at least progress does not hold in our
      system.
      Fortunately this is not the case, consider the reduction  of the following term,
      tassign (tref (an int H)(tcon 0 L) b)(tcon 0 H) / []
      ==H=> by [st_assign1] and [st_refv],
      tassign (tloc (an int H) 0 b)(tcon 0 H) / [tcon 0 H,an int H]
      ==H=> by [st_assign],
      tunit H / [tcon 0 H,an int H],
      which shows that dynamic checking implemented in [step] supplements [has_type] in
      regard to secure information checking. Specifically it disallows updating an old cell
      under a high security context. Qed.
*) 
Example has_type_26':forall pc Gamma HT b1 b2 b3 b4 b5,
subsum_r b1 b5 ->
subsum_r b2 b1 ->
subsum_r b4 b1 ->
subsum_r (joins pc b3) b1 ->
has_type pc Gamma HT (tassign (tref (an int b1)(tcon 0 b2)b3)(tcon 1 b4))(an unit b5).
Proof. intros. apply t_sub with (pc:=pc)(T:=an unit b1). apply t_assign with (b:=b3)(T:=an int b1).
reflexivity. apply H3. apply t_ref. apply t_sub with (pc:=pc)(T:=an int b2). apply t_con. apply sub_refl.
apply subt_int. apply H1. simpl. destruct b1. destruct pc. apply sub_refl. simpl in H3. inversion H3.
destruct pc. apply sub_LH. apply sub_refl. apply t_sub with (pc:=pc)(T:=an int b4). apply t_con. apply sub_refl.
apply subt_int. apply H2. apply sub_refl. apply subt_unit. apply H0. Qed.
Example has_type_27:forall pc Gamma b1 b2 b3 b4 b5 b6,
subsum_r b5 b3 ->
subsum_r (joins b3 b4) b1 ->
subsum_r (joins pc b2) b1 ->
subsum_r b1 b6 ->
has_type pc Gamma [an int b1] (tassign (tloc (an int b1) 0 b2)(tapp (tabs (Id 0)(an int b3)(tvar (Id 0)) b4)(tcon 1 b5)))
(an unit b6).
Proof. intros. apply t_sub with (pc:=pc)(T:=an unit b1). apply t_assign with (b:=b2)(T:=an int b1). reflexivity. apply H2.
apply t_loc. reflexivity. apply t_sub with (pc:=pc)(T:=an int (joins b3 b4)). apply t_app with (T1:=an int b3)(T2:=an int b3)(b:=b4).
apply t_abs. apply t_var. rewrite->Cupdate_eq. reflexivity. apply t_sub with (pc:=pc)(T:=an int b5). apply t_con. apply sub_refl.
apply subt_int. apply H0. destruct b3. destruct b4. reflexivity. reflexivity. destruct b4. reflexivity. reflexivity. apply sub_refl.
apply subt_int. apply H1. apply sub_refl. apply subt_unit. apply H3. Qed.
Example has_type_28:forall pc Gamma HT b1 b2 b3 b4 b5 b6 b7,
subsum_r pc b1 ->
subsum_r b2 b1 ->
subsum_r (joins pc b3) b1 ->
subsum_r b1 b7 ->
subsum_r b6 b4 ->
subsum_r (joins b4 b5) b1 ->
has_type pc Gamma HT (tassign (tref (an int b1)(tcon 0 b2)b3)(tapp (tabs (Id 0)(an int b4)(tvar (Id 0)) b5)(tcon 1 b6)))
(an unit b7).
Proof. intros. apply t_sub with (pc:=pc)(T:=an unit b1). apply t_assign with (b:=b3)(T:=an int b1). reflexivity. apply H2.
apply t_ref. apply t_sub with (pc:=pc)(T:=an int b2). apply t_con. apply sub_refl. apply subt_int. apply H1. simpl. destruct pc. destruct b1.
apply sub_refl. apply sub_LH. destruct b1. inversion H0. apply sub_refl. apply t_sub with (pc:=pc)(T:=an int (joins b4 b5)). apply t_app with (T1:=an int b4)(T2:=an int b4)(b:=b5).
 apply t_abs. apply t_var. rewrite->Cupdate_eq. reflexivity. apply t_sub with (pc:=pc)(T:=an int b6). apply t_con. apply sub_refl. apply subt_int. apply H4. destruct b4. destruct b5. 
reflexivity. reflexivity. destruct b5. reflexivity. reflexivity. apply sub_refl. apply subt_int. apply H5. apply sub_refl. apply subt_unit. apply H3. Qed.


(*###inversion of [has_type]###*)
(*inversion of [has_type pc Gamma HT (tvar x) T]*)
Lemma inversion_tvar: forall pc Gamma HT x T,
has_type pc Gamma HT (tvar x) T ->
exists T0, (Gamma x = Some T0)/\(T0 <: T).
Proof. intros. remember (tvar x) as t. induction H0.
inversion Heqt. subst. exists T. split. apply H0. apply subtyping_refl.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt.
inversion Heqt. inversion Heqt. inversion Heqt. 
apply IHhas_type in Heqt. inversion Heqt. exists x0. split. inversion H3.
apply H4. inversion H3. apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl.
apply H5. apply H2.
Qed.

(*inversion of [has_type pc Gamma HT (tabs x T1 e b) T]*)
Lemma inversion_tabs: forall pc Gamma HT x T1 T e b,
has_type pc Gamma HT (tabs x T1 e b) T ->
exists T1', exists T2, exists T2', exists pc', exists pc'', exists pc''', exists b',
(has_type pc' Gamma HT (tabs x T1 e b) (an (fn T1 pc'' T2) b)) /\
(has_type pc'' (Cupdate Gamma x (Some T1)) HT e T2) /\(subsum_r pc''' pc'')/\(subsum_r pc pc')/\
(T1'<:T1)/\(T2<:T2')/\(subsum_r b b')/\((an (fn T1' pc''' T2') b') <: T).
Proof. intros. remember (tabs x T1 e b) as t. induction H0. inversion Heqt. inversion Heqt. inversion Heqt.
inversion Heqt. inversion Heqt. subst. exists T1. exists T'. exists T'. exists pc. exists pc'. exists pc'. exists b.
split. apply t_abs with (b:=b)(pc:=pc) in H0. apply H0.
split. apply H0. split. apply sub_refl. split. apply sub_refl. split. apply subtyping_refl. split. apply subtyping_refl. split. apply sub_refl. apply subtyping_refl.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. apply IHhas_type in Heqt. inversion Heqt. exists x0. inversion H3. exists x1. inversion H4. exists x2.
inversion H5. exists x3. inversion H6. exists x4. inversion H7. exists x5. inversion H8. exists x6. split. apply H9. split. apply H9. split. apply H9. split. apply subsum_r_trans with (a:=pc')(b:=pc)(c:=x3).
apply H1. apply H9. split. apply H9. split. apply H9. split. apply H9.
 apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl. apply H9. apply H2.
Qed.

(*inversion of [has_type pc Gamma HT (tcon n b) T]*)

Lemma inversion_tcon: forall pc Gamma HT T n b,
has_type pc Gamma HT (tcon n b) T ->
exists T', exists T'', exists b', 
(T' = an int b)/\(T'' = an int b')/\(subsum_r b b')/\(T'' <: T).
Proof. 
 intros. remember (tcon n b) as t. induction H0.
inversion Heqt. inversion Heqt. subst. exists (an int b). exists (an int b).
exists b. split. reflexivity. split. reflexivity. split. apply sub_refl.
apply subt_int. apply sub_refl. inversion Heqt. inversion Heqt. inversion Heqt.
inversion Heqt.  inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt.
apply IHhas_type in Heqt. inversion Heqt. exists x. inversion H3.
exists x0. inversion H4. exists x1. 
inversion H5. split. apply H6. inversion H7. split. apply H8. inversion H9. split. apply H10. 
apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl. apply H11. apply H2.
Qed.

(*inversion of [has_type pc Gamma HT (tunit b) T]*)

Lemma inversion_tunit:forall pc Gamma HT T b,
has_type pc Gamma HT (tunit b) T ->
exists T', exists T'', exists b',
(T'=an unit b)/\(T''=an unit b')/\(subsum_r b b')/\(T''<:T).
Proof. intros. remember (tunit b) as t. induction H0. inversion Heqt. inversion Heqt. inversion Heqt.
subst. exists (an unit b). exists (an unit b). exists b. split. reflexivity. split. reflexivity. split.
apply sub_refl. apply subt_unit. apply sub_refl. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt.
inversion Heqt. inversion Heqt. inversion Heqt. apply IHhas_type in Heqt. inversion Heqt. exists x. inversion H3.
exists x0. inversion H4. exists x1. split. apply H5. split. apply H5. split. apply H5. apply subtyping_trans with (x:=T)(y:=T).
apply subtyping_refl. apply H5. apply H2. Qed.

(*inversion of [has_type pc Gamma HT (tloc T n b)(an (ref T) b)]*)

Lemma inversion_tloc:forall pc Gamma HT n T1 b T,
has_type pc Gamma HT (tloc T1 n b) T ->
exists T', exists T'', exists b',
(heap_Tlookup n HT = Some T1)/\(T'=an (ref T1) b)/\(T''=an (ref T1) b')/\(subsum_r b b')/\(T''<:T).
Proof. intros. remember (tloc T1 n b) as t. induction H0. inversion Heqt. inversion Heqt.
inversion Heqt. inversion Heqt. subst. exists (an (ref T1) b). exists (an (ref T1) b).
exists b. split. apply H0. split. reflexivity. split. reflexivity. split. apply sub_refl. apply subtyping_refl. inversion Heqt. inversion Heqt.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. apply IHhas_type in Heqt. inversion Heqt. exists x. inversion H3. exists x0.
inversion H4. exists x1. split. apply H5. split. apply H5. split. apply H5. split. apply H5. apply subtyping_trans with (x:=T)(y:=T). 
apply subtyping_refl. apply H5. apply H2. Qed.
 
(*inversion of [has_type pc Gamma HT (tprot b t) T]*)

Lemma inversion_tprot:forall pc Gamma HT t T b,
has_type pc Gamma HT (tprot b t) T ->
exists T', exists T'', exists pc',
((joinTs T' b) <: T) /\(has_type pc' Gamma HT t T'')/\(subsum_r (joins pc b) pc')/\(T'' <: T').
Proof. intros. remember (tprot b t) as e. induction H0. inversion Heqe.
       inversion Heqe. inversion Heqe. inversion Heqe. inversion Heqe. inversion Heqe. subst.
       exists T. exists T. exists (joins pc b). split. apply subtyping_refl. split. apply H0.
       split. apply sub_refl. apply subtyping_refl.
       inversion Heqe. inversion Heqe.  inversion Heqe. inversion Heqe.
       apply IHhas_type in Heqe. inversion Heqe. exists x. inversion H3. exists x0. inversion H4.
       exists x1. split. apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl. apply H5.
       apply H2. split. apply H5. split. destruct pc. destruct pc'. simpl. simpl in H5. apply H5.
       inversion H1. simpl in H5. destruct pc'. simpl. destruct b. apply subsum_r_trans with (a:=L)(b:=H)(c:=x1).
       apply sub_LH. apply H5. apply H5. simpl. apply H5. apply H5.
Qed.

(*inversion of [has_type pc Gamma HT (tapp t1 t2) T]*)


Lemma inversion_tapp: forall pc Gamma HT t1 t2 T2,
has_type pc Gamma HT (tapp t1 t2) T2 ->
exists T1', exists T2', exists b', exists T1'', exists T1''', exists T2'', exists b'', exists pc', exists sp', exists sp'',
(sp'=joins pc' b')/\has_type pc' Gamma HT t1 (an (fn T1' sp' T2') b')/\((an (fn T1' sp' T2') b')<:(an (fn T1'' sp'' T2'') b''))/\
(has_type pc' Gamma HT t2 T1''')/\(T1''' <: T1'')/\(subsum_r pc pc')/\
((joinTs T2'' b'')<:T2).
Proof. intros. remember (tapp t1 t2) as t. induction H0.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt.
 subst. exists T1. exists T2. exists b. exists T1. exists T1. exists T2. exists b. exists pc. exists (joins pc b). exists (joins pc b). split. reflexivity.
split. apply H0_. split. apply subtyping_refl. split. apply H0_0. split. apply subtyping_refl. split. destruct b. destruct pc. simpl.
apply sub_refl. simpl. apply sub_refl. destruct pc. simpl. apply sub_refl. apply sub_refl. apply subtyping_refl. inversion Heqt. inversion Heqt. inversion Heqt.
apply IHhas_type in Heqt. inversion Heqt. exists x. inversion H3.
exists x0. inversion H4. exists x1. inversion H5. exists x2. inversion H6. exists x3. inversion H7. exists x4.
inversion H8. exists x5. inversion H9. exists x6. inversion H10. exists x7. inversion H11. exists x8. split. apply H12.
split. apply H12. split. apply H12. split. apply H12. split. apply H12. split. apply subsum_r_trans with (a:=pc')(b:=pc)(c:=x6).
apply H1. apply H12. apply subtyping_trans with (x:=T)(y:=T).
apply subtyping_refl. apply H12. apply H2. Qed.

(*inversion of [has_type pc Gamma HT (tref T1 t b) T]*)

Lemma inversion_tref:forall pc Gamma HT T1 T t b,
has_type pc Gamma HT (tref T1 t b) T ->
exists pc', exists pc'', exists T1', exists T1'', exists b',
(has_type pc'' Gamma HT (tref T1 t b)(an (ref T1) b))/\
(subsum_r b b')/\
((an (ref T1) b')<:T)/\
(has_type pc' Gamma HT t T1')/\(T1' <: T1'')/\(subsum_r pc pc')/\(T1''<:T1)/\
(subsum_r pc (labelT T1')).
Proof. intros. remember (tref T1 t b) as e. induction H0. inversion Heqe.
inversion Heqe. inversion Heqe. inversion Heqe. inversion Heqe. inversion Heqe.
inversion Heqe. inversion Heqe. subst. exists pc. exists pc. exists T1. exists T1.
exists b. split. apply t_ref. apply H0. apply H1. split. apply sub_refl. split. apply subtyping_refl.
split. apply H0. split. apply subtyping_refl. split. apply sub_refl. split. apply subtyping_refl.
apply H1. inversion Heqe. inversion Heqe. 
apply IHhas_type in Heqe. inversion Heqe. exists x. inversion H3. exists x0. inversion H4. exists x1.
inversion H5. exists x2. inversion H6. exists x3. split. apply H7. split. apply H7. split. 
apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl. apply H7. apply H2. split. apply H7. split. apply H7. split.
apply subsum_r_trans with (a:=pc')(b:=pc)(c:=x). apply H1. apply H7. split. apply H7. apply subsum_r_trans with (a:=pc')(b:=pc)(c:=labelT x1).
apply H1. apply H7. Qed.

(*inversion of [has_type pc Gamma HT (tderef t) T]*)

Lemma inversion_tderef:forall pc Gamma HT t T,
has_type pc Gamma HT (tderef t) T ->
exists pc', exists T1, exists b', exists b'',
has_type pc' Gamma HT t (an (ref T1) b')/\(subsum_r b' b'')/\
((joinTs T1 b'')<:T)/\(subsum_r pc pc').  
Proof. intros. remember (tderef t) as e. induction H0. inversion Heqe. inversion Heqe. inversion Heqe. inversion Heqe. inversion Heqe.
inversion Heqe. inversion Heqe. inversion Heqe. inversion Heqe. subst. exists pc. exists T. exists b. exists b. split. apply H0. split.
apply sub_refl. split. apply subtyping_refl. apply sub_refl. inversion Heqe. 
apply IHhas_type in Heqe. inversion Heqe. exists x. inversion H3. exists x0. inversion H4. exists x1.
inversion H5. exists x2. split. apply H6. split. apply H6. split. apply subtyping_trans with (x:=T)(y:=T).
apply subtyping_refl. apply H6. apply H2. apply subsum_r_trans with (a:=pc')(b:=pc)(c:=x).
apply H1. apply H6. Qed.
 
(*inversion of [has_type pc Gamma HT (tassign t1 t2) T]*)

Lemma inversion_tassign:forall pc Gamma HT t1 t2 T,
has_type pc Gamma HT (tassign t1 t2) T ->
exists pc',exists T1, exists T1', exists b,
has_type pc' Gamma HT (tassign t1 t2)(an unit (labelT T1))/\
has_type pc' Gamma HT t1 (an (ref T1) b)/\
has_type pc' Gamma HT t2 T1'/\
(T1'<:T1)/\(subsum_r pc pc')/\(subsum_r (joins pc' b)(labelT T1))/\
((an unit (labelT T1))<:T).
Proof. intros. remember (tassign t1 t2) as t. induction H0. inversion Heqt.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. subst. exists pc.
exists T. exists T. exists b. split. apply t_assign with (b:=b)(T:=T). reflexivity. apply H1.
apply H0_. apply H0_0. split. apply H0_. split. apply H0_0. split. apply subtyping_refl. split.
apply sub_refl. split. apply H1. apply subtyping_refl. apply IHhas_type in Heqt.
inversion Heqt. exists x. inversion H3. exists x0. inversion H4. exists x1. inversion H5. exists x2.
split. apply H6. split. apply H6. split. apply H6. split. apply H6. split. apply subsum_r_trans with (a:=pc')(b:=pc)(c:=x).
apply H1. apply H6. split. apply H6. apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl. apply H6. apply H2. Qed.
(*#############################*)


(*some ill-typed terms*)
(**
Case 1: undefined or ill-defined free variables
*)
Example has_type_not_tvar_1:forall pc HT,
 ~has_type pc empty_context HT 
           (tvar (Id 0))
           (an int L).
Proof. intros. intros contra. apply inversion_tvar in contra. inversion contra.
       inversion H0. inversion H1.
Qed.
Example has_type_not_tvar_2:forall pc HT,
~has_type pc (Cupdate empty_context (Id 0) (Some (an int H))) HT
         (tvar (Id 0))
         (an (fn (an int L) L (an int L)) H).
Proof. intros. intros contra. apply inversion_tvar in contra. inversion contra.
       rewrite->Cupdate_eq in H0. inversion H0. inversion H1. subst.
       inversion H2. Qed.
Example has_type_not_tvar_3:forall pc HT,
~has_type pc (Cupdate empty_context (Id 1) (Some (an unit H))) HT
          (tvar (Id 0))
          (an (ref (an int L)) L).
Proof. intros. intros contra. apply inversion_tvar in contra. inversion contra.
       assert (beq_id (Id 1)(Id 0) = false). compute. reflexivity. apply Cupdate_neq with (T:=Some (an unit H))(St:=empty_context) in H1.
       rewrite->H1 in H0. inversion H0. inversion H2. Qed.
Example has_type_not_tvar_4:forall pc HT n b,
~has_type pc empty_context HT (tvar (Id n)) (an unit b).
Proof. intros. intros contra. apply inversion_tvar in contra. inversion contra. inversion H0.
inversion H1. Qed.
(*Case 2: ill-typed abstractions*)
(**
a. ill-typed abstractions whose body contains undefined
        free variables
*)
Example has_type_not_tabs_a1:forall pc pc' HT,
~has_type pc empty_context HT
          (tabs (Id 0) (an int L)(tvar  (Id 1)) H)
          (an (fn (an int L) pc' (an int L)) H).
Proof. intros. intros contra. apply inversion_tabs in contra. inversion contra.
       inversion H0. inversion H1.  inversion H2. inversion H3. inversion H4. inversion H5.
       inversion H6. inversion H8.
       apply inversion_tvar in H9. inversion H9. inversion H11. assert (beq_id (Id 0)(Id 1) = false).
       apply not_eq_beq_id_false. intros contra'. inversion contra'.
       apply Cupdate_neq with (T:=Some (an int L))(St:=empty_context) in H14.
       rewrite->H14 in H12. inversion H12. Qed.
Example has_type_not_tabs_a2:forall pc pc' HT,
~has_type pc (Cupdate empty_context (Id 1)(Some (an int L))) HT 
          (tabs (Id 0)(an int L)(tvar (Id 2)) L)
          (an (fn (an int L) pc' (an int H)) L).
Proof. intros. intros contra. apply inversion_tabs in contra. inversion contra.
       inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5.
       inversion H6. inversion H8.
       apply inversion_tvar in H9. inversion H9. inversion H11. 
       assert (beq_id (Id 0)(Id 2) = false). apply not_eq_beq_id_false.
       intros contra'. inversion contra'. apply Cupdate_neq with (T:=Some (an int L))(St:=Cupdate empty_context (Id 1)(Some (an int L))) in H14.
       rewrite->H14 in H12. assert (beq_id (Id 1)(Id 2)=false). apply not_eq_beq_id_false.
       intros contra'. inversion contra'.
       apply Cupdate_neq with (T:=Some (an int L))(St:=empty_context) in H15. rewrite->H15 in H12. 
       inversion H12.
Qed.

(**
b. ill-typed abstraction whose type is not a function type
*)
Example has_type_not_tabs_b1:forall pc HT,
~has_type pc empty_context HT
    (tabs (Id 0)(an int H)(tvar (Id 1)) H) 
    (an int H).
Proof. intros. intros contra. apply inversion_tabs in contra. inversion contra.
       inversion H0. inversion H1. inversion H2. inversion H3. inversion H4.
       inversion H5. inversion H6. inversion H8. inversion H10. inversion H12.
       inversion H14. inversion H16. inversion H18. inversion H20.
Qed.
Example has_type_not_tabs_b2:forall pc HT,
~has_type  pc empty_context HT 
          (tabs (Id 0)(an int L)(tvar (Id 0)) H) 
          (an (ref (an unit H)) H).
Proof. intros. intros contra. apply inversion_tabs in contra. inversion contra.
       inversion H0. inversion H1. inversion H2. inversion H3. inversion H4.
       inversion H5. inversion H6. inversion H8. inversion H10. inversion H12.
       inversion H14. inversion H16. inversion H18. inversion H20.
Qed. 
(**
c. ill-typed abstraction whose body is not typable under its 
   side-effect label [pc']
*)
Example has_type_not_tabs_c1:forall pc Gamma,
~has_type pc Gamma [an int L]
          (tabs (Id 0)(an unit L)(tassign (tloc (an int L) 0 L)(tcon 0 L)) L)
          (an (fn (an unit L) H (an unit L)) L).
Proof. intros. intros contra. apply inversion_tabs in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5.
inversion H6. inversion H8. inversion H10. inversion H12. inversion H14. inversion H16.
inversion H18. inversion H20. destruct x4. inversion H30. destruct x3. inversion H11.
apply inversion_tassign in H9. subst. destruct x1. destruct r. inversion H32. inversion H32.
destruct s. inversion H9. inversion H21. inversion H22. inversion H23. inversion H24. inversion H27.
inversion H29. inversion H34. inversion H36. inversion H38. destruct x1. inversion H37. simpl in H39.
destruct x3. simpl in H39. destruct s. inversion H39. simpl in H40. destruct x0. destruct r0. inversion H40.
inversion H40. destruct s. inversion H40. inversion H43. inversion H17. inversion H43. inversion H40. inversion H32.
inversion H23. inversion H32. Qed.
Example has_type_not_tabs_c2:forall pc Gamma HT,
~has_type pc Gamma HT
          (tabs (Id 0)(an unit L)(tref (an int L)(tcon 0 L) H) L)
          (an (fn (an unit L) H (an (ref (an int L)) H)) L).
Proof. intros. intros contra. apply inversion_tabs in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5.
inversion H6. inversion H8. inversion H10. inversion H12. inversion H14. inversion H16.
inversion H18. destruct x4. inversion H20. inversion H30. destruct x3.  inversion H11.
apply inversion_tref in H9. inversion H9. inversion H21.  inversion H22. inversion H23.
inversion H24. inversion H25. inversion H27. inversion H29. inversion H31. inversion H33.
inversion H35. inversion H37. assert (x6<:an int L). apply subtyping_trans with (x:=x7)(y:=x7).
apply subtyping_refl. apply H34. apply H38. destruct x6. destruct r. destruct s. simpl in H39.
inversion H39. inversion H40. inversion H43. inversion H40. inversion H40. inversion H40.
Qed.
(**
d. ill-typed abstraction whose body is not typable under its heap_typing [HT]
*)
Example has_type_not_tabs_d1:forall pc pc' Gamma,
~has_type pc Gamma []
          (tabs (Id 0)(an unit H)(tloc (an unit L) 0 L) H)
          (an (fn (an unit H) pc' (an (ref (an unit L)) L)) H).
Proof. intros. intros contra. apply inversion_tabs in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5.
inversion H6. inversion H8. apply inversion_tloc in H9. inversion H9. inversion H11.
inversion H12. inversion H13. simpl in H14. inversion H14. Qed.
(**
e. ill-typed abstraction whose body is a ill-typed term
*)
Example has_type_not_tabs_e1:forall pc Gamma HT,
~has_type pc Gamma HT
          (tabs (Id 0)(an unit H)(tcon 0 H) L)
          (an (fn (an unit H) L (an int L)) L).
Proof. intros. intros contra. apply inversion_tabs in contra. inversion contra.
       inversion H0. inversion H1. inversion H2. inversion H3. inversion H4.
       inversion H5. inversion H6. inversion H8. inversion H10. inversion H12.
       inversion H14. inversion H16. inversion H18. inversion H20. subst. inversion H32.
       subst. destruct b. inversion H17. subst. destruct b. apply inversion_tcon in H9.
       inversion H9. inversion H21. inversion H22. inversion H25. inversion H28. inversion H33.
       inversion H35. subst. destruct b. inversion H34. subst. inversion H37. inversion H38.
       inversion H17. inversion H25. inversion H32. inversion H24. Qed.
Example has_type_not_tabs_e2:forall pc Gamma HT,
~has_type pc Gamma HT
          (tabs (Id 0)(an unit L)(tunit H) L)
          (an (fn (an unit L) L (an unit L)) L).
Proof. intros. intros contra. apply inversion_tabs in contra.  inversion contra. inversion H0.
inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6. inversion H8.
inversion H10. inversion H12. inversion H14. inversion H16. inversion H18. inversion H20. subst.
destruct x1. destruct r. inversion H32. inversion H32. destruct s.  destruct x0. destruct r.
inversion H17. inversion H17. destruct s. apply inversion_tunit in H9. inversion H9. inversion H21.
inversion H22. inversion H23. inversion H25. inversion H28. destruct x1. destruct r. inversion H33.
inversion H33. destruct s. inversion H27. subst. inversion H29. inversion H33. inversion H36. inversion H33.
inversion H17. inversion H23. inversion H17. inversion H32. inversion H23. inversion H32. Qed.
(*Case 3: ill-typed constants*)
Example has_type_not_tcon_1:forall pc Gamma HT n,
~has_type pc Gamma HT 
         (tcon n H) 
         (an int L).
Proof. intros. intros contra. apply inversion_tcon in contra.
inversion contra. inversion H0. inversion H1. inversion H2. 
inversion H4. inversion H6. inversion H7. subst. inversion H8.
inversion H9. Qed.
Example has_type_not_tcon_2:forall pc Gamma HT n b,
~has_type pc Gamma HT (tcon n b) (an (fn (an int L) L (an int L)) L).
Proof. intros. intros contra. apply inversion_tcon in contra.
inversion contra. inversion H0. inversion H1. inversion H2.
inversion H4. inversion H6. subst. inversion H8. Qed.
Example has_type_not_tcon_3:forall pc Gamma HT n b,
~has_type pc Gamma HT 
          (tcon n b)
          (an (ref (an unit L)) H).
Proof. intros. intros contra. apply inversion_tcon in contra. inversion contra. inversion H0.
inversion H1. inversion H2. inversion H4. inversion H6. subst. inversion H8. Qed.
(*Case 4: ill-typed units*)

Example has_type_not_tunit_1:forall pc Gamma HT,
~has_type pc Gamma HT 
          (tunit H)
          (an unit L).
Proof. intros. intros contra. apply inversion_tunit in contra. inversion contra. inversion H0.
inversion H1. inversion H2. inversion H4. inversion H6. destruct x0. destruct r. inversion H8.
inversion H8. destruct s. inversion H5. subst. inversion H7. inversion H8. inversion H11. inversion H8.
Qed.
Example has_type_not_tunit_2:forall pc Gamma HT,
~has_type pc Gamma HT
          (tunit H)
          (an int H).
Proof. intros. intros contra. apply inversion_tunit in contra. inversion contra. inversion H0. inversion H1.
inversion H2. inversion H4. inversion H6. subst. inversion H8. Qed.
Example has_type_not_tunit_3:forall pc Gamma HT,
~has_type pc Gamma HT
          (tunit L)
          (an (ref (an (fn (an int H) H (an int H)) L)) L).
Proof. intros. intros contra. apply inversion_tunit in contra. inversion contra. inversion H0. inversion H1.
inversion H2. inversion H4. inversion H6. subst. inversion H8. Qed.
(*Case 5: ill-typed locations*)

Example has_type_not_tloc_1:forall pc Gamma n b T,
~has_type pc Gamma []
          (tloc T n b) 
          (an (ref T) b).
Proof. intros. intros contra. apply inversion_tloc in contra. inversion contra. 
       inversion H0. inversion H1. inversion H2. destruct n. simpl in H3. inversion H3. simpl in H3.
       inversion H3. Qed. 

Example has_type_not_tloc_2:forall pc Gamma,
~has_type pc Gamma [an int L]
             (tloc (an int H) 0 H)
             (an (ref (an int H)) H).
Proof. intros. intros contra. apply inversion_tloc in contra. inversion contra. inversion H0. inversion H1. inversion H2.
simpl in H3. inversion H3. Qed.

Example has_type_not_tloc_3:forall pc Gamma HT n b T,
~has_type pc Gamma HT
           (tloc T n b)
           (an int b).
Proof. intros. intros contra. apply inversion_tloc in contra. inversion contra. inversion H0.
inversion H1. inversion H2. inversion H4. inversion H6. inversion H8. subst. inversion H10. Qed.
(*Case 6: ill-typed protect*)
(**
a. the label of the protect is not guarded by the "lower bound" security level
*)    
Example has_type_not_tprot_a1:forall pc Gamma HT,
~has_type pc Gamma HT
         (tprot H (tcon 0 L))
         (an int L).
Proof. intros. intros contra. apply inversion_tprot in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H4. inversion H6. apply inversion_tcon in H5.
inversion H5. inversion H9. inversion H10. inversion H11. inversion H13. inversion H15. subst. inversion H11.
inversion H14. inversion H19. destruct x0. destruct r. destruct x. destruct r. simpl in H3. inversion H3. inversion H24.
inversion H8. inversion H8. inversion H8. inversion H21. inversion H21.  inversion H21.
Qed.
Example has_type_not_tprot_a2:forall pc Gamma HT,
~has_type pc Gamma HT 
          (tprot H (tunit L))
          (an unit L).
Proof. intros. intros contra. apply inversion_tprot in contra. inversion contra. inversion H0. 
inversion H1. inversion H2. inversion H4. inversion H6. apply inversion_tunit in H5. inversion H5.
inversion H9. inversion H10. inversion H11. inversion H13. inversion H15. subst. destruct x0. destruct r.
destruct x. destruct r. inversion H3. inversion H3. simpl in H3. inversion H3. inversion H18. inversion H3.
inversion H17. destruct x. destruct r. inversion H8. inversion H8. simpl in H3. inversion H3. inversion H18.
inversion H8. inversion H17. Qed.
Example has_type_not_tprot_a3:forall pc Gamma HT,
~has_type pc Gamma HT
          (tprot H (tabs (Id 0)(an int L)(tvar (Id 0)) L))
          (an (fn (an int L) L (an int L)) L).
Proof. intros. intros contra. apply inversion_tprot in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H4. inversion H6. apply inversion_tabs in H5.
inversion H5. inversion H9. inversion H10. inversion H11. inversion H12. inversion H13. inversion H14.
inversion H15. inversion H17. inversion H19. inversion H21. inversion H23. inversion H25. inversion H27.
destruct x0. destruct r. inversion H29. destruct x. destruct r. inversion H8. simpl in H3. inversion H3.
inversion H35. inversion H8. inversion H8. inversion H29. inversion H29.
Qed.
Example has_type_not_tprot_a4:forall pc Gamma,
~has_type pc Gamma [an unit H]
          (tprot H (tloc (an unit H) 0 L))
          (an (ref (an unit H)) L).
Proof. intros. intros contra. apply inversion_tprot in contra. inversion contra. inversion H0. inversion H1. inversion H2.
inversion H4. inversion H6. apply inversion_tloc in H5. inversion H5. inversion H9. inversion H10. inversion H11. inversion H13.
inversion H15. inversion H17. subst. destruct x0. destruct r. inversion H19. inversion H19. inversion H19. destruct x. destruct r.
inversion H8. inversion H8. inversion H8. simpl in H3. inversion H3. inversion H16. Qed.
(**
b. the protected term is not typable under the new security context,[joins pc b],
   the heap typing,[HT], or the typing context,[Gamma]
*)
Example has_type_not_tprot_b1:forall pc Gamma,
~has_type pc Gamma [an int L]
          (tprot H (tassign (tloc (an int L) 0 L)(tcon 0 L)))
          (an unit H).
Proof. intros. intros contra. apply inversion_tprot in contra. inversion contra. inversion H0. inversion H1. inversion H2. inversion H4.
inversion H6. assert (joins pc H=H). destruct pc. reflexivity. reflexivity. rewrite->H9 in H7. clear H9. destruct x1. inversion H7.
apply inversion_tassign in H5. inversion H5. inversion H9. inversion H10. inversion H11. inversion H12. inversion H14. inversion H16.
inversion H18. inversion H20. inversion H22. apply inversion_tloc in H15. inversion H15. inversion H25. inversion H26. inversion H27. inversion H29.
inversion H31. inversion H33. subst. destruct x2. destruct r. destruct s. simpl in H23. destruct x1. inversion H21. simpl in H23. inversion H23.
inversion H35. inversion H35. inversion H35. inversion H35. Qed.
Example has_type_not_tprot_b2:forall pc Gamma HT,
~has_type pc Gamma HT
         (tprot H (tref (an int L)(tcon 0 L) L))
         (an (ref (an int L)) H).
Proof. intros. intros contra. apply inversion_tprot in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H4.  inversion H6.
assert (joins pc H = H). destruct pc. reflexivity. reflexivity. rewrite->H9 in H7. clear H9.
destruct x1. inversion H7. apply inversion_tref in H5. inversion H5. inversion H9. inversion H10. inversion H11. inversion H12.
inversion H13. inversion H15. inversion H17. inversion H19. inversion H21. inversion H23. inversion H25. assert (x3<:an int L). 
apply subtyping_trans with (x:=x4)(y:=x4). apply subtyping_refl. apply H22. apply H26. destruct x3. destruct r. destruct s.
simpl in H27. inversion H27. inversion H28. inversion H31. inversion H28. inversion H28. inversion H28. Qed.
Example has_type_not_tprot_b3:forall pc Gamma,
~has_type pc Gamma []
         (tprot L (tloc (an int L) 0 L))
         (an (ref (an int L)) L).
Proof. intros. intros contra. apply inversion_tprot in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H4. apply inversion_tloc in H5.
inversion H5. inversion H7. inversion H8. inversion H9. simpl in H10. inversion H10.
Qed.
Example has_type_not_tprot_b4:forall pc HT,
~has_type pc empty_context HT
          (tprot H (tvar (Id 0)))
          (an int H).
Proof. intros. intros contra. apply inversion_tprot in contra. inversion contra. inversion H0.
inversion H1. inversion H2. inversion H4. apply inversion_tvar in H5. inversion H5. inversion H7.
inversion H8. Qed.

(*Case 7: ill-typed applications*)
(**
a. the type of the second argument of the application does not match 
   that of the input argument of the abstraction
*)
Example has_type_not_tapp_a1:forall pc HT,
~has_type pc empty_context HT
          (tapp (tabs (Id 0)(an int L)(tcon 2 L) H)(tcon 1 H))
          (an int H).
Proof. intros. intros contra. apply inversion_tapp in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6.
inversion H7. inversion H8. inversion H9. inversion H11. inversion H13. inversion H15. inversion H17.
apply inversion_tabs in H12. inversion H12. inversion H20. inversion H21. inversion H22.
inversion H23. inversion H24. inversion H25. inversion H26. inversion H28.  inversion H30.
inversion H32. inversion H34. inversion H36. inversion H38. destruct x9. destruct r. destruct x. destruct r.
destruct s. destruct s0. destruct x2. destruct r. destruct s. destruct x3. destruct r. destruct s. apply inversion_tcon in H16.
inversion H16. inversion H41. inversion H42. inversion H43. inversion H45. inversion H47. destruct x3. inversion H48. subst.
inversion H49. inversion H46. inversion H18. inversion H43. inversion H18. inversion H18. inversion H18. inversion H14. inversion H51.
inversion H55. inversion H14. inversion H51. inversion H14. inversion H51. inversion H14. inversion H51. inversion H40. inversion H51.
inversion H55. inversion H35. inversion H43. inversion H40. inversion H51. inversion H40. inversion H51. inversion H40. inversion H51.
inversion H35. inversion H35. inversion H35. Qed.

Example has_type_not_tapp_a2:forall pc HT,
~has_type pc empty_context HT
         (tapp (tabs (Id 0)(an int L)(tvar (Id 0)) L)(tprot H (tcon 1 L)))
         (an int L).
Proof. intros. intros contra. apply inversion_tapp in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6. inversion H7. inversion H8.
inversion H9. inversion H11. inversion H13. inversion H15. inversion H17. inversion H19.
apply inversion_tabs in H12. inversion H12. inversion H22. inversion H23. inversion H24. inversion H25.
inversion H26. inversion H27. inversion H28. inversion H30. inversion H32. inversion H34. inversion H36. inversion H38. inversion H40.
destruct x9. destruct r. destruct s. destruct x. destruct r. destruct s. destruct x2. destruct r. destruct s. 
apply inversion_tprot in H16. inversion H16. inversion H43. inversion H44. inversion H45. inversion H47. inversion H49. apply inversion_tcon in H48.
inversion H48. inversion H52. inversion H53. inversion H54. inversion H56. inversion H58. subst. destruct x2. destruct r. destruct x. destruct r. simpl in H46.
destruct x3. destruct r. destruct s1. inversion H46. inversion H57. inversion H18. inversion H57. inversion H18. inversion H18. inversion H18. inversion H51.
inversion H51. inversion H51. inversion H60. inversion H60. inversion H60. inversion H14. inversion H53. inversion H57. inversion H14. inversion H53. inversion H14.
inversion H53. inversion H14. inversion H53. inversion H42. inversion H53. inversion H57. inversion H42. inversion H53. inversion H42. inversion H53. inversion H42.
inversion H53. inversion H37. inversion H45. inversion H37. inversion H37. inversion H37. Qed.
(**
b. the argument of the application is not typable due to the security context
   , the heap typing ,or the typing context imposed upon it
*)
(*security context*)
Example has_type_not_tapp_b1:forall HT,
~has_type H empty_context HT
          (tapp (tabs (Id 0)(an int L)(tref (an int L)(tcon 0 L) L) L)(tcon 0 L))
          (an (ref (an int L)) L).
Proof. intros. intros contra. apply inversion_tapp in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6.
inversion H7. inversion H8. inversion H9. inversion H11. inversion H13. inversion H15. inversion H17.
inversion H19. destruct x6. inversion H20. simpl in H10. subst.
apply inversion_tabs in H12. inversion H12. inversion H10. inversion H22. inversion H23. inversion H24.
inversion H25. inversion H26. inversion H27. inversion H29. inversion H31. inversion H33. inversion H35.
inversion H37. inversion H39. inversion H41. destruct x12. inversion H51. destruct x11. inversion H32.
apply inversion_tref in H30. inversion H30. inversion H54. inversion H55. inversion H56. inversion H57.
inversion H58. inversion H60. inversion H62. inversion H64. inversion H66. inversion H68. inversion H70.
apply inversion_tcon in H65. inversion H65. inversion H73. inversion H74. inversion H75. inversion H77.
inversion H79. subst. destruct x14. destruct r. simpl in H72. destruct s. inversion H72. destruct x15. destruct r. destruct s.
inversion H67. inversion H44. inversion H71. inversion H44. inversion H67. inversion H71. inversion H71.
inversion H81. inversion H81. inversion H81. Qed.
Example has_type_not_tapp_b2:
~has_type H empty_context [an int L]
         (tapp (tabs (Id 0)(an unit L)(tvar (Id 0)) L)(tassign (tloc (an int L) 0 L)(tcon 0 L)))
         (an unit L).
Proof. intros. intros contra. apply inversion_tapp in contra. inversion contra.  inversion H0. inversion H1. inversion H2.
inversion H3. inversion H4. inversion H5. inversion H6. inversion H7. inversion H8. inversion H9. inversion H11. inversion H13.
inversion H15. inversion H17. inversion H19. destruct x6. inversion H20. apply inversion_tassign in H16.
inversion H16. inversion H22. inversion H23. inversion H24. inversion H25. inversion H27. inversion H29.
inversion H31. inversion H33. inversion H35. destruct x6. inversion H34. simpl in H36. apply inversion_tloc in H28.
inversion H28. inversion H38. inversion H39. inversion H40. inversion H42. inversion H44.
inversion H46. subst. destruct x9. destruct r. destruct s. simpl in H36. inversion H36. inversion H48. inversion H48.
inversion H48. inversion H48. Qed.
(*heap typing*)
Example has_type_not_tapp_b3:forall pc Gamma,
~has_type pc Gamma []
          (tapp (tabs (Id 0)(an (ref (an int L)) L)(tvar (Id 0))L)(tloc (an int L) 0 L))
          (an (ref (an int L)) L).
Proof. intros. intros contra. apply inversion_tapp in contra. inversion contra. inversion H0.
inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6. inversion H7. inversion H8.
inversion H9. inversion H11. inversion H13. inversion H15. apply inversion_tloc in H16. inversion H16. inversion H18.
inversion H19. inversion H20. simpl in H21. inversion H21. Qed.
(*typing context*)
Example has_type_not_tapp_b4:forall pc HT,
~has_type pc empty_context HT
         (tapp (tabs (Id 0)(an int L)(tcon 0 L) L)(tvar (Id 0)))
         (an int L).
Proof. intros. intros contra. apply inversion_tapp in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5.
inversion H6. inversion H7. inversion H8. inversion H9. inversion H11. inversion H13.
inversion H15. apply inversion_tvar in H16. inversion H16. inversion H18. 
inversion H19. Qed.
(**
c. the first argument of the application is not an abstraction
*)
Example has_type_not_tapp_b5:forall pc Gamma HT,
~has_type pc Gamma HT
         (tapp (tcon 0 L)(tcon 1 L))
         (an int L).
Proof. intros. intros contra. apply inversion_tapp in contra. inversion contra. inversion H0.
inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6. inversion H7.
inversion H8. inversion H9. inversion H11. apply inversion_tcon in H12. inversion H12. inversion H14.
inversion H15.  inversion H16. inversion H18. inversion H20. subst. inversion H22. Qed.

(*Case 8: ill-typed reference*)
(**
a. the cell being rewritten is not guarded by the security context,[pc]
*)
Example has_type_not_tref_a1:forall Gamma HT,
~has_type H Gamma HT 
          (tref (an int L)(tcon 0 L) H)
          (an (ref (an int L)) H).
Proof. intros. intros contra. apply inversion_tref in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. inversion H6.
inversion H8. inversion H10. inversion H12. inversion H14. inversion H16. destruct x2.
destruct r. destruct s. apply inversion_tcon in H11. inversion H11. inversion H19. inversion H20.
inversion H21. inversion H23. inversion H25. subst. destruct x1. destruct r. simpl in H18. destruct s.
inversion H18. inversion H13. inversion H28. inversion H27. inversion H27. inversion H27. inversion H17.
inversion H21. inversion H17. inversion H17. inversion H17. Qed.
(**
b. the type of the cell being rewritten does not match the "initial type"
*)
Example has_type_not_tref_b1:forall Gamma HT,
~has_type L Gamma HT 
          (tref (an int L)(tcon 0 H) L)
          (an (ref (an int L)) L).
Proof. intros. intros contra. apply inversion_tref in contra. inversion contra. 
inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. inversion H6.
inversion H8. inversion H10. inversion H12. inversion H14. inversion H16. destruct x2. destruct r.
destruct s. destruct x1. destruct r. destruct s. apply inversion_tcon in H11. inversion H11. inversion H19.
inversion H20. inversion H21. inversion H23. inversion H25. subst. destruct x4. inversion H26. inversion H27.
inversion H28. inversion H13. inversion H21. inversion H13. inversion H13. inversion H13. inversion H17.
inversion H21. inversion H17. inversion H17. inversion H17. Qed.
(**
c. ill-typed reference whose type is not a reference type
*)
Example has_type_not_tref_c1:forall pc Gamma HT T1 t b,
~has_type pc Gamma HT 
          (tref T1 t b)
          (an int b).
Proof. intros. intros contra. apply inversion_tref in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. inversion H6.
inversion H8. inversion H9. Qed.
(**
d. ill-typed reference whose subterm is ill-typed
*)
Example has_type_not_tref_d1:forall HT,
~has_type L empty_context HT
          (tref (an int L)(tvar (Id 0)) H)
          (an (ref (an int L)) H).
Proof. intro. intros contra. apply inversion_tref in contra. inversion contra. inversion H0.
inversion H1. inversion H2. inversion H3. inversion H4. inversion H6. inversion H8. inversion H10.
apply inversion_tvar in H11. inversion H11.  inversion H13. inversion H14. Qed.

(*Case 9: ill-typed dereference*)
(**
a. ill-typed dereference whose subterm is not a reference
*)
Example has_type_not_tderef_a1:forall pc Gamma HT,
~has_type pc Gamma HT
          (tderef (tunit H))
          (an unit H).
Proof. intros. intros contra. apply inversion_tderef in contra. inversion contra. inversion H0.
inversion H1. inversion H2. inversion H3. apply inversion_tunit in H4. inversion H4. inversion H6.
inversion H7. inversion H8. inversion H10. inversion H12. subst. inversion H14. Qed.
(**
b. ill-typed dereference whose subterm is ill-typed due to the security context,
   the typing context, or the heap typing
*)
(*security context*)
Example has_type_tderef_b1:forall Gamma HT,
~has_type H Gamma HT
          (tderef (tref (an int L)(tcon 0 L) H))
          (an int H).
Proof. intros. intros contra. apply inversion_tderef in contra. inversion contra. inversion H0. inversion H1.
inversion H2. inversion H3. inversion H5. inversion H7. destruct x. inversion H9. apply inversion_tref in H4.
inversion H4. inversion H10. inversion H11. inversion H12. inversion H13. inversion H14. inversion H16. inversion H18.
inversion H20. inversion H22. inversion H24. inversion H26. destruct x5. destruct r. destruct s. apply inversion_tcon in H21.
inversion H21. inversion H29. inversion H30. inversion H31. inversion H33. inversion H35. subst. destruct x4. destruct r.
simpl in H28. destruct s. inversion H28. inversion H23. inversion H38. inversion H37. inversion H37. inversion H37. inversion H27.
inversion H31. inversion H27. inversion H27. inversion H27. Qed.
(*heap typing*)
Example has_type_tderef_b2:forall pc Gamma,
~has_type pc Gamma []
          (tderef (tloc (an int L) 0 L))
          (an int L).
Proof. intros. intros contra. apply inversion_tderef in contra. inversion contra. inversion H0. inversion H1. inversion H2. inversion H3.
apply inversion_tloc in H4. inversion H4. inversion H6. inversion H7. inversion H8. simpl in H9. inversion H9. Qed.
(*typing context*)
Example has_type_tderef_b3:forall pc HT,
~has_type pc empty_context HT
          (tderef (tvar (Id 0)))
          (an int L).
Proof. intros. intros contra. apply inversion_tderef in contra. inversion contra. inversion H0. inversion H1. inversion H2. inversion H3.
apply inversion_tvar in H4. inversion H4. inversion H6. inversion H7. Qed.

(*Case 10: ill-typed assignment*)
(**
a. ill-typed assignment whose "access type" is either not guarded by 
   security context or by the security level of the pointer
*)
Example has_type_tassign_a1:forall Gamma,
~has_type L Gamma [an int L]
          (tassign (tloc (an int L) 0 H)(tcon 1 L))
          (an unit L).
Proof. intros. intros contra. apply inversion_tassign in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H5. inversion H7.
inversion H9. inversion H11. inversion H13.  apply inversion_tloc in H6. inversion H6.
inversion H16. inversion H17. inversion H18. inversion H20. inversion H22. inversion H24.
subst. destruct x5. inversion H25. destruct x2. inversion H26. inversion H23. destruct x0. 
destruct r. destruct s. simpl in H14. assert (joins x H=H). destruct x. reflexivity. reflexivity.
rewrite->H21 in H14. clear H21. inversion H14. inversion H26. inversion H26. inversion H26.
inversion H26. Qed.

Example has_type_tassign_a2:forall Gamma,
~has_type H Gamma [an int L]
          (tassign (tloc (an int L) 0 L)(tcon 1 L))
          (an unit L).
Proof. intros. intros contra. apply inversion_tassign in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H5. inversion H7.
inversion H9. inversion H11. inversion H13. destruct x. inversion H12. simpl in H14.
apply inversion_tloc in H6. inversion H6. inversion H16. inversion H17. inversion H18.
inversion H20. inversion H22. inversion H24. subst. destruct x0. destruct r. destruct s.
simpl in H14. inversion H14. inversion H26. inversion H26. inversion H26. inversion H26.
Qed.
(**
b. ill-typed assignment which tries to overwrite a cell with another one with different
   type
*)
Example has_type_tassign_a3:forall Gamma,
~has_type L Gamma [an int L]
         (tassign (tloc (an int L) 0 L)(tcon 1 H))
         (an unit L).
Proof. intros. intros contra. apply inversion_tassign in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H5. inversion H7.
inversion H9. apply inversion_tcon in H8. inversion H8. inversion H12. inversion H13.
inversion H14. inversion H16. inversion H18. destruct x5. inversion H19. subst. destruct x1.
destruct r. destruct s. inversion H20. inversion H21. apply inversion_tloc in H6. inversion H6.
inversion H15. inversion H17. inversion H21. inversion H23. inversion H25. inversion H27.
subst. destruct x0. destruct r. destruct s. inversion H10. inversion H30. inversion H29.
inversion H29. inversion H29. inversion H29. inversion H20. inversion H20. inversion H20.
Qed.
Example has_type_tassign_a4:forall pc Gamma HT,
~has_type pc Gamma HT
          (tassign (tloc (an int L) 0 L)(tunit L))
          (an unit L).
Proof. intros. intros contra. apply inversion_tassign in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H5. inversion H7.
apply inversion_tunit in H8. inversion H8. inversion H10. inversion H11. inversion H12.
inversion H14. inversion H16. subst. destruct x1. destruct r. inversion H18. inversion H18.
apply inversion_tloc in H6. inversion H6. inversion H13. inversion H15. inversion H19.
inversion H21. inversion H23. inversion H25. subst. destruct x0. destruct r. inversion H9.
inversion H22. inversion H27. inversion H27. inversion H27. inversion H18. Qed.
(**
c. ill-typed assignment whose first argument is  not a pointer
*)
Example has_type_tassign_a5:forall pc Gamma HT,
~has_type pc Gamma HT
          (tassign (tcon 0 L)(tcon 0 L))
          (an unit L).
Proof. intros. intros contra. apply inversion_tassign in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H5. apply inversion_tcon in H6.
inversion H6. inversion H8. inversion H9. inversion H10. inversion H12. inversion H14. subst.
inversion H16. Qed.
(**
d. ill-typed assignment whose subterms are ill-typed due to either the security context,
the heap typing, or the typing context
*)
(*security context*)
Example has_type_tassign_a6:forall Gamma,
~has_type H Gamma [an (ref (an int L)) H]
            (tassign (tloc (an (ref (an int L)) H) 0 L)(tref (an int L)(tcon 0 L)H ))
            (an unit H).
Proof. intros. intros contra. apply inversion_tassign in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H5. inversion H7. inversion H9.
inversion H11. inversion H13. destruct x. inversion H12. apply inversion_tref in H8. inversion H8.
inversion H16. inversion H17.  inversion H18. inversion H19. inversion H20. inversion H22. inversion H24.
inversion H26. inversion H28. inversion H30. inversion H32. assert (x4<:an int L). apply subtyping_trans with (x:=x5)(y:=x5).
apply subtyping_refl. apply H29. apply H33. destruct x4. destruct r. destruct s. simpl in H34. inversion H34. inversion H35.
inversion H38. inversion H35. inversion H35. inversion H35. Qed.
(*typing_context*)
Example has_type_tassign_a7:forall pc,
~has_type pc empty_context [an int H]
          (tassign (tloc (an int H) 0 L)(tvar (Id 0)))
          (an unit H).
Proof. intros. intros contra. apply inversion_tassign in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H5. inversion H7. 
apply inversion_tvar in H8. inversion H8. inversion H10. inversion H11. Qed.
(*heap typing*)
Example has_type_tassign_a8:forall pc Gamma,
~has_type pc Gamma []
          (tassign (tloc (an int H) 0 L)(tcon 0 L))
          (an unit H).
Proof. intros. intros contra. apply inversion_tassign in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H5. apply inversion_tloc in H6.
inversion H6. inversion H8. inversion H9. inversion H10. simpl in H11. inversion H11. 
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

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.


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
      free_var x (tabs y T e b)
| e_tref :forall x T t b,
      free_var x t ->
      free_var x (tref T t b)
| e_tderef:forall x t,
      free_var x t ->
      free_var x (tderef t)
| e_tassign1:forall x t1 t2,
      free_var x t1 ->
      free_var x (tassign t1 t2)
| e_tassign2:forall x t1 t2,
      free_var x t2 ->
      free_var x (tassign t1 t2)
.

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
free_var (Id 0)(tref (an int L)(tvar (Id 0)) L).
Proof. apply e_tref. apply e_tvar. Qed.
Example test_free_var_9:
free_var (Id 0)(tderef (tapp (tabs (Id 0)(an unit L)(tloc (an int L) 0 L) L)(tvar (Id 0)))).
Proof. apply e_tderef. apply e_tapp2. apply e_tvar. Qed.
Example test_free_var_10:
free_var (Id 0)(tassign (tvar (Id 0))(tabs (Id 0)(an int L)(tvar (Id 0)) L)).
Proof. apply e_tassign1. apply e_tvar. Qed.
Example test_free_var_11:
free_var (Id 0)(tassign (tloc (an unit L) 0 L)(tabs (Id 1)(an int L)(tvar (Id 0)) L)).
Proof. apply e_tassign2. apply e_tabs. intros contra. inversion contra. apply e_tvar.
Qed.
Example test_free_var_12:
forall x n b, ~free_var x (tcon n b).
Proof. intros. intros contra. inversion contra. Qed.
Example test_free_var_13:
forall x T e b,~free_var x (tabs x T e b).
Proof. intros. intros contra. inversion contra. subst. apply H3. reflexivity.
Qed.
Example test_free_var_14:
forall x n b b', ~free_var x (tprot b (tcon n b')).
Proof. intros. intros contra. inversion contra. subst. inversion H2.
Qed.
Example test_free_var_15:
forall x T n b,~free_var x (tloc T n b).
Proof. intros. intros contra. inversion contra. Qed.
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
Lemma term_typable_empty_closed_1:forall pc Gamma HT x t T,
free_var x t ->
has_type pc Gamma HT t T ->
exists T',Gamma x = Some T'.
Proof. intros. generalize dependent T. generalize dependent Gamma.
generalize dependent HT. generalize dependent pc.
induction H0. 
Case ("tvar").
intros. apply inversion_tvar in H1. inversion H1. inversion H0.
        exists x0. apply H2.
Case ("tprot"). 
intros. apply inversion_tprot in H1. inversion H1. inversion H2.
        inversion H3. inversion H4. inversion H6. 
        apply IHfree_var in H7. inversion H7. exists x3. apply H9.
Case ("tapp1").
intros.  apply inversion_tapp in H1. inversion H1. inversion H2.
inversion H3. inversion H4. inversion H5. inversion H6. inversion H7.
inversion H8. inversion H9. inversion H10. inversion H11. inversion H13.
 apply IHfree_var in H14. inversion H14. exists x10. 
apply H16.
Case ("tapp2").
intros. apply inversion_tapp in H1. inversion H1. inversion H2.
inversion H3. inversion H4. inversion H5. inversion H6. inversion H7.
inversion H8. inversion H9. inversion H10. inversion H11. inversion H13.
inversion H15. inversion H17. 
apply IHfree_var in H18. inversion H18. exists x10. apply H20.
Case ("tabs").
intros.  apply inversion_tabs in H2. inversion H2. inversion H3. inversion H4.
inversion H5. inversion H6. inversion H7. inversion H8. inversion H9. inversion H11.
 apply IHfree_var in H12. inversion H12. 
apply not_eq_beq_id_false in H0. apply Cupdate_neq with (T:=Some T)(St:=Gamma)in H0.
rewrite->H0 in H14. exists x7. apply H14.
Case ("tref").
intros. apply inversion_tref in H1. inversion H1. inversion H2. inversion H3. inversion H4.
inversion H5. inversion H6. inversion H8. inversion H10. inversion H12.
apply IHfree_var in H13. inversion H13. exists x5. apply H15.
Case ("tderef").
intros. apply inversion_tderef in H1. inversion H1. inversion H2. inversion H3. inversion H4.
inversion H5. apply IHfree_var in H6. inversion H6. exists x4. apply H8.
Case ("tassign1").
intros. apply inversion_tassign in H1. inversion H1. inversion H2. inversion H3. inversion H4.
inversion H5. inversion H7. apply IHfree_var in H8. inversion H8. exists x4. apply H10.
Case ("tassign2").
intros. apply inversion_tassign in H1. inversion H1. inversion H2. inversion H3. inversion H4.
inversion H5. inversion H7. inversion H9. apply IHfree_var in H10. inversion H10. exists x4.
apply H12.
Qed.

Corollary term_typable_empty_closed: forall t pc HT T,
has_type pc empty_context HT t T ->
forall x, ~free_var x t.
Proof. intros t. induction t.
Case ("tvar").
intros. apply inversion_tvar in H0. inversion H0. inversion H1.
        inversion H2.
Case ("tprot"). 
intros. apply inversion_tprot in H0. inversion H0. inversion H1. inversion H2.
        inversion H3. inversion H5.  apply IHt with (x:=x)in H6.
        intros contra. inversion contra. subst. apply H6 in H10. inversion H10.
Case ("tcon").
intros. intros contra. inversion contra.
Case ("tabs").
intros. apply inversion_tabs in H0. inversion H0. inversion H1. inversion H2. inversion H3.
inversion H4. inversion H5. inversion H6. inversion H7. inversion H9. 
        intros contra. inversion contra.  subst. 
        apply term_typable_empty_closed_1 with (T:=x1)(Gamma:=Cupdate empty_context i (Some t))(pc:=x4)(HT:=HT)in H18.
        inversion H18. apply not_eq_beq_id_false in H15. apply Cupdate_neq with (T:=Some t)(St:=empty_context)in H15.
        rewrite->H15 in H12. inversion H12. apply H10.
Case ("tapp").
intros. apply inversion_tapp in H0. inversion H0. inversion H1. inversion H2. inversion H3.
      inversion H4. inversion H5. inversion H6. inversion H7. inversion H8. inversion H9.
      inversion H10. inversion H12. inversion H14. inversion H16.
      apply IHt1 with (x:=x)in H13. apply IHt2 with(x:=x) in H17. intros contra. inversion contra. 
      subst. apply H13 in H21. inversion H21. apply H17 in H21. inversion H21.
Case ("tunit").
intros. intros contra. inversion contra.
Case ("tref").
intros. apply inversion_tref in H0. inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5.
inversion H7. inversion H9. inversion H11. apply IHt with (x:=x)in H12. intros contra. inversion contra.  apply H12 in H16.
inversion H16.
Case ("tderef").
intros. apply inversion_tderef in H0. inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. apply IHt with(x:=x) in H5.
intros contra. inversion contra. apply H5 in H9. inversion H9.
Case ("tloc").
intros. intros contra. inversion contra.
Case ("tassign").
intros. apply inversion_tassign in H0. inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. inversion H6. inversion H8.
apply IHt1 with (x:=x) in H7. apply IHt2 with (x:=x) in H9. intros contra. inversion contra. subst. apply H7 in H13. inversion H13.
apply H9 in H13. inversion H13.
Qed.


Corollary change_context: forall pc Gamma Gamma' HT t T,
has_type pc Gamma HT t T ->
(forall x, free_var x t -> Gamma x = Gamma' x) ->
has_type pc Gamma' HT t T.
Proof.
intros. generalize dependent Gamma'. induction H0.
Case ("t_var").
intros. apply t_var. rewrite<-H0. symmetry. apply H1.
apply e_tvar.
Case ("t_con").
intros. apply t_con.
Case ("tunit").
intros. apply t_unit.
Case ("tloc").
intros. apply t_loc. apply H0.
Case ("t_abs").
intros. apply t_abs. apply IHhas_type. intros. remember (beq_id x x0) as BB.
        destruct BB.  apply beq_id_eq in HeqBB. rewrite->HeqBB. rewrite->Cupdate_eq.
        rewrite->Cupdate_eq. reflexivity. inversion HeqBB. symmetry in H4.
        apply Cupdate_neq with (T:=Some T)(St:=Gamma) in H4. rewrite->H4.
        inversion HeqBB. symmetry in H5. apply Cupdate_neq with (T:=Some T)(St:=Gamma') in H5.
        rewrite->H5. clear H4. clear H5. apply H1. apply e_tabs. intros contra. rewrite->contra in HeqBB.
        rewrite<-beq_id_refl in HeqBB. inversion HeqBB. apply H2.
Case ("t_prot").
intros. apply t_prot with (T:=T). apply IHhas_type. intros. apply H2.
apply e_tprot. apply H3. apply H1.
Case ("t_app").
intros. apply t_app with (T1:=T1)(T2:=T2)(b:=b). apply IHhas_type1. intros. apply H1. apply e_tapp1.
        apply H2. apply IHhas_type2. intros. apply H1. apply e_tapp2. apply H2.
        apply H0.
Case ("t_tref").
intros. apply t_ref. apply IHhas_type. intros. apply H2. apply e_tref. apply H3. apply H1.
Case ("t_deref").
intros. apply t_deref with (T:=T)(b:=b). apply IHhas_type. intros. apply H2. apply e_tderef. apply H3.
apply H1.
Case ("t_assign").
intros. apply t_assign with (b:=b)(T:=T). apply H0. apply H1. apply IHhas_type1. intros. apply H2.
apply e_tassign1. apply H3. apply IHhas_type2. intros. apply H2. apply e_tassign2. apply H3.
Case ("t_sub").
intros. apply t_sub with(pc:=pc) (T:=T). apply IHhas_type. apply H3. apply H1.
apply H2.
Qed.


Theorem s_p_t_1: forall t pc Gamma HT T,
has_type pc empty_context HT t T ->
has_type pc Gamma HT t T.
Proof. intros. apply change_context with (Gamma':=Gamma)in H0.
      apply H0. intros. apply term_typable_empty_closed with (x:=x)in H0.
      apply H0 in H1.  inversion H1.
Qed.

(*################s_p_t_1################*)
(**
Recall that in [step], we specify that substitution can only take place if 
the second argument of the application is reduced to be a value which is 
closed and typable under both high and low security context. 
In the following Theorem, we assume that the term used to replace bounded
variables is value.
*)
Lemma value_pc:forall pc pc' Gamma HT v T,
value v ->
has_type pc Gamma HT v T ->
has_type pc' Gamma HT v T.
Proof. intros. generalize dependent pc'. induction H1.
Case("tvar").
             inversion H0.
Case("tcon").
             intros. apply t_con.
Case("tunit").
             intros. apply t_unit.
Case("tloc").
             intros. apply t_loc. apply H1.
Case("tabs").
             intros. apply t_abs. apply H1.
Case("tprot").
             inversion H0.
Case("tapp").
             inversion H0.
Case("tref").
             inversion H0.
Case("tderef").
             inversion H0.
Case("tassign").
             inversion H0.
Case("sub").
             intros. apply t_sub with (pc:=pc'0)(T:=T). apply IHhas_type. apply H0.
             apply sub_refl. apply H3.
Qed. 
Theorem substitution_preserves_typing: forall pc Gamma HT x v2 T1 T2 e,
value v2 ->
has_type pc empty_context HT v2 T1 ->
has_type pc (Cupdate Gamma x (Some T1)) HT e T2 ->
has_type pc Gamma HT ([x := v2]e) T2.
Proof. intros. generalize dependent pc. generalize dependent HT. 
generalize dependent Gamma. generalize dependent x.
generalize dependent v2. generalize dependent T1. generalize dependent
T2. induction e.
Case ("tvar").
intros. apply inversion_tvar in H2. inversion H2. inversion H3. 
remember (beq_id x i) as BB.
destruct BB. apply beq_id_eq in HeqBB. rewrite->HeqBB in H4.
rewrite->Cupdate_eq in H4. inversion H4. subst. simpl. rewrite<-beq_id_refl.
apply s_p_t_1. apply t_sub with (pc:=pc)(T:=x0). apply H1. apply sub_refl. apply H5.
symmetry in HeqBB. simpl. rewrite->HeqBB. destruct i. apply t_sub with (pc:=pc)(T:=x0).
 apply t_var. apply Cupdate_neq with (T:=Some T1)(St:=Gamma)in HeqBB.
rewrite->HeqBB in H4. apply H4. apply sub_refl. apply H5.
Case ("tprot").
intros. simpl. apply inversion_tprot in H2. inversion H2. inversion H3.
inversion H4. inversion H5. inversion H7.  apply t_sub with (pc:=pc)(T:=joinTs x0 s). apply t_prot with (T:=x0) .  apply IHe with (T1:=T1).
apply H0. apply value_pc with (pc:=pc). apply H0. apply H1.
subst. apply t_sub with (pc:=x2)(T:=x1). apply H8. apply H9. apply H9. reflexivity. apply sub_refl. apply H6. 
Case ("tcon").
intros. simpl. apply inversion_tcon in H2. inversion H2. inversion H3. inversion H4. inversion H5. inversion H7.
inversion H9. subst. destruct T2. destruct r. inversion H11. subst. apply t_sub with (pc:=pc)(T:=an int s). apply t_con.
apply sub_refl. apply subt_int. apply subsum_r_trans with (a:=s)(b:=x2)(c:=s0). apply H10. apply H12. inversion H11.
inversion H11. inversion H11.
Case ("tabs").

intros. simpl. remember (beq_id x i) as BB. destruct BB. apply inversion_tabs in H2. 
inversion H2. inversion H3. inversion H4. inversion H5. inversion H6. inversion H7. 
inversion H8. inversion H9. inversion H11. inversion H13. inversion H15. inversion H17.
inversion H19. inversion H21. destruct T2. destruct r. inversion H23. apply t_sub with (pc:=pc)(T:=an (fn t0 s1 t1) x6).
apply t_sub with (pc:=pc)(T:=an (fn t0 s1 t1) s). apply t_sub with (pc:=pc)(T:=an (fn x0 s1 t1) s). apply t_sub with (pc:=pc)(T:=an (fn t s1 t1) s).
apply t_sub with (pc:=pc)(T:=an (fn t x5 t1) s). apply t_sub with (pc:=pc)(T:=an (fn t x4 t1) s).
apply t_abs.  apply t_sub with (pc:=x4)(T:=x2). apply t_sub with (pc:=x4)(T:=x1). apply beq_id_eq in HeqBB. rewrite->HeqBB in H12.
assert (Cupdate Gamma i (Some t) = Cupdate (Cupdate Gamma i (Some T1)) i (Some t)).
apply functional_extensionality. intros. remember (beq_id i x7) as CC. destruct CC.
apply beq_id_eq in HeqCC. rewrite->HeqCC. rewrite->Cupdate_eq.
rewrite->Cupdate_eq. reflexivity. symmetry in HeqCC. inversion HeqCC. inversion HeqCC.
apply Cupdate_neq with (T:= Some t)(St:=Gamma ) in HeqCC. rewrite->HeqCC. 
apply Cupdate_neq with (T:= Some t)(St:=Cupdate Gamma i (Some T1)) in H25.
rewrite->H25. apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in H26. rewrite->H26.
reflexivity. rewrite->H24. apply H12. apply sub_refl. apply H20. apply sub_refl. inversion H23. apply H35.
apply sub_refl. apply subt_fn. apply sub_refl. apply H14. apply subtyping_refl. apply subtyping_refl.
apply sub_refl. apply subt_fn. apply sub_refl. inversion H23. apply H33. apply subtyping_refl. apply subtyping_refl.
apply sub_refl. apply subt_fn. apply sub_refl. apply sub_refl. apply H18. apply subtyping_refl. apply sub_refl.
apply subt_fn. apply sub_refl. apply sub_refl. inversion H23. apply H34. apply subtyping_refl. apply sub_refl.
apply subt_fn. apply H22. apply sub_refl. apply subtyping_refl. apply subtyping_refl. apply sub_refl. apply subt_fn.
inversion H23. apply H29. apply sub_refl. apply subtyping_refl. apply subtyping_refl. inversion H23. inversion H23.


apply inversion_tabs in H2. inversion H2. inversion H3. inversion H4. inversion H5.
inversion H6. inversion H7. inversion H8. inversion H9. inversion H11. inversion H13. inversion H15.
inversion H17. inversion H19. inversion H21. destruct T2. destruct r. inversion H23.
apply t_sub with (pc:=pc)(T:=an (fn t0 s1 t1) x6). apply t_sub with (pc:=pc)(T:=an (fn t0 s1 t1) s).
apply t_sub with (pc:=pc)(T:=an (fn x0 s1 t1) s). apply t_sub with (pc:=pc)(T:=an (fn t s1 t1) s). 
apply t_abs. apply IHe with (T1:=T1). apply H0. apply value_pc with (pc:=pc). apply H0. apply H1.
apply t_sub with (pc:=s1)(T:=x2). apply t_sub with (pc:=s1)(T:=x1). apply t_sub with (pc:=x5)(T:=x1).
apply t_sub with (pc:=x4)(T:=x1). 


assert (Cupdate (Cupdate Gamma x (Some T1)) i (Some t) = Cupdate (Cupdate Gamma i (Some t)) x (Some T1)).
apply functional_extensionality. intros. remember (beq_id x x7) as AA.
remember (beq_id i x7) as BB. destruct AA. destruct BB. apply beq_id_eq in HeqAA.
apply beq_id_eq in HeqBB0. rewrite->HeqAA in HeqBB. rewrite->HeqBB0 in HeqBB.
rewrite<-beq_id_refl in HeqBB. inversion HeqBB. apply beq_id_eq in HeqAA. rewrite->HeqAA.
rewrite->Cupdate_eq. rewrite->HeqAA in HeqBB. symmetry in HeqBB. apply Cupdate_permute with (T1:=Some T1)(T2:=Some t)(X3:=x7)(f:=Gamma) in HeqBB.
rewrite->HeqBB. rewrite->Cupdate_eq. reflexivity.  destruct BB. apply beq_id_eq in HeqBB0. rewrite->HeqBB0. rewrite->Cupdate_eq.
symmetry in HeqAA. apply Cupdate_permute with (T1:=Some T1)(T2:=Some t)(X3:=x7)(f:=Gamma) in HeqAA.
rewrite<-HeqAA. rewrite->Cupdate_eq. reflexivity. symmetry in HeqBB0. inversion HeqBB0.
apply Cupdate_neq with (T:=Some t)(St:=Cupdate Gamma x (Some T1))in HeqBB0.
rewrite->HeqBB0. symmetry in HeqAA. inversion HeqAA.
 apply Cupdate_neq with (T:=Some T1)(St:=Gamma) in HeqAA.
rewrite->HeqAA. apply Cupdate_neq with (T:=Some T1)(St:=Cupdate Gamma i (Some t)) in H26.
rewrite->H26. apply Cupdate_neq with (T:=Some t)(St:=Gamma) in H25. rewrite->H25. reflexivity.
rewrite<-H24. apply H12.
apply H14. apply subtyping_refl. inversion H23. inversion H33. apply sub_refl. apply sub_LH.
apply subtyping_refl. apply sub_refl. apply H20. apply sub_refl. inversion H23. apply H35.
apply sub_refl. apply subt_fn. apply sub_refl. apply sub_refl.
apply H18. apply subtyping_refl. apply sub_refl. apply subt_fn. apply sub_refl. apply sub_refl.
inversion H23. apply H34. apply subtyping_refl. apply sub_refl. apply subt_fn. apply H22. apply sub_refl.
apply subtyping_refl. apply subtyping_refl. apply sub_refl. apply subt_fn. inversion H23. apply H29. apply sub_refl.
apply subtyping_refl. apply subtyping_refl. inversion H23. inversion H23. 
Case ("tapp").
intros. simpl. apply inversion_tapp in H2. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6.
inversion H7. inversion H8. inversion H9. inversion H10. inversion H11. inversion H12. inversion H14. inversion H16.
inversion H18. 
apply t_sub with (pc:=pc)(T:=joinTs x5 x2).
 apply t_app with (T1:=x4)(T2:=x5)(b:=x2). 
apply IHe1 with (T1:=T1). apply H0. apply H1. apply t_sub with (pc:=x7)(T:= an (fn x4 (joins pc x2) x5) x2). 
apply t_sub with (pc:=x7)(T:=an (fn x3 (joins pc x2) x5) x2). apply t_sub with (pc:=x7)(T:=an (fn x0(joins pc x2)x5)x2).
apply t_sub with (pc:=x7)(T:=an (fn x0 x8 x5) x2). apply t_sub with (pc:=x7)(T:=an (fn x0 x8 x1) x2).
apply H15. apply sub_refl. apply subt_fn. apply sub_refl. apply sub_refl. apply subtyping_refl. inversion H17. apply H32.
apply sub_refl. apply subt_fn. apply sub_refl. assert (subsum_r (joins pc x2) x8). rewrite->H13. destruct pc. destruct x7.
simpl. apply sub_refl. simpl. destruct x2. apply sub_LH. apply sub_refl. destruct x7. inversion H20. inversion H22. inversion H23.
simpl. apply sub_refl. apply H21. apply subtyping_refl. apply subtyping_refl. apply sub_refl. apply subt_fn. apply sub_refl. apply sub_refl.
inversion H17. apply H31. apply subtyping_refl. apply sub_refl. apply subt_fn. apply sub_refl. apply sub_refl. apply H20. apply subtyping_refl.
apply H20. apply subtyping_refl. 
apply IHe2 with (T1:=T1). apply H0. apply H1. apply t_sub with (pc:=x7)(T:=x4). apply H19. inversion H20. apply H22.
apply subtyping_refl. reflexivity. apply sub_refl. assert (joinTs x5 x2 <: T2). apply subtyping_trans with (x:=joinTs x5 x6)(y:=joinTs x5 x6).
apply subtyping_refl. destruct x2. destruct x6. apply subtyping_refl. destruct x5. simpl. destruct r. apply subt_int. destruct s. apply sub_LH.
apply sub_refl. apply subt_fn. destruct s. apply sub_LH. apply sub_refl. apply sub_refl. apply subtyping_refl. apply subtyping_refl. apply subt_unit.
destruct s. apply sub_LH. apply sub_refl. apply subt_ref. destruct s. apply sub_LH. apply sub_refl. destruct x6. inversion H17. inversion H26. apply subtyping_refl.
apply H20. apply H21.
Case ("tunit").
intros. simpl. apply inversion_tunit in H2. inversion H2. inversion H3. inversion H4. inversion H5. inversion H7.
inversion H9. subst. destruct T2. destruct r. inversion H11. inversion H11. apply t_sub with (pc:=pc)(T:=an unit x2).
apply t_sub with (pc:=pc)(T:=an unit s). apply t_unit. apply sub_refl. apply subt_unit. apply H9. apply sub_refl. apply H11. inversion H11.
Case ("tref").
intros. simpl. apply inversion_tref in H2. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6.
inversion H7. inversion H9. inversion H11. destruct T2. destruct r. inversion H12. inversion H12. inversion H12. apply t_sub with (pc:=pc)(T:=an (ref t0) x4).
apply t_sub with (pc:=pc)(T:=an (ref t0) s).  inversion H12. subst. apply t_ref. apply IHe with (T1:=T1).
apply H0. apply H1. apply t_sub with (pc:=x0)(T:=t0). apply t_sub with (pc:=x0)(T:=x3).
apply t_sub with (pc:=x0)(T:=x2). apply H13. apply sub_refl. apply H13. apply sub_refl. apply H13. apply H13. apply subtyping_refl. assert (x2<:t0).
apply subtyping_trans with (x:=x3)(y:=x3). apply subtyping_refl. apply H13. apply H13. assert (subsum_r (labelT x2)(labelT t0)).
destruct x2. destruct t0. destruct r. destruct r0. simpl. inversion H14. apply H18. inversion H14. inversion H14. inversion H14. destruct r0. inversion H14.
simpl. inversion H14. apply H21. inversion H14. inversion H14. destruct r0. inversion H14. inversion H14. simpl. inversion H14. apply H18. inversion H14.
destruct r0. inversion H14. inversion H14. inversion H14. simpl. inversion H14. apply H17.
apply subsum_r_trans with (a:=pc)(b:=labelT x2)(c:=labelT t0). apply H13. apply H16. apply sub_refl. apply subt_ref. apply H10. apply sub_refl. inversion H12.
apply subt_ref. apply H15.
Case ("tderef").
intros. simpl. apply inversion_tderef in H2. inversion H2. inversion H3. inversion H4. inversion H5.
apply t_sub with (pc:=pc)(T:=joinTs x1 x3).
 apply t_deref with (T:=x1)(b:=x3). apply IHe with (T1:=T1).
apply H0. apply H1. apply t_sub with (pc:=x0)(T:=an (ref x1) x3). apply t_sub with (pc:=x0)(T:=an (ref x1) x2).
apply H6. apply sub_refl. apply subt_ref. apply H6. apply H6. apply subtyping_refl. reflexivity. apply sub_refl.
apply H6.
Case ("tloc").
intros. simpl. apply inversion_tloc in H2. inversion H2. inversion H3. inversion H4. inversion H5. inversion H7.
inversion H9. inversion H11. subst. apply t_sub with (pc:=pc)(T:=an (ref t) x2). apply t_sub with (pc:=pc)(T:=an (ref t) s).
apply t_loc. apply H5. apply sub_refl. apply subt_ref. apply H7. apply sub_refl. apply H7.
Case ("tassign").
intros. simpl. apply inversion_tassign in H2. inversion H2. inversion H3. inversion H4. inversion H5. apply t_sub with (pc:=pc)(T:=an unit (labelT x1)).
apply t_assign with (b:=x3)(T:=x1).  reflexivity. apply subsum_r_trans with (a:=joins pc x3)(b:=joins x0 x3)(c:=labelT x1). destruct pc. destruct x0.
simpl. apply sub_refl. simpl. destruct x3. apply sub_LH. apply sub_refl. destruct x0. inversion H6. inversion H8. inversion H10. inversion H12. inversion H14.
inversion H15. simpl. apply sub_refl. apply H6. apply IHe1 with (T1:=T1). apply H0. apply H1. apply t_sub with (pc:=x0)(T:=an (ref x1) x3). apply H6.
apply H6. apply subtyping_refl. apply IHe2 with (T1:=T1). apply H0. apply H1. apply t_sub with (pc:=x0)(T:=x2). apply H6. apply H6. apply H6. apply sub_refl.
apply H6.
Qed.

(*heap well typed*)
(**
Note: the following two definitions help us to establish relation between the 
      heap,[hp],and the heap typing,[HT] such that each cell in the heap typing
      indicates the right type of each value stored in heap.
*)
(*heap_well_typed*)
Definition heap_well_typed (HT:heap_Ty) (hp:heap) :=
  length HT = length hp /\
  (forall pc l, l < length hp -> 
     has_type pc empty_context HT (efst(heap_lookup l hp)) (extract (heap_Tlookup l HT))).
(*Some instances of consistent heap typing [HT] w.r.t. some heap [hp]*)
Example test_heap_well_typed_1:
heap_well_typed (an int L :: an unit H :: an (fn (an int L) H (an int L)) L :: an (ref (an int L)) H :: nil)
                ((tcon 0 L,an int L) :: (tunit H,an unit H) :: (tabs (Id 0)(an int L)(tcon 0 L) L,an (fn (an int L) H (an int L)) L) :: (tloc (an int L) 0 H,an (ref (an int L)) H) :: nil).
Proof. split. simpl. reflexivity. intros. simpl in H0. inversion H0. simpl. apply t_loc. reflexivity. inversion H2.
simpl. apply t_abs. apply t_con. inversion H4. simpl. apply t_unit. inversion H6. simpl.
apply t_con. inversion H8. Qed.
Example test_heap_well_typed_2:
~heap_well_typed (an int L :: an unit H :: an (ref (an int L)) L :: nil)
               ((tcon 1 L,an int L) :: (tunit H,an unit H) :: nil).
Proof. intros contra. inversion contra. inversion H0. Qed.
Example test_heap_well_typed_3:
~heap_well_typed (an int L :: nil)
                 ((tcon 0 H,an int H) :: nil).
Proof. intros contra. inversion contra. specialize (H1 H 0). simpl in H1.
assert (0 < 1). apply le_n. apply H1 in H2. apply inversion_tcon in H2.
inversion H2. inversion H3. inversion H4. inversion H5. inversion H7.
inversion H9. subst. destruct x1. inversion H10. inversion H11. inversion H12.
Qed.
(*heap_extends*)
(**
As our heap grows in the process of evaluation, its corresponding heap typing 
also expands. We need to take this into consideration.
*)
Inductive extends : heap_Ty -> heap_Ty -> Prop :=
  | extends_nil : forall HT', 
      extends HT' nil
  | extends_cons : forall x HT' HT, 
      extends HT' HT -> 
      extends (x::HT') (x::HT).
(*some example*)
Example test_extends_1:
extends (an int L :: an int H :: an unit H :: an (ref (an unit H)) L :: nil)
        (an int L :: an int H :: an unit H :: nil).
Proof. apply extends_cons. apply extends_cons. apply extends_cons. apply extends_nil.
Qed.

(*lemmas about extended contexts*)
Lemma zero_n:forall n,
0<=n.
Proof. intros. induction n. apply le_n. apply le_S.
apply IHn. Qed.

Lemma n_iff_Sn_left: forall n m,
n <= m -> S n <= S m.
Proof. 
intros. induction H0. apply le_n. apply le_S. apply IHle.
Qed.
Lemma n_iff_Sn_right : forall n m,
S n <= S m -> n <= m.
Proof. intros. generalize dependent n. induction m.
intros. destruct n. apply le_n. inversion H0. inversion H2.
intros. inversion H0. apply le_n. apply le_S. apply IHm in H2.
apply H2. Qed.
Theorem n_iff_Sn : forall n m,
  n <= m <-> S n <= S m.
Proof. 
intros. split.
Case ("->"). apply n_iff_Sn_left.
Case ("<-"). apply n_iff_Sn_right.
Qed.

(**
Lemma Sn_m_n:forall n m,
S n <= m ->
n <= m.
Proof. intros n. induction n.
intros. apply zero_n.
intros. destruct m. inversion H0. apply n_iff_Sn_right in H0.
apply n_iff_Sn_left. apply IHn. apply H0. Qed.
*)


Lemma extends_lookup_last:forall hp p,
heap_lookup (length hp)(snoc hp p) = Some p.
Proof. intros hp. induction hp. 
Case ("nil"). intros. simpl. reflexivity.
Case ("hd::t"). intros. simpl. apply IHhp.
Qed.

Lemma extends_Tlookup_last:forall HT T,
heap_Tlookup (length HT)(snoc HT T) = Some T.
Proof. intros HT. induction HT. 
Case ("nil"). intros. simpl. reflexivity.
Case ("hd::t"). intros. simpl. apply IHHT.
Qed.

Lemma extends_lookup:forall l hp p,
  l < length hp ->
  heap_lookup l hp = heap_lookup l (snoc hp p).
Proof.
intros. generalize dependent hp. generalize dependent p. induction l.
intros. destruct hp. simpl in H0. inversion H0. simpl. reflexivity.
intros. destruct hp. simpl in H0. inversion H0. simpl in H0. unfold lt in H0.
apply n_iff_Sn_right in H0. simpl. apply IHl. unfold lt. apply H0. Qed.
Lemma extends_Tlookup:forall l HT HT',
  l < length HT ->
  extends HT' HT ->
  heap_Tlookup l HT' = heap_Tlookup l HT.
Proof.
intros. generalize dependent l. induction H1. 
Case ("extends_nil"). intros. destruct l. simpl in H0. inversion H0. simpl in H0.
                     inversion H0. 
Case ("extends_cons"). intros. destruct l. reflexivity. apply IHextends. simpl in H0.
                       unfold lt in H0. unfold lt. apply n_iff_Sn in H0.
                       apply H0.
Qed.

Lemma length_extends:forall l HT HT',
     l < length HT ->
     extends HT' HT ->
     l < length HT'.
Proof.
intros. generalize dependent l. induction H1.
intros. destruct l. unfold lt in H0. inversion H0. inversion H0.
intros. destruct l. admit. unfold lt. simpl. apply n_iff_Sn_left.
apply IHextends. simpl in H0. apply n_iff_Sn_right in H0. apply H0.
Qed.
   
Lemma extends_snoc: forall HT T,
  extends (snoc HT T) HT.
Proof.
intros. generalize dependent T. induction HT.
intros. simpl. apply extends_nil.
intros. simpl. apply extends_cons. specialize (IHHT T). apply IHHT.
Qed.

Lemma extends_refl: forall HT,
  extends HT HT.
Proof.
intros. induction HT. apply extends_nil. apply extends_cons.
apply IHHT. Qed.

Lemma extends_trans:forall HT HT' HT'',
extends HT' HT ->
extends HT'' HT' ->
extends HT'' HT.
Proof. intros. generalize dependent HT''. induction H0.
Case ("extends_nil"). intros. apply extends_nil.
Case ("extends_cons"). intros. destruct HT''. inversion H1. inversion H1. 
                      apply extends_cons. apply IHextends. apply H3.
Qed.

Lemma change_HT':forall HT n T,
heap_Tlookup n HT = Some T ->
n < length HT.
Proof. intros. generalize dependent HT. generalize dependent T.
induction n. intros. destruct HT. simpl in H0. inversion H0. simpl.
apply n_iff_Sn_left. apply zero_n. 
intros. destruct HT. simpl in H0. inversion H0. simpl in H0. apply IHn in H0.
unfold lt in H0. unfold lt. simpl. apply n_iff_Sn_left. apply H0. Qed.


Lemma change_HT: forall HT HT' pc Gamma t T,
extends HT' HT ->
has_type pc Gamma HT t T ->
has_type pc Gamma HT' t T.
Proof. intros. generalize dependent HT'. induction H1.
Case ("t_var"). intros. apply t_var. apply H0.
Case ("t_con"). intros. apply t_con.
Case ("t_unit"). intros. apply t_unit.
Case ("t_loc"). intros. apply t_loc. rewrite<-H0. apply extends_Tlookup.
                apply change_HT' with (T:=T). apply H0. apply H1.
Case ("t_tabs"). intros. apply t_abs. apply IHhas_type. apply H0.
Case ("t_prot"). intros. subst. apply t_prot with (T:=T). apply IHhas_type. apply H2.
                 reflexivity.
Case ("t_app"). intros. subst. apply t_app with (T1:=T1)(T2:=T2)(b:=b). apply IHhas_type1. apply H1.
                apply IHhas_type2. apply H1. reflexivity.
Case ("t_ref"). intros. apply t_ref. apply IHhas_type. apply H2. apply H0.
Case ("t_deref"). intros. subst. apply t_deref with (T:=T)(b:=b). apply IHhas_type. apply H2. reflexivity.
Case ("t_assign"). intros. apply t_assign with (b:=b)(T:=T). apply H0. apply H1. apply IHhas_type1. apply H2.
                  apply IHhas_type2. apply H2. 
Case ("t_sub"). intros. apply IHhas_type in H3. apply t_sub with (pc:=pc)(T:=T). apply H3. apply H0. apply H2.
Qed.
(*#######################end###################*)

(*preservation*)
(*some auxiliary lemmas*)
Lemma joins_b:forall s1 s2 b,
subsum_r s1 s2 ->
subsum_r (joins s1 b)(joins s2 b).
Proof. intros. destruct s1. destruct s2. destruct b.
simpl. apply sub_refl. simpl. apply sub_refl. destruct b. simpl. apply sub_LH.
simpl. apply sub_refl. destruct b. destruct s2. inversion H0. simpl. apply H0.
destruct s2. inversion H0. simpl. apply sub_refl. Qed.
Lemma subsum_joins:forall a b c,
subsum_r a c ->
subsum_r b c ->
subsum_r (joins a b) c.
Proof. intros. destruct a. destruct b. destruct c.
simpl. apply sub_refl. simpl. apply sub_LH. destruct c. inversion H1. simpl. apply sub_refl.
destruct c. inversion H0. destruct b. simpl. apply sub_refl. simpl. apply sub_refl.
Qed.
Lemma joinTs_b:forall r s b,
joinTs (an r s) b = an r (joins s b).
Proof. intros. destruct s. destruct b. simpl. reflexivity.
simpl. reflexivity. simpl. destruct b. reflexivity. reflexivity.
Qed.
Lemma join_tcon_b:forall n s b,
joinvs (tcon n s) b = tcon n (joins s b).
Proof. intros. destruct b. destruct s. simpl. reflexivity. simpl. reflexivity.
destruct s. simpl. reflexivity. simpl. reflexivity. 
Qed. 
Lemma join_tabs_b:forall n T e s b,
joinvs (tabs (Id n) T e s) b = tabs (Id n) T e (joins s b).
Proof. destruct s. destruct b. simpl. reflexivity. simpl. reflexivity.
intros. destruct b. simpl. reflexivity. simpl. reflexivity. Qed.
Lemma join_tunit_b:forall s b,
joinvs (tunit s) b = tunit (joins s b).
Proof. intros. destruct s. destruct b. simpl. reflexivity. simpl. reflexivity. 
       destruct b.  simpl. reflexivity. simpl. reflexivity. Qed. 
Lemma join_tloc_b:forall T n s b,
joinvs (tloc T n s) b = tloc T n (joins s b).
Proof. intros. destruct s. destruct b. simpl. reflexivity. simpl. reflexivity.
destruct b. simpl. reflexivity. simpl. reflexivity. Qed.
Lemma joinTs_subtyping_s:forall T b' b,
subsum_r b' b ->
joinTs T b' <: joinTs T b.
Proof. intros. inversion H0. apply subtyping_refl. destruct T. simpl.
destruct r. destruct s. apply subt_int. apply sub_LH. apply subtyping_refl.
destruct s. apply subt_fn. apply sub_LH. apply sub_refl. apply subtyping_refl.
apply subtyping_refl. apply subtyping_refl. apply subt_unit. destruct s. apply sub_LH.
apply sub_refl. apply subt_ref. destruct s. apply sub_LH. apply sub_refl.
Qed.
Lemma joinTs_subtyping_T:forall T1 T2 b,
T1 <: T2 ->
joinTs T1 b <: joinTs T2 b.
Proof. intros. destruct T1. destruct T2. rewrite->joinTs_b. rewrite->joinTs_b. 
inversion H0. subst. apply subt_int. apply joins_b. apply H2. subst. apply subt_fn.
apply joins_b. apply H5. apply H6. apply H7. apply H8. subst. apply subt_unit.
apply joins_b. apply H2. subst. apply subt_ref. apply joins_b. apply H2. Qed.
Lemma joins_subtyping_1:forall s1 s1' s2,
subsum_r s1 s1' ->
subsum_r (joins s1 s2)(joins s1' s2).
Proof. intros. destruct s1. destruct s1'. destruct s2. simpl. apply sub_refl.
simpl. apply sub_refl. simpl. destruct s2. apply sub_LH. apply sub_refl. destruct s1'.
inversion H0. simpl. apply sub_refl. Qed.
Lemma joins_subtyping_2:forall s1 s2 s2',
subsum_r s2 s2' ->
subsum_r (joins s1 s2)(joins s1 s2').
Proof. intros. destruct s1. destruct s2. destruct s2'. simpl. apply sub_refl. simpl. apply sub_LH.
destruct s2'. inversion H0. simpl. apply sub_refl. simpl. apply sub_refl. Qed.
Lemma value_b:forall t b,
value t ->
value (joinvs t b).
Proof. intros. inversion H0. rewrite->join_tcon_b. apply v_c. rewrite->join_tabs_b. apply v_f. 
rewrite->join_tunit_b. apply v_u. rewrite->join_tloc_b. apply v_l. Qed.
Lemma has_type_value_joinvs:forall pc b Gamma HT t T,
value t ->
subsum_r pc b ->
subsum_r b (labelT T) ->
has_type pc Gamma HT t T ->
has_type pc Gamma HT (joinvs t b) T.
Proof. intros.  inversion H0.
Case ("tcon").
      intros. rewrite->join_tcon_b. subst. apply inversion_tcon in H3. inversion H3. inversion H4.
      inversion H5. inversion H6. inversion H8. inversion H10. subst. destruct T. destruct r.
      simpl in H2. apply t_sub with (pc:=pc)(T:=an int (joins b0 b)). apply t_con. apply sub_refl.
      apply subt_int. apply subsum_joins. apply subsum_r_trans with (a:=b0)(b:=x1)(c:=s). apply H6.
      inversion H12. apply H13. apply H2. inversion H12.
      inversion H12. inversion H12.
Case ("tabs").
      intros. rewrite->join_tabs_b. subst. apply inversion_tabs in H3. inversion H3. inversion H4. inversion H5.
      inversion H6. inversion H7. inversion H8. inversion H9. inversion H10. inversion H12. inversion H14.
      inversion H16. inversion H18. inversion H20. inversion H22. destruct T. destruct r. inversion H24.
      simpl in H2. apply t_sub with (pc:=pc)(T:=an (fn t s0 t0) (joins b0 b)). apply t_sub with (pc:=pc)(T:=an (fn x s0 t0)(joins b0 b)).
      apply t_sub with (pc:=pc)(T:=an (fn T0 s0 t0) (joins b0 b)). apply t_abs. apply t_sub with (pc:=x4)(T:=x1). apply t_sub with (pc:=x3)(T:=x0).
      apply H13. apply H15. apply H21. inversion H24. apply H34. inversion H24. apply H36. apply sub_refl. apply subt_fn. apply sub_refl. apply sub_refl.
      apply H19. apply subtyping_refl. apply sub_refl. apply subt_fn. apply sub_refl. apply sub_refl. inversion H24. apply H35. apply subtyping_refl. apply sub_refl.
      apply subt_fn. apply subsum_joins. apply subsum_r_trans with (a:=b0)(b:=x5)(c:=s). apply H23. inversion H24. apply H30. apply H2. apply sub_refl. apply subtyping_refl.
      apply subtyping_refl. inversion H24. inversion H24.
Case ("tunit").
      intros. rewrite->join_tunit_b. subst. apply inversion_tunit in H3. inversion H3. inversion H4. inversion H5. inversion H6. inversion H8. inversion H10.
      subst. destruct T. destruct r. inversion H12. inversion H12. apply t_sub with (pc:=pc)(T:=an unit (joins b0 b)).
      apply t_unit. apply sub_refl. apply subt_unit. apply subsum_joins. apply subsum_r_trans with (a:=b0)(b:=x1)(c:=s). apply H6. inversion H12. apply H13.
     simpl in H2. apply H2. inversion H12.
Case ("tloc").
      intros. rewrite->join_tloc_b. subst. apply inversion_tloc in H3. inversion H3. inversion H4. inversion H5. inversion H6. inversion H8. inversion H10. inversion H12. subst.
      destruct T. destruct r. inversion H14. inversion H14. inversion H14. inversion H14. subst. simpl in H2. apply t_sub with (pc:=pc)(T:=an (ref t) (joins b0 b)). apply t_loc.
      apply H6. apply sub_refl. apply subt_ref. apply subsum_joins. apply subsum_r_trans with (a:=b0)(b:=x1)(c:=s). apply H8. inversion H14. apply H11. apply H2. 
Qed. 
Lemma has_type_joinvs_sub:forall pc b b' Gamma HT t T,
value t ->
subsum_r b b' ->
has_type pc Gamma HT (joinvs t b') T ->
has_type pc Gamma HT (joinvs t b) T.
Proof. intros. inversion H0.
Case ("tcon").
      rewrite->join_tcon_b. subst. rewrite->join_tcon_b in H2. apply inversion_tcon in H2. inversion H2. inversion H3. inversion H4. inversion H5. inversion H7.
      inversion H9. subst. destruct T. destruct r. apply t_sub with (pc:=pc)(T:=an int x1). apply t_sub with (pc:=pc)(T:=an int (joins b0 b')).
      apply t_sub with (pc:=pc)(T:=an int (joins b0 b)). apply t_con. apply sub_refl. apply subt_int. apply joins_subtyping_2. apply H1. apply sub_refl. apply subt_int.
      apply H5. apply sub_refl. apply H11. inversion H11. inversion H11. inversion H11.
Case ("tabs").
      rewrite->join_tabs_b. subst. rewrite->join_tabs_b in H2. apply inversion_tabs in H2. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6. inversion H7.
      inversion H8. inversion H9. inversion H11. inversion H13. inversion H15. inversion H17. inversion H19. inversion H21. destruct T. destruct r. inversion H23. apply t_sub with (pc:=pc)(T:=an (fn t s0 t0) x5).
      apply t_sub with (pc:=pc)(T:=an (fn t s0 t0) (joins b0 b')). apply t_sub with (pc:=pc)(T:=an (fn t s0 t0)(joins b0 b)). apply t_sub with (pc:=pc)(T:=an (fn x s0 t0)(joins b0 b)).
      apply t_sub with (pc:=pc)(T:=an (fn T0 s0 t0)(joins b0 b)). apply t_abs. apply t_sub with (pc:=x4)(T:=x1). apply t_sub with (pc:=x3)(T:=x0). apply H12. apply H14. apply H20. inversion H23. apply H33.
      inversion H23. apply H35. apply sub_refl. apply subt_fn. apply sub_refl. apply sub_refl. apply H18. apply subtyping_refl. apply sub_refl. apply subt_fn. apply sub_refl. apply sub_refl. inversion H23. inversion H34. subst.
      apply H34. subst. apply H34. subst. apply H34. subst. apply H34. apply subtyping_refl. apply sub_refl. apply subt_fn. apply joins_subtyping_2. apply H1. apply sub_refl. apply subtyping_refl. apply subtyping_refl. apply sub_refl.
      apply subt_fn. apply H22. apply sub_refl. apply subtyping_refl. apply subtyping_refl. apply sub_refl. apply subt_fn. inversion H23. apply H29. apply sub_refl. apply subtyping_refl. apply subtyping_refl. inversion H23. inversion H23.
Case ("tunit").
      rewrite->join_tunit_b. subst. rewrite->join_tunit_b in H2. apply inversion_tunit in H2. inversion H2. inversion H3. inversion H4. inversion H5. inversion H7. inversion H9. subst. destruct T. destruct r. inversion H11. inversion H11.
      apply t_sub with (pc:=pc)(T:=an unit x1). apply t_sub with (pc:=pc)(T:=an unit (joins b0 b')). apply t_sub with (pc:=pc)(T:=an unit (joins b0 b)). apply t_unit. apply sub_refl. apply subt_unit. apply joins_subtyping_2. apply H1. apply sub_refl.
      apply subt_unit. apply H5. apply sub_refl. apply H11. inversion H11.
Case ("tloc").
      rewrite->join_tloc_b. subst. rewrite->join_tloc_b in H2. apply inversion_tloc in H2. inversion H2. inversion H3. inversion H4. inversion H5. inversion H7. inversion H9. inversion H11. subst. destruct T. destruct r. inversion H13. inversion H13. inversion H13.
      inversion H13. subst. apply t_sub with (pc:=pc)(T:=an (ref t) x1). apply t_sub with (pc:=pc)(T:=an (ref t) (joins b0 b')).
      apply t_sub with (pc:=pc)(T:=an (ref t) (joins b0 b)). apply t_loc. apply H5. apply sub_refl. apply subt_ref. apply joins_subtyping_2. apply H1. apply sub_refl. apply subt_ref. apply H7. apply sub_refl. apply subt_ref. inversion H13. apply H14.
Qed.
      

Lemma has_type_joinvs_b:forall pc HT t T b,
value t ->
has_type pc empty_context HT t T ->
has_type pc empty_context HT (joinvs t b) (joinTs T b).
Proof.
intros. inversion H0.
Case ("tcon").
     intros. rewrite->join_tcon_b. subst. apply inversion_tcon in H1. inversion H1. inversion H2. inversion H3. inversion H4. inversion H6.
     inversion H8. subst. destruct T. destruct r. rewrite->joinTs_b. apply t_sub with (pc:=pc)(T:=an int (joins b0 b)). apply t_con. apply sub_refl.
     apply subt_int. apply joins_subtyping_1. apply subsum_r_trans with (a:=b0)(b:=x1)(c:=s). apply H9. inversion H10. apply H11.  inversion H10.
     inversion H10. inversion H10.
Case ("tabs").
     intros. rewrite->join_tabs_b. subst. apply inversion_tabs in H1. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6.
     inversion H7. inversion H8. inversion H10. inversion H12. inversion H14. inversion H16. inversion H18. inversion H20. destruct T. destruct r. inversion H22.
     rewrite->joinTs_b. apply t_sub with (pc:=pc)(T:=an (fn t s0 t0) (joins b0 b)). apply t_sub with (pc:=pc)(T:=an (fn x s0 t0) (joins b0 b)).
     apply t_sub with (pc:=pc)(T:=an (fn T0 s0 t0)(joins b0 b)). apply t_abs. apply t_sub with (pc:=x4)(T:=x1). apply t_sub with (pc:=x3)(T:=x0).
     apply H11. inversion H13. apply sub_refl. apply sub_LH. apply H19. inversion H22. apply H32. inversion H22. apply H34. apply sub_refl. apply subt_fn. apply sub_refl.
     apply sub_refl. apply H17. apply subtyping_refl. apply sub_refl. apply subt_fn. apply sub_refl. apply sub_refl. inversion H22. apply H33. apply subtyping_refl. apply sub_refl.
     apply subt_fn. apply joins_subtyping_1. apply subsum_r_trans with (a:=b0)(b:=x5)(c:=s). apply H21. inversion H22. apply H28. apply sub_refl. apply subtyping_refl. apply subtyping_refl.
     inversion H22. inversion H22.
Case ("tunit").
     intros. rewrite->join_tunit_b. subst. apply inversion_tunit in H1. inversion H1. inversion H2. inversion H3. inversion H4. inversion H6. inversion H8. subst. destruct T. destruct r. inversion H10.
     inversion H10. rewrite->joinTs_b. apply t_sub with (pc:=pc)(T:=an unit (joins b0 b)). apply t_unit. apply sub_refl. apply subt_unit. apply joins_subtyping_1. apply subsum_r_trans with (a:=b0)(b:=x1)(c:=s).
     apply H9. inversion H10. apply H11. inversion H10.
Case ("tloc").
     intros. rewrite->join_tloc_b. subst. apply inversion_tloc in H1. inversion H1. inversion H2. inversion H3. inversion H4. inversion H6. inversion H8.
     inversion H10. subst. destruct T. destruct r. inversion H12. inversion H12. inversion H12. rewrite->joinTs_b. inversion H12. subst. apply t_sub with (pc:=pc)(T:=an (ref t)(joins b0 b)).
     apply t_loc. apply H4. apply sub_refl. apply subt_ref. apply joins_subtyping_1. apply subsum_r_trans with (a:=b0)(b:=x1)(c:=s). apply H6. inversion H12. apply H13.
Qed.

Lemma l_lt_hp:forall (T:Type)(l:nat) (hp:list T),
l <= length hp ->
l <> length hp ->
l < length hp.
Proof. intros. unfold not in H1. unfold lt. inversion H0. apply H1 in H2. inversion H2. 
apply n_iff_Sn_left. apply H3. Qed.

(*#####################*)
Theorem preservation:forall pc PC HT t t' T hp hp',
has_type pc empty_context HT t T ->
heap_well_typed HT hp ->
t / hp ==PC=> t' / hp' ->
subsum_r PC pc ->
exists HT',
(extends HT' HT /\
has_type pc empty_context HT' t' T /\
heap_well_typed HT' hp').
Proof.
intros. remember (@empty_context) as context. generalize dependent hp.
generalize dependent hp'. generalize dependent t'. generalize dependent PC.
induction H0. 
Case ("t_var").
     intros. inversion H2.
Case ("t_con").
     intros. inversion H2.
Case ("t_unit").
     intros. inversion H2.
Case ("t_loc").
     intros. inversion H2.
Case ("t_abs"). 
     intros. inversion H2. 
Case ("t_prot").
     intros. inversion H4. subst. apply IHhas_type in H9. inversion H9. exists x.
     split. apply H1. split. apply t_prot with (T:=T). apply H1. reflexivity. apply H1.
     reflexivity. apply joins_subtyping_1. apply H3. apply H2. 
     subst. exists HT. split. apply extends_refl. split. apply value_pc with (pc:=joins pc b).
     apply value_b. apply H9. apply has_type_joinvs_b. apply H9. apply H0. apply H2.
Case ("t_app").
     intros. inversion H2. subst. exists HT. split. apply extends_refl. split. apply inversion_tabs in H0_. inversion H0_. inversion H0. inversion H4. inversion H5. inversion H6. inversion H7. inversion H9.
     inversion H10. inversion H12. inversion H14. inversion H16. inversion H18. inversion H20. inversion H22.
     apply t_sub with (pc:=pc)(T:=joinTs T2 x6). apply t_sub with (pc:=pc)(T:=joinTs T2 b0). apply t_prot with (T:=T2).
     apply t_sub with (pc:=x5)(T:=T2). apply t_sub with (pc:=x4)(T:=T2). apply t_sub with (pc:=x4)(T:=x2). apply t_sub with (pc:=x4)(T:=x1). apply value_pc with (pc':=x4) in H0_0.
     apply t_sub with (pc':=x4)(T':=x0)in H0_0. apply t_sub with (pc':=x4)(T':=T) in H0_0. apply substitution_preserves_typing with (T1:=T). apply H8. apply H0_0. apply H13. apply sub_refl.
     apply H19. apply sub_refl.  inversion H24. apply H35. apply H8. apply sub_refl. apply H21. apply sub_refl.
     inversion H24. apply H36. apply H15. apply subtyping_refl. apply subsum_r_trans with (a:=joins pc b0)(b:=joins pc b)(c:=x5). apply subsum_r_trans with (a:=joins pc b0)(b:=joins pc x6)(c:=joins pc b).
     apply joins_subtyping_2. apply H23. apply joins_subtyping_2. inversion H24. apply H30. inversion H24. apply H34. apply subtyping_refl. reflexivity. apply sub_refl. apply joinTs_subtyping_s. apply H23. apply sub_refl.
     apply joinTs_subtyping_s.  inversion H24. apply H30. apply H1. subst.
     apply IHhas_type1 in H8. inversion H8. exists x. split. apply H0. split. apply t_app with (T1:=T1)(T2:=T2)(b:=b). apply H0. apply change_HT with (HT:=HT). apply H0. apply H0_0. reflexivity. apply H0. reflexivity. apply H3. apply H1.
     subst. apply IHhas_type2 in H11. inversion H11. exists x. split. apply H0. split. apply t_app with (T1:=T1)(T2:=T2)(b:=b). apply change_HT with (HT:=HT).  apply H0. apply H0_. apply H0. reflexivity. apply H0. reflexivity. apply H3.
     apply H1.
Case ("t_ref").
      intros. inversion H4. subst. exists (snoc HT T). split. apply extends_snoc. split. apply t_loc. inversion H2. rewrite<-H5. rewrite->extends_Tlookup_last. reflexivity. split. rewrite->length_snoc. rewrite->length_snoc.
      inversion H2. rewrite->H5. reflexivity. inversion H2. intros. remember (beq_nat l (length hp)) as CC. destruct CC. apply beq_nat_eq in HeqCC. rewrite->HeqCC. assert (heap_Tlookup (length hp)(snoc HT T) = heap_Tlookup (length HT)(snoc HT T)).
      rewrite<-H5. reflexivity. rewrite->H8. rewrite->extends_Tlookup_last. simpl. rewrite->extends_lookup_last. simpl. apply change_HT with (HT:=HT). apply extends_snoc. apply value_pc with (pc:=pc). apply value_b. apply H10. apply has_type_joinvs_sub with (b':=pc). apply H10. apply H3.
      apply has_type_value_joinvs. apply H10. apply sub_refl. apply H1.
      apply H0. 
      symmetry in HeqCC. apply beq_nat_false in HeqCC. unfold lt in H7. rewrite ->length_snoc in H7. apply n_iff_Sn_right in H7. assert (l < length hp). apply l_lt_hp. apply H7. apply HeqCC. clear H7. clear HeqCC. assert (l <length hp). apply H8. assert (l <length hp).
      apply H8. rewrite<-H5 in H8. apply extends_lookup with (p:=(joinvs t PC,T))in H7. rewrite<-H7. apply extends_Tlookup with (HT':=snoc HT T) in H8.  rewrite->H8.
      apply change_HT with (HT:=HT). apply extends_snoc. apply H6. apply H9. apply extends_snoc. subst.
      apply IHhas_type in H10. inversion H10. exists x. split. apply H5. split. apply t_ref. apply H5. apply H1. apply H5. reflexivity. apply H3. apply H2.
Case ("t_deref").
      intros. inversion H4. subst. exists HT. split. apply extends_refl. split. apply inversion_tloc in H0. inversion H0. inversion H1. inversion H5. inversion H6. inversion H8. inversion H11. inversion H13.
      subst. apply t_sub with (pc:=pc)(T:=joinTs T x1). apply t_sub with (pc:=pc)(T:=joinTs T b0). apply t_prot with (T:=T). inversion H15. subst. inversion H2. apply H16 with (pc:=joins pc b0)in H9. rewrite->H7 in H9. simpl in H9.
      apply H9. reflexivity. apply sub_refl. apply joinTs_subtyping_s. apply H8. apply sub_refl. apply joinTs_subtyping_s. inversion H15. apply H12. apply H2. subst.
      apply IHhas_type in H8. inversion H8. exists x. split. apply H1. split. apply t_deref with (T:=T)(b:=b). apply H1. reflexivity. apply H1. reflexivity. apply H3. apply H2.
Case ("t_assign").
      intros. inversion H4. subst. exists HT. split. apply extends_refl. split. apply t_sub with (pc:=pc)(T:=an unit (joins pc b)).
      apply t_sub with (pc:=pc)(T:=an unit pc). apply t_sub with (pc:=pc)(T:=an unit PC). apply t_unit. apply sub_refl. apply subt_unit. apply H3. apply sub_refl. apply subt_unit. destruct pc. destruct b. simpl. apply sub_refl. simpl. apply sub_LH. destruct b. simpl.
      apply sub_refl. simpl. apply sub_refl. apply sub_refl. apply subt_unit. apply H1. inversion H2. split. rewrite->H0. rewrite->length_replace. reflexivity. intros. remember (beq_nat l n) as CC. destruct CC.
       apply beq_nat_eq in HeqCC. subst. apply lookup_replace_eq with (t:=(joinvs t2 (joins PC b0),joinTs T0 (joins PC b0)))in H10. rewrite->H10. simpl. apply inversion_tloc in H0_. inversion H0_. inversion H7. inversion H8.
      inversion H9. inversion H14. inversion H16. inversion H18. subst. rewrite->H12. simpl. inversion H20. subst. apply value_pc with (pc:=pc). apply value_b. apply H11. apply has_type_joinvs_sub with (b':=joins pc b0). apply H11. apply joins_subtyping_1. apply H3. apply has_type_value_joinvs. apply H11. destruct pc. destruct b0. simpl. apply sub_refl.
      simpl. apply sub_LH. simpl. apply sub_refl. apply subsum_r_trans with (a:=joins pc b0)(b:=joins pc b)(c:=labelT T). apply joins_subtyping_2. apply subsum_r_trans with (a:=b0)(b:=x1)(c:=b). apply H14. inversion H20. apply H21. apply H1. apply H0_0.
      symmetry in HeqCC. apply beq_nat_false in HeqCC. rewrite->length_replace in H6. apply lookup_replace_neq with (t:=(joinvs t2 (joins PC b0),joinTs T0 (joins PC b0)))(st:=hp) in HeqCC. rewrite->HeqCC. apply H5. apply H6. subst.
      apply IHhas_type1 in H9. inversion H9. exists x. split. apply H0. split. apply t_assign with (b:=b)(T:=T). reflexivity. apply H1.  apply H0. apply change_HT with (HT:=HT). apply H0. apply H0_0. apply H0. reflexivity. apply H3. apply H2. subst.
      apply IHhas_type2 in H12. inversion H12. exists x. split. apply H0. split. apply t_assign with (b:=b)(T:=T). reflexivity. apply H1. apply change_HT with (HT:=HT). apply H0. apply H0_. apply H0. apply H0. reflexivity. apply H3. apply H2.
Case ("t_sub"). 
      intros. apply IHhas_type in H5. inversion H5. exists x. split. apply H6. split. apply t_sub with (pc:=pc)(T:=T). apply H6. apply H1. apply H2. apply H6. apply Heqcontext. apply subsum_r_trans with (a:=PC)(b:=pc')(c:=pc). apply H3. apply H1. apply H4.
Qed.


Theorem type_uniqueness:forall x z PC pc HT T,
        has_type pc empty_context HT (fst x) T ->
        heap_well_typed HT (snd x) ->
        subsum_r PC pc ->
        Multistep x PC z ->
        (exists HT',
        extends HT' HT /\
        heap_well_typed HT' (snd z) /\
        has_type pc empty_context HT'(fst z) T).
        
Proof. intros. generalize dependent pc. generalize dependent HT. induction H3.
Case ("multi_refl"). intros. exists HT. admit.
Case ("multi_step"). intros. apply preservation with (PC:=b)(t':=fst y)(hp:=snd x)(hp':=snd y)in H2.
                     inversion H2. inversion H5. inversion H7. apply IHMulti with (pc:=pc)in H9. 
                     inversion H9. exists x1. split. apply extends_trans with (HT':=x0). apply H6.
                     apply H10. apply H10. apply H8. apply H4. apply H1. destruct x. destruct y. apply H0.
                     apply H4.                     
Qed. 


(*###########end##########*)
(*#########progress#########*)
(*one useful lemma*)
Lemma change_PC:forall s hp PC PC',
(exists e',step (s,hp) PC e') ->
subsum_r PC' PC ->
exists e',step (s,hp) PC' e'.
Proof.
intros s. induction s.
Case ("tvar"). intros. inversion H0. inversion H2.
Case ("tprot"). intros. inversion H0. inversion H2. subst. assert (exists e',step (s0,hp) (joins PC s) e'). exists (t',hp').
                apply H8. apply IHs with (PC':=joins PC' s)in H3. inversion H3. destruct x. exists (tprot s t,h). apply st_prot.
                apply H4. apply joins_subtyping_1. apply H1. subst. exists (joinvs s0 s,hp). apply st_protv. apply H8.
Case ("tcon"). intros. inversion H0. inversion H2.
Case ("tabs"). intros. inversion H0. inversion H2.
Case ("tapp"). intros. inversion H0. inversion H2.
               subst. exists (tprot b ([x0:=s2]e),hp). apply st_appabs. apply H8.
               subst. assert (exists e',step (s1,hp) PC e'). exists (t1',hp'). 
               apply H8. apply IHs1 with (PC':=PC')in H3. inversion H3. destruct x. 
               exists (tapp t s2,h). apply st_app1. apply H4. apply H1. subst.
               assert (exists e',step (s2,hp) PC e'). exists (t2',hp'). apply H9.
               apply IHs2 with (PC':=PC')in H3. inversion H3. destruct x. exists (tapp s1 t,h).
               apply st_app2. apply H8. apply H4. apply H1.
Case ("tunit"). intros. inversion H0. inversion H2.
Case ("tref"). intros. inversion H0. inversion H2. subst. exists (tloc t (length hp) s0,snoc hp (joinvs s PC',t)).
               apply st_refv with (v':=joinvs s PC'). apply H9. reflexivity. reflexivity. subst.
               assert (exists e',step (s,hp) PC e'). exists (t',hp'). apply H9. apply IHs with (PC':=PC')in H3. inversion H3.
               destruct x. exists (tref t t0 s0,h). apply st_ref. apply H4. apply H1.
Case ("tderef"). intros. inversion H0. inversion H2. subst. exists (tprot b (efst (heap_lookup n hp)),hp).
               apply st_derefloc. apply H5. reflexivity. subst. assert (exists e',step (s,hp) PC e').  exists (t',hp').
               apply H7. apply IHs with (PC':=PC') in H3. inversion H3. destruct x. exists (tderef t,h). apply st_deref. apply H4. apply H1.
Case ("tloc"). intros. inversion H0. inversion H2.
Case ("tassign"). intros. inversion H0. inversion H2. subst. exists (tunit PC',heap_replace n (joinvs s2 (joins PC' b), joinTs T (joins PC' b)) hp).
               apply st_assign with (v':=joinvs s2 (joins PC' b))(T':=joinTs T (joins PC' b)). apply H6. apply H7. apply subsum_r_trans with (a:=joins PC' b)(b:=joins PC b)(c:=label (efst (heap_lookup n hp))).
               apply joins_subtyping_1. apply H1. apply H8. reflexivity. reflexivity. reflexivity. subst.
               assert (exists e',step (s1,hp) PC e'). exists (t1',hp'). apply H8. apply IHs1 with (PC':=PC')in H3. inversion H3.
               destruct x. exists (tassign t s2,h ). apply st_assign1. apply H4. apply H1. subst. assert (exists e',step (s2,hp) PC e'). exists (t2',hp').
               apply H9. apply IHs2 with (PC':=PC')in H3. inversion H3. destruct x. exists (tassign s1 t,h). apply st_assign2. apply H8. apply H4. apply H1.
Qed.

(**
Note: the condition "the programme counter must be guarded by the security context",
      thus [subsum_r PC pc], unlike in [preservation] is not necessary in [progress].
      For in the subcase [t_sub] of [progress], a reduction under high security context
      can alway imply a related reduction (not the same) under a lower security context
      ,instead of the other way round. See [change_PC].
*)

Theorem progress_1: forall t T pc HT hp,
has_type pc empty_context HT t T ->
heap_well_typed HT hp ->
value t \/ (exists p, step (t,hp) pc p).
Proof. intros. remember (@empty_context) as context. generalize dependent hp.
       induction H0.
Case ("t_var").
      intros. subst. inversion H0.
Case ("t_con").
      intros. subst. left. apply v_c.
Case ("t_unit").
      intros. subst. left. apply v_u.
Case ("t_loc").
      intros. subst. left. apply v_l.
Case ("t_abs").
      intros. subst. left. destruct x. apply v_f.
Case ("t_prot").
      intros. subst. right. apply IHhas_type in H2. inversion H2. inversion H1.
      exists ((joinvs (tcon n b0) b),hp). apply st_protv. apply v_c.
      exists (joinvs (tabs (Id n) T0 e b0) b,hp). apply st_protv. apply v_f.
      exists (joinvs (tunit b0) b,hp). apply st_protv. apply v_u.
      exists (joinvs (tloc T0 n b0) b,hp). apply st_protv. apply v_l.
      inversion H1. destruct x. exists (tprot b t0,h). apply st_prot. apply H3. reflexivity.
Case ("t_app").
      intros. subst. right. assert (heap_well_typed HT hp). apply H1.
      assert (heap_well_typed HT hp). apply H1.
      apply IHhas_type1 in H1.
      apply IHhas_type2 in H0. inversion H1. inversion H0. inversion H3. subst. apply inversion_tcon in H0_.
      inversion H0_. inversion H5. inversion H6. inversion H7. inversion H9. inversion H11. subst. inversion H13.
      subst. exists (tprot b0 ([(Id n ) :=  t2]e),hp). apply st_appabs. apply H4. subst. apply inversion_tunit in H0_.
      inversion H0_. inversion H5. inversion H6. inversion H7. inversion H9. inversion H11. subst. inversion H13.
      subst. apply inversion_tloc in H0_. inversion H0_. inversion H5. inversion H6. inversion H7. inversion H9. inversion H11.
      inversion H13. subst. inversion H15. inversion H4. destruct x. exists (tapp t1 t,h). apply st_app2. apply H3. apply H5.
      inversion H3. destruct x. exists (tapp t t2,h). apply st_app1. apply H4. reflexivity. reflexivity.
Case ("t_ref").
      intros. subst. right. apply IHhas_type in H2. inversion H2. exists (tloc T (length hp) b,snoc hp (joinvs t pc,T)).
      apply st_refv with (v':=joinvs t pc). apply H3. reflexivity. reflexivity. inversion H3. destruct x. exists (tref T t0 b,h). apply st_ref.  
      apply H4. reflexivity.
Case ("t_deref").
      intros. subst. right. assert (heap_well_typed HT hp). apply H2. apply IHhas_type in H2. inversion H2. inversion H3. subst. apply inversion_tcon in H0. inversion H0. inversion H4. inversion H5.
      inversion H6. inversion H8. inversion H10. subst. inversion H12. subst. apply inversion_tabs in H0. inversion H0. inversion H4. inversion H5. inversion H6.
      inversion H7. inversion H8. inversion H9. inversion H10. inversion H12. inversion H14. inversion H16. inversion H18. inversion H20. inversion H22. inversion H24.
      subst. apply inversion_tunit in H0. inversion H0. inversion H4. inversion H5. inversion H6. inversion H8. inversion H10. subst. inversion H12. subst. apply inversion_tloc in H0.
      inversion H0. inversion H4. inversion H5. inversion H6. apply change_HT' in H7. exists (tprot b0 (efst (heap_lookup n hp)),hp). apply st_derefloc. inversion H1. rewrite<-H9. apply H7.
      reflexivity. inversion H3. destruct x. exists (tderef t0,h). apply st_deref. apply H4. reflexivity.
Case ("t_assign").
      intros. subst. right. assert (heap_well_typed HT hp). apply H2. assert (heap_well_typed HT hp). apply H2. 
      apply IHhas_type1 in H0. apply IHhas_type2 in H3. inversion H0. inversion H3. inversion H4. subst. apply inversion_tcon in H0_. inversion H0_. inversion H6. inversion H7.
      inversion H8. inversion H10. inversion H12. subst. inversion H14. subst. apply inversion_tabs in H0_. inversion H0_. inversion H6. inversion H7. inversion H8. inversion H9.
      inversion H10. inversion H11. inversion H12. inversion H14. inversion H16. inversion H18. inversion H20. inversion H22. inversion H24. inversion H26. subst. apply inversion_tunit in H0_. inversion H0_.
      inversion H6. inversion H7. inversion H8. inversion H10. inversion H12. subst. inversion H14. subst. apply inversion_tloc in H0_. inversion H0_. inversion H6. inversion H7. inversion H8. apply change_HT' in H9.
      exists (tunit pc,heap_replace n (joinvs t2 (joins pc b0),joinTs T0 (joins pc b0)) hp). apply st_assign with (v':=joinvs t2 (joins pc b0))(T':=joinTs T0 (joins pc b0)). inversion H2. rewrite<-H11. apply H9. apply H5.
      inversion H2. rewrite->H11 in H9. apply H12 with (pc:=pc)in H9. (*we are stuck here*) 
      Admitted.

                
Theorem progress': forall t T pc PC HT hp,
has_type pc empty_context HT t T ->
heap_well_typed HT hp ->
subsum_r PC pc ->
value t \/ (exists p, step (t,hp) PC p).
Proof. intros. remember (@empty_context) as context. induction H0.
admit. admit. admit. admit. admit. admit. admit. admit. admit. admit.
assert (subsum_r PC pc). apply subsum_r_trans with (a:=PC)(b:=pc')(c:=pc). apply H2. apply H3.
apply IHhas_type in H5. apply H5. apply Heqcontext. apply H1. Admitted.

(**
Note [progress] acctually does not hold for the current system,
consider the following well typed term and its reduction sequence,
*)
Example non_progress:
has_type L empty_context [] 
        (tassign (tref (an int H)(tcon 0 L) H)(tcon 1 H))
        (an unit H).
Proof. apply t_assign with (b:=H)(T:=an int H). reflexivity. simpl. apply sub_refl.
       apply t_ref. apply t_sub with (pc:=L)(T:=an int L). apply t_con. apply sub_refl.
       apply subt_int. apply sub_LH. simpl. apply sub_LH. apply t_con. Qed.

(*suppose we start with an empty heap, and the security context is low*)
Example well_typed_stuck_term:
(tassign (tref (an int H)(tcon 0 L) H)(tcon 1 H)) / emp_hp ==L=>* (tassign (tloc (an int H) 0 H)(tcon 1 H)) / ((tcon 0 L,an int H) :: emp_hp).
Proof. apply Multi_step with (y:=(tassign (tloc (an int H) 0 H)(tcon 1 H),((tcon 0 L,an int H) :: emp_hp))).
apply st_assign1. apply st_refv with (v':=tcon 0 L). apply v_c. reflexivity. reflexivity.
apply Multi_refl. Qed.

(**
Note now we get a stuck-term which is the evaluation result of a well-typed a term
it is sufficient to illustrate that [progress] does not hold for the system.
*)
Example imporatant_stuck_term:
stuck_term (tassign (tloc (an int H) 0 H)(tcon 1 H))
           ((tcon 0 L,an int H) :: emp_hp)
           L.
Proof. split. intros contra. inversion contra. inversion H0. subst. compute in H10.
       inversion H10. subst. inversion H6. subst. inversion H7.
       intros contra. inversion contra. Qed.
(**
Note that acctually if we suppose the following heap typing,
HT = [an int H], the above stuck term is acctually well-typed!!
*) 
Example well_typed_stuck_term':
has_type L empty_context [an int H]
         (tassign (tloc (an int H) 0 H)(tcon 1 H))
         (an unit H).
Proof.  apply t_assign with (b:=H)(T:=an int H). reflexivity. simpl. apply sub_refl. apply t_loc.
        reflexivity. apply t_con. Qed.


     
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












