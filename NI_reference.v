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
(*end typing context*)
(*heap_Ty*) 
Definition heap_Ty := list Ty.

Fixpoint heap_Tlookup (n:nat)(ht:heap_Ty): option Ty :=
  match ht , n with
  | nil , _ => None (*default return*)
  | h::t , 0 => Some h
  | h::t , S n' =>heap_Tlookup n' t
  end.
(*end heap_Ty*)
(*functional extensionality*)
Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.
(*end*)
Module SecLang.
(*syntax*)
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
| tloc    : Ty -> option nat -> Sec -> tm(*[Ty] as the "access type"*)
(**
Note that regarding the type of the referred location in [tloc] we use
[option nat] instead of [nat] 
*)
| tassign : tm -> tm -> tm.

(*values*)
(*###values###*)
Inductive value : tm -> Prop :=
| v_c : forall b n,
        value (tcon n b)
| v_f : forall n T e b,
        value (tabs (Id n) T e b)
| v_u : forall b,
        value (tunit b)
| v_l : forall n T b,
        value (tloc T (Some n) b).

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
(*###end heap###*)

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
  | tloc T N b => tloc T N b
(*assignments*)
  | tassign t1 t2 => tassign (subst x s t1)(subst x s t2)
  end.
Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(*###reduction relation###*)
(*###"join" functions###*)
Definition joins (b1:Sec) (b2:Sec): Sec :=
 match b1 with
 | L => b2
 | H => H
 end.


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
 | tloc T N b , L => Some (tloc T N b)
 | tloc T N b , H => Some (tloc T N H)
 | tassign t1 t2 , _ => None
 end.
(*############*)
Definition extract (t:option Ty) : Ty :=
match t with
| Some T => T
| None => an unit L (*default type*)
end.

(*############*)
Definition extractT (t:option tm) : tm :=
match t with
| Some e => e
| None => tvar (Id 100)
end.
Definition joinvs (T:tm) (b:Sec): tm :=
extractT (joinVS T b).

Definition joinTs (T:Ty)(b:Sec) : Ty :=
 match T , b with
 | an rt s , L => an rt s
 | an rt s , H => an rt H
 end.

(*"get-label" functions*)
Fixpoint Label (t:tm) : option Sec :=
 match t with
 | tvar x => None
 | tprot H t => Some H
 | tprot L t => Label t
 | tcon n b => Some b
 | tabs x T e b => Some b
 | tapp t1 t2 => None
 | tunit b => Some b
 | tref T e b => None
 | tderef e => None
 | tloc T N b => Some b
 | tassign t1 t2 => None
 end.
Definition eLabel (s:option Sec) : Sec :=
 match s with
 | Some s' => s'
 | None => L
 end.
Definition label (t:tm) : Sec :=
eLabel (Label t).

Definition labelT (T:Ty) : Sec:=
match T with
 | an rt b => b
end.
(**
Now,we impose upon the language a relation which restricts the 
form of expressions we are interested in when doing reduction. 
Specifically we want to exclude from our consideration expression 
which contains pointers whose referred location is out of range,
e.g. tapp t1 (tloc T n L) where n is equal or greater than the length
     of the current heap
*)
(*well formed expressions*)
Inductive well_formed : tm -> nat -> Prop :=
  | wf_tvar:forall (x:id)(hp:nat),
         well_formed (tvar x) hp 
  | wf_tcon:forall (b:Sec)(n:nat)(hp:nat),
         well_formed (tcon n b) hp
  | wf_tunit:forall (b:Sec)(hp:nat),
         well_formed (tunit b) hp
  | wf_tloc:forall (T:Ty)(n:nat)(b:Sec)(hp:nat),
         n < hp ->
         well_formed (tloc T (Some n) b) hp
  | wf_tprot:forall b t (hp:nat),
         well_formed t hp ->
         well_formed (tprot b t) hp
  | wf_tabs:forall x T e b hp,
         well_formed e hp ->
         well_formed (tabs x T e b) hp
  | wf_tapp:forall t1 t2 hp,
         well_formed t1 hp ->
         well_formed t2 hp ->
         well_formed (tapp t1 t2) hp
  | wf_tref:forall (T:Ty) (e:tm) (b:Sec) (hp:nat),
         well_formed e hp ->
         well_formed (tref T e b) hp
  | wf_tderef:forall e hp,
         well_formed e hp ->
         well_formed (tderef e) hp
  | wf_tassign:forall t1 t2 hp,
         well_formed t1 hp ->
         well_formed t2 hp ->
         well_formed (tassign t1 t2) hp.
(*some examples of well-formed expressions*)
Example well_formed_1:
well_formed (tvar (Id 0)) 0.
Proof. apply wf_tvar. 
Qed.
Example well_formed_2:
well_formed (tprot H (tloc (an int L) (Some 0) L)) 1.
Proof. apply wf_tprot. apply wf_tloc. apply le_n.
Qed.
Example well_formed_3:forall hp,
well_formed (tcon 0 H) hp.
Proof. intros. apply wf_tcon.
Qed.
Example well_formed_4:forall hp,
well_formed (tunit L) hp.
Proof. intros. apply wf_tunit.
Qed.
Example well_formed_5:
well_formed (tabs (Id 0)(an int L)(tderef (tloc (an int L) (Some 0) H)) L) 1.
Proof. apply wf_tabs. apply wf_tderef. apply wf_tloc. apply le_n.
Qed.
Example well_formed_6:forall hp,
well_formed (tref (an int L) (tcon 0 L) H) hp.
Proof. intros. apply wf_tref. apply wf_tcon.
Qed.
Example well_formed_7:
well_formed (tassign (tloc (an int L) (Some 0) L)(tcon 1 L)) 1.
Proof. apply wf_tassign. apply wf_tloc. apply le_n. apply wf_tcon.
Qed.
(*some examples of ill-formed expression*)
Example ill_formed_1:
~well_formed (tloc (an int L) (Some 0) L) 0.
Proof. intros contra. inversion contra. inversion H4.
Qed.
Example ill_formed_2:
~well_formed (tapp (tref (an int L) (tcon 1 L) L)(tloc (an int L) (Some 1) L)) 1.
Proof. intros contra. inversion contra. inversion H4. inversion H9. inversion H11.
Qed.
Example ill_formed_3:
~well_formed (tassign (tloc (an int L) (Some 1) L)(tapp (tabs (Id 0)(an int L)(tvar (Id 0)) L)(tcon 1 L))) 1.
Proof. intros contra. inversion contra. inversion H2. inversion H9. inversion H11.
Qed.
(*some lemmas regarding [well_formed]*)
Lemma well_formed_extend:forall t hp,
well_formed t hp ->
well_formed t (S hp).
Proof. intros t. induction t.
Case ("tvar"). intros. apply wf_tvar.
Case ("tprot"). intros. inversion H0. apply wf_tprot. apply IHt. apply H4.
Case ("tcon"). intros. apply wf_tcon. 
Case ("tabs"). intros. inversion H0. apply wf_tabs. apply IHt. apply H6.
Case ("tapp"). intros. inversion H0. apply wf_tapp. apply IHt1. apply H3.
               apply IHt2. apply H5.
Case ("tunit"). intros. apply wf_tunit.
Case ("tref"). intros. apply wf_tref. apply IHt. inversion H0. apply H5.
Case ("tderef"). intros. apply wf_tderef. apply IHt. inversion H0. apply H2.
Case ("tloc"). intros. destruct o. apply wf_tloc. inversion H0. 
              apply le_S. apply H5. inversion H0.
Case ("tassign"). intros. apply wf_tassign. apply IHt1. inversion H0. apply H3. apply IHt2. inversion H0.
                apply H5.
Qed.
(**
Also,we restrict the heap at the beginning of our reduction such that
each and every element within the heap is well-foremed according to
the heap itself,
*)
(*heap well_formed*)
Inductive heap_well_formed : heap -> nat -> Prop :=
| nil_hwf:forall n, 
           heap_well_formed nil n
| one_hwf:forall t0 t T n,
          heap_well_formed t n ->
          well_formed t0 n ->
          heap_well_formed ((t0,T) :: t) n.
(*some lemmas regarding [heap_well_formed]*)
Lemma heap_well_formed_extend'': forall n m,
n <= m -> S n <= S m.
Proof. 
intros. induction H0. apply le_n. apply le_S. apply IHle.
Qed.
Lemma heap_well_formed_extend':forall (T:Type)(l:nat) (hp:list T),
l <= length hp ->
l <> length hp ->
l < length hp.
Proof. intros. unfold not in H1. unfold lt. inversion H0. apply H1 in H2. inversion H2. 
apply heap_well_formed_extend'' in H3. apply H3. Qed.
Lemma heap_well_formed_extend:forall hp t T n,
heap_well_formed hp n->
well_formed t n ->
heap_well_formed (snoc hp (t,T)) (S n).
Proof. intros hp. induction hp.
Case ("nil"). intros. simpl. apply one_hwf. apply nil_hwf. apply well_formed_extend. apply H1.
Case ("h::t"). intros. simpl. destruct a. apply one_hwf. apply IHhp. inversion H0. apply H6.
              apply H1. inversion H0. subst. apply well_formed_extend. apply H7.
Qed.
Lemma heap_well_formed_shrink:forall hp a n,
  heap_well_formed (a :: hp) n ->
  heap_well_formed hp n.
Proof. intros. inversion H0. apply H3.
Qed. 
Lemma lt_same_F' : forall n m,
S n <= S m -> n <= m.
Proof. intros. generalize dependent n. induction m.
intros. destruct n. apply le_n. inversion H0. inversion H2.
intros. inversion H0. apply le_n. apply le_S. apply IHm in H2.
apply H2. Qed.
Lemma lt_same_F:forall n,
n < n -> False.
Proof. intros. induction n. inversion H0. unfold lt in H0. unfold lt in IHn.
apply lt_same_F' in H0. apply IHn in H0. inversion H0. Qed.
Lemma heap_well_formed_replace:forall hp t T n n',
well_formed t n ->
heap_well_formed hp n ->
n' < length hp ->
heap_well_formed (heap_replace n' (t,T) hp) n.
Proof. intros hp. induction hp.
Case ("nil"). intros. simpl in H2. destruct n'. apply lt_same_F in H2. inversion H2. inversion H2.
Case ("h::t"). intros. destruct n'. simpl. apply one_hwf. inversion H1. apply H5. apply H0. simpl.
              destruct a. apply one_hwf. apply IHhp. apply H0. inversion H1. apply H7. simpl in H2.
              apply lt_same_F' in H2. apply H2. inversion H1. apply H8.
Qed.
(**
Note that the reason for having this additional restriction upon the heap is
that when the heap is extended we have to make sure that the projection of the 
elements on the heap before the allocation is the same as that of those on  the 
heap after the allocation,
project_conf'_hp (project_hp heap)(project_hp heap)
=
project_conf'_hp (project_hp heap)(project_hp (snoc heap v)),
where [v] stands for a low value
*)
(**
Note regarding the reduction relation, there are few modifications made,
a. [st_refv] 
   1. the cell being written is guarded by both the security context and 
      the label of the allocation
   2. moreover,we have to guarantee that the label of the cell being written
      subsums that of its type 
b. [st_assign]
   1. the label of the resulting unit is the joint of PC and the label of the pointer
   2. the label of the cell written to the heap has to be guarded by that of its type
   3. the label of the cell on the heap being over-written equals the joint of the label
      of the referred type and that of the replacing value
Note [a.2] and [b.2] together guarantee that for every pair in heap, the label of 
the first element subsums that of the second one. This extra condition imposed upon
our typing system allows us to reintroduce "the condition" without sacrificing [progress]  






c. [st_ref]
   1. the security_context where the sub-term is reduced has to be guarded by
      the label of the pointer for when we have a high pointer we have to make
      sure that we also write high value to the heap so that our projection function
      can successfully handle this case in the sense that the resulting reduction
      is allowed in [LowLang]


Note that there are two types of over-writing we care for in the system,
1. a low cell being over-written by a low value
   tassign (tloc (an int L) 0 L)(tcon 1 L) / ((tcon 0 L,an int L) :: nil)
   ==L=>
   tunit L / ((tcon 1 L,an int L) :: nil)
2. a high cell being over-written by a high value
   tassign (tloc (an int L) 0 L)(tcon 1 H) / ((tcon 0 H,an int L) :: nil)
   ==L=>
   tunit L / ((tcon 1 H,an int L) :: nil) 

##########################################################################
the remaining two cases are left out currently,  
3. a high cell being over-written by a low value
   tassign (tloc (an int L) 0 L)(tcon 1 L) / ((tcon 0 H,an int L) :: nil)
   ==L=>
   tunit L / ((tcon 1 L,an int L) :: nil)
4. a low cell being over-written by a high value
   tassign (tloc (an int L) 0 L)(tcon 1 H) / ((tcon 0 L,an int L) :: nil)
   ==L=>
   tunit L / ((tcon 1 H,an int L) :: nil)
##########################################################################
*)
(**
Now in addition to the above analysis,we also require that the expression we
are concerned with before reduction is well-formed. This is already adequate for
us to exclude from consideration all expression involved in the reduction process
which are ill-formed for the heap can only be extended in the process.
*)
(*##########*)
Reserved Notation "t1 '/' hp '==' PC '=>' t2 '/' hp'"
  (at level 40, hp at level 39, t2 at level 39, PC at level 39).

Inductive step : tm * heap -> Sec -> tm * heap -> Prop :=
  | st_prot: forall b PC t t' hp hp',
         heap_well_formed hp (length hp)-> (*additional requirement*)
         well_formed t (length hp) -> (*additional requirement*)
         t / hp == (joins PC b) => t' / hp' ->
        tprot b t / hp == PC => tprot b t' / hp'
 
  | st_protv: forall b v hp PC,
         heap_well_formed hp (length hp) -> (*additional requirement*)
         well_formed v (length hp) -> (*additional requirement*)
         value v ->
         tprot b v / hp == PC => joinvs v b / hp
  | st_appabs: forall x T e b PC hp v,
         heap_well_formed hp (length hp) -> (*additional requirement*)
         well_formed v (length hp) -> (*additional requirement*)
         well_formed e (length hp) -> (*additional requirement*)
         value v ->
         tapp (tabs x T e b) v / hp == PC => tprot b ([x := v]e) / hp
  | st_app1: forall t1 t1' t2  PC hp hp',
         heap_well_formed hp (length hp) -> (*additional requirement*)
         well_formed t1 (length hp) -> (*additional requirement*)
         well_formed t2 (length hp) -> (*additional requirement*)
         t1 / hp == PC => t1' / hp' ->
         tapp t1 t2 / hp == PC => tapp t1' t2 / hp'
  | st_app2: forall v1 t2 t2' PC hp hp',
         heap_well_formed hp (length hp) -> (*additional requirement*)
         well_formed v1 (length hp) -> (*additional requirement*)
         well_formed t2 (length hp) -> (*additional requirement*)
         value v1 ->
         t2 / hp == PC => t2' / hp' ->
         tapp v1 t2 / hp == PC => tapp v1 t2' / hp'
  | st_refv: forall T v v' b b' b'' b''' PC hp hp',
         heap_well_formed hp (length hp) -> (*additional requirement*)
         well_formed v (length hp) -> (*additional requirement*)
         value v ->
         b' = labelT T ->
         b'' = joins b PC -> (*join PC with label of the pointer*)
         b''' =joins b' b'' ->(*then join with the label of the type of the pointer*)
         v' = joinvs v b''' ->
         hp' = snoc hp (v',T) ->
         tref T v b / hp == PC => tloc T (Some (length hp)) b / hp'
  | st_ref: forall T t t' b PC hp hp',
          heap_well_formed hp (length hp) -> (*additional requirement*)
          well_formed t (length hp) -> (*additional requirement*)
          t / hp == (joins PC b) => t' / hp' ->
          tref T t b / hp == PC => tref T t' b / hp'
  | st_derefloc: forall T n b PC hp t,
          heap_well_formed hp (length hp) -> (*additional requirement*)
          n < length hp ->
          t = efst (heap_lookup n hp) ->
          tderef (tloc T (Some n) b) / hp == PC => tprot b t / hp
  | st_deref: forall t t' hp hp' PC,
          heap_well_formed hp (length hp) -> (*additional requirement*)
          well_formed t (length hp) -> (*additional requirement*)
          t / hp == PC => t' / hp' ->
          tderef t / hp == PC => tderef t' / hp'
  | st_assign: forall v v' T T' b b' b'' b''' l n PC hp hp',
          heap_well_formed hp (length hp) -> (*additional requirement*)
          well_formed v (length hp) -> (*additional requirement*)
          n < length hp -> (* heap_lookup n hp = some e'*)
          value v ->
          l = label v ->
          b' = labelT T ->
          b'' = joins PC b ->
          joins l b' = label (efst (heap_lookup n hp)) ->
          subsum_r b'' (label (efst (heap_lookup n hp))) ->
          b'''= joins b' b'' ->
          T' = joinTs T b'' ->
          v' = joinvs v b''' ->
          hp' = heap_replace n (v',T') hp ->
          tassign (tloc T (Some n) b) v / hp == PC => tunit b'' / hp'
  | st_assign1: forall t1 t1' t2 PC hp hp',
          heap_well_formed hp (length hp) -> (*additional requirement*)
          well_formed t1 (length hp) -> (*additional requirement*)
          well_formed t2 (length hp) -> (*additional requirement*)
          t1 / hp == PC => t1' / hp' ->
          tassign t1 t2 / hp == PC => tassign t1' t2 / hp'
  | st_assign2: forall v1 t2 t2' PC hp hp',
          heap_well_formed hp (length hp) -> (*additional requirement*)
          well_formed v1 (length hp) -> (*additional requirement*)
          well_formed t2 (length hp) -> (*additional requirement*)
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

Definition stuck_term (s:tm) (hp:heap) (PC:Sec) : Prop :=
 (~exists e', step (s,hp) PC e') /\ (~value s).

(*Some reduction examples*)
Example test_step_1:
tref (an int L)(tcon 0 L) L / emp_hp
==L=>
tloc (an int L) (Some 0) L / ((tcon 0 L,an int L) :: emp_hp).
Proof. apply st_refv with (v':=tcon 0 L)(b':=L)(b'':=L)(b''':=L).
apply nil_hwf.   
apply wf_tcon. apply v_c. reflexivity.
reflexivity. reflexivity. reflexivity. reflexivity. Qed.
Example test_step_2:forall hp,
heap_well_formed hp (length hp) ->
tref (an int L)(tcon 0 L) H / hp
==L=>
tloc (an int L) (Some (length hp)) H / snoc hp (tcon 0 H,an int L).
Proof. intros. apply st_refv with (v':=tcon 0 H)(b':=L)(b'':=H)(b''':=H).
apply H0.
apply wf_tcon.
apply v_c. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity.
Qed.
Example test_step_3:forall hp,
heap_well_formed hp (length hp) ->
tref (an int H)(tcon 0 L) L / hp
==L=>
tloc (an int H) (Some (length hp)) L / snoc hp (tcon 0 H,an int H).
Proof. intros. apply st_refv with (v':=tcon 0 H)(b':=H)(b'':=L)(b''':=H).
apply H0.
apply wf_tcon.
apply v_c. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity.
Qed.
Example test_step_4:forall hp,
heap_well_formed hp (length hp) ->
tref (an int L)(tcon 0 H) L / hp
==L=>
tloc (an int L) (Some (length hp)) L / snoc hp (tcon 0 H,an int L).
Proof. intros. apply st_refv with (v':=tcon 0 H)(b':=L)(b'':=L)(b''':=L).
apply H0.
apply wf_tcon.
apply v_c. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity.
Qed.
Lemma test_step_5'': forall n m,
n <= m -> S n <= S m.
Proof. 
intros. induction H0. apply le_n. apply le_S. apply IHle.
Qed.
Lemma test_step_5':forall (T:Type)(l:nat) (hp:list T),
l <= length hp ->
l <> length hp ->
l < length hp.
Proof. intros. unfold not in H1. unfold lt. inversion H0. apply H1 in H2. inversion H2. 
apply test_step_5'' in H3. apply H3. Qed.
Example test_step_5:forall hp,
heap_well_formed hp (length hp) ->
tprot H (tref (an int H)(tcon 0 L) L) / hp
==L=>*
tloc (an int H) (Some (length hp)) H / snoc hp (tcon 0 H,an int H).
Proof. intros. apply Multi_step with (y:=(tprot H (tloc (an int H)(Some (length hp)) L),(snoc hp (tcon 0 H,an int H)))).
apply st_prot.
apply H0.
 apply wf_tref. apply wf_tcon.
 apply st_refv with (v':=tcon 0 H)(b':=H)(b'':=H)(b''':=H).
apply H0.
 apply wf_tcon.
apply v_c. reflexivity. reflexivity. reflexivity.
reflexivity.  reflexivity.
apply Multi_step with (y:=(tloc (an int H) (Some (length hp)) H,(snoc hp (tcon 0 H,an int H)))). apply st_protv.
rewrite->length_snoc.
apply heap_well_formed_extend. apply H0. apply wf_tcon.
apply wf_tloc. rewrite->length_snoc. apply le_n. apply v_l.
apply Multi_refl. Qed.
Example test_step_6:forall hp,
heap_well_formed hp (length hp) ->
tprot L (tref (an int H)(tcon 0 L)L) / hp
==L=>*
tloc (an int H) (Some (length hp)) L / snoc hp (tcon 0 H,an int H).
Proof. intros. apply Multi_step with (y:=(tprot L (tloc (an int H) (Some (length hp)) L),(snoc hp (tcon 0 H,an int H)))).
apply st_prot. apply H0. apply wf_tref. apply wf_tcon.
apply st_refv with (v':=tcon 0 H)(b':=H)(b'':=L)(b''':=H). apply H0. apply wf_tcon.
apply v_c. reflexivity. reflexivity. reflexivity.
reflexivity. reflexivity.
apply Multi_step with (y:=(tloc (an int H) (Some (length hp)) L,(snoc hp (tcon 0 H,an int H)))). apply st_protv. rewrite->length_snoc.
apply heap_well_formed_extend.
apply H0. apply wf_tcon.
apply wf_tloc. rewrite->length_snoc. apply le_n. 
apply v_l. apply Multi_refl. Qed.
(*a low cell is being over-written by a low value*)
Example test_step_7:
tassign (tloc (an int L) (Some 0) L)(tcon 1 L) / ((tcon 0 L,an int L) :: emp_hp)
==L=>
tunit L / ((tcon 1 L,an int L) :: emp_hp).
Proof. apply st_assign with (v':=tcon 1 L)(T':=an int L)(b':=L)(b''':=L)(l:=L). 
assert (snoc emp_hp (tcon 0 L,an int L)=((tcon 0 L,an int L) :: emp_hp)). reflexivity. rewrite<-H0.
rewrite->length_snoc.
apply heap_well_formed_extend. apply nil_hwf. apply wf_tcon.
apply wf_tcon.
apply le_n. apply v_c. reflexivity. reflexivity.
reflexivity.  reflexivity. apply sub_refl. reflexivity. reflexivity. reflexivity. reflexivity. 
Qed.
(*high cell being over-written by a high value*)
Example test_step_8:
tassign (tloc (an int H) (Some 0) L)(tcon 1 H) / ((tcon 0 H,an int H) :: emp_hp)
==L=>
tunit L / ((tcon 1 H,an int H) :: emp_hp).
Proof. apply st_assign with (v':=tcon 1 H)(T':=an int H)(b':=H)(b''':=H)(l:=H).
assert ((tcon 0 H,an int H) :: emp_hp = snoc emp_hp (tcon 0 H,an int H)). reflexivity.
rewrite->H0. rewrite->length_snoc.  apply heap_well_formed_extend. apply nil_hwf. apply wf_tcon.
apply wf_tcon.
 apply le_n. apply v_c.
reflexivity. reflexivity.  reflexivity. reflexivity. apply sub_LH. reflexivity. reflexivity. reflexivity. reflexivity. 
Qed.
(*high cell being over-written  by a low value*)
Example test_step_9:
stuck_term (tassign (tloc (an int L) (Some 0) L)(tcon 1 L)) ((tcon 0 H,an int L) :: emp_hp) L.
Proof. split. intros contra. inversion contra. inversion H0. subst. 
simpl in H13. inversion H13.
inversion H9. inversion H10. intros contra. inversion contra.
Qed.
(*low cell being over-written by high value
*)
Example test_step_9':
stuck_term (tassign (tloc (an int L) (Some 0) L)(tcon 1 H)) ((tcon 0 L,an int L) :: emp_hp) L.
Proof. split. intros contra. inversion contra. inversion H0. subst.  inversion H13. inversion H9.
inversion H10. intros contra. inversion contra.
Qed.
Example test_step_10:
stuck_term (tassign (tloc (an int L) (Some 0) H)(tcon 1 L)) ((tcon 0 L,an int H) :: emp_hp) L.
Proof. split. intros contra. inversion contra. inversion H0. subst. inversion H14. inversion H9. inversion H10.
intros contra. inversion contra. 
Qed.
Example test_step_11:
stuck_term (tassign (tloc (an int L) (Some 0) L)(tcon 1 L)) ((tcon 0 L,an int L) :: emp_hp) H.
Proof. split. intros contra. inversion contra. inversion H0. subst. simpl in H14. inversion H14. inversion H9.
inversion H10. intros contra. inversion contra. 
Qed.
Example test_step_12:
stuck_term (tassign (tloc (an int L) (Some 0) H)(tcon 1 L))((tcon 0 L,an int L) :: emp_hp) H.
Proof. split. intros contra. inversion contra. inversion H0. subst. simpl in H14. inversion H14. inversion H9. inversion H10.
intros contra. inversion contra. 
Qed.
Example test_step_13:
tref (an (ref (an int L)) L) (tref (an int L)(tcon 0 L) L) H / nil
==L=>
tref (an (ref (an int L)) L) (tloc (an int L) (Some 0) L) H / ((tcon 0 H,an int L) :: nil).
Proof. apply st_ref. apply nil_hwf. apply wf_tref. apply wf_tcon.
apply st_refv with (v':=tcon 0 H)(b':=L)(b'':=H)(b''':=H). apply nil_hwf. apply wf_tcon.
apply v_c. reflexivity. reflexivity. reflexivity. reflexivity.
reflexivity. 
Qed.
(**
Note that it is clear from the above examples that when a cell is being written the label
of the cell subsums that of its type. This is necessary for us to restore the restriction
for security upgrading without sacrificing [progress]
*)
(**
Note that by including extra condition in [st_assign], we can
no longer have the following property,
forall PC PC' t hp,
exists c,t / hp ==PC=> c -> exists c', t / hp ==PC'=> c'.
Consider the following configuration,
tassign (tloc (an int L) 0 L)(tcon 1 L) / ((tcon 0 L,an int L) :: emp_hp)
it is reducible under [L] while it is not under [H]. 
Actually,we can only argue that if a configuration is reducible under [H] then
it is also under [L]. See the following lemma.
*)
Lemma HL_scontext:forall s hp,
(exists e',step (s,hp) H e') ->
exists e',step (s,hp) L e'.
Proof.
intros s. induction s.
Case ("tvar"). intros. inversion H0. inversion H1.
Case ("tprot"). intros. inversion H0. inversion H1. subst. destruct s.
                simpl in H9. assert (exists e',step (s0,hp) H e'). exists (t',hp').
                apply H9. apply IHs in H2. inversion H2. destruct x. exists (tprot L t,h).
                apply st_prot. apply H5. apply H8. simpl. apply H3. simpl in H9. exists (tprot H t',hp').
                apply st_prot. apply H5. apply H8. simpl. apply H9. subst. exists (joinvs s0 s,hp). apply st_protv.
                apply H5. apply H8.
                apply H9.
Case ("tcon"). intros. inversion H0. inversion H1.
Case ("tabs"). intros. inversion H0. inversion H1.
Case ("tapp"). intros. inversion H0. inversion H1.
               subst. exists (tprot b ([x0:=s2]e),hp). apply st_appabs. apply H5. apply H6. apply H9. 
               apply H10. 
               subst. assert (exists e',step (s1,hp) H e'). exists (t1',hp'). 
               apply H10. apply IHs1 in H2. inversion H2. destruct x. 
               exists (tapp t s2,h). apply st_app1. apply H5. apply H6. apply H9. apply H3. 
               subst.
               assert (exists e',step (s2,hp) H e'). exists (t2',hp'). apply H11.
               apply IHs2 in H2. inversion H2. destruct x. exists (tapp s1 t,h).
               apply st_app2. apply H5. apply H6. apply H7. apply H10. apply H3. 
Case ("tunit"). intros. inversion H0. inversion H1.
Case ("tref"). intros. inversion H0. inversion H1. subst.
               exists (tloc t (Some (length hp)) s0,snoc hp (joinvs s (joins (labelT t)(joins s0 L)),t)). apply st_refv with (v':=joinvs s (joins (labelT t)(joins s0 L)))(b':=labelT t)(b'':=joins s0 L)(b''':=joins (labelT t)(joins s0 L)).
               apply H6. 
               apply H7. apply H8. 
               reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. subst. destruct s0. simpl in H10.
               assert (exists e',step (s,hp) H e'). exists (t',hp'). apply H10. apply IHs in H2. inversion H2. 
               destruct x. exists (tref t t0 L,h). apply st_ref. apply H8. apply H9. simpl. apply H3.  simpl in H10. exists (tref t t' H,hp').
               apply st_ref. apply H8. apply H9. simpl. apply H10.  
Case ("tderef"). intros. inversion H0. inversion H1. subst. exists (tprot b (efst (heap_lookup n hp)),hp).
               apply st_derefloc. apply H4. apply H5. reflexivity. subst. assert (exists e',step (s,hp) H e').  exists (t',hp').
               apply H8. apply IHs in H2. inversion H2. destruct x. exists (tderef t,h). apply st_deref. apply H4. apply H5. apply H3.
Case ("tloc"). intros. inversion H0. inversion H1. 
Case ("tassign"). intros. inversion H0. inversion H1. subst. exists (tunit (joins L b),heap_replace n (joinvs s2 (joins (labelT T)(joins L b)), joinTs T (joins L b)) hp).
               apply st_assign with (v':=joinvs s2 (joins (labelT T)(joins L b)))(T':=joinTs T (joins L b))(b':=labelT T)(b''':=joins (labelT T)(joins L b))(l:=label s2). apply H5. apply H6. apply H7. apply H8. reflexivity. reflexivity. reflexivity.
               apply H12. simpl. 
               apply subsum_r_trans with (a:= b)(b:= H)(c:=label (efst (heap_lookup n hp))). destruct b. apply sub_LH. apply sub_refl. simpl in H13. apply H13. reflexivity. reflexivity. reflexivity. reflexivity. 
               assert (exists e',step (s1,hp) H e'). exists (t1',hp'). apply H10. apply IHs1 in H11. inversion H11.
               destruct x0. exists (tassign t s2,h ). apply st_assign1. apply H5. apply H6. apply H9. apply H12. subst. assert (exists e',step (s2,hp) H e'). exists (t2',hp').
               apply H11. apply IHs2 in H2. inversion H2. destruct x. exists (tassign s1 t,h). apply st_assign2. apply H5. apply H6. apply H7. apply H10. apply H3.
Qed. 
(*generalization of the above lemma*)
Lemma prot_scontext:forall s hp PC b, 
(exists e', step (s,hp) (joins PC b) e') ->
exists e',step (s,hp) PC e'.
Proof.
intros. destruct PC. destruct b. simpl in H0. apply H0.
simpl in H0. apply HL_scontext. apply H0. simpl in H0.
apply H0.
Qed.

(*typing rule*)
(*typing relation*)
(**
Note that we make one change above in [st_ref] so that the evaluation of
the subterm in allocation is under the security context guarded by the label
of the allocation,
[st_ref]:forall T t t' b PC hp hp',
 t / hp == (joins PC b) => t' / hp' ->
 tref T t b / hp == PC => tref T t' b / hp'
this is some what similar to the reduction rule of protection when the 
protected subterm is not a value.

Now we show that we have to modify [t_ref] as well in the following typing rule 
so as to make the whole system sound. For without it [preservation breaks down],
[t_ref]: forall pc Gamma HT t T b b',
    has_type (joins pc b) Gamma HT t T ->
    b' = joins pc b ->
    subsum_r b' (labelT T) ->
    has_type pc Gamma HT (tref T t b) (an (ref T) b)
To see why we have to modify our typing rule consider the following legit reduction
sequence,
tref (an (ref (an int L)) L) (tref (an int L)(tcon 0 L) L) H / nil
==L=>
tref (an (ref (an int L)) L) (tloc (an int L) 0 L) H / ((tcon 0 H,an int L) :: nil),
according to [t_ref] we know that
has_type L empty_context []
         (tref (an int L)(tcon 0 L) L)
         (an (ref (an int L)) L)
which implies that 
has_type L empty_context []
         (tref (an (ref (an int L)) L) (tref (an int L)(tcon 0 L) L) H)
         (an (ref (an (ref (an int L)) L)) H)
now we reduce it according to [st_ref] we have,
tref (an (ref (an int L)) L) (tloc (an int L) 0 L) H / ((tcon 0 H,an int L) :: nil)
and given the new heap_typing,HT',as [an int L] we again have the resulting term as
well-typed,
has_type L empty_context [an int L]
         (tref (an (ref (an int L)) L) (tloc (an int L) 0 L) H) 
         (an (ref (an (ref (an int L)) L)) H)  
however the [heap_well_typed] breaks down,
~has_typed pc empty_context HT
          (tcon 0 H)
          (an int L).
One way to fix it is to have the following typing rule,
[t_ref]: forall pc Gamma HT t T b b',
 has_type (joins pc b) Gamma HT t T ->
 b' = joins pc b ->
 subsum_r b' (labelT T) ->
 has_type pc Gamma HT (tref T t b) (an (ref T) b)
which renders the term before reduction ill-typed.
Qed.     
*)
Inductive has_type : Sec -> context -> heap_Ty -> tm -> Ty -> Prop :=
  | t_var : forall pc Gamma HT x T,
      Gamma x = Some T ->
      has_type pc Gamma HT (tvar x) T
  | t_con : forall pc Gamma HT n b,
      has_type pc Gamma HT (tcon n b) (an int b)
 
  | t_unit: forall pc Gamma HT b,
      has_type pc Gamma HT (tunit b) (an unit b)
  | t_loc: forall pc Gamma HT T n b,
      heap_Tlookup n HT = Some T ->
      has_type pc Gamma HT (tloc T (Some n) b) (an (ref T) b)
 
  | t_abs: forall pc pc' Gamma HT x T e b T',
    has_type pc' (Cupdate Gamma x (Some T)) HT e T' ->
    has_type pc Gamma HT (tabs x T e b) (an (fn T pc' T') b)
 
  | t_prot: forall pc Gamma HT t b T T',
    has_type (joins pc b) Gamma HT t T ->
    T' = joinTs T b ->
    has_type pc Gamma HT (tprot b t) T'
 
  | t_app: forall pc Gamma HT T1 T2 T2' b t1 t2,
    has_type pc Gamma HT t1 (an (fn T1 (joins pc b) T2) b) ->
    has_type pc Gamma HT t2 T1 ->
    joinTs T2 b = T2' ->
    has_type pc Gamma HT (tapp t1 t2) T2'
 
  | t_ref: forall pc Gamma HT t T b b',
    has_type (joins pc b) Gamma HT t T ->
    b' = joins pc b ->
    subsum_r b' (labelT T)->
    has_type pc Gamma HT (tref T t b) (an (ref T) b)
 
  | t_deref: forall pc Gamma HT t T T' b,
    has_type pc Gamma HT t (an (ref T) b) ->
    T' = joinTs T b                        ->
    has_type pc Gamma HT (tderef t) T'
 
 | t_assign: forall pc Gamma HT t1 t2 b b' T,
   b' = labelT T ->
   subsum_r (joins pc b) b' ->
   has_type pc Gamma HT t1 (an (ref T) b) ->
   has_type pc Gamma HT t2 T ->
   has_type pc Gamma HT (tassign t1 t2) (an unit b')
 | t_sub: forall pc pc' Gamma HT t T T',
   has_type pc Gamma HT t T ->
   subsum_r pc' pc ->
   T <: T' ->
   has_type pc' Gamma HT t T'
.

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

(*inversion of [has_type pc Gamma HT (tloc T N b)(an (ref T) b)]*)

Lemma inversion_tloc:forall pc Gamma HT N T1 b T,
has_type pc Gamma HT (tloc T1 N b) T ->
exists n, exists T', exists T'', exists b',
(N = Some n)/\ 
(heap_Tlookup n HT = Some T1)/\(T'=an (ref T1) b)/\(T''=an (ref T1) b')/\(subsum_r b b')/\(T''<:T).
Proof. intros. remember (tloc T1 N b) as t. induction H0. inversion Heqt. inversion Heqt.
inversion Heqt. inversion Heqt. subst. exists n. exists (an (ref T1) b). exists (an (ref T1) b).
exists b. split. reflexivity. split. apply H0. split. reflexivity. split. reflexivity. split. apply sub_refl. apply subtyping_refl. inversion Heqt. inversion Heqt.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. apply IHhas_type in Heqt. inversion Heqt. exists x. inversion H3. exists x0.
inversion H4. exists x1. inversion H5. exists x2. split. apply H6. split. apply H6. split. apply H6. split. apply H6. split. apply H6. apply subtyping_trans with (x:=T)(y:=T). 
apply subtyping_refl. apply H6. apply H2. Qed.
 
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
(subsum_r b b')/\(subsum_r pc pc'')/\
((an (ref T1) b')<:T)/\
(has_type pc' Gamma HT t T1')/\(T1' <: T1'')/\(T1''<:T1)/\
(subsum_r (joins pc'' b) pc')/\
(subsum_r (joins pc'' b) (labelT T1')).
Proof. intros. remember (tref T1 t b) as e. induction H0. inversion Heqe.
inversion Heqe. inversion Heqe. inversion Heqe. inversion Heqe. inversion Heqe.
inversion Heqe. inversion Heqe. subst. exists (joins pc b). exists pc. exists T1. exists T1.
exists b. split. apply t_ref with (b':=joins pc b). apply H0. reflexivity. apply H2. split. apply sub_refl. split. apply sub_refl.
split. apply subtyping_refl. split. apply H0. split. apply subtyping_refl. split. apply subtyping_refl. split. apply sub_refl. apply H2.
inversion Heqe. inversion Heqe. 
apply IHhas_type in Heqe. inversion Heqe. exists x. inversion H3. exists x0. inversion H4. exists x1. inversion H5. exists x2. inversion H6. exists x3.
split. apply H7. split. apply H7. split. apply subsum_r_trans with (a:=pc')(b:=pc)(c:=x0). apply H1. apply H7. split. apply subtyping_trans with (x:=T)(y:=T).
apply subtyping_refl. apply H7. apply H2. apply H7.
Qed.

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
inversion H5. inversion H6. inversion H8. inversion H10. inversion H12. inversion H14.  
apply IHfree_var in H15. apply H15.
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
intros. apply inversion_tref in H0. inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H7.
inversion H9. inversion H11. inversion H13. apply IHt with (x:=x)in H14. intros contra. inversion contra.  apply H14 in H18.
inversion H18.
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
intros. apply t_ref with (b':=joins pc b). apply IHhas_type. intros. apply H3. apply e_tref. apply H4. reflexivity. subst.
apply H2.
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
intros. simpl. apply inversion_tref in H2. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6. inversion H7.
inversion H9. inversion H11. inversion H13. destruct T2. destruct r. inversion H14. inversion H14. inversion H14. apply t_sub with (pc:=pc)(T:=an (ref t0) x4).
apply t_sub with (pc:=pc)(T:=an (ref t0) s).   inversion H14. subst. apply t_ref with (b':=joins pc s). apply IHe with (T1:=T1).
apply H0.  apply value_pc with (pc:=pc). apply H0. apply H1. apply t_sub with (pc:=joins x1 s)(T:=x3). apply t_sub with (pc:=x0)(T:=x2). apply H15. apply H13.
apply H15. destruct pc. destruct x1. destruct s. apply sub_refl. apply sub_refl. destruct s. apply sub_LH. apply sub_refl. destruct x1. inversion H12. apply sub_refl.
apply H15. reflexivity. apply subsum_r_trans with (a:=joins pc s)(b:=joins x1 s)(c:=labelT t0). destruct pc. destruct x1. destruct s. apply sub_refl. apply sub_refl.
destruct s. apply sub_LH. apply sub_refl. destruct x1. inversion H12. apply sub_refl. apply subsum_r_trans with (a:=joins x1 s)(b:=labelT x2)(c:=labelT t0).
apply H15. apply subsum_r_trans with (a:=labelT x2)(b:=labelT x3)(c:=labelT t0). inversion H15. inversion H18. destruct x2. destruct x3. inversion H19. simpl. apply H22.
simpl. apply H25. simpl. apply H22. simpl. apply H22. inversion H15. inversion H18. inversion H20. destruct x3. destruct t0. inversion H21. simpl. apply H24. simpl. apply H27.
simpl. apply H24. simpl. apply H24. apply sub_refl. apply subt_ref. apply H10. apply sub_refl. apply subt_ref. inversion H14. apply H17.
Case ("tderef").
intros. simpl. apply inversion_tderef in H2. inversion H2. inversion H3. inversion H4. inversion H5.
apply t_sub with (pc:=pc)(T:=joinTs x1 x3).
 apply t_deref with (T:=x1)(b:=x3). apply IHe with (T1:=T1).
apply H0. apply H1. apply t_sub with (pc:=x0)(T:=an (ref x1) x3). apply t_sub with (pc:=x0)(T:=an (ref x1) x2).
apply H6. apply sub_refl. apply subt_ref. apply H6. apply H6. apply subtyping_refl. reflexivity. apply sub_refl.
apply H6.
Case ("tloc").
intros. simpl. destruct o. apply inversion_tloc in H2. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6.
inversion H8. inversion H10. inversion H12. inversion H14. subst. apply t_sub with (pc:=pc)(T:=an (ref t) x3). apply t_sub with (pc:=pc)(T:=an (ref t) s).
apply t_loc. inversion H7. subst. apply H6. apply sub_refl. apply subt_ref. apply H15. apply sub_refl. apply H6. apply inversion_tloc in H2. inversion H2.
inversion H3. inversion H4. inversion H5. inversion H6. inversion H7.
Case ("tassign").
intros. simpl. apply inversion_tassign in H2. inversion H2. inversion H3. inversion H4. inversion H5. apply t_sub with (pc:=pc)(T:=an unit (labelT x1)).
apply t_assign with (b:=x3)(T:=x1).  reflexivity. apply subsum_r_trans with (a:=joins pc x3)(b:=joins x0 x3)(c:=labelT x1). destruct pc. destruct x0.
simpl. apply sub_refl. simpl. destruct x3. apply sub_LH. apply sub_refl. destruct x0. inversion H6. inversion H8. inversion H10. inversion H12. inversion H14.
inversion H15. simpl. apply sub_refl. apply H6. apply IHe1 with (T1:=T1). apply H0. apply H1. apply t_sub with (pc:=x0)(T:=an (ref x1) x3). apply H6.
apply H6. apply subtyping_refl. apply IHe2 with (T1:=T1). apply H0. apply H1. apply t_sub with (pc:=x0)(T:=x2). apply H6. apply H6. apply H6. apply sub_refl.
apply H6.
Qed.
(*heap_well_typed*)
Definition heap_well_typed (HT:heap_Ty) (hp:heap) :=
  length HT = length hp /\
  (*every value on the heap must be well-formed*)
  (heap_well_formed hp (length hp))/\
  (forall pc l, l < length hp -> 
  (*two additional constraints*)
  (value (efst (heap_lookup l hp)))/\
  extract (heap_Tlookup l HT) <: esnd (heap_lookup l hp) /\
  subsum_r (labelT (esnd (heap_lookup l hp))) (label(efst (heap_lookup l hp))) /\
     has_type pc empty_context HT (efst(heap_lookup l hp)) (extract (heap_Tlookup l HT))).
(**
Note the reason for having the additional constraint which requires for a well_typed a heap
typing is that the type on the heap subsums the corresponding typing in the heap typing. 
Consider the following example which illustrates a well-typed stuck configuration,
has_type H empty_context [an int H] (tassign (tloc (an int H) 0 L)(tcon 1 L)) (an unit H)
with [(tcon 0 L,an int L)] as hp we have,
heap_well_typed [an int H] [(tcon 0 L,an int L)] for
a. has_type pc empty_context [an int H] (tcon 0 L)(an int H)
b. the label of the type on the heap is guarded by that of its type
c. they have the same length
Now,according to [progress] and set [PC=H] we should have,
exists p, tassign (tloc (an int H) 0 L)(tcon 1 L) / (tcon 0 L,an int L) 
==H=> p
and according to [st_assign],we acctually have,
stuck_term (tassign (tloc (an int H) 0 L)(tcon 1 L)) [(tcon 0 L,an int L)] H.
Qed.

*)
(*Some instances of consistent heap typing [HT] w.r.t. some heap [hp]*)
Example test_heap_well_typed_1:
heap_well_typed (an int L :: an unit H :: an (fn (an int L) H (an int L)) L :: an (ref (an int L)) H :: nil)
                ((tcon 0 L,an int L) :: (tunit H,an unit H) :: (tabs (Id 0)(an int L)(tcon 0 L) L,an (fn (an int L) H (an int L)) L) :: (tloc (an int L) (Some 0) H,an (ref (an int L)) H) :: nil).
Proof. split. simpl. reflexivity. split. apply one_hwf. apply one_hwf. apply one_hwf. apply one_hwf. apply nil_hwf. 
       simpl. apply wf_tloc. apply le_S. apply le_S. apply le_S. apply le_n.
       simpl. apply wf_tabs. apply wf_tcon. simpl. apply wf_tunit. simpl. apply wf_tcon.
       split. 
       simpl in H0. inversion H0. simpl. apply v_l. inversion H2. simpl. apply v_f. inversion H4. simpl. apply v_u. inversion H6. simpl. apply v_c. inversion H8.
       split. simpl in H0. inversion H0. simpl. apply subtyping_refl. inversion H2. simpl. apply subtyping_refl. inversion H4. simpl. apply subtyping_refl.
       inversion H6. simpl. apply subtyping_refl. inversion H8.
       split. simpl in H0. inversion H0. simpl. apply sub_refl. inversion H2. simpl. apply sub_refl. inversion H4. simpl. apply sub_refl.
       inversion H6. simpl. apply sub_refl. inversion H8. 
       simpl in H0. inversion H0. simpl. apply t_loc. simpl. reflexivity. inversion H2. simpl. apply t_abs. apply t_con. inversion H4. simpl. apply t_unit. inversion H6. simpl.
       apply t_con. inversion H8.
Qed.
Example test_heap_well_typed_2:
~heap_well_typed (an int L :: an unit H :: an (ref (an int L)) L :: nil)
               ((tcon 1 L,an int L) :: (tunit H,an unit H) :: nil).
Proof. intros contra. inversion contra. inversion H0. Qed.
Example test_heap_well_typed_3:
~heap_well_typed (an int L :: nil)
                 ((tcon 0 H,an int H) :: nil).
Proof. intros contra. inversion contra. inversion H1. specialize (H3 H 0). simpl in H3.
assert (0 < 1). apply le_n. apply H3 in H4. inversion H4. inversion H6. inversion H8. 
apply inversion_tcon in H10.
inversion H10. inversion H11. inversion H12. inversion H13. inversion H15.
inversion H17. subst. destruct x1. inversion H18. inversion H19. inversion H20.
Qed.
(*continue from here*)
Example test_heap_well_typed_4:
~heap_well_typed (an int L :: an unit H :: (an (ref (an int L)) L) :: nil)
                 ((tcon 1 L,an int L) :: (tunit L,an unit H) :: (tloc (an int L) (Some 0) L,an (ref (an int L)) L) :: nil).
Proof. intros contra. inversion contra. inversion H1. specialize (H3 L 1). simpl in H3. assert (1<3). apply le_S. apply le_n. apply H3 in H4.
inversion H4. inversion H6. inversion H8. inversion H9. 
Qed.
Example test_heap_well_typed_5:
~heap_well_typed ((an int H) :: nil)((tcon 0 L,an int L) :: nil).
Proof. intros contra. inversion contra. inversion H1. specialize (H3 L 0). simpl in H3. assert (0<1). apply le_n. apply H3 in H4.
inversion H4. inversion H6. inversion H7. inversion H11. 
Qed.
(*heap extends*)
Inductive extends : heap_Ty -> heap_Ty -> Prop :=
  | extends_nil : forall HT', 
      extends HT' nil
  | extends_cons : forall x HT' HT, 
      extends HT' HT -> 
      extends (x::HT') (x::HT).
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
Case ("t_ref"). intros. apply t_ref with(b':=joins pc b). apply IHhas_type. apply H3. reflexivity. subst. apply H2. 
Case ("t_deref"). intros. subst. apply t_deref with (T:=T)(b:=b). apply IHhas_type. apply H2. reflexivity.
Case ("t_assign"). intros. apply t_assign with (b:=b)(T:=T). apply H0. apply H1. apply IHhas_type1. apply H2.
                  apply IHhas_type2. apply H2. 
Case ("t_sub"). intros. apply IHhas_type in H3. apply t_sub with (pc:=pc)(T:=T). apply H3. apply H0. apply H2.
Qed.
(*#######################end###################*)

(*preservation*)
(*some auxiliary lemmas*)
Lemma joins_refl:forall a b,
joins a b = joins b a.
Proof. intros. destruct a. destruct b. reflexivity.
reflexivity. destruct b. reflexivity. reflexivity.
Qed.
Lemma joins_subsum:forall a b,
subsum_r a b ->
joins a b = b.
Proof. intros. destruct a. destruct b. reflexivity. reflexivity.
destruct b. inversion H0. reflexivity.
Qed.
Lemma subsum_guard:forall a b,
subsum_r a (joins a b).
Proof. destruct a. destruct b. apply sub_refl. apply sub_LH. destruct b.
apply sub_refl. apply sub_refl. Qed.
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
Lemma subsum_equal:forall a b,
subsum_r a b ->
subsum_r b a ->
a = b.
Proof. intros. destruct a. destruct b. reflexivity. inversion H1. destruct b. inversion H0. reflexivity.
Qed.
Lemma subsum_low:forall a,
subsum_r a L ->
a = L.
Proof. intros. destruct a. reflexivity. inversion H0.
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
Lemma join_tloc_b:forall T N s b,
joinvs (tloc T N s) b = tloc T N (joins s b).
Proof. intros. destruct s. destruct b. simpl. reflexivity. simpl. reflexivity.
destruct b. simpl. reflexivity. simpl. reflexivity. Qed.
Lemma join_tcon_H:forall n b,
joinvs (tcon n H) b = tcon n H.
Proof. intros. destruct b. reflexivity. reflexivity.
Qed.

Lemma join_tabs_H:forall x T e b,
joinvs (tabs x T e H) b = tabs x T e H.
Proof. intros. destruct b. reflexivity. reflexivity.
Qed.
Lemma join_tunit_H:forall b,
joinvs (tunit H) b = tunit H.
Proof. intros. destruct b. reflexivity. reflexivity.
Qed.
Lemma join_tloc_H:forall T N b,
joinvs (tloc T N H) b = tloc T N H.
Proof. intros. destruct b. reflexivity. reflexivity.
Qed.
Lemma label_joinvs:forall t a,
value t ->
label (joinvs t a) = joins (label t) a.
Proof. intros. inversion H0. rewrite->join_tcon_b.  reflexivity. rewrite->join_tabs_b. simpl.
       reflexivity. rewrite->join_tunit_b. reflexivity.  rewrite->join_tloc_b. reflexivity.
Qed.
Lemma joinTs_same:forall T,
joinTs T (labelT T) = T.
Proof. intros. destruct T. simpl. destruct s. reflexivity. reflexivity.
Qed.
Lemma sub_T_b:forall a b r,
subsum_r a b ->
an r a <: an r b.
Proof. intros. destruct r. apply subt_int. apply H0. apply subt_fn. apply H0. apply sub_refl.
apply subtyping_refl. apply subtyping_refl. apply subt_unit. apply H0. apply subt_ref. apply H0.
Qed.
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
Lemma subtyping_subsum:forall T1 T2,
T1 <: T2 ->
subsum_r (labelT T1)(labelT T2).
Proof. intros. inversion H0. subst. simpl. apply H1. subst. simpl. apply H1.
subst. simpl. apply H1. subst. simpl. apply H1.
Qed.
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
      intros. rewrite->join_tloc_b. subst. apply inversion_tloc in H3. inversion H3. inversion H4. inversion H5. inversion H6. inversion H7. inversion H9. inversion H11. inversion H13. inversion H15. subst.
      destruct T. destruct r. inversion H17. inversion H17. inversion H17. inversion H17. subst. simpl in H2. apply t_sub with (pc:=pc)(T:=an (ref t) (joins b0 b)). apply t_loc. inversion H8. subst.
      apply H7. apply sub_refl. apply subt_ref. apply subsum_joins. apply subsum_r_trans with (a:=b0)(b:=x2)(c:=s). apply H11. inversion H17. apply H18. apply H2. 
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
      rewrite->join_tloc_b. subst. rewrite->join_tloc_b in H2. apply inversion_tloc in H2. inversion H2. inversion H3. inversion H4. inversion H5.  inversion H6. inversion H8. inversion H10. inversion H12. inversion H14. subst. destruct T. destruct r. inversion H16. inversion H16. inversion H16.
      inversion H16. subst. apply t_sub with (pc:=pc)(T:=an (ref t) x2). apply t_sub with (pc:=pc)(T:=an (ref t) (joins b0 b')).
      apply t_sub with (pc:=pc)(T:=an (ref t) (joins b0 b)). apply t_loc. inversion H7. subst. apply H6. apply sub_refl. apply subt_ref. apply joins_subtyping_2. apply H1. apply sub_refl. apply subt_ref. apply H10. apply sub_refl. apply subt_ref. inversion H16. apply H17.
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
     intros. rewrite->join_tloc_b. subst. apply inversion_tloc in H1. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H7. inversion H9.
     inversion H11. inversion H13. subst. destruct T. destruct r. inversion H15. inversion H15. inversion H15. rewrite->joinTs_b. inversion H15. subst. apply t_sub with (pc:=pc)(T:=an (ref t)(joins b0 b)).
     apply t_loc. inversion H6. subst. apply H5. apply sub_refl. apply subt_ref. apply joins_subtyping_1. apply subsum_r_trans with (a:=b0)(b:=x2)(c:=s). apply H9. inversion H15. apply H16.
Qed.

Lemma l_lt_hp:forall (T:Type)(l:nat) (hp:list T),
l <= length hp ->
l <> length hp ->
l < length hp.
Proof. intros. unfold not in H1. unfold lt. inversion H0. apply H1 in H2. inversion H2. 
apply n_iff_Sn_left. apply H3. Qed.

Lemma labelT_subsum_labelt:forall pc HT t T,
value t ->
has_type pc empty_context HT t T ->
subsum_r (label t)(labelT T).
Proof. intros. inversion H0.
Case ("tcon"). subst. apply inversion_tcon in H1. inversion H1. inversion H2. inversion H3. inversion H4.
               inversion H6. inversion H8. subst. apply subtyping_subsum in H10. simpl in H10. apply subsum_r_trans with (a:=label (tcon n b))(b:=x1)(c:=labelT T).
               compute. apply H9. apply H10. 
Case ("tabs"). subst. apply inversion_tabs in H1. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6. inversion H7. inversion H8.
               inversion H10. inversion H12. inversion H14. inversion H16. inversion H18. inversion H20. apply subtyping_subsum in H22. simpl in H22. compute. destruct T. simpl in H22.
               apply subsum_r_trans with (a:=b)(b:=x5)(c:=s). apply H21. apply H22.
Case ("tunit"). subst. apply inversion_tunit in H1. inversion H1. inversion H2. inversion H3. inversion H4. inversion H6. inversion H8. subst. apply subtyping_subsum in H10. simpl in H10.
               apply subsum_r_trans with (a:=label (tunit b))(b:=x1)(c:=labelT T). compute. apply H9. apply H10.
Case ("tloc"). subst. apply inversion_tloc in H1. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H7. inversion H9. inversion H11. inversion H13. subst.  apply subtyping_subsum in H15. simpl in H15.
               apply subsum_r_trans with (a:=label (tloc T0 (Some n) b))(b:=x2)(c:=labelT T). compute. apply H9. apply H15.
Qed.

(**
Lemma well_formed_heap_extend:forall t hp C,
well_formed t hp ->
well_formed t (snoc hp C).
Proof. intros t. induction t.
Case ("tvar"). intros. apply wf_tvar.
Case ("tprot"). intros. apply wf_tprot. apply IHt. inversion H0. apply H4.
Case ("tcon"). intros. apply wf_tcon.
Case ("tabs"). intros. apply wf_tabs. apply IHt. inversion H0. apply H6.
Case ("tapp"). intros. apply wf_tapp. apply IHt1. inversion H0. apply H3. 
               apply IHt2. inversion H0. apply H5.
Case ("tunit"). intros. apply wf_tunit.
Case ("tref"). intros. apply wf_tref. apply IHt. inversion H0. apply H5.
Case ("tderef"). intros. apply wf_tderef. apply IHt. inversion H0. apply H2.
Case ("tloc"). intros. destruct o. apply wf_tloc. rewrite->length_snoc. apply le_S. inversion H0. apply H5.
               inversion H0.
Case ("tassign"). intros. apply wf_tassign. apply IHt1. inversion H0. apply H3. apply IHt2. inversion H0.
               apply H5.
Qed.
*)

(**
Lemma well_formed_heap_replace:forall t hp C x,
well_formed t hp ->
well_formed t (heap_replace x C hp).
Proof. intros t. induction t.
Case ("tvar"). intros. apply wf_tvar.
Case ("tprot"). intros. apply wf_tprot. apply IHt. inversion H0. apply H4.
Case ("tcon"). intros.  apply wf_tcon.
Case ("tabs"). intros. apply wf_tabs. apply IHt. inversion H0. apply H6.
Case ("tapp"). intros. apply wf_tapp. apply IHt1. inversion H0. apply H3.  apply IHt2. inversion H0.
               apply H5.
Case ("tunit"). intros. apply wf_tunit.
Case ("tref"). intros. apply wf_tref. apply IHt. inversion H0. apply H5.
Case ("tderef"). intros. apply wf_tderef. apply IHt. inversion H0. apply H2.
Case ("tloc"). intros. destruct o. apply wf_tloc. rewrite->length_replace. inversion H0.
               apply H5. inversion H0.
Case ("tassign"). intros. apply wf_tassign. apply IHt1. inversion H0. apply H3. apply IHt2. inversion H0.
               apply H5.
Qed.
*)
(**
Lemma well_formed_joinvs_b:forall t hp b C,
value t ->
well_formed t hp ->
well_formed (joinvs t b) (snoc hp C).
Proof. intros. inversion H0.
Case ("tcon"). subst. rewrite->join_tcon_b. apply wf_tcon.
Case ("tabs"). subst. rewrite->join_tabs_b. apply wf_tabs. inversion H1. subst. apply well_formed_heap_extend.
               apply H7.
Case ("tunit"). rewrite->join_tunit_b. apply wf_tunit.
Case ("tloc"). rewrite->join_tloc_b. apply wf_tloc. subst. inversion H1. subst. rewrite->length_snoc. apply le_S.
               apply H6.
Qed. 
*)

Lemma well_formed_b:forall t hp b,
value t ->
well_formed t hp ->
well_formed (joinvs t b) hp.
Proof. intros. inversion H0.
Case ("tcon"). subst. rewrite->join_tcon_b. apply wf_tcon.
Case ("tabs"). subst. rewrite->join_tabs_b. apply wf_tabs.
               inversion H1. apply H7.
Case ("tunit"). subst. rewrite->join_tunit_b. apply wf_tunit.
Case ("tloc"). subst. rewrite->join_tloc_b. apply wf_tloc. inversion H1.
               apply H6.
Qed.


(*type preservation*)
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
     intros. inversion H4. subst. apply IHhas_type in H13. inversion H13. exists x.
     split. apply H1. split. apply t_prot with (T:=T). apply H1. reflexivity. apply H1.
     reflexivity. apply joins_subtyping_1. apply H3. apply H2. 
     subst. exists HT. split. apply extends_refl. split. apply value_pc with (pc:=joins pc b).
     apply value_b. apply H13. apply has_type_joinvs_b. apply H13. apply H0. apply H2.
Case ("t_app").
     intros. inversion H2. subst. exists HT. split. apply extends_refl. split. apply inversion_tabs in H0_. inversion H0_. inversion H0. inversion H4. inversion H5. inversion H6. inversion H7. inversion H8.
     inversion H9. inversion H15. inversion H17. inversion H19. inversion H21. inversion H23. inversion H25.
     apply t_sub with (pc:=pc)(T:=joinTs T2 x6). apply t_sub with (pc:=pc)(T:=joinTs T2 b0). apply t_prot with (T:=T2).
     apply t_sub with (pc:=x5)(T:=T2). apply t_sub with (pc:=x4)(T:=T2). apply t_sub with (pc:=x4)(T:=x2). apply t_sub with (pc:=x4)(T:=x1). apply value_pc with (pc':=x4) in H0_0.
     apply t_sub with (pc':=x4)(T':=x0)in H0_0. apply t_sub with (pc':=x4)(T':=T) in H0_0. apply substitution_preserves_typing with (T1:=T). apply H13. apply H0_0. apply H16. apply sub_refl.
     apply H22. apply sub_refl.  inversion H27. apply H38. apply H13. apply sub_refl. apply H24. apply sub_refl.
     inversion H27. apply H39. apply H18. apply subtyping_refl. apply subsum_r_trans with (a:=joins pc b0)(b:=joins pc b)(c:=x5). apply subsum_r_trans with (a:=joins pc b0)(b:=joins pc x6)(c:=joins pc b).
     apply joins_subtyping_2. apply H26. apply joins_subtyping_2. inversion H27. apply H33. inversion H27. apply H37. apply subtyping_refl. reflexivity. apply sub_refl. apply joinTs_subtyping_s. apply H26. apply sub_refl.
     apply joinTs_subtyping_s.  inversion H27. apply H33. apply H1. subst.
     apply IHhas_type1 in H13. inversion H13. exists x. split. apply H0. split. apply t_app with (T1:=T1)(T2:=T2)(b:=b). apply H0. apply change_HT with (HT:=HT). apply H0. apply H0_0. reflexivity. apply H0. reflexivity. apply H3. apply H1.
     subst. apply IHhas_type2 in H14. inversion H14. exists x. split. apply H0. split. apply t_app with (T1:=T1)(T2:=T2)(b:=b). apply change_HT with (HT:=HT).  apply H0. apply H0_. apply H0. reflexivity. apply H0. reflexivity. apply H3.
     apply H1.
Case ("t_ref").
      intros. inversion H5. subst. exists (snoc HT T). split. apply extends_snoc. split. apply t_loc. inversion H4. 
      rewrite<-H1. rewrite->extends_Tlookup_last. reflexivity. split.
      rewrite->length_snoc. rewrite->length_snoc. inversion H4. rewrite->H1. reflexivity.
      inversion H4. split. rewrite->length_snoc. apply heap_well_formed_extend.  apply H6. apply well_formed_b. apply H14. apply H13.
      (*continue from here*)
       intros. remember (beq_nat l (length hp)) as CC. destruct CC. apply beq_nat_eq in HeqCC. rewrite->HeqCC. assert (heap_Tlookup (length hp)(snoc HT T) = heap_Tlookup (length HT)(snoc HT T)).
      rewrite<-H1. reflexivity. rewrite->H8. rewrite->extends_Tlookup_last. simpl. rewrite->extends_lookup_last. simpl. split. apply value_b. apply H14. split. apply subtyping_refl. split.
      rewrite->joins_refl.  
      assert (subsum_r (joins PC b)(labelT T)). apply subsum_r_trans with (a:=joins PC b)(b:=joins pc b)(c:=labelT T). apply joins_subtyping_1. apply H3. apply H2.
      apply joins_subsum in H9. assert (joins PC b = joins b PC). rewrite->joins_refl. reflexivity. rewrite->H10 in H9. rewrite->H9. inversion H14. subst. rewrite->join_tcon_b. assert (label (tcon n (joins b0 (labelT T)))=joins b0 (labelT T)). reflexivity.
      rewrite->joins_refl. compute. apply subsum_guard. rewrite->join_tabs_b. rewrite->joins_refl. compute. apply subsum_guard. rewrite->join_tunit_b. rewrite->joins_refl. compute. apply subsum_guard. rewrite->join_tloc_b. rewrite->joins_refl. compute. apply subsum_guard.
      apply change_HT with (HT:=HT). apply extends_snoc. apply value_pc with (pc:=joins pc b). apply value_b. apply H14. apply t_sub with (pc:=joins pc b)(T:=joinTs T (joins (labelT T)(joins b PC))).
      apply has_type_joinvs_b. apply H14. apply H0. apply sub_refl. assert (subsum_r (joins b PC)(labelT T)). apply subsum_r_trans with (a:=joins b PC)(b:=joins b pc)(c:=labelT T). apply joins_subtyping_2. apply H3. rewrite->joins_refl.
      apply H2. apply joins_subsum in H9. rewrite->joins_refl. rewrite->H9. destruct T. simpl. destruct s. apply subtyping_refl. apply subtyping_refl.
      symmetry in HeqCC. apply beq_nat_false in HeqCC. unfold lt in H7. rewrite ->length_snoc in H7. apply n_iff_Sn_right in H7. assert (l < length hp). apply l_lt_hp. apply H7. apply HeqCC. clear H7. clear HeqCC. assert (l <length hp). apply H8. assert (l <length hp).
      apply H8. rewrite<-H1 in H8. apply extends_lookup with (p:=(joinvs t (joins (labelT T)(joins b PC)),T))in H7. rewrite<-H7. apply extends_Tlookup with (HT':=snoc HT T) in H8.  rewrite->H8. split. inversion H6. specialize (H11 pc0 l). apply H11 in H9. apply H9. split. 
      inversion H6.  specialize (H11 pc0 l). apply H11 in H9. apply H9. split.
      inversion H6.  specialize (H11 pc0 l). apply H11 in H9. apply H9. 
      inversion H6.  specialize (H11 pc0 l). apply H11 in H9.
      apply change_HT with (HT:=HT). apply extends_snoc. apply H9.
      apply extends_snoc. subst. destruct b. rewrite->joins_refl in H15. simpl in H15.
      apply IHhas_type in H15. inversion H15. exists x. split. apply H1. split. apply t_ref with (b':=joins pc L). apply H1. reflexivity. apply H2. apply H1. reflexivity. rewrite->joins_refl. simpl. apply H3. apply H4. rewrite->joins_refl in H15. simpl in H15.
      apply IHhas_type in H15. inversion H15. exists x. split. apply H1. split. apply t_ref with (b':=joins pc H). apply H1. reflexivity. apply H2. apply H1. reflexivity. rewrite->joins_refl. simpl. apply sub_refl. apply H4.
Case ("t_deref").
      intros. inversion H4. subst. exists HT. split. apply extends_refl. split. apply inversion_tloc in H0. inversion H0. inversion H1. inversion H5. inversion H6. inversion H7. inversion H9. inversion H13. inversion H15. inversion H17.
      subst. apply t_sub with (pc:=pc)(T:=joinTs T x2). apply t_sub with (pc:=pc)(T:=joinTs T b0). apply t_prot with (T:=T). inversion H19. subst. inversion H2. inversion H20. apply H22 with (pc:=joins pc b0)in H11. inversion H7.  inversion H23. subst. rewrite->H12 in H11. simpl in H11.
      inversion H11. inversion H26. inversion H28. apply H30.
      reflexivity. apply sub_refl. apply joinTs_subtyping_s. apply H13. apply sub_refl. apply joinTs_subtyping_s. inversion H19. apply H16. apply H2. subst. 
      apply IHhas_type in H12. inversion H12. exists x. split. apply H1. split. apply t_deref with (T:=T)(b:=b). apply H1. reflexivity. apply H1. reflexivity. apply H3. apply H2.
Case ("t_assign").
      intros. inversion H4. subst. exists HT. split. apply extends_refl. split. apply t_sub with (pc:=pc)(T:=an unit (joins pc b)).
      apply t_sub with (pc:=pc)(T:=an unit (joins PC b)). apply t_sub with (pc:=pc)(T:=an unit (joins PC b0)). apply t_unit. apply sub_refl. apply subt_unit. apply joins_subtyping_2. apply inversion_tloc in H0_. inversion H0_. inversion H0. inversion H5. inversion H6. inversion H7. inversion H9. inversion H15. inversion H19. inversion H21. subst. inversion H23. subst.
      apply subsum_r_trans with (a:=b0)(b:=x2)(c:=b). apply H15. inversion H23. apply H24. apply sub_refl. apply subt_unit. apply joins_subtyping_1. apply H3. apply sub_refl. apply subt_unit. apply H1. split. inversion H2. 
      rewrite->H0. rewrite->length_replace. reflexivity. split. rewrite->length_replace. 
      apply heap_well_formed_replace. apply well_formed_b. apply H13. apply H11. apply H10. apply H12.
      intros. remember (beq_nat l n) as CC. destruct CC.
       apply beq_nat_eq in HeqCC. subst. apply lookup_replace_eq with (t:=(joinvs t2 (joins (labelT T0) (joins PC b0)),joinTs T0 (joins PC b0)))in H12. rewrite->H12. simpl. apply inversion_tloc in H0_. inversion H0_. inversion H5. inversion H6.
      inversion H7. inversion H8. inversion H14. inversion H16. inversion H20. inversion H22. subst. inversion H9. subst. rewrite->H15. simpl. split.
      apply value_b. apply H13.
      split.
      assert(subsum_r (joins PC b0)(labelT T0)). apply subsum_r_trans with (a:=joins PC b0)(b:=joins pc b0)(c:=labelT T0). apply joins_subtyping_1. apply H3. apply subsum_r_trans with (a:=joins pc b0)(b:=joins pc b)(c:=labelT T0). 
      apply joins_subtyping_2. apply subsum_r_trans with (a:=b0)(b:=x2)(c:=b). apply H8. inversion H24. apply H21. inversion H24. apply H1. apply joins_subsum in H19. assert (joins (labelT T0)(joins PC b0) = joins (joins PC b0)(labelT T0)). rewrite->joins_refl. reflexivity. destruct T0. rewrite->joinTs_b. simpl in H19. rewrite->joins_refl in H19. rewrite->H19. apply subtyping_refl.
      split.
      assert(subsum_r (joins PC b0)(labelT T0)). apply subsum_r_trans with (a:=joins PC b0)(b:=joins pc b0)(c:=labelT T0). apply joins_subtyping_1. apply H3. apply subsum_r_trans with (a:=joins pc b0)(b:=joins pc b)(c:=labelT T0). 
      apply joins_subtyping_2. apply subsum_r_trans with (a:=b0)(b:=x2)(c:=b). apply H8. inversion H24. apply H21. inversion H24. apply H1. apply joins_subsum in H19.  destruct T0. rewrite->joinTs_b. simpl in H19. rewrite->joins_refl in H19. rewrite->H19. simpl. rewrite->H19.
      inversion H13.
      rewrite->join_tcon_b. assert (label (tcon n (joins b1 s)) = joins b1 s). reflexivity. rewrite->H25. rewrite->joins_refl. apply subsum_guard. rewrite->join_tabs_b. assert (label (tabs (Id n) T0 e (joins b1 s)) = joins b1 s). reflexivity. rewrite->H25.
      rewrite->joins_refl. apply subsum_guard. rewrite->join_tunit_b. assert (label (tunit (joins b1 s)) = joins b1 s). reflexivity. rewrite->H25. rewrite->joins_refl. apply subsum_guard.
      rewrite->join_tloc_b. assert (label (tloc T0 (Some n) (joins b1 s)) = joins b1 s). reflexivity. rewrite->H25. rewrite->joins_refl. apply subsum_guard.

      apply value_pc with (pc:=pc). apply value_b. apply H13. apply t_sub with (pc:=pc)(T:=joinTs T0 (joins (labelT T0)(joins PC b0))). 
      apply has_type_joinvs_b. apply H13. inversion H24. apply H0_0. apply sub_refl. assert (subsum_r (joins PC b0)(labelT T0)). apply subsum_r_trans with (a:=joins PC b0)(b:=joins pc b)(c:=labelT T0). apply subsum_r_trans with (a:=joins PC b0)(b:=joins PC b)(c:=joins pc b). apply joins_subtyping_2. apply subsum_r_trans with (a:=b0)(b:=x2)(c:=b). apply H8. inversion H24. apply H21. apply joins_subtyping_1. 
      apply H3. inversion H24. subst. apply H1. apply joins_subsum in H19. rewrite->joins_refl in H19. rewrite->H19. rewrite->joinTs_same. apply subtyping_refl. subst.

      symmetry in HeqCC. apply beq_nat_false in HeqCC. rewrite->length_replace in H0. apply lookup_replace_neq with (t:=(joinvs t2 (joins (labelT T0)(joins PC b0)),joinTs T0 (joins PC b0)))(st:=hp) in HeqCC. rewrite->HeqCC. split. inversion H2. inversion H6. specialize (H8 pc0 l). apply H8 in H0. apply H0.
      split. inversion H2. inversion H6. specialize (H8 pc0 l). apply H8 in H0. apply H0. split. inversion H2. inversion H6. specialize (H8 pc0 l). apply H8 in H0. apply H0. inversion H2. inversion H6. specialize (H8 pc0 l). apply H8 in H0. apply H0.
      subst.
      apply IHhas_type1 in H14. inversion H14. exists x. split. apply H0. split. apply t_assign with (b:=b)(T:=T). reflexivity. apply H1.  apply H0. apply change_HT with (HT:=HT). apply H0. apply H0_0. apply H0. reflexivity. apply H3. apply H2. subst.
      apply IHhas_type2 in H15. inversion H15. exists x. split. apply H0. split. apply t_assign with (b:=b)(T:=T). reflexivity. apply H1. apply change_HT with (HT:=HT). apply H0. apply H0_. apply H0. apply H0. reflexivity. apply H3. apply H2.
Case ("t_sub"). 
      intros. apply IHhas_type in H5. inversion H5. exists x. split. apply H6. split. apply t_sub with (pc:=pc)(T:=T). apply H6. apply H1. apply H2. apply H6. apply Heqcontext. apply subsum_r_trans with (a:=PC)(b:=pc')(c:=pc). apply H3. apply H1. apply H4.
Qed.
(*generalization of preservation*)
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

(*progress*)
(*one auxiliary lemma*)
Lemma well_typed_well_formed:forall pc HT hp t T,
has_type pc empty_context HT t T ->
heap_well_typed HT hp ->
well_formed t (length hp).
Proof. intros. generalize dependent hp. induction H0.
Case ("t_var"). intros. apply wf_tvar.
Case ("t_con"). intros. apply wf_tcon.
Case ("t_unit"). intros. apply wf_tunit.
Case ("t_loc"). intros. apply wf_tloc. inversion H1. rewrite<-H2. apply change_HT' with (T:=T).
               apply H0.
Case ("t_abs"). intros. apply wf_tabs. apply IHhas_type. apply H1.
Case ("t_prot"). intros. apply wf_tprot. apply IHhas_type. apply H2.
Case ("t_app"). intros. apply wf_tapp. apply IHhas_type1. apply H1. apply IHhas_type2.
               apply H1.
Case ("t_ref"). intros. apply wf_tref. apply IHhas_type. apply H3.
Case ("t_deref"). intros. apply wf_tderef. apply IHhas_type. apply H2.
Case ("t_assign"). intros. apply wf_tassign. apply IHhas_type1. apply H2.
                 apply IHhas_type2. apply H2.
Case ("t_sub"). intros. apply IHhas_type. apply H3.
Qed.

Theorem progress: forall t T pc PC HT hp,
has_type pc empty_context HT t T ->
heap_well_typed HT hp ->
subsum_r PC pc ->
value t \/ (exists p, step (t,hp) PC p).
Proof. intros. remember (@empty_context) as context. generalize dependent hp.
generalize dependent PC. induction H0.
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
      intros. subst. right. assert (heap_well_typed HT hp). apply H3. apply IHhas_type with (PC:=joins PC b)in H1. 
      inversion H1. exists (joinvs t b,hp). apply st_protv. inversion H3. apply H6. 
      apply well_typed_well_formed with (hp:=hp)in H0.  apply H0. apply H3.
      apply H4. inversion H4. destruct x. exists (tprot b t0,h).
      apply st_prot. inversion H3. apply H7. 
      apply well_typed_well_formed with (hp:=hp) in H0. apply H0. apply H3. 
      apply H5. reflexivity. apply joins_subtyping_1. apply H2. 
Case ("t_app").
      intros. subst. right. assert (heap_well_typed HT hp). apply H1.
      assert (heap_well_typed HT hp). apply H1.
      apply IHhas_type1 with (PC:=PC) in H1.
      apply IHhas_type2 with (PC:=PC) in H0. inversion H1. inversion H0. inversion H4. subst. apply inversion_tcon in H0_.
      inversion H0_. inversion H6. inversion H7. inversion H8. inversion H10. inversion H12. subst. inversion H14.
      subst. exists (tprot b0 ([(Id n ) :=  t2]e),hp). apply st_appabs. inversion H3. apply H7.
      apply well_typed_well_formed with (hp:=hp)in H0_0. apply H0_0. apply H3. apply well_typed_well_formed with (hp:=hp)in H0_.
      inversion H0_. apply H11. apply H3. 
       apply H5. subst. apply inversion_tunit in H0_.
      inversion H0_. inversion H6. inversion H7. inversion H8. inversion H10. inversion H12. subst. inversion H14.
      subst. apply inversion_tloc in H0_. inversion H0_. inversion H6. inversion H7. inversion H8. inversion H9. inversion H11. inversion H13.
      inversion H15. inversion H17. subst. inversion H19. inversion H5. destruct x. exists (tapp t1 t,h). apply st_app2. inversion H3. apply H8.
      apply well_typed_well_formed with (hp:=hp) in H0_.
      apply H0_. apply H3. apply well_typed_well_formed with (hp:=hp) in H0_0. apply H0_0. apply H3.  
      apply H4. apply H6.
      inversion H4. destruct x. exists (tapp t t2,h). apply st_app1.  inversion H3. apply H7. 
      apply well_typed_well_formed with (hp:=hp) in H0_.
      apply H0_. apply H3.
       apply well_typed_well_formed with (hp:=hp) in H0_0. apply H0_0. apply H3.
      apply H5. reflexivity. apply H2. reflexivity. apply H2.
Case ("t_ref").
      intros. subst. right. assert (heap_well_typed HT hp). apply H4. apply IHhas_type with (PC:=PC)in H1. inversion H1. 
      exists (tloc T (Some (length hp)) b,snoc hp (joinvs t (joins (labelT T)(joins b PC)),T)). apply st_refv with (v':=joinvs t (joins (labelT T)(joins b PC)))(b':=labelT T)(b'':=joins b PC)(b''':= joins (labelT T)(joins b PC)).
      inversion H4. apply H7. 
      apply well_typed_well_formed with (hp:=hp) in H0. apply H0. apply H4.
      apply H5. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. destruct b.  inversion H5. destruct x. exists (tref T t0 L,h).
      apply st_ref. inversion H4. apply H8. 
      apply well_typed_well_formed with (hp:=hp) in H0. apply H0. apply H4.
      rewrite->joins_refl. simpl. apply H6. assert (empty_context=empty_context). reflexivity. apply IHhas_type with (PC:=H)(hp:=hp) in H6. inversion H6.
      exists (tloc T (Some (length hp)) H,snoc hp (joinvs t H,T)). apply st_refv with (v':=joinvs t H)(b':=labelT T)(b'':=H)(b''':=H).
      inversion H4.  apply H9. 
      apply well_typed_well_formed with (hp:=hp) in H0. apply H0. apply H4.
      apply H7. reflexivity. reflexivity. rewrite->joins_refl. reflexivity. reflexivity. reflexivity.
      inversion H7. destruct x. exists (tref T t0 H,h). apply st_ref.
      inversion H4. apply H10. 
      apply well_typed_well_formed with (hp:=hp) in H0. apply H0. apply H4.
      rewrite->joins_refl. simpl. apply H8. rewrite->joins_refl. simpl. apply sub_refl. apply H4. reflexivity. apply subsum_r_trans with (a:=PC)(b:=pc)(c:=joins pc b).
      apply H3. apply subsum_guard. 
Case ("t_deref").
      intros. subst. right. assert (heap_well_typed HT hp). apply H3. apply IHhas_type with (PC:=PC)in H1. inversion H1. 
      inversion H4. subst. apply inversion_tcon in H0. inversion H0. inversion H5. inversion H6.
      inversion H7. inversion H9. inversion H11. subst. inversion H13. subst. apply inversion_tabs in H0. inversion H0. inversion H5. inversion H6. inversion H7.
      inversion H8. inversion H9. inversion H10. inversion H11. inversion H13. inversion H15. inversion H17. inversion H19. inversion H21. inversion H23. inversion H25.
      subst. apply inversion_tunit in H0. inversion H0. inversion H5. inversion H6. inversion H7. inversion H9. inversion H11. subst. inversion H13. subst. apply inversion_tloc in H0.
      inversion H0. inversion H5. inversion H6. inversion H7. inversion H8. inversion H9. inversion H10.  apply change_HT' in H11. exists (tprot b0 (efst (heap_lookup x hp)),hp). apply st_derefloc. inversion H3.
      apply H15. inversion H3. rewrite->H14 in H11. apply H11. reflexivity. 
      inversion H4. destruct x. exists (tderef t0,h). apply st_deref. inversion H3. apply H7. 
      apply well_typed_well_formed with (hp:=hp) in H0. apply H0. apply H3.
      apply H5. reflexivity. apply H2.
Case ("t_assign").
      intros. subst. right. assert (heap_well_typed HT hp). apply H3. assert (heap_well_typed HT hp). apply H3. 
      apply IHhas_type1 with (PC:=PC)in H0. apply IHhas_type2 with (PC:=PC)in H4. inversion H0. inversion H4. inversion H5. subst. apply inversion_tcon in H0_. inversion H0_. inversion H7. inversion H8.
      inversion H9. inversion H11. inversion H13. subst. inversion H15. subst. apply inversion_tabs in H0_. inversion H0_. inversion H7. inversion H8. inversion H9. inversion H10.
      inversion H11. inversion H12. inversion H13. inversion H15. inversion H17. inversion H19. inversion H21. inversion H23. inversion H25. inversion H27. subst. apply inversion_tunit in H0_. inversion H0_.
      inversion H7. inversion H8. inversion H9. inversion H11. inversion H13. subst. inversion H15. subst. apply inversion_tloc in H0_. inversion H0_. inversion H7. inversion H8. inversion H9. inversion H10. inversion H11. subst. inversion H12. apply change_HT' in H13.
      exists (tunit (joins PC b0),heap_replace x (joinvs t2 (joins (labelT T0)(joins PC b0)),joinTs T0 (joins PC b0)) hp). apply st_assign with (v':=joinvs t2 (joins(labelT T0)(joins PC b0)))(T':=joinTs T0 (joins PC b0))(b':=labelT T0)(b''':=joins (labelT T0)(joins PC b0))(l:=label t2). inversion H3.
      apply H16.
      apply well_typed_well_formed with (hp:=hp) in H0_0. apply H0_0. apply H3. inversion H3.
      rewrite<-H15. apply H13. apply H6.
      reflexivity. reflexivity. reflexivity. inversion H3.
      assert (value t2). apply H6. apply labelT_subsum_labelt with (pc:=pc)(HT:=HT)(T:=T) in H17. inversion H14. inversion H19. inversion H21. subst. inversion H23. subst. apply joins_subsum in H17. rewrite->H17. inversion H16. specialize (H24 pc x). rewrite->H15 in H13. apply H24 in H13. inversion H10. inversion H26. rewrite->H27 in H13. simpl in H13. inversion H13. inversion H30. inversion H32.
      apply subtyping_subsum in H31. inversion H32. assert (subsum_r (labelT T)(label (efst (heap_lookup x hp)))). apply subsum_r_trans with (a:=labelT T)(b:=labelT (esnd (heap_lookup x hp)))(c:=label (efst (heap_lookup x hp))). apply H31. apply H33. inversion H32. assert (subsum_r (label (efst (heap_lookup x hp)))(labelT T)). apply labelT_subsum_labelt with (pc:=pc)(HT:=HT).
      apply H29. apply H36. apply subsum_equal. apply H37. apply H40. apply H0_0. 
      inversion H3. inversion H12. inversion H16. specialize (H20 L x). rewrite->H17 in H20. rewrite->H15 in H13. apply H20 in H13. inversion H13. simpl in H22. inversion H18. inversion H24. inversion H26. subst. inversion H28. subst.
      apply subsum_r_trans with (a:=joins PC b0)(b:=labelT T)(c:=label (efst (heap_lookup x hp))). assert (subsum_r (joins PC b0)(labelT T)). apply subsum_r_trans with (a:=joins PC b0)(b:=joins pc b0)(c:=labelT T). apply joins_subtyping_1. apply H2. apply subsum_r_trans with (a:=joins pc b0)(b:=joins pc b)(c:=labelT T). apply joins_subtyping_2. 
      apply subsum_r_trans with (a:=b0)(b:=x2)(c:=b). apply H18. inversion H28. apply H29. apply H1. apply H23.
      apply subsum_r_trans with (a:=labelT T)(b:=labelT (esnd (heap_lookup x hp)))(c:=label (efst (heap_lookup x hp))). inversion H22. inversion H29.  apply subtyping_subsum in H23. apply H23. apply H13. reflexivity. reflexivity. reflexivity. reflexivity.
(**
      inversion H30. rewrite->H32. apply labelT_subsum_labelt with (pc:=pc)(HT:=HT)(T:=T) in H27. rewrite<-H32 in H27. rewrite<-H32. apply subsum_low in H27. symmetry. apply H27. apply H34. apply H0_0.
      inversion H3. inversion H12. specialize (H16 L x). rewrite->H17 in H16. rewrite->H15 in H13. apply H16 in H13. inversion H13. simpl in H19. inversion H18. inversion H22. inversion H24. subst. inversion H26. subst.
      apply subsum_r_trans with (a:=joins PC b0)(b:=labelT T)(c:=label (efst (heap_lookup x hp))). assert (subsum_r (joins PC b0)(labelT T)). apply subsum_r_trans with (a:=joins PC b0)(b:=joins pc b0)(c:=labelT T). apply joins_subtyping_1. apply H2. apply subsum_r_trans with (a:=joins pc b0)(b:=joins pc b)(c:=labelT T). apply joins_subtyping_2. 
      apply subsum_r_trans with (a:=b0)(b:=x2)(c:=b). apply H14. inversion H20. apply H23. apply H1. apply H21.
      apply subsum_r_trans with (a:=labelT T)(b:=labelT (esnd (heap_lookup x hp)))(c:=label (efst (heap_lookup x hp))). inversion H20. simpl in H21. apply subtyping_subsum in H21. apply H21. apply H13. reflexivity. reflexivity. reflexivity. reflexivity.
*)
      inversion H6. destruct x. exists (tassign t1 t,h). apply st_assign2.
      inversion H3. apply H9. 
      apply well_typed_well_formed with (hp:=hp) in H0_. apply H0_. apply H3. apply well_typed_well_formed with (hp:=hp) in H0_0. apply H0_0. apply H3.
      apply H5. apply H7. inversion H5. destruct x.
      exists (tassign t t2,h). apply st_assign1.
      inversion H3. apply H8.
      apply well_typed_well_formed with (hp:=hp) in H0_. apply H0_. apply H3. apply well_typed_well_formed with (hp:=hp) in H0_0. apply H0_0. apply H3.
      apply H6. reflexivity. apply H2. reflexivity. apply H2.
Case ("t_sub").
      intros. assert (subsum_r PC pc). apply subsum_r_trans with (a:=PC)(b:=pc')(c:=pc). apply H3. apply H1.
      apply IHhas_type with (PC:=PC)in H4. apply H4. apply Heqcontext. apply H5. 
Qed.

(*##########determinism#########*)
Theorem determinism: forall t t' t'' hp hp' hp'' PC,
t / hp ==PC=> t' / hp'  ->
t / hp ==PC=> t'' / hp'' ->
(t' = t''/\hp' = hp'').
Proof. intros t. induction t.
Case ("tvar").
             intros. inversion H0.
Case ("tprot").
             intros. inversion H0. subst.  inversion H1. subst.
             apply IHt with (t':=t'0)(t'':=t')(hp'':=hp'')in H10. inversion H10. subst.
             split. reflexivity. reflexivity. apply H13. subst. inversion H13. subst. inversion H10.
             subst. inversion H10. subst. inversion H10. subst. inversion H10. subst. inversion H1. subst.
             inversion H10. subst. inversion H13. subst. inversion H13. subst. inversion H13. subst. inversion H13.
             subst. split. reflexivity. reflexivity.
Case ("tcon").
             intros. inversion H0.
Case ("tabs"). 
             intros. inversion H0.
Case ("tapp"). 
             intros. inversion H0. inversion H1. subst. inversion H12. subst. split.
             reflexivity. reflexivity. subst. inversion H21. subst. inversion H11. subst. inversion H22.
             subst. inversion H22. subst. inversion H22. subst. inversion H22. subst. inversion H1. subst.
             inversion H11. subst.
             apply IHt1 with (t':=t1')(t'':=t1'0)(hp'':=hp'') in H11. inversion H11. subst. split. reflexivity.
             reflexivity. apply H15. subst. inversion H15. subst. inversion H11. subst. inversion H11. subst. inversion H11.
             subst. inversion H11. subst. inversion H1. subst. inversion H16. subst. inversion H12. subst. inversion H12.
             subst. inversion H12. subst. inversion H12. subst. inversion H11. subst. inversion H16. subst. inversion H16.
             subst. inversion H16. subst. inversion H16. subst. 
             apply IHt2 with (t':=t2')(t'':=t2'0)(hp'':=hp'')in H12. inversion H12. subst. split. reflexivity. reflexivity.
             apply H17.
Case ("tunit").
             intros. inversion H0.
Case ("tref").
             intros. inversion H0. subst. inversion H1. subst.  split. reflexivity. reflexivity. subst. inversion H10. subst.
             inversion H14. subst. inversion H14. subst. inversion H14. subst. inversion H14. subst. inversion H1. subst. inversion H13. subst.
             inversion H11. subst. inversion H11. subst. inversion H11. subst. inversion H11. subst. specialize (IHt t'0 t' hp hp' hp''). apply IHt in H14.
             inversion H14. subst. split. reflexivity. reflexivity. apply H11.           
Case ("tderef").
             intros. inversion H0. inversion H1. subst. inversion H10. subst. split. reflexivity. reflexivity. subst. inversion H17. subst. inversion H1. subst.
             inversion H9. subst. apply IHt with (t':=t'0)(t'':=t')(hp'':=hp'') in H9. inversion H9. subst. split. reflexivity. reflexivity. apply H12.
Case ("tloc").
             intros. inversion H0.
Case ("tassign"). 
             intros. inversion H0. subst. inversion H1. subst. split. reflexivity. reflexivity. subst. inversion H17. subst. inversion H10. subst. inversion H18. subst. inversion H18.
             subst. inversion H18. subst. inversion H18.  subst. inversion H1. subst. inversion H11. subst.            
             specialize (IHt1 t1' t1'0 hp hp' hp'' PC). apply IHt1 in H11. inversion H11. subst.
             split. reflexivity. reflexivity. apply H15. subst. inversion H15. subst. inversion H11. subst. inversion H11. subst. inversion H11. subst. inversion H11. subst. inversion H1. subst.
             inversion H15. subst. inversion H12. subst. inversion H12. subst. inversion H12. subst. inversion H12. subst. inversion H11. subst. inversion H16. subst. inversion H16. subst. inversion H16.
             subst. inversion H14. subst. inversion H16. subst. specialize (IHt2 t2' t2'0 hp hp' hp'' PC). apply IHt2 in H12. inversion H12. subst. split. reflexivity. reflexivity. apply H17.
Qed.
(*############soundness############*)
Corollary soundness : forall pc PC HT p p' T,
  has_type pc empty_context HT (fst p) T ->  
  heap_well_typed HT (snd p) ->
  Multistep p PC p' ->
  subsum_r PC pc ->
 ~((~exists p'', step p' PC p'')/\(~ value (fst p'))).
Proof.
intros. remember (@empty_context) as context. generalize dependent pc. generalize dependent HT.  
generalize dependent T. induction H2.
Case ("multi_refl").
     intros. subst. intros contra. inversion contra.
     apply progress with (PC:=b)(hp:=snd x) in H0. inversion H0.
     SCase ("left"). apply H4 in H5. inversion H5.
     SCase ("right"). destruct x. apply H2 in H5. inversion H5. apply H1. apply H3.
Case ("multi_step"). subst. intros. apply preservation with (PC:=b)(t':=fst y)(hp:=snd x)(hp':=snd y)in H3.
     inversion H3. inversion H5. inversion H7. apply IHMulti with (T:=T)(pc:=pc) in H9. apply H9. apply H8.
     apply H4. apply H1. destruct x. destruct y. apply H0. apply H4.
Qed.
  
End SecLang.


Module LowLang.
(*syntax*)
Inductive tm : Type :=
| tvar  : id -> tm 
(*| tprot : Sec -> tm -> tm*)
| tcon  : nat -> tm
| tabs  : id -> Ty -> tm -> tm
| tapp  : tm -> tm -> tm
(*#####new terms######*)
| tunit   : tm
| tref    : Ty -> tm -> tm (*[Ty] as the initial type*)
| tderef  : tm -> tm
| tloc    : Ty -> option nat -> tm(*[Ty] as the "access type"*)
| tassign : tm -> tm -> tm
(*####one additional terms meant to be typed with high security####*)
| tH      : tm.
(**
Note that there is no [tprot] in [LowLang]. For the projection of a
term protected by [H] is always [tH] while the projection of terms 
protected by [L] is just that of themselves
*)
(**
Also note that the referred location in [tloc] is typed as [option nat] where
we use [None] indicating a pointer to a high value on the heap in [SecLang] while
[Some n] indicating a pointer to a low value on the projected heap given that [n]
is smaller than the length of the projected heap
*)

(*well-formed term in [LowLang]*)
(*well formed expressions*)
(**
Here,a term is well-formed given a natural number which stands for 
the length of the heap in [SecLang]
*)
Inductive well_formed : tm -> nat -> Prop :=
  | wf_tvar:forall (x:id)(hp:nat),
         well_formed (tvar x) hp 
  | wf_tcon:forall (n:nat)(hp:nat),
         well_formed (tcon n) hp
  | wf_tunit:forall (hp:nat),
         well_formed tunit hp
  | wf_tloc:forall (T:Ty)(n:nat)(hp:nat),
         n < hp ->
         well_formed (tloc T (Some n)) hp
  | wf_tabs:forall x T e hp,
         well_formed e hp ->
         well_formed (tabs x T e) hp
  | wf_tapp:forall t1 t2 hp,
         well_formed t1 hp ->
         well_formed t2 hp ->
         well_formed (tapp t1 t2) hp
  | wf_tref:forall (T:Ty) (e:tm) (hp:nat),
         well_formed e hp ->
         well_formed (tref T e) hp
  | wf_tderef:forall e hp,
         well_formed e hp ->
         well_formed (tderef e) hp
  | wf_tassign:forall t1 t2 hp,
         well_formed t1 hp ->
         well_formed t2 hp ->
         well_formed (tassign t1 t2) hp
  | wf_tH:forall hp,
         well_formed tH hp.

(*value*)
Inductive value : tm -> Prop :=
| v_c : forall n,
        value (tcon n)
| v_f : forall n T e,
        value (tabs (Id n) T e)
| v_u : value  tunit
| v_l : forall N T,
        value (tloc T N)
| v_H : value tH
.

(*heap*)
Definition heap := list (tm*Ty).
Definition emp_hp:= @nil (tm*Ty).
(*some useful functions*)
(*###lookup function and some lemmas###*)
Fixpoint heap_lookup (n:nat)(st:heap):(option (tm*Ty)):=
  match st , n with
  | nil , _ =>None
  | h::t , 0 => Some h
  | h::t , S n' =>heap_lookup n' t
  end.

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

(*substitution*)
Fixpoint subst (x:id) (s:tm) (t:tm): tm :=
  match t with
(*variables*)
  | tvar x' => 
      if beq_id x x' then s  else t
(*abstractions*)
  | tabs x' T t1 => 
      tabs x' T (if beq_id x x' then t1 else (subst x s t1))
(*constants*)
  | tcon n => tcon n 
(*applications*)
  | tapp t1 t2 => 
      tapp (subst x s t1) (subst x s t2)
(*units*)
  | tunit => tunit
(*tref*)
  | tref T t1 => tref T (subst x s t1)
(*tderef*)
  | tderef t1 => tderef (subst x s t1)
(*tloc*)
  | tloc T N => tloc T N 
(*assignments*)
  | tassign t1 t2 => tassign (subst x s t1)(subst x s t2)
(*high value*)
  | tH => tH
  end.
Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

Definition labelT (T:Ty) : Sec:=
match T with
 | an rt b => b
end.

Reserved Notation "t1 '/' hp '==' PC '=>' t2 '/' hp'"
  (at level 40, hp at level 39, t2 at level 39, PC at level 39).

(**
Note currently all terms are without any security labels and as will be 
specified below in the type relation all terms except [tH] can be typed 
as low and high while [tH] can only be typed as low.
*)
(**
Regarding the reduction relation,
a. application
In [LowLang], we preserve both [st_app1] [st_app2] and [st_appabs] to deal with
cases where either of the subterms of the application are reducible or the first
term of the application which is a low abstraction is applied to a value. In addition,
we have [st_apptH] to deal with cases where a high abstraction is being applied to
a value. In such cases,since the result is always being protected by [H] we should 
have it as follows,
[st_apptH]:forall v PC hp,
value v ->
tapp tH v / hp ==PC=> tH / hp
b. reference
in [LowLang], we preserve both [st_ref] and [st_refv] to deal with cases where either the
subterm is reducible or the subterm is a low value and both the label of the referred
tpye and PC have to be low for the new cell being written onto the heap is being 
protected by both [labelT T] and [PC] and after reduction the heap is extended by
the pair of the guarded low value and the referred type. In addtion we also have
 to deal with cases where a high value actually gets written onto the heap either
because the value itself is [tH] or the join of [PC] and [labelT T] is [H]. In such
cases, the heaps before and after the reduction are the same while we replace the
referred location to [None] to signal the fact that in [LowLang],all
high values in a heap are referred to via [None] which is the default value of the referred 
location.
[st_reftH]:forall v PC T hp,
value v ->
v = tH \/ PC = H \/ LabelT T = H ->
tref T v / hp ==PC=> tloc T None / hp

Note that we only consider three cases of assignment in [LowLang],
1. a high cell is being over-written by a high value
2. a low cell is being over-written by a low value
It should be noted that we do not deal with cases where a high cell is being over-written
by a low value and a low cell is being over-written by a high value. Such cases are ruled out by explicitly prohibiting any upgrading 
and downgrading in [SecLang]

c. dereference
as illustrated in [b.],the ways how we write a low value and a high value are 
different in that the low cell being written onto the heap is always referred 
to via a location which is within range while all high values are actually not
being written onto the heap for in [LowLang] we want to abstract away all high
level side-effect. Instead, we rewrite the referred location as [None] so as to 
signal cases where high value is being written onto the heap.
Hence we should have the following reduction rules besides [st_deref] where the 
subterm is reducible,
[st_derefloc]:forall n hp T hp PC,
n < length hp ->
v = efst (heap_lookup n hp) ->
tderef (tloc T (Some n)) / hp ==PC=> v / hp  

[st_derefloctH]:
tderef (tloc T None) / hp ==PC=> tH / hp

the case where the subterm is [tH] is simple for it must
correspond to the dereference of a high location in [SecLang] where the
result of the reduction is protected by [H] the projection of which is [tH],
[st_dereftH]:
tderef tH / hp ==PC=> tH / hp
d. assignment
the reduction rule in cases where each of its subterms is reducible is not different
from [st_assign1] and [st_assign2] in [SecLang]. Now in regard with cases where 
a cell on the heap is being over-written by some value it is not necessary for us
to deal with cases where either a high cell is being over-written by a low value or
a low cell is being over-written by a high value. They are ruled out by prohibiting any
upgrading and downgrading in [SecLang].

Now in [LowLang],we only need to consider two cases of assignment,
a. a low cell is being over-written by a low value
[st_assign]:forall n hp v T PC 
n < length hp ->
value v ->
v <> tH ->
PC = labelT T = L ->
hp'=heap_replace n (v,T) hp ->
tassign ((tloc T )(Some n)) v / hp ==PC=>tunit / hp'

b. a high cell is being over-written by a high value
   when security context is low
[st_assigntH_L]:forall hp v T PC hp,
value v ->
v = tH \/ labelT T = H ->
PC = L ->
tassign (tloc T None) v / hp ==PC=> tunit / hp

c. a high cell is being over-written by a high value
   when security context is high
[st_assigntH_H]:forall n hp v PC T hp,
n = length hp ->
value v ->
PC = H ->
tassign (tloc T None) v / hp ==PC=> tH / hp

the case where the pointer through which heap cell is updated is high would 
mean either over-writing a low cell with a high value or a high cell with a 
high value where the former case bring us difficulty for the projection of
a high pointer according to our projection function destroys all info. regarding
the location of the relevent low cell which we would like to get rid of through
projection. Yet,we need not consider this case for condition that the cell being
over-written must be guarded by the joint of [PC] and the label of the pointer for
the reduction to proceed. Then we have,
[st_assignHP]:forall
value v ->
tassign tH v / hp ==PC=> tH / hp
*)

Inductive step : tm * heap -> Sec -> tm * heap -> Prop :=
  | st_appabs: forall x T e PC hp v,
         value v ->
         tapp (tabs x T e) v / hp == PC => [x := v]e / hp
 
  | st_app1: forall t1 t1' t2  PC hp hp',
         t1 / hp == PC => t1' / hp' ->
         tapp t1 t2 / hp == PC => tapp t1' t2 / hp'
  | st_app2: forall v1 t2 t2' PC hp hp',
         value v1 ->
         t2 / hp == PC => t2' / hp' ->
         tapp v1 t2 / hp == PC => tapp v1 t2' / hp'
 (*application were a high abstraction is being applied*)
  | st_apptH:forall v hp PC,
         value v ->
         tapp tH v / hp ==PC=> tH / hp
 (*writing a new low cell*)
  | st_refv: forall T v PC hp hp',
         value v ->
         v <> tH ->
         labelT T = L ->
         PC = L ->
         hp' = snoc hp (v,T) ->
         tref T v / hp == PC => tloc T (Some (length hp)) / hp'
 (*writing a new high cell*)
  | st_reftH:forall v PC T hp,
         value v ->
         v = tH \/ PC = H \/ labelT T = H ->
         tref T v / hp ==PC=> tloc T None / hp
  | st_ref: forall T t t' PC hp hp',
          t / hp == PC => t' / hp' ->
          tref T t / hp == PC => tref T t' / hp'
  (*dereferencing a low cell on the heap*)
  | st_derefloc: forall T n PC hp v,
          n < length hp ->
          v = efst (heap_lookup n hp) ->
          tderef (tloc T (Some n)) / hp == PC => v / hp
  (*dereferencing a high cell on the heap*)
  | st_derefloctH:forall hp T PC,
          tderef (tloc T None) / hp == PC => tH / hp
  | st_deref: forall t t' hp hp' PC,
          t / hp == PC => t' / hp' ->
          tderef t / hp == PC => tderef t' / hp'
  (*dereferencing a high loction*)
  | st_dereftH:forall hp PC,
          tderef tH / hp ==PC=> tH / hp
  (*low cell is being over-written by a low value*)
  | st_assign: forall v T n PC hp hp',
          n < length hp -> (* heap_lookup n hp = some e'*)
          value v ->
          v <> tH ->
          PC = L /\ labelT T = L ->
          hp' = heap_replace n (v,T) hp ->
          tassign (tloc T (Some n)) v / hp == PC => tunit / hp'
  (*high cell is being over-written by a high value when [PC] is L*)
  | st_assigntH_L:forall hp v PC T,
          value v ->
          PC = L ->
          v = tH \/ labelT T = H ->
          tassign (tloc T None) v / hp ==PC=> tunit / hp
  (*high cell is being over-written by a high value when [PC] is H*)
  | st_assigntH_H:forall hp v PC T,
          value v ->
          PC = H ->
          tassign (tloc T None) v / hp ==PC=> tH / hp
  (*a high pointer*)
  | st_assignHP:forall v hp PC,
          value v ->
          tassign tH v / hp ==PC=> tH / hp
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

Theorem multi_trans:forall t t' t'' hp hp' hp'' pc,
      Multistep (t,hp) pc (t',hp')  ->
      Multistep (t',hp') pc (t'',hp'') ->
      Multistep (t,hp) pc (t'',hp'').
Proof.
intros. induction H0. apply H1. apply IHMulti in H1.
apply Multi_step with y. apply H0. apply H1.
Qed.

(*some reduction samples*)
Example test_step_1:forall hp PC,
tapp tH (tcon 0) / hp ==PC=> tH / hp.
Proof. intros. apply st_apptH. apply v_c. Qed.
Example test_step_2:forall PC hp,
tref (an int L) tH / hp ==PC=>tloc (an int L) None / hp.
Proof. intros. apply st_reftH. apply v_H. left. reflexivity. Qed.
Example test_step_3:forall hp,
tref (an int L)(tcon 0) / hp ==L=> tloc (an int L) (Some (length hp)) / snoc hp (tcon 0,an int L).
Proof. intros. apply st_refv. apply v_c. intros contra. inversion contra. reflexivity. reflexivity.
reflexivity. Qed.
Example test_step_4:forall PC,
tderef (tloc (an int H) (Some 0)) / ((tcon 0,an int H) :: nil)
==PC=>
tcon 0 / ((tcon 0,an int H) :: nil).
Proof. intros. apply st_derefloc. apply le_n. reflexivity. Qed.
Example test_step_5:forall hp PC,
tderef (tloc (an int H) None) / hp
==PC=>
tH / hp.
Proof.  intros. apply st_derefloctH. Qed.
Example test_step_6:forall hp PC,
tderef tH / hp ==PC=> tH / hp.
Proof. apply st_dereftH. Qed.
Example test_step_7:
tassign (tloc (an int L) (Some 0))(tcon 1) / ((tcon 0,an int L) :: nil)
==L=>
tunit / ((tcon 1,an int L) :: nil).
Proof. apply st_assign. apply le_n. apply v_c. intros contra. inversion contra.
split. reflexivity. reflexivity. reflexivity. Qed.
Example test_step_8:forall hp,
tassign (tloc (an int L) None) tH / hp
==L=>
tunit / hp.
Proof. intros. apply st_assigntH_L. apply v_H. reflexivity. left.
reflexivity. Qed.
Example test_step_9:forall hp,
tassign (tloc (an int H) None) (tcon 1) / hp
==L=>
tunit / hp.
Proof. intros. apply st_assigntH_L.  apply v_c. reflexivity. right.
reflexivity. Qed.
Example test_step_10:forall hp,
tassign (tloc (an int L) None)(tcon 1) / hp
==H=>
tH / hp.
Proof. intros. apply st_assigntH_H. apply v_c. reflexivity. Qed.
Example test_step_11:forall hp PC,
tassign tH (tcon 1) / hp ==PC=> tH / hp.
Proof. intros. apply st_assignHP. apply v_c. Qed.
Example test_step_12:forall hp,
tapp (tassign (tloc (an int L) None)(tcon 1))(tderef (tloc (an int H) None)) / hp
==H=>*
tH / hp.
Proof. intros.
apply Multi_step with (y:=(tapp tH (tderef (tloc (an int H) None)),hp)). 
apply st_app1. apply st_assigntH_H. apply v_c. reflexivity.
apply Multi_step with (y:=(tapp tH tH,hp)). 
apply st_app2. apply v_H. apply st_derefloctH. 
apply Multi_step with (y:=(tH,hp)).
apply st_apptH. apply v_H. 
apply Multi_refl.
Qed.
Example test_step_13:forall PC hp,
tref (an int H)(tapp tH (tcon 0)) / hp
==PC=>*
tloc (an int H) None / hp.
Proof. intros.
apply Multi_step with (y:=(tref (an int H)(tH),hp)). 
apply st_ref. apply st_apptH. apply v_c. 
apply Multi_step with (y:=(tloc (an int H) None,hp)).
apply st_reftH. apply v_H. left. reflexivity.
apply Multi_refl.
Qed.
Example test_step_14:forall hp,
tderef (tref (an int L)(tcon 0)) / hp
==H=>*
tH / hp.
Proof. intros.
apply Multi_step with (y:=(tderef (tloc (an int L) None),hp)).
apply st_deref. apply st_reftH. apply v_c. right. left. reflexivity.
apply Multi_step with (y:=(tH,hp)).
apply st_derefloctH. apply Multi_refl.
Qed.
Example test_step_15:forall hp,
tassign (tref (an int L) tH)(tapp tH (tcon 0)) / hp
==L=>*
tunit / hp.
Proof. intros.
apply Multi_step with (y:=(tassign(tloc (an int L) None)(tapp tH (tcon 0)),hp)).
apply st_assign1. apply st_reftH. apply v_H. left. reflexivity.
apply Multi_step with (y:=(tassign (tloc (an int L) None) tH,hp)).
apply st_assign2. apply v_l. apply st_apptH. apply v_c.
apply Multi_step with (y:=(tunit,hp)).
apply st_assigntH_L. apply v_H. reflexivity. left. reflexivity.
apply Multi_refl.
Qed.

(**
Note we might thought that in [LowLang],the securtiy context can be freely modified
if we know that some configuration is reducible under some security context.
This is,however,not the case. Consider the following reduction under high
security context where a high cell is being over-written by a high value,
tassign (tloc (an int L) None)(tcon 1) / hp
==H=>
tH / hp.
If we change the security context to low, we suddenly have a stuck configuration,
tassign (tloc (an int L) None)(tcon 1) / hp ==L=> ?.
Now how about the other way round, can we argue that if a configuration is reducible
under low security context is also reducible under high security context?
The answer is still no.
Consider the following example where a low cell is being over-written by a low value,
tassign (tloc (an int L) (Some n))(tcon 1) 
==L=>
tunit / heap_replace n (tcon 1,an int L) hp,where n < length hp.
Now if we change the security context to H then we get a stuck term,
tassign (tloc (an int L) (Some n))(tcon 1)
==H=>?.
In conclusion, since in [LowLang] we donot care for the cases where either a low
cell is being over-written by a high value or a high cell is being written by a
low value,the security context is not allowed to be changed at all even though we
have on our hands a reducible configuration under some security context.
*)
(*some stuck terms in [LowLang]*)
Definition stuck_term (s:tm) (hp:heap) (PC:Sec) : Prop :=
 (~exists e', step (s,hp) PC e') /\ (~value s).
Lemma lt_same_F' : forall n m,
S n <= S m -> n <= m.
Proof. intros. generalize dependent n. induction m.
intros. destruct n. apply le_n. inversion H0. inversion H2.
intros. inversion H0. apply le_n. apply le_S. apply IHm in H2.
apply H2. Qed.
Lemma lt_same_F:forall n,
n < n -> False.
Proof. intros. induction n. inversion H0. unfold lt in H0. unfold lt in IHn.
apply lt_same_F' in H0. apply IHn in H0. inversion H0. Qed.
Example test_stuck_term_1:forall hp,
stuck_term (tassign (tloc (an int L) None)(tcon 1)) hp L.
Proof. intros. split. intros contra. inversion contra. inversion H0. 
       subst. inversion H0. subst. inversion H10. inversion H1. inversion H1.
       subst. inversion H7. inversion H6. inversion H7. intros contra. inversion contra.
Qed.
      
Lemma test_stuck_term_2':forall {A:Type} (hp:list A),
hp <> hp -> False.
Proof. intros.  apply H0. reflexivity.
Qed. 
Example test_stuck_term_2:forall hp,
hp <> nil ->
stuck_term (tassign (tloc (an int L) (Some 0))(tcon 1)) hp H.
Proof. intros. split. intros contra. inversion contra. inversion H1.
       inversion H11. inversion H13. inversion H7. inversion H8.
       intros contra. inversion contra.
Qed. 
Lemma not_equal_nat:forall (n:nat),
n <> n -> False.
Proof. intros.  assert (n=n). reflexivity. apply H0 in H1.
inversion H1.
Qed.

(*typing rule*)
(*some auxiliary functions*)
Definition joinTs (T:Ty)(b:Sec) : Ty :=
 match T , b with
 | an rt s , L => an rt s
 | an rt s , H => an rt H
 end.
Definition joins (b1:Sec) (b2:Sec): Sec :=
 match b1 with
 | L => b2
 | H => H
 end.
(*typing relation*)
(**
Regarding the typing relation in [LowLang],all terms except for [tH] can be 
typed with both low and high security level while [tH] can only be typed with
high security level. The typing relation itself is similar to that in [SecLang]
which consists of the programme counter,pc,the tying context,Gamma,the heap typing
,HT,the term,and the related type.
There are three  cases needed discussion,

a. [t_H]
[tH] can be typed under all [pc],[Gamma],[HT],and [rt] as follows,
has_type pc Gamma HT tH (an rt H)

b. [t_loc]
Recall that in [LowLang] we only store low terms in the heap,hp,whose address,n,
satisfies that [n < length hp] while all high terms in the heap are indicated via
their address as [None]. Since the heap_typing,HT,should correspond to
the heap,hp,in a consistent way,when we type location,[tloc T N],we should consider
both reference to low terms where the referred loction is smaller than the length
of the heap_typing and high terms where the referred location is simply [None],
b.1. [t_loc_L]:forall n HT T pc Gamma,
n < length HT ->
heap_Tlookup n HT = Some T ->
has_type pc Gamma HT (tloc T (Some n))(an (ref T) L)

b.2. [t_loc_H]:forall pc Gamma HT rt,
has_type pc Gamma HT (tloc (an rt H) None)(an (ref (an rt H)) L)


c. [t_ref]
Recall the typing rule for allocation in [SecLang],the label of the allocation joined
with the programme counter must be smaller than the label of the referred type.
Such restriction still applies when we try to type allocation in [LowLang],
where the label of the allocation joined by [pc] has to be smaller than the label of 
the referred type,
forall pc Gamma HT t T,
has_type pc Gamma HT t T ->
subsum_r pc (labelT T) ->
has_type pc Gamma HT (tref T t)(an (ref T) L)
*)
Inductive has_type : Sec -> context -> heap_Ty -> tm -> Ty -> Prop :=
  | t_var : forall pc Gamma HT x T,
      Gamma x = Some T ->
      has_type pc Gamma HT (tvar x) T
  | t_con : forall pc Gamma HT n,
      has_type pc Gamma HT (tcon n) (an int L)
  | t_unit: forall pc Gamma HT,
      has_type pc Gamma HT tunit (an unit L)
(*special case*)
  | t_H:forall pc Gamma HT rt,
      has_type pc Gamma HT tH (an rt H)
(*special case*)
  | t_loc_L:forall n HT T pc Gamma,
      heap_Tlookup n HT = Some T ->
      has_type pc Gamma HT (tloc T (Some n))(an (ref T) L)
  | t_loc_H:forall pc Gamma HT rt,
      has_type pc Gamma HT (tloc (an rt H) None) (an (ref (an rt H)) L)
 
  | t_abs: forall pc pc' Gamma HT x T e T',
    has_type pc' (Cupdate Gamma x (Some T)) HT e T' ->
    has_type pc Gamma HT (tabs x T e) (an (fn T pc' T') L)

 
  | t_app: forall pc Gamma HT T1 T2 T2' b t1 t2,
  has_type pc Gamma HT t1 (an (fn T1 (joins pc b) T2) b) ->
  has_type pc Gamma HT t2 T1 ->
  joinTs T2 b = T2' ->
  has_type pc Gamma HT (tapp t1 t2) T2'
 (*special case*)
  | t_ref: forall pc Gamma HT t T,
    has_type pc Gamma HT t T ->
    subsum_r pc (labelT T) ->
    has_type pc Gamma HT (tref T t) (an (ref T) L)
  | t_deref: forall pc Gamma HT t T T' b,
    has_type pc Gamma HT t (an (ref T) b) ->
    T' = joinTs T b ->
    has_type pc Gamma HT (tderef t) T'
 | t_assign: forall pc Gamma HT t1 t2 b b' T,
   b' = labelT T ->
   subsum_r (joins pc b) b' ->
   has_type pc Gamma HT t1 (an (ref T) b) ->
   has_type pc Gamma HT t2 T ->
   has_type pc Gamma HT (tassign t1 t2) (an unit b')
 | t_sub: forall pc pc' Gamma HT t T T',
   has_type pc Gamma HT t T ->
   subsum_r pc' pc ->
   T <: T' ->
   has_type pc' Gamma HT t T'
.

(*some examples*)

Example has_type_1:forall pc Gamma HT,
has_type pc Gamma HT tH (an int H).
Proof. intros. apply t_H. Qed.
Example has_type_2:forall pc Gamma HT,
has_type pc Gamma HT tH (an unit H).
Proof. intros. apply t_H. Qed.
Example has_type_3:forall pc Gamma HT,
has_type pc Gamma HT tH (an (ref (an int L)) H).
Proof. intros. apply t_H. Qed.
Example has_type_4:forall pc Gamma HT,
has_type pc Gamma HT tH (an (fn (an int L) L (an unit H)) H).
Proof. intros. apply t_H. Qed.
Example has_type_5:forall pc HT,
has_type pc (Cupdate empty_context (Id 0) (Some(an int H))) HT
            (tvar (Id 0))
            (an int H).
Proof. intros. apply t_var. rewrite->Cupdate_eq. reflexivity. Qed.
Example has_type_6:forall pc Gamma HT n,
has_type pc Gamma HT (tcon n) (an int H).
Proof. intros. apply t_sub with (pc:=pc)(T:=an int L). apply t_con.
apply sub_refl. apply subt_int. apply sub_LH. Qed.
Example has_type_7:forall pc Gamma HT,
has_type pc Gamma HT tunit (an unit H).
Proof. intros. apply t_sub with (pc:=pc)(T:=an unit L). apply t_unit.
apply sub_refl. apply subt_unit. apply sub_LH. Qed.
Example has_type_8:forall pc Gamma,
has_type pc Gamma [an int L]
         (tloc (an int L) (Some 0))
         (an (ref (an int L)) H).
Proof. intros. apply t_sub with (pc:=pc)(T:=an (ref (an int L)) L). apply t_loc_L. 
reflexivity. apply sub_refl. apply subt_ref. apply sub_LH. Qed.
Example has_type_9:forall pc Gamma rt,
has_type pc Gamma []
         (tloc (an rt H) None)
         (an (ref (an rt H)) H).
Proof. intros. apply t_sub with (pc:=pc)(T:=an (ref (an rt H)) L). apply t_loc_H.
       apply sub_refl. apply subt_ref. apply sub_LH. Qed.
Example has_type_10:forall Gamma HT,
has_type L Gamma HT
         (tref (an int H) (tcon 0))
         (an (ref (an int H)) H).
Proof. intros. apply t_sub with (pc:=L)(T:=an (ref (an int H)) L). apply t_ref.
apply t_sub with (pc:=L)(T:=an int L). apply t_con. apply sub_refl. apply subt_int. apply sub_LH.
apply sub_LH. apply sub_refl. apply subt_ref. apply sub_LH. 
Qed.
Example has_type_10':forall Gamma HT,
has_type H Gamma HT
         (tref (an int H) tH)
         (an (ref (an int H)) H).
Proof. intros. apply t_sub with (pc:=H)(T:=an (ref (an int H)) L). apply t_ref. apply t_H. apply sub_refl.
apply sub_refl. apply subt_ref. apply sub_LH.
Qed.
Example has_type_11:forall Gamma HT,
has_type L Gamma HT
         (tref (an int L)(tcon 0))
         (an (ref (an int L)) L).
Proof. intros. apply t_ref. apply t_con. apply sub_refl. 
Qed.
Example has_type_12:forall Gamma HT,
has_type L Gamma HT
         (tref (an int L)(tcon 0))
         (an (ref (an int L)) H).
Proof. intros. apply t_sub with (pc:=L)(T:=an (ref (an int L)) L). apply t_ref. apply t_con.
apply sub_refl. apply sub_refl. apply subt_ref. apply sub_LH.
Qed.
Example has_type_13:forall Gamma HT pc,
has_type pc Gamma HT
         (tabs (Id 0)(an unit H)(tref (an int H)(tcon 0)))
         (an (fn (an unit H) H (an (ref (an int H)) L)) H).
Proof. intros. apply t_sub with (pc:=pc)(T:=an (fn (an unit H) H (an (ref (an int H)) L)) L).
apply t_abs. apply t_ref. apply t_sub with (pc:=H)(T:=an int L). apply t_con.
apply sub_refl. apply subt_int. apply sub_LH. apply sub_refl. apply sub_refl.
apply subt_fn. apply sub_LH. apply sub_refl. apply subt_unit. apply sub_refl.
apply subt_ref. apply sub_refl. Qed.
Example has_type_14:forall Gamma HT,
has_type L Gamma HT
         (tapp (tabs (Id 0)(an int H)(tvar (Id 0)))(tcon 0))
         (an int H).
Proof. intros. apply t_app with (T1:=an int H)(T2:=an int H)(b:=H).
simpl. apply t_sub with (pc:=L)(T:=an (fn (an int H) H (an int H)) L).
apply t_abs. apply t_var. rewrite->Cupdate_eq. reflexivity. apply sub_refl.
apply subt_fn. apply sub_LH. apply sub_refl. apply subt_int. apply sub_refl.
apply subt_int. apply sub_refl. apply t_sub with (pc:=L)(T:=an int L). apply t_con.
apply sub_refl. apply subt_int. apply sub_LH. reflexivity. Qed.
Example has_type_15:forall Gamma HT,
has_type L Gamma HT
         (tapp (tabs (Id 0)(an int H)(tvar (Id 0)))(tcon 0))
         (an int H).
Proof. intros. apply t_app with (T1:=an int H)(T2:=an int H)(b:=L).
apply t_abs. apply t_var. rewrite->Cupdate_eq. reflexivity. apply t_sub with (pc:=L)(T:=an int L).
apply t_con. apply sub_refl. apply subt_int. apply sub_LH. reflexivity. Qed. 
Example has_type_15':forall Gamma HT,
has_type L Gamma HT
         (tapp tH (tcon 0))
         (an int H).
Proof. intros. apply t_app with (T1:=an int L)(T2:=an int L)(b:=H). apply t_H. apply t_con.
reflexivity.
Qed.
Example has_type_16:forall pc Gamma,
has_type pc Gamma [an int L]
         (tderef (tloc (an int L) (Some 0)))
         (an int H).
Proof. intros. apply t_deref with (T:=an int L)(b:=H). apply t_sub with (pc:=pc)(T:=an (ref (an int L)) L).
apply t_loc_L. reflexivity. apply sub_refl. apply subt_ref. apply sub_LH. reflexivity.
Qed.
Example has_type_17:forall pc Gamma,
has_type pc Gamma [an int L]
         (tderef (tloc (an int L) (Some 0)))
         (an int L).
Proof. intros. apply t_deref with (T:=an int L)(b:=L). apply t_loc_L. reflexivity. reflexivity.
Qed.
Example has_type_18:forall pc Gamma rt,
has_type pc Gamma []
         (tderef (tloc (an rt H) None))
         (an rt H).
Proof. intros. apply t_deref with (T:=an rt H)(b:=L). apply t_loc_H. reflexivity. 
Qed.
Example has_type_19:forall pc Gamma rt,
has_type pc Gamma []
         (tderef (tloc (an rt H) None))
         (an rt H).
Proof. intros. apply t_deref with (T:=an rt H)(b:=H). apply t_sub with (pc:=pc)(T:=an (ref (an rt H)) L).
apply t_loc_H. apply sub_refl. apply subt_ref. apply sub_LH. reflexivity.
Qed.
Example has_type_19':forall pc Gamma rt,
has_type pc Gamma []
         (tderef tH)
         (an rt H).
Proof. intros. apply t_deref with (T:=an rt L)(b:=H). apply t_H. reflexivity.
Qed.
Example has_type_20:forall Gamma HT,
has_type H Gamma HT
         (tassign (tref (an int H)(tcon 0))(tcon 1))
         (an unit H).
Proof. intros. apply t_assign with (b:=L)(T:=an int H). reflexivity. apply sub_refl.
apply t_ref. apply t_sub with (pc:=H)(T:=an int L). apply t_con. apply sub_refl.
apply subt_int. apply sub_LH. apply sub_refl. apply t_sub with (pc:=H)(T:=an int L).
apply t_con. apply sub_refl. apply subt_int. apply sub_LH. Qed.
Example has_type_21:forall Gamma HT,
has_type L Gamma HT
         (tassign (tref (an int L)(tcon 0))(tcon 1))
         (an unit L).
Proof. intros. apply t_assign with (b:=L)(T:=an int L). reflexivity. apply sub_refl.
apply t_ref. apply t_con. apply sub_refl. apply t_con.
Qed.
Example has_type_21':forall Gamma HT,
has_type L Gamma HT
         (tassign tH (tcon 1))
         (an unit H).
Proof. intros. apply t_assign with (b:=H)(T:=an int H). reflexivity. apply sub_refl. apply t_H.
apply t_sub with (pc:=L)(T:=an int L). apply t_con. apply sub_refl. apply subt_int. apply sub_LH.
Qed.


(*###inversion of [has_type]###*)
(*inversion of [has_type pc Gamma HT tH T]*)
Lemma inversion_tH:forall pc Gamma HT T,
has_type pc Gamma HT tH T ->
exists rt,
(an rt H) <: T.
Proof. intros. remember tH as t. induction H0. inversion Heqt. inversion Heqt. inversion Heqt.
exists rt. destruct rt. apply subt_int. apply sub_refl. apply subt_fn. apply sub_refl. apply sub_refl.
apply subtyping_refl. apply subtyping_refl. apply subt_unit. apply sub_refl. apply subt_ref. apply sub_refl.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt.
apply IHhas_type in Heqt. inversion Heqt. exists x. apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl.
apply H3. apply H2. 
Qed.

(*inversion of [has_type pc Gamma HT (tvar x) T]*)
Lemma inversion_tvar: forall pc Gamma HT x T,
has_type pc Gamma HT (tvar x) T ->
exists T0, (Gamma x = Some T0)/\(T0 <: T).
Proof. intros. remember (tvar x) as t. induction H0.
inversion Heqt. subst. exists T. split. apply H0. apply subtyping_refl.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt.
apply IHhas_type in Heqt. inversion Heqt. exists x0. split. inversion H3.
apply H4. inversion H3. apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl.
apply H5. apply H2.
Qed.

(*inversion of [has_type pc Gamma HT (tabs x T1 e b) T]*)
Lemma inversion_tabs: forall pc Gamma HT x T1 T e,
has_type pc Gamma HT (tabs x T1 e) T ->
exists T1', exists T2, exists T2', exists pc', exists pc'', exists pc''', exists b,
(has_type pc' Gamma HT (tabs x T1 e) (an (fn T1 pc'' T2) L)) /\
(has_type pc'' (Cupdate Gamma x (Some T1)) HT e T2) /\(subsum_r pc''' pc'')/\(subsum_r pc pc')/\
(T1'<:T1)/\(T2<:T2')/\(subsum_r L b)/\((an (fn T1' pc''' T2') b) <: T).
Proof. intros. remember (tabs x T1 e) as t. induction H0. inversion Heqt. inversion Heqt. inversion Heqt.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. subst.
exists T1. exists T'. exists T'. exists pc. exists pc'. exists pc'. exists L. split. apply t_abs. apply H0.
split. apply H0. split. apply sub_refl. split. apply sub_refl. split. apply subtyping_refl. split. apply subtyping_refl.
split. apply sub_refl. apply subt_fn. apply sub_refl. apply sub_refl. apply subtyping_refl. apply subtyping_refl.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. apply IHhas_type in Heqt. inversion Heqt. exists x0.
inversion H4. exists x1. inversion H5. exists x2. inversion H6. exists x3. inversion H7. exists x4. inversion H8. exists x5. inversion H9.
exists x6. split. apply t_abs. apply H10. split. apply H10. split. apply H10. split. apply subsum_r_trans with (a:=pc')(b:=pc)(c:=x3).
apply H1. apply H10. split. apply H10. split. apply H10. split. apply H10. apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl.
apply H10. apply H2. 
Qed.

(*inversion of [has_type pc Gamma HT (tcon n b) T]*)
Lemma inversion_tcon: forall pc Gamma HT T n,
has_type pc Gamma HT (tcon n) T ->
exists T', exists T'', exists b, 
(T' = an int L)/\(T'' = an int b)/\(subsum_r L b)/\(T'' <: T).
Proof. 
 intros. remember (tcon n) as t. induction H0.
inversion Heqt. inversion Heqt. subst. exists (an int L). exists (an int L).
exists L. split. reflexivity. split. reflexivity. split. apply sub_refl.
apply subt_int. apply sub_refl. inversion Heqt. inversion Heqt. inversion Heqt.
inversion Heqt.  inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt.
inversion Heqt.
apply IHhas_type in Heqt. inversion Heqt. exists x. inversion H3.
exists x0. inversion H4. exists x1. split. apply H5. split. apply H5. split. apply H5.
apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl. apply H5. apply H2.
Qed.

(*inversion of [has_type pc Gamma HT (tunit b) T]*)
Lemma inversion_tunit:forall pc Gamma HT T,
has_type pc Gamma HT tunit T ->
exists T', exists T'', exists b,
(T'=an unit L)/\(T''=an unit b)/\(subsum_r L b)/\(T''<:T).
Proof. intros. remember tunit as t. induction H0. inversion Heqt. inversion Heqt. 
exists (an unit L). exists (an unit L). exists L. split. reflexivity. split. reflexivity. split.
apply sub_refl. apply subt_unit. apply sub_refl. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt.
apply IHhas_type in Heqt. inversion Heqt. exists x. inversion H3.
exists x0. inversion H4. exists x1. split. apply H5. split. apply H5. split. apply H5. apply subtyping_trans with (x:=T)(y:=T).
apply subtyping_refl. apply H5. apply H2. 
Qed.

(**
inversion of [has_type pc Gamma HT (tloc T (Some n)) T'] 
where n <= length HT
*)
Lemma inversion_tloc_L:forall pc Gamma HT n T1 T,
has_type pc Gamma HT (tloc T1 (Some n)) T ->
exists T', exists T'', exists b,
(heap_Tlookup n HT = Some T1)/\(T'=an (ref T1) L)/\(T''=an (ref T1) b)/\(subsum_r L b)/\(T''<:T).
Proof. intros. remember (tloc T1 (Some n)) as t. induction H0. inversion Heqt. inversion Heqt. inversion Heqt.
inversion Heqt. inversion Heqt. subst. exists (an (ref T1) L). exists (an (ref T1) L). exists L. split.
apply H0. split. reflexivity. split. reflexivity. split. apply sub_refl. apply subtyping_refl.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. apply IHhas_type in Heqt. inversion Heqt.
exists x. inversion H3. exists x0. inversion H4. exists x1. split. apply H5. split. apply H5. split. apply H5. split. apply H5.
apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl. apply H5. apply H2. 
Qed.

(*inversion of [has_type pc Gamma HT (tloc T None) T']*)
Lemma inversion_tloc_H:forall pc Gamma HT T1 T,
has_type pc Gamma HT (tloc T1 None) T ->
exists T', exists T'', exists b, exists rt,
(T1=an rt H)/\
(T'=an (ref (an rt H)) L)/\(T''=an (ref (an rt H)) b)/\(subsum_r L b)/\(T''<:T).
Proof. intros. remember (tloc T1 None) as t.  induction H0. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt.
inversion Heqt. subst. exists (an (ref (an rt H)) L). exists (an (ref (an rt H)) L). exists L. exists rt. split. reflexivity. split. reflexivity. split. reflexivity.
split. apply sub_refl. apply subtyping_refl. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt.
apply IHhas_type in Heqt. inversion Heqt. exists x.
inversion H3. exists x0. inversion H4. exists x1. inversion H5. exists x2. split. apply H6. split. apply H6. split. apply H6. split. apply H6.
apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl.
apply H6. apply H2.
Qed.



(*inversion of [has_type pc Gamma HT (tapp t1 t2) T]*)
Lemma inversion_tapp: forall pc Gamma HT t1 t2 T2,
has_type pc Gamma HT (tapp t1 t2) T2 ->
exists T1', exists T2', exists b', exists T1'', exists T1''', exists T2'', exists b'', exists pc', exists sp', exists sp'',
(sp'=joins pc' b')/\has_type pc' Gamma HT t1 (an (fn T1' sp' T2') b')/\((an (fn T1' sp' T2') b')<:(an (fn T1'' sp'' T2'') b''))/\
(has_type pc' Gamma HT t2 T1''')/\(T1''' <: T1'')/\(subsum_r pc pc')/\
((joinTs T2'' b'')<:T2).
Proof. intros. remember (tapp t1 t2) as t. induction H0.
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt.
 subst. exists T1. exists T2. exists b. exists T1. exists T1. exists T2. exists b. exists pc. exists (joins pc b). exists (joins pc b). split. reflexivity.
split. apply H0_. split. apply subtyping_refl. split. apply H0_0. split. apply subtyping_refl. split. apply sub_refl. apply subtyping_refl. 
inversion Heqt. inversion Heqt. inversion Heqt. apply IHhas_type in Heqt. inversion Heqt. exists x. inversion H3. exists x0. inversion H4. exists x1. inversion H5. exists x2.
inversion H6. exists x3. inversion H7. exists x4. inversion H8. exists x5. inversion H9. exists x6. inversion H10. exists x7. inversion H11. exists x8. 
split. apply H12. split. apply H12. split. apply  H12. split. apply H12. split. apply H12. split. apply subsum_r_trans with (a:=pc')(b:=pc)(c:=x6). apply H1. apply H12. apply subtyping_trans with (x:=T)(y:=T).
apply subtyping_refl. apply H12. apply H2.
Qed.

(*inversion of [has_type pc Gamma HT (tref T1 t b) T]*)
Lemma inversion_tref:forall pc Gamma HT T1 T t,
has_type pc Gamma HT (tref T1 t) T ->
exists pc', exists T1', exists T1'', exists b,
(subsum_r L b)/\
((an (ref T1) b)<:T)/\
(has_type pc' Gamma HT t T1')/\(T1' <: T1'')/\(subsum_r pc pc')/\(T1''<:T1)/\
(subsum_r pc' (labelT T1')).
Proof. intros. remember (tref T1 t) as e. induction H0. inversion Heqe. inversion Heqe. inversion Heqe.
inversion Heqe. inversion Heqe. inversion Heqe. inversion Heqe. inversion Heqe. inversion Heqe. subst. 
exists pc. exists T1. exists T1. exists L. split. apply sub_refl. split. apply subtyping_refl.
split. apply H0. split. apply subtyping_refl. split. apply sub_refl. split. apply subtyping_refl. apply H1.
inversion Heqe. inversion Heqe. apply IHhas_type in Heqe. inversion Heqe. exists x. inversion H3. exists x0.
inversion H4. exists x1. inversion H5. exists x2. split. apply H6. split. 
apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl. apply H6. apply H2. split. apply H6.
split. apply H6. split. apply subsum_r_trans with (a:=pc')(b:=pc)(c:=x). apply H1. apply H6. split. apply  H6.
apply H6.
Qed.

(*inversion of [has_type pc Gamma HT (tderef t) T]*)
Lemma inversion_tderef:forall pc Gamma HT t T,
has_type pc Gamma HT (tderef t) T ->
exists pc', exists T1, exists b', exists b'',
has_type pc' Gamma HT t (an (ref T1) b')/\(subsum_r b' b'')/\
((joinTs T1 b'')<:T)/\(subsum_r pc pc').  
Proof. intros. remember (tderef t) as e. induction H0. inversion Heqe. inversion Heqe. inversion Heqe. inversion Heqe. inversion Heqe.
inversion Heqe. inversion Heqe. inversion Heqe. inversion Heqe. inversion Heqe. subst. exists pc. exists T. exists b. exists b. split. apply H0. split.
apply sub_refl. split. apply subtyping_refl. apply sub_refl. inversion Heqe. 
apply IHhas_type in Heqe. inversion Heqe. exists x. inversion H3. exists x0. inversion H4. exists x1.
inversion H5. exists x2. split. apply H6. split. apply H6. split. apply subtyping_trans with (x:=T)(y:=T).
apply subtyping_refl. apply H6. apply H2. apply subsum_r_trans with (a:=pc')(b:=pc)(c:=x).
apply H1. apply H6. 
Qed.
 
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
inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. inversion Heqt. subst. exists pc.
exists T. exists T. exists b. split. apply t_assign with (b:=b)(T:=T). reflexivity. apply H1.
apply H0_. apply H0_0. split. apply H0_. split. apply H0_0. split. apply subtyping_refl. split.
apply sub_refl. split. apply H1. apply subtyping_refl. apply IHhas_type in Heqt.
inversion Heqt. exists x. inversion H3. exists x0. inversion H4. exists x1. inversion H5. exists x2.
split. apply H6. split. apply H6. split. apply H6. split. apply H6. split. apply subsum_r_trans with (a:=pc')(b:=pc)(c:=x).
apply H1. apply H6. split. apply H6. apply subtyping_trans with (x:=T)(y:=T). apply subtyping_refl. apply H6. apply H2.
Qed.


(*#############################*)
(*some examples of ill-typed terms*)

Example ill_typed_1:forall pc HT,
~has_type pc empty_context HT
          (tvar (Id 0))
          (an int L).
Proof. intros. intros contra. apply inversion_tvar in contra. inversion contra. inversion H0. 
inversion H1.
Qed.
Example ill_typed_2:forall pc Gamma HT,
~has_type pc Gamma HT
          (tcon 0)
          (an unit H).
Proof. intros. intros contra. apply inversion_tcon in contra. inversion contra. inversion H0. inversion H1.
inversion H2. inversion H4. inversion H6. subst. inversion H8.
Qed.
Example ill_typed_3:forall pc Gamma HT,
~has_type pc Gamma HT
          tunit
          (an int L).
Proof. intros. intros contra. apply inversion_tunit in contra. inversion contra. inversion H0. inversion H1. 
inversion H2. inversion H4. inversion H6. subst. inversion H8.
Qed.
Example ill_typed_4:forall pc Gamma HT rt,
~has_type pc Gamma HT
          tH
          (an rt L).
Proof. intros. intros contra. apply inversion_tH in contra. inversion contra. inversion H0. inversion H2.
inversion H5. inversion H2. inversion H2.
Qed.
Example ill_typed_5:forall pc Gamma,
~has_type pc Gamma [an int L]
          (tloc (an int L) (Some 1))
          (an (ref (an int L)) H).
Proof. intros. intros contra. apply inversion_tloc_L in contra. inversion contra. 
inversion H0. inversion H1. inversion H2. simpl in H3. inversion H3.
Qed.
Example ill_typed_6:forall pc Gamma,
~has_type pc Gamma [an int L]
          (tloc (an int H) (Some 0))
          (an (ref (an int L)) H).
Proof. intros. intros contra. apply inversion_tloc_L in contra. inversion contra.
inversion H0. inversion H1.  inversion H2. simpl in H3. inversion H3.
Qed.
Example ill_typed_7:forall pc Gamma HT,
~has_type pc Gamma HT
          (tabs (Id 0)(an int L)(tvar (Id 0)))
          (an int L).
Proof. intros. intros contra. apply inversion_tabs in contra. inversion contra.
inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. inversion H5.
inversion H6. inversion H8. inversion H10. inversion H12. inversion H14. inversion H16.
inversion H18. inversion H20. 
Qed.
Example ill_typed_8:forall pc Gamma HT,
~has_type pc Gamma HT
          (tabs (Id 0)(an int H)(tref (an int L)(tcon 0)))
          (an (fn (an int H) H (an (ref (an int L)) H)) H).
Proof. intros. intros contra. apply inversion_tabs in contra. inversion contra. inversion H0.
inversion H1. inversion H2. inversion H3. inversion H4. inversion H5. inversion H6. inversion H8.
inversion H10. inversion H12. inversion H14.  inversion H16. inversion H18. inversion H20. subst. destruct x4.
inversion H30. destruct x3. inversion H11. apply inversion_tref in H9. inversion H9. inversion H21. inversion H22.
inversion H23. inversion H24. inversion H27. inversion H29. inversion H34. inversion H36. inversion H38. 
apply inversion_tcon in H33. inversion H33. inversion H41. inversion H42. inversion H43. inversion H45. inversion H47.
rewrite->H46 in H49. destruct x4. destruct r. destruct x3. inversion H37. destruct s. inversion H40. destruct x6. destruct r.
destruct s. inversion H35. inversion H52.  inversion H39. inversion H52. inversion H39. inversion H39. inversion H39. inversion H49.
inversion H49. inversion H49.
Qed.
Example ill_typed_9:forall pc Gamma HT,
~has_type pc Gamma HT
          (tapp (tcon 0)(tcon 1))
          (an int L).
Proof. intros. intros contra. apply inversion_tapp in contra. inversion contra. inversion H0. inversion H1. inversion H2. inversion H3.
inversion H4. inversion H5. inversion H6. inversion H7. inversion H8. inversion H9. inversion H11. apply inversion_tcon  in H12. inversion H12.
inversion H14. inversion H15. inversion H16. inversion H18. inversion H20. subst. inversion H22.
Qed.
Example ill_typed_10:forall Gamma HT,
~has_type H Gamma HT 
          (tapp (tabs (Id 0)(an int L)(tref (an int L)(tcon 0)))(tcon 1))
          (an (ref (an int L)) L).
Proof. intros. intros contra. apply inversion_tapp in contra. inversion contra. inversion H0. inversion H1. inversion H2. inversion H3. inversion H4.
inversion H5. inversion H6. inversion H7. inversion H8. inversion H9. inversion H11. inversion H13. inversion H15. inversion H17. inversion H19.
destruct x6. inversion H0. inversion H20. simpl in H10. subst. apply inversion_tabs in H12. inversion H12. inversion H10. inversion H22. inversion H23.
inversion H24. inversion H25. inversion H26. inversion H27. inversion H29. inversion H31. inversion H33. destruct x10. inversion H34. inversion H35.
inversion H37. inversion H39. inversion H41. destruct x12. inversion H51. destruct x11. inversion H32. apply inversion_tref in H30. inversion H30. inversion H54.
inversion H55. inversion H56. inversion H57. inversion H59. inversion H61. inversion H63. inversion H65. inversion H67. destruct x12. destruct r. destruct s.
destruct x11. destruct r. destruct s. destruct x10. inversion H66. inversion H69. inversion H64. inversion H72. inversion H64. inversion H64. inversion H64.
inversion H68. inversion H72. inversion H68. inversion H68. inversion H68. 
Qed.
Example ill_typed_11:forall Gamma HT,
~has_type H Gamma HT
          (tref (an int L)(tcon 0))
          (an (ref (an int L)) H).
Proof. intros. intros contra. apply inversion_tref in contra. inversion contra. inversion H0. inversion H1. inversion H2. inversion H3. inversion H5. inversion H7.
inversion H9. inversion H11. inversion H13. destruct x1. destruct r. destruct s. destruct x0. destruct r. destruct s. destruct x. inversion H12. inversion H15.
inversion H10. inversion H18. inversion H10. inversion H10. inversion H10. inversion H14. inversion H18. inversion H14. inversion H14. inversion H14.
Qed.
Example ill_typed_12:forall pc Gamma,
~has_type pc Gamma []
          (tderef (tloc (an int L) None))
          (an int H).
Proof. intros. intros contra. apply inversion_tderef in contra. inversion contra. inversion H0. inversion H1. inversion H2. inversion H3.
apply inversion_tloc_H in H4. inversion H4. inversion H6. inversion H7. inversion H8. inversion H9. inversion H10. 
Qed.
Example ill_typed_13:forall pc Gamma HT,
~has_type pc Gamma HT
          (tassign (tcon 0)(tcon 1))
          (an unit L).
Proof. intros. intros contra. apply inversion_tassign in contra. inversion contra. inversion H0. inversion H1. inversion H2. inversion H3. inversion H5. 
apply inversion_tcon in H6. inversion H6. inversion H8. inversion H9. inversion H10. inversion H12. inversion H14. subst. inversion H16.
Qed.
Example ill_typed_14:forall Gamma HT n,
~has_type H Gamma HT
          (tassign (tloc (an int L) (Some n))(tcon 1))
          (an unit H).
Proof. intros. intros contra. apply inversion_tassign in contra. inversion contra. inversion H0. inversion H1. inversion H2. inversion H3. inversion H5.
inversion H7. inversion H9. inversion H11. destruct x. inversion H12. apply inversion_tloc_L in H6. inversion H6. inversion H14. inversion H15. inversion H16.
inversion H18. inversion H20. inversion H22. subst. inversion H24. subst. inversion H13. simpl in H19. inversion H19.
Qed.


          
(**
Properties of [LowLang],
a. Determinism
b. ...
*)
(*Determinism*)
Theorem determinism: forall t t' t'' hp hp' hp'' PC,
t / hp ==PC=> t' / hp'  ->
t / hp ==PC=> t'' / hp'' ->
(t' = t''/\hp' = hp'').
Proof. intros t. induction t.
Case ("tvar").
             intros. inversion H0.
Case ("tcon").
             intros. inversion H0.
Case ("tabs"). 
             intros. inversion H0.
Case ("tapp"). 
             intros. inversion H0. inversion H1. subst. inversion H9. subst. split.
             reflexivity. reflexivity. subst. inversion H13. subst. inversion H6. subst.
             inversion H16. subst. inversion H16. subst. inversion H16. subst. inversion H16. subst. inversion H16. subst.
             inversion H9. subst.
             inversion H1. subst. inversion H6. subst.
             apply IHt1 with (t':=t1')(t'':=t1'0)(hp'':=hp'') in H6. inversion H6. subst. split. reflexivity.
             reflexivity. apply H7. subst. inversion H7. subst. inversion H6. subst. inversion H6. subst. inversion H6.
             subst. inversion H6. subst. inversion H6. subst. inversion H6. subst. inversion H1. subst. inversion H7.
             subst. inversion H9. subst. inversion H9. subst. inversion H9. subst. inversion H9. subst. inversion H9.
             subst. inversion H6. subst. inversion H7. subst. inversion H7. subst. inversion H7. subst. inversion H7. subst.
             inversion H7. subst.
             apply IHt2 with (t':=t2')(t'':=t2'0)(hp'':=hp'')in H9. inversion H9. subst. split. reflexivity. reflexivity.
             apply H11. subst. inversion H7. subst. inversion H9. subst. inversion H9. subst. inversion H9. subst. inversion H9. subst.
             inversion H9. subst. inversion H1. subst. inversion H7. subst. inversion H6. subst. inversion H10. subst. inversion H10. subst. inversion H10. subst.
             inversion H10. subst. inversion H10. subst. split. reflexivity. reflexivity.
Case ("tunit").
             intros. inversion H0.
Case ("tref").
             intros. inversion H0. inversion H1. subst.  split. reflexivity. reflexivity. subst. inversion H20.
             apply H9 in H2. inversion H2. inversion H2. inversion H3. rewrite->H10 in H3. inversion H3. subst.
             inversion H7. subst.
             inversion H17. subst. inversion H17. subst. inversion H17. subst. inversion H17. subst. inversion H17. subst.
             inversion H1. subst. inversion H9. apply H11 in H2. inversion H2. inversion H2. inversion H3. rewrite->H12 in H3. inversion H3.
             split. reflexivity. reflexivity. subst. inversion H6. subst.
             inversion H9. subst. inversion H7. subst. inversion H7. subst. inversion H7. subst. 
              inversion H7. subst.  inversion H7. subst.  inversion H7. subst. 
             inversion H1. subst. inversion H8. subst. inversion H6. subst. inversion H6. subst. inversion H6. subst. inversion H6. subst.
             inversion H6. subst. inversion H7. subst. inversion H6. subst. inversion H6. subst. inversion H6. subst. inversion H6. subst.
             inversion H6. subst.
             specialize (IHt t'0 t' hp hp' hp''). apply IHt in H6.
             inversion H6. subst. split. reflexivity. reflexivity. apply H7.           
Case ("tderef").
             intros. inversion H0. inversion H1. subst. inversion H9. subst. split. reflexivity. reflexivity. subst. inversion H10. subst. inversion H12. subst.
             inversion H10. subst. inversion H1. subst. split. reflexivity. reflexivity. subst. inversion H5. subst. inversion H1. subst. inversion H5. subst.
             inversion H5. subst. 
             apply IHt with (t':=t'0)(t'':=t')(hp'':=hp'') in H5. inversion H5. subst. split. reflexivity. reflexivity. apply H6. subst. inversion H5. subst.
             inversion H1. subst. inversion H5. split. reflexivity. reflexivity.
Case ("tloc").
             intros. inversion H0.
Case ("tassign"). 
             intros. inversion H0. inversion H1. subst. inversion H13. subst. split. reflexivity. reflexivity. subst. inversion H13. subst. inversion H11. inversion H2.
             subst. inversion H13. subst. inversion H17. subst. inversion H9. subst.
             inversion H20. subst. inversion H20. subst. inversion H20. subst. inversion H20.
             subst. inversion H20. subst. inversion H1.  subst. split. reflexivity. reflexivity.
             subst. inversion H11. subst. inversion H6. subst. inversion H7. subst. inversion H11. subst. inversion H11. subst. inversion H11. subst. inversion H11. subst. inversion H11.
             subst. inversion H1. subst. inversion H10. subst. split. reflexivity. reflexivity. subst. inversion H7. subst. inversion H6. subst. inversion H10. subst. inversion H10. subst. inversion H10. subst.
             inversion H10. subst. inversion H10. subst. inversion H1. subst. split. reflexivity. reflexivity. subst. inversion H7. subst. inversion H6. subst.
             inversion H10. subst. inversion H10. subst. inversion H10. subst. inversion H10. subst. inversion H10. subst. inversion H1. subst. inversion H6. subst. inversion H6. subst. inversion H6. subst. inversion H6.
             subst.             
             specialize (IHt1 t1' t1'0 hp hp' hp'' PC). apply IHt1 in H6. inversion H6. subst.
             split. reflexivity. reflexivity. apply H7. subst. inversion H7. subst. inversion H6. subst. inversion H6. subst. inversion H6. subst. inversion H6. subst. inversion H6. subst.
             inversion H1. subst. 
             inversion H11. subst. inversion H0. inversion H7. subst. inversion H15. subst. inversion H0. inversion H7. subst. inversion H15. subst. inversion H0. inversion H7. subst. inversion H15. subst.
             inversion H0. inversion H7. subst. inversion H15. subst. inversion H0. inversion H7. subst. inversion H15. subst. inversion H8. subst.
             inversion H9. subst. inversion H9. subst. inversion H9. subst. inversion H9. subst. inversion H9. subst. inversion H7. subst. inversion H9.
             subst. inversion H9. subst. inversion H9. subst. inversion H9. subst. inversion H9. subst. inversion H0. subst. inversion H8. subst. inversion H7. subst.
             inversion H9. subst. inversion H9. subst. inversion H9. subst. inversion H9. subst. inversion H9. subst. inversion H6. subst. inversion H7. subst. inversion H7. subst. inversion H7. subst. inversion H7. subst. 
             inversion H7. subst.
             specialize (IHt2 t2' t2'0 hp hp' hp'' PC). apply IHt2 in H9. inversion H9. subst. split. reflexivity. reflexivity. apply H11.
Case ("tH"). 
             intros. inversion H0.
Qed.

Theorem determinism_extended:forall x y z PC,
value (fst y)  ->
value (fst z) ->
Multistep x PC y  ->
Multistep x PC z  ->
fst y = fst z.
Proof. intros. generalize dependent z. induction H2.
intros. inversion H0. inversion H3. subst. apply H4. subst. destruct x. simpl in H4. subst.
inversion H2. inversion H3. subst. apply H4. subst. destruct x. simpl in H4. subst. inversion H2.
inversion H3. subst. apply H4. subst. destruct x. simpl in H4. subst. inversion H2.
inversion H3. subst. apply H4. subst. destruct x. simpl in H4. subst. inversion H2.
inversion H3. subst. apply H4. subst. destruct x. simpl in H4. subst. inversion H2.

intros. apply IHMulti. apply H0. apply H3. inversion H4. subst. inversion H3. subst.
destruct z0. simpl in H6. subst. inversion H1. destruct z0. simpl in H6. subst. inversion H1. destruct z0. simpl in H6. subst. inversion H1.
destruct z0. simpl in H6. subst. inversion H1. destruct z0. simpl in H6. subst. inversion H1.
subst. destruct x. destruct y. destruct y0. apply determinism with (t':=t0)(hp':=h0)(t'':=t1)(hp'':=h1)in H1. inversion H1. subst.
apply H6. apply H5.
Qed.



End LowLang.   

Module Correspondence.

(*Projection function*)
(*a. projection of term*)
Fixpoint project_e (e : SecLang.tm) : LowLang.tm :=
match e with
(*variables*)
| SecLang.tvar x => LowLang.tvar x
(*constants*)
| SecLang.tcon n L => LowLang.tcon n
| SecLang.tcon n H => LowLang.tH
(*protects*)
| SecLang.tprot L e' => project_e e'
| SecLang.tprot H e' => LowLang.tH
(*abstractions*)
| SecLang.tabs x T e L => LowLang.tabs x T (project_e e) 
| SecLang.tabs x T e H => LowLang.tH
(*applications*)
| SecLang.tapp t1 t2 => LowLang.tapp (project_e t1)(project_e t2)
(*unit*)
| SecLang.tunit L => LowLang.tunit
| SecLang.tunit H => LowLang.tH
(*allocation*)
| SecLang.tref T t L => LowLang.tref T (project_e t)
| SecLang.tref T t H => LowLang.tH
(*deallocation*)
| SecLang.tderef t => LowLang.tderef (project_e t)
(*location*)
| SecLang.tloc T N L => LowLang.tloc T N
| SecLang.tloc T N H => LowLang.tH
(*assignment*)
| SecLang.tassign t1 t2 => LowLang.tassign (project_e t1)(project_e t2)
end.

(*some lemma regarding [project_e]*)
Lemma project_e_subst:forall x v e,
SecLang.value v ->
project_e (SecLang.subst x v e) = LowLang.subst x (project_e v)(project_e e).
Proof. intros. generalize dependent x. generalize dependent v. induction e.
Case ("tvar"). intros. simpl. remember (beq_id x i) as CC. destruct CC. reflexivity.
               reflexivity.
Case ("tprot"). intros. simpl. destruct s. apply IHe. apply H0. reflexivity.
Case ("tcon"). intros. simpl. destruct s. reflexivity. reflexivity.
Case ("tabs"). intros. simpl. destruct s. simpl. remember (beq_id x i) as CC. destruct CC.
               reflexivity. apply IHe with(x:=x)in H0. rewrite<-H0. reflexivity.
               reflexivity.
Case ("tapp"). intros. simpl. assert (SecLang.value v). apply H0. apply IHe1 with(x:=x)in H0.
               apply IHe2 with(x:=x)in H1. rewrite->H0. rewrite->H1. reflexivity.
Case ("tunit"). intros. simpl. destruct s. reflexivity. reflexivity.
Case ("tref"). intros. simpl. destruct s. apply IHe with(x:=x)in H0. rewrite->H0. reflexivity.
               reflexivity.
Case ("tderef"). intros. simpl. apply IHe with(x:=x)in H0. rewrite->H0. reflexivity.
Case ("tloc"). intros. simpl. destruct s. reflexivity. reflexivity.
Case ("tassign"). intros. simpl. assert (SecLang.value v). apply H0. apply IHe1 with(x:=x)in H0.
               apply IHe2 with(x:=x)in H1. rewrite->H0. rewrite->H1. reflexivity.
Qed.


(*marked heap*)
Definition heap := list ((LowLang.tm*Ty)*(nat*nat)).
Definition emp_hp:= @nil ((LowLang.tm*Ty)*(nat*nat)).

(**
Note the marked heap is the projection of the heap in [SecLang] to a heap where
each of its member is marked with a pair of numbers indication the change of its 
location in the heap
*)

(*Some examples*)
Check (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil).
(**
Note the above marked heap indicates that,
a. a Low constant in [SecLang] whose position on the heap is [0] before the
   projection and [0] after the projection
b. another constant in [SecLang] whose position on the heap is [2] before the
   projection and [1] after the projection
*)

(*heap_projection*)
(*firstly we generate a heap where every cell is marked according to its location on the heap*)
Fixpoint marked_heap' (hp:SecLang.heap)(n:nat) : list ((SecLang.tm*Ty)*(nat*nat)) :=
match hp , n with
| h :: t , 0 =>match h with
               |(e,T)=>((e,T),(0,0)) :: (marked_heap' t 1)
               end
| h :: t , n =>match h with
               |(e,T)=>((e,T),(n,n)) :: (marked_heap' t (S n))
               end
| nil , _ => nil
end.
(*some tests*)
Example test_marked_heap'_1:
marked_heap' ((SecLang.tcon 6 L,an int L) :: (SecLang.tcon 6 H,an int H) :: (SecLang.tcon 5 L,an int L) :: nil) 0
= ((SecLang.tcon 6 L,an int L),(0,0)) :: ((SecLang.tcon 6 H,an int H),(1,1)) :: ((SecLang.tcon 5 L,an int L),(2,2)) :: nil.
Proof. simpl. reflexivity. Qed.
Example test_marked_heap'_2:
marked_heap' ((SecLang.tcon 0 L,an int L) :: (SecLang.tcon 1 L,an int L) :: nil) 0
= ((SecLang.tcon 0 L,an int L),(0,0)) :: ((SecLang.tcon 1 L,an int L),(1,1)) :: nil.
Proof. simpl. reflexivity. Qed.
(*some lemmas regarding [marked_heap']*)
Lemma n_plus_1:forall n,
n + 1 = S n.
Proof. intros n. induction n. reflexivity. rewrite->plus_Sn_m. rewrite->IHn.
reflexivity.
Qed.
Lemma marked_heap'_hd:forall h t n,
marked_heap' (h :: t) n = (h,(n,n)) :: (marked_heap' t (n+1)).
Proof. intros. generalize dependent h. generalize dependent t. induction n.
intros. simpl.  destruct h. reflexivity.
intros. simpl. destruct h. rewrite->n_plus_1. reflexivity.
Qed.

(* then we get the marked heap with only low cells on it*)
Fixpoint marked_heap (hp:list ((SecLang.tm*Ty)*(nat*nat))) (n:nat): list ((LowLang.tm*Ty)*(nat*nat)) :=
match hp with
| h :: t =>match h with
           |(a,b)=>match a with
                   | (e,T)=>match SecLang.label e with
                            | H =>marked_heap t (S n)
                            | L =>match b with
                                       |(n1,n2)=>match a with
                                                 |(e,T)=>((project_e e,T),(n1,n2-n)) :: (marked_heap t n)
                                                 end
                                  end
                            end
                   end
           end
| nil => nil
end.
(*some test*)
Example test_marked_heap_1:
marked_heap (((SecLang.tcon 1 L,an int L),(0,0)) :: ((SecLang.tcon 2 H,an int H),(1,1)) :: ((SecLang.tcon 3 L,an int L),(2,2)) :: ((SecLang.tcon 4 H,an int H),(3,3)) :: ((SecLang.tcon 5 L,an int L),(4,4)) :: nil) 0
= (((LowLang.tcon 1,an int L),(0,0)) :: ((LowLang.tcon 3,an int L),(2,1)) :: ((LowLang.tcon 5,an int L),(4,2)) :: nil).
Proof. simpl. reflexivity. 
Qed.
(*some lemmas regarding [marked_heap]*)
Lemma marked_heap_L:forall e T n1 n2 t n,
SecLang.label e = L ->
marked_heap (((e,T),(n1,n2)) :: t) n = ((project_e e,T),(n1,n2-n)) :: (marked_heap t n).
Proof. intros. simpl. rewrite->H0. reflexivity. 
Qed.

Lemma marked_heap_mark_length:forall hp n1 n2 n3 n4,
length (marked_heap(marked_heap' hp n1)n2) = length (marked_heap(marked_heap' hp n3)n4).
Proof. intros hp. induction hp.
Case ("nil"). intros. reflexivity.
Case ("h::t"). intros. destruct a. simpl. destruct n1. destruct n3. simpl. remember (SecLang.label t) as BB.
              destruct BB. simpl. specialize (IHhp 1 n2 1 n4). rewrite->IHhp. reflexivity.
              specialize (IHhp 1 (S n2) 1 (S n4)). rewrite->IHhp. reflexivity. simpl. remember (SecLang.label t) as BB.
              destruct BB. simpl. specialize (IHhp 1 n2 (S (S n3)) n4). rewrite<-IHhp. reflexivity.
              specialize (IHhp 1 (S n2)(S (S n3)) (S n4)). rewrite<-IHhp. reflexivity. destruct n3. simpl.
              remember (SecLang.label t) as BB. destruct BB. simpl. specialize (IHhp (S (S n1)) n2 1 n4). 
              rewrite<-IHhp. reflexivity. specialize (IHhp (S (S n1)) (S n2) 1 (S n4)). rewrite<-IHhp.
              reflexivity. simpl. remember (SecLang.label t) as BB. destruct BB. simpl. specialize (IHhp (S (S n1)) n2 (S (S n3)) n4).
              rewrite<-IHhp. reflexivity. specialize (IHhp (S (S n1)) (S n2) (S (S n3)) (S n4)). rewrite<-IHhp.
              reflexivity.
Qed.
             

(*look-up function regarding the marked heap*)
(**
Note: in the current segment, heaps are all marked and there are two ways of looking up
      a value stored on a heap,
a. looking up via matching up query with some mark,[marked_heap_lookup]
b. looking up via the query indicating the position of some value stored on the heap
   [].
*)
(*a*)
(**
The search is being done via looking for a match between a target and the first number
of some mark of the marked heap
*)
Fixpoint marked_heap_lookup (n:nat)(hp:list ((LowLang.tm*Ty)*(nat*nat))):(option (LowLang.tm*Ty)):=
match hp with
| h :: t => match h with
            | (fst,snd) => match snd with
                           | (n1,n2) =>if beq_nat n1 n
                                      then Some fst                              
                                      else marked_heap_lookup n t
                           end
            end
| nil => None
end.

(*extract the result of [marked_heap_lookup]*)
Definition marked_efst (p:option(LowLang.tm*Ty)) : option (LowLang.tm) :=
 match p with
 | None => None
 | Some (t , T) => Some t
 end.
(*b*)
(*heap_lookup*)
Fixpoint heap_lookup (n:nat)(hp:list ((LowLang.tm*Ty)*(nat*nat))):(option ((LowLang.tm*Ty)*(nat*nat))):=
  match hp , n with
  | nil , _ =>None
  | h::t , 0 => Some h
  | h::t , S n' =>heap_lookup n' t
  end.

(*extract the result of [heap_lookup]*)
Definition efst (p:option((LowLang.tm*Ty)*(nat*nat))) : option (LowLang.tm) :=
 match p with
 | None => None
 | Some ((t,T),N) => Some t
 end.

(*the following block is regarding the "replace" function w.r.t. marked heap*)
(*#########################*)
(**
note that similar to the "lookup" functions defines in the current block,there are
two ways to replace a value on the marked heap,
a. we can either query for the first element of the mark attached to the value like 
   [return_smallest_match] to locate the value and then replace it
b. we can also firstly get the second value of the mark and then search for the value
   on the indicated location directly essentially ignoring the marks on the heap
*)
(**
"a. marked_heap_replace"
*)
Fixpoint marked_heap_replace n (x:(LowLang.tm)*Ty) (hp:list ((LowLang.tm*Ty)*(nat*nat))): list ((LowLang.tm*Ty)*(nat*nat)) :=
match hp with
| h :: t => match h with
            | (fst,snd) => match snd with
                           | (n1,n2) =>if beq_nat n1 n
                                       then (x,snd)::t
                                       else h::(marked_heap_replace n x t)
                           end
                end
| nil => nil
end.
(*some examples*)
Example test_marked_heap_replace_1:
marked_heap_replace 3 (LowLang.tcon 1,an int L) (((LowLang.tcon 0,an int L),(0,0)):: ((LowLang.tcon 2,an int L),(3,1)) :: ((LowLang.tunit,an unit L),(4,2)) :: nil)
= (((LowLang.tcon 0,an int L),(0,0)) :: ((LowLang.tcon 1,an int L),(3,1)) :: ((LowLang.tunit,an unit L),(4,2)) :: nil).
Proof. simpl. reflexivity.
Qed.
Example test_marked_heap_replace_2:
marked_heap_replace 2 (LowLang.tcon 2,an int L) (((LowLang.tcon 0,an int L),(3,0))::((LowLang.tcon 1,an int L),(6,1))::nil)
= (((LowLang.tcon 0,an int L),(3,0))::((LowLang.tcon 1,an int L),(6,1))::nil).
Proof. simpl. reflexivity. 
Qed.

(*########*)
(*backhere*)
(*########*)

(*some lemmas related to [marked_heap_replace]*)
Lemma marked_heap_replace_same:forall hp n n1 n2 p,
n < n1 ->
marked_heap_replace n p (marked_heap(marked_heap' hp n1)n2)
=(marked_heap(marked_heap' hp n1)n2).
Proof. intros hp. induction hp.
Case ("nil"). intros. reflexivity.
Case ("h::t"). intros. destruct a. simpl. destruct n1. destruct n.
              apply LowLang.lt_same_F in H0. inversion H0. inversion H0.
              simpl. remember (SecLang.label t) as BB. destruct BB. destruct n2.
              simpl. destruct n. specialize (IHhp 0 (S (S n1)) 0 p). apply le_S in H0.
              apply IHhp in H0. rewrite->H0. reflexivity. remember (beq_nat n1 n) as CC. destruct CC.
              apply beq_nat_eq in HeqCC. subst. apply LowLang.lt_same_F in H0. inversion H0.
              specialize (IHhp (S n) (S (S n1)) 0 p). apply le_S in H0. apply IHhp in H0. rewrite->H0.
              reflexivity. simpl. destruct n. specialize (IHhp 0 (S (S n1)) (S n2) p). apply le_S in H0.
              apply IHhp in H0. rewrite->H0. reflexivity. remember (beq_nat n1 n) as CC. destruct CC.
              apply beq_nat_eq in HeqCC. rewrite->HeqCC in H0. apply LowLang.lt_same_F in H0. inversion H0.
              specialize (IHhp (S n) (S (S n1)) (S n2) p). apply le_S in H0. apply IHhp in H0. rewrite->H0.
              reflexivity. specialize (IHhp n (S (S n1)) (S n2) p). apply le_S in H0. apply IHhp in H0. 
              rewrite->H0. reflexivity.
Qed.

 
(**
"b. heap_replace"
*)
Fixpoint heap_replace n (x:(LowLang.tm)*Ty) (hp:list ((LowLang.tm*Ty)*(nat*nat))): list ((LowLang.tm*Ty)*(nat*nat)) :=
  match hp , n with
  | nil , _ =>nil
  | h::t , 0 => match h with
                |(fst,snd)=>(x,snd)::t
                         
                end
  | h::t , S n' =>h :: (heap_replace n' x t)
  end.
(*some examples*)
Example test_heap_replace_1:
heap_replace 2 (LowLang.tcon 1,an int L)(((LowLang.tcon 0,an int L),(7,0))::((LowLang.tcon 2,an int L),(8,1))::((LowLang.tcon 3,an int L),(9,2))::nil)
= (((LowLang.tcon 0,an int L),(7,0))::((LowLang.tcon 2,an int L),(8,1))::((LowLang.tcon 1,an int L),(9,2))::nil).
Proof. simpl. reflexivity.
Qed.
Example test_heap_replace_2:
heap_replace 3 (LowLang.tcon 1,an int L)(((LowLang.tcon 0,an int L),(3,0))::((LowLang.tcon 2,an int L),(5,1))::((LowLang.tcon 3,an int L),(6,2))::nil)
= (((LowLang.tcon 0,an int L),(3,0))::((LowLang.tcon 2,an int L),(5,1))::((LowLang.tcon 3,an int L),(6,2))::nil).
Proof. simpl. reflexivity. 
Qed.
(*#########################*)


(*marked heap well-formed*)
(**
the property [marked_heap_well_formed] states that for each term on the marked heap
,it is well_formed given some natural number corresponding to the length of the 
original heap in [SecLang]
*)
(*marked_heap well_formed*)
Inductive marked_heap_well_formed : list ((LowLang.tm*Ty)*(nat*nat)) -> nat -> Prop :=
| nil_mhwf:forall n, 
          marked_heap_well_formed nil n
| one_mhwf:forall t0 T p t n,
          marked_heap_well_formed t n ->
          LowLang.well_formed t0 n ->
          marked_heap_well_formed (((t0,T),p) :: t) n.
(*some lemmas regarding [marked_heap_well_formed]*)
Lemma marked_heap_well_formed_shrink:forall hp a n,
  marked_heap_well_formed (a :: hp) n ->
  marked_heap_well_formed hp n.
Proof. intros. inversion H0. apply H3.
Qed.

(*finally we put [marked_hp'] and [marked_hp] together to get [project_hp]*)
Definition project_hp (hp:SecLang.heap) : list ((LowLang.tm*Ty)*(nat*nat)) :=
marked_heap (marked_heap' hp 0) 0.
(*some examples*)
Example test_project_hp_1:
project_hp ((SecLang.tcon 6 L,an int L) :: (SecLang.tcon 6 H,an int H) :: (SecLang.tcon 5 L,an int L) :: nil)
= (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil).
Proof. compute. reflexivity. Qed. 

(**
Note the following function decides whether or not two marked heaps have the same
marks. It will be useful later on for proving "Lemma two" in Lu's paper
*)
Fixpoint same_mark (hp1:list ((LowLang.tm*Ty)*(nat*nat)))(hp2:list ((LowLang.tm*Ty)*(nat*nat))) : bool :=
match hp1 , hp2 with
| (L1,(n1,m1)) :: t1 , (L2,(n2,m2)) :: t2 =>match beq_nat n1 n2 with
                                            | true =>match beq_nat m1 m2 with
                                                     | true =>same_mark t1 t2
                                                     | false =>false
                                                     end
                                            | false =>false
                                            end
| nil , h :: t =>false
| h :: t , nil =>false
| nil , nil =>true
end.
(**
There is only one case where two marked heaps are considered to have the same marks,
a. each of their corresponding marks are the same 
b. these two heaps involved have the same length
See the following examples
*)
Example test_same_mark_1:
same_mark (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 7,an int L),(2,1)) :: ((LowLang.tcon 8,an int L),(5,2)) :: nil)(((LowLang.tcon 1,an int L),(0,0)) :: ((LowLang.tcon 2,an int L),(2,1)) :: ((LowLang.tcon 3,an int L),(5,2)) :: nil)
= true.
Proof. simpl. reflexivity. 
Qed.
Example test_same_mark_2:
same_mark (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 7,an int L),(2,1)) :: nil)(((LowLang.tcon 1,an int L),(0,0)) :: ((LowLang.tcon 2,an int L),(2,1)) :: ((LowLang.tcon 3,an int L),(5,2)) :: nil)
= false.
Proof. simpl. reflexivity.
Qed.
Example test_same_mark_3:
same_mark (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 7,an int L),(2,1)) :: ((LowLang.tcon 8,an int L),(5,2)) :: nil)(((LowLang.tcon 1,an int L),(0,0)) :: ((LowLang.tcon 2,an int L),(2,1)) :: nil)
= false.
Proof. simpl. reflexivity.
Qed.

(*some lemmas regarding [same_mark]*)
Lemma same_mark_length:forall hp hp',
same_mark hp hp' = true ->
length hp = length hp'.
Proof. intros hp. induction hp.
intros. destruct hp'. reflexivity. simpl in H0. inversion H0. intros. destruct hp'. 
destruct a. destruct p0.  simpl in H0. inversion H0. destruct a.  destruct p1. destruct p.
destruct p1. simpl. simpl in H0. remember (beq_nat n n1) as BB. destruct BB. remember (beq_nat n0 n2) as CC.
destruct CC. apply IHhp in H0. rewrite->H0. reflexivity. inversion H0. inversion H0.
Qed. 
Lemma same_mark_refl:forall hp,
same_mark hp hp = true.
Proof. intros. induction hp. reflexivity. destruct a. destruct p0. simpl.
rewrite<-beq_nat_refl. rewrite<-beq_nat_refl. apply IHhp.
Qed.
Lemma same_mark_sym:forall hp1 hp2,
same_mark hp1 hp2 = true ->
same_mark hp2 hp1 = true.
Proof. intros. generalize dependent hp2. induction hp1.
intros. destruct hp2. reflexivity. simpl. destruct p. destruct p0. simpl in H0.  inversion H0. 
intros. destruct hp2. simpl. simpl in H0.  destruct a. destruct p0.  inversion H0. 
 simpl. destruct p. destruct p0. destruct a. destruct p1. remember (beq_nat n n1) as BB.
remember (beq_nat n0 n2) as CC. destruct BB. destruct CC. apply IHhp1. simpl in H0. rewrite->beq_nat_sym in HeqBB. rewrite->beq_nat_sym in HeqCC. 
rewrite<-HeqBB in H0. rewrite<-HeqCC in H0. apply H0. simpl in H0. rewrite->beq_nat_sym in HeqBB. rewrite->beq_nat_sym in HeqCC. rewrite<-HeqBB in H0. rewrite<-HeqCC in H0.
inversion H0. simpl in H0. rewrite->beq_nat_sym in HeqBB. rewrite<-HeqBB in H0. inversion H0.
Qed.

Lemma same_mark_replace:forall hp1 hp2 hp3,
same_mark hp1 hp2 = true ->
same_mark hp1 hp3 = true ->
same_mark hp3 hp2 = true.
Proof. intros. generalize dependent hp2. generalize dependent hp3. induction hp1.
Case ("nil"). intros. destruct hp2. destruct hp3. reflexivity. simpl in H1. inversion H1. destruct hp3. simpl in H0. inversion H0.
              simpl in H0. inversion H0.
Case ("h::t"). intros. destruct hp3. simpl in H1. inversion H1. destruct hp2. simpl in H0. destruct a. destruct p0.  inversion H0.
               destruct a. destruct p1.  inversion H1. destruct hp2. simpl in H0. inversion H0. simpl. destruct p. destruct p0. destruct a. destruct p1. reflexivity.
               simpl. destruct p. destruct p1. destruct p0. destruct p1. remember (beq_nat n n1) as BB. remember (beq_nat n0 n2) as CC. destruct BB. destruct CC.
               destruct a. destruct p2. apply IHhp1. inversion H1. remember (beq_nat n3 n) as DD. destruct DD. remember (beq_nat n4 n0) as EE. destruct EE.
               reflexivity. inversion H3. inversion H3. 
               inversion H0. remember (beq_nat n3 n1) as DD. destruct DD. remember (beq_nat n4 n2) as EE. destruct EE. reflexivity. inversion H3. inversion H3.
               destruct a. destruct p2. simpl in H1. remember (beq_nat n3 n) as DD. destruct DD. remember (beq_nat n4 n0) as EE. destruct EE. apply beq_nat_eq in HeqEE.
               simpl in H0. remember (beq_nat n3 n1) as FF. destruct FF. remember (beq_nat n4 n2) as GG. destruct GG. apply beq_nat_eq in HeqGG. rewrite->HeqEE in HeqGG. rewrite->HeqGG in HeqCC.
               symmetry in HeqCC. apply beq_nat_false in HeqCC. assert (n2=n2). reflexivity. apply HeqCC in H2. inversion H2. inversion H0. inversion H0. inversion H1. inversion H1. 
               destruct a. destruct p2. simpl in H1. remember (beq_nat n3 n) as DD. destruct DD. apply beq_nat_eq in HeqDD. simpl in H0. remember (beq_nat n3 n1) as EE. destruct EE. apply beq_nat_eq in HeqEE.
               rewrite->HeqDD in HeqEE. rewrite->HeqEE in HeqBB. symmetry in HeqBB. apply beq_nat_false in HeqBB. assert (n1=n1). reflexivity. apply HeqBB in H2. inversion H2.
               inversion H0. inversion H1.
Qed.

(*#######try#########*)
Lemma same_mark_empty:forall hp n,
same_mark (marked_heap (marked_heap' hp n) n) [] = true ->
same_mark (marked_heap (marked_heap' hp (S n)) (S n)) [] = true.
Proof. intros. generalize dependent n. induction hp.
Case ("nil"). intros. simpl. reflexivity.
Case ("h::t"). intros. destruct a. simpl in H0. destruct n. simpl in H0. remember (SecLang.label t) as BB. destruct BB.
              inversion H0. simpl. rewrite<-HeqBB. apply IHhp in H0. apply H0. simpl. simpl in H0. remember (SecLang.label t) as BB.
              destruct BB. inversion H0. apply IHhp in H0. apply H0.
Qed.
(*###################*)
               
 


(*some lemmas regarding [project_hp]*)
(**
Recall the way how we get our marked heap,
firstly we have a heap from [SecLang] and we mark each cell on the heap according
to its location on the heap;then for each cell we calculate the number of high cells
on its left and then subtract it from its mark giving us the location of the cell
after we discard the high cells;lastly we apply [project_e] to all the terms on 
the marked heap. 
*)
(**
Consider the following example,
suppose we have
hp = [L(1),H(2),L(3),H(4),L(5)] and hp' = [L(1),H(7),L(3),H(8),L(5)]
according to [project_hp] we have,
project_hp hp = [  1,   3,   5] = project_hp hp'
                0->0 2->1 4->2
Now,we prefix both hp and hp' by (L(8)) and as a result we have,
project_hp hp = [  8,   1,   3,   5] = project_hp hp'
                0->0 1->1 3->2 5->3
while if we prefix by (H(8)) we get,
project_hp hp = [  1,  3,    5] = project_hp hp'
                1->0 3->1 4->2
.
Note how the marks of the extended heap depends upon the label of the new cell.
If it is [L] then the marks of the rest of the heap is equal to the original 
ones added by one or if [H] the marks of the original one is increased only in
their first element.
Sppose we define the following two functions,
[add_both_mark] which add every mark on the heap by one
and [add_fst_mark] which add the first element of every mark on the heap by one
then we have,
a. 
project_hp (a::hp) = (a,(0,0)) :: add_both_mark (project_hp hp)
when the label of is [L];
b.
project_hp (a::hp) = add_fst_mark (project_hp hp)
when the label of hp is [H].
In what follows we firstly define [add_both_mark] and [add_fst_mark] and then prove the above
two equalities.
*)          
(*###########*)
(*add_both_mark*)
Fixpoint add_both_mark (hp:list ((LowLang.tm*Ty)*(nat*nat))) : list ((LowLang.tm*Ty)*(nat*nat)) :=
match hp with
| h :: t =>match h with
           | (a , b) =>match b with
                      |(n1,n2) =>(a,(n1+1,n2+1)) :: (add_both_mark t)
                      end
           end
| nil =>nil
end.
(*some example*)
Example test_add_both_mark_1:
add_both_mark (((LowLang.tcon 1,an int L),(0,0)) :: ((LowLang.tcon 3,an int L),(2,1)) :: ((LowLang.tcon 5,an int L),(4,2)) :: nil)
= (((LowLang.tcon 1,an int L),(1,1)) :: ((LowLang.tcon 3,an int L),(3,2)) :: ((LowLang.tcon 5,an int L),(5,3)) :: nil).
Proof. simpl. reflexivity. Qed.
(*some lemmas regarding [add_both_mark]*)
Lemma add_both_mark_hd:forall a n1 n2 t,
add_both_mark ((a,(n1,n2)) :: t) = (a,(n1+1,n2+1)) :: (add_both_mark t).
Proof. intros. simpl. reflexivity.
Qed.

Lemma Sn_n_plus_one:forall n,
S n = n + 1.
Proof. intros. induction n.
reflexivity. rewrite->plus_Sn_m. rewrite<-IHn.
reflexivity.
Qed.

Lemma n_minus_m_plus_one:forall n m,
m <= n ->
n - m + 1 = 1 + n - m.
Proof. intros. generalize dependent m. induction n.
Case ("nil"). intros. destruct m. reflexivity. inversion H0.
Case ("h::t"). intros. simpl. destruct m. rewrite<-Sn_n_plus_one.
              reflexivity. destruct m. rewrite<-minus_n_O.
              rewrite<-Sn_n_plus_one. reflexivity. apply LowLang.lt_snoc_1 in H0.
              apply IHn in H0. rewrite->H0. rewrite->plus_comm. rewrite<-Sn_n_plus_one.
              simpl. reflexivity.
Qed.
Lemma marked_heap_add_both_mark:forall hp n n',
n' <= n ->
add_both_mark (marked_heap (marked_heap' hp n) n')
=marked_heap (marked_heap' hp (n+1)) n'.
Proof. intros. generalize dependent n. generalize dependent n'. induction hp. 
Case ("nil"). intros. simpl. reflexivity.
Case ("h::t"). intros. rewrite->marked_heap'_hd. rewrite->marked_heap'_hd.
destruct a. remember (SecLang.label t) as BB. destruct BB. simpl. rewrite<-HeqBB. simpl. specialize (IHhp n' (n+1)).
assert (n'<=n). apply H0. apply le_S in H0. rewrite->Sn_n_plus_one in H0. apply IHhp in H0. rewrite->H0.
rewrite->n_minus_m_plus_one. rewrite plus_comm. reflexivity. apply H1.
simpl. rewrite<-HeqBB. specialize (IHhp (S n') (n+1)). apply IHhp. apply SecLang.n_iff_Sn_left in H0.
rewrite<-Sn_n_plus_one. apply H0.
Qed.

Lemma marked_heap_add_both_mark_snoc:forall hp n1 n2 n3 n4 V T,
n2 <= n1 ->
add_both_mark (LowLang.snoc (marked_heap (marked_heap' hp n1)n2)((V,T),(n3,n4)))
=LowLang.snoc (marked_heap (marked_heap' hp (n1+1)) n2)((V,T),(S n3,S n4)).
Proof. intros hp. induction hp. 
Case ("nil"). intros. simpl. rewrite->plus_comm. simpl. rewrite->plus_comm. simpl. reflexivity.
Case ("h::t"). intros. rewrite->marked_heap'_hd. rewrite->marked_heap'_hd.
destruct a. remember (SecLang.label t) as BB. destruct BB. simpl. rewrite<-HeqBB. simpl.
assert (n1+1-n2=1+n1-n2). rewrite->plus_comm. reflexivity. rewrite->H1. clear H1.
assert (n2<=n1). apply H0. apply n_minus_m_plus_one in H0. rewrite->H0. specialize (IHhp (n1+1) n2 n3 n4 V T).
apply le_S in H1. rewrite->plus_comm in IHhp. simpl in IHhp. apply IHhp in H1.
rewrite->plus_comm. simpl. rewrite<-H1. reflexivity.
simpl.  rewrite<-HeqBB. specialize (IHhp (n1+1) (S n2) n3 n4 V T). rewrite->plus_comm in IHhp. simpl in IHhp.
apply SecLang.n_iff_Sn_left in H0. apply IHhp in H0. rewrite->plus_comm. simpl. apply H0.
Qed.


Lemma add_both_mark_same_mark':forall hp hp',
same_mark hp hp' = true ->
same_mark (add_both_mark hp)(add_both_mark hp') = true.
Proof. intros hp. induction hp.
Case ("nil"). intros. destruct hp'. simpl. reflexivity. inversion H0.
Case ("h::t"). intros. destruct a. destruct p0. destruct hp'. inversion H0.
               destruct p0. destruct p1. simpl. simpl in H0. remember (beq_nat n n1) as BB.
               destruct BB. apply beq_nat_eq in HeqBB. rewrite->HeqBB. rewrite<-beq_nat_refl.
               remember (beq_nat n0 n2) as CC. destruct CC. apply beq_nat_eq in HeqCC. rewrite->HeqCC.
               rewrite<-beq_nat_refl. apply IHhp. apply H0. inversion H0. inversion H0.
Qed.

Lemma add_both_mark_same_mark:forall hp hp',
same_mark (project_hp hp)(project_hp hp')  = true ->
same_mark (add_both_mark (project_hp hp))(add_both_mark (project_hp hp')) = true.
Proof. intros. apply add_both_mark_same_mark'. apply H0.
Qed.



(*add_fst_mark*)
Fixpoint add_fst_mark (hp:list ((LowLang.tm*Ty)*(nat*nat))) : list ((LowLang.tm*Ty)*(nat*nat)) :=
match hp with
| h :: t =>match h with
           | (a , b) =>match b with
                      |(n1,n2) =>(a,(n1+1,n2)) :: (add_fst_mark t)
                      end
           end
| nil =>nil
end.
(*some example*)
Example test_add_fst_mark_1:
add_fst_mark (((LowLang.tcon 1,an int L),(0,0)) :: ((LowLang.tcon 3,an int L),(2,1)) :: ((LowLang.tcon 5,an int L),(4,2)) :: nil)
= (((LowLang.tcon 1,an int L),(1,0)) :: ((LowLang.tcon 3,an int L),(3,1)) :: ((LowLang.tcon 5,an int L),(5,2)) :: nil).
Proof. simpl. reflexivity. Qed.
Lemma marked_heap_add_fst_mark:forall hp n m,
m <= n ->
add_fst_mark (marked_heap (marked_heap' hp n) m)
=marked_heap (marked_heap' hp (n+1)) (m+1).
Proof. intros. generalize dependent n. generalize dependent m. induction hp. 
Case ("nil"). intros. simpl. reflexivity.
Case ("h::t"). intros. destruct a. rewrite->marked_heap'_hd. rewrite->marked_heap'_hd. 
remember (SecLang.label t) as BB. destruct BB. simpl. rewrite<-HeqBB. simpl. apply le_S in H0. 
apply IHhp in H0. rewrite->Sn_n_plus_one in H0. assert (n+1-(m+1)=S n - S m). rewrite<-Sn_n_plus_one.
rewrite<-Sn_n_plus_one. reflexivity. rewrite->H1. simpl. rewrite->H0. reflexivity.
simpl. rewrite<-HeqBB. apply SecLang.n_iff_Sn_left in H0. apply IHhp in H0. rewrite->Sn_n_plus_one in H0.
rewrite->plus_Sn_m in H0. apply H0.
Qed.

Lemma marked_heap_add_fst_mark_snoc:forall hp n1 n2 n3 n4 V T,
n2 <= n1 ->
add_fst_mark (LowLang.snoc (marked_heap (marked_heap' hp n1)n2)((V,T),(n3,n4)))
=LowLang.snoc (marked_heap (marked_heap' hp (n1+1))(n2+1))((V,T),(S n3,n4)).
Proof. intros hp. induction hp. 
Case ("nil"). intros. simpl. rewrite->plus_comm. simpl. reflexivity.
Case ("h::t"). intros. destruct a. rewrite->marked_heap'_hd. rewrite->marked_heap'_hd. 
remember (SecLang.label t) as BB. destruct BB. simpl. rewrite<-HeqBB. simpl. specialize (IHhp (n1+1) n2 n3 n4 V T).
rewrite->plus_comm in IHhp. simpl in IHhp. apply le_S in H0. apply IHhp in H0. rewrite->plus_comm. assert (1+n1+1=S (n1+1)). reflexivity.
rewrite->H1. clear H1. assert (1+n1=S n1). reflexivity. rewrite->H1. clear H1.  rewrite<-H0.
assert (n2+1=S n2). rewrite->plus_comm. reflexivity. rewrite->H1. clear H1. simpl. reflexivity.
specialize (IHhp (n1+1) (n2+1) n3 n4 V T). apply SecLang.n_iff_Sn_left in H0.
assert (n1+1=S n1). rewrite->plus_comm. reflexivity. rewrite<-H1 in H0. clear H1.
assert (n2+1=S n2). rewrite->plus_comm. reflexivity. rewrite<-H1 in H0. clear H1. apply IHhp in H0.
simpl.  rewrite<-HeqBB. rewrite->plus_comm in H0. simpl in H0. rewrite->plus_comm in H0. simpl in H0.
rewrite->plus_comm. simpl. apply H0. 
Qed.


Lemma add_fst_mark_same_mark':forall hp hp',
same_mark hp hp' = true ->
same_mark (add_fst_mark hp)(add_fst_mark hp') = true.
Proof. intros hp. induction hp.
Case ("nil"). intros. destruct hp'. simpl. reflexivity. inversion H0.
Case ("h::t"). intros. destruct hp'. destruct a. destruct p0. inversion H0.
              destruct a. destruct p. destruct p1. destruct p2. simpl. simpl in H0.
              remember (beq_nat n n1) as BB. destruct BB. apply beq_nat_eq in HeqBB.
              rewrite->HeqBB. rewrite<-beq_nat_refl. remember (beq_nat n0 n2) as CC. destruct CC.
              apply IHhp. apply H0. inversion H0. inversion H0.
Qed.
Lemma add_fst_mark_same_mark:forall hp hp',
same_mark (project_hp hp)(project_hp hp') = true ->
same_mark (add_fst_mark (project_hp hp))(add_fst_mark (project_hp hp')) = true.
Proof. intros. apply add_fst_mark_same_mark'. apply H0.
Qed.


(*minus_snd_mark*)
Fixpoint minus_snd_mark (hp:list ((LowLang.tm*Ty)*(nat*nat))) : list ((LowLang.tm*Ty)*(nat*nat)) :=
match hp with
| h :: t =>match h with
           | (a , b) =>match b with
                      |(n1,n2) =>(a,(n1,n2-1)) :: (minus_snd_mark t)
                      end
           end
| nil =>nil
end.
(*some example*)
Example test_minus_snd_mark_1:
minus_snd_mark (((LowLang.tcon 1,an int L),(0,0))::((LowLang.tcon 4,an int L),(3,1))::((LowLang.tcon 5,an int L),(4,2))::nil) =
(((LowLang.tcon 1,an int L),(0,0))::((LowLang.tcon 4,an int L),(3,0))::((LowLang.tcon 5,an int L),(4,1))::nil).
Proof. simpl. reflexivity.
Qed.


Lemma marked_heap_minus_snd_mark_1:forall n n',
n - (n' + 1) = n -n' -1.
Proof. intros n. induction n.
Case ("n=0"). reflexivity.
Case ("n=Sn''"). intros. destruct n'. simpl. reflexivity. simpl.
                apply IHn.
Qed.

Lemma marked_heap_minus_snd_mark:forall hp n1 n2,
minus_snd_mark (marked_heap(marked_heap' hp n1) n2)
= (marked_heap(marked_heap' hp n1)(S n2)).
Proof. intro hp. induction hp. 
Case ("nil"). intros. reflexivity.
Case ("h::t"). intros. destruct a. simpl. destruct n1. simpl. 
              remember (SecLang.label t) as BB. destruct BB.
              simpl. specialize (IHhp 1 n2). rewrite->IHhp. reflexivity.
              specialize (IHhp 1 (S n2)). rewrite->IHhp. reflexivity.
              simpl. remember (SecLang.label t) as BB. destruct BB.
              destruct n2. simpl. specialize (IHhp (S (S n1)) 0). rewrite->IHhp.
              reflexivity. simpl. specialize (IHhp (S (S n1)) (S n2)). rewrite->IHhp.
              SearchAbout minus. assert (S n2 = n2 + 1). rewrite->plus_comm. reflexivity.
              rewrite->H0. clear H0. rewrite->marked_heap_minus_snd_mark_1. reflexivity.
              specialize (IHhp (S (S n1)) (S n2)). rewrite->IHhp. reflexivity.
Qed.

Lemma minus_snd_mark_same_mark:forall hp hp',
same_mark hp hp' = true ->
same_mark (minus_snd_mark hp)(minus_snd_mark hp') = true.
Proof. intros hp. induction hp.
Case ("nil"). intros. destruct hp'. simpl. reflexivity. inversion H0.
Case ("h::t"). intros. destruct hp'. destruct a. destruct p0. inversion H0.
              destruct a. destruct p. destruct p1. destruct p2. simpl. simpl in H0.
              remember (beq_nat n n1) as BB. destruct BB. remember (beq_nat n0 n2) as CC. destruct CC.
               apply beq_nat_eq in HeqCC. rewrite->HeqCC. rewrite<-beq_nat_refl. apply IHhp. apply H0.
              inversion H0. inversion H0.
Qed.
    
              

(*Lemma add_both_mark_L*)
Lemma add_both_mark_L:forall e T hp,
SecLang.label e = L ->
project_hp ((e,T) :: hp) = ((project_e e,T),(0,0)) :: (add_both_mark (project_hp hp)).
Proof. intros. generalize dependent e. generalize dependent T. induction hp.
intros. simpl. unfold project_hp. unfold marked_heap'. unfold marked_heap. rewrite->H0. reflexivity.
intros. unfold project_hp. rewrite->marked_heap'_hd. simpl. rewrite->H0. destruct a. remember (SecLang.label t) as BB.
destruct BB. rewrite->marked_heap_L. simpl. rewrite<-HeqBB. rewrite->add_both_mark_hd. simpl. assert (0<=1). apply le_S.
apply le_n. apply marked_heap_add_both_mark with (hp:=hp) in H1. simpl in H1. rewrite->H1. reflexivity. symmetry. apply HeqBB.
simpl. rewrite<-HeqBB. assert (1<=1). apply le_n. apply marked_heap_add_both_mark with (hp:=hp) in H1.
rewrite->H1. reflexivity.
Qed.
(*#######################################################*)
Lemma same_mark_marked_heap:forall hp hp',
same_mark (project_hp hp)(project_hp hp') = true ->
same_mark (marked_heap (marked_heap' hp 1) 1)(marked_heap (marked_heap' hp' 1) 1) = true.
Proof. intros. assert (marked_heap (marked_heap' hp 1) 1 = add_fst_mark (project_hp hp)).
unfold project_hp. symmetry. apply marked_heap_add_fst_mark. apply le_n. rewrite->H1. clear H1.
assert (add_fst_mark (project_hp hp') = marked_heap (marked_heap' hp' 1) 1). unfold project_hp.
apply marked_heap_add_fst_mark. apply le_n. rewrite<-H1. clear H1.
apply add_fst_mark_same_mark. apply H0.
Qed.

(**
Lemma same_mark_marked_heap_generalize_1:forall n hp hp',
same_mark (marked_heap(marked_heap' hp 0)0)(marked_heap(marked_heap' hp' 0)0) = true ->
same_mark (marked_heap (marked_heap' hp 0) n)(marked_heap (marked_heap' hp' 0) n) = true.
Proof. intros n. induction n.
Case ("n=0").  intros. apply H0.
Case ("n=S n'"). intros. rewrite<-marked_heap_minus_snd_mark. rewrite<-marked_heap_minus_snd_mark.
               apply minus_snd_mark_same_mark. apply IHn. apply H0.
Qed.
*)              



Lemma same_mark_marked_heap_generalize:forall hp hp' n1 n2,
n2<=n1 ->
same_mark (marked_heap(marked_heap' hp 0)0)(marked_heap(marked_heap' hp' 0)0) = true ->
same_mark (marked_heap (marked_heap' hp n1) n2)(marked_heap (marked_heap' hp' n1) n2) = true.
Proof. intros. generalize dependent n2. generalize dependent hp. generalize dependent hp'.
induction n1.
Case ("n1=0"). intros. destruct n2. apply H1. inversion H0.
Case ("n1=S n"). intros. destruct n2. assert (0<=n1). apply SecLang.zero_n.
                 assert (S n1 = n1 +1). rewrite->plus_comm. reflexivity. rewrite->H3.
                 clear H3. assert (0<=n1). apply H2. apply marked_heap_add_both_mark with (hp:=hp)in H2.
                 rewrite<-H2. clear H2. apply marked_heap_add_both_mark with (hp:=hp') in H3. rewrite<-H3.
                 clear H3. apply IHn1 with (n2:=0)in H1. apply add_both_mark_same_mark'.
                 apply H1. apply SecLang.zero_n. apply SecLang.lt_snoc_1 in H0. assert (n2<=n1). apply H0. assert (n2<=n1). apply H0.
                 apply marked_heap_add_fst_mark with(hp:=hp)in H0. apply marked_heap_add_fst_mark with(hp:=hp')in H2.
                 assert (S n1 = n1 + 1). rewrite->plus_comm. reflexivity. rewrite->H4. clear H4. assert (S n2 = n2 + 1).
                 rewrite->plus_comm. reflexivity. rewrite->H4. clear H4. rewrite<-H0. clear H0. rewrite<-H2. clear H2. 
                 apply IHn1 with (n2:=n2)in H1.  apply add_fst_mark_same_mark'. apply H1. apply H3.
Qed.





(*########################################################*)

Lemma same_mark_Sameext:forall hp hp' a,
same_mark (project_hp hp)(project_hp hp') = true ->
same_mark (project_hp (a :: hp))(project_hp (a :: hp')) = true.
Proof. intros. destruct a. remember (SecLang.label t) as BB. destruct BB.
       symmetry in HeqBB. assert (SecLang.label t = L). apply HeqBB. 
       apply add_both_mark_L with (T:=t0)(hp:=hp)in HeqBB. rewrite->HeqBB.
       apply add_both_mark_L with (T:=t0)(hp:=hp')in H1. rewrite->H1.
       simpl. apply add_both_mark_same_mark. apply H0. unfold project_hp.
       simpl. rewrite<-HeqBB. 
       assert (add_fst_mark (project_hp hp) = marked_heap (marked_heap' hp 1) 1).
       unfold project_hp. apply marked_heap_add_fst_mark. apply le_n. rewrite<-H1. clear H1.
       assert (add_fst_mark (project_hp hp') = marked_heap (marked_heap' hp' 1) 1).
       unfold project_hp. apply marked_heap_add_fst_mark. apply le_n. rewrite<-H1.
       apply add_fst_mark_same_mark. apply H0.
Qed.

(*###########*)
Lemma project_hp_Sameext:forall hp hp' a,
project_hp hp = project_hp hp' ->
project_hp (a::hp) = project_hp (a::hp').
Proof. intros. destruct a. remember (SecLang.label t) as BB. destruct BB. unfold project_hp.
rewrite->marked_heap'_hd. rewrite->marked_heap'_hd. simpl. rewrite<-HeqBB. unfold project_hp in H0.
assert (0<=0). apply le_n. assert (0<=0). apply le_n. apply marked_heap_add_both_mark with (hp:=hp) in H1.
apply marked_heap_add_both_mark with (hp:=hp') in H2. simpl in H1. simpl in H2. rewrite<-H1. rewrite<-H2.
rewrite->H0. reflexivity. unfold project_hp. simpl. rewrite<-HeqBB. unfold project_hp in H0. assert (0<=0). apply le_n.
assert (0<=0). apply le_n. apply marked_heap_add_fst_mark with (hp:=hp) in H1. apply marked_heap_add_fst_mark with (hp:=hp') in H2.
simpl in H1. simpl in H2. rewrite<-H1. rewrite<-H2. rewrite->H0. reflexivity.
Qed.

(*the projection of a heap equals that of the heap itself*)
Lemma project_hp_Hextend:forall v hp T,
SecLang.value v ->
project_hp hp = project_hp (SecLang.snoc hp (SecLang.joinvs v H,T)).
Proof. intros. generalize dependent T. generalize dependent v. induction hp.
Case ("nil"). intros. simpl. inversion H0. subst. rewrite->SecLang.join_tcon_b. rewrite->SecLang.joins_refl.
              simpl. compute. reflexivity. subst. rewrite->SecLang.join_tabs_b. rewrite->SecLang.joins_refl.
              simpl. compute. reflexivity. subst. rewrite->SecLang.join_tunit_b. rewrite->SecLang.joins_refl.
              simpl. compute. reflexivity. subst. rewrite->SecLang.join_tloc_b. rewrite->SecLang.joins_refl.
              simpl. compute. reflexivity.
Case ("h::t"). intros. simpl. apply project_hp_Sameext. apply IHhp. apply H0.
Qed.   


Lemma project_hp_Lextend:forall v hp T,
SecLang.value v ->
SecLang.label v = L ->
project_hp (SecLang.snoc hp (v,T)) = LowLang.snoc (project_hp hp) ((project_e v,T),(length hp,length (project_hp hp))).
Proof. intros. generalize dependent v. generalize dependent T. induction hp.
Case ("nil"). intros. unfold project_hp. simpl. rewrite->H1. reflexivity.
Case ("h::t"). intros. simpl. unfold project_hp. destruct a. simpl. remember (SecLang.label t) as BB. destruct BB.
              simpl. assert (0<=0). apply le_n. apply marked_heap_add_both_mark with(hp:=SecLang.snoc hp (v,T))in H2.
              simpl in H2. rewrite<-H2. clear H2. assert (0<=0). apply le_n. 
              apply marked_heap_add_both_mark_snoc with(hp:=hp)(n3:=length hp)(n4:=length (marked_heap(marked_heap' hp 1)0))(V:=project_e v)(T:=T)in H2.
              simpl in H2. rewrite<-H2. clear H2. rewrite->marked_heap_mark_length with(n3:=0)(n4:=0). apply IHhp with(T:=T)in H0. unfold project_hp in H0.
              rewrite<-H0. reflexivity. apply H1.
              assert (0<=0). apply le_n. apply marked_heap_add_fst_mark with(hp:=SecLang.snoc hp (v,T))in H2.
              simpl in H2. rewrite<-H2. clear H2. assert (0<=0). apply le_n.
              apply marked_heap_add_fst_mark_snoc with(hp:=hp)(n3:=length hp)(n4:=length(marked_heap(marked_heap' hp 1)1))(V:=project_e v)(T:=T)in H2.
              simpl in H2. rewrite<-H2. clear H2.
              rewrite->marked_heap_mark_length with(n3:=0)(n4:=0).   unfold project_hp in IHhp. apply IHhp with(T:=T)in H0. rewrite<-H0. reflexivity.
              apply H1.
Qed.

              
(**
the projection of a heap equals that of the heap with some of its high cell
being over-written by a high value
*)
Lemma project_hp_Hoverwrite:forall n hp t T,
n < length hp ->
SecLang.value t ->
subsum_r H (SecLang.label (SecLang.efst (SecLang.heap_lookup n hp))) ->
project_hp hp = project_hp (SecLang.heap_replace n (SecLang.joinvs t H,T) hp).
Proof. intros. generalize dependent n. generalize dependent t. generalize dependent T. induction hp.
Case ("nil"). intros. simpl. destruct n. simpl. reflexivity. inversion H0.
Case ("h::t"). intros. destruct n. simpl. simpl in H2. destruct a. unfold project_hp. rewrite->marked_heap'_hd.
              rewrite->marked_heap'_hd. simpl. inversion H2. subst. inversion H1. rewrite->SecLang.join_tcon_b.
              rewrite->SecLang.joins_refl. simpl. reflexivity. rewrite->SecLang.join_tabs_b. rewrite->SecLang.joins_refl.
              simpl. reflexivity. rewrite->SecLang.join_tunit_b. rewrite->SecLang.joins_refl. simpl. reflexivity.
              rewrite->SecLang.join_tloc_b. rewrite->SecLang.joins_refl. simpl. reflexivity. simpl. apply project_hp_Sameext.
              apply IHhp. apply H1. simpl in H0. apply LowLang.lt_snoc_1 in H0. apply H0. simpl in H2. apply H2.
Qed.
Lemma lt_S_n:forall n n',
S n < S n' ->
n < n'.
Proof. intros. apply LowLang.lt_snoc_1 in H0. apply H0.
Qed.
Lemma project_hp_Loverwrite:forall n hp t T,
n < length hp ->
SecLang.value t ->
SecLang.label t = L ->
SecLang.label (SecLang.efst (SecLang.heap_lookup n hp)) = L ->
same_mark (project_hp hp)(project_hp (SecLang.heap_replace n (t,T) hp)) = true.
Proof. intros. generalize dependent n. generalize dependent t. generalize dependent T.
induction hp.
Case ("nil"). intros. destruct n. simpl in H0. apply LowLang.lt_same_F in H0. inversion H0. inversion H0.
Case ("h::t"). intros. destruct n. simpl. simpl in H3. destruct a. apply add_both_mark_L with (T:=t1)(hp:=hp) in H3.
              rewrite->H3. apply add_both_mark_L with (T:=T)(hp:=hp) in H2. rewrite->H2. simpl. apply same_mark_refl.
              simpl. apply same_mark_Sameext. apply IHhp. apply H1. apply H2. simpl in H0.
              apply lt_S_n. apply H0. simpl in H3. apply H3.
Qed.

(**
Now how about the projection of a heap versus that of the heap with some of its
low cell being over-written by 
the projection of a heap equals that of the heap with some of its high cell
being over-written by a low value

Lemma project_hp_LHoverwrite:forall n hp t T,
n < length hp ->
SecLang.value t ->
subsum_r H (SecLang.label (SecLang.efst (SecLang.heap_lookup n hp))) ->
project_hp hp = project_hp (SecLang.heap_replace n (SecLang.joinvs t H,T) hp).
*)

(**
Note that with the help of [project_e] and [project_hp], the configuration in [SecLang] can be
converted to a term in [LowLang] and a marked heap with mark indicating the positions
of each cell both before and after the projection of the heap.
Now we finish up our job by further project the configuration,rewriting the locations in the term, 
and then erasing all the marks on the heap.

Keep in mind that regarding the rewriting of referred location we have the following
two cases to consider,
a. high cell being over-written by high value
b. low cell being over-written by low value
This,as is discussed later,implies that our further projection w.r.t. the marked
heap simply erases the marks on the heap
*)

(**
Note regarding the further projection of the configuration of term and heap,let us 
consider the following cases:
suppose our unprojected heap in [SecLang] as follows,
[3 L,4 H,5 H,6 L]

a. high cell being over-written by a low value

   tassign (tloc (an int L) 2) 7 / [(3,(0->0)),(6,(3->1))]
   "proj",
   tassign (tloc (an int L) 1) 7 / [(3,(0->0)),(#,(2->1)),(6,(3->2))]
Note that if the type of the pointer is [L] and the location in [tloc] does not
match up with the first element of all markers,the rules  for the game as follows,
firstly find the element whose first number is the lowest number which is bigger
than that in [tloc];then insert some arbitrary element together with its mark 
to the heap;finally replace the location in [tloc] with the location of the inserted
cell on the heap

Note that we can actually use a much simply fix,
we can replace the low value with [tH],treating it as a high value and then
change the referred location to be the length of the heap,transforming the case
to the case where a high cell is being over-written by a high value

Note: for now this case is excluded from our consideration

b. high cell being over-written by a high value
   tassign (tloc (an int H) 2) 7 / [(3,0->0),(6,3->1)] 
   "proj",
   tassign (tloc (an int H) 2) 7 / [(3,0->0),(6,3->1)]
Recall [st_assign] that the value being written onto the heap is guarded also by
the label of the referred type which is [H] in this case. It follows that whatever
gets written onto the heap, it must have high label and therefore must not appear
in the projected heap. Therefore in the current case we need not further project
the configuration to change the location in [tloc] and the corresponding heap in case
where the number in [tloc] does not match up with all the marks

c. low cell being over-written by a low value
   tassign (tloc (an int L) 3) 7 / [(3,0->0),(6,3->1)]
   "proj"
   tassign (tloc (an int L) 1) 7 / [(3,0->0),(6,3->1)]
Note that in case the number in [tloc] matches up with some mark in the heap,
we simply replace that number by the second number in the mark while leaving 
the heap unchanged. By doing so we can then specify reduction rules in [LowLang]
which over-writes the corresponding cell on the heap. 

In conclusion, the only case where both the marked heap and the location in [tloc]
need to be modified is that both the referred type of the pointer and the value being
written have low security.  
*)

(*
Note we proceed as follows,
1. we specify some list functions to help us to manipulate our marked heap
   so that we can insert cell in the heap then mark that cell with
   the right mark and after that replace the location in [tloc] correctly
2. combine the projections together
*)

(*some useful list operations*)
(**
a. given a number and a marked heap return the location of the cell 
  whose first number is the smallest one among all that are bigger 
  than that number;if there is a match,however,the second number of the
  mark of the matched cell is returned
  
  the function relies upon the assumption that the input heap is such that
  the first numbers of the marker are in ascending order from left to right
  moreover the second number of the marker corresponds to the location of 
  that cell on the heap
*)

Fixpoint return_smallest_match (n:nat)(hp:list ((LowLang.tm*Ty)*(nat*nat))) : bool*(nat*nat) :=
match hp with
| h :: t => match h with
            | (fst,snd) => match snd with
                           | (n1,n2) =>if beq_nat n1 n
                                      then (false,(n,n2))                              
                                      else return_smallest_match n t
                           end
            end
| nil => (true,(n,n))
end.
(*some examples*)
Example test_return_smallest_match_1:
return_smallest_match 1 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: ((LowLang.tcon 7,an int L),(3,2)) :: nil)
= (true,(1,1)).
Proof. simpl. reflexivity. Qed.
(**
Note in [test_return_smallest_match_1],no match and the position of the cell the
first number of whose marker is bigger is one,hence returning [(true,1)]
*)
Example test_return_smallest_match_2:
return_smallest_match 2 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
= (false,(2,1)).
Proof. simpl. reflexivity. Qed.
(**
Note in [test_return_smallest_match_2], a match is obtained and the second number
of the marker is returned
*)
Example test_return_smallest_match_3:
return_smallest_match 100 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
= (true,(100,100)).
Proof. simpl. reflexivity. Qed.

(*some lemmas regarding [return_smallest_match]*)
Lemma return_smallest_match_true'':forall n n',
beq_nat n (n' + (S n)) = false.
Proof. intros. generalize dependent n'. induction n.
intros. rewrite->plus_comm. simpl. reflexivity. intros.
rewrite<-plus_n_Sm. simpl. apply IHn.
Qed.

Lemma return_smallest_match_true':forall hp n1 n2,
return_smallest_match ((length hp)+n1)(marked_heap(marked_heap' hp n1)n2)
=(true,(length hp + n1,length hp + n1)).
Proof. intros hp. induction hp.
Case ("nil"). intros. simpl. reflexivity.
Case ("h::t"). intros. destruct a. simpl. destruct n1. simpl. remember (SecLang.label t) as BB.
              destruct BB. simpl. specialize (IHhp 1 n2). rewrite->plus_comm in IHhp. simpl in IHhp.
              rewrite->plus_comm. simpl. apply IHhp. specialize (IHhp 1 (S n2)). rewrite->plus_comm in IHhp.
              simpl in IHhp. rewrite->plus_comm. simpl. apply IHhp. simpl. remember (SecLang.label t) as BB.
              destruct BB. destruct n2. simpl. rewrite->return_smallest_match_true''.
              rewrite->plus_n_Sm. specialize (IHhp (S (S n1)) 0). apply IHhp. simpl. rewrite->return_smallest_match_true''.
              rewrite->plus_n_Sm. specialize (IHhp (S (S n1)) (S n2)). apply IHhp. rewrite->plus_n_Sm. specialize (IHhp (S (S n1))(S n2)).
              apply IHhp.
Qed.
                           
Lemma return_smallest_match_true:forall hp,
return_smallest_match (length hp)(project_hp hp) = (true,(length hp,length hp)).
Proof. unfold project_hp. intros. 
       assert ((length hp) + 0 = length hp). rewrite->plus_comm. reflexivity.
       rewrite<-H0. clear H0. apply return_smallest_match_true'.
Qed.

Lemma Hlabel_tH:forall t,
SecLang.label t = H ->
project_e t = LowLang.tH.
Proof. intros t. induction t.
Case ("tvar"). intros. inversion H0.
Case ("tprot"). intros. destruct s. simpl. assert (SecLang.label (SecLang.tprot L t) = SecLang.label t). reflexivity. rewrite->H1 in H0.
                apply IHt. apply H0. simpl. reflexivity.
Case ("tcon"). intros. destruct s. inversion H0. simpl. reflexivity.
Case ("tabs"). intros. destruct s. inversion H0. simpl. reflexivity.
Case ("tapp"). intros. inversion H0.
Case ("tunit"). intros. destruct s. inversion H0. simpl. reflexivity.
Case ("tref"). intros. destruct s. inversion H0. simpl. reflexivity.
Case ("tderef"). intros.  inversion H0.
Case ("tloc"). intros. destruct s. inversion H0. simpl. reflexivity.
Case ("tassign"). intros. inversion H0.
Qed.  
Lemma return_smallest_match_Sn_n:forall n n0 n1 n2 hp,
fst (return_smallest_match (S n) (marked_heap (marked_heap' hp (S n0)) n1))
= fst (return_smallest_match n (marked_heap (marked_heap' hp n0) n2)).
Proof. intros. generalize dependent n. generalize dependent n0. generalize dependent n1. generalize dependent n2.
induction hp.
Case ("nil"). intros. reflexivity.
Case ("h::t"). intros. destruct a. simpl. remember (SecLang.label t) as BB. destruct BB.  destruct n1. destruct n0. simpl.
               destruct n. rewrite<-HeqBB. simpl. reflexivity. rewrite<-HeqBB. simpl. specialize (IHhp n2 0 1 (S n)). apply IHhp.
               simpl. rewrite<-HeqBB. destruct n. destruct n2. simpl. specialize (IHhp 0 0 (S (S n0)) 0). apply IHhp. simpl. 
               specialize (IHhp (S n2) 0 (S (S n0)) 0). apply IHhp. destruct n2. simpl. remember (beq_nat n0 n) as CC. destruct CC.
               reflexivity. specialize (IHhp 0 0 (S (S n0)) (S n)). apply IHhp. simpl. remember (beq_nat n0 n) as CC. destruct CC.
               reflexivity. specialize (IHhp (S n2) 0 (S (S n0)) (S n)). apply IHhp. simpl. destruct n0. simpl. rewrite<-HeqBB. simpl.
               destruct n. reflexivity. specialize (IHhp n2 (S n1) 1 (S n)). apply IHhp. simpl. rewrite<-HeqBB. destruct n2. simpl. destruct n.
               specialize (IHhp 0 (S n1) (S (S n0)) 0). apply IHhp. remember (beq_nat n0 n) as CC. destruct CC. reflexivity. specialize (IHhp 0 (S n1) (S (S n0)) (S n)). apply IHhp.
               simpl. destruct n. specialize (IHhp (S n2) (S n1) (S (S n0)) 0). apply IHhp. remember (beq_nat n0 n) as CC. destruct CC. reflexivity. specialize (IHhp (S n2) (S n1) (S (S n0)) (S n)). apply IHhp.
               destruct n0. simpl. rewrite<-HeqBB. specialize (IHhp (S n2) (S n1) 1 n). apply IHhp. simpl. rewrite<-HeqBB. specialize (IHhp (S n2) (S n1) (S (S n0)) n). apply IHhp.
Qed.  

Lemma return_smallest_match_Sn_Sn:forall n n0 n1 n2 hp,
fst (return_smallest_match (S n) (marked_heap (marked_heap' hp (S n0))(S n1)))
= fst (return_smallest_match n (marked_heap (marked_heap' hp n0) n2)).
Proof. intros. generalize dependent n. generalize dependent n0. generalize dependent n1. generalize dependent n2.
induction hp.
Case ("nil"). intros. reflexivity.
Case ("h::t"). intros. destruct a. simpl. remember (SecLang.label t) as BB. destruct BB.  destruct n0. simpl. destruct n.
               rewrite<-HeqBB. simpl. reflexivity. rewrite<-HeqBB. simpl. specialize (IHhp n2 n1 1 (S n)). apply IHhp.
               simpl. rewrite<-HeqBB. destruct n. destruct n2. simpl. specialize (IHhp 0 n1 (S (S n0)) 0). apply IHhp. simpl. 
               specialize (IHhp (S n2) n1 (S (S n0)) 0). apply IHhp. destruct n2. simpl. remember (beq_nat n0 n) as CC. destruct CC.
               destruct n1. reflexivity. reflexivity.
               specialize (IHhp 0 n1 (S (S n0)) (S n)). apply IHhp. simpl. remember (beq_nat n0 n) as CC. destruct CC. destruct n1. reflexivity.
               reflexivity. specialize (IHhp (S n2) n1 (S (S n0)) (S n)). apply IHhp. destruct n0. simpl. rewrite<-HeqBB. simpl.
               specialize (IHhp (S n2) (S n1) 1 n). apply IHhp. simpl. rewrite<-HeqBB. specialize (IHhp (S n2)(S n1)(S (S n0)) n). apply IHhp.
Qed.

Lemma return_smallest_match_snd_Sn_Sn:forall n n0 n1 hp,
fst (return_smallest_match n (marked_heap (marked_heap' hp n0) n1)) = false ->
snd(snd(return_smallest_match (S n) (marked_heap (marked_heap' hp (S n0))(S n1))))
=snd(snd(return_smallest_match n (marked_heap (marked_heap' hp n0) n1))).
Proof. intros. generalize dependent n. generalize dependent n0. generalize dependent n1.
induction hp.
Case ("nil"). intros. simpl in H0. inversion H0.
Case ("h::t"). intros. destruct a. simpl. remember (SecLang.label t) as BB. destruct BB.
              destruct n0. simpl. rewrite<-HeqBB. destruct n. simpl. reflexivity. simpl.
              apply IHhp. simpl in H0. rewrite<-HeqBB in H0. simpl in H0. apply H0.
              simpl. rewrite<-HeqBB. destruct n1. destruct n. apply IHhp. simpl in H0. rewrite<-HeqBB in H0.
            simpl in H0. apply H0. remember (beq_nat n0 n) as CC. destruct CC. simpl. rewrite<-HeqCC. simpl.
              reflexivity. simpl. rewrite<-HeqCC. apply IHhp. simpl in H0. rewrite<-HeqBB in H0. simpl in H0.
              rewrite<-HeqCC in H0. apply H0. destruct n. simpl. apply IHhp. simpl in H0. rewrite<-HeqBB in H0.
              apply H0. remember (beq_nat n0 n) as CC. destruct CC. simpl. rewrite<-HeqCC. simpl. reflexivity.
              simpl. rewrite<-HeqCC. apply IHhp. simpl in H0. rewrite<-H0. rewrite<-HeqBB. simpl. rewrite<-HeqCC.
             reflexivity. destruct n0. simpl. rewrite<-HeqBB. apply IHhp. simpl in H0. rewrite<-HeqBB in H0.
             apply H0. simpl. rewrite<-HeqBB. apply IHhp. simpl in H0. rewrite<-HeqBB in H0. apply H0.
Qed.               
            
Lemma return_smallest_match_snd_Sn_n:forall hp n n0 n1,
n1 <= n0 ->
snd (snd (return_smallest_match (S n) (marked_heap (marked_heap' hp (S n0)) n1)))
=S (snd (snd (return_smallest_match n (marked_heap (marked_heap' hp n0) n1)))).
Proof. intros hp. induction hp.
Case ("nil"). intros. reflexivity.
Case ("h::t"). intros. destruct a. simpl. remember (SecLang.label t) as BB. destruct BB.
              destruct n1. destruct n0. simpl. rewrite<-HeqBB. simpl. destruct n. reflexivity.
              specialize (IHhp (S n) 1 0). apply IHhp. apply le_S. apply le_n. simpl. rewrite<-HeqBB. simpl. destruct n. 
              specialize (IHhp 0 (S (S n0)) 0). apply IHhp. apply le_S. apply H0.  remember (beq_nat n0 n) as CC. destruct CC. 
              reflexivity. specialize (IHhp (S n) (S (S n0)) 0). apply IHhp.  apply le_S. apply H0. simpl.
              destruct n0.  simpl. rewrite<-HeqBB.  simpl. destruct n. inversion H0. specialize (IHhp (S n) 1 (S n1)). apply IHhp.  inversion H0.
              simpl. rewrite<-HeqBB. simpl. destruct n. specialize (IHhp 0 (S (S n0)) (S n1)). apply IHhp. apply le_S. apply H0.
              remember (beq_nat n0 n) as CC. destruct CC. destruct n1. rewrite<-minus_n_O. reflexivity.
              simpl. rewrite->minus_Sn_m. reflexivity. apply LowLang.lt_same_F'. apply H0.
              specialize (IHhp (S n) (S (S n0)) (S n1)). apply IHhp. apply le_S. apply H0. destruct n0. simpl. rewrite<-HeqBB. 
              specialize (IHhp n 1 (S n1)). apply IHhp. apply SecLang.n_iff_Sn_left in H0. apply H0.
              simpl. rewrite<-HeqBB. specialize (IHhp n (S (S n0)) (S n1)). apply IHhp. apply SecLang.n_iff_Sn_left in H0. apply H0.
Qed.


Lemma n_le_minus_n':forall n n',
n - n' <= n.
Proof. intros. generalize dependent n'. induction n.
Case ("nil"). intros. simpl. apply le_n.
Case ("h::t"). intros. destruct n'. simpl. apply le_n. simpl. apply le_S.
              apply IHn.
Qed.
Lemma return_smallest_match_fst_snd':forall n n1 n2 hp,
snd(snd(return_smallest_match n (marked_heap(marked_heap' hp n1)n2))) <= n.
Proof. intros. generalize dependent n. generalize dependent n1. generalize dependent n2.
      induction hp.
Case ("nil"). intros. simpl. apply le_n.
Case ("h::t"). intros. destruct a. simpl. destruct n1. simpl. remember (SecLang.label t) as BB. 
              destruct BB. simpl. destruct n. simpl. apply le_n. specialize (IHhp n2 1 (S n)).
              apply IHhp. specialize (IHhp (S n2) 1 n). apply IHhp. simpl. remember (SecLang.label t) as BB.
              destruct BB. destruct n2. simpl. destruct n. specialize (IHhp 0 (S (S n1)) 0). apply IHhp.
              remember (beq_nat n1 n) as CC. destruct CC. simpl. apply beq_nat_eq in HeqCC.
              subst. apply le_n. specialize (IHhp 0 (S (S n1)) (S n)). apply IHhp. simpl. destruct n.
              specialize (IHhp (S n2)(S (S n1)) 0). apply IHhp. remember (beq_nat n1 n) as CC. destruct CC.
              simpl. apply beq_nat_eq in HeqCC. subst. apply le_S. apply n_le_minus_n'.
              specialize (IHhp (S n2) (S (S n1)) (S n)). apply IHhp. specialize (IHhp (S n2)(S (S n1)) n). apply IHhp.
Qed.

Lemma return_smallest_match_fst_snd:forall n hp,
snd(snd(return_smallest_match n (project_hp hp))) <= n.
Proof. unfold project_hp. intros. apply return_smallest_match_fst_snd'.
Qed.
 
              

Lemma project_hp_le_length:forall hp,
length (project_hp hp) <= length hp.
Proof. intros hp. induction hp. 
Case ("nil"). simpl. apply le_n.
Case ("h::t"). unfold project_hp. destruct a. simpl. remember (SecLang.label t) as BB.
              destruct BB. simpl. apply SecLang.n_iff_Sn_left. rewrite->marked_heap_mark_length with (n3:=0)(n4:=0).
              apply IHhp. apply le_S. rewrite->marked_heap_mark_length with (n3:=0)(n4:=0).
              apply IHhp.
Qed.

Lemma return_smallest_match_project_e_true:forall n hp,
n < length hp ->
fst(return_smallest_match n (project_hp hp)) = true ->
project_e (SecLang.efst (SecLang.heap_lookup n hp)) = LowLang.tH.
Proof. intros. generalize dependent n. induction hp.
Case ("nil"). intros. simpl in H0. destruct n. apply LowLang.lt_same_F in H0. inversion H0.
              inversion H0.
Case ("h::t"). intros.  destruct n. destruct a. simpl. unfold project_hp in H1. simpl in H1. remember (SecLang.label t) as BB. destruct BB.
               simpl in H1. inversion H1. apply Hlabel_tH. symmetry. apply HeqBB. simpl. apply IHhp. simpl in H0. apply lt_S_n in H0. apply H0.
               unfold project_hp. unfold project_hp in H1. destruct a. simpl in H1. remember (SecLang.label t) as BB. destruct BB. simpl in H1.
               assert (fst (return_smallest_match (S n)(marked_heap (marked_heap' hp 1) 0)) = fst (return_smallest_match n (marked_heap (marked_heap' hp 0) 0))).
               apply return_smallest_match_Sn_n. rewrite<-H2. apply H1.
               assert (fst (return_smallest_match (S n)(marked_heap (marked_heap' hp 1) 1)) = fst (return_smallest_match n (marked_heap (marked_heap' hp 0) 0))).
               apply return_smallest_match_Sn_n. rewrite<-H2. apply H1.
Qed.
(*###################*)
Lemma return_smallest_match_hit'':forall n m,
ble_nat n m = ble_nat (S n)(S m).
Proof. intros n. induction n. intros. simpl. reflexivity.
intros. simpl. destruct m. reflexivity. reflexivity.
Qed.

Lemma return_smallest_match_hit':forall n,
ble_nat (S n) n = false.
Proof. intros. induction n. simpl. reflexivity. simpl. destruct n. reflexivity.
       rewrite->return_smallest_match_hit''. apply IHn.
Qed.
(*####################*)      
Lemma return_true_marked_heap:forall hp n n1 n2,
n < n1 ->
true = fst (return_smallest_match n (marked_heap (marked_heap' hp n1) n2)).
Proof. intros hp. induction hp.
Case ("nil"). intros. simpl. reflexivity.
Case ("h::t"). intros. destruct n. destruct a. simpl. destruct n1. apply LowLang.lt_same_F in H0.
               inversion H0. simpl. destruct n2.
               remember (SecLang.label t) as BB. destruct BB. simpl. apply IHhp. apply le_S in H0. 
               apply H0. apply IHhp. apply le_S in H0. apply H0. 
               remember (SecLang.label t) as BB. destruct BB. simpl. apply IHhp. apply le_S in H0. apply H0.
               apply IHhp. apply le_S in H0. apply H0. destruct a. simpl. destruct n1. inversion H0. simpl.
               destruct n2.
               remember (SecLang.label t) as BB. destruct BB. simpl. assert (n<>n1). intros contra. rewrite->contra in H0.
               apply LowLang.lt_same_F in H0. inversion H0. apply not_eq_beq_false in H1. rewrite->beq_nat_sym in H1. rewrite->H1.
               apply IHhp. apply le_S in H0. apply H0. apply IHhp. apply le_S in H0. apply H0. 
               remember (SecLang.label t) as BB. destruct BB. simpl. 
                assert (n<>n1). intros contra. rewrite->contra in H0.
               apply LowLang.lt_same_F in H0. inversion H0. apply not_eq_beq_false in H1. rewrite->beq_nat_sym in H1. rewrite->H1.
               apply IHhp. apply le_S in H0. apply H0. apply IHhp. apply le_S in H0. apply H0.
Qed.

Lemma return_smallest_match_hit:forall n n' L hp,
return_smallest_match n ((L,(n,n')) :: hp) = (false,(n,n')).
Proof. intros. simpl. destruct n. reflexivity. rewrite<-beq_nat_refl.
       reflexivity.
Qed.

Lemma return_smallest_match_hit_snoc':forall n n1 n2 L hp,
return_smallest_match ((length hp)+n1) (LowLang.snoc (marked_heap(marked_heap' hp n1)n2) (L,((length hp)+n1,n))) =(false,((length hp)+n1,n)).
Proof. intros. generalize dependent n. generalize dependent n1. generalize dependent n2. generalize dependent L0.
induction hp.
Case ("nil"). intros.  simpl. rewrite<-beq_nat_refl. reflexivity.
Case ("h::t"). intros. destruct a. simpl. destruct n1. simpl. remember (SecLang.label t) as BB.  destruct BB.
              simpl. rewrite->plus_comm. simpl. specialize (IHhp L0 n2 1 n). rewrite->plus_comm in IHhp. simpl in IHhp.
              apply IHhp. rewrite->plus_comm. simpl. specialize (IHhp L0 (S n2) 1 n). rewrite->plus_comm in IHhp. simpl in IHhp.
              apply IHhp. simpl. remember (SecLang.label t) as BB. destruct BB. destruct n2. simpl. rewrite->return_smallest_match_true''.
              rewrite->plus_n_Sm. specialize (IHhp L0 0 (S (S n1)) n). apply IHhp. simpl. rewrite->return_smallest_match_true''.
              rewrite->plus_n_Sm. specialize (IHhp L0 (S n2)(S (S n1)) n). apply IHhp. rewrite->plus_n_Sm. specialize (IHhp L0 (S n2)(S (S n1)) n).
              apply IHhp. 
Qed. 
Lemma return_smallest_match_hit_snoc:forall n L hp,
return_smallest_match (length hp)(LowLang.snoc (project_hp hp)(L,(length hp,n)))
=(false,(length hp,n)).
Proof. intros. unfold project_hp. assert (length hp = (length hp) + 0). rewrite->plus_comm. reflexivity.
       rewrite->H0. clear H0. apply return_smallest_match_hit_snoc'.
Qed.

Lemma return_smallest_match_project_hp_hit:forall n hp,
n < length hp ->
SecLang.label (SecLang.efst (SecLang.heap_lookup n hp)) = L ->
fst (return_smallest_match n (project_hp hp)) = false.
Proof. intros. generalize dependent n. induction hp.
Case ("nil"). intros. destruct n. simpl in H0. apply LowLang.lt_same_F in H0. inversion H0.
             simpl in H0. inversion H0.
Case ("h::t"). intros. destruct a. unfold project_hp. simpl. remember (SecLang.label t) as BB.
             destruct BB. destruct n. simpl. reflexivity. simpl. 
             rewrite->return_smallest_match_Sn_n with (n2:=0). apply IHhp.
             simpl in H0. apply lt_S_n in H0. apply H0. simpl in H1. apply H1.
             destruct n. simpl in H1. rewrite<-HeqBB in H1. inversion H1. 
             rewrite->return_smallest_match_Sn_n with (n2:=0). apply IHhp.
             simpl in H0. apply lt_S_n in H0. apply H0. simpl in H1. apply H1.
Qed.

Lemma return_smallest_match_project_hp_not_hit:forall n hp,
n < length hp ->
SecLang.label (SecLang.efst (SecLang.heap_lookup n hp)) = H ->
fst (return_smallest_match n (project_hp hp)) = true.
Proof. intros. generalize dependent n. induction hp.
Case ("nil"). intros. destruct n. simpl in H0. apply LowLang.lt_same_F in H0. inversion H0.
             simpl in H0. inversion H0.
Case ("h::t"). intros. destruct a. unfold project_hp. simpl. remember (SecLang.label t) as BB.
             destruct BB. simpl. destruct n. simpl in H1. rewrite<-HeqBB in H1. inversion H1.
             rewrite->return_smallest_match_Sn_n with (n2:=0). apply IHhp.
             simpl in H0. apply lt_S_n in H0. apply H0. simpl in H1. apply H1.
             destruct n. assert (0<1). apply le_n. apply return_true_marked_heap with(hp:=hp)(n2:=1)in H2.
             symmetry. apply H2.
             rewrite->return_smallest_match_Sn_Sn with (n2:=0). apply IHhp.
             simpl in H0. apply lt_S_n in H0. apply H0. simpl in H1. apply H1.
Qed.

Lemma return_smallest_match_F_length:forall n hp,
fst (return_smallest_match n (project_hp hp)) = false ->
n < length hp.
Proof. intros. generalize dependent n. induction hp.
Case ("nil"). intros. simpl in H0. inversion H0.
Case ("h::t"). intros. destruct a. unfold project_hp in H0. simpl in H0. remember (SecLang.label t) as BB. 
               destruct BB. destruct n. simpl. apply SecLang.n_iff_Sn_left. apply SecLang.zero_n.
              simpl in H0. rewrite->return_smallest_match_Sn_n with(n2:=0)in H0. apply IHhp in H0.
              simpl. apply SecLang.n_iff_Sn_left. apply H0. destruct n. simpl. apply SecLang.n_iff_Sn_left.
              apply SecLang.zero_n. rewrite->return_smallest_match_Sn_Sn with(n2:=0) in H0. apply IHhp in H0.
              simpl. apply SecLang.n_iff_Sn_left. apply H0.
Qed.


              
 
Lemma return_smallest_match_not_hit:forall n1 n2 n3 L hp,
n1 <> n2 ->
return_smallest_match n1 ((L,(n2,n3)) :: hp) = return_smallest_match n1 hp.
Proof. intros. remember (beq_nat n1 n2) as BB. destruct BB. apply beq_nat_eq in HeqBB. 
rewrite->HeqBB in H0. apply LowLang.not_equal_nat in H0. inversion H0. simpl. rewrite->beq_nat_sym.
rewrite<-HeqBB. reflexivity.
Qed.

Lemma return_smallest_match_extend:forall n hp hp' a,
return_smallest_match n hp = return_smallest_match n hp' ->
return_smallest_match n (a :: hp) = return_smallest_match n (a :: hp').
Proof. intros. destruct a. destruct p0. remember (beq_nat n n0) as BB.
destruct BB. simpl. rewrite->beq_nat_sym. rewrite<-HeqBB. reflexivity.
simpl. rewrite->beq_nat_sym. rewrite<-HeqBB. apply H0.
Qed. 

Lemma return_smallest_match_not_hit_snoc:forall n1 n2 n3 L hp,
n1 <> n2 ->
return_smallest_match n1 (LowLang.snoc hp (L,(n2,n3))) = return_smallest_match n1 hp.
Proof. intros. generalize dependent n1. generalize dependent n2. generalize dependent n3.
generalize dependent L0. induction hp.
intros. simpl. remember (beq_nat n2 n1) as BB. destruct BB. apply beq_nat_eq in HeqBB.
rewrite->HeqBB in H0. apply LowLang.not_equal_nat in H0. inversion H0. reflexivity.
intros. assert (LowLang.snoc (a :: hp)(L0,(n2,n3)) = a :: (LowLang.snoc hp (L0,(n2,n3)))). reflexivity.
rewrite->H1. apply return_smallest_match_extend. apply IHhp. apply H0.
Qed. 

Lemma return_smallest_match_miss_one':forall n,
ble_nat n n = true.
Proof. intros. induction n. reflexivity. rewrite<-return_smallest_match_hit''. apply IHn.
Qed.
Lemma not_equal_le_S':forall n1 n2,
(S n1) <> (S n2) ->
n1 <> n2.
Proof. intros n1. destruct n1. intros. destruct n2. assert (1=1). reflexivity. apply H0 in H1. inversion H1.
intros contra. inversion contra. intros. destruct n2. intros contra. inversion contra. intros contra.
assert (S (S n1) = S (S n2)). rewrite->contra. reflexivity. apply H0 in H1. inversion H1.
Qed.
Lemma not_equal_le_S:forall n1 n2,
n1 <> n2 ->
(ble_nat (S n1) n2 = true) \/ (ble_nat (S n2) n1 = true).
Proof. intros n1. induction n1. intros. destruct n2. assert (0=0). reflexivity. apply H0 in H1.
inversion H1. left. simpl. reflexivity. intros. destruct n2. right. simpl. reflexivity.  
apply not_equal_le_S' in H0. apply IHn1 in H0. inversion H0. left. rewrite<-return_smallest_match_hit''.
apply H1. right. rewrite<-return_smallest_match_hit''. apply H1.
Qed.
Lemma return_smallest_match_miss_one'':forall n1 n2,
false = ble_nat (S n1) n2 ->
false = ble_nat (S n2) n1 ->
n1 = n2.
Proof. intros. remember (beq_nat n1 n2) as BB. destruct BB. apply beq_nat_eq in HeqBB. apply HeqBB.
symmetry in HeqBB. apply beq_nat_false in HeqBB. apply not_equal_le_S in HeqBB. inversion HeqBB. rewrite->H2 in H0.
inversion H0. rewrite->H2 in H1. inversion H1.
Qed.
Lemma return_smallest_match_miss_one:forall n n1 n2 L,
n <> n1 ->
return_smallest_match n ((L,(n1,n2)) :: nil)= (true,(n,n)).
Proof. intros. simpl. remember (beq_nat n1 n) as BB. destruct BB. apply beq_nat_eq in HeqBB. symmetry in HeqBB. apply H0 in HeqBB.
inversion HeqBB. reflexivity.      
Qed.
Lemma return_smallest_match_same_mark:forall hp hp' n,
same_mark hp hp' = true ->
fst (return_smallest_match n hp) = fst (return_smallest_match n hp').
Proof. intros hp. induction hp.
intros. destruct hp'. reflexivity. simpl in H0. inversion H0. 
intros. destruct hp'. destruct a. destruct p0. simpl in H0. inversion H0.
        destruct a. destruct p1. destruct p. destruct p1. simpl in H0.
        remember (beq_nat n0 n2) as BB. remember (beq_nat n1 n3) as CC.
        destruct BB. destruct CC. apply beq_nat_eq in HeqBB. apply beq_nat_eq in HeqCC.
        rewrite->HeqBB. rewrite->HeqCC. remember (beq_nat n n2) as DD. destruct DD.
        apply beq_nat_eq in HeqDD. rewrite->HeqDD.  rewrite->return_smallest_match_hit.
        rewrite->return_smallest_match_hit. reflexivity. 
        symmetry in HeqDD. apply beq_nat_false in HeqDD. destruct hp. destruct hp'.
        assert (n<>n2). apply HeqDD. apply return_smallest_match_miss_one with (n2:=n3)(L:=p0)in HeqDD. rewrite->HeqDD.
        apply return_smallest_match_miss_one with (n2:=n3)(L:=p)in H1. rewrite->H1. reflexivity. destruct p1. destruct p2. simpl in H0.
        inversion H0. destruct hp'. destruct p1. destruct p2. simpl in H0. inversion H0. 
        assert (n<>n2). apply HeqDD. apply return_smallest_match_not_hit with (n3:=n3)(L:=p0)(hp:=p1 :: hp) in HeqDD. rewrite->HeqDD.
        apply return_smallest_match_not_hit with (n3:=n3)(L:=p)(hp:=p2 :: hp') in H1. rewrite->H1. apply IHhp. apply H0.
        inversion H0. inversion H0.
Qed.





Lemma return_smallest_match_same_mark':forall hp hp' n,
same_mark hp hp' = true ->
return_smallest_match n hp = return_smallest_match n hp'.
Proof. intros hp. induction hp.
intros. destruct hp'. reflexivity. simpl in H0. inversion H0. 
intros. destruct hp'. destruct a. destruct p0. simpl in H0. inversion H0.
        destruct a. destruct p1. destruct p. destruct p1. simpl in H0.
        remember (beq_nat n0 n2) as BB. remember (beq_nat n1 n3) as CC.
        destruct BB. destruct CC. apply beq_nat_eq in HeqBB. apply beq_nat_eq in HeqCC.
        rewrite->HeqBB. rewrite->HeqCC. remember (beq_nat n n2) as DD. destruct DD.
        apply beq_nat_eq in HeqDD. rewrite->HeqDD.  rewrite->return_smallest_match_hit.
        rewrite->return_smallest_match_hit. reflexivity. 
        symmetry in HeqDD. apply beq_nat_false in HeqDD. destruct hp. destruct hp'.
        assert (n<>n2). apply HeqDD. apply return_smallest_match_miss_one with (n2:=n3)(L:=p0)in HeqDD. rewrite->HeqDD.
        apply return_smallest_match_miss_one with (n2:=n3)(L:=p)in H1. rewrite->H1. reflexivity. destruct p1. destruct p2. simpl in H0.
        inversion H0. destruct hp'. destruct p1. destruct p2. simpl in H0. inversion H0. 
        assert (n<>n2). apply HeqDD. apply return_smallest_match_not_hit with (n3:=n3)(L:=p0)(hp:=p1 :: hp) in HeqDD. rewrite->HeqDD.
        apply return_smallest_match_not_hit with (n3:=n3)(L:=p)(hp:=p2 :: hp') in H1. rewrite->H1. apply IHhp. apply H0.
        inversion H0. inversion H0.
Qed.



(**
Now given a position on the heap for us to insert one extra cell we have to 
specify three functions before constructing the insert function for heap,
c. a function which upon a list and a number returns the prefix of the list 
   till indicated by that number
d. a function which upon a list and a number returns the suffix of the list
   the starting point of which is indicated by that number
b. a function which upon a list increases the second number of its markers by 
   1,the "right shift"
*)

(*b. a function upon a list increase the second number of its markers by one*)
Fixpoint increase_snd (hp:list ((LowLang.tm*Ty)*(nat*nat))) : list ((LowLang.tm*Ty)*(nat*nat)) :=
match hp with
| h :: t => match h with
            | (fst,snd) => match snd with
                           | (n1,n2) => (fst,(n1,n2+1)) :: (increase_snd t)
                           end
            end
| nil => nil
end.
(*some test*)
Example test_increase_snd_1:
increase_snd (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
= (((LowLang.tcon 6,an int L),(0,1)) :: ((LowLang.tcon 5,an int L),(2,2)) :: nil).
Proof. simpl. reflexivity. Qed.

(*c. a function upon a number and a list returns the prefix of the list till
     the location indicated by that number*)
(**
To finish up,we also need to over-write the last element of the list with the following pair,
((tH,an int H),(n,n2)) where [(tH,an int H)] is chosen for [tH] is typable under all
types in [LowLang] while [n] indicates the position of the cell before projection and
[n2] indicates the current position of the cell
*)
Fixpoint prefix_hp (m:nat)(n:nat)(hp:list ((LowLang.tm*Ty)*(nat*nat))) : list ((LowLang.tm*Ty)*(nat*nat)) :=
match hp , n with
| h :: t , S n' => match t with 
                   | h' :: t' => h :: (prefix_hp m n' t)
                   | nil => match h with
                            | (fst,snd) => match snd with
                                           | (n1,n2) =>  h :: ((LowLang.tH,an int H),(m,n2+1)) :: nil
                                           end
                            end
                   end
| h :: t , 0 => match h with
                | (fst,snd) => match snd with
                               | (n1,n2) =>((LowLang.tH,an int H),(m,n2)) :: nil
                               end
                end
| nil , _ => nil (*this branch is never visited*)
end.
(*some examples*)
Example test_prefix_hp_1:
prefix_hp 100 1 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: ((LowLang.tcon 7,an int L),(3,2)) :: nil)
= (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tH,an int H),(100,1)) :: nil).
Proof. simpl. reflexivity. Qed.
Example test_prefix_hp_2:
prefix_hp 100 1 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
= (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tH,an int H),(100,1)) :: nil).
Proof. simpl. reflexivity. Qed.
Example test_prefix_hp_3:
prefix_hp 100 2 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
= (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: ((LowLang.tH,an int H),(100,2)) :: nil).
Proof. simpl. reflexivity. Qed.

(**
d. a function which upon a number returns its suffix starting at the cell
   indicated by that number
*)
Fixpoint suffix_hp (n:nat)(hp:list ((LowLang.tm*Ty)*(nat*nat))) : list ((LowLang.tm*Ty)*(nat*nat)) :=
match hp , n with
| h :: t , S n' => suffix_hp n' t
| h :: t , 0 => h :: t
| nil , _ => nil
end.
(*some examples*)
Example test_suffix_hp_1:
suffix_hp 1 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: ((LowLang.tcon 7,an int L),(3,2)) :: nil)
= (((LowLang.tcon 5,an int L),(2,1)) :: ((LowLang.tcon 7,an int L),(3,2)) :: nil).
Proof. simpl. reflexivity. Qed.
Example test_suffix_hp_2:
suffix_hp 0 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
= (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil).
Proof. simpl. reflexivity. Qed.
Example test_suffix_hp_3:
suffix_hp 1 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
= (((LowLang.tcon 5,an int L),(2,1)) :: nil).
Proof. simpl. reflexivity. Qed.
Example test_suffix_hp_4:
suffix_hp 2 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
= nil.
Proof. simpl. reflexivity. Qed.

(**
Now we can finally specify the insert function for the heap given a number
representing the position to be inserted and the marked heap
*)
(**
Note that the first argument of the following function is a pair where the 
first component of it stands for the location on the heap before projection while
the second the location after
*)
Definition insert_hp (p:nat*nat)(hp:list ((LowLang.tm*Ty)*(nat*nat))) : list ((LowLang.tm*Ty)*(nat*nat)) :=
(prefix_hp (fst p) (snd p) hp) ++ (increase_snd (suffix_hp (snd p) hp)).
(*some examples*)
Example test_insert_hp_1:
insert_hp (1,1) (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
= (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tH,an int H),(1,1)) :: ((LowLang.tcon 5,an int L),(2,2)) :: nil).
Proof.  reflexivity. Qed.
Example test_insert_hp_2:
insert_hp (6,0) (((LowLang.tcon 6,an int L),(7,0)) :: ((LowLang.tcon 5,an int L),(8,1)) :: nil)
= (((LowLang.tH,an int H),(6,0)) :: ((LowLang.tcon 6,an int L),(7,1)) :: ((LowLang.tcon 5,an int L),(8,2)) :: nil).
Proof. reflexivity. Qed.
Example test_insert_hp_3:
insert_hp (100,2) (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
= (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: ((LowLang.tH,an int H),(100,2)) :: nil). 
Proof. reflexivity. Qed.
(**
About [insert_hp],upon a pair of numbers indicating the locations of a cell both before and
after the projection of the heap,it insert a "dummy cell"  to some location on the
projected heap
*)
(**
Note that since the case where a low cell is being over-written by a high value is
being ruled out in [SecLang],the following discussion can be ignored.
*)
(**
Note the following function will be used by the projection function for the configuraiton
to remove some element from the marked heap in order to relieve us from dealing 
with heap removal in [LowLang].
Consider the following projected configuration by [project_e] and [project_hp],
tassign (tloc (an int L) 2) tH / [L(6),L(5),L(4)]
                                  0->0 2->1 4->2
which is a case where we try to over-write a low value with a high value.
One option for us,as discussed above, is to do projection as follows,
tassign (tloc (an int L) 1) tH / [L(6),L(5),L(4)]
                                  0->0 2->1 4->2
where we have a match and the referred location is change to the acctual location
on the heap and that is it! If we stick to this projection method,we would have
to deal with reduction in [LowLang] where the heap before the reduction is actually
longer and we would have to deal with problems like type safety,rearranging referred
location, and so forth which is entirely unnecessary if we instead use the
following projection,
tassign (tloc (an int L) 2) tH / [L(6),L(4)]
                                  0->0 4->1
where the low cell on the heap is removed while the referred location is changed
so that it is out of range. Actually it now is exactly the same as if we have
a case where we try to over-write a high cell with a high value.

Another example which requires the above treatment,
tassign (tloc (an int H) 2) v / [L(6),L(5),L(4)]
                                 0->0 2->1 4->2
which is being projected as
tassign (tloc (an int H) 2) v / [L(6),L(4)]
                                 0->0 4->1
*)
(**
In order to enable our project function so that the above method can be implemented we
need the following functions,
a. a function which decrease every second element of the marks on the heap
   by 1
b. a function given a natural number and a heap returns its prefix to the cell
   whose right neighbour is indicated by that number
c. a function given a natural number and a heap returns its suffix starting from
   the cell whose left neighbour is indicated by that number
d. a function which puts all together to remove one cell from the marked heap
*)
(*a. a function which upon a marked heap decrease every second number of the mark by one*)
Fixpoint decrease_snd (hp:list ((LowLang.tm*Ty)*(nat*nat))) : list ((LowLang.tm*Ty)*(nat*nat)) :=
match hp with
| h :: t => match h with
            | (fst,snd) => match snd with
                           | (n1,n2) => (fst,(n1,n2-1)) :: (decrease_snd t)
                           end
            end
| nil => nil
end.
(*some example*)
Example test_decrease_snd_1:
decrease_snd (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
=(((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,0)) :: nil).
Proof. simpl. reflexivity. Qed.

(*b. a function which upon a heap and a number returns its prefix to that number exclusive*)
Fixpoint prefix_hp_ex (n:nat)(hp:list ((LowLang.tm*Ty)*(nat*nat))) : list ((LowLang.tm*Ty)*(nat*nat)) :=
match hp , n with
| h :: t , S n' => match n' with
                   | S n'' => h :: (prefix_hp_ex n' t)
                   | 0 => h :: nil
                   end
| h :: t , 0 => nil
| nil , _ => nil
end.
(*some examples*)
Example test_prefix_hp_ex_1:
prefix_hp_ex 0 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
=nil.
Proof. simpl. reflexivity. Qed.
Example test_prefix_hp_ex_2:
prefix_hp_ex 1 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
=(((LowLang.tcon 6,an int L),(0,0)) :: nil).
Proof. simpl. reflexivity. Qed.
Example test_prefix_hp_ex_3:
prefix_hp_ex 100 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
= (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil).
Proof. simpl. reflexivity. Qed.

(*c. a function which upon a heap and a number returns its suffix starting from the next number*)
Fixpoint suffix_hp_ex (n:nat)(hp:list ((LowLang.tm*Ty)*(nat*nat))) : list ((LowLang.tm*Ty)*(nat*nat)) :=
match hp , n with
| h :: t , S n' => suffix_hp_ex n' t
| h :: t , 0 => t
| nil , _ => nil
end.
(*some examples*)
Example test_suffix_hp_ex_1:
suffix_hp_ex 0 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
=(((LowLang.tcon 5,an int L),(2,1)) :: nil).
Proof. simpl. reflexivity. Qed.
Example test_suffix_hp_ex_2:
suffix_hp_ex 1 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil) = nil.
Proof. simpl. reflexivity. Qed.
Example test_suffix_hp_ex_3:
suffix_hp_ex 100 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil) = nil.
Proof. simpl. reflexivity. Qed.

(*d. a function which removes one cell from the heap*)
Definition remove_hp (n:nat) (hp:list ((LowLang.tm*Ty)*(nat*nat))) : list ((LowLang.tm*Ty)*(nat*nat)) :=
(prefix_hp_ex n hp) ++ (decrease_snd (suffix_hp_ex n hp)).
(*some examples*)
Example test_remove_hp_1:
remove_hp 0 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: ((LowLang.tcon 7,an int L),(4,2)) :: nil)
=(((LowLang.tcon 5,an int L),(2,0)) :: ((LowLang.tcon 7,an int L),(4,1)) :: nil).
Proof. compute. reflexivity. Qed.
Example test_remove_hp_2:
remove_hp 1 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: ((LowLang.tcon 7,an int L),(4,2)) :: nil)
=(((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 7,an int L),(4,1)) :: nil).
Proof. compute. reflexivity. Qed.
Example test_remove_hp_3:
remove_hp 2 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: ((LowLang.tcon 7,an int L),(4,2)) :: nil)
=(((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil).
Proof. compute. reflexivity. Qed.
Example test_remove_hp_4:
remove_hp 100 (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: ((LowLang.tcon 7,an int L),(4,2)) :: nil)
=(((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: ((LowLang.tcon 7,an int L),(4,2)) :: nil).
Proof. compute. reflexivity. Qed.

(**
Now what about the case where we want to over write a high cell referred to by 
a pointer whose reference type is low with a low cell? 
Should we do as suggested above that we insert a dummy cell to the heap which
then will be over-written by the low value? Not a good idear for by doing so
we introduce cell in the heap whose type is not clear and who is different from
the rest of the cells on the heap in [LowLang] which brings us complications when
we try to specify reduction relation.
Consider the following projected configuration by [project_e] and [project_hp],
tassign (tloc (an int L) 1) (7) / [L(6),L(5),L(4)]
                                  0->0 2->1 4->2
which is a case where we over write a high cell with a low value, according to
the above suggested method we insert a dummy value onto the heap at the "right"
location and then change the referred location accordingly,
tassign (tloc (an int L) 1)(7) / [L(6),   *,L(5),L(4)]
                                  0->0 1->1 2->2 4->3
such method is thoroughly discussed in the next block of comments and so we are
not going to linger on furher.
A better approach,however,requires no insertion at all!for if we want to abstract
from all operations upon high value in the heap,then we should treat the case
of over-writing high cell with low cell the same as the case of over-writing high
cell with a high value and the projected heaps both before and after the projection
should be the same to [LowLang],thus,we should have the following projected configuration,
tassign (tloc (an int L) 3)(tH) / [L(6),L(5),L(4)]
                                  0->0  2->1 4->2
where we simply replace the value with [tH] and replace the referred location as
the length of the heap to make it out of range which signals a high value in the 
heap in [LowLang]. Then it is clear that we treat this case as the same as the case
when we try over-write a high cell with a high value. 
*)    
(**
Now we are ready for specifying the project function of the projected configuration
by both [project_e] and [project_hp].
Let us consider the projection sequence of the following configuration,
tapp (tassign (tloc (an int L) 2 L)(L(8)))
     (tassign (tloc (an int L) 5 L)(L(9))) / [L(1),L(2),H(3),H(4),H(5),H(6),L(7)]
by[project_e]&[project_hp]
==========================>
tapp (tassign (tloc (an int L) 2)(8))
     (tassign (tloc (an int L) 5)(9)) / [L(1),L(2),L(7)]
                                        0->0  1->1 6->2
by[project_conf] \a
==========================>
tapp (tassign (tloc (an int L) {#3#})(tH))
     (tassign (tloc (an int L) 5)(9)) / [L(1),L(2),L(7)]
                                        0->0  1->1 6->2 
by[project_conf] \b
==========================>
tapp (tassign (tloc (an int L) 3)(tH))
     (tassign (tloc (an int L) {#3#})(tH)) / [L(1),L(2),L(7)]
                                             0->0  1->1 6->2
by[project_conf] \c
==========================>
tapp (tassign (tloc (an int L) 3)(tH))
     (tassign (tloc (an int L) 3)(tH)) / [L(1),L(2),L(7)]

Note that one important point from the above projection sequence is that
the further projection of the marked heap is simply removing the marks on the heap
. It is completely independent from the projected terms under consideration.
This characteristic will simplify our task of specifying the projection function
of the configuration.
*)
(**
the project function for configuration takes a term in [LowLang] and a marked heap
and returns a configuration in [LowLang]
*)
(*one auxiliary function to erase marks on the heap*)
Fixpoint erase_hp (hp:list (((LowLang.tm)*Ty)*(nat*nat))) : LowLang.heap  := (*list ((LowLang.tm)*Ty)*)
match hp with
| h :: t => match h with
            | (fst,snd) =>fst :: (erase_hp t)
            end
| nil => nil
end.
(*some example*)
Example test_erase_hp_1:
erase_hp (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
= ((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L) :: nil).
Proof. simpl. reflexivity. Qed.

(*some lemmas regarding [erase_hp]*)

Lemma erase_hp_length:forall hp,
length (erase_hp hp) = length hp.
Proof. intros. induction hp. reflexivity. simpl. destruct a. simpl.
rewrite->IHhp. reflexivity. 
Qed.

Lemma erase_hp_snoc:forall Hp L0 p,
erase_hp (LowLang.snoc Hp (L0,p)) = LowLang.snoc (erase_hp Hp) L0.
Proof. intros Hp. induction Hp.
Case ("nil"). intros. simpl. reflexivity.
Case ("h::t"). intros. destruct a. simpl. specialize (IHHp L0 p). rewrite->IHHp. reflexivity.
Qed.


Fixpoint project_conf'_e (e:LowLang.tm)(hp:list (((LowLang.tm)*Ty)*(nat*nat))) : (LowLang.tm) :=
match e with
| LowLang.tvar x => LowLang.tvar x
(*Block One:projection of values in [LowLang]*)
(**
Note the general principle here is that no modification is make to the value
term for their counter-parts in [SecLang] are either not reducible
or reducible high terms.
There are,however,two value terms which need to be further projected to account for
the cases where a referred location is involved,
a. [LowLang.tabs x T t] whose body needs to be projected with the marked heap
b. [LowLang.tloc T n] whose referring location needs to be modified given a marked heap
*)
| LowLang.tcon n => LowLang.tcon n
| LowLang.tabs x T t => LowLang.tabs x T (project_conf'_e t hp)
| LowLang.tunit => LowLang.tunit
| LowLang.tloc T (Some n) =>if (fst(return_smallest_match n hp))
            (*no match*)       then LowLang.tloc T None 
            (*match*)          else LowLang.tloc T (Some (snd(snd(return_smallest_match n hp))))
| LowLang.tloc T None => LowLang.tloc T None
| LowLang.tH => LowLang.tH
(*End Block One*)

(*Block Two:compound expressions with only one argument*)
| LowLang.tref T t =>  LowLang.tref T (project_conf'_e t hp)
| LowLang.tderef t =>  LowLang.tderef (project_conf'_e t hp)
(*End Block Two*)

(*Block Three:compound expressions with two arguments*)
(*tapp*)
(**
Note the idea of projection here is that we first inspect the 
first argument if it is not a value we project it with the marked heap leaving 
the second argument unchanged;if it is however a value we proceed to inspect the 
second argument;if it is a value then we project both of them;if the second is not
a value we only project the second one
*)
(**
Note the following block might be used when upgrading and downgrading are 
taken into consideration
*)
(**
|LowLang.tapp t1 t2 =>match t1 with
                      | LowLang.tvar y =>LowLang.tapp t1 t2
                      | LowLang.tcon m =>LowLang.tapp t1 (project_conf'_e t2 hp)
                      | LowLang.tabs y T' t' =>match t2 with
                                       | LowLang.tvar y =>LowLang.tapp t1 t2
                                       | LowLang.tcon o =>LowLang.tapp (project_conf'_e t1 hp)(project_conf'_e t2 hp)
                                       | LowLang.tabs z T'' t'' =>LowLang.tapp (project_conf'_e t1 hp)(project_conf'_e t2 hp)
                                       | LowLang.tapp t1' t2' =>LowLang.tapp t1 (project_conf'_e t2 hp)
                                       | LowLang.tunit  =>LowLang.tapp (project_conf'_e t1 hp)(project_conf'_e t2 hp)
                                       | LowLang.tref T'' t'' =>LowLang.tapp t1 (project_conf'_e t2 hp)
                                       | LowLang.tderef t'' =>LowLang.tapp t1 (project_conf'_e t2 hp)
                                       | LowLang.tloc T'' N =>LowLang.tapp (project_conf'_e t1 hp)(project_conf'_e t2 hp)
                                       | LowLang.tassign t1' t2' =>LowLang.tapp t1 (project_conf'_e t2 hp)
                                       | LowLang.tH =>LowLang.tapp (project_conf'_e t1 hp)(project_conf'_e t2 hp)
                                       end
                      | LowLang.tapp t1' t2' =>LowLang.tapp (project_conf'_e t1 hp) t2
                      | LowLang.tunit =>LowLang.tapp t1 (project_conf'_e t2 hp)
                      | LowLang.tref T' t' =>LowLang.tapp (project_conf'_e t1 hp) t2
                      | LowLang.tderef t' =>LowLang.tapp (project_conf'_e t1 hp) t2
                      | LowLang.tloc T' N =>LowLang.tapp t1 (project_conf'_e t2 hp)
                      | LowLang.tassign t1' t2' =>LowLang.tapp (project_conf'_e t1 hp) t2
                      | LowLang.tH =>LowLang.tapp t1 (project_conf'_e t2 hp)
                      end
(*tassign*)
|LowLang.tassign t1 t2 =>match t1 with
                      | LowLang.tvar y =>LowLang.tassign t1 t2
                      | LowLang.tcon m =>LowLang.tassign t1 (project_conf'_e t2 hp)
                      | LowLang.tabs y T' t' =>LowLang.tassign t1 (project_conf'_e t2 hp)
                      | LowLang.tapp t1' t2' =>LowLang.tassign (project_conf'_e t1 hp) t2
                      | LowLang.tunit =>LowLang.tassign t1 (project_conf'_e t2 hp)
                      | LowLang.tref T' t' =>LowLang.tassign (project_conf'_e t1 hp) t2
                      | LowLang.tderef t' =>LowLang.tassign (project_conf'_e t1 hp) t2
                      | LowLang.tloc T' N =>match t2 with
                                       | LowLang.tvar y =>LowLang.tassign t1 t2
                                       | LowLang.tcon o =>LowLang.tassign (project_conf'_e t1 hp)(project_conf'_e t2 hp)
                                       | LowLang.tabs z T'' t'' =>LowLang.tassign (project_conf'_e t1 hp)(project_conf'_e t2 hp)
                                       | LowLang.tapp t1' t2' =>LowLang.tassign t1 (project_conf'_e t2 hp)
                                       | LowLang.tunit  =>LowLang.tassign (project_conf'_e t1 hp)(project_conf'_e t2 hp)
                                       | LowLang.tref T'' t'' =>LowLang.tassign t1 (project_conf'_e t2 hp)
                                       | LowLang.tderef t'' =>LowLang.tassign t1 (project_conf'_e t2 hp)
                                       | LowLang.tloc T'' N =>LowLang.tassign (project_conf'_e t1 hp)(project_conf'_e t2 hp)
                                       | LowLang.tassign t1' t2' =>LowLang.tassign t1 (project_conf'_e t2 hp)
                                       | LowLang.tH =>LowLang.tassign (project_conf'_e t1 hp)(project_conf'_e t2 hp)
                                       end
                      | LowLang.tassign t1' t2' =>LowLang.tassign (project_conf'_e t1 hp) t2
                      | LowLang.tH =>LowLang.tassign t1 (project_conf'_e t2 hp)
                      end
*)
|LowLang.tapp t1 t2 =>LowLang.tapp (project_conf'_e t1 hp)(project_conf'_e t2 hp)
|LowLang.tassign t1 t2 =>LowLang.tassign (project_conf'_e t1 hp)(project_conf'_e t2 hp)
(*End Block Three*)
end.
(*some lemmas regarding [project_conf'_e]*)
Lemma project_conf'_e_same_mark:forall t hp hp',
same_mark hp hp' = true ->
project_conf'_e t hp = project_conf'_e t hp'.
Proof. intros t. induction t.
Case ("tvar"). intros. simpl. reflexivity.
Case ("tcon"). intros. simpl. reflexivity.
Case ("tabs"). intros. simpl. apply IHt in H0. rewrite->H0. reflexivity.
Case ("tapp"). intros. simpl. assert (same_mark hp hp' = true). apply H0. apply IHt1 in H0. apply IHt2 in H1. 
               rewrite->H0. rewrite->H1. reflexivity.
Case ("tunit"). intros. simpl. reflexivity.
Case ("tref"). intros. simpl. apply IHt in H0. rewrite->H0. reflexivity.
Case ("tderef"). intros.  apply IHt in H0. simpl. rewrite->H0. reflexivity.
Case ("tloc"). intros. simpl. destruct o. apply return_smallest_match_same_mark' with(n:=n)in H0. rewrite->H0. reflexivity. reflexivity.
Case ("tassign"). intros. simpl. assert (same_mark hp hp' = true). apply H0. apply IHt1 in H0. apply IHt2 in H1. rewrite->H0. 
               rewrite->H1. reflexivity.
Case ("tH"). intros. simpl. reflexivity.
Qed.

(**
Now we are in a position to calculate the "right" heap in [LowLang] with
the following projection function. The result of it then will be used to
calculate the projection of the term in [LowLang]
*)
Fixpoint project_conf'_hp (hp1:list (((LowLang.tm)*Ty)*(nat*nat))) (hp2:list (((LowLang.tm)*Ty)*(nat*nat))): list (((LowLang.tm)*Ty)*(nat*nat)) :=
match hp1 with
|h :: t => match h with
           |(l,r) => match l with
                     |(t0,T)=>((project_conf'_e t0 hp2,T),r) :: (project_conf'_hp t hp2)
                     end
           end
| nil   => nil
end.

(**
Note some interesting properties regarding [project_conf'_hp],
1. forall hp, length hp = length (project_conf'_hp hp)
2. forall n, nth element's mark of hp is the same as that of project_conf'_hp hp
*)
Lemma same_mark_heap_proj:forall hp hp' hp'',
same_mark (project_conf'_hp hp hp')(project_conf'_hp hp hp'') = true.
Proof. intros hp. induction hp.
intros. simpl. reflexivity.
intros. destruct a. destruct p0. simpl. destruct p. simpl. rewrite<-beq_nat_refl.
        rewrite<-beq_nat_refl. apply IHhp.
Qed.

Lemma project_conf'_hp_same_mark:forall hp hp' hp'',
same_mark hp' hp'' = true ->
project_conf'_hp hp hp' = project_conf'_hp hp hp''.
Proof. intros hp. induction hp.
Case ("nil"). intros. reflexivity.
Case ("h::t"). intros. destruct a. destruct p. simpl. 
              assert (same_mark hp' hp'' = true).
              apply H0. apply project_conf'_e_same_mark with (t:=t)in H0.
              rewrite->H0. apply IHhp in H1. rewrite->H1. reflexivity.
Qed.

Lemma project_conf'_hp_length:forall hp,
length (project_conf'_hp hp hp) = length hp.
Proof. intros. induction hp. simpl. reflexivity. simpl. destruct a. destruct p. simpl.
assert (same_mark (project_conf'_hp hp hp)(project_conf'_hp hp ((t,t0,p0) :: hp)) = true).
apply same_mark_heap_proj. apply same_mark_length in H0. rewrite<-H0. rewrite->IHhp. reflexivity.
Qed.

Lemma same_mark_heap:forall hp,
same_mark hp (project_conf'_hp hp hp) = true.
Proof. intros. induction hp.
simpl. reflexivity. destruct a. destruct p0. destruct p. 
assert (project_conf'_hp (((t,t0),(n,n0)) :: hp)(((t,t0),(n,n0)) :: hp) = ((project_conf'_e t (((t,t0),(n,n0)) :: hp),t0),(n,n0)) :: (project_conf'_hp hp (((t,t0),(n,n0)) :: hp))).
simpl. reflexivity. rewrite->H0. clear H0. simpl. rewrite<-beq_nat_refl. rewrite<-beq_nat_refl.
 simpl. rewrite->same_mark_sym. reflexivity.
assert (same_mark (project_conf'_hp hp (((t,t0),(n,n0)) :: hp))(project_conf'_hp hp hp) = true). apply same_mark_heap_proj.
apply same_mark_sym in IHhp. apply same_mark_sym in H0. apply same_mark_replace with (hp1:=project_conf'_hp hp hp). apply IHhp. apply H0.
Qed.

Lemma return_smallest_match_same_mark_false:forall n hp,
fst (return_smallest_match n (project_hp hp)) = false ->
fst (return_smallest_match n (project_conf'_hp (project_hp hp)(project_hp hp))) = false.
Proof. intros. assert (same_mark (project_hp hp)(project_conf'_hp (project_hp hp)(project_hp hp))=true).
apply same_mark_heap. apply return_smallest_match_same_mark with (n:=n)in H1. rewrite<-H1. apply H0.
Qed.

Lemma project_conf'_e_add_one_low:forall t hp L,
SecLang.well_formed t (length hp) ->
project_conf'_e (project_e t) 
(project_conf'_hp (project_hp hp)(project_hp hp))
= 
project_conf'_e (project_e t)
(project_conf'_hp (LowLang.snoc (project_hp hp)(L,(length hp,length (project_hp hp))))
(LowLang.snoc (project_hp hp)(L,(length hp,length (project_hp hp))))).
Proof. intros t. induction t.
Case ("tvar"). intros. simpl. reflexivity.
Case ("tprot"). intros. destruct s. simpl. inversion H0. apply IHt with (L:=L0) in H4.
               rewrite->H4. reflexivity. simpl. reflexivity.
Case ("tcon"). intros. destruct s. simpl.  reflexivity. simpl. reflexivity.
Case ("tabs"). intros. destruct s. simpl. inversion H0. apply IHt with (L:=L0) in H6. rewrite->H6.
               reflexivity. simpl. reflexivity.
Case ("tapp"). intros. simpl. inversion H0. apply IHt1 with (L:=L0) in H3. apply IHt2 with (L:=L0) in H5.
               rewrite->H3. rewrite->H5. reflexivity.
Case ("tunit"). intros. destruct s. simpl. reflexivity. simpl. reflexivity.
Case ("tref"). intros. destruct s. simpl. inversion H0. apply IHt with (L:=L0) in H5.
               rewrite->H5. reflexivity. simpl. reflexivity.
Case ("tderef"). intros. simpl. inversion H0. apply IHt with (L:=L0) in H2. rewrite->H2.
               reflexivity.
Case ("tloc"). intros. destruct s. assert (project_e (SecLang.tloc t o L) = LowLang.tloc t o). reflexivity.
               rewrite->H1.
               assert (same_mark (project_hp hp)(project_conf'_hp (project_hp hp)(project_hp hp)) = true).
               apply same_mark_heap. apply project_conf'_e_same_mark with (t:=LowLang.tloc t o)in H2. rewrite<-H2.
               assert (same_mark (LowLang.snoc (project_hp hp)(L0,(length hp,length (project_hp hp))))(project_conf'_hp
     (LowLang.snoc (project_hp hp) (L0, (length hp, length (project_hp hp))))
     (LowLang.snoc (project_hp hp) (L0, (length hp, length (project_hp hp))))
      ) = true). apply same_mark_heap. apply project_conf'_e_same_mark with (t:=LowLang.tloc t o)in H3.
     rewrite<-H3. inversion H0. subst. remember (beq_nat n (length hp)) as BB. destruct BB. apply beq_nat_eq in HeqBB.
     rewrite->HeqBB in H8.  apply LowLang.lt_same_F in H8. inversion H8. symmetry in HeqBB. apply beq_nat_false in HeqBB.
     apply return_smallest_match_not_hit_snoc with(n3:=length (project_hp hp))(L:=L0)(hp:=project_hp hp) in HeqBB. simpl. rewrite->HeqBB.
     remember (fst (return_smallest_match n (project_hp hp))) as CC. destruct CC. reflexivity. reflexivity.  simpl. reflexivity.
Case ("tassign"). intros. simpl. inversion H0. apply IHt1 with (L:=L0) in H3. rewrite->H3. apply IHt2 with (L:=L0) in H5. rewrite->H5.
                reflexivity.
Qed.

(**
Lemma try:forall hp,
SecLang.heap_well_formed hp ->
(forall l L0, l < length hp
-> 
project_conf'_e (project_e (SecLang.efst (SecLang.heap_lookup l hp))) (project_hp hp)
=
project_conf'_e (project_e (SecLang.efst (SecLang.heap_lookup l hp))) (LowLang.snoc (project_hp hp) (L0,(length hp,length (project_hp hp))))
).
Proof. intros.
assert (same_mark (project_hp hp)(project_conf'_hp (project_hp hp)(project_hp hp)) = true).
apply same_mark_heap. apply project_conf'_e_same_mark with(t:=project_e (SecLang.efst (SecLang.heap_lookup l hp))) in H2.
rewrite->H2. 
assert (same_mark (LowLang.snoc (project_hp hp)(L0,(length hp,length (project_hp hp)))) (project_conf'_hp (LowLang.snoc (project_hp hp)(L0,(length hp,length (project_hp hp))))
(LowLang.snoc (project_hp hp)(L0,(length hp,length (project_hp hp))))) = true).
apply same_mark_heap. apply project_conf'_e_same_mark with (t:=project_e (SecLang.efst (SecLang.heap_lookup l hp)))in H3.
rewrite->H3. clear H2. clear H3. apply project_conf'_e_add_one_low. apply H0 in H1. apply H1.
Qed.
*)

Lemma marked_heap_well_formed_change_mark:forall hp n n1 n2 n3 n4,
marked_heap_well_formed (marked_heap (marked_heap' hp n1) n2) n ->
marked_heap_well_formed (marked_heap (marked_heap' hp n3) n4) n.
Proof. intros hp. induction hp.
Case ("nil"). intros. simpl. apply nil_mhwf.
Case ("h::t"). intros. destruct a. assert (marked_heap' ((t,t0) :: hp) n3 = (t,t0,(n3,n3)) :: (marked_heap' hp (S n3))). simpl. destruct n3. reflexivity. reflexivity.
               rewrite->H1. clear H1.
               simpl. remember (SecLang.label t) as BB. destruct BB.
               apply one_mhwf. simpl in H0. destruct n1. simpl in H0. rewrite<-HeqBB in H0. inversion H0. subst.
               apply IHhp with (n1:=1)(n2:=n2). apply H6. simpl in H0. rewrite<-HeqBB in H0. inversion H0. subst.
               apply IHhp with (n1:=S (S n1))(n2:=n2). apply H6. simpl in H0. destruct n1. simpl in H0. rewrite<-HeqBB in H0.
               inversion H0. subst. apply H7. simpl in H0. rewrite<-HeqBB in H0. destruct n2. inversion H0. apply H7. inversion H0.
               apply H7. simpl in H0. destruct n1. simpl in H0. rewrite<-HeqBB in H0. apply IHhp with (n1:=1)(n2:=S n2). apply H0.
               simpl in H0. rewrite<-HeqBB in H0. apply IHhp with (n1:=S (S n1))(n2:=S n2). apply H0.
Qed.
  
Lemma SecLow_well_formed:forall t n,
SecLang.well_formed t n ->
LowLang.well_formed (project_e t) n.
Proof. intros t. induction t.
Case ("tvar"). intros. simpl. apply LowLang.wf_tvar.
Case ("tprot"). intros. destruct s. simpl. apply IHt. inversion H0. apply H4.
               simpl. apply LowLang.wf_tH.
Case ("tcon"). intros. destruct s. simpl. apply LowLang.wf_tcon. simpl. apply LowLang.wf_tH.
               intros. destruct s. simpl. apply LowLang.wf_tabs. apply IHt. inversion H0. apply H6.
               simpl. apply LowLang.wf_tH.
Case ("tapp"). intros. simpl. apply LowLang.wf_tapp. apply IHt1. inversion H0. apply H3. apply IHt2.
               inversion H0. apply H5.
Case ("tunit"). intros. destruct s. simpl. apply LowLang.wf_tunit. simpl. apply LowLang.wf_tH.
Case ("tref"). intros. destruct s. simpl. apply LowLang.wf_tref. apply IHt. inversion H0. apply H5.
               simpl. apply LowLang.wf_tH.
Case ("tderef"). intros. simpl. apply LowLang.wf_tderef. apply IHt. inversion H0. apply H2.
Case ("tloc"). intros. destruct s. simpl. destruct o. apply LowLang.wf_tloc. inversion H0. apply H5.
               inversion H0. simpl. apply LowLang.wf_tH.
Case ("tassign"). intros. simpl. apply LowLang.wf_tassign. apply IHt1. inversion H0. apply H3. apply IHt2.
               inversion H0. apply H5.
Qed.
Lemma heap_marked_heap_well_formed:forall hp n,
SecLang.heap_well_formed hp n ->
marked_heap_well_formed (project_hp hp) n.
Proof. intros hp. induction hp.
Case ("nil"). intros. compute. apply nil_mhwf.
Case ("h::t"). intros. destruct a. unfold project_hp. simpl. unfold project_hp in IHhp.
               remember (SecLang.label t) as BB. destruct BB. apply one_mhwf. inversion H0.
               apply marked_heap_well_formed_change_mark with (n1:=0)(n2:=0). apply IHhp. apply H5.
               inversion H0. apply SecLow_well_formed. apply H6.
               apply marked_heap_well_formed_change_mark with (n1:=0)(n2:=0). apply IHhp.
               inversion H0. apply H5.
Qed.


Lemma project_conf'_e_add_one_low':forall Hp t n L0,
LowLang.well_formed t n ->
project_conf'_e t Hp = project_conf'_e t (LowLang.snoc Hp (L0,(n,length Hp))).
Proof. intros. generalize dependent Hp. generalize dependent L0. generalize dependent n.
induction t.
Case ("tvar"). intros. simpl. reflexivity.
Case ("tcon"). intros. simpl. reflexivity.
Case ("tabs"). intros. simpl. inversion H0. subst. apply IHt with (L0:=L0)(Hp:=Hp) in H5.
               rewrite<-H5. reflexivity.
Case ("tapp"). intros. simpl. inversion H0. subst. apply IHt1 with (L0:=L0)(Hp:=Hp)in H3.
               apply IHt2 with (L0:=L0)(Hp:=Hp) in H5. rewrite<-H3. rewrite<-H5. reflexivity.
Case ("tunit"). intros. simpl. reflexivity.
Case ("tref"). intros. simpl. inversion H0. subst. apply IHt with (L0:=L0)(Hp:=Hp)in H4. rewrite<-H4.
               reflexivity.
Case ("tderef"). intros. simpl. inversion H0. subst. apply IHt with (L0:=L0)(Hp:=Hp) in H2. rewrite<-H2.
               reflexivity.
Case ("tloc"). intros. destruct o. simpl. inversion H0. subst. assert (n0<>n). intros contra. subst. apply LowLang.lt_same_F in H4.
               inversion H4. apply return_smallest_match_not_hit_snoc with (n3:=length Hp)(L:=L0)(hp:=Hp)in H1.
               rewrite->H1. reflexivity.
               inversion H0.
Case ("tassign"). intros. simpl. inversion H0. subst. apply IHt1 with(L0:=L0)(Hp:=Hp)in H3.
               apply IHt2 with(L0:=L0)(Hp:=Hp) in H5. rewrite<-H3. rewrite<-H5. reflexivity.
Case ("tH"). intros. simpl. reflexivity. 
Qed.


Lemma project_conf'_hp_add_one_low':forall Hp Hp' n L0,
marked_heap_well_formed Hp n ->
project_conf'_hp Hp
(LowLang.snoc Hp' ((L0,(n,length Hp'))))
=project_conf'_hp Hp Hp'.
Proof. intros. generalize dependent L0. generalize dependent Hp'.
generalize dependent n. induction Hp.
Case ("nil"). intros. simpl. reflexivity.
Case ("h::t"). intros. destruct a. destruct p. simpl. assert (marked_heap_well_formed ((t,t0,p0) :: Hp) n).
               apply H0. apply marked_heap_well_formed_shrink in H0.
              apply IHHp with (Hp':=Hp')(L0:=L0)in H0. rewrite->H0. inversion H1. subst.
              apply project_conf'_e_add_one_low' with (Hp:=Hp')(L0:=L0) in H8. rewrite->H8.
              reflexivity.
Qed.

Lemma project_conf'_hp_add_one_low:forall hp L0,
SecLang.heap_well_formed hp (length hp) ->
project_conf'_hp (project_hp hp)
(LowLang.snoc (project_hp hp) ((L0,(length hp,length (project_hp hp)))))
=project_conf'_hp (project_hp hp) (project_hp hp).
Proof. intros. apply heap_marked_heap_well_formed in H0. 
       apply project_conf'_hp_add_one_low' with(Hp':=project_hp hp)(L0:=L0) in H0.
       rewrite->H0. reflexivity.
Qed.
 


Lemma project_conf'_hp_snoc:forall hp hp' t T p,
project_conf'_hp 
(LowLang.snoc hp ((t ,T),p))
 hp'
= LowLang.snoc 
(project_conf'_hp hp hp') 
((project_conf'_e t hp',T),p).
Proof. intros. generalize dependent t. generalize dependent T. generalize dependent p.
generalize dependent hp'. induction hp.
Case ("nil"). intros. simpl. reflexivity. 
Case ("h::t"). intros. destruct a. destruct p0.  simpl. specialize (IHhp hp' p T t).
              rewrite->IHhp. reflexivity.
Qed.


(*some lemmas involving [project_conf'_hp]*)
(**
Lemma erase_hp_snoc:forall v hp rt,
LowLang.value v ->
v <> LowLang.tH ->
erase_hp (project_conf'_hp (LowLang.snoc (project_hp hp)((v,an rt L),(length hp,length (project_hp hp)))) (LowLang.snoc (project_hp hp)((v,an rt L),(length hp,length (project_hp hp)))))
=LowLang.snoc (erase_hp (project_conf'_hp (project_hp hp)(project_hp hp))) ((project_conf'_e v ,an rt L).
Proof. Admitted.
*)


(*some lemmas involves [project_conf'_hp]*)

Lemma project_conf'_hp_hp_snoc:forall hp hp' v T R,
LowLang.snoc (project_conf'_hp hp hp')((project_conf'_e v hp',T),R)
=project_conf'_hp (LowLang.snoc hp ((v,T),R)) hp'.
Proof. intros hp. induction hp.
Case ("nil"). intros. simpl. reflexivity.
Case ("h::t"). intros. destruct a. destruct p. simpl. specialize (IHhp hp' v T R).
              rewrite->IHhp. reflexivity.
Qed.

Lemma return_smallest_match_snoc:forall hp v T,
LowLang.value v ->
v <> LowLang.tH ->
return_smallest_match (length hp) (project_conf'_hp ((LowLang.snoc (project_hp hp)((v,T),(length hp,length (project_hp hp)))))((LowLang.snoc (project_hp hp)((v,T),(length hp,length (project_hp hp))))))
= (false,(length hp,length (project_hp hp))).
Proof. intros. rewrite->project_conf'_hp_snoc. rewrite->project_conf'_hp_hp_snoc. assert (same_mark (LowLang.snoc (project_hp hp)
        (v, T, (length hp, length (project_hp hp))))(project_conf'_hp (LowLang.snoc (project_hp hp)
        (v, T, (length hp, length (project_hp hp))))(LowLang.snoc (project_hp hp)
        (v, T, (length hp, length (project_hp hp)))))=true). apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=length hp)in H2.
        rewrite<-H2. clear H2. rewrite->return_smallest_match_hit_snoc. reflexivity.
Qed.



(*projection of configuration*)
Definition project_conf (e:LowLang.tm)(hp:list (((LowLang.tm)*Ty)*(nat*nat))): ((LowLang.tm))*(list (((LowLang.tm)*Ty))) :=
(project_conf'_e e (project_conf'_hp hp hp),erase_hp (project_conf'_hp hp hp)).
(*some examples*)
(**
Example test_project_conf_1:
project_conf (LowLang.tassign (LowLang.tloc (an int L) (Some 1))(LowLang.tcon 7))(((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
=(LowLang.tassign (LowLang.tloc (an int L) None)(LowLang.tH),((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L) :: nil)).
Proof. compute. reflexivity. Qed.
(**
Note that as explained above,the case where we try to over-write a high cell via
a pointer whose reference type is low with a low value,we simply replace the value
with [tH] and the referred location with [None],thus treating it as
the case where a high cell is being replaced by a high value.
This is illustrated in [test_project_conf_1].
*)
*)
Example test_project_conf_2:
project_conf (LowLang.tassign (LowLang.tloc (an int L) (Some 2))(LowLang.tcon 7))(((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
=(LowLang.tassign (LowLang.tloc (an int L) (Some 1))(LowLang.tcon 7),((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L) :: nil)).
Proof. compute. reflexivity. Qed.
(**
Note in case where we want to over-write a low cell via a pointer whose reference
type is low with a low value, we need not change the heap at all. We should only 
replace the referred location to the acctually location on the heap where the 
cell to be over-written is located.
*)
Example test_project_conf_3:
project_conf (LowLang.tassign (LowLang.tloc (an int H) (Some 1))(LowLang.tcon 7))(((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
=(LowLang.tassign (LowLang.tloc (an int H) None)(LowLang.tcon 7),((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L) :: nil)).
Proof. compute. reflexivity. Qed.
(**
Note in case where we want to over-write a high cell via a pointer whose reference
type is high with a low value,since the side effect of such operation will not 
be reflected at all in projected heap, we simply replace the referred location with
[None] and leave the rest to our reduction relation in [LowLang].
*)
Example test_project_conf_4:
project_conf (LowLang.tassign (LowLang.tloc (an int L) (Some 1))(LowLang.tH))(((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil) 
=(LowLang.tassign (LowLang.tloc (an int L) None)(LowLang.tH),((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L) :: nil)).
Proof. compute. reflexivity. Qed.
(**
Note [test_project_conf_4] is a case where a high cell is being over-written by a high value.
Suppose we have the following projected configuration by [project_e] and [project_hp],
tassign (tloc (an int L) 1)(tH) / [L(6),L(5)]
                                   0->0 2->1
which is to over-write a high value via a pointer whose reference type is low with
a high value. Since any side effect related with high security does not show up in
the projected heap, we should have the following configuration as the result of 
our [project_conf] above,
tassign (tloc (an int L) 2)(tH) / [L(6),L(5)]
*) 
(**
Example test_project_conf_5:
project_conf (LowLang.tapp 
              (LowLang.tassign (LowLang.tloc (an int L) (Some 2))(LowLang.tcon 8))
              (LowLang.tassign (LowLang.tloc (an int L) (Some 5))(LowLang.tcon 9)))
             (((LowLang.tcon 1,an int L),(0,0)) :: ((LowLang.tcon 2,an int L),(1,1)) :: ((LowLang.tcon 7,an int L),(6,2)) :: nil)
= (
  LowLang.tapp
  (LowLang.tassign (LowLang.tloc (an int L) None)(LowLang.tH))
  (LowLang.tassign (LowLang.tloc (an int L) None)(LowLang.tH)),
   ((LowLang.tcon 1,an int L) :: (LowLang.tcon 2,an int L) :: (LowLang.tcon 7,an int L) :: nil)).
Proof. compute. reflexivity. Qed.
*)
Example test_project_conf_5':
project_conf (LowLang.tapp (LowLang.tH) (LowLang.tloc (an int L) (Some 2)))
             (((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil) 
=(LowLang.tapp (LowLang.tH) (LowLang.tloc (an int L) (Some 1)),((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L) :: nil)).
Proof. compute. reflexivity. Qed.
Example test_project_conf_6:
project_conf (LowLang.tderef(LowLang.tloc (an int H) (Some 1)))(((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
=(LowLang.tderef(LowLang.tloc (an int H) None),((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L) :: nil)).
Proof. compute. reflexivity. Qed.
Example test_project_conf_7:
project_conf (LowLang.tderef(LowLang.tloc (an int L) (Some 2)))(((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
=(LowLang.tderef(LowLang.tloc (an int L) (Some 1)),((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L) :: nil)).
Proof. compute. reflexivity. Qed.
(**
Example test_project_conf_8:
project_conf (LowLang.tassign (LowLang.tloc (an int L) (Some 2))(LowLang.tH))(((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
=(LowLang.tassign (LowLang.tloc (an int L) (Some 1))(LowLang.tH),((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L):: nil)).
Proof. compute. reflexivity. Qed.
(**
Note that the above example is the case where a low cell is being over-written by a high value.
Since it is the case excluded specifically in [SecLang],we need not consider the projection of it
at all
*)
*)
(**
Example test_project_conf_9:
project_conf (LowLang.tassign (LowLang.tloc (an int H) (Some 2))(LowLang.tcon 7))(((LowLang.tcon 6,an int L),(0,0)) :: ((LowLang.tcon 5,an int L),(2,1)) :: nil)
=(LowLang.tassign (LowLang.tloc (an int H) (Some 1))(LowLang.tcon 7),((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L) :: nil)).
Proof. compute. reflexivity. Qed.
(**
Similar to [test_project_conf_8] where a low cell is being over-written by a high value
*)
*)


(*some lemmas regarding [project_conf']*)

Lemma project_conf'_subst:forall x v e hp,
project_conf'_e (LowLang.subst x v e) hp 
= LowLang.subst x (project_conf'_e v hp) (project_conf'_e e hp).
Proof. intros. generalize dependent x. generalize dependent v. generalize dependent hp.
induction e.
Case ("tvar"). intros. simpl. remember (beq_id x i) as C. destruct C. reflexivity. reflexivity.
Case ("tcon"). intros. simpl. reflexivity.
Case ("tabs"). intros. simpl. remember (beq_id x i) as C. destruct C.  reflexivity.
               specialize (IHe hp v x). rewrite<-IHe. reflexivity.
Case ("tapp"). intros. simpl. specialize (IHe1 hp v x). specialize (IHe2 hp v x). rewrite->IHe1.
               rewrite->IHe2. reflexivity.
Case ("tunit"). intros. simpl. reflexivity.
Case ("tref"). intros. simpl. specialize (IHe hp v x). rewrite<-IHe. reflexivity.
Case ("tderef"). intros. simpl. specialize (IHe hp v x). rewrite->IHe. reflexivity.
Case ("tloc"). intros. simpl. destruct o. remember (fst(return_smallest_match n hp)) as C. destruct C. simpl.
               reflexivity. simpl. reflexivity. simpl. reflexivity.
Case ("tassign"). intros. simpl. specialize (IHe1 hp v x). specialize (IHe2 hp v x).
               rewrite->IHe1. rewrite->IHe2. reflexivity.
Case ("tH"). intros. reflexivity.
Qed. 


(**
Finally,we assemble the above three projection functions,[project_e],[project_hp],and [project_conf] together
*)
(*projection from a configuration in [SecLang] to one in [LowLang]*)
Definition project (c:SecLang.tm*SecLang.heap) : LowLang.tm*LowLang.heap :=
project_conf (project_e (fst c))(project_hp (snd c)).
(*some examples*)
(**
Example test_project_1:
project (SecLang.tassign (SecLang.tloc (an int L) (Some 1) L)(SecLang.tcon 7 L),((SecLang.tcon 6 L,an int L) :: (SecLang.tcon 6 H,an int H) :: (SecLang.tcon 5 L,an int L) :: nil))
= (LowLang.tassign (LowLang.tloc (an int L) None)(LowLang.tH),((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L) :: nil)).
Proof. compute. reflexivity. Qed.
*)
Example test_project_2:
project (SecLang.tassign (SecLang.tloc (an int L) (Some 2) L)(SecLang.tcon 7 L),((SecLang.tcon 6 L,an int L) :: (SecLang.tcon 6 H,an int H) :: (SecLang.tcon 5 L,an int L)::nil))
=(LowLang.tassign (LowLang.tloc (an int L) (Some 1))(LowLang.tcon 7),((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L) :: nil)).
Proof. compute. reflexivity. Qed.
Example test_project_3:
project (SecLang.tassign (SecLang.tloc (an int H) (Some 1) L)(SecLang.tcon 7 L),((SecLang.tcon 6 L,an int L) :: (SecLang.tcon 6 H,an int H) :: (SecLang.tcon 5 L,an int L) :: nil))
=(LowLang.tassign (LowLang.tloc (an int H) None)(LowLang.tcon 7),((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L) :: nil)).
Proof. compute. reflexivity. Qed.
(**
Example test_project_4:
project (SecLang.tassign (SecLang.tloc (an int L) (Some 2) L)(SecLang.tcon 7 H),((SecLang.tcon 6 L,an int L) :: (SecLang.tcon 6 H,an int H) :: (SecLang.tcon 5 L,an int L) :: nil))
=((LowLang.tassign (LowLang.tloc (an int L) (Some 1))(LowLang.tH)),((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L) :: nil)).
Proof. compute. reflexivity. Qed.
*)
(**
Example test_project_5:
project (SecLang.tassign (SecLang.tloc (an int H) (Some 2) L)(SecLang.tcon 7 L),((SecLang.tcon 6 L,an int L) :: (SecLang.tcon 6 H,an int H) :: (SecLang.tcon 5 L,an int L) :: nil))
=(LowLang.tassign (LowLang.tloc (an int H) (Some 1))(LowLang.tcon 7),((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L) :: nil)).
Proof. compute. reflexivity. Qed.
*)
Example test_project_6:
project (SecLang.tassign (SecLang.tloc (an int H) (Some 2) L)(SecLang.tcon 7 L),((SecLang.tcon 6 L,an int L) :: (SecLang.tcon 5 L,an int L) :: nil))
=(LowLang.tassign (LowLang.tloc (an int H) None)(LowLang.tcon 7),((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L) :: nil)).
Proof. compute. reflexivity. Qed.
(**
Note that in [test_project_6],the pointer is considerec to refer to high value
on the heap and that is why the referred location is projected to be [None]
*)
Example test_project_7:
project (SecLang.tassign (SecLang.tloc (an int H) (Some 4) L)(SecLang.tcon 7 L),((SecLang.tcon 6 L,an int L) :: (SecLang.tcon 6 H,an int H) :: (SecLang.tcon 5 L,an int L) :: nil))
=(LowLang.tassign (LowLang.tloc (an int H) None)(LowLang.tcon 7),((LowLang.tcon 6,an int L) :: (LowLang.tcon 5,an int L) :: nil)).
Proof. compute. reflexivity. Qed.
(**
similar to that of [test_project_6]
*)

(*some important lemmas before NI*)
(*a single-step reduction in [SecLang] can be projected to be a multi-step reduction in [LowLang]*)

Lemma proj_hp_H_same:forall t t' hp hp',
SecLang.step (t,hp) H (t',hp') ->
project_hp hp = project_hp hp'.
Proof. intros t. induction t. 
Case ("tvar"). 
               intros. inversion H0.
Case ("tprot"). 
               intros. inversion H0. subst. simpl in H9. apply IHt with (t':=t'0). apply H9. subst. 
               reflexivity.
Case ("tcon").
               intros. inversion H0.
Case ("tabs"). 
               intros. inversion H0.
Case ("tapp").
               intros. inversion H0. subst. reflexivity. subst. apply IHt1 with (t':=t1'). apply H10. 
               subst. apply IHt2 with (t':=t2'). apply H11.
Case ("tunit").
               intros. inversion H0. 
Case ("tref").
               intros. inversion H0. subst. assert (SecLang.joins s H = SecLang.joins H s). rewrite->SecLang.joins_refl. reflexivity.
               rewrite->H1. simpl. destruct t. simpl. assert (SecLang.joins s0 H = SecLang.joins H s0). rewrite->SecLang.joins_refl. reflexivity.
               rewrite->H2. clear H1. clear H2. simpl. apply project_hp_Hextend with (hp:=hp)(T:=an r s0) in H9. apply H9. subst. apply IHt with (t':=t'0).
               apply H10.
Case ("tderef").
               intros. inversion H0. subst. reflexivity. subst. apply IHt with (t':=t'0). apply H8.
Case ("tloc").
               intros. inversion H0.
Case ("tassign").
               intros. inversion H0. subst. simpl. destruct T. simpl. rewrite->SecLang.joins_refl. simpl.  
              apply project_hp_Hoverwrite. apply H8. apply H9. simpl in H14. apply H14.
(**
Here we have to prove that a high cell being replaced by high value won't make a difference in
[project_hp]
*)
               subst. apply IHt1 with (t':=t1'). apply H10. subst. apply IHt2 with (t':=t2'). apply H11.
Qed.

(*some auxialary lemmas regarding [corresp_step]*)

Lemma SecLang_value_LowLang:forall v hp,
SecLang.value v ->
LowLang.value (project_conf'_e (project_e v)(project_conf'_hp (project_hp hp)(project_hp hp))).
Proof. intros. inversion H0.
Case ("tcon"). subst. destruct b. simpl. apply LowLang.v_c. simpl. apply LowLang.v_H.
Case ("tabs"). subst. destruct b. simpl. apply LowLang.v_f. simpl. apply LowLang.v_H. 
Case ("tunit"). subst. destruct b. simpl. apply LowLang.v_u. simpl. apply LowLang.v_H.
Case ("tloc"). subst. destruct b. simpl. remember (fst(return_smallest_match n(project_conf'_hp (project_hp hp) (project_hp hp)))) as C. 
               destruct C. apply LowLang.v_l. apply LowLang.v_l. simpl. apply LowLang.v_H.
Qed.



Lemma multi_step_app1:forall c c' t2  PC,
LowLang.Multi LowLang.step c PC c' ->
LowLang.Multi LowLang.step (LowLang.tapp (fst c) t2,snd c) PC (LowLang.tapp (fst c') t2,snd c').
Proof. intros. generalize dependent t2. induction H0.
Case ("Multi_refl"). intros. apply LowLang.Multi_refl.
Case ("Multi_step"). intros. destruct y. apply LowLang.Multi_step with (y:=(LowLang.tapp t t2,h)).
                     apply LowLang.st_app1. destruct x. apply H0. specialize (IHMulti t2). apply IHMulti.
Qed.

Lemma multi_step_app2:forall v1 c c' PC,
LowLang.value v1 ->
LowLang.Multi LowLang.step c PC c' ->
LowLang.Multi LowLang.step (LowLang.tapp v1 (fst c),snd c) PC (LowLang.tapp v1 (fst c'),snd c').
Proof. intros. generalize dependent v1. induction H1.
Case ("Multi_refl"). intros. apply LowLang.Multi_refl.
Case ("Multi_step"). intros. destruct y. destruct x. apply LowLang.Multi_step with (y:=(LowLang.tapp v1 t,h)).
                     apply LowLang.st_app2. apply H2. apply H0. apply IHMulti. apply H2.
Qed.

Lemma multi_step_ref:forall c c' PC T,
LowLang.Multi LowLang.step c PC c' ->
LowLang.Multi LowLang.step (LowLang.tref T (fst c),snd c) PC (LowLang.tref T (fst c'),snd c').
Proof. intros. generalize dependent T. induction H0.
Case ("Multi_refl"). intros. apply LowLang.Multi_refl.
Case ("Multi_step"). intros. destruct y. apply LowLang.Multi_step with (y:=(LowLang.tref T t,h)). apply LowLang.st_ref. destruct x.
                    apply H0. specialize (IHMulti T). apply IHMulti.
Qed.

Lemma multi_step_deref:forall c c' PC,
LowLang.Multi LowLang.step c PC c' ->
LowLang.Multi LowLang.step (LowLang.tderef (fst c),snd c) PC (LowLang.tderef (fst c'),snd c').
Proof. intros. induction H0.
Case ("Multi_refl"). intros. apply LowLang.Multi_refl.
Case ("Multi_step"). intros. destruct y. apply LowLang.Multi_step with (y:=(LowLang.tderef t,h)). apply LowLang.st_deref. destruct x.
                    apply H0. apply IHMulti.
Qed.

Lemma multi_step_assign1:forall c c' t2  PC,
LowLang.Multi LowLang.step c PC c' ->
LowLang.Multi LowLang.step (LowLang.tassign (fst c) t2,snd c) PC (LowLang.tassign (fst c') t2,snd c').
Proof. intros. generalize dependent t2. induction H0.
Case ("Multi_refl"). intros. apply LowLang.Multi_refl.
Case ("Multi_step"). intros. destruct y. apply LowLang.Multi_step with (y:=(LowLang.tassign t t2,h)).
                     apply LowLang.st_assign1. destruct x. apply H0. specialize (IHMulti t2). apply IHMulti.
Qed.

Lemma multi_step_assign2:forall v1 c c' PC,
LowLang.value v1 ->
LowLang.Multi LowLang.step c PC c' ->
LowLang.Multi LowLang.step (LowLang.tassign v1 (fst c),snd c) PC (LowLang.tassign v1 (fst c'),snd c').
Proof. intros. generalize dependent v1. induction H1.
Case ("Multi_refl"). intros. apply LowLang.Multi_refl.
Case ("Multi_step"). intros. destruct y. destruct x. apply LowLang.Multi_step with (y:=(LowLang.tassign v1 t,h)).
                     apply LowLang.st_assign2. apply H2. apply H0. apply IHMulti. apply H2.
Qed.

Lemma step_same_mark_or_extend:forall t t' hp hp',
SecLang.step (t,hp) L (t',hp') ->
(same_mark (project_hp hp)(project_hp hp') = true) \/
(exists L0,project_hp hp' = LowLang.snoc (project_hp hp) (L0,(length hp,length (project_hp hp)))).
Proof. intros t. induction t.
Case ("tvar"). intros. inversion H0.
Case ("tprot"). intros. inversion H0. subst. destruct s. apply IHt in H9. apply H9. simpl in H9. apply proj_hp_H_same in H9.
               left. rewrite->H9. apply same_mark_refl. subst. left. apply same_mark_refl.
Case ("tcon"). intros. inversion H0.
Case ("tabs"). intros. inversion H0.
Case ("tapp"). intros. inversion H0. subst. left. apply same_mark_refl. subst. apply IHt1 in H10. apply H10. subst. apply IHt2 in H11. apply H11.
Case ("tunit"). intros. inversion H0.
Case ("tref"). intros. inversion H0. subst. destruct t. destruct s0. destruct s. simpl. inversion H9. destruct b. rewrite->SecLang.join_tcon_b.
               simpl. right. exists (LowLang.tcon n,an r L). apply project_hp_Lextend. apply SecLang.v_c. reflexivity. assert (SecLang.joinvs (SecLang.tcon n H) L = SecLang.joinvs (SecLang.tcon n L) H).
               reflexivity. rewrite->H2.  left. subst. assert (SecLang.value (SecLang.tcon n L)). apply SecLang.v_c. apply project_hp_Hextend with (hp:=hp)(T:=an r L)in H1. rewrite<-H1. apply same_mark_refl.
               destruct b. rewrite->SecLang.join_tabs_b. simpl. right. exists (LowLang.tabs (Id n) T (project_e e),an r L). apply project_hp_Lextend. apply SecLang.v_f. reflexivity. assert (SecLang.joinvs (SecLang.tabs (Id n) T e H) L = SecLang.joinvs (SecLang.tabs (Id n) T e L) H).
               reflexivity. rewrite->H2. left. assert (SecLang.value (SecLang.tabs (Id n) T e L)). apply SecLang.v_f. apply project_hp_Hextend with (hp:=hp)(T:=an r L) in H3. rewrite<-H3. apply same_mark_refl. destruct b. rewrite->SecLang.join_tunit_b. simpl. right.
               exists (LowLang.tunit,an r L). apply project_hp_Lextend. apply SecLang.v_u. reflexivity.  assert (SecLang.joinvs (SecLang.tunit H) L = SecLang.joinvs (SecLang.tunit L) H). reflexivity. rewrite->H2. left. assert (SecLang.value (SecLang.tunit L)). apply SecLang.v_u.
               apply project_hp_Hextend with (hp:=hp)(T:=an r L) in H3. rewrite<-H3. apply same_mark_refl. destruct b. rewrite->SecLang.join_tloc_b. simpl. right. exists (LowLang.tloc T (Some n),an r L). apply project_hp_Lextend. apply SecLang.v_l. reflexivity. assert (SecLang.joinvs (SecLang.tloc T (Some n) H) L = SecLang.joinvs (SecLang.tloc T (Some n) L) H).
               reflexivity. rewrite->H2. left. assert (SecLang.value (SecLang.tloc T (Some n) L)). apply SecLang.v_l. apply project_hp_Hextend with (hp:=hp)(T:=an r L)in H3. rewrite<-H3. apply same_mark_refl. left. simpl. apply project_hp_Hextend with (hp:=hp)(T:=an r L) in H9. rewrite<-H9. apply same_mark_refl. left. simpl. apply project_hp_Hextend with (hp:=hp)(T:=an r H) in H9.
               rewrite<-H9. apply same_mark_refl. subst. destruct s. apply IHt in H10. apply H10. simpl in H10. apply proj_hp_H_same in H10. left. rewrite->H10. apply same_mark_refl. 
Case ("tderef"). intros. inversion H0. subst. left. apply same_mark_refl. subst. apply IHt in H8. apply H8.
Case ("tloc"). intros. inversion H0.
Case ("tassign"). intros. inversion H0. subst. left. destruct T. destruct s. destruct b. simpl. inversion H9. destruct b. rewrite->SecLang.join_tcon_b. simpl. subst. simpl in H13. apply project_hp_Loverwrite.
                apply H8. apply SecLang.v_c. reflexivity. symmetry. apply H13. subst. simpl in H13.  assert (project_hp hp = project_hp (SecLang.heap_replace n (SecLang.joinvs (SecLang.tcon n0 H) L,an r L) hp)). 
                assert (SecLang.joinvs (SecLang.tcon n0 H) L = SecLang.joinvs (SecLang.tcon n0 L) H). reflexivity. rewrite->H1. clear H1.
                apply project_hp_Hoverwrite. apply H8. apply SecLang.v_c. rewrite<-H13. apply sub_refl. rewrite<-H1. apply same_mark_refl. subst. destruct b. rewrite->SecLang.join_tabs_b. simpl. simpl in H13. apply project_hp_Loverwrite.
                apply H8. apply SecLang.v_f. reflexivity. symmetry. apply H13. simpl in H13. assert (SecLang.joinvs (SecLang.tabs (Id n0) T e H) L = SecLang.joinvs (SecLang.tabs (Id n0) T e L) H). reflexivity. rewrite->H1. clear H1.
                assert (project_hp hp = project_hp (SecLang.heap_replace n (SecLang.joinvs (SecLang.tabs (Id n0) T e L) H, an r L) hp) ). apply project_hp_Hoverwrite. apply H8. apply SecLang.v_f. rewrite<-H13. apply sub_refl. rewrite->H1. apply same_mark_refl.
                subst. destruct b. rewrite->SecLang.join_tunit_b. simpl. apply project_hp_Loverwrite. apply H8. apply SecLang.v_u. reflexivity. simpl in H13. rewrite<-H13. reflexivity. assert (SecLang.joinvs (SecLang.tunit H) L = SecLang.joinvs (SecLang.tunit L) H). reflexivity.
                rewrite->H1. clear H1. assert (project_hp hp = project_hp (SecLang.heap_replace n (SecLang.joinvs (SecLang.tunit L) H, an r L) hp)). apply project_hp_Hoverwrite.  apply H8. apply SecLang.v_u. simpl in H13. rewrite<-H13. apply sub_refl.   rewrite<-H1. apply same_mark_refl.
                subst. destruct b. rewrite->SecLang.join_tloc_b. simpl. apply project_hp_Loverwrite. apply H8. apply SecLang.v_l. reflexivity. simpl in H13. rewrite<-H13. reflexivity. assert (SecLang.joinvs (SecLang.tloc T (Some n0) H) L = SecLang.joinvs (SecLang.tloc T (Some n0) L) H). reflexivity.
                rewrite->H1. clear H1. assert (project_hp hp = project_hp (SecLang.heap_replace n (SecLang.joinvs (SecLang.tloc T (Some n0) L) H, an r L) hp)). apply project_hp_Hoverwrite. apply H8. apply SecLang.v_l. simpl in H13. rewrite<-H13. apply sub_refl. rewrite<-H1. apply same_mark_refl.
                simpl. assert (project_hp hp = project_hp (SecLang.heap_replace n (SecLang.joinvs t2 H, an r H) hp)). apply project_hp_Hoverwrite. apply H8. apply H9. simpl in H14. inversion H14. apply sub_refl. rewrite<-H1. apply same_mark_refl. assert (SecLang.joinTs (an r H)(SecLang.joins L b) = an r H). simpl.
                destruct b. reflexivity. reflexivity. rewrite->H1. clear H1. simpl. assert (project_hp hp = project_hp (SecLang.heap_replace n (SecLang.joinvs t2 H, an r H) hp)). apply project_hp_Hoverwrite. apply H8. apply H9. simpl in H13. remember (SecLang.label t2) as BB. destruct BB. simpl in H13. rewrite<-H13. apply sub_refl.
                simpl in H13. rewrite<-H13. apply sub_refl. rewrite<-H1. apply same_mark_refl. subst.
                apply IHt1 in H10. apply H10. subst. apply IHt2 in H11. apply H11.
Qed.


(**
Note that marked_heap_lookup has to be respecified such that it searches the 
marked_heap according to the first number of the relevant mark.
*)
(*some auxiliary lemmas*)
(*######################*)
Lemma n_plus_neq_n:forall n n',
n <> (n' + (S n)).
Proof. intros n. induction n. intros. intros contra. destruct n'. inversion contra. inversion contra.
intros. intros contra. rewrite<-plus_n_Sm in contra. inversion contra. apply IHn in H1. inversion H1.
Qed.
(*######################*)
(**
Note:[heap_marked_heap_low] guarantees that whenever the query function [return_smallest_match]
     returns [false] upon a query [n],we know that the nth value on the marked heap is 
     [project_e t],given that the nth value on the heap is [t]
*)
Lemma heap_marked_heap_low':forall n t n1 n2 hp,
t = SecLang.efst (SecLang.heap_lookup n hp) ->
false = fst (return_smallest_match (n+n1) (marked_heap (marked_heap' hp n1) n2)) ->
Some (project_e t) =
marked_efst (marked_heap_lookup (n+n1) 
            (marked_heap (marked_heap' hp n1) n2)).
Proof. intros. generalize dependent n. generalize dependent t. generalize dependent n1. generalize dependent n2.
       induction hp.
Case ("nil"). intros. simpl in H1. inversion H1.
Case ("h::t"). intros. destruct n. destruct n1. destruct a. simpl.  
               remember (SecLang.label t0) as BB. destruct BB. simpl. simpl in H0. subst. reflexivity.
               simpl in H1. rewrite<-HeqBB in H1. assert (0<1). apply le_n. apply return_true_marked_heap with (hp:=hp)(n2:=S n2)in H2.
               rewrite<-H2 in H1. inversion H1.
               destruct a. simpl. destruct n2. simpl. 
               remember (SecLang.label t0) as BB. destruct BB.  simpl. rewrite<-beq_nat_refl. simpl. simpl in H0. subst. 
               reflexivity. simpl in H1. rewrite<-HeqBB in H1.
                assert (S n1<S (S n1)). apply le_n. apply return_true_marked_heap with (hp:=hp)(n2:=1)in H2.
               rewrite<-H2 in H1. inversion H1.
               remember (SecLang.label t0) as BB. destruct BB.  simpl. rewrite<-beq_nat_refl. simpl. simpl in H0. subst.
               reflexivity. simpl in H1. rewrite<-HeqBB in H1. 
               assert (S n1<S (S n1)). apply le_n. apply return_true_marked_heap with (hp:=hp)(n2:=S (S n2))in H2.
               rewrite<-H2 in H1. inversion H1.              
               destruct a. simpl. destruct n1. simpl.
               remember (SecLang.label t0) as BB. destruct BB. simpl.
               rewrite->plus_n_Sm. 
               apply IHhp. simpl in H0. apply H0. simpl in H1. rewrite<-HeqBB in H1. simpl in H1. 
               rewrite->plus_n_Sm in H1. apply H1. 
               rewrite->plus_n_Sm.
               apply IHhp. simpl in H0. apply H0. simpl in H1. rewrite<-HeqBB in H1.
               rewrite->plus_n_Sm in H1. apply H1.  
               simpl. destruct n2.
               remember (SecLang.label t0) as BB. destruct BB. simpl.
               assert (n1<>n+(S n1)). apply n_plus_neq_n. apply not_eq_beq_false in H2.
               rewrite->H2. clear H2.
               rewrite->plus_n_Sm. apply IHhp.
               simpl in H0. apply H0. simpl in H1. rewrite<-HeqBB in H1. simpl in H1.
               assert (n1<>n+(S n1)). apply n_plus_neq_n. apply not_eq_beq_false in H2.
               rewrite->H2 in H1. clear H2. rewrite->plus_n_Sm in H1. apply H1.
               rewrite->plus_n_Sm. apply IHhp.
               simpl in H0. apply H0. simpl in H1. rewrite<-HeqBB in H1. 
               rewrite->plus_n_Sm in H1. apply H1.
               remember (SecLang.label t0) as BB. destruct BB. simpl.
               assert (n1<>n+(S n1)). apply n_plus_neq_n. apply not_eq_beq_false in H2.
               rewrite->H2. rewrite->plus_n_Sm.
               apply IHhp. simpl in H0. apply H0. simpl in H1. rewrite<-HeqBB in H1. simpl in H1.
               rewrite->H2 in H1.
               rewrite->plus_n_Sm in H1. apply H1.
               rewrite->plus_n_Sm. apply IHhp.
               simpl in H0. apply H0.
               simpl in H1. rewrite<-HeqBB in H1. 
               rewrite->plus_n_Sm in H1. apply H1.
Qed.

               

Lemma heap_marked_heap_low:forall n t hp,
t = SecLang.efst (SecLang.heap_lookup n hp) ->
false = fst (return_smallest_match n (project_hp hp)) ->
Some (project_e t) =
marked_efst (marked_heap_lookup n 
            (project_hp hp)).
Proof. unfold project_hp. intros. assert (n = n+0). rewrite->plus_comm. reflexivity. rewrite->H2. 
       clear H2. apply heap_marked_heap_low'. apply H0. rewrite->plus_comm. simpl.
       apply H1.
Qed.



(**
Note: Now we are trying to show that the position of the value with the matched
      mark on the marked heap is the same as the second number of the matched mark
*)
(*some auxiliary lemmas*)
(*#####################*)
Lemma marked_heap_lookup_Sn_n:forall n n0 n1 n2 hp,
marked_efst (marked_heap_lookup (S n) (marked_heap (marked_heap' hp (S n0)) n1))
= marked_efst (marked_heap_lookup n (marked_heap (marked_heap' hp n0) n2)).
Proof. intros. generalize dependent n. generalize dependent n0. generalize dependent n1. generalize dependent n2.
induction hp.
Case ("nil"). intros. reflexivity.
Case ("h::t"). intros. destruct a. simpl. remember (SecLang.label t) as BB. destruct BB.  destruct n1. destruct n0. simpl.
               destruct n. rewrite<-HeqBB. simpl. reflexivity. rewrite<-HeqBB. simpl. specialize (IHhp n2 0 1 (S n)). apply IHhp.
               simpl. rewrite<-HeqBB. destruct n. destruct n2. simpl. specialize (IHhp 0 0 (S (S n0)) 0). apply IHhp. simpl. 
               specialize (IHhp (S n2) 0 (S (S n0)) 0). apply IHhp. destruct n2. simpl. remember (beq_nat n0 n) as CC. destruct CC.
               reflexivity. specialize (IHhp 0 0 (S (S n0)) (S n)). apply IHhp. simpl. remember (beq_nat n0 n) as CC. destruct CC.
               reflexivity. specialize (IHhp (S n2) 0 (S (S n0)) (S n)). apply IHhp. simpl. destruct n0. simpl. rewrite<-HeqBB. simpl.
               destruct n. reflexivity. specialize (IHhp n2 (S n1) 1 (S n)). apply IHhp. simpl. rewrite<-HeqBB. destruct n2. simpl. destruct n.
               specialize (IHhp 0 (S n1) (S (S n0)) 0). apply IHhp. remember (beq_nat n0 n) as CC. destruct CC. reflexivity. specialize (IHhp 0 (S n1) (S (S n0)) (S n)). apply IHhp.
               simpl. destruct n. specialize (IHhp (S n2) (S n1) (S (S n0)) 0). apply IHhp. remember (beq_nat n0 n) as CC. destruct CC. reflexivity. specialize (IHhp (S n2) (S n1) (S (S n0)) (S n)). apply IHhp.
               destruct n0. simpl. rewrite<-HeqBB. specialize (IHhp (S n2) (S n1) 1 n). apply IHhp. simpl. rewrite<-HeqBB. specialize (IHhp (S n2) (S n1) (S (S n0)) n). apply IHhp.
Qed. 
Lemma heap_lookup_n_all_marks:forall hp n n1 n2 n3 n4,
efst (heap_lookup n (marked_heap (marked_heap' hp n1) n2)) =efst (heap_lookup n (marked_heap (marked_heap' hp n3) n4)).
Proof. intros hp. induction hp.
Case ("nil"). intros. reflexivity.
Case ("h::t"). intros. destruct a. simpl. destruct n1. destruct n3. simpl. remember (SecLang.label t) as BB. destruct BB.
               destruct n. simpl. reflexivity. simpl. apply IHhp. apply IHhp. simpl. remember (SecLang.label t) as BB. destruct BB.
               destruct n4. destruct n. simpl. reflexivity. simpl. apply IHhp. destruct n. simpl. reflexivity. simpl. apply IHhp.
               apply IHhp. destruct n3. simpl. remember (SecLang.label t) as BB. destruct BB. destruct n2. destruct n. simpl. reflexivity.
               simpl. apply IHhp. destruct n. simpl. reflexivity. simpl. apply IHhp. apply IHhp. simpl. remember (SecLang.label t) as BB. destruct BB.
               destruct n2. destruct n4. destruct n. simpl. reflexivity. simpl. apply IHhp. destruct n. simpl. reflexivity. simpl. apply IHhp.
               destruct n4. destruct n. simpl. reflexivity. simpl. apply IHhp. destruct n. simpl. reflexivity. simpl. apply IHhp.
               apply IHhp.
Qed.

Lemma return_None_marked_heap_lookup:forall hp n n1 n2,
n < n1 ->
None = marked_efst (marked_heap_lookup n (marked_heap (marked_heap' hp n1) n2)).
Proof. intros hp. induction hp.
Case ("nil"). intros. simpl. reflexivity.
Case ("h::t"). intros. destruct n. destruct a. simpl. destruct n1. apply LowLang.lt_same_F in H0.
               inversion H0. simpl. destruct n2.
               remember (SecLang.label t) as BB. destruct BB. simpl. apply IHhp. apply le_S in H0. 
               apply H0. apply IHhp. apply le_S in H0. apply H0. 
               remember (SecLang.label t) as BB. destruct BB. simpl. apply IHhp. apply le_S in H0. apply H0.
               apply IHhp. apply le_S in H0. apply H0. destruct a. simpl. destruct n1. inversion H0. simpl.
               destruct n2.
               remember (SecLang.label t) as BB. destruct BB. simpl. assert (n<>n1). intros contra. rewrite->contra in H0.
               apply LowLang.lt_same_F in H0. inversion H0. apply not_eq_beq_false in H1. rewrite->beq_nat_sym in H1. rewrite->H1.
               apply IHhp. apply le_S in H0. apply H0. apply IHhp. apply le_S in H0. apply H0. 
               remember (SecLang.label t) as BB. destruct BB. simpl. 
                assert (n<>n1). intros contra. rewrite->contra in H0.
               apply LowLang.lt_same_F in H0. inversion H0. apply not_eq_beq_false in H1. rewrite->beq_nat_sym in H1. rewrite->H1.
               apply IHhp. apply le_S in H0. apply H0. apply IHhp. apply le_S in H0. apply H0.
Qed.

(*#####################*)
Lemma lt_Sn_zero:forall n,
0 < S n.
Proof. intros. induction n. apply le_n. apply le_S. apply IHn.
Qed.
Lemma marked_heap_value_tws':forall n n' hp,
marked_efst (marked_heap_lookup n (marked_heap (marked_heap' hp n') n')) <> None ->
marked_efst (marked_heap_lookup n (marked_heap (marked_heap' hp n') n')) =
efst (heap_lookup (snd(snd(return_smallest_match n (marked_heap (marked_heap' hp n') n')))) (marked_heap (marked_heap' hp n') n')).
Proof. intros. generalize dependent n. generalize dependent n'. induction hp.
Case ("nil"). intros. simpl. destruct n. reflexivity. reflexivity.
Case ("h::t"). intros. destruct a. simpl. destruct n'. simpl. 
              remember (SecLang.label t) as BB. destruct BB. simpl. destruct n. simpl.
              reflexivity. simpl in H0. 
              rewrite<-HeqBB in H0. simpl in H0. rewrite->marked_heap_lookup_Sn_n with (n2:=0).
              assert (0<=0). apply le_n. apply return_smallest_match_snd_Sn_n with (hp:=hp)(n:=n)in H1.
              rewrite->H1. clear H1. simpl. rewrite->heap_lookup_n_all_marks with(n3:=0)(n4:=0).
              apply IHhp. rewrite->marked_heap_lookup_Sn_n  with (n2:=0) in H0. apply H0.
              apply IHhp. simpl in H0. rewrite<-HeqBB in H0. apply H0. simpl.
              remember (SecLang.label t) as BB. destruct BB. simpl. destruct n.         
              assert (0<S n'). apply lt_Sn_zero.
              apply return_None_marked_heap_lookup with(hp:=(t,t0)::hp)(n2:=S n')in H1. rewrite<-H1 in H0. assert (False). 
              apply H0. reflexivity. inversion H2. 
              remember (beq_nat n' n) as CC. destruct CC. simpl in H0. rewrite<-HeqBB in H0. simpl in H0. rewrite<-HeqCC in H0.
              simpl. rewrite->minus_diag. simpl. reflexivity.
              simpl. simpl in H0. rewrite<-HeqBB in H0. simpl in H0. rewrite<-HeqCC in H0.
              rewrite->marked_heap_lookup_Sn_n with (n2:=S n'). assert (S n'<=S n'). apply le_n.
              apply return_smallest_match_snd_Sn_n with (hp:=hp)(n:=n)in H1. rewrite->H1. clear H1. simpl. 
              rewrite->heap_lookup_n_all_marks with (n3:=S n')(n4:=S n'). apply IHhp. rewrite->marked_heap_lookup_Sn_n with(n2:=S n') in H0.
              apply H0. apply IHhp. simpl in H0. rewrite<-HeqBB in H0. apply H0.
Qed.
Lemma marked_heap_value_tws:forall n hp,
marked_efst (marked_heap_lookup n (project_hp hp)) <> None ->
marked_efst (marked_heap_lookup n (project_hp hp)) = 
efst (heap_lookup (snd(snd(return_smallest_match n (project_hp hp)))) (project_hp hp)).
Proof. unfold project_hp. intros. apply marked_heap_value_tws'. apply H0.
Qed.

(**
Now we are ready to prove the following equality,
v = efst (heap_lookup n hp) where
v = project_conf'_e (project_e t)(project_hp hp0)
n = snd(snd (return_smallest_match n (project_hp hp0)))
hp= erase_hp (project_conf'_hp (project_hp hp0)(project_hp hp0))
*)
(**
Step one,
we get started by proving some lemma where [project_e t] and 
[snd(snd (return_smallest_match n (project_hp hp0)))] appear on opposite sides of 
an equality,
*)
Lemma cs_derefloc_one:forall n t hp,
t = SecLang.efst (SecLang.heap_lookup n hp) ->
false = fst (return_smallest_match n (project_hp hp)) ->
Some (project_e t) =
efst (heap_lookup (snd(snd(return_smallest_match n (project_hp hp)))) (project_hp hp)).
Proof. intros. apply heap_marked_heap_low in H0. rewrite->H0. apply marked_heap_value_tws.
       rewrite<-H0. intros contra. inversion contra. apply H1.
Qed.
(**
Step two,
we prove that if we use the same "query",[n],instead on the marked heap obtained 
from evaluating every value on [project_hp hp] from [project_hp hp] we get a new
value obtained from evaluating the old one,[project_e t],from [project_hp hp],
*)
Lemma heap_lookup_project_conf'_hp':forall n hp hp' v,
efst (heap_lookup n hp) = Some v ->
efst (heap_lookup n (project_conf'_hp hp hp'))
= Some (project_conf'_e v hp').
Proof. intros. generalize dependent n. generalize dependent hp'. generalize dependent v.
induction hp.
Case ("nil"). intros. destruct n. simpl in H0. inversion H0. simpl in H0. inversion H0.
Case ("h::t"). intros. destruct n. destruct a. destruct p. simpl in H0. simpl. inversion H0.
               reflexivity. destruct a. destruct p. simpl. apply IHhp. simpl in H0. apply H0.
Qed.

Lemma heap_lookup_project_conf'_hp:forall n hp v,
efst (heap_lookup n hp) = Some v ->
efst (heap_lookup n (project_conf'_hp hp hp))
= Some (project_conf'_e v hp).
Proof. intros. apply heap_lookup_project_conf'_hp'. apply H0.
Qed.

Lemma cs_derefloc_two':forall n t hp,
Some (project_e t) =
efst (heap_lookup (snd(snd(return_smallest_match n (project_hp hp)))) (project_hp hp)) ->
Some (project_conf'_e (project_e t)(project_hp hp)) =
efst (heap_lookup (snd(snd(return_smallest_match n (project_conf'_hp (project_hp hp)(project_hp hp))))) (project_conf'_hp (project_hp hp)(project_hp hp))).
Proof. intros. assert (same_mark (project_hp hp)(project_conf'_hp (project_hp hp)(project_hp hp)) = true). apply same_mark_heap.
      apply return_smallest_match_same_mark' with (n:=n) in H1. rewrite<-H1. clear H1.
      symmetry. apply heap_lookup_project_conf'_hp. symmetry. apply H0.
Qed.

Lemma cs_derefloc_two:forall n t hp,
t = SecLang.efst (SecLang.heap_lookup n hp) ->
false = fst (return_smallest_match n (project_hp hp)) ->
Some (project_conf'_e (project_e t)(project_hp hp)) =
efst (heap_lookup (snd(snd(return_smallest_match n (project_conf'_hp (project_hp hp)(project_hp hp))))) (project_conf'_hp (project_hp hp)(project_hp hp))).
Proof. intros. apply cs_derefloc_two'. apply cs_derefloc_one. apply H0. apply H1.
Qed.

(*one extra lemma related to [cs_derefloc_two]*)
(*############################################*)
Lemma heap_lookup_n_length: forall hp n v,
efst (heap_lookup n hp) = Some v ->
n < length hp.
Proof. intros hp. induction hp.
Case ("nil"). intros. destruct n. simpl in H0. inversion H0. simpl in H0. inversion H0.
Case ("h::t"). intros. destruct n. simpl. apply lt_0_Sn. simpl. apply SecLang.n_iff_Sn_left. apply IHhp with (v:=v).
              simpl in H0. apply H0.
Qed.
(*############################################*)
(**
Step three,
finishing up by establishing relation between [heap_lookup] and [efst] in [LowLang] 
and their counterparts in the current block,
efst (heap_lookup n hp) = Some (LowLang.efst (LowLang.heap_lookup n (erase hp)))
when there is a hit,
*)
Lemma cs_derefloc_three:forall n hp,
efst (heap_lookup n hp) <> None ->
efst (heap_lookup n hp) = Some (LowLang.efst (LowLang.heap_lookup n (erase_hp hp))).
Proof. intros. generalize dependent n. induction hp.
Case ("nil"). intros. destruct n. simpl in H0. assert (False). apply H0. reflexivity. 
              inversion H1. simpl in H0. assert (False). apply H0. reflexivity. inversion H1.
Case ("h::t"). intros. destruct n. destruct a. destruct p. simpl. reflexivity. simpl. destruct a.
              apply IHhp. simpl in H0. apply H0.
Qed.

Lemma cs_derefloc:forall n t hp,
t = SecLang.efst (SecLang.heap_lookup n hp) ->
false = fst (return_smallest_match n (project_hp hp)) ->
project_conf'_e (project_e t)(project_hp hp) =
LowLang.efst (LowLang.heap_lookup (snd(snd(return_smallest_match n (project_hp hp)))) (erase_hp (project_conf'_hp (project_hp hp)(project_hp hp)))).
Proof. intros. apply cs_derefloc_two in H0. 
       assert (efst (heap_lookup(snd(snd(return_smallest_match n
              (project_conf'_hp (project_hp hp) (project_hp hp)))))
              (project_conf'_hp (project_hp hp) (project_hp hp)))<>None).
       intros contra. rewrite<-H0 in contra. inversion contra.
       apply cs_derefloc_three in H2. rewrite->H2 in H0. clear H2.  inversion H0. 
       assert (same_mark (project_hp hp)(project_conf'_hp (project_hp hp)(project_hp hp))=true).
       apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=n) in H2.
       rewrite->H2. clear H2. apply H3.
       apply H1. 
Qed.

(**
Note the following block contains lemmas necessary to prove the sub-case,[st_assign], 
in [corresp_step]
*)
(*##################*)


Lemma replace_BA_marked_heap_project_hp:forall n n1 n2 (v:SecLang.tm) (T:Ty) (hp:SecLang.heap),
n < length hp ->
SecLang.label v = SecLang.label (SecLang.efst (SecLang.heap_lookup n hp))->
marked_heap (marked_heap' (SecLang.heap_replace n (v,T) hp) n1) n2 =
marked_heap_replace (n+n1) (project_e v,T) (marked_heap (marked_heap' hp n1) n2).
Proof. intros. generalize dependent n. generalize dependent n1. generalize dependent n2.
generalize dependent v. generalize dependent T.
induction hp.
Case ("nil"). intros. simpl in H0. destruct n. apply LowLang.lt_same_F in H0. inversion H0.
              inversion H0.
Case ("h::t"). intros. destruct n. 
     SCase ("n=0").         
              destruct a. simpl. simpl in H1. destruct n1. simpl. 
              remember (SecLang.label v) as BB. destruct BB. rewrite<-H1.
              simpl. reflexivity. rewrite<-H1.  assert (0<1). apply le_n. 
              apply marked_heap_replace_same with (hp:=hp)(n2:=S n2)(p:=(project_e v,T)) in H2.
              rewrite->H2. reflexivity.
              simpl. remember (SecLang.label v) as BB. destruct BB. rewrite<-H1. destruct n2. simpl.
              rewrite<-beq_nat_refl. reflexivity. simpl. rewrite<-beq_nat_refl. reflexivity. rewrite<-H1.
              assert ((S n1)<(S (S n1))). apply le_n. apply marked_heap_replace_same with (hp:=hp)(n2:=S n2)(p:=(project_e v,T)) in H2.
              rewrite->H2. reflexivity.
     SCase ("n=S n'").
              destruct a. simpl. destruct n1. simpl. 
              remember (SecLang.label t) as BB. destruct BB. simpl.
              specialize (IHhp T v n2 1 n). simpl in H0. apply SecLang.lt_same_F' in H0. apply IHhp in H0.
              rewrite<-plus_n_O. rewrite->plus_comm in H0. simpl in H0. rewrite->H0. reflexivity. simpl in H1.
              apply H1. rewrite->plus_comm. simpl. specialize (IHhp T v (S n2) 1 n). simpl in H0.
              apply SecLang.lt_same_F' in H0. apply IHhp in H0. rewrite->plus_comm in H0. simpl in H0.
              rewrite->H0. reflexivity. simpl in H1. apply H1. simpl. remember (SecLang.label t) as BB. destruct BB.
              destruct n2. simpl. assert (n1<>(n+ S n1)). apply n_plus_neq_n. apply not_eq_beq_false in H2. rewrite->H2.
              clear H2. specialize (IHhp T v 0 (S (S n1)) n). simpl in H0. apply SecLang.lt_same_F' in H0. apply IHhp in H0.
              rewrite->plus_n_Sm. rewrite->H0. reflexivity. simpl in H1. apply H1. simpl. 
              assert (n1<>(n + S n1)). apply n_plus_neq_n. apply not_eq_beq_false in H2. rewrite->H2. clear H2. 
              specialize (IHhp T v (S n2)(S (S n1)) n). simpl in H0. apply SecLang.lt_same_F' in H0. apply IHhp in H0.
              rewrite->plus_n_Sm. rewrite->H0. reflexivity. simpl in H1. apply H1. rewrite->plus_n_Sm.
              simpl in H0. apply SecLang.lt_same_F' in H0.  specialize (IHhp T v (S n2)(S (S n1)) n). apply IHhp in H0.
              rewrite->H0. reflexivity. simpl in H1. apply H1.
Qed.


Lemma same_mark_marked_heap_replace':forall n (v:SecLang.tm) (T:Ty) (hp:SecLang.heap),
SecLang.value v ->
n < length hp ->
SecLang.label v = SecLang.label (SecLang.efst (SecLang.heap_lookup n hp))->
same_mark (marked_heap (marked_heap' hp 0)0)
          (marked_heap (marked_heap' (SecLang.heap_replace n (v,T) hp)0)0) = true.
Proof. intros. inversion H0.
Case ("tcon"). destruct b. subst.
     SCase ("Loverwrite").  apply project_hp_Loverwrite. apply H1. apply SecLang.v_c. reflexivity.
                          rewrite<-H2. reflexivity.
     SCase ("Hoverwrite"). assert (project_hp hp = project_hp (SecLang.heap_replace n (SecLang.joinvs (SecLang.tcon n0 H) H,T) hp)).
                          apply project_hp_Hoverwrite. apply H1. apply SecLang.v_c. subst. rewrite<-H2. apply sub_refl. 
                          rewrite->SecLang.join_tcon_H in H4. unfold project_hp in H4. rewrite<-H4.
                          apply same_mark_refl.
Case ("tabs"). destruct b. subst.
      SCase ("Loverwrite").  apply project_hp_Loverwrite. apply H1. apply SecLang.v_f. reflexivity.
                          rewrite<-H2. reflexivity.
     SCase ("Hoverwrite"). assert (project_hp hp = project_hp (SecLang.heap_replace n (SecLang.joinvs (SecLang.tabs (Id n0) T0 e H) H,T) hp)).
                          apply project_hp_Hoverwrite. apply H1. apply SecLang.v_f. subst. rewrite<-H2. apply sub_refl. 
                          rewrite->SecLang.join_tabs_H in H4. unfold project_hp in H4. rewrite<-H4.
                          apply same_mark_refl.
Case ("tunit"). destruct b. subst.
     SCase ("Loverwrite").  apply project_hp_Loverwrite. apply H1. apply SecLang.v_u. reflexivity.
                          rewrite<-H2. reflexivity.
     SCase ("Hoverwrite"). assert (project_hp hp = project_hp (SecLang.heap_replace n (SecLang.joinvs (SecLang.tunit H) H,T) hp)).
                          apply project_hp_Hoverwrite. apply H1. apply SecLang.v_u. subst. rewrite<-H2. apply sub_refl. 
                          rewrite->SecLang.join_tunit_H in H4. unfold project_hp in H4. rewrite<-H4.
                          apply same_mark_refl.   
Case ("tloc"). destruct b. subst.
     SCase ("Loverwrite").  apply project_hp_Loverwrite. apply H1. apply SecLang.v_l. reflexivity.
                          rewrite<-H2. reflexivity.
     SCase ("Hoverwrite"). assert (project_hp hp = project_hp (SecLang.heap_replace n (SecLang.joinvs (SecLang.tloc T0 (Some n0) H) H,T) hp)).
                          apply project_hp_Hoverwrite. apply H1. apply SecLang.v_l. subst. rewrite<-H2. apply sub_refl. 
                          rewrite->SecLang.join_tloc_H in H4. unfold project_hp in H4. rewrite<-H4.
                          apply same_mark_refl.
Qed.


Lemma same_mark_marked_heap_replace:forall n n1 n2 (v:SecLang.tm) (T:Ty) (hp:SecLang.heap),
n2<=n1 ->
SecLang.value v ->
n < length hp ->
SecLang.label v = SecLang.label (SecLang.efst (SecLang.heap_lookup n hp))->
same_mark (marked_heap (marked_heap' hp n1)n2)
          (marked_heap (marked_heap' (SecLang.heap_replace n (v,T) hp)n1)n2) = true.
Proof. intros. apply same_mark_marked_heap_replace' with(n:=n)(T:=T)(hp:=hp) in H1.
       apply same_mark_marked_heap_generalize. apply H0. apply H1. apply H2. apply H3.
Qed.
       

Lemma project_conf'_hp_marked_heap_replace_1:forall n v T hp, 
SecLang.value v ->
n < length hp ->
SecLang.label v = SecLang.label (SecLang.efst (SecLang.heap_lookup n hp))->
project_conf'_hp (project_hp (SecLang.heap_replace n (v,T) hp))(project_hp (SecLang.heap_replace n (v,T) hp)) 
=project_conf'_hp (marked_heap_replace n (project_e v,T) (project_hp hp)) (project_hp hp).
Proof. intros. assert (n<length hp). apply H1. apply replace_BA_marked_heap_project_hp with (n1:=0)(n2:=0)(v:=v)(T:=T)in H1.
       rewrite->plus_comm in H1. simpl in H1. unfold project_hp. rewrite<-H1. 
       apply same_mark_marked_heap_replace' with (n:=n)(T:=T)(hp:=hp) in H0.
       apply project_conf'_hp_same_mark with (hp:=marked_heap (marked_heap' (SecLang.heap_replace n (v, T) hp) 0) 0)in H0. 
       rewrite<-H0. reflexivity. apply H3. apply H2. apply H2.
Qed.


Lemma project_conf'_hp_marked_heap_replace_2:forall N V T HP HP',
project_conf'_hp (marked_heap_replace N (V,T) HP) HP'
= marked_heap_replace N (project_conf'_e V HP',T)(project_conf'_hp HP HP'). 
Proof. intros. generalize dependent N. generalize dependent V. generalize dependent T.
generalize dependent HP'. induction HP.
Case ("nil"). intros. simpl. reflexivity.
Case ("h::t"). intros. destruct a. destruct p0. simpl. remember (beq_nat n N) as BB. destruct BB.
              destruct p. simpl. rewrite<-HeqBB. reflexivity. destruct p. simpl. rewrite<-HeqBB.
              specialize (IHHP HP' T V N). rewrite->IHHP. reflexivity.
Qed.

Lemma project_conf'_hp_marked_heap_replace:forall v T n hp,
SecLang.value v ->
n < length hp ->
SecLang.label v = SecLang.label (SecLang.efst (SecLang.heap_lookup n hp))->
project_conf'_hp (project_hp (SecLang.heap_replace n (v,T) hp))(project_hp (SecLang.heap_replace n (v,T) hp)) 
=marked_heap_replace n (project_conf'_e (project_e v) (project_conf'_hp (project_hp hp)(project_hp hp)),T)
 (project_conf'_hp (project_hp hp)(project_hp hp)).
Proof. intros. apply project_conf'_hp_marked_heap_replace_1 with (n:=n)(T:=T)(hp:=hp)in H0.
       assert (same_mark (project_hp hp) (project_conf'_hp (project_hp hp) (project_hp hp)) = true).
       apply same_mark_heap. apply project_conf'_e_same_mark with (t:=project_e v)in H3. rewrite<-H3.
       rewrite<-project_conf'_hp_marked_heap_replace_2. apply H0.
       apply H1. apply H2.
Qed.  


(*some auxiliary lemmas for the following lemma*)
(*##############################################*)
Lemma add_both_mark_marked_heap_replace:forall hp n n1 n2 V T,
n2<=n1 ->
marked_heap_replace (S n) (V,T) (marked_heap(marked_heap' hp (S n1))n2)
=add_both_mark (marked_heap_replace n (V,T) (marked_heap(marked_heap' hp n1)n2)).
Proof. intros hp. induction hp.
Case ("nil"). intros. reflexivity.
Case ("h::t"). intros. destruct a. simpl. remember (SecLang.label t) as BB. destruct BB.
              destruct n2. destruct n1. simpl. destruct n. rewrite<-HeqBB. simpl.
              assert (0<=1). apply le_S. apply le_n. apply marked_heap_add_both_mark with (hp:=hp) in H1.
              simpl in H1. rewrite<-H1. reflexivity. rewrite<-HeqBB. simpl. specialize (IHhp (S n) 1 0 V T).
              assert (0<=1). apply le_S. apply le_n. apply IHhp in H1. rewrite->H1. reflexivity. simpl. rewrite<-HeqBB.
              destruct n. simpl. rewrite->plus_comm. simpl. specialize (IHhp 0 (S (S n1)) 0 V T). apply le_S in H0.
              apply IHhp in H0. rewrite<-H0. reflexivity. remember (beq_nat n1 n) as CC. destruct CC. simpl. 
              rewrite<-HeqCC. simpl. rewrite->plus_comm. simpl. assert (0<=S (S n1)). apply SecLang.zero_n.
              apply marked_heap_add_both_mark with (hp:=hp) in H1. rewrite->plus_comm in H1. simpl in H1. rewrite<-H1.
              reflexivity.  simpl. rewrite<-HeqCC. simpl. rewrite->plus_comm. simpl. specialize (IHhp (S n) (S (S n1)) 0 V T).
              apply le_S in H0. apply IHhp in H0. rewrite->H0. reflexivity. destruct n1. inversion H0. simpl. rewrite<-HeqBB.
              destruct n2. destruct n. simpl. rewrite<-minus_n_O. rewrite->plus_comm. simpl. specialize (IHhp 0 (S (S n1)) 1 V T).
              apply le_S in H0. apply IHhp in H0. rewrite->H0. reflexivity. remember (beq_nat n1 n) as CC. destruct CC.
              simpl. rewrite<-HeqCC. simpl. rewrite<-minus_n_O. rewrite->plus_comm. simpl. apply le_S in H0. 
              apply marked_heap_add_both_mark with (hp:=hp) in H0. rewrite->plus_comm in H0. simpl in H0. rewrite<-H0. reflexivity.
              simpl. rewrite<-HeqCC. simpl. rewrite<-minus_n_O. rewrite->plus_comm. simpl. specialize (IHhp (S n) (S (S n1)) 1 V T).
              apply le_S in H0. apply IHhp in H0. rewrite->H0. reflexivity. destruct n. simpl. rewrite->plus_comm. simpl. rewrite->plus_comm.
              simpl. assert (S (S n2)<=S n1). apply H0. apply SecLang.lt_snoc_1 in H0. apply minus_Sn_m in H0. rewrite->H0. simpl. specialize (IHhp 0 (S (S n1)) (S (S n2)) V T).
              apply SecLang.lt_snoc_1 in H1. apply le_S in H1. apply SecLang.n_iff_Sn_left in H1. apply IHhp in H1. rewrite->H1. reflexivity.
              remember (beq_nat n1 n) as CC. destruct CC. simpl. rewrite<-HeqCC. simpl. rewrite->plus_comm. simpl. rewrite->plus_comm. simpl. assert (S (S n2)<=S n1). apply H0.
              apply SecLang.lt_snoc_1 in H0. apply minus_Sn_m in H0. rewrite->H0. simpl. apply le_S in H1. apply marked_heap_add_both_mark with (hp:=hp) in H1. rewrite->plus_comm in H1.
              simpl in H1. rewrite->H1. reflexivity. simpl. rewrite<-HeqCC. simpl. rewrite->plus_comm. simpl. rewrite->plus_comm. simpl. assert (S (S n2)<=S n1). apply H0. apply SecLang.lt_snoc_1 in H0.
              apply minus_Sn_m in H0. rewrite->H0. simpl. specialize (IHhp (S n) (S (S n1)) (S (S n2)) V T). apply le_S in H1. apply IHhp in H1. rewrite->H1. reflexivity. destruct n. destruct n1. 
              simpl.  rewrite<-HeqBB. specialize (IHhp 0 1 (S n2) V T). apply SecLang.n_iff_Sn_left in H0. apply IHhp in H0. rewrite->H0. reflexivity. simpl. rewrite<-HeqBB. specialize (IHhp 0 (S (S n1)) (S n2) V T).
              apply SecLang.n_iff_Sn_left in H0. apply IHhp in H0. apply H0. 
               destruct n.  destruct n1. simpl. rewrite<-HeqBB. specialize (IHhp 1 1 (S n2) V T). apply SecLang.n_iff_Sn_left in H0. apply IHhp in H0. apply H0.
              simpl. rewrite<-HeqBB. specialize (IHhp 1 (S (S n1))(S n2) V T). apply SecLang.n_iff_Sn_left in H0. apply IHhp in H0. apply H0. destruct n1. simpl.
              rewrite<-HeqBB. specialize (IHhp (S (S n)) 1 (S n2) V T). apply SecLang.n_iff_Sn_left in H0. apply IHhp in H0. apply H0. simpl. rewrite<-HeqBB.
              specialize (IHhp (S (S n))(S (S n1))(S n2) V T).  apply SecLang.n_iff_Sn_left in H0. apply IHhp in H0. apply H0.
Qed.

Lemma add_both_mark_heap_replace:forall hp n n1 n2 V T,
n2<=n1->
heap_replace n (V,T) (marked_heap(marked_heap' hp (S n1))n2)
=add_both_mark (heap_replace n (V,T) (marked_heap(marked_heap' hp n1)n2)).
Proof. intros hp. induction hp. 
Case ("nil"). intros. destruct n. reflexivity. reflexivity.
Case ("h::t"). intros. destruct a. simpl. remember (SecLang.label t) as BB. 
              destruct BB. destruct n2. destruct n1. simpl. rewrite<-HeqBB.
              destruct n. simpl. assert (0<=1). apply le_S. apply le_n.
              apply marked_heap_add_both_mark with (hp:=hp) in H1. simpl in H1.
              rewrite->H1. clear H1. reflexivity. simpl. specialize (IHhp n 1 0  V T).
              apply le_S in H0. apply IHhp in H0.
              rewrite->H0. reflexivity. simpl. rewrite<-HeqBB. destruct n. simpl. 
              rewrite->plus_comm. simpl. assert (0<=S (S n1)). apply SecLang.zero_n.
              apply marked_heap_add_both_mark with (hp:=hp) in H1. rewrite->plus_comm in H1.
              simpl in H1. rewrite->H1. reflexivity. simpl. rewrite->plus_comm. simpl.
              specialize (IHhp n (S (S n1))  0 V T). apply le_S in H0. apply IHhp in H0. 
              rewrite->H0. reflexivity.
              destruct n1. inversion H0. simpl. rewrite<-HeqBB. destruct n2. destruct n.
              simpl. rewrite<-minus_n_O. rewrite->plus_comm. simpl. apply le_S in H0.
              apply marked_heap_add_both_mark with (hp:=hp) in H0. rewrite->plus_comm in H0. 
              simpl in H0. rewrite->H0. reflexivity.  simpl. rewrite<-minus_n_O. rewrite->plus_comm.
              simpl. specialize (IHhp n (S (S n1)) 1 V T). apply le_S in H0. apply IHhp in H0. rewrite->H0.
              reflexivity. destruct n. simpl. rewrite->plus_comm. simpl. rewrite->plus_comm. simpl.
              assert (S n2<=n1). apply SecLang.lt_same_F' in H0.
              apply H0. apply minus_Sn_m in H1. rewrite->H1. clear H1. simpl. apply le_S in H0.
              apply marked_heap_add_both_mark with (hp:=hp) in H0. rewrite->plus_comm in H0. simpl in H0.
              rewrite->H0. reflexivity. simpl. rewrite->plus_comm. simpl. rewrite->plus_comm. simpl.
              assert (S n2<=n1). apply SecLang.lt_same_F' in H0. apply H0. apply minus_Sn_m in H1. rewrite->H1.
              clear H1. simpl. specialize (IHhp n (S (S n1))(S(S n2)) V T). apply le_S in H0. apply IHhp in H0.
              rewrite->H0. reflexivity. destruct n1.  destruct n. destruct n2. 
              assert (marked_heap((t,t0,(0,0))::marked_heap' hp 1)0=marked_heap(marked_heap' hp 1)1). simpl. 
              rewrite<-HeqBB. reflexivity. rewrite->H1. apply SecLang.n_iff_Sn_left in H0. specialize (IHhp 0 1 1 V T).
              apply IHhp in H0. rewrite->H0. reflexivity. inversion H0. destruct n2. 
              assert (marked_heap((t,t0,(0,0))::marked_heap' hp 1)0=marked_heap(marked_heap' hp 1)1). simpl. 
              rewrite<-HeqBB. reflexivity. rewrite->H1. clear H1. apply SecLang.n_iff_Sn_left in H0.
              specialize (IHhp (S n) 1 1 V T). apply IHhp in H0. apply H0. inversion H0. 
              assert (marked_heap((t,t0,(S n1,S n1))::marked_heap' hp (S (S n1)))n2=marked_heap(marked_heap' hp (S (S n1)))(S n2)). simpl. 
              rewrite<-HeqBB. reflexivity. rewrite->H1. clear H1. apply SecLang.n_iff_Sn_left in H0. specialize (IHhp n (S (S n1))(S n2) V T).
              apply IHhp in H0. apply H0.
Qed.
(*##############################################*)
Lemma marked_heap_replace_heap_replace':forall n n' V T hp,
fst (return_smallest_match n (marked_heap (marked_heap' hp n') n')) = false -> (*restricted to "low to low" case*)
marked_heap_replace n (V,T) (marked_heap (marked_heap' hp n') n') 
= heap_replace (snd(snd(return_smallest_match n (marked_heap (marked_heap' hp n') n'))))(V,T) (marked_heap (marked_heap' hp n') n').      
Proof. intros. generalize dependent n. generalize dependent n'. generalize dependent V. generalize dependent T.
induction hp. 
Case ("nil"). intros. simpl in H0. inversion H0.
Case ("h::t"). intros. destruct a. simpl. destruct n'. simpl. remember (SecLang.label t) as BB.
              destruct BB. simpl. destruct n. simpl. reflexivity. assert (0<=0). apply le_n.
             apply return_smallest_match_snd_Sn_n with(hp:=hp)(n:=n) in H1. rewrite->H1. clear H1.
             simpl. assert (0<=0). apply le_n. apply add_both_mark_marked_heap_replace with (hp:=hp)(n:=n)(V:=V)(T:=T)in H1.
              rewrite->H1. clear H1. assert (0<=0). apply le_n. 
             apply add_both_mark_heap_replace with (hp:=hp)(n:=snd (snd (return_smallest_match n (marked_heap (marked_heap' hp 0) 0))))(V:=V)(T:=T) in H1.
             rewrite->H1. clear H1. specialize (IHhp T V 0 n). simpl in H0. rewrite<-HeqBB in H0. simpl in H0. rewrite->return_smallest_match_Sn_n with (n:=n)(n1:=0)(n2:=0)in H0.
             apply IHhp in H0. rewrite->H0. reflexivity. apply IHhp. simpl in H0. rewrite<-HeqBB in H0. apply H0.
             simpl.
             remember (SecLang.label t) as BB. destruct BB. simpl. destruct n. assert (0<S n'). apply SecLang.n_iff_Sn_left. apply SecLang.zero_n. apply return_true_marked_heap with (hp:=((t,t0)::hp))(n2:=(S n'))in H1.
             rewrite<-H1 in H0. clear H1. inversion H0. simpl. remember (beq_nat n' n) as CC. destruct CC.
             simpl. rewrite->minus_diag. simpl. reflexivity. rewrite->minus_diag. 
             assert (S n'<=S n'). apply le_n. apply return_smallest_match_snd_Sn_n with(hp:=hp)(n:=n) in H1. rewrite->H1. clear H1. simpl.
             assert (S n'<=S n'). apply le_n. apply add_both_mark_marked_heap_replace with (hp:=hp)(n:=n)(V:=V)(T:=T)in H1.
              rewrite->H1. clear H1. assert (S n'<=S n'). apply le_n. 
             apply add_both_mark_heap_replace with (hp:=hp)(n:=snd (snd (return_smallest_match n (marked_heap (marked_heap' hp (S n')) (S n')))))(V:=V)(T:=T) in H1.
             rewrite->H1. clear H1. specialize (IHhp T V (S n') n). simpl in H0. rewrite<-HeqBB in H0. simpl in H0. rewrite<-HeqCC in H0. rewrite->return_smallest_match_Sn_n with (n:=n)(n1:=S n')(n2:=S n')in H0.
             apply IHhp in H0. rewrite->H0. reflexivity. apply IHhp. simpl in H0. rewrite<-HeqBB in H0. apply H0.
Qed.
       
Lemma marked_heap_replace_project_conf'_hp:forall n v T HP HP',
marked_heap_replace n (project_conf'_e v HP',T)(project_conf'_hp HP HP')
=project_conf'_hp (marked_heap_replace n (v,T) HP) HP'.
Proof. intros. generalize dependent n. generalize dependent v. generalize dependent T. generalize dependent HP'.
induction HP.
Case ("nil"). intros. reflexivity.
Case ("h::t"). intros. destruct a. destruct p.  destruct p0. simpl. remember (beq_nat n0 n) as BB. destruct BB.
              simpl. reflexivity. simpl. specialize (IHHP HP' T v n). rewrite->IHHP. reflexivity.
Qed.

Lemma heap_replace_project_conf'_hp:forall n v T HP HP',
heap_replace n (project_conf'_e v HP',T)(project_conf'_hp HP HP')
=project_conf'_hp (heap_replace n (v,T) HP) HP'. 
Proof. intros. generalize dependent n. generalize dependent v. generalize dependent T.
generalize dependent HP'. induction HP.
Case ("nil"). intros. destruct n. reflexivity. reflexivity.
Case ("h::t"). intros. destruct a. destruct p. destruct p0. simpl. destruct n. simpl. reflexivity.
              simpl. specialize (IHHP HP' T v n). rewrite->IHHP. reflexivity.
Qed.


Lemma marked_heap_replace_heap_replace:forall n v T hp,
fst (return_smallest_match n (project_hp hp)) = false -> (*restricted to "low to low" case*)
marked_heap_replace n (project_conf'_e (project_e v)(project_conf'_hp (project_hp hp)(project_hp hp)),T) (project_conf'_hp (project_hp hp)(project_hp hp)) 
= heap_replace (snd(snd(return_smallest_match n (project_conf'_hp (project_hp hp)(project_hp hp)))))
  (project_conf'_e (project_e v)(project_conf'_hp (project_hp hp)(project_hp hp)),T) 
  (project_conf'_hp (project_hp hp)(project_hp hp)). 
Proof. intros. assert (same_mark (project_hp hp)(project_conf'_hp (project_hp hp)(project_hp hp))=true). apply same_mark_heap. apply project_conf'_e_same_mark with(t:=project_e v)in H1.
      rewrite<-H1. clear H1. rewrite->marked_heap_replace_project_conf'_hp.
      assert (same_mark (project_hp hp)(project_conf'_hp (project_hp hp)(project_hp hp))=true). apply same_mark_heap.  apply return_smallest_match_same_mark' with (n:=n)in H1.
      rewrite<-H1. clear H1. rewrite->heap_replace_project_conf'_hp. unfold project_hp in H0. apply marked_heap_replace_heap_replace' with (V:=project_e v)(T:=T)in H0. unfold project_hp.
      rewrite<-H0. reflexivity.
Qed.

Lemma project_conf'_hp_heap_replace':forall v T n hp,
SecLang.value v ->
SecLang.label v = SecLang.label (SecLang.efst (SecLang.heap_lookup n hp))->
fst (return_smallest_match n (project_hp hp)) = false ->
project_conf'_hp (project_hp (SecLang.heap_replace n (v,T) hp))(project_hp (SecLang.heap_replace n (v,T) hp)) 
=heap_replace (snd(snd(return_smallest_match n (project_conf'_hp (project_hp hp)(project_hp hp)))))
  (project_conf'_e (project_e v)(project_conf'_hp (project_hp hp)(project_hp hp)),T) 
  (project_conf'_hp (project_hp hp)(project_hp hp)). 
Proof.  intros. apply project_conf'_hp_marked_heap_replace with(T:=T)(n:=n)(hp:=hp) in H0. 
       apply marked_heap_replace_heap_replace with(v:=v)(T:=T)in H2. rewrite->H2 in H0. apply H0. apply return_smallest_match_F_length in H2.
       apply H2. apply H1.
Qed.

Lemma project_conf'_hp_heap_replace'':forall N V T HP,
erase_hp (heap_replace N (V,T) HP)
=LowLang.heap_replace N (V,T)(erase_hp HP).
Proof. intros. generalize dependent N. generalize dependent V. generalize dependent T.
induction HP. 
Case ("nil"). intros. destruct N. reflexivity. reflexivity.
Case ("h::t"). intros. destruct a. destruct p. destruct N. simpl. reflexivity.
              simpl. specialize (IHHP T V N). rewrite->IHHP. reflexivity.
Qed.

Lemma project_conf'_hp_heap_replace:forall v T n hp,
SecLang.value v ->
SecLang.label v = SecLang.label (SecLang.efst (SecLang.heap_lookup n hp))->
fst (return_smallest_match n (project_hp hp)) = false ->
erase_hp (project_conf'_hp (project_hp (SecLang.heap_replace n (v,T) hp))(project_hp (SecLang.heap_replace n (v,T) hp)))
=LowLang.heap_replace (snd(snd(return_smallest_match n (project_hp hp))))
  (project_conf'_e (project_e v)(project_conf'_hp (project_hp hp)(project_hp hp)),T) 
  (erase_hp (project_conf'_hp (project_hp hp)(project_hp hp))). 
Proof. intros. assert (same_mark (project_hp hp)(project_conf'_hp (project_hp hp)(project_hp hp))=true). apply same_mark_heap.  
       apply return_smallest_match_same_mark' with (n:=n)in H3. rewrite->H3. clear H3. rewrite<-project_conf'_hp_heap_replace''.
       apply project_conf'_hp_heap_replace' with(T:=T)(n:=n)(hp:=hp)in H0. rewrite<-H0. reflexivity.
       apply H1. apply H2.
Qed.


Lemma return_smallest_match_snd_length:forall n hp,
fst (return_smallest_match n (marked_heap(marked_heap' hp 0)0)) = false ->
snd(snd(return_smallest_match n (marked_heap(marked_heap' hp 0)0))) < length (marked_heap(marked_heap' hp 0)0).
Proof. intros. generalize dependent n. induction hp. 
Case ("nil"). intros. simpl in H0. inversion H0.
Case ("h::t"). intros. destruct a. simpl. remember (SecLang.label t) as BB. destruct BB. simpl. destruct n. simpl.
              apply SecLang.n_iff_Sn_left. apply SecLang.zero_n. assert (0<=0). apply le_n.
              apply return_smallest_match_snd_Sn_n with (hp:=hp)(n:=n) in H1. rewrite->H1. clear H1. apply SecLang.n_iff_Sn_left.
              rewrite->marked_heap_mark_length with (n3:=0)(n4:=0). simpl in H0. rewrite<-HeqBB in H0. simpl in H0. 
              rewrite->return_smallest_match_Sn_n with (n2:=0)in H0. apply IHhp. apply H0. simpl in H0. rewrite<-HeqBB in H0.
              destruct n. assert (0<1). apply le_n. apply return_true_marked_heap with (hp:=hp)(n2:=1)in H1. rewrite<-H1 in H0. clear H1.
              inversion H0. assert (fst (return_smallest_match (S n)(marked_heap(marked_heap' hp 1)1))=false). apply H0. 
              rewrite->return_smallest_match_Sn_Sn with(n2:=0)in H1. apply return_smallest_match_snd_Sn_Sn in H1.
              rewrite->H1. clear H1. rewrite->marked_heap_mark_length with(n3:=0)(n4:=0). apply IHhp.
              rewrite->return_smallest_match_Sn_Sn with(n2:=0)in H0. apply H0.
Qed.


(*##################*)
Lemma corresp_step:forall e e' hp hp',
SecLang.step (e,hp) L (e',hp') ->
LowLang.Multi LowLang.step (project (e,hp)) L (project (e',hp')).
Proof. intros. induction H0. (*induction upon the reduction relation in [SecLang]*)
Case ("st_prot").
                 intros. destruct b. simpl. destruct PC. simpl in H0. apply IHstep. simpl in IHstep. apply IHstep. 
                 destruct PC. simpl in IHstep. unfold project. simpl. simpl in H0. apply proj_hp_H_same in H2. rewrite->H2. 
                 apply LowLang.Multi_refl.
                 unfold project. simpl. simpl in H2. apply proj_hp_H_same in H2. rewrite->H2. apply LowLang.Multi_refl.
Case ("st_protv"). 
                 destruct b. unfold project. simpl. inversion H2.
                 rewrite->SecLang.join_tcon_b. rewrite->SecLang.joins_refl. simpl. apply LowLang.Multi_refl. rewrite->SecLang.join_tabs_b.
                 rewrite->SecLang.joins_refl. simpl. apply LowLang.Multi_refl. rewrite->SecLang.join_tunit_b. rewrite->SecLang.joins_refl.
                 simpl. apply LowLang.Multi_refl. rewrite->SecLang.join_tloc_b. rewrite->SecLang.joins_refl. simpl. apply LowLang.Multi_refl.
                 inversion H2. rewrite->SecLang.join_tcon_b. rewrite->SecLang.joins_refl. simpl. apply LowLang.Multi_refl.
                 rewrite->SecLang.join_tabs_b. rewrite->SecLang.joins_refl. simpl. apply LowLang.Multi_refl. rewrite->SecLang.join_tunit_b.
                 rewrite->SecLang.joins_refl. simpl. apply LowLang.Multi_refl. rewrite->SecLang.join_tloc_b. rewrite->SecLang.joins_refl. simpl.
                 apply LowLang.Multi_refl.
Case ("st_appabs").
                 destruct b. unfold project. simpl.  unfold project_conf. simpl. rewrite->project_e_subst. rewrite->project_conf'_subst. 
                 apply LowLang.Multi_step with (y:=(LowLang.subst x
     (project_conf'_e (project_e v)
        (project_conf'_hp (project_hp hp0) (project_hp hp0)))
     (project_conf'_e (project_e e0)
        (project_conf'_hp (project_hp hp0) (project_hp hp0))),
  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))). 
                 apply LowLang.st_appabs. apply SecLang_value_LowLang. apply H3. apply LowLang.Multi_refl. apply H3. unfold project. simpl. unfold project_conf.
                 simpl. apply LowLang.Multi_step with (y:=(LowLang.tH,
                 erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))). apply LowLang.st_apptH.
                 apply SecLang_value_LowLang. apply H3. apply LowLang.Multi_refl.
Case ("st_app1").
                 unfold project. unfold project_conf. unfold project in IHstep. unfold project_conf in IHstep. simpl. simpl in IHstep.
                 destruct PC. 
                 SCase ("PC:=L").  apply step_same_mark_or_extend in H3. inversion H3.
                                  (*case one: two heaps of the same length with identical marks*)
                                   assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap.
                                   assert (same_mark (project_conf'_hp (project_hp hp0) (project_hp hp0))(project_hp hp'0) = true). apply same_mark_replace with (hp1:=project_hp hp0).
                                   apply H4. apply H5. apply same_mark_sym in H6. assert (same_mark (project_hp hp'0)(project_conf'_hp (project_hp hp'0) (project_hp hp'0)) = true). 
                                   apply same_mark_heap. assert (same_mark (project_conf'_hp (project_hp hp0) (project_hp hp0))(project_conf'_hp (project_hp hp'0) (project_hp hp'0)) = true).
                                   apply same_mark_replace with (hp1:=project_hp hp'0). apply H7. apply H6. apply project_conf'_e_same_mark with (t:=project_e t2)in H8. rewrite->H8. clear H4.
                                   clear H5. clear H6. clear H7. clear H8. 
                                   assert (fst (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)))). reflexivity. rewrite<-H4. clear H4.
                                  assert (snd (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))).
                                  reflexivity. rewrite<-H4. clear H4. 
                                  assert (fst (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) = (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))). reflexivity. rewrite<-H4. clear H4.
                                  assert (snd (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) =  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))).
                                  reflexivity. rewrite<-H4. clear H4. apply multi_step_app1. apply IHstep.
                                  (*case two: after reduction heap is expanded by one low value*)
                                  inversion H4. assert (project_conf'_e (project_e t2)
                                  (project_conf'_hp (project_hp hp'0) (project_hp hp'0)) = project_conf'_e (project_e t2)
                                  (project_conf'_hp ((LowLang.snoc (project_hp hp0) (x, (length hp0, length (project_hp hp0))))) ((LowLang.snoc (project_hp hp0) (x, (length hp0, length (project_hp hp0))))))).
                                  rewrite<-H5. reflexivity. rewrite->H6. assert ((project_conf'_e (project_e t2)
                                  (project_conf'_hp (project_hp hp0) (project_hp hp0))) = (project_conf'_e (project_e t2)
                                  (project_conf'_hp
                                  (LowLang.snoc (project_hp hp0)
                                  (x, (length hp0, length (project_hp hp0))))
                                  (LowLang.snoc (project_hp hp0)
                                  (x, (length hp0, length (project_hp hp0))))))). apply project_conf'_e_add_one_low. apply H2. rewrite<-H7. clear H5. clear H6. clear H7. 
                                   assert (fst (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)))). reflexivity. rewrite<-H5. clear H5.
                                  assert (snd (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))).
                                  reflexivity. rewrite<-H5. clear H5. 
                                  assert (fst (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) = (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))). reflexivity. rewrite<-H5. clear H5.
                                  assert (snd (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) =  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))).
                                  reflexivity. rewrite<-H5. clear H5. apply multi_step_app1. apply IHstep.                                 
                 SCase ("PC:=H"). apply proj_hp_H_same in H3. assert (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)) = project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0))). rewrite->H3. reflexivity. rewrite->H4. clear H4.
                                  assert (fst (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)))). reflexivity. rewrite<-H4. clear H4.
                                  assert (snd (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))).
                                  reflexivity. rewrite<-H4. clear H4. 
                                  assert (fst (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) = (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))). reflexivity. rewrite<-H4. clear H4.
                                  assert (snd (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) =  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))).
                                  reflexivity. rewrite<-H4. clear H4. apply multi_step_app1. apply IHstep.
Case ("tapp2"). 
               unfold project. unfold project_conf. unfold project in IHstep. unfold project_conf in IHstep. simpl. simpl in IHstep.
                 destruct PC. 
                 SCase ("PC:=L").  apply step_same_mark_or_extend in H4. inversion H4.
                                  (*case one: two heaps of the same length with identical marks*)
                                   assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap.
                                   assert (same_mark (project_conf'_hp (project_hp hp0) (project_hp hp0))(project_hp hp'0) = true). apply same_mark_replace with (hp1:=project_hp hp0).
                                   apply H5. apply H6. apply same_mark_sym in H7. assert (same_mark (project_hp hp'0)(project_conf'_hp (project_hp hp'0) (project_hp hp'0)) = true). 
                                   apply same_mark_heap. assert (same_mark (project_conf'_hp (project_hp hp0) (project_hp hp0))(project_conf'_hp (project_hp hp'0) (project_hp hp'0)) = true).
                                   apply same_mark_replace with (hp1:=project_hp hp'0). apply H8. apply H7. apply project_conf'_e_same_mark with (t:=project_e v1)in H9. rewrite->H9. clear H5.
                                   clear H6. clear H7. clear H8. clear H9. 
                                   assert (fst (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)))). reflexivity. rewrite<-H5. clear H5.
                                  assert (snd (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))).
                                  reflexivity. rewrite<-H5. clear H5. 
                                  assert (fst (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) = (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))). reflexivity. rewrite<-H5. clear H5.
                                  assert (snd (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) =  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))).
                                  reflexivity. rewrite<-H5. clear H5. apply multi_step_app2. apply SecLang_value_LowLang. apply H3.
                                 apply IHstep.
                                  (*case two: after reduction heap is expanded by one low value*)
                                  inversion H5. assert (project_conf'_e (project_e v1)
                                  (project_conf'_hp (project_hp hp'0) (project_hp hp'0)) = project_conf'_e (project_e v1)
                                  (project_conf'_hp ((LowLang.snoc (project_hp hp0) (x, (length hp0, length (project_hp hp0))))) ((LowLang.snoc (project_hp hp0) (x, (length hp0, length (project_hp hp0))))))).
                                  rewrite<-H6. reflexivity. rewrite->H7. assert ((project_conf'_e (project_e v1)
                                  (project_conf'_hp (project_hp hp0) (project_hp hp0))) = (project_conf'_e (project_e v1)
                                  (project_conf'_hp
                                  (LowLang.snoc (project_hp hp0)
                                  (x, (length hp0, length (project_hp hp0))))
                                  (LowLang.snoc (project_hp hp0)
                                  (x, (length hp0, length (project_hp hp0))))))). apply project_conf'_e_add_one_low. apply H1. rewrite<-H8. clear H6. clear H7. clear H8. 
                                   assert (fst (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)))). reflexivity. rewrite<-H6. clear H6.
                                  assert (snd (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))).
                                  reflexivity. rewrite<-H6. clear H6. 
                                  assert (fst (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) = (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))). reflexivity. rewrite<-H6. clear H6.
                                  assert (snd (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) =  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))).
                                  reflexivity. rewrite<-H6. clear H6. apply multi_step_app2. apply SecLang_value_LowLang. apply H3.
                                  apply IHstep.                                 
                 SCase ("PC:=H"). apply proj_hp_H_same in H4. assert (project_conf'_e (project_e v1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)) = project_conf'_e (project_e v1)
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0))). rewrite->H4. reflexivity. rewrite->H5. clear H5.
                                  assert (fst (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)))). reflexivity. rewrite<-H5. clear H5.
                                  assert (snd (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))).
                                  reflexivity. rewrite<-H5. clear H5. 
                                  assert (fst (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) = (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))). reflexivity. rewrite<-H5. clear H5.
                                  assert (snd (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) =  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))).
                                  reflexivity. rewrite<-H5. clear H5. apply multi_step_app2. apply SecLang_value_LowLang. apply H3. apply IHstep.
Case ("st_refv").
                subst. destruct b.
                unfold project. unfold project_conf. simpl. 
                inversion H2.
                (*v=SecLang.tcon n b*)
                destruct b. destruct T. destruct s. destruct PC. simpl. rewrite->SecLang.join_tcon_b. simpl. subst.
                apply project_hp_Lextend with (hp:=hp0)(T:=an r L) in H2. rewrite->H2. simpl. assert (LowLang.value (LowLang.tcon n)). apply LowLang.v_c. apply return_smallest_match_snoc with (hp:=hp0)(T:=an r L) in H3.
                rewrite->H3. simpl. assert (Some (length (project_hp hp0)) = Some (length (project_conf'_hp(project_hp hp0)(project_hp hp0)))). rewrite->project_conf'_hp_length. reflexivity. rewrite->H4. clear H4.
                assert (Some (length (project_conf'_hp(project_hp hp0)(project_hp hp0))) = Some (length (erase_hp (project_conf'_hp(project_hp hp0)(project_hp hp0))))). rewrite->erase_hp_length. reflexivity. rewrite->H4.
                clear H4. rewrite->project_conf'_hp_snoc. simpl. apply project_conf'_hp_add_one_low with (L0:=(LowLang.tcon n,an r L))in H0. rewrite->H0. apply LowLang.Multi_step with (y:=(LowLang.tloc (an r L)
                (Some
                (length
                (erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))))),
                 erase_hp
                (LowLang.snoc (project_conf'_hp (project_hp hp0) (project_hp hp0))
                (LowLang.tcon n, an r L, (length hp0, length (project_hp hp0)))))). apply LowLang.st_refv. apply LowLang.v_c. intros contra. inversion contra. reflexivity. reflexivity.
                 rewrite->erase_hp_snoc. reflexivity. apply LowLang.Multi_refl. intros contra. inversion contra. reflexivity. simpl. subst. apply project_hp_Hextend with(hp:=hp0)(T:=an r L) in H2.
                 rewrite<-H2. assert (same_mark (project_conf'_hp (project_hp hp0)(project_hp hp0))(project_hp hp0) = true). apply same_mark_sym. apply same_mark_heap. apply return_smallest_match_same_mark with (n:=length hp0)in H3. rewrite->H3.
                 rewrite->return_smallest_match_true. clear H3. assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=length hp0)in H3. rewrite<-H3.
                 rewrite->return_smallest_match_true. simpl. apply LowLang.Multi_step with (y:=(LowLang.tloc (an r L) None,
  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))). apply LowLang.st_reftH. apply LowLang.v_c. right. left. reflexivity. apply LowLang.Multi_refl. simpl. subst. apply project_hp_Hextend with(hp:=hp0)(T:=an r H) in H2. rewrite<-H2. 
  assert (same_mark (project_conf'_hp (project_hp hp0)(project_hp hp0))(project_hp hp0) = true). apply same_mark_sym. apply same_mark_heap. apply return_smallest_match_same_mark with (n:=length hp0)in H3. rewrite->H3.
                 rewrite->return_smallest_match_true. clear H3. assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=length hp0)in H3. rewrite<-H3.
                 rewrite->return_smallest_match_true. simpl. apply LowLang.Multi_step with (y:=((LowLang.tloc (an r H) None,
  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))))). apply LowLang.st_reftH. apply LowLang.v_c. right. right. reflexivity. apply LowLang.Multi_refl. subst. rewrite->SecLang.join_tcon_b. simpl. assert (SecLang.joinvs (SecLang.tcon n L) H = SecLang.tcon n H). reflexivity.
                  rewrite<-H3. clear H3. assert (SecLang.value (SecLang.tcon n L)). apply SecLang.v_c. apply project_hp_Hextend with(hp:=hp0)(T:=T) in H3. rewrite<-H3. clear H3.  
  assert (same_mark (project_conf'_hp (project_hp hp0)(project_hp hp0))(project_hp hp0) = true). apply same_mark_sym. apply same_mark_heap. apply return_smallest_match_same_mark with (n:=length hp0)in H3. rewrite->H3.
                 rewrite->return_smallest_match_true. clear H3. assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=length hp0)in H3. rewrite<-H3.
                 rewrite->return_smallest_match_true. simpl. apply LowLang.Multi_step with (y:=((LowLang.tloc T None,
  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))))). apply LowLang.st_reftH. apply LowLang.v_H. left. reflexivity. apply LowLang.Multi_refl.
                 (*v=SecLang.tabs (Id n) T0 e0 b*)
                 destruct b. destruct T. destruct s. destruct PC. simpl. rewrite->SecLang.join_tabs_b. simpl. subst.
                apply project_hp_Lextend with (hp:=hp0)(T:=an r L) in H2. rewrite->H2. simpl. assert (LowLang.value (LowLang.tabs (Id n) T0 (project_e e0))). apply LowLang.v_f. apply return_smallest_match_snoc with (hp:=hp0)(T:=an r L) in H3.
                rewrite->H3. simpl. assert (Some (length (project_hp hp0)) = Some (length (project_conf'_hp(project_hp hp0)(project_hp hp0)))). rewrite->project_conf'_hp_length. reflexivity. rewrite->H4. clear H4.
                assert (Some (length (project_conf'_hp(project_hp hp0)(project_hp hp0))) = Some (length (erase_hp (project_conf'_hp(project_hp hp0)(project_hp hp0))))). rewrite->erase_hp_length. reflexivity. rewrite->H4.
                clear H4. rewrite->project_conf'_hp_snoc. simpl. apply project_conf'_hp_add_one_low with (L0:=(LowLang.tabs (Id n) T0 (project_e e0),an r L))in H0. rewrite->H0. apply LowLang.Multi_step with (y:= (LowLang.tloc (an r L)
               (Some
               (length
               (erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))))),
                erase_hp
               (LowLang.snoc (project_conf'_hp (project_hp hp0) (project_hp hp0))
               (LowLang.tabs (Id n) T0
               (project_conf'_e (project_e e0)
               (LowLang.snoc (project_hp hp0)
               (LowLang.tabs (Id n) T0 (project_e e0), an r L,
               (length hp0, length (project_hp hp0))))), an r L,
               (length hp0, length (project_hp hp0)))))). 
                 apply LowLang.st_refv. apply LowLang.v_f. intros contra. inversion contra. reflexivity. reflexivity.
                 rewrite->erase_hp_snoc. inversion H1. subst. apply SecLow_well_formed in H9. apply project_conf'_e_add_one_low' with(Hp:=project_hp hp0)(L0:=(LowLang.tabs (Id n) T0 (project_e e0),an r L)) in H9. rewrite<-H9.
                assert (same_mark (project_conf'_hp (project_hp hp0)(project_hp hp0))(project_hp hp0) = true). apply same_mark_sym. apply same_mark_heap. apply project_conf'_e_same_mark with (t:=project_e e0) in H4. rewrite->H4.
                clear H4.  
                 reflexivity. apply LowLang.Multi_refl. intros contra. inversion contra. reflexivity. simpl. subst. apply project_hp_Hextend with(hp:=hp0)(T:=an r L) in H2.
                 rewrite<-H2. assert (same_mark (project_conf'_hp (project_hp hp0)(project_hp hp0))(project_hp hp0) = true). apply same_mark_sym. apply same_mark_heap. apply return_smallest_match_same_mark with (n:=length hp0)in H3. rewrite->H3.
                 rewrite->return_smallest_match_true. clear H3. assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=length hp0)in H3. rewrite<-H3.
                 rewrite->return_smallest_match_true. simpl. apply LowLang.Multi_step with (y:=(LowLang.tloc (an r L) None,
  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))). apply LowLang.st_reftH. apply LowLang.v_f. right. left. reflexivity. apply LowLang.Multi_refl. simpl. subst. apply project_hp_Hextend with(hp:=hp0)(T:=an r H) in H2. rewrite<-H2. 
  assert (same_mark (project_conf'_hp (project_hp hp0)(project_hp hp0))(project_hp hp0) = true). apply same_mark_sym. apply same_mark_heap. apply return_smallest_match_same_mark with (n:=length hp0)in H3. rewrite->H3.
                 rewrite->return_smallest_match_true. clear H3. assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=length hp0)in H3. rewrite<-H3.
                 rewrite->return_smallest_match_true. simpl. apply LowLang.Multi_step with (y:=((LowLang.tloc (an r H) None,
  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))))). apply LowLang.st_reftH. apply LowLang.v_f. right. right. reflexivity. apply LowLang.Multi_refl. subst. rewrite->SecLang.join_tabs_b. simpl. assert (SecLang.joinvs (SecLang.tabs (Id n) T0 e0 L) H = SecLang.tabs (Id n) T0 e0 H). reflexivity.
                  rewrite<-H3. clear H3. assert (SecLang.value (SecLang.tabs (Id n) T0 e0 L)). apply SecLang.v_f. apply project_hp_Hextend with(hp:=hp0)(T:=T) in H3. rewrite<-H3. clear H3.  
  assert (same_mark (project_conf'_hp (project_hp hp0)(project_hp hp0))(project_hp hp0) = true). apply same_mark_sym. apply same_mark_heap. apply return_smallest_match_same_mark with (n:=length hp0)in H3. rewrite->H3.
                 rewrite->return_smallest_match_true. clear H3. assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=length hp0)in H3. rewrite<-H3.
                 rewrite->return_smallest_match_true. simpl. apply LowLang.Multi_step with (y:=((LowLang.tloc T None,
  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))))). apply LowLang.st_reftH. apply LowLang.v_H. left. reflexivity. apply LowLang.Multi_refl.
                 (*v=tunit b*) 
                destruct b. destruct T. destruct s. destruct PC. simpl. rewrite->SecLang.join_tunit_b. simpl. subst.
                apply project_hp_Lextend with (hp:=hp0)(T:=an r L) in H2. rewrite->H2. simpl. assert (LowLang.value (LowLang.tunit)). apply LowLang.v_u. apply return_smallest_match_snoc with (hp:=hp0)(T:=an r L) in H3.
                rewrite->H3. simpl. assert (Some (length (project_hp hp0)) = Some (length (project_conf'_hp(project_hp hp0)(project_hp hp0)))). rewrite->project_conf'_hp_length. reflexivity. rewrite->H4. clear H4.
                assert (Some (length (project_conf'_hp(project_hp hp0)(project_hp hp0))) = Some (length (erase_hp (project_conf'_hp(project_hp hp0)(project_hp hp0))))). rewrite->erase_hp_length. reflexivity. rewrite->H4.
                clear H4. rewrite->project_conf'_hp_snoc. simpl. apply project_conf'_hp_add_one_low with (L0:=(LowLang.tunit,an r L))in H0. rewrite->H0. apply LowLang.Multi_step with (y:=(LowLang.tloc (an r L)
                (Some
                (length
                (erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))))),
                 erase_hp
                (LowLang.snoc (project_conf'_hp (project_hp hp0) (project_hp hp0))
                (LowLang.tunit, an r L, (length hp0, length (project_hp hp0)))))). apply LowLang.st_refv. apply LowLang.v_u. intros contra. inversion contra. reflexivity. reflexivity.
                 rewrite->erase_hp_snoc. reflexivity. apply LowLang.Multi_refl. intros contra. inversion contra. reflexivity. simpl. subst. apply project_hp_Hextend with(hp:=hp0)(T:=an r L) in H2.
                 rewrite<-H2. assert (same_mark (project_conf'_hp (project_hp hp0)(project_hp hp0))(project_hp hp0) = true). apply same_mark_sym. apply same_mark_heap. apply return_smallest_match_same_mark with (n:=length hp0)in H3. rewrite->H3.
                 rewrite->return_smallest_match_true. clear H3. assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=length hp0)in H3. rewrite<-H3.
                 rewrite->return_smallest_match_true. simpl. apply LowLang.Multi_step with (y:=(LowLang.tloc (an r L) None,
  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))). apply LowLang.st_reftH. apply LowLang.v_u. right. left. reflexivity. apply LowLang.Multi_refl. simpl. subst. apply project_hp_Hextend with(hp:=hp0)(T:=an r H) in H2. rewrite<-H2. 
  assert (same_mark (project_conf'_hp (project_hp hp0)(project_hp hp0))(project_hp hp0) = true). apply same_mark_sym. apply same_mark_heap. apply return_smallest_match_same_mark with (n:=length hp0)in H3. rewrite->H3.
                 rewrite->return_smallest_match_true. clear H3. assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=length hp0)in H3. rewrite<-H3.
                 rewrite->return_smallest_match_true. simpl. apply LowLang.Multi_step with (y:=((LowLang.tloc (an r H) None,
  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))))). apply LowLang.st_reftH. apply LowLang.v_u. right. right. reflexivity. apply LowLang.Multi_refl. subst. rewrite->SecLang.join_tunit_b. simpl. assert (SecLang.joinvs (SecLang.tunit L) H = SecLang.tunit H). reflexivity.
                  rewrite<-H3. clear H3. assert (SecLang.value (SecLang.tunit L)). apply SecLang.v_u. apply project_hp_Hextend with(hp:=hp0)(T:=T) in H3. rewrite<-H3. clear H3.  
  assert (same_mark (project_conf'_hp (project_hp hp0)(project_hp hp0))(project_hp hp0) = true). apply same_mark_sym. apply same_mark_heap. apply return_smallest_match_same_mark with (n:=length hp0)in H3. rewrite->H3.
                 rewrite->return_smallest_match_true. clear H3. assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=length hp0)in H3. rewrite<-H3.
                 rewrite->return_smallest_match_true. simpl. apply LowLang.Multi_step with (y:=((LowLang.tloc T None,
  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))))). apply LowLang.st_reftH. apply LowLang.v_H. left. reflexivity. apply LowLang.Multi_refl.
                 (*v = SecLang.tloc T0 (Some n) b *)
                destruct b. destruct T. destruct s. destruct PC. simpl. rewrite->SecLang.join_tloc_b. simpl. subst.
                apply project_hp_Lextend with (hp:=hp0)(T:=an r L) in H2. rewrite->H2. simpl. assert (LowLang.value (LowLang.tloc T0 (Some n))). apply LowLang.v_l. apply return_smallest_match_snoc with (hp:=hp0)(T:=an r L) in H3.
                rewrite->H3. simpl. assert (Some (length (project_hp hp0)) = Some (length (project_conf'_hp(project_hp hp0)(project_hp hp0)))). rewrite->project_conf'_hp_length. reflexivity. rewrite->H4. clear H4.
                assert (Some (length (project_conf'_hp(project_hp hp0)(project_hp hp0))) = Some (length (erase_hp (project_conf'_hp(project_hp hp0)(project_hp hp0))))). rewrite->erase_hp_length. reflexivity. rewrite->H4.
                clear H4. rewrite->project_conf'_hp_snoc. simpl. apply project_conf'_hp_add_one_low with (L0:=(LowLang.tloc T0 (Some n),an r L))in H0. rewrite->H0. inversion H1. subst. assert (n<>length hp0). intros contra. rewrite<-contra in H8. apply LowLang.lt_same_F in H8. inversion H8.
                apply return_smallest_match_not_hit_snoc with (n3:=length (project_hp hp0))(L:=(LowLang.tloc T0 (Some n),an r L))(hp:=project_hp hp0) in H4. rewrite->H4.  assert (same_mark (project_conf'_hp (project_hp hp0)(project_hp hp0))(project_hp hp0) = true). apply same_mark_sym. apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=n)in H5. rewrite->H5.
                clear H5. 
                apply LowLang.Multi_step with (y:=(LowLang.tloc (an r L)
                (Some
                (length
                (erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))))),
                 erase_hp
                (LowLang.snoc (project_conf'_hp (project_hp hp0) (project_hp hp0))
                (if fst (return_smallest_match n (project_hp hp0))
                 then LowLang.tloc T0 None
                else
                LowLang.tloc T0
               (Some (snd (snd (return_smallest_match n (project_hp hp0))))),
                an r L, (length hp0, length (project_hp hp0)))))). apply LowLang.st_refv. remember (fst (return_smallest_match n (project_hp hp0))) as BB. destruct BB. 
                 apply LowLang.v_l. apply LowLang.v_l. remember (fst (return_smallest_match n (project_hp hp0))) as BB. destruct BB.
                 intros contra. inversion contra. intros contra. inversion contra. reflexivity. reflexivity.
                 rewrite->erase_hp_snoc. reflexivity. apply LowLang.Multi_refl. intros contra. inversion contra. reflexivity. simpl. subst. apply project_hp_Hextend with(hp:=hp0)(T:=an r L) in H2.
                 rewrite<-H2. assert (same_mark (project_conf'_hp (project_hp hp0)(project_hp hp0))(project_hp hp0) = true). apply same_mark_sym. apply same_mark_heap. apply return_smallest_match_same_mark with (n:=length hp0)in H3. rewrite->H3.
                 rewrite->return_smallest_match_true. clear H3. assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=length hp0)in H3. rewrite<-H3.
                 rewrite->return_smallest_match_true. simpl.  assert (same_mark (project_conf'_hp (project_hp hp0)(project_hp hp0))(project_hp hp0) = true). apply same_mark_sym. apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=n)in H4. rewrite->H4.
                 clear H4. clear H3. remember (fst (return_smallest_match n (project_hp hp0))) as BB. destruct BB.
                 apply LowLang.Multi_step with (y:=(LowLang.tloc (an r L) None,
  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))). apply LowLang.st_reftH. apply LowLang.v_l. right. left. reflexivity. 
  apply LowLang.Multi_refl.
  apply LowLang.Multi_step with (y:=(LowLang.tloc (an r L) None,
  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))). apply LowLang.st_reftH. apply LowLang.v_l. right. left. reflexivity. 
  apply LowLang.Multi_refl.
 simpl. subst. apply project_hp_Hextend with(hp:=hp0)(T:=an r H) in H2. rewrite<-H2. 
  assert (same_mark (project_conf'_hp (project_hp hp0)(project_hp hp0))(project_hp hp0) = true). apply same_mark_sym. apply same_mark_heap. apply return_smallest_match_same_mark with (n:=length hp0)in H3. rewrite->H3.
                 rewrite->return_smallest_match_true. clear H3. assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=length hp0)in H3. rewrite<-H3.
                 rewrite->return_smallest_match_true. simpl.
  assert (same_mark (project_conf'_hp (project_hp hp0)(project_hp hp0))(project_hp hp0) = true). apply same_mark_sym. apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=n)in H4. rewrite->H4.
                 clear H4. clear H3. remember (fst (return_smallest_match n (project_hp hp0))) as BB. destruct BB.
 apply LowLang.Multi_step with (y:=((LowLang.tloc (an r H) None,
  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))))). apply LowLang.st_reftH. apply LowLang.v_l. right. right. reflexivity. apply LowLang.Multi_refl.
 apply LowLang.Multi_step with (y:=((LowLang.tloc (an r H) None,
  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))))). apply LowLang.st_reftH. apply LowLang.v_l. right. right. reflexivity. apply LowLang.Multi_refl.
 subst. rewrite->SecLang.join_tloc_b. simpl. assert (SecLang.joinvs (SecLang.tloc T0 (Some n) L) H = SecLang.tloc T0 (Some n) H). reflexivity.
                  rewrite<-H3. clear H3. assert (SecLang.value (SecLang.tloc T0 (Some n) L)). apply SecLang.v_l. apply project_hp_Hextend with(hp:=hp0)(T:=T) in H3. rewrite<-H3. clear H3.  
  assert (same_mark (project_conf'_hp (project_hp hp0)(project_hp hp0))(project_hp hp0) = true). apply same_mark_sym. apply same_mark_heap. apply return_smallest_match_same_mark with (n:=length hp0)in H3. rewrite->H3.
                 rewrite->return_smallest_match_true. clear H3. assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=length hp0)in H3. rewrite<-H3.
                 rewrite->return_smallest_match_true. simpl. apply LowLang.Multi_step with (y:=((LowLang.tloc T None,
  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))))). apply LowLang.st_reftH. apply LowLang.v_H. left. reflexivity. apply LowLang.Multi_refl.
                 (*high pointer*)
                 unfold project. unfold project_conf. simpl.  rewrite->SecLang.joins_refl. simpl. apply project_hp_Hextend with(hp:=hp0)(T:=T) in H2. rewrite<-H2. apply LowLang.Multi_refl.
Case ("st_ref"). 
               destruct b. destruct PC. simpl in H2. unfold project. unfold project_conf. simpl. unfold project in IHstep. unfold project_conf in IHstep. simpl in IHstep. 
               assert (fst ( (project_conf'_e (project_e t)
              (project_conf'_hp (project_hp hp0) (project_hp hp0)),
              erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))) = (project_conf'_e (project_e t)(project_conf'_hp (project_hp hp0) (project_hp hp0)))). reflexivity. rewrite<-H3. clear H3.
               assert (snd ( (project_conf'_e (project_e t)
              (project_conf'_hp (project_hp hp0) (project_hp hp0)),
              erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))) =erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)) ). reflexivity. rewrite<-H3. clear H3.
               assert (fst ((project_conf'_e (project_e t')
              (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
               erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))) =(project_conf'_e (project_e t')(project_conf'_hp (project_hp hp'0) (project_hp hp'0))) ). reflexivity. rewrite<-H3. clear H3.
               assert (snd ((project_conf'_e (project_e t')
              (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
               erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))) = erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0)) ). reflexivity. rewrite<-H3. clear H3.
               apply multi_step_ref. apply IHstep. simpl in H2. 
               simpl in IHstep. unfold project. unfold project_conf. simpl. unfold project in IHstep. unfold project_conf in IHstep. simpl in IHstep.
               assert (fst ( (project_conf'_e (project_e t)
              (project_conf'_hp (project_hp hp0) (project_hp hp0)),
              erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))) = (project_conf'_e (project_e t)(project_conf'_hp (project_hp hp0) (project_hp hp0)))). reflexivity. rewrite<-H3. clear H3.
               assert (snd ( (project_conf'_e (project_e t)
              (project_conf'_hp (project_hp hp0) (project_hp hp0)),
              erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))) =erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)) ). reflexivity. rewrite<-H3. clear H3.
               assert (fst ((project_conf'_e (project_e t')
              (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
               erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))) =(project_conf'_e (project_e t')(project_conf'_hp (project_hp hp'0) (project_hp hp'0))) ). reflexivity. rewrite<-H3. clear H3.
               assert (snd ((project_conf'_e (project_e t')
              (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
               erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))) = erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0)) ). reflexivity. rewrite<-H3. clear H3.
               apply multi_step_ref. apply IHstep. rewrite->SecLang.joins_refl in H2. simpl in H2. unfold project. simpl. apply proj_hp_H_same in H2. rewrite->H2. apply LowLang.Multi_refl.

Case ("st_derefloc").
               destruct b. unfold project. unfold project_conf. simpl.
               assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap. apply return_smallest_match_same_mark' with (n:=n)in H3. rewrite<-H3. clear H3.
               assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap. apply project_conf'_e_same_mark with (t:=project_e t) in H3. rewrite<-H3. clear H3.
               remember (fst (return_smallest_match n (project_hp hp0))) as BB. destruct BB. rewrite->H2. apply return_smallest_match_project_e_true in H1. rewrite->H1. apply LowLang.Multi_step with (y:=(project_conf'_e LowLang.tH (project_hp hp0),
               erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))). apply LowLang.st_derefloctH. apply LowLang.Multi_refl. symmetry. apply HeqBB. unfold project_hp in HeqBB. 
               apply LowLang.Multi_step with (y:=(project_conf'_e (project_e t) (project_hp hp0),
               erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))). apply LowLang.st_derefloc. (*referring to [marked_heap_value_tws]*) 
               apply cs_derefloc_two in H2. assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0))=true). apply same_mark_heap.
               apply return_smallest_match_same_mark' with (n:=n) in H3. rewrite<-H3 in H2. clear H3. symmetry in H2. apply heap_lookup_n_length in H2.
               rewrite->erase_hp_length. apply H2. apply HeqBB.
               apply cs_derefloc in H2. apply H2. apply HeqBB. apply LowLang.Multi_refl. 
               unfold project. unfold project_conf. simpl. apply LowLang.Multi_step with (y:=(LowLang.tH, erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))). apply LowLang.st_dereftH. apply LowLang.Multi_refl. 

Case ("st_deref").
               destruct PC. unfold project. unfold project_conf. simpl. unfold project in IHstep. unfold project_conf in IHstep. simpl in IHstep. 
               assert (fst ( (project_conf'_e (project_e t)
              (project_conf'_hp (project_hp hp0) (project_hp hp0)),
              erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))) = (project_conf'_e (project_e t)(project_conf'_hp (project_hp hp0) (project_hp hp0)))). reflexivity. rewrite<-H3. clear H3.
               assert (snd ( (project_conf'_e (project_e t)
              (project_conf'_hp (project_hp hp0) (project_hp hp0)),
              erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))) =erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)) ). reflexivity. rewrite<-H3. clear H3.
               assert (fst ((project_conf'_e (project_e t')
              (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
               erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))) =(project_conf'_e (project_e t')(project_conf'_hp (project_hp hp'0) (project_hp hp'0))) ). reflexivity. rewrite<-H3. clear H3.
               assert (snd ((project_conf'_e (project_e t')
              (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
               erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))) = erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0)) ). reflexivity. rewrite<-H3. clear H3.
               apply multi_step_deref. apply IHstep. 
               unfold project. unfold project_conf. simpl. unfold project in IHstep. unfold project_conf in IHstep. simpl in IHstep.
               assert (fst ( (project_conf'_e (project_e t)
              (project_conf'_hp (project_hp hp0) (project_hp hp0)),
              erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))) = (project_conf'_e (project_e t)(project_conf'_hp (project_hp hp0) (project_hp hp0)))). reflexivity. rewrite<-H3. clear H3.
               assert (snd ( (project_conf'_e (project_e t)
              (project_conf'_hp (project_hp hp0) (project_hp hp0)),
              erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))) =erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)) ). reflexivity. rewrite<-H3. clear H3.
               assert (fst ((project_conf'_e (project_e t')
              (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
               erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))) =(project_conf'_e (project_e t')(project_conf'_hp (project_hp hp'0) (project_hp hp'0))) ). reflexivity. rewrite<-H3. clear H3.
               assert (snd ((project_conf'_e (project_e t')
              (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
               erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))) = erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0)) ). reflexivity. rewrite<-H3. clear H3.
               apply multi_step_deref. apply IHstep.                             
Case ("st_assign"). 
              unfold project. unfold project_conf. destruct PC. destruct b. destruct l. destruct b'. simpl. simpl in H6. rewrite->H6. simpl. simpl in H7. 
              (*low cell being over-written by a low value*)
              apply return_smallest_match_project_hp_hit in H2. assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0))=true). apply same_mark_heap.
              apply return_smallest_match_same_mark' with (n:=n) in H13. rewrite<-H13. clear H13. rewrite->H2. 
              apply LowLang.Multi_step with (y:=(LowLang.tunit,
              erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))). apply LowLang.st_assign. rewrite->erase_hp_length. assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0))=true).
              apply same_mark_heap. apply same_mark_length in H13. rewrite<-H13. clear H13. unfold project_hp. apply return_smallest_match_snd_length. apply H2.
              apply SecLang_value_LowLang. apply H3. intros contra. inversion H3.
              (*tcon*) subst. compute in H4. subst. simpl in contra. inversion contra.
              (*tabs*) subst. compute in H4. subst. simpl in contra. inversion contra.
              (*tunit*) subst. compute in H4. subst. simpl in contra. inversion contra.
              (*tloc*) subst. compute in H4. subst. simpl in contra. 
                       remember (fst(return_smallest_match n0(project_conf'_hp (project_hp hp0) (project_hp hp0)))) as C. destruct C.
                       inversion contra. inversion contra.
              split. reflexivity. symmetry. apply H5. subst. assert (SecLang.joinTs T L = T). 
              destruct T. simpl. reflexivity. rewrite->H6. clear H6.
              simpl. assert (SecLang.joinvs v L= v). inversion H3.
              (*tcon*) subst. rewrite->SecLang.join_tcon_b. rewrite->SecLang.joins_refl. simpl. reflexivity.
              (*tabs*) subst. rewrite->SecLang.join_tabs_b. rewrite->SecLang.joins_refl. simpl. reflexivity.
              (*tunit*) subst. rewrite->SecLang.join_tunit_b. rewrite->SecLang.joins_refl. simpl. reflexivity.
              (*tloc*) subst. rewrite->SecLang.join_tloc_b. rewrite->SecLang.joins_refl. simpl. reflexivity.
              rewrite->H6. clear H6.
              apply project_conf'_hp_heap_replace. apply H3. rewrite->H4 in H7. apply H7. apply H2.
              apply LowLang.Multi_refl. symmetry. apply H7. 
              (*high cell being over-written by a high value*)
              (*when PC is low*)
              (*subcase 1: v <> tH & SecLang.label T = H*)
              simpl. simpl in H6. rewrite->H6. simpl in H7. assert (n<length hp0). apply H2. apply return_smallest_match_project_hp_not_hit in H2.
              assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0))=true). apply same_mark_heap.
              apply return_smallest_match_same_mark' with (n:=n) in H14. rewrite<-H14. clear H14. rewrite->H2. simpl in H9. subst.
              apply project_hp_Hoverwrite with (t:=v)(T:=T)in H13.
              assert (SecLang.joinTs T L=T). destruct T. simpl. reflexivity. rewrite->H6. clear H6. rewrite<-H13. simpl. apply LowLang.Multi_step with (y:=(LowLang.tunit,
              erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))). apply LowLang.st_assigntH_L. apply SecLang_value_LowLang. apply H3.
              reflexivity. right. symmetry. apply H5. apply LowLang.Multi_refl. apply H3. rewrite<-H7. apply sub_refl. symmetry. apply H7.
              (*subcase 2: v= tH*)
              simpl. simpl in H6. rewrite->H6. simpl in H7. assert (n<length hp0). apply H2. apply return_smallest_match_project_hp_not_hit in H2.
              assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0))=true). apply same_mark_heap.
              apply return_smallest_match_same_mark' with (n:=n) in H14. rewrite<-H14. clear H14. rewrite->H2. 
              apply project_hp_Hoverwrite with (t:=v)(T:=T)in H13. subst.
              assert (SecLang.joinvs v (SecLang.joins (SecLang.labelT T) L)= SecLang.joinvs v H). inversion H3.
              (*tcon*) subst. compute in H4. subst. rewrite->SecLang.join_tcon_H. symmetry. apply SecLang.join_tcon_H.
              (*tabs*) subst. compute in H4. subst. rewrite->SecLang.join_tabs_H. symmetry. apply SecLang.join_tabs_H.
              (*tunit*) subst. compute in H4. subst. rewrite->SecLang.join_tunit_H. symmetry. apply SecLang.join_tunit_H.
              (*tloc*) subst. compute in H4. subst. rewrite->SecLang.join_tloc_H. symmetry. apply SecLang.join_tloc_H.
              rewrite->H5. clear H5.
              assert (SecLang.joinTs T L=T). destruct T. simpl. reflexivity. rewrite->H5. clear H5. rewrite<-H13. simpl. apply LowLang.Multi_step with (y:=(LowLang.tunit,
              erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))). apply LowLang.st_assigntH_L. apply SecLang_value_LowLang. apply H3.
              reflexivity. left. inversion H3. subst. compute in H4. subst. simpl. reflexivity. subst. compute in H4. subst. simpl. reflexivity. subst. compute in H4. subst. simpl. reflexivity.
              subst. compute in H4. subst. simpl. reflexivity.
              apply LowLang.Multi_refl. apply H3. rewrite<-H7. apply sub_refl. symmetry. apply H7.
              (*high pointer*)
              simpl. simpl in H6. rewrite->H6. simpl. subst. apply project_hp_Hoverwrite with (t:=v)(T:=SecLang.joinTs T H)in H2. rewrite->SecLang.joins_refl. simpl. rewrite<-H2.
              apply LowLang.Multi_step with (y:=(LowLang.tH, erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))).
              apply LowLang.st_assignHP. apply SecLang_value_LowLang. apply H3. apply LowLang.Multi_refl. apply H3. apply H8.
              (*finishing up by casing [b],the label of the pointer*)
              destruct b.
              (*high cell being over-written by a high value*)
              (*when PC is high*)
              simpl. simpl in H6. rewrite->H6. assert (n<length hp0). apply H2. apply return_smallest_match_project_hp_not_hit in H2.
              assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0))=true). apply same_mark_heap.
              apply return_smallest_match_same_mark' with (n:=n) in H14. rewrite<-H14. clear H14. rewrite->H2. subst.
              apply project_hp_Hoverwrite with (t:=v)(T:=SecLang.joinTs T H)in H13.
              rewrite->SecLang.joins_refl. simpl.
              rewrite<-H13. apply LowLang.Multi_step with (y:=(LowLang.tH,
              erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))). apply LowLang.st_assigntH_H. apply SecLang_value_LowLang. apply H3.
              reflexivity.  apply LowLang.Multi_refl. apply H3. apply H8. rewrite->H6 in H8. remember (SecLang.label (SecLang.efst (SecLang.heap_lookup n hp0))) as C. 
              destruct C. inversion H8. reflexivity.
              (*high pointer*)
              simpl. simpl in H6. rewrite->H6. simpl. subst. apply project_hp_Hoverwrite with (t:=v)(T:=SecLang.joinTs T H)in H2. rewrite->SecLang.joins_refl. simpl. rewrite<-H2.
              apply LowLang.Multi_step with (y:=(LowLang.tH, erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0)))).
              apply LowLang.st_assignHP. apply SecLang_value_LowLang. apply H3. apply LowLang.Multi_refl. apply H3. apply H8.                     
Case ("st_assign1"). 
              unfold project. unfold project_conf. unfold project in IHstep. unfold project_conf in IHstep. simpl. simpl in IHstep.
                 destruct PC. 
                 SCase ("PC:=L").  apply step_same_mark_or_extend in H3. inversion H3.
                                  (*case one: two heaps of the same length with identical marks*)
                                   assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap.
                                   assert (same_mark (project_conf'_hp (project_hp hp0) (project_hp hp0))(project_hp hp'0) = true). apply same_mark_replace with (hp1:=project_hp hp0).
                                   apply H4. apply H5. apply same_mark_sym in H6. assert (same_mark (project_hp hp'0)(project_conf'_hp (project_hp hp'0) (project_hp hp'0)) = true). 
                                   apply same_mark_heap. assert (same_mark (project_conf'_hp (project_hp hp0) (project_hp hp0))(project_conf'_hp (project_hp hp'0) (project_hp hp'0)) = true).
                                   apply same_mark_replace with (hp1:=project_hp hp'0). apply H7. apply H6. apply project_conf'_e_same_mark with (t:=project_e t2)in H8. rewrite->H8. clear H4.
                                   clear H5. clear H6. clear H7. clear H8. 
                                   assert (fst (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)))). reflexivity. rewrite<-H4. clear H4.
                                  assert (snd (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))).
                                  reflexivity. rewrite<-H4. clear H4. 
                                  assert (fst (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) = (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))). reflexivity. rewrite<-H4. clear H4.
                                  assert (snd (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) =  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))).
                                  reflexivity. rewrite<-H4. clear H4. apply multi_step_assign1. apply IHstep.
                                  (*case two: after reduction heap is expanded by one low value*)
                                  inversion H4. assert (project_conf'_e (project_e t2)
                                  (project_conf'_hp (project_hp hp'0) (project_hp hp'0)) = project_conf'_e (project_e t2)
                                  (project_conf'_hp ((LowLang.snoc (project_hp hp0) (x, (length hp0, length (project_hp hp0))))) ((LowLang.snoc (project_hp hp0) (x, (length hp0, length (project_hp hp0))))))).
                                  rewrite<-H5. reflexivity. rewrite->H6. assert ((project_conf'_e (project_e t2)
                                  (project_conf'_hp (project_hp hp0) (project_hp hp0))) = (project_conf'_e (project_e t2)
                                  (project_conf'_hp
                                  (LowLang.snoc (project_hp hp0)
                                  (x, (length hp0, length (project_hp hp0))))
                                  (LowLang.snoc (project_hp hp0)
                                  (x, (length hp0, length (project_hp hp0))))))). apply project_conf'_e_add_one_low. apply H2. rewrite<-H7. clear H5. clear H6. clear H7. 
                                   assert (fst (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)))). reflexivity. rewrite<-H5. clear H5.
                                  assert (snd (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))).
                                  reflexivity. rewrite<-H5. clear H5. 
                                  assert (fst (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) = (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))). reflexivity. rewrite<-H5. clear H5.
                                  assert (snd (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) =  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))).
                                  reflexivity. rewrite<-H5. clear H5. apply multi_step_assign1. apply IHstep.                                 
                 SCase ("PC:=H"). apply proj_hp_H_same in H3. assert (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)) = project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0))). rewrite->H3. reflexivity. rewrite->H4. clear H4.
                                  assert (fst (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)))). reflexivity. rewrite<-H4. clear H4.
                                  assert (snd (project_conf'_e (project_e t1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))).
                                  reflexivity. rewrite<-H4. clear H4. 
                                  assert (fst (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) = (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))). reflexivity. rewrite<-H4. clear H4.
                                  assert (snd (project_conf'_e (project_e t1')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) =  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))).
                                  reflexivity. rewrite<-H4. clear H4. apply multi_step_assign1. apply IHstep.

Case ("st_assign2").
                            unfold project. unfold project_conf. unfold project in IHstep. unfold project_conf in IHstep. simpl. simpl in IHstep.
                            destruct PC. 
                 SCase ("PC:=L").  apply step_same_mark_or_extend in H4. inversion H4.
                                  (*case one: two heaps of the same length with identical marks*)
                                   assert (same_mark (project_hp hp0)(project_conf'_hp (project_hp hp0)(project_hp hp0)) = true). apply same_mark_heap.
                                   assert (same_mark (project_conf'_hp (project_hp hp0) (project_hp hp0))(project_hp hp'0) = true). apply same_mark_replace with (hp1:=project_hp hp0).
                                   apply H5. apply H6. apply same_mark_sym in H7. assert (same_mark (project_hp hp'0)(project_conf'_hp (project_hp hp'0) (project_hp hp'0)) = true). 
                                   apply same_mark_heap. assert (same_mark (project_conf'_hp (project_hp hp0) (project_hp hp0))(project_conf'_hp (project_hp hp'0) (project_hp hp'0)) = true).
                                   apply same_mark_replace with (hp1:=project_hp hp'0). apply H8. apply H7. apply project_conf'_e_same_mark with (t:=project_e v1)in H9. rewrite->H9. clear H5.
                                   clear H6. clear H7. clear H8. clear H9. 
                                   assert (fst (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)))). reflexivity. rewrite<-H5. clear H5.
                                  assert (snd (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))).
                                  reflexivity. rewrite<-H5. clear H5. 
                                  assert (fst (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) = (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))). reflexivity. rewrite<-H5. clear H5.
                                  assert (snd (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) =  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))).
                                  reflexivity. rewrite<-H5. clear H5. apply multi_step_assign2. apply SecLang_value_LowLang. apply H3.
                                 apply IHstep.
                                  (*case two: after reduction heap is expanded by one low value*)
                                  inversion H5. assert (project_conf'_e (project_e v1)
                                  (project_conf'_hp (project_hp hp'0) (project_hp hp'0)) = project_conf'_e (project_e v1)
                                  (project_conf'_hp ((LowLang.snoc (project_hp hp0) (x, (length hp0, length (project_hp hp0))))) ((LowLang.snoc (project_hp hp0) (x, (length hp0, length (project_hp hp0))))))).
                                  rewrite<-H6. reflexivity. rewrite->H7. assert ((project_conf'_e (project_e v1)
                                  (project_conf'_hp (project_hp hp0) (project_hp hp0))) = (project_conf'_e (project_e v1)
                                  (project_conf'_hp
                                  (LowLang.snoc (project_hp hp0)
                                  (x, (length hp0, length (project_hp hp0))))
                                  (LowLang.snoc (project_hp hp0)
                                  (x, (length hp0, length (project_hp hp0))))))). apply project_conf'_e_add_one_low. apply H1. rewrite<-H8. clear H6. clear H7. clear H8. 
                                   assert (fst (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)))). reflexivity. rewrite<-H6. clear H6.
                                  assert (snd (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))).
                                  reflexivity. rewrite<-H6. clear H6. 
                                  assert (fst (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) = (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))). reflexivity. rewrite<-H6. clear H6.
                                  assert (snd (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) =  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))).
                                  reflexivity. rewrite<-H6. clear H6. apply multi_step_assign2. apply SecLang_value_LowLang. apply H3.
                                  apply IHstep.                                 
                 SCase ("PC:=H"). apply proj_hp_H_same in H4. assert (project_conf'_e (project_e v1)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)) = project_conf'_e (project_e v1)
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0))). rewrite->H4. reflexivity. rewrite->H5. clear H5.
                                  assert (fst (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)))). reflexivity. rewrite<-H5. clear H5.
                                  assert (snd (project_conf'_e (project_e t2)
                                 (project_conf'_hp (project_hp hp0) (project_hp hp0)),
                                  erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))) = erase_hp (project_conf'_hp (project_hp hp0) (project_hp hp0))).
                                  reflexivity. rewrite<-H5. clear H5. 
                                  assert (fst (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) = (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)))). reflexivity. rewrite<-H5. clear H5.
                                  assert (snd (project_conf'_e (project_e t2')
                                 (project_conf'_hp (project_hp hp'0) (project_hp hp'0)),
                                  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))) =  erase_hp (project_conf'_hp (project_hp hp'0) (project_hp hp'0))).
                                  reflexivity. rewrite<-H5. clear H5. apply multi_step_assign2. apply SecLang_value_LowLang. apply H3. apply IHstep.
Qed.

(*Theorem 5 in Lu's paper*)
Lemma corresp_eval:forall e e' hp hp',
SecLang.Multi SecLang.step (e,hp) L (e',hp') ->
LowLang.Multi LowLang.step (project (e,hp)) L (project (e',hp')).
Proof. intros. remember L as B. induction H0. apply LowLang.Multi_refl. destruct x. destruct y. subst.
       apply corresp_step in H0. unfold project in H0. unfold project_conf in H0. 
       apply LowLang.multi_trans with 
       (t':=project_conf'_e (project_e (fst (t0, h0)))(project_conf'_hp (project_hp (snd (t0, h0)))(project_hp (snd (t0, h0)))))
       (hp':=erase_hp(project_conf'_hp (project_hp (snd (t0, h0)))(project_hp (snd (t0, h0))))). 
       apply H0. apply IHMulti. reflexivity.
Qed.

(*NI of static typing with reference*)
Theorem NI:forall x v1 v2 w1 w2 e HT pc rt hp hp' hp'',
SecLang.value v1 ->
SecLang.value v2 ->                                                 (*1*)
SecLang.has_type pc empty_context HT v1 (an rt H) ->                (*3*)
SecLang.has_type pc empty_context HT v2 (an rt H) ->                (*4*)
SecLang.label v1 = H ->
SecLang.label v2 = H ->                                             (*5*)
SecLang.has_type pc (Cupdate empty_context x (Some (an rt H))) HT
e (an int L) ->                                                     (*6*)
SecLang.heap_well_typed HT hp ->                                    (*7*)                                                 (*8*)
SecLang.value w1 ->
SecLang.value w2 ->                                                 (*2*)
SecLang.Multi SecLang.step (SecLang.subst x v1 e,hp) L (w1,hp') -> (*8*)
SecLang.Multi SecLang.step (SecLang.subst x v2 e,hp) L (w2,hp'')-> (*9*)
w1 = w2.
Proof. intros.
(*step one*)
(**
(3),(4),(6),and [substitution_preserves_typing] in [SecLang] imply that
both [SecLang.subst x v1 e] and [SecLang.subst x v2 e] are of type [an int L]
*)
assert (SecLang.has_type pc empty_context HT (SecLang.subst x v1 e) (an int L)).
apply SecLang.substitution_preserves_typing with(pc:=pc)(Gamma:=empty_context)(HT:=HT)(x:=x)(T1:=an rt H)(T2:=an int L)(e:=e) in H0.
apply H0. apply H2. apply H6.
assert (SecLang.has_type pc empty_context HT (SecLang.subst x v2 e) (an int L)).
apply SecLang.substitution_preserves_typing with(pc:=pc)(Gamma:=empty_context)(HT:=HT)(x:=x)(T1:=an rt H)(T2:=an int L)(e:=e) in H1.
apply H1. apply H3. apply H6.
(*step two*)
(**
From [H13] and [H14],obtained from step one,together with [type_uniqueness] in [SecLang]
we conclude that [w1] and [w2] are of type [an int L]
*)
assert (fst (SecLang.subst x v1 e,hp)=SecLang.subst x v1 e). reflexivity.
rewrite<-H14 in H12. clear H14.
apply SecLang.type_uniqueness with(z:=(w1,hp'))(PC:=L)in H12. simpl in H12.
assert (fst (SecLang.subst x v2 e,hp)=SecLang.subst x v2 e). reflexivity.
rewrite<-H14 in H13. clear H14.
apply SecLang.type_uniqueness with(z:=(w2,hp''))(PC:=L)in H13. simpl in H13.
(*step three*)
(**
From the conclusion of [step two] that [w1] and [w2] are of type [an int L] and 
(2) we know that [w1=tcon n1 L] and [w2=tcon n2 L]
*) 
assert (SecLang.value w1). apply H8. assert (SecLang.value w2). apply H9.
inversion H14. inversion H15. subst.
inversion H12. inversion H16. inversion H18. apply SecLang.inversion_tcon in H20.
inversion H20. inversion H21. inversion H22. inversion H23. inversion H25. subst.
inversion H27. inversion H26. inversion H30. subst. inversion H24. subst.
inversion H13. inversion H28. inversion H31. apply SecLang.inversion_tcon in H33.
inversion H33. inversion H34. inversion H35. inversion H36. inversion H38. subst.
inversion H40. inversion H39. inversion H43. subst. inversion H37. subst.
(*step four*) 
(**
From [corresp_eval],(1),(3),(4),[project_conf'_subst],and [determinism_extended]
we conclude that [n1 = n2]. Qed.
*)
apply corresp_eval in H10. apply corresp_eval in H11. 
unfold project in H10. simpl in H10. unfold project_conf in H10.
assert (SecLang.value v1). apply H0. apply project_e_subst with (x:=x)(e:=e)in H41.
rewrite->H41 in H10. clear H41. rewrite->project_conf'_subst in H10. simpl in H10.
unfold project in H11. simpl in H11. unfold project_conf in H11.
assert (SecLang.value v2). apply H1. apply project_e_subst with (x:=x)(e:=e)in H41.
rewrite->H41 in H11. clear H41. rewrite->project_conf'_subst in H11. simpl in H11.
assert (project_e v1 = LowLang.tH). inversion H0. subst. compute in H4. subst. reflexivity.
subst. compute in H4. subst. reflexivity. subst. compute in H4. subst. reflexivity. 
subst. compute in H4. subst. reflexivity. rewrite->H41 in H10. clear H41. simpl in H10.
assert (project_e v2 = LowLang.tH). inversion H1. subst. compute in H5. subst. reflexivity.
subst. compute in H5. subst. reflexivity. subst. compute in H5. subst. reflexivity. 
subst. compute in H5. subst. reflexivity. rewrite->H41 in H11. clear H41. simpl in H11.
assert (LowLang.value (fst(LowLang.tcon n,erase_hp (project_conf'_hp (project_hp hp') (project_hp hp'))))).
simpl. apply LowLang.v_c.
assert (LowLang.value (fst(LowLang.tcon n0,erase_hp (project_conf'_hp (project_hp hp'') (project_hp hp''))))).
simpl. apply LowLang.v_c.
apply LowLang.determinism_extended with (x:=(LowLang.subst x LowLang.tH
     (project_conf'_e (project_e e)(project_conf'_hp (project_hp hp) (project_hp hp))),
      erase_hp (project_conf'_hp (project_hp hp) (project_hp hp))))
     (y:=(LowLang.tcon n,
     erase_hp (project_conf'_hp (project_hp hp') (project_hp hp'))))
     (z:=(LowLang.tcon n0,
     erase_hp (project_conf'_hp (project_hp hp'') (project_hp hp''))))
     (PC:=L)in H41. simpl in H41. inversion H41. reflexivity.
simpl. apply LowLang.v_c. apply H10. apply H11. 
(*contradictions*)
subst. inversion H13. inversion H16. inversion H18. apply SecLang.inversion_tabs in H20.
inversion H20. inversion H21. inversion H22. inversion H23. inversion H24. inversion H25.
inversion H26. inversion H27. inversion H29. inversion H31. inversion H33. inversion H35.
inversion H37. inversion H39. inversion H41. 
subst. inversion H13. inversion H16. inversion H18. apply SecLang.inversion_tunit in H20.
inversion H20. inversion H21. inversion H22. inversion H23. inversion H25. inversion H27.
subst. inversion H29.
subst. inversion H13. inversion H16. inversion H18. apply SecLang.inversion_tloc in H20.
inversion H20. inversion H21. inversion H22. inversion H23. inversion H24. inversion H26.
inversion H28. inversion H30. inversion H32. subst. inversion H34.
subst. inversion H12. inversion H16. inversion H18. apply SecLang.inversion_tabs in H20.
inversion H20. inversion H21. inversion H22. inversion H23. inversion H24. inversion H25.
inversion H26. inversion H27. inversion H29. inversion H31. inversion H33. inversion H35.
inversion H37. inversion H39. inversion H41. 
subst. inversion H12. inversion H16. inversion H18. apply SecLang.inversion_tunit in H20.
inversion H20. inversion H21. inversion H22. inversion H23. inversion H25. inversion H27.
subst. inversion H29.
subst. inversion H12. inversion H16. inversion H18. apply SecLang.inversion_tloc in H20.
inversion H20. inversion H21. inversion H22. inversion H23. inversion H24. inversion H26.
inversion H28. inversion H30. inversion H32. subst. inversion H34.
(*tidy-up*)
simpl. apply H7. destruct pc. apply sub_refl. apply sub_LH. apply H11. 
simpl. apply H7. destruct pc. apply sub_refl. apply sub_LH. apply H10.
Qed.
End Correspondence.
















