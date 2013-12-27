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

Lemma has_type_joinvs_b_al:forall pc HT t T b Gamma,
value t ->
has_type pc Gamma HT t T ->
has_type pc Gamma HT (joinvs t b) (joinTs T b).
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

(*type preservation:alternative*)
Theorem preservation_al:forall pc PC HT t t' T hp hp' Gamma,
has_type pc Gamma HT t T ->
heap_well_typed HT hp ->
t / hp ==PC=> t' / hp' ->
subsum_r PC pc ->
exists HT',
(extends HT' HT /\
has_type pc Gamma HT' t' T /\
heap_well_typed HT' hp').
Proof.
intros. generalize dependent hp.
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
     apply joins_subtyping_1. apply H3. apply H2. 
     subst. exists HT. split. apply extends_refl. split. apply value_pc with (pc:=joins pc b).
     apply value_b. apply H13. apply has_type_joinvs_b_al. apply H13. apply H0. apply H2.
Case ("t_app").
     intros. inversion H2. subst. exists HT. split. apply extends_refl. split. apply inversion_tabs in H0_. inversion H0_. inversion H0. inversion H4. inversion H5. inversion H6. inversion H7. inversion H8.
     inversion H9. inversion H15. inversion H17. inversion H19. inversion H21. inversion H23. inversion H25.
     apply t_sub with (pc:=pc)(T:=joinTs T2 x6). apply t_sub with (pc:=pc)(T:=joinTs T2 b0). apply t_prot with (T:=T2).
     apply t_sub with (pc:=x5)(T:=T2). apply t_sub with (pc:=x4)(T:=T2). apply t_sub with (pc:=x4)(T:=x2). apply t_sub with (pc:=x4)(T:=x1). apply value_pc with (pc':=x4) in H0_0.
     apply t_sub with (pc':=x4)(T':=x0)in H0_0. apply t_sub with (pc':=x4)(T':=T) in H0_0. apply substitution_preserves_typing with (T1:=T). apply H13.
     (*we are stuck here*)
     (**
     Note that [has_type x4 Gamma HT t2 T] can never imply [has_type x4 empty_context HT t2 T].
     This is the reason why in [preservation] we do not consider cases where the term
     before reduction contains any free variables
     *)
     admit.
Admitted.


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


End LowLang.













