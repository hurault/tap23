Require Import Extraction.
Require Import Arith Lia Init.Datatypes Omega.
Require Import Coq.Program.Wf.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical.

Section Classifier.
Open Scope list_scope.


Lemma contrapose : forall p q:Prop, (p->q)->(~q->~p).
Proof. intros. intro. apply H0. apply H. exact H1. Qed.

(* About list *)
Fixpoint mem {a:Type} (i:a) (p: list a) : Prop :=
  match p with
  | nil => False
  | x :: q => (i=x) \/ mem i q 
  end.


Fixpoint mem_nat (i:nat) (p: list nat) : bool :=
  match p with
  | nil => false
  | x :: q => if (eq_nat_dec i x) then true else (mem_nat i q) 
  end.
 

Lemma mem_coherent : forall (i:nat) (p: list nat), mem_nat i p = true <-> mem i p.
Proof.
   induction p.
   simpl.
   lia.
   split.
   simpl.
   destruct (Nat.eq_dec i a).
   auto.
   rewrite IHp.
   auto.
   simpl.
   destruct (Nat.eq_dec i a).
   auto.
   rewrite IHp.
   intro.
   destruct H.
   tauto.
   apply H.
Qed.


Lemma mem_not_mem : forall (i:nat) (p: list nat), mem i p \/ ~ mem i p.
Proof.
   intros.
   induction p.
   simpl.
   auto.
   cut (i=a \/ i<>a).
   intro di.
   destruct di.
   left.
   simpl.
   auto.
   destruct IHp.
   left.
   simpl.
   auto.
   right.
   auto.
   simpl.
   tauto.
   lia.
Qed.

Lemma list_mem_not_nil {a:Type}: 
forall (x :a) (l:list a), mem x l -> l <> nil.
Proof.
intro.
destruct l.
simpl.
tauto.
intro.
discriminate.
Qed.

Lemma list_mem_middle  {a:Type}:  forall (x :a) (x0 x1:list a),
mem x (x0 ++ x :: x1).
Proof.
intros.
induction x0.
simpl.
auto.
simpl.
auto.
Qed.

(* x0++(Cons x x1) = (Cons i Nil) -> x0=Nil /\ x=i /\ x1=Nil *)
Lemma destruct_list_1elt  {a:Type} :
  forall (x i:a) (x0 x1:list a),
  ((app x0 (cons x x1)) = (cons i nil)) ->
  (x0 = nil) /\ (x = i) /\ (x1 = nil).
Proof.
intros.
destruct x0.
(* x0 = nil -> OK*)
simpl in H.
injection H.
auto.
(* x0 <> nil *)
(* x1 <> nil *)
cut False.
tauto.
simpl in H.
cut (x0 ++ x :: x1 = nil).
cut (x0 ++ x :: x1 <> nil).
tauto.
(* x0 ++ x :: x1 <> nil *)
cut (mem x (x0 ++ x :: x1)).
apply list_mem_not_nil.
apply list_mem_middle.
(* x0 ++ x :: x1 = nil *)
injection H.
auto.
Qed.

(* Nil++(Cons x x1) = (Cons i p) -> x=i /\ x1=p *)
Lemma destruct_list_debutvide {a:Type}:
  forall (x i :a) (p x1 : list a),
  ((app nil (cons x x1)) = (cons i p)) -> (x = i) /\ (x1 = p).
Proof.
intros.
generalize H.
simpl.
intro I.
injection I.
auto.
Qed.

(* Number of feature *)
Parameter nb_feature : nat.
Axiom nb_feature_not_nul : nb_feature > 0.

(* All feature have the same type : T*)
Parameter T : Type.
(* inferior or egals *)
Parameter led : T -> T -> Prop.
Axiom led_eq : forall (d1:T) (d2:T), d1=d2 -> led d1 d2.
Axiom led_borne : forall (d1:T) (d2:T) (d3:T), led d1 d2 /\ led d2 d3 /\ d1=d3 -> d1=d2 /\ d2=d3.
Axiom led_transitivity : forall (d1:T) (d2:T) (d3:T), led d1 d2 /\ led d2 d3 -> led d1 d3.
(* Type of the classes of the classifier *)
Parameter Tk : Type.
Parameter Tk_eq_dec : Tk -> Tk -> bool.
Axiom Tk_eq_coherent_eq : forall (d1:Tk) (d2:Tk), d1=d2 -> (Tk_eq_dec d1 d2)=true.
Axiom Tk_eq_coherent_neq : forall (d1:Tk) (d2:Tk), d1<>d2 -> (Tk_eq_dec d1 d2)=false.
Axiom Tk_tier_exclu : forall (d1:Tk) (d2:Tk), d1<>d2 \/ d1=d2.

Parameter Exception : T.

Definition get  (i:nat) (v : list T) : T :=
 List.nth i v  Exception.

Lemma id_list_aux : forall (l1 l2 : list T),
 (List.length l1=List.length l2 /\ (forall (i:nat), i>=0 /\ i<List.length l1 -> get i l1=get i l2))
 -> l1=l2.
Proof.
   induction l1.
   (* cas de base *)
   intros.
   destruct H.
   destruct l2.
   auto.
   generalize H.
   simpl.
   discriminate.
   (* cas général *)
   intros.
   destruct H.
   destruct l2.
   generalize H.
   simpl.
   discriminate.
   cut (a=t).
   intro eq_t.
   rewrite eq_t.
   cut (l1=l2).
   intro eq_q.
   rewrite eq_q.
   reflexivity.
   apply IHl1.
   split.
   generalize H.
   simpl.
   auto.
   intros.
   generalize (H0 (S i)).
   simpl.
   unfold get.
   simpl.
   intro H0bis.
   apply H0bis.
   lia.
   generalize (H0 0).
   unfold get.
   simpl.
   intro H0bis.
   apply H0bis.
   lia.
Qed.

Lemma id_list : forall (l1 l2 : list T), l1=l2 
  <-> (List.length l1=List.length l2 /\ (forall (i:nat), i>=0 /\ i<List.length l1 -> get i l1=get i l2)).
  Proof.
     intros.
     split.
     (* -> *)
     intro.
     rewrite H.
     auto.
     (* <- *)
     apply id_list_aux.
  Qed.


Definition le_n (v1 : list T) (v2 : list T) : Prop :=
   List.length v1 = nb_feature 
/\ List.length v2 = nb_feature
/\ (forall (i:nat), 0<= i /\ i< nb_feature -> led (get i v1) (get i v2)).

(*** bounds on the features ***)
Parameter nu : nat -> T.
Axiom nu_n : forall (j:nat), j >= nb_feature -> nu j = Exception.
Parameter lambda : nat -> T.
Axiom lambda_n : forall (j:nat), j >= nb_feature -> lambda j = Exception.

(*** The classifier ***)
(*
Parameter k : list T -> Tk.
*)

(*
Need a led on Tk - not needed for stablity
Definition monotonic (k:list T -> Tk): Prop := forall (f1:list T) (f2:list T), 
   List.length f1 = nb_feature 
/\ List.length f2 = nb_feature
/\ (forall (i:nat), 0<= i /\ i< nb_feature -> led (lambda i) (get i f1) /\ led (get i f1) (nu i) )
/\ (forall (i:nat), 0<= i /\ i< nb_feature -> led (lambda i) (get i f2) /\ led (get i f2) (nu i) )
/\ le_n f1 f2 -> led (k f1) (k f2).
*)

Definition stable (k:list T -> Tk): Prop := forall (f1:list T) (f2:list T) (x:list T), 
   List.length f1 = nb_feature 
/\ List.length f2 = nb_feature
/\ List.length x = nb_feature
/\ (forall (i:nat), 0<= i /\ i< nb_feature -> led (lambda i) (get i f1) /\ led (get i f1) (nu i) )
/\ (forall (i:nat), 0<= i /\ i< nb_feature -> led (lambda i) (get i f2) /\ led (get i f2) (nu i) )
/\ (forall (i:nat), 0<= i /\ i< nb_feature -> led (lambda i) (get i x) /\ led (get i x) (nu i) )
/\ le_n f1 x /\ le_n x f2 /\ (k f1)=(k f2)-> (k f1)=(k x).

(*
Lemma monotonic_implies_stable : forall (k:list T -> Tk), monotonic k -> stable k.
Proof.
   unfold stable.
   unfold monotonic.
   intros.
   destruct H0 as (S1,S). 
   destruct S as (S2,S).
   destruct S as (S3,S).
   destruct S as (S4,S).
   destruct S as (S5,S).
   destruct S as (S6,S).
   destruct S as (S7,S).
   destruct S as (S8,S9).

   cut (led (k0 f1) (k0 x)).
   cut (led (k0 x) (k0 f2)).
   intros M1 M2.
   apply (led_borne (k0 f1) (k0 x) (k0 f2)).
   repeat split; [apply M2|apply M1|apply S9].
   
   apply (H x f2).
   auto.

   apply (H f1 x).
   auto.

Qed.
*)

(* Need for CXp but not for AXp *)
Definition not_trivial (k:list T -> Tk): Prop := exists (f1:list T) (f2:list T), 
List.length f1 = nb_feature 
/\ List.length f2 = nb_feature
/\ (forall (i:nat), 0<= i /\ i< nb_feature -> led (lambda i) (get i f1) /\ led (get i f1) (nu i) )
/\ (forall (i:nat), 0<= i /\ i< nb_feature -> led (lambda i) (get i f2) /\ led (get i f2) (nu i) )
/\ (k f1)<>(k f2).


(* AXp *)
Fixpoint freeAttr_aux (i:nat) (n:nat) (vl:list T) (vu:list T) := 
   match i,vl,vu with
   | 0,_::ql,_::qu => ((lambda n)::ql,(nu n)::qu)
   | _,tl::ql,tu::qu => let (rl,ru) := freeAttr_aux (i-1) n ql qu in (tl::rl,tu::ru)
   |_,_,_ => (vl,vu)
   end.

Definition freeAttr (i:nat) (vl:list T) (vu:list T) := freeAttr_aux i i vl vu.


Lemma free_aux_size : forall (s:nat) (i:nat) (n:nat) (vl vu :list T),
   List.length vl = s
/\ List.length vu = s
->  List.length (fst (freeAttr_aux i n vl vu)) = s
/\ List.length  (snd (freeAttr_aux i n vl vu)) = s.
Proof.
induction s.
(* cas de base *)
intros.
destruct H.
destruct i.
(* i = 0 *)
destruct vl.
(* vl = nil*)
destruct vu.
(* vu = nil *)
simpl.
lia.
(* vu <> nil -> pas possible *)
cut False.
tauto.
generalize H0.
simpl.
discriminate.
(* vl <> nil -> pas possible *)
cut False.
tauto.
generalize H0.
simpl.
discriminate.
(* i <> 0 *)
destruct vl.
(* vl = nil*)
destruct vu.
(* vu = nil *)
simpl.
lia.
(* vu <> nil -> pas possible *)
cut False.
tauto.
generalize H0.
simpl.
discriminate.
(* vl <> nil -> pas possible *)
cut False.
tauto.
generalize H0.
simpl.
discriminate.

(* cas général *)
intros.
destruct i.
(* i = 0 *)
destruct vl.
(* vl = nil -> pas possible *)
cut False.
tauto.
destruct H.
generalize H.
simpl.
discriminate.
(* vl <> nil *)
destruct vu.
(* vu = nil -> pas possible *)
cut False.
tauto.
destruct H.
generalize H0.
simpl.
discriminate.
(* vu <> nil*)
generalize H.
simpl.
tauto.
(* i <> 0 *)
destruct vl.
(* vl = nil -> pas possible *)
cut False.
tauto.
destruct H.
generalize H.
simpl.
discriminate.
(* vl <> nil *)
destruct vu.
(* vu = nil -> pas possible *)
cut False.
tauto.
destruct H.
generalize H0.
simpl.
discriminate.
(* vu <> nil*)
simpl.
rewrite (surjective_pairing (freeAttr_aux (i - 0) n vl vu)).
simpl.
cut (i-0 = i).
intro ri.
rewrite ri.
generalize (IHs i n vl vu).
intros.
cut (length (fst (freeAttr_aux i n vl vu)) = s /\
length (snd (freeAttr_aux i n vl vu)) = s).
intro Hy.
destruct Hy.
rewrite H1.
rewrite H2.
tauto.
apply H0.
generalize H.
simpl.
lia.
lia.
Qed.

Lemma free_size : forall (s:nat) (i:nat) (vl vu :list T),
   List.length vl = s
/\ List.length vu = s
->  List.length (fst (freeAttr i vl vu)) = s
/\ List.length  (snd (freeAttr i vl vu)) = s.
Proof.
intros.
unfold freeAttr.
apply free_aux_size.
apply H.
Qed.



Lemma free_aux_get : forall (s i j n:nat) (vl vu nvl nvu:list T),
j>=0 /\ i>=0 /\ j< s /\ i< s /\ j<>i 
/\ freeAttr_aux i n vl vu = (nvl,nvu) 
/\ List.length vl = s
/\ List.length vu = s
-> get j vl = get j nvl /\ get j vu = get j nvu.
Proof.
induction s.
(* s = 0 -> impossible *)
intros.
cut False.
tauto.
lia.
(* cas général - s<>0 *)
intros.
destruct H as (H0,H1).
destruct H1 as (H1,H2).
destruct H2 as (H2,H3).
destruct H3 as (H3,H4).
destruct H4 as (H4,H5).
destruct H5 as (H5,H6).
destruct H6 as (H6,H7).
destruct vl.
(* vl = nil -> pas possible *)
cut False.
tauto.
generalize H6.
simpl.
discriminate.
(* vl <> nil *)
destruct vu.
(* vu = nil -> pas possible *)
cut False.
tauto.
generalize H7.
simpl.
discriminate.
(* vl <> nil et vu <> nil donc idem nvl et nvu -> th précédent *)
cut (List.length (t :: vl) = List.length nvl).
cut (List.length (t0 :: vu) = List.length nvu).
intros svu svl.
destruct nvl.
(* nvl vide -> pas possible *)
cut False.
tauto.
generalize svl.
discriminate.
(* nvl <> nil *)
destruct nvu.
(* nvl vide -> pas possible *)
cut False.
tauto.
generalize svu.
discriminate.
(* nvu <> nil *)
destruct i.
(* i=0 *)
destruct j.
(* j=0 -> pas possible *)
tauto.
(* j<>0 *)
cut (vl=nvl).
intro rvl.
cut (vu = nvu).
intro rvu.
rewrite rvl.
rewrite rvu.
unfold get.
simpl.
tauto.
(* vu = nvu *)
generalize H5.
simpl.
intro i.
injection i.
auto.
(* vl = nvl *)
generalize H5.
simpl.
intro i.
injection i.
auto.
(* i <>0 *)
destruct j.
(* j = 0 *)
unfold get.
simpl.
generalize H5.
simpl.
rewrite (surjective_pairing (freeAttr_aux (i - 0) n vl vu)).
intro ii.
injection ii.
tauto.
(* j<>0 *)
unfold get.
simpl.
unfold get in IHs.
generalize H5.
simpl.
intro.
apply (IHs i j n vl vu nvl nvu).
split.
lia.
split.
lia.
split.
lia.
split.
lia.
split.
lia.
split.
(* freeAttr_aux i n vl vu = (nvl, nvu) *)
generalize H8.
rewrite (surjective_pairing (freeAttr_aux (i - 0) n vl vu)).
intro ii.
injection ii.
cut (i-0 = i).
intro ri.
rewrite ri.
intros.
destruct H.
destruct H10.
case (freeAttr_aux i n vl vu).
tauto.
lia.
generalize H6.
generalize H7.
simpl.
lia.
(* length (t0 :: vu) = length nvu *)
cut (length nvu = S s).
intro rl.
rewrite rl.
generalize H7.
simpl.
auto.
cut (nvu = snd (freeAttr_aux i n (t :: vl) (t0 :: vu))).
intro rnvu.
rewrite rnvu.
apply (free_aux_size (S s) i n (t :: vl) (t0 :: vu)).
tauto.
rewrite H5.
tauto.
(* length (t :: vl) = length nvl *)
cut (length nvl = S s).
intro rl.
rewrite rl.
generalize H7.
simpl.
auto.
cut (nvl = fst (freeAttr_aux i n (t :: vl) (t0 :: vu))).
intro rnvu.
rewrite rnvu.
apply (free_aux_size (S s) i n (t :: vl) (t0 :: vu)).
tauto.
rewrite H5.
tauto.
Qed.



Lemma free_get : forall (s i j :nat) (vl vu nvl nvu:list T),
j>=0 /\ i>=0 /\ j< s /\ i< s /\ j<>i 
/\ freeAttr i vl vu = (nvl,nvu) 
/\ List.length vl = s
/\ List.length vu = s
-> get j vl = get j nvl /\ get j vu = get j nvu.
Proof.
intros.
unfold freeAttr in H.
apply (free_aux_get s i j i vl vu nvl nvu).
apply H.
Qed.


Lemma free_aux_i : forall (s i n:nat) (vl vu nvl nvu:list T),
i>=0 /\ i< s /\ s > 0
/\ freeAttr_aux i n vl vu = (nvl,nvu) 
/\ List.length vl = s
/\ List.length vu = s
-> get i nvl = (lambda n) /\ get i nvu = (nu n).
Proof.
induction s.
(* s = 0 -> impossible*)
intros.
cut False.
tauto.
lia.
(* cas général *)
intros.
destruct H as (H0,H1).
destruct H1 as (H1,H2).
destruct H2 as (H2,H3).
destruct H3 as (H3,H4).
destruct H4 as (H4,H5).
destruct vl.
(* vl = nil -> pas possible *)
cut False.
tauto.
generalize H4.
simpl.
discriminate.
(* vl <> nil *)
destruct vu.
(* vu = nil -> pas possible *)
cut False.
tauto.
generalize H5.
simpl.
discriminate.
(* vl <> nil et vu <> nil donc idem nvl et nvu -> th précédent *)
cut (List.length (t :: vl) = List.length nvl).
cut (List.length (t0 :: vu) = List.length nvu).
intros svu svl.
destruct nvl.
(* nvl vide -> pas possible *)
cut False.
tauto.
generalize svl.
discriminate.
(* nvl <> nil *)
destruct nvu.
(* nvl vide -> pas possible *)
cut False.
tauto.
generalize svu.
discriminate.
(* nvu <> nil *)
destruct i.
(* i= 0 *)
unfold get.
simpl.
generalize H3.
simpl.
intro i.
injection i.
intros.
rewrite H8.
rewrite H6.
auto.
(* i<> 0 *)
unfold get.
simpl.
unfold get in IHs.
apply (IHs i n vl vu nvl nvu).
split.
lia.
split.
lia.
split.
lia.
split.
(* freeAttr_aux i n vl vu = (nvl, nvu) *)
generalize H3.
simpl.
rewrite (surjective_pairing ( freeAttr_aux (i - 0) n vl vu)) .
intro ii.
injection ii.
cut (i-0 = i).
intro ri.
rewrite ri.
intros.
destruct H.
destruct H7.
case (freeAttr_aux i n vl vu).
tauto.
lia.
generalize H4.
generalize H5.
simpl.
lia.
(* length (t0 :: vu) = length nvu *)
cut (length nvu = S s).
intro rl.
rewrite rl.
generalize H5.
simpl.
auto.
cut (nvu = snd (freeAttr_aux i n (t :: vl) (t0 :: vu))).
intro rnvu.
rewrite rnvu.
apply (free_aux_size (S s) i n (t :: vl) (t0 :: vu)).
tauto.
rewrite H3.
tauto.
(* length (t :: vl) = length nvl *)
cut (length nvl = S s).
intro rl.
rewrite rl.
generalize H4.
simpl.
auto.
cut (nvl = fst (freeAttr_aux i n (t :: vl) (t0 :: vu))).
intro rnvu.
rewrite rnvu.
apply (free_aux_size (S s) i n (t :: vl) (t0 :: vu)).
tauto.
rewrite H3.
tauto.
Qed.

Lemma free_i : forall (s i:nat) (vl vu nvl nvu:list T),
i>=0 /\ i< s /\ s > 0
/\ freeAttr i vl vu = (nvl,nvu) 
/\ List.length vl = s
/\ List.length vu = s
-> get i nvl = (lambda i) /\ get i nvu = (nu i).
Proof.
Proof.
intros.
unfold freeAttr in H.
apply (free_aux_i s i i vl vu nvl nvu).
apply H.
Qed.

Lemma borne_free : forall (s i:nat) (vl vu nvl nvu:list T),
   i>=0 /\ i< s
/\ List.length vl = s
/\ List.length vu = s
/\ (forall (j:nat), j>=0 /\ j< s -> ( led (lambda j) (get j vl) /\ led (get j vl) (nu j) 
                                     /\ led (lambda j) (get j vu) /\ led (get j vu) (nu j)))
/\ freeAttr i vl vu = (nvl,nvu)
-> ((forall (j:nat), j>=0 /\ j< s -> led (lambda j) (get j nvl) /\ led (get j nvl) (nu j)
                                    /\ led (lambda j) (get j nvu) /\ led (get j nvu) (nu j))).
Proof.
intros.
destruct H as (H,H1).
destruct H1 as (H1,H2).
destruct H2 as (H2,H3).
destruct H3 as (H3,H4).
destruct H4 as (H4,H5).
cut (i=j \/ i<> j).
intro di.
destruct di.
(* i=j *)
cut (get j nvl = (lambda j)).
intro invl.
rewrite invl.
cut (get j nvu = (nu j)).
intro invu.
rewrite invu.
split. apply led_eq. reflexivity.
split.
cut (led (lambda j) (get j vl) /\ led (get j vl) (nu j)).
apply led_transitivity.
split.
apply (H4 j).
lia.
apply (H4 j).
lia.
split.
cut (led (lambda j) (get j vl) /\ led (get j vl) (nu j)).
apply led_transitivity.
split.
apply (H4 j).
lia.
apply (H4 j).
lia.
apply led_eq. reflexivity.
rewrite <- H6.
apply (free_i s i vl vu nvl nvu).
repeat split; [lia | lia | lia | exact H5 | exact H2 | exact H3]. 
rewrite <- H6.
apply (free_i s i vl vu nvl nvu).
repeat split; [lia | lia | lia | exact H5 | exact H2 | exact H3].
(* i<> j *) 
cut (get j vl = get j nvl).
intro invl.
rewrite <- invl.
cut (get j vu = get j nvu).
intro invu.
rewrite <- invu.
apply H4.
exact H0.
apply (free_get s i j vl vu nvl nvu).
repeat split; [lia | lia | lia | lia | lia| exact H5 | exact H2 | exact H3].
apply (free_get s i j vl vu nvl nvu).
repeat split; [lia | lia | lia | lia | lia| exact H5 | exact H2 | exact H3].
lia.
Qed.

Fixpoint fixAttr_aux (i:nat) (v vl vu :list T) : (list T * list T) :=
   match i,v,vl,vu with
   | 0,v0::qv,vl0::qvl,vu0::qvu => (v0::qvl,v0::qvu)
   | _,v0::qv,vl0::qvl,vu0::qvu =>
      let (nvl,nvu) := fixAttr_aux (i-1) qv qvl qvu in (vl0::nvl,vu0::nvu)
   |_,_,_,_ => (vl,vu)
   end. 

Definition fixAttr (i:nat) (v vl vu :list T) (p : list nat) : (list T * list T * list nat ) :=
  let (nvl,nvu) := fixAttr_aux i v vl vu in (nvl,nvu,i::p).


Lemma fix_aux_size : forall (s:nat) (i:nat) (v vl vu :list T),
i>=0 /\ i< s
/\ List.length v = s
/\ List.length vl = s
/\ List.length vu = s
->  List.length (fst (fixAttr_aux i v vl vu)) = s
/\ List.length  (snd (fixAttr_aux i v vl vu)) = s.
Proof.
induction s.
(* s = 0 -> impossible*)
intros.
cut False.
tauto.
lia.
(* s <> 0 - cas général *)
intros.
destruct H as (H0,H1).
destruct H1 as (H1,H2).
destruct H2 as (H2,H3).
destruct H3 as (H3,H4).
destruct v.
(* v = nil -> impossible *)
cut False.
tauto.
generalize H2.
simpl.
discriminate.
(* v <> nil *)
destruct vl.
(* vl = nil -> impossible *)
cut False.
tauto.
generalize H3.
simpl.
discriminate.
(* vl <> nil *)
destruct vu.
(* vu = nil -> impossible *)
cut False.
tauto.
generalize H4.
simpl.
discriminate.
(* v <> nil /\ vl <> nil /\ vu <> nil *)
destruct i.
(* i =0 *)
simpl.
generalize H3.
generalize H4.
simpl.
auto.
(* i <> 0 *)
simpl.
rewrite (surjective_pairing (fixAttr_aux (i - 0) v vl vu)).
simpl.
cut (i-0 = i).
intro ri.
rewrite ri.
split.
apply f_equal.
apply (IHs i v vl vu).
repeat split; [lia | lia | generalize H2; simpl; auto | generalize H3; simpl; auto | generalize H4; simpl; auto ].
apply f_equal.
apply (IHs i v vl vu).
repeat split; [lia | lia | generalize H2; simpl; auto | generalize H3; simpl; auto | generalize H4; simpl; auto ].
lia.
Qed.

Lemma fix_size : forall (s:nat) (i:nat) (v vl vu :list T) (p : list nat),
i>=0 /\ i< s
/\ List.length v = s
/\ List.length vl = s
/\ List.length vu = s
->  List.length (fst (fst (fixAttr i v vl vu p))) = s
/\ List.length  (snd (fst (fixAttr i v vl vu p))) = s.
Proof.
intros.
destruct H as (H0,H1).
destruct H1 as (H1,H2).
destruct H2 as (H2,H3).
destruct H3 as (H3,H4).
unfold fixAttr.
rewrite (surjective_pairing (fixAttr_aux i v vl vu)).
simpl.
apply (fix_aux_size s i v vl vu).
repeat split; [lia | lia | exact H2 | exact H3 | exact H4].
Qed.


Lemma fix_p : forall (i:nat) (v vl vu : list T) (p: list nat) (nvl nvu : list T) (np : list nat),
fixAttr i v vl vu p = (nvl,nvu,np) -> np = i::p.
Proof.
intros.
symmetry.
generalize H.
unfold fixAttr.
rewrite (surjective_pairing ( fixAttr_aux i v vl vu)).
intro inj.
injection inj.
auto.
Qed.

(* ancien fix_get *)
Lemma fix_i : forall (s i:nat) (v vl vu : list T) (p: list nat) (nvl nvu : list T) (np : list nat),
   i>=0 /\ i< s
/\ List.length v = s
/\ List.length vl = s
/\ List.length vu = s
/\ fixAttr i v vl vu p = (nvl,nvu,np) 
-> get i nvl = get i v /\ get i nvu = get i v.
Proof.
induction s.
(* s = 0 -> impossible *)
intros.
cut False. tauto. lia.
(* s <> 0 *)
intros.
destruct H as (H0,H1).
destruct H1 as (H1,H2).
destruct H2 as (H2,H3).
destruct H3 as (H3,H4).
destruct H4 as (H4,H5).
destruct v.
(* v = nil -> impossible *)
cut False.
tauto.
generalize H2.
simpl.
discriminate.
(* v <> nil *)
destruct vl.
(* vl = nil -> impossible *)
cut False.
tauto.
generalize H3.
simpl.
discriminate.
(* vl <> nil *)
destruct vu.
(* vu = nil -> impossible *)
cut False.
tauto.
generalize H4.
simpl.
discriminate.
(* v <> nil /\ vl <> nil /\ vu <> nil *)
destruct i.
(* i =0 *)
unfold get.
generalize H5.
simpl.
intro inj.
injection inj.
intros.
rewrite <- H7.
rewrite <- H6.
simpl.
auto.
(* i <> 0 *)
generalize H5.
unfold get.
unfold fixAttr.
simpl.
unfold get in IHs.
rewrite (surjective_pairing (fixAttr_aux (i - 0) v vl vu)).
cut (i-0=i).
intro ri.
rewrite ri.
intro inj.
injection inj.
intros.
rewrite <- H7.
rewrite <- H6.
simpl.
apply (IHs i v vl vu p (fst (fixAttr_aux i v vl vu)) (snd (fixAttr_aux i v vl vu)) (i::p)).
split. lia.
split. lia.
split. generalize H2. simpl. auto.
split. generalize H3. simpl. auto.
split. generalize H4. simpl. auto.
unfold fixAttr.
rewrite (surjective_pairing (fixAttr_aux i v vl vu)).
simpl.
reflexivity.
lia.
Qed.


Lemma fix_aux_get : forall (s i j : nat) (v vl vu : list T) (p: list nat) (nvl nvu : list T) (np : list nat),  
   i>=0 /\ i< s /\ j>=0 /\ j< s
/\ i<> j
/\ List.length v = s
/\ List.length vl = s
/\ List.length vu = s
/\ fixAttr_aux i v vl vu = (nvl,nvu) 
-> get j vl = get j nvl /\ get j vu = get j nvu.
Proof.
induction s.
(* s = 0 -> impossible *)
intros.
cut False. tauto. lia.
(* s <> 0 *)
intros.
destruct H as (H0,H1).
destruct H1 as (H1,H2).
destruct H2 as (H2,H3).
destruct H3 as (H3,H4).
destruct H4 as (H4,H5).
destruct H5 as (H5,H6).
destruct H6 as (H6,H7).
destruct H7 as (H7,H8).
destruct v.
(* v = nil -> impossible *)
cut False.
tauto.
generalize H5.
simpl.
discriminate.
(* v <> nil *)
destruct vl.
(* vl = nil -> impossible *)
cut False.
tauto.
generalize H6.
simpl.
discriminate.
(* vl <> nil *)
destruct vu.
(* vu = nil -> impossible *)
cut False.
tauto.
generalize H7.
simpl.
discriminate.
(* v <> nil /\ vl <> nil /\ vu <> nil *)
destruct i.
(* i =0 *)
destruct j.
(* j = 0 -> impossible *)
cut False.
tauto.
lia.
(*j <> 0 *)
generalize H8.
unfold get.
simpl.
intros.
injection H9.
intros.
rewrite <- H10.
rewrite <- H.
simpl.
auto.
(* i<> 0 *)
destruct j.
(* j = 0  *)
unfold get.
generalize H8.
simpl.
simpl.
rewrite (surjective_pairing(fixAttr_aux (i - 0) v vl vu)).
intro inj.
injection inj.
intros.
rewrite <- H.
rewrite <- H9.
simpl.
auto.
(*j <> 0 *)
unfold get.
simpl.
generalize H8.
cut (length nvl = length (t0::vl)).
cut (length nvu = length (t1::vu)).
intros.
destruct nvl.
(* nvl = nil -> impossible *)
cut False.
tauto.
generalize H9.
simpl.
discriminate.
(* nvl <> nil *)
destruct nvu.
(* nvu = nil -> impossible *)
cut False.
tauto.
generalize H.
simpl.
discriminate.
(* nvu <> nil *)
simpl.
unfold get in IHs.
apply (IHs i j v vl vu p nvl nvu np).
split. lia.
split. lia.
split. lia.
split. lia.
split. lia.
split. generalize H5. simpl. auto.
split. generalize H6. simpl. auto.
split. generalize H7. simpl. auto.
generalize H8.
simpl.
cut (i-0  = i).
intro ri.
rewrite ri.
rewrite (surjective_pairing( fixAttr_aux i v vl vu)).
intro inj.
injection inj.
intros.
rewrite H11. rewrite H13.
auto.
lia.
(* length nvu = length (t1 :: vu)*)
generalize H8.
simpl.
rewrite (surjective_pairing (fixAttr_aux (i - 0) v vl vu)).
cut (i-0 = i).
intro ri.
rewrite ri.
intro inj.
injection inj.
intros.
rewrite <- H.
simpl.
apply f_equal.
cut (length vu = s).
intro lvu.
rewrite lvu.
apply (fix_aux_size s i v vl vu).
split. lia.
split. lia.
split. generalize H5. simpl. auto.
split. generalize H6. simpl. auto.
generalize H7. simpl. auto.
generalize H7. simpl. auto.
lia.
(* length nvl = length (t0 :: vl)*)
generalize H8.
simpl.
rewrite (surjective_pairing (fixAttr_aux (i - 0) v vl vu)).
cut (i-0 = i).
intro ri.
rewrite ri.
intro inj.
injection inj.
intros.
rewrite <- H9.
simpl.
apply f_equal.
cut (length vl = s).
intro lvu.
rewrite lvu.
apply (fix_aux_size s i v vl vu).
split. lia.
split. lia.
split. generalize H5. simpl. auto.
split. generalize H6. simpl. auto.
generalize H7. simpl. auto.
generalize H6. simpl. auto.
lia.
Qed.


Lemma fix_get : forall (s i j : nat) (v vl vu : list T) (p: list nat) (nvl nvu : list T) (np : list nat),  
   i>=0 /\ i< s /\ j>=0 /\ j< s
/\ i<> j
/\ List.length v = s
/\ List.length vl = s
/\ List.length vu = s
/\ fixAttr i v vl vu p  = (nvl,nvu,np) 
-> get j vl = get j nvl /\ get j vu = get j nvu.
Proof.
   intros.
   destruct H as (H0,H1).
   destruct H1 as (H1,H2).
   destruct H2 as (H2,H3).
   destruct H3 as (H3,H4).
   destruct H4 as (H4,H5).
   destruct H5 as (H5,H6).
   destruct H6 as (H6,H7).
   destruct H7 as (H7,H8).
   apply (fix_aux_get s i j v vl vu p nvl nvu np).
   split. lia.
   split. lia.
   split. lia.
   split. lia.
   split. lia.
   split. exact H5.
   split. exact H6.
   split. exact H7.
   unfold fixAttr in H8.
   generalize H8.
   rewrite (surjective_pairing (fixAttr_aux i v vl vu)).
   intros inj.
   injection inj.
   intros.
   rewrite H9.
   rewrite H10.
   auto.
Qed.


Lemma free_fix_id : forall (s i j : nat) (v vl vu nvl nvu: list T) (p: list nat) (nnvl nnvu : list T) (np : list nat),  
i>=0 /\ i< s /\ j>=0 /\ j< s/\ i<> j
/\ List.length v = s
/\ List.length vl = s
/\ List.length vu = s
/\ freeAttr i vl vu = (nvl,nvu)
/\ fixAttr i v nvl nvu p = (nnvl,nnvu,np)
-> get j nnvl = get j vl /\ get j nnvu = get j vu.
Proof.
   intros.
   destruct H as (H0,H1).
   destruct H1 as (H1,H2).
   destruct H2 as (H2,H3).
   destruct H3 as (H3,H4).
   destruct H4 as (H4,H5).
   destruct H5 as (H5,H6).
   destruct H6 as (H6,H7).
   destruct H7 as (H7,H8).
   destruct H8 as (H8,H9).
   cut (length nvl = s).
   intro.
   cut (length nvu = s).
   intro.
   cut (length nnvl = s).
   intro.
   cut (length nnvu = s).
   intro.
   cut (get j vl = get j nvl /\ get j vu = get j nvu).
   intro.
   destruct H13.
   rewrite H13.
   rewrite H14.
   split.
   symmetry.
   apply (fix_get s i j v nvl nvu p nnvl nnvu np).
   repeat split; [lia | lia | lia | lia | lia| exact H5 | exact H | exact H10 | exact H9].
   symmetry.
   apply (fix_get s i j v nvl nvu p nnvl nnvu np).
   repeat split; [lia | lia | lia | lia | lia| exact H5 | exact H | exact H10 | exact H9].
   apply (free_get s i j vl vu nvl nvu).
   repeat split; [lia | lia | lia | lia | lia| exact H8 | exact H6 | exact H7].
   (* length nnvu = s *)
   generalize H9.
   unfold fixAttr.
   rewrite (surjective_pairing(fixAttr_aux i v nvl nvu)).
   intro inj.
   injection inj.
   intros.
   rewrite <- H13.
   apply (fix_aux_size s i v nvl nvu ).
   auto.
   (* length nnvl = s *)
   generalize H9.
   unfold fixAttr.
   rewrite (surjective_pairing(fixAttr_aux i v nvl nvu)).
   intro inj.
   injection inj.
   intros.
   rewrite <- H13.
   apply (fix_aux_size s i v nvl nvu ).
   auto.
   (* length nvu = s *)
   generalize H8.
   rewrite (surjective_pairing( freeAttr i vl vu)).
   intro inj.
   injection inj.
   intros.
   rewrite <- H10.
   apply (free_size s i vl vu ).
   auto.
   (* length nvl = s *)
   generalize H8.
   rewrite (surjective_pairing( freeAttr i vl vu)).
   intro inj.
   injection inj.
   intros.
   rewrite <- H10.
   apply (free_size s i vl vu ).
   auto.
Qed.


Lemma fix_free_id : forall (s i j : nat) (v vl vu nvl nvu: list T) (p: list nat) (nnvl nnvu : list T) (np : list nat),  
i>=0 /\ i< s /\ j>=0 /\ j< s/\ i<> j
/\ List.length v = s
/\ List.length vl = s
/\ List.length vu = s
/\ fixAttr i v vl vu p = (nvl,nvu,np)
/\ freeAttr i nvl nvu = (nnvl,nnvu)
-> get j nnvl = get j vl /\ get j nnvu = get j vu.
Proof.
   intros.
   destruct H as (H0,H1).
   destruct H1 as (H1,H2).
   destruct H2 as (H2,H3).
   destruct H3 as (H3,H4).
   destruct H4 as (H4,H5).
   destruct H5 as (H5,H6).
   destruct H6 as (H6,H7).
   destruct H7 as (H7,H8).
   destruct H8 as (H8,H9).
   cut (length nvl = s).
   intro.
   cut (length nvu = s).
   intro.
   cut (length nnvl = s).
   intro.
   cut (length nnvu = s).
   intro.
   cut (get j vl = get j nvl /\ get j vu = get j nvu).
   intro.
   destruct H13.
   rewrite H13.
   rewrite H14.
   split.
   symmetry.
   apply (free_get s i j nvl nvu nnvl nnvu).
   repeat split; [lia | lia | lia | lia | lia| exact H9 | exact H | exact H10].
   symmetry.
   apply (free_get s i j nvl nvu nnvl nnvu).
   repeat split; [lia | lia | lia | lia | lia| exact H9 | exact H | exact H10].
   apply (fix_get s i j v vl vu p nvl nvu np).
   repeat split; [lia | lia | lia | lia | lia| exact H5 | exact H6 | exact H7 | exact H8].
   (* length nnvu = s *)
   generalize H9.
   unfold freeAttr.
   rewrite (surjective_pairing(freeAttr_aux i i nvl nvu)).
   intro inj.
   injection inj.
   intros.
   rewrite <- H12.
   apply (free_size s i nvl nvu ).
   auto.
   (* length nnvl = s *)
   generalize H9.
   unfold freeAttr.
   rewrite (surjective_pairing(freeAttr_aux i i nvl nvu)).
   intro inj.
   injection inj.
   intros.
   rewrite <- H12.
   apply (free_size s i nvl nvu ).
   auto.
   (* length nvu = s *)
   generalize H8.
   rewrite (surjective_pairing( fixAttr i v vl vu p)).
   intro inj.
   injection inj.
   rewrite (surjective_pairing( fst (fixAttr i v vl vu p))).
   intros.
   injection H11.
   intros.
   rewrite <- H12.
   apply (fix_size s i v vl vu ).
   auto.
   (* length nvl = s *)
   generalize H8.
   rewrite (surjective_pairing( fixAttr i v vl vu p)).
   intro inj.
   injection inj.
   rewrite (surjective_pairing( fst (fixAttr i v vl vu p))).
   intros.
   injection H10.
   intros.
   rewrite <- H12.
   apply (fix_size s i v vl vu ).
   auto.
Qed.



Lemma borne_fix : forall (s i:nat) (v vl vu : list T) (p: list nat) (nvl nvu: list T) (np : list nat),
i>=0 /\ i< s
/\ List.length v = s
/\ List.length vl = s
/\ List.length vu = s
/\ (forall (j:nat), j>=0 /\ j< s -> (  led (lambda j) (get j v) /\ led (get j v) (nu j) 
                                    /\ led (lambda j) (get j vl) /\ led (get j vl) (nu j) 
                                    /\ led (lambda j) (get j vu) /\ led (get j vu) (nu j)))
/\ fixAttr i v vl vu p= (nvl,nvu,np)
-> (forall (j:nat), j>=0 /\ j< s -> (led (lambda j) (get j nvl) /\ led (get j nvl) (nu j)
                                    /\ led (lambda j) (get j nvu) /\ led (get j nvu) (nu j))).
Proof.
   intros.
destruct H as (H,H1).
destruct H1 as (H1,H2).
destruct H2 as (H2,H3).
destruct H3 as (H3,H4).
destruct H4 as (H4,H5).
destruct H5 as (H5,H6).
cut (i=j \/ i<> j).
intro di.
destruct di.
(* i=j *)
cut (get j nvl = (get j v)).
intro invl.
rewrite invl.
cut (get j nvu = (get j v)).
intro invu.
rewrite invu.
repeat split; [apply H5; lia |apply H5; lia |apply H5; lia |apply H5; lia].
rewrite <- H7.
apply (fix_i s i v vl vu p nvl nvu np).
repeat split; [lia | lia | exact H2 | exact H3 | exact H4 | exact H6 ]. 
rewrite <- H7.
apply (fix_i s i v vl vu p nvl nvu np).
repeat split; [lia | lia | exact H2 | exact H3 | exact H4 | exact H6 ]. 
(* i<> j *) 
cut (get j vl = get j nvl).
intro invl.
rewrite <- invl.
cut (get j vu = get j nvu).
intro invu.
rewrite <- invu.
apply H5.
exact H0.
apply (fix_get s i j v vl vu p nvl nvu np).
repeat split; [lia | lia | lia | lia | lia| exact H2 | exact H3 | exact H4 | exact H6].
apply (fix_get s i j v vl vu p nvl nvu np).
repeat split; [lia | lia | lia | lia | lia| exact H2 | exact H3 | exact H4 | exact H6].
lia.
Qed.


(* missing that it should be the smallest set *)  
Definition is_weak_AXp (k : list T -> Tk) (v: list T) (p:list nat) : Prop :=
   forall (x: list T),
   List.length v = nb_feature
/\ List.length x = nb_feature
/\ (forall (j:nat), j>=0 /\ j< nb_feature -> (led (lambda j) (get j x) /\ led (get j x) (nu j))) 
/\ (forall (j:nat), j>=0 /\ j< nb_feature -> ((mem j p /\ get j x = get j v) \/ (not (mem j p))))
 -> k(x)=k(v).

Fixpoint is_sorted (p:list nat) : Prop :=
match p with
| nil => True
| t :: q => (forall (e:nat), mem e q -> t>e) /\ is_sorted q
end.

(* moche mais plus facil à manipuler en coq *)
(* La terminaison est évidente et la manipulation est plus simple qu'avec Programm Fixpoint *)
(* i = nb_feature-j *)
Fixpoint findAXp_aux_j (k : list T -> Tk)  (j:nat) (v vl vu: list T) (p:list nat) {struct j}:
list nat :=
match j with
| 0 => p 
| S jmoins1 => 
  let '(nvl,nvu) := freeAttr (nb_feature-j) vl vu in
    match Tk_eq_dec (k nvl) (k nvu) with
    | false => let '(nvl,nvu,np) := fixAttr (nb_feature-j) v nvl nvu p in
               findAXp_aux_j k jmoins1 v nvl nvu np
    | true => findAXp_aux_j k jmoins1 v nvl nvu p
    end 
end.

Lemma findAXp_aux_j_spec2 :
 forall  (k : list T -> Tk) (j:nat) (v vl vu: list T) (p:list nat),
   j>0 
/\ ( let '(nvl,nvu) :=  freeAttr (nb_feature-j) vl vu in (k nvl) <> (k nvu))
-> let '(nvl,nvu) :=  freeAttr (nb_feature-j) vl vu in let '(nnvl,nnvu,np) := fixAttr (nb_feature-j) v nvl nvu p in findAXp_aux_j k j v vl vu p = findAXp_aux_j k (j-1) v nnvl nnvu np.
Proof.
intros.
destruct H.
rewrite (surjective_pairing (freeAttr (nb_feature - j) vl vu)).
rewrite (surjective_pairing (fixAttr (nb_feature - j) v (fst (freeAttr (nb_feature - j) vl vu))
(snd (freeAttr (nb_feature - j) vl vu)) p )).
rewrite (surjective_pairing (fst
(fixAttr (nb_feature - j) v
   (fst (freeAttr (nb_feature - j) vl vu))
   (snd (freeAttr (nb_feature - j) vl vu)) p))).
   
destruct j.
(* j=0 *)
lia.
(* j <> 0*)
simpl.
cut (j-0=j).
intro rj.
rewrite rj.
rewrite (surjective_pairing (freeAttr (nb_feature - S j) vl vu)).
cut ( Tk_eq_dec (k (fst (freeAttr (nb_feature - S j) vl vu)))
(k (snd (freeAttr (nb_feature - S j) vl vu))) = false).
intro r2.
rewrite r2.
rewrite (surjective_pairing (fixAttr (nb_feature - S j) v
(fst (freeAttr (nb_feature - S j) vl vu))
(snd (freeAttr (nb_feature - S j) vl vu)) p)).
rewrite (surjective_pairing (fst
(fixAttr (nb_feature - S j) v
   (fst (freeAttr (nb_feature - S j) vl vu))
   (snd (freeAttr (nb_feature - S j) vl vu)) p))).
simpl.
reflexivity.
(* Tk_eq_dec *)
generalize H0.
rewrite (surjective_pairing (freeAttr (nb_feature - S j) vl vu)).
simpl.
apply Tk_eq_coherent_neq.
(* j-0 = j *)
lia.
Qed.


Lemma findAXp_aux_j_spec3 :
forall  (k : list T -> Tk) (j:nat) (v vl vu: list T) (p:list nat),
j>0 /\ ( let '(nvl,nvu) :=  freeAttr (nb_feature-j) vl vu in (k nvl) = (k nvu))
-> let '(nvl,nvu) :=  freeAttr (nb_feature-j) vl vu in findAXp_aux_j k j v vl vu p = findAXp_aux_j k (j-1) v nvl nvu p.
Proof.
intros.
destruct H.
rewrite (surjective_pairing (freeAttr (nb_feature - j) vl vu)).
destruct j.
(* j = 0 : 0>0 en hypothèse *)
lia.
(* j > 0 : cas général *)
simpl.
cut (j-0=j).
intro r3.
rewrite r3.
rewrite (surjective_pairing (freeAttr (nb_feature - S j) vl vu)).
 cut ( Tk_eq_dec (k (fst (freeAttr (nb_feature - S j) vl vu)))
 (k (snd (freeAttr (nb_feature - S j) vl vu))) = true).
intro r2.
rewrite r2.
simpl.
reflexivity.
(* Tk_eq_dec *)
generalize H0.
rewrite (surjective_pairing (freeAttr (nb_feature - S j) vl vu)).
simpl.
apply Tk_eq_coherent_eq.
(* j-0 = j *)
lia.
Qed.


Definition findAXp_aux  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat):
list nat := findAXp_aux_j k (nb_feature-i) v vl vu p.


Lemma findAXp_aux_spec2 : 
forall  (k : list T -> Tk)  (i:nat) (v vl vu: list T) (p:list nat),
i>= 0 /\ i < nb_feature 
/\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) <> (k nvu))
-> let '(nvl,nvu) :=  freeAttr i vl vu in let '(nnvl,nnvu,np) := fixAttr i v nvl nvu p in findAXp_aux k i v vl vu p = findAXp_aux k (i+1) v nnvl nnvu np.
Proof.
intros.
destruct H.
destruct H0.
cut (exists j:nat, j= nb_feature - i).
intro.
destruct H2 as (j,H2).
cut (i = nb_feature - j).
intro ri.
rewrite ri.
unfold findAXp_aux.
cut (nb_feature - (nb_feature - j) = j).
intro rj.
rewrite rj.
cut (nb_feature - (nb_feature - j + 1) = j-1).
intro rjm1.
rewrite rjm1.
apply findAXp_aux_j_spec2.
(*Hyp findAXp_aux_j_spec2 *)
split.
lia.
rewrite <- ri.
exact H1.
(* egalité *)
lia.
lia.
lia.
exists (nb_feature-i).
reflexivity.
Qed.

Lemma findAXp_aux_spec3 : 
forall  (k : list T -> Tk)  (i:nat) (v vl vu: list T) (p:list nat),
i>= 0 /\ i < nb_feature 
/\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) = (k nvu))
-> let '(nvl,nvu) :=  freeAttr i vl vu in findAXp_aux k i v vl vu p = findAXp_aux k (i+1) v nvl nvu p.
Proof.
intros.
destruct H.
destruct H0.
cut (exists j:nat, j= nb_feature - i).
intro.
destruct H2 as (j,H2).
cut (i = nb_feature - j).
intro ri.
rewrite ri.
unfold findAXp_aux.
cut (nb_feature - (nb_feature - j ) = j).
intro rj.
rewrite rj.
cut (nb_feature - (nb_feature - j + 1) = j-1).
intro rjm1.
rewrite rjm1.
apply findAXp_aux_j_spec3.
(*Hyp findAXp_aux_j_spec3 *)
split.
lia.
rewrite <- ri.
exact H1.
(* egalité *)
lia.
lia.
lia.
exists (nb_feature-i).
reflexivity.
Qed.


Definition R0  (k : list T -> Tk)  (i:nat) (v vl vu: list T) (p:list nat) : Prop :=
   List.length v = nb_feature
/\ List.length vl = nb_feature
/\ List.length vu = nb_feature.

Definition R1  (k : list T -> Tk)  (i:nat) (v vl vu: list T) (p:list nat) : Prop :=
   forall (j:nat), j>=0 /\ j< nb_feature -> 
     led (lambda j) (get j v) /\ led (get j v) (nu j)
  /\ led (lambda j) (get j vl) /\ led (get j vl) (nu j)
  /\ led (lambda j) (get j vu) /\ led (get j vu) (nu j). 


Definition R2  (k : list T -> Tk)  (i:nat) (v vl vu: list T) (p:list nat) : Prop :=
  k vl = k vu /\ k vl = k v.
  (* k vl = k v since k is stable *)

Definition R3  (k : list T -> Tk)  (i:nat) (v vl vu: list T) (p:list nat) : Prop :=
  i >= 0.

Definition R4  (k : list T -> Tk)  (i:nat) (v vl vu: list T) (p:list nat) : Prop :=
  forall (j:nat), 
     ((get j vl = lambda j) /\ (get j vu = nu j)) 
  \/ ((get j vl = get j v) /\ (get j vu = get j v)).

Definition R4_bis  (k : list T -> Tk)  (i:nat) (v vl vu: list T) (p:list nat) : Prop :=
    forall (j:nat), 
      (j>=0 /\ j< nb_feature) ->
       ((get j vl = lambda j) /\ (get j vu = nu j)) 
    \/ ((get j vl = get j v) /\ (get j vu = get j v)).

Definition R5  (k : list T -> Tk)  (i:nat) (v vl vu: list T) (p:list nat) : Prop :=
  forall (j:nat),
  (j>= i \/ j<0 \/ j>=nb_feature -> not (mem j p)).

Definition R6  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat) : Prop :=
  forall (j:nat),
  ((mem j p) -> ((get j vl = get j v) /\ (get j vu = get j v))).
  
Definition R7  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat) : Prop :=
  forall (j:nat),
  (j>=0 /\ j<i /\ not( mem j p)) -> ((get j vl = lambda j) /\ (get j vu = nu j)).
  
Definition R8  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat) : Prop := is_sorted p.

Definition R9  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat) : Prop :=
  forall (j:nat),
  (j>=i /\ j>=0 /\ i>=0 /\ j<nb_feature /\ i<nb_feature
  -> ((get j vl = get j v) /\ (get j vu = get j v))).
  
Definition R10  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat) : Prop :=
  forall (x:nat), forall (x0 x1 : list nat), 
  (p = x0++(x::x1)
-> 
exists (nvl nvu : list T),
length nvl = nb_feature /\
length nvu = nb_feature /\
(forall (j:nat), j>=0 /\ j< nb_feature 
  ->  ((mem j x1 \/ j>x) /\ get j nvl=get j v /\ get j nvu =get j v) 
        \/ ( (not (mem j x1 \/ j>x)) /\ get j nvl =lambda j /\ get j nvu =nu j) ) 
/\ (k nvl) <> (k nvu)).


Definition E1  (k : list T -> Tk)  (i:nat) (v vl vu: list T) (p:list nat) : Prop := 
  is_weak_AXp k v (findAXp_aux k i v vl vu p).

Definition E2  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat) : Prop := 
  is_sorted (findAXp_aux k i v vl vu p).

Definition E3  (k : list T -> Tk)  (i:nat) (v vl vu: list T) (p:list nat) : Prop := 
  forall (x:nat), forall (x0 x1 : list nat), ((findAXp_aux k i v vl vu p) = x0++(x::x1)
-> 
exists  (vl vu : list T),
length vl = nb_feature /\
length vu = nb_feature /\
 (forall (j:nat), j>=0 /\ j< nb_feature 
 ->  ((mem j x1 \/ j>x) /\ get j vl=get j v /\ get j vu=get j v) 
 \/ ( (not (mem j x1 \/ j>x)) /\ get j vl=lambda j /\ get j vu = nu j) )
/\ (k vl) <> (k vu)).

Lemma my_induction : 
 forall (nb:nat) (P : nat -> Prop) ,
 ((forall (i:nat), (i>=0 /\ i < nb) -> (P(i+1)->P(i))) /\ P(nb)
 -> 
 (forall (i:nat), i>=0 /\ i < nb +1 -> P(i))).
 Proof.
 intros.
 decompose [and] H.
 decompose [and] H0.
 induction nb.
 (* cas de base *)
 cut (i=0).
 intro ri.
 rewrite ri.
 tauto.
 lia.
 (* cas général *)
 cut (i<= nb  \/ i =  S nb).
 intro d.
 destruct d.
 (* i<= nb + 1 : OK appliquer induction *)
  apply IHnb.
  (* (forall i0 : nat, i0 > 0 /\ i0 <= nb -> P (i0 + 1) -> P i0) /\ P (nb + 1) *)
  split.
  intros.
  apply H1.
  lia.
  exact H7.
  apply H1.
  lia.
  generalize H2.
  cut (S nb= nb +1).
  intro r.
  rewrite r.
  auto.
  lia.
  lia.
  intros.
  apply H1.
  lia.
  exact H7.
  apply H1.
  lia.
  generalize H2.
  cut (S nb = nb +1).
  intro r.
  rewrite r.
  auto.
  lia.
  lia.
  (* i = S nb + 1 *)
  rewrite H5.
  auto.
  (* i <= nb + 1 \/ i = S nb + 1*)
  lia.
Qed.

Definition R_implies_E_AXp (k : list T -> Tk) (i:nat) : Prop :=
  forall    (v vl vu: list T) (p:list nat), 
  (R0 k i v vl vu p /\
   R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
   R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9 k i v vl vu p /\ R10 k i v vl vu p) 
  -> (E1 k i v vl vu p) /\ (E2 k i v vl vu p) /\ (E3 k i v vl vu p).

Lemma preserveR0Cas2_AXp : 
forall  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) <> (k nvu)) /\ 
(R0 k i v vl vu p /\
R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
R9 k i v vl vu p /\ R10 k i v vl vu p) 
-> R0 k (i + 1) v
(fst
  (fst
     (fixAttr i v (fst (freeAttr i vl vu))
        (snd (freeAttr i vl vu)) p)))
(snd
  (fst
     (fixAttr i v (fst (freeAttr i vl vu))
        (snd (freeAttr i vl vu)) p)))
(snd
  (fixAttr i v (fst (freeAttr i vl vu))
     (snd (freeAttr i vl vu)) p)) .
Proof.
   intros. 
   unfold R0.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.

   cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
   intro varfree.
   destruct varfree as (nvl,varfree).
   destruct varfree as (nvu,varfree).
   rewrite varfree.
   simpl.

   split.
   apply HR0.
   apply (fix_size nb_feature i v nvl nvu p).
   split. lia.
   split. lia.
   
   cut (nvl = fst (freeAttr i vl vu)).
   intro rvl.
   rewrite rvl.
   cut (nvu = snd (freeAttr i vl vu)).
   intro rvu.
   rewrite rvu.

   split.
   apply HR0.
   apply (free_size nb_feature i vl vu).
   split. lia. apply HR0.
   rewrite varfree. simpl. reflexivity.
   rewrite varfree. simpl. reflexivity.

   destruct (freeAttr i vl vu).
   exists l.
   exists l0.
   reflexivity.
Qed.

Lemma preserveSizeCas2 : forall (i:nat) (v vl vu nvl nvu nnvl nnvu : list T) (p np:list nat),
   i>= 0 /\ i < nb_feature  
/\ List.length v = nb_feature
/\ List.length vl = nb_feature
/\ List.length vu = nb_feature
/\ freeAttr i vl vu = (nvl, nvu)
/\ fixAttr i v nvl nvu p = (nnvl, nnvu, np)
-> List.length nvl = nb_feature
/\ List.length nvu = nb_feature
/\ List.length nnvl = nb_feature
/\ List.length nnvu = nb_feature.
Proof.
   intros.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Lv,H).
   destruct H as (Lvl,H).
   destruct H as (Lvu,H).
   destruct H as (Hfree,Hfix).

   cut (List.length nvl = nb_feature).
   intro Lnvl.
   cut (List.length nvu = nb_feature).
   intro Lnvu.

   split.
   exact Lnvl.
   split.
   exact Lnvu.

  
   cut (nnvl = fst (fst (fixAttr i v nvl nvu p) )).
   intro rnvl.
   rewrite rnvl.
   cut (nnvu = snd (fst (fixAttr i v nvl nvu p) )).
   intro rnvu.
   rewrite rnvu.
   split.
   apply (fix_size nb_feature i v nvl nvu p).
   split. lia. split. lia. split. apply Lv. split. apply Lnvl. apply Lnvu.
   apply (fix_size nb_feature i v nvl nvu p).
   split. lia. split. lia. split. apply Lv. split. apply Lnvl. apply Lnvu.
   
   rewrite Hfix. simpl. reflexivity.
   rewrite Hfix. simpl. reflexivity.

   (* Lnvu *)
   cut (nvu = snd (freeAttr i vl vu)).
   intro rvu.
   rewrite rvu.
   apply (free_size nb_feature i vl vu).
   split. apply Lvl. apply Lvu.
   rewrite Hfree. simpl. reflexivity.

   (* Lnvl*)
   cut (nvl = fst (freeAttr i vl vu)).
   intro rvl.
   rewrite rvl.
   apply (free_size nb_feature i vl vu).
   split. apply Lvl. apply Lvu.
   rewrite Hfree. simpl. reflexivity.
Qed.



Lemma preserveR1Cas2_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
  i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) <> (k nvu)) /\ 
  (R0 k i v vl vu p /\
  R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
  R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
  R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R1 k (i + 1) v
 (fst
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fixAttr i v (fst (freeAttr i vl vu))
       (snd (freeAttr i vl vu)) p)) .
Proof.
intros. 
unfold R1.
destruct H as (Hi_inf,H).
destruct H as (Hi_sup,H).
destruct H as (Hdif_k,H).
destruct H as (HR0,H).
destruct H as (HR1,H).
destruct H as (HR2,H).
destruct H as (HR3,H).
destruct H as (HR4,H).
destruct H as (HR5,H).
destruct H as (HR6,H).
destruct H as (HR7,H).
destruct H as (HR8,H).
destruct H as (HR9,HR10).
unfold R0 in HR0.
unfold R1 in HR1.
split.
apply HR1.
lia.
split.
apply HR1.
lia.


cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
intro varfree.
destruct varfree as (nvl,varfree).
destruct varfree as (nvu,varfree).
rewrite varfree.
simpl.

cut (exists (nnvl nnvu : list T) (np : list nat), fixAttr i v nvl nvu p = (nnvl,nnvu,np)).
intro varfix.
destruct varfix as (nnvl,varfix).
destruct varfix as (nnvu,varfix).
destruct varfix as (np,varfix).
rewrite varfix.
simpl.

generalize (preserveSizeCas2 i v vl vu nvl nvu nnvl nnvu p np).
intro HR0p.

apply (borne_fix nb_feature i v nvl nvu p nnvl nnvu np).
split. lia.
split. lia.
split. apply HR0.
split. apply HR0p.
repeat split; [lia | lia | apply HR0 | apply HR0 | apply HR0 | exact varfree | exact varfix].
split. apply HR0p.
repeat split; [lia | lia | apply HR0 | apply HR0 | apply HR0 | exact varfree | exact varfix].
split. 

intro.
split. apply HR1. exact H0.
split. apply HR1. exact H0.
apply (borne_free nb_feature i vl vu nvl nvu).
split. lia.
split. lia.
split. apply HR0.
split. apply HR0.
split. apply HR1.

exact varfree.
lia.
exact varfix.
lia.


(* preuve des cut avec les exists *)
destruct (fixAttr i v nvl nvu p).
destruct p0.
exists l0.
exists l1.
exists l.
reflexivity.

destruct (freeAttr i vl vu).
exists l.
exists l0.
reflexivity.

Qed.

Lemma preserveR2Cas2_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) <> (k nvu)) /\ 
  (R0 k i v vl vu p /\
  R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
  R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
  R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R2 k (i + 1) v
 (fst
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fixAttr i v (fst (freeAttr i vl vu))
       (snd (freeAttr i vl vu)) p)) .
Proof.
   intros. 
   unfold R2.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.
   unfold R2 in HR2.
   unfold R9 in HR9.
   
   cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
   intro varfree.
   destruct varfree as (nvl,varfree).
   destruct varfree as (nvu,varfree).
   rewrite varfree.
   simpl.
   
   cut (exists (nnvl nnvu : list T) (np : list nat), fixAttr i v nvl nvu p = (nnvl,nnvu,np)).
   intro varfix.
   destruct varfix as (nnvl,varfix).
   destruct varfix as (nnvu,varfix).
   destruct varfix as (np,varfix).
   rewrite varfix.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature /\ length nnvl = nb_feature /\ length nnvu = nb_feature).
   intro L.
   destruct L as (Lnvl,L).
   destruct L as (Lnvu,L).
   destruct L as (Lnnvl,Lnnvu).


   (* cut de nnvl = vl et nnvu = vu *)
   cut (nnvl=vl).
   intro rnnvl.
   rewrite rnnvl.
   cut (nnvu=vu).
   intro rnnvu.
   rewrite rnnvu.
   apply HR2.

   (* nnvu = vu *)
   apply id_list_aux.
      split.
      (* length nnvu = length vu *)
      rewrite Lnnvu.
      symmetry.
      apply HR0.
      (* get égaux *)
      intros.
      cut (i0=i \/ i0 <> i).
      intro di.
      destruct di.
        (* i0=i *)
        cut (get i0 nnvu = get i0 v).
        intro rv.
        rewrite rv.
        cut (get i0 vu = get i0 v).
        intro rv_2.
        rewrite rv_2.
        reflexivity.
           (* get i0 vu = get i0 v *)
           apply (HR9 i0).
           lia.
           (* get i0 nnvu = get i0 v *)
           rewrite H0.
           apply (fix_i nb_feature i v nvl nvu p nnvl nnvu np).
           repeat split; [lia | lia | apply HR0 | apply Lnvl | apply Lnvu | apply varfix].
        (* i0 <> i *)
        cut (get i0 nnvu = get i0 nvu).
        intro rv.
        rewrite rv.
        cut (get i0 vu = get i0 nvu).
        intro rv_2.
        rewrite rv_2.
        reflexivity.
          (* get i0 vu = get i0 nvu *)
          apply (free_get nb_feature i i0 vl vu nvl nvu).
          repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
          (* get i0 nnvu = get i0 nvu *)
          symmetry.
          apply (fix_get nb_feature i i0 v nvl nvu p nnvl nnvu np).
          repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply Lnvl | apply Lnvu | apply varfix].
      lia.
   (* nnvl = vl *)
   apply id_list_aux.
   split.
   (* length nnvl = length vl *)
   rewrite Lnnvl.
   symmetry.
   apply HR0.
   (* get égaux *)
   intros.
   cut (i0=i \/ i0 <> i).
   intro di.
   destruct di.
     (* i0=i *)
     cut (get i0 nnvl = get i0 v).
     intro rv.
     rewrite rv.
     cut (get i0 vl = get i0 v).
     intro rv_2.
     rewrite rv_2.
     reflexivity.
        (* get i0 vl = get i0 v *)
        apply (HR9 i0).
        lia.
        (* get i0 nnvl = get i0 v *)
        rewrite H0.
        apply (fix_i nb_feature i v nvl nvu p nnvl nnvu np).
        repeat split; [lia | lia | apply HR0 | apply Lnvl | apply Lnvu | apply varfix].
     (* i0 <> i *)
     cut (get i0 nnvl = get i0 nvl).
     intro rv.
     rewrite rv.
     cut (get i0 vl = get i0 nvl).
     intro rv_2.
     rewrite rv_2.
     reflexivity.
       (* get i0 vl = get i0 nvl *)
       apply (free_get nb_feature i i0 vl vu nvl nvu).
       repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
       (* get i0 nnvl = get i0 nvl *)
       symmetry.
       apply (fix_get nb_feature i i0 v nvl nvu p nnvl nnvu np).
       repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply Lnvl | apply Lnvu | apply varfix].
   lia.

(* knnvl = k v *)

(* preuve des tailles *)
apply (preserveSizeCas2 i v vl vu nvl nvu nnvl nnvu p np).
repeat split ; [lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree | apply varfix].

(* preuve des cut avec les exists *)
destruct (fixAttr i v nvl nvu p).
destruct p0.
exists l0.
exists l1.
exists l.
reflexivity.

destruct (freeAttr i vl vu).
exists l.
exists l0.
reflexivity.
Qed.



Lemma preserveR3Cas2_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) <> (k nvu)) /\ 
  (R0 k i v vl vu p /\
  R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
  R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
  R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R3 k (i + 1) v
 (fst
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fixAttr i v (fst (freeAttr i vl vu))
       (snd (freeAttr i vl vu)) p)) .
Proof.
   intros.
   unfold R3.
   unfold R3 in H.
   lia.
Qed.
   

Lemma preserveR4_bisCas2_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) <> (k nvu)) /\ 
  (R0 k i v vl vu p /\
  R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
  R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
  R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R4_bis k (i + 1) v
 (fst
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fixAttr i v (fst (freeAttr i vl vu))
       (snd (freeAttr i vl vu)) p)) .
Proof.
   intros. 
   unfold R4_bis.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.
   unfold R4_bis in HR4.
   
   cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
   intro varfree.
   destruct varfree as (nvl,varfree).
   destruct varfree as (nvu,varfree).
   rewrite varfree.
   simpl.
   
   cut (exists (nnvl nnvu : list T) (np : list nat), fixAttr i v nvl nvu p = (nnvl,nnvu,np)).
   intro varfix.
   destruct varfix as (nnvl,varfix).
   destruct varfix as (nnvu,varfix).
   destruct varfix as (np,varfix).
   rewrite varfix.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature /\ length nnvl = nb_feature /\ length nnvu = nb_feature).
   intro L.
   destruct L as (Lnvl,L).
   destruct L as (Lnvu,L).
   destruct L as (Lnnvl,Lnnvu).

(* début de la preuve *)
  intros.
  cut (i<>j \/ i=j).
  intro di.
  destruct di.
  (* i<>j -> get j nnvl = get j vl + HR4 *)
  cut (get j nnvl = get j vl).
  intro rnnvl.
  rewrite rnnvl.
  cut (get j nnvu = get j vu).
  intro rnnvu.
  rewrite rnnvu.
  apply HR4.
  (*lia.*)
  apply (free_fix_id nb_feature i j v vl vu nvl nvu p nnvl nnvu np).
  repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree | apply varfix].
  
  apply (free_fix_id nb_feature i j v vl vu nvl nvu p nnvl nnvu np).
  repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree | apply varfix].
  (* i=j -> corps de fix*)
  right.
  rewrite <- H0.
  apply (fix_i nb_feature i v nvl nvu p nnvl nnvu np).
  repeat split; [lia | lia | apply HR0 | apply Lnvl | apply Lnvu | apply varfix].
  lia.

(* preuve des tailles *)
apply (preserveSizeCas2 i v vl vu nvl nvu nnvl nnvu p np).
repeat split ; [lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree | apply varfix].

(* preuve des cut avec les exists *)
destruct (fixAttr i v nvl nvu p).
destruct p0.
exists l0.
exists l1.
exists l.
reflexivity.

destruct (freeAttr i vl vu).
exists l.
exists l0.
reflexivity.
Qed.

Lemma R4_implies_R4_bis : forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
R4 k i v vl vu p -> R4_bis k i v vl vu p.
Proof.
   unfold R4.
   unfold R4_bis.
   intros.
   apply H.
Qed.

Lemma R4_bis_implies_R4 : forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
R0 k i v vl vu p /\ R4_bis k i v vl vu p -> R4 k i v vl vu p.
Proof.
   unfold R0.
   unfold R4.
   unfold R4_bis.
   intros.
   destruct H as (HR0, HR4_bis).
   cut ((j >= 0 /\ j < nb_feature) \/ j< 0 \/ j >= nb_feature).
   intro dj.
   destruct dj.
   (*j< 0 \/ j >= nb_feature *)
   apply HR4_bis.
   tauto.
   (* j <= 0 \/ j > nb_feature *)
   unfold get.
   simpl.
   right.
   cut (List.nth j vl Exception = Exception).
   intro rvl.
   rewrite rvl.
   cut (List.nth j vu Exception = Exception).
   intro rvu.
   rewrite rvu.
   cut (List.nth j v Exception = Exception).
   intro rv.
   rewrite rv.
   auto.
   apply  List.nth_overflow.
   lia.
   apply  List.nth_overflow.
   lia.
   apply  List.nth_overflow.
   lia.
   lia.
Qed.


Lemma preserveR4Cas2_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) <> (k nvu)) /\ 
  (R0 k i v vl vu p /\
  R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
  R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
  R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R4 k (i + 1) v
 (fst
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fixAttr i v (fst (freeAttr i vl vu))
       (snd (freeAttr i vl vu)) p)) .
Proof.
   intros.
   cut (
      R0 k (i + 1) v
      (fst
         (fst
            (fixAttr i v (fst (freeAttr i vl vu))
               (snd (freeAttr i vl vu)) p)))
      (snd
         (fst
            (fixAttr i v (fst (freeAttr i vl vu))
               (snd (freeAttr i vl vu)) p)))
      (snd
         (fixAttr i v (fst (freeAttr i vl vu))
            (snd (freeAttr i vl vu)) p))   
   /\
   R4_bis k (i + 1) v
   (fst
      (fst
         (fixAttr i v (fst (freeAttr i vl vu))
            (snd (freeAttr i vl vu)) p)))
   (snd
      (fst
         (fixAttr i v (fst (freeAttr i vl vu))
            (snd (freeAttr i vl vu)) p)))
   (snd
      (fixAttr i v (fst (freeAttr i vl vu))
         (snd (freeAttr i vl vu)) p))).
   apply R4_bis_implies_R4.
   split.
   apply preserveR0Cas2_AXp.
   apply H.

   cut (R4_bis k i v vl vu p).
   intro.
   apply preserveR4_bisCas2_AXp.
   tauto.
   apply R4_implies_R4_bis.
   apply H.
Qed.

Lemma preserveR5Cas2_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) <> (k nvu)) /\ 
  (R0 k i v vl vu p /\
  R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
  R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
  R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R5 k (i + 1) v
 (fst
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fixAttr i v (fst (freeAttr i vl vu))
       (snd (freeAttr i vl vu)) p)) .
Proof.
   intros. 
   unfold R5.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.
   unfold R5 in HR5.
   
   cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
   intro varfree.
   destruct varfree as (nvl,varfree).
   destruct varfree as (nvu,varfree).
   rewrite varfree.
   simpl.
   
   cut (exists (nnvl nnvu : list T) (np : list nat), fixAttr i v nvl nvu p = (nnvl,nnvu,np)).
   intro varfix.
   destruct varfix as (nnvl,varfix).
   destruct varfix as (nnvu,varfix).
   destruct varfix as (np,varfix).
   rewrite varfix.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature /\ length nnvl = nb_feature /\ length nnvu = nb_feature).
   intro L.
   destruct L as (Lnvl,L).
   destruct L as (Lnvu,L).
   destruct L as (Lnnvl,Lnnvu).

(* début de la preuve *)
intros.

cut (np = i::p).
intro rnp.
rewrite rnp.
simpl.
intro.
destruct H0.
lia.
cut (~ mem j p).
tauto.
apply (HR5 j).
lia.
apply (fix_p i v nvl nvu p nnvl nnvu np).
apply varfix.

(* preuve des tailles *)
apply (preserveSizeCas2 i v vl vu nvl nvu nnvl nnvu p np).
repeat split ; [lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree | apply varfix].

(* preuve des cut avec les exists *)
destruct (fixAttr i v nvl nvu p).
destruct p0.
exists l0.
exists l1.
exists l.
reflexivity.

destruct (freeAttr i vl vu).
exists l.
exists l0.
reflexivity.
Qed.


Lemma preserveR6Cas2_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) <> (k nvu)) /\ 
  (R0 k i v vl vu p /\
  R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
  R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
  R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R6 k (i + 1) v
 (fst
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fixAttr i v (fst (freeAttr i vl vu))
       (snd (freeAttr i vl vu)) p)) .
Proof.
   intros. 
   unfold R6.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.
   unfold R6 in HR6.
   
   cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
   intro varfree.
   destruct varfree as (nvl,varfree).
   destruct varfree as (nvu,varfree).
   rewrite varfree.
   simpl.
   
   cut (exists (nnvl nnvu : list T) (np : list nat), fixAttr i v nvl nvu p = (nnvl,nnvu,np)).
   intro varfix.
   destruct varfix as (nnvl,varfix).
   destruct varfix as (nnvu,varfix).
   destruct varfix as (np,varfix).
   rewrite varfix.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature /\ length nnvl = nb_feature /\ length nnvu = nb_feature).
   intro L.
   destruct L as (Lnvl,L).
   destruct L as (Lnvu,L).
   destruct L as (Lnnvl,Lnnvu).

(* début de la preuve *)
intros.
cut (j=i \/ mem j p).
intro d.
destruct d.
(* j=i *)
rewrite H0.
apply (fix_i nb_feature i v nvl nvu p nnvl nnvu np).
repeat split; [lia | lia | apply HR0 | apply Lnvl | apply Lnvu | apply varfix].

(* mem j p -> j<>i (contraposé de HR5) -> nnvlj = vlj (free_fix_id) -> nnvlj=vj (HR6) *)
(* D'abord des hypothèse liés à la contraposée de HR5 *)
cut (j<i /\ j >= 0 /\ j < nb_feature).
intro.
(* preuve en elle même*)
cut (j<>i).
intro difij.
cut (get j nnvl = get j vl).
intro r1.
rewrite r1.
cut (get j nnvu = get j vu).
intro r2.
rewrite r2.
apply HR6.
tauto.
(* get j nnvu = get j vu *)
apply (free_fix_id nb_feature i j v vl vu nvl nvu p nnvl nnvu np).
repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree | apply varfix].
(* get j nnvl = get j vl *)
apply (free_fix_id nb_feature i j v vl vu nvl nvu p nnvl nnvu np).
repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree | apply varfix].
(* j<>i *)
cut (j >= 0 /\ j < nb_feature).
lia.
unfold R5 in HR5.
lia.

(* contraposée de HR5 *)
cut (mem j p -> (j < i /\ j >= 0 /\ j < nb_feature)).
intro.
apply H1.
tauto.
cut (~~mem j p ->  ~(j >= i \/ j < 0 \/ j >= nb_feature)).
intros.
cut (~(j >= i \/ j < 0 \/ j >= nb_feature)).
lia.
apply H1.
tauto.
generalize (HR5 j).
apply contrapose.

(* j=i \/ mem j p*)
generalize H.
cut (np = i::p).
intro rnp.
rewrite rnp.
simpl.
auto.
apply (fix_p i v nvl nvu p nnvl nnvu np).
apply varfix.


(* preuve des tailles *)
apply (preserveSizeCas2 i v vl vu nvl nvu nnvl nnvu p np).
repeat split ; [lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree | apply varfix].

(* preuve des cut avec les exists *)
destruct (fixAttr i v nvl nvu p).
destruct p0.
exists l0.
exists l1.
exists l.
reflexivity.

destruct (freeAttr i vl vu).
exists l.
exists l0.
reflexivity.
Qed.


Lemma preserveR7Cas2_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) <> (k nvu)) /\ 
  (R0 k i v vl vu p /\
  R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
  R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
  R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R7 k (i + 1) v
 (fst
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fixAttr i v (fst (freeAttr i vl vu))
       (snd (freeAttr i vl vu)) p)) .
Proof.
   intros. 
   unfold R7.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.
   unfold R7 in HR7.
   
   cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
   intro varfree.
   destruct varfree as (nvl,varfree).
   destruct varfree as (nvu,varfree).
   rewrite varfree.
   simpl.
   
   cut (exists (nnvl nnvu : list T) (np : list nat), fixAttr i v nvl nvu p = (nnvl,nnvu,np)).
   intro varfix.
   destruct varfix as (nnvl,varfix).
   destruct varfix as (nnvu,varfix).
   destruct varfix as (np,varfix).
   rewrite varfix.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature /\ length nnvl = nb_feature /\ length nnvu = nb_feature).
   intro L.
   destruct L as (Lnvl,L).
   destruct L as (Lnvu,L).
   destruct L as (Lnnvl,Lnnvu).

(* début de la preuve *)
intros.
cut (j<>i /\ ~ mem j p).
intro.
cut (get j nnvl = get j vl).
intro rnnvl.
rewrite rnnvl.
cut (get j nnvu = get j vu).
intro rnnvu.
rewrite rnnvu.
apply (HR7 j).
generalize H.
cut (np=i::p).
intro rnp.
rewrite rnp.
simpl.
intros.
destruct H0.
destruct H1.
split.
tauto.
split.
lia.
tauto.
apply (fix_p i v nvl nvu p nnvl nnvu np).
apply varfix.
apply (free_fix_id nb_feature i j v vl vu nvl nvu p nnvl nnvu np).
repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree | apply varfix].
apply (free_fix_id nb_feature i j v vl vu nvl nvu p nnvl nnvu np).
repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree | apply varfix].
(* j <> i /\ ~ mem j p *)
destruct H.
destruct H0.
generalize H1.
cut (np = i::p).
intro rnp.
rewrite rnp.
simpl.
auto.
(*np = i :: p *)
apply (fix_p i v nvl nvu p nnvl nnvu np).
apply varfix.

(* preuve des tailles *)
apply (preserveSizeCas2 i v vl vu nvl nvu nnvl nnvu p np).
repeat split ; [lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree | apply varfix].

(* preuve des cut avec les exists *)
destruct (fixAttr i v nvl nvu p).
destruct p0.
exists l0.
exists l1.
exists l.
reflexivity.

destruct (freeAttr i vl vu).
exists l.
exists l0.
reflexivity.
Qed.


Lemma preserveR8Cas2_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) <> (k nvu)) /\ 
  (R0 k i v vl vu p /\
  R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
  R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
  R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R8 k (i + 1) v
 (fst
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fixAttr i v (fst (freeAttr i vl vu))
       (snd (freeAttr i vl vu)) p)) .
Proof.
   intros. 
   unfold R8.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.
   unfold R8 in HR8.
   
   cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
   intro varfree.
   destruct varfree as (nvl,varfree).
   destruct varfree as (nvu,varfree).
   rewrite varfree.
   simpl.
   
   cut (exists (nnvl nnvu : list T) (np : list nat), fixAttr i v nvl nvu p = (nnvl,nnvu,np)).
   intro varfix.
   destruct varfix as (nnvl,varfix).
   destruct varfix as (nnvu,varfix).
   destruct varfix as (np,varfix).
   rewrite varfix.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature /\ length nnvl = nb_feature /\ length nnvu = nb_feature).
   intro L.
   destruct L as (Lnvl,L).
   destruct L as (Lnvu,L).
   destruct L as (Lnnvl,Lnnvu).

(* début de la preuve *)
cut (np=i::p).
intro rnp.
rewrite rnp.
simpl.
split.
(* forall e : nat, mem e p -> i > e *)
intros.
(* D'abord des hypothèse liés à la contraposée de HR5 *)
cut (e<i /\ e >= 0 /\ e < nb_feature).
intro.
tauto.
(* contraposée de HR5 *)
cut (mem e p -> (e < i /\ e >= 0 /\ e < nb_feature)).
intro CHR5.
apply CHR5.
tauto.
cut (~~mem e p ->  ~(e >= i \/ e < 0 \/ e >= nb_feature)).
intros.
cut (~(e >= i \/ e < 0 \/ e >= nb_feature)).
lia.
apply H0.
tauto.
unfold R5 in HR5.
generalize (HR5 e).
apply contrapose.
(* is_sorted p *)
tauto.
(* np = i :: p *)
apply (fix_p i v nvl nvu p nnvl nnvu np).
apply varfix.

(* preuve des tailles *)
apply (preserveSizeCas2 i v vl vu nvl nvu nnvl nnvu p np).
repeat split ; [lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree | apply varfix].

(* preuve des cut avec les exists *)
destruct (fixAttr i v nvl nvu p).
destruct p0.
exists l0.
exists l1.
exists l.
reflexivity.

destruct (freeAttr i vl vu).
exists l.
exists l0.
reflexivity.
Qed.


Lemma preserveR9Cas2_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) <> (k nvu)) /\ 
  (R0 k i v vl vu p /\
  R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
  R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
  R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R9 k (i + 1) v
 (fst
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fixAttr i v (fst (freeAttr i vl vu))
       (snd (freeAttr i vl vu)) p)) .
Proof.
   intros. 
   unfold R9.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.
   unfold R9 in HR9.
   
   cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
   intro varfree.
   destruct varfree as (nvl,varfree).
   destruct varfree as (nvu,varfree).
   rewrite varfree.
   simpl.
   
   cut (exists (nnvl nnvu : list T) (np : list nat), fixAttr i v nvl nvu p = (nnvl,nnvu,np)).
   intro varfix.
   destruct varfix as (nnvl,varfix).
   destruct varfix as (nnvu,varfix).
   destruct varfix as (np,varfix).
   rewrite varfix.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature /\ length nnvl = nb_feature /\ length nnvu = nb_feature).
   intro L.
   destruct L as (Lnvl,L).
   destruct L as (Lnvu,L).
   destruct L as (Lnnvl,Lnnvu).

(* début de la preuve *)
intros.
cut (i<>j).
intro.
cut (get j nnvl = get j vl).
intro rnnvl.
rewrite rnnvl.
cut (get j nnvu = get j vu).
intro rnnvu.
rewrite rnnvu.
apply HR9.
lia.
apply (free_fix_id nb_feature i j v vl vu nvl nvu p nnvl nnvu np).
repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree | apply varfix].
apply (free_fix_id nb_feature i j v vl vu nvl nvu p nnvl nnvu np).
repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree | apply varfix].

(* i<>j *)
lia.


(* preuve des tailles *)
apply (preserveSizeCas2 i v vl vu nvl nvu nnvl nnvu p np).
repeat split ; [lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree | apply varfix].

(* preuve des cut avec les exists *)
destruct (fixAttr i v nvl nvu p).
destruct p0.
exists l0.
exists l1.
exists l.
reflexivity.

destruct (freeAttr i vl vu).
exists l.
exists l0.
reflexivity.
Qed.

(* lambda / nu pour feature <= à i et v pour >i *)
Fixpoint ln_i_v_aux (ind:nat) (i:nat) (s:nat) (v : list T) (ln : nat -> T) (p : list nat): list T  :=
   match s with
   | 0 => nil
   | S smoins1 => if (ind <=? i)
          then if (mem_nat ind p)
               then (get ind v)::(ln_i_v_aux (ind+1) i smoins1 v ln p)
               else (ln ind)::(ln_i_v_aux (ind+1) i smoins1 v ln p)
          else (get ind v)::(ln_i_v_aux (ind+1) i smoins1 v ln p)
   end.

Definition ln_i_v (i:nat) (v : list T) (ln : nat -> T)  (p : list nat) : list T  := ln_i_v_aux 0 i (List.length v) v ln p.



Lemma get_sup_i_ln_i_v_aux : forall (s ind i j :nat) (v : list T) (ln : nat -> T)  (p : list nat),
ind > i /\ j>=0 /\ j <s -> get j (ln_i_v_aux ind i s v ln p) = get (ind+j) v.
Proof.
induction s.
(* cas de base -> pas possible *)
lia.
(* cas général *)
intros.
simpl.
cut (ind <=? i = false).
intro rt.
rewrite rt.
destruct j.
(* j = 0 *)
unfold get.
simpl.
cut (ind+0 = ind).
intro r0.
rewrite r0.
reflexivity.
lia.
(* j<>0 *)
unfold get.
simpl.
cut (ind + S j = ind + 1 + j).
intro r1.
rewrite r1.
apply (IHs (ind+1) i j v).
lia.
lia.
cut (not (ind <=i)).
rewrite <- Nat.leb_le.
destruct ((ind <=? i)).
tauto.
tauto.
lia.
Qed.


Lemma get_sup_i_ln_i_v_aux_2 : forall (s ind i j :nat) (v : list T) (ln : nat -> T)  (p : list nat),
ind <= i /\ j<s/\  j>(i-ind) -> get j (ln_i_v_aux ind i s v ln p) = get (ind+j) v.
Proof.
  induction s.
  (* cas de base -> pas possible *)
  lia.
  (* cas général *)
  intros.
  simpl.
  cut (ind <=? i = true).
  intro rt.
  rewrite rt.
  destruct j.
  (* j = 0 -> pas possible *)
  lia.
  (* j<>0 *)
  unfold get.
  simpl.
  cut (ind + S j = ind + 1 + j).
  intro r1.
  rewrite r1.
  cut (ind+1 <=i \/ ind+1>i).
  intro di.
  destruct di.
  (* ind + 1 <= i *)
  destruct (mem_nat ind p).
  simpl.
  apply (IHs (ind+1) i j v ln p). 
  lia.
  apply (IHs (ind+1) i j v ln p). 
  lia.
  (* ind + 1 > i *)
  destruct (mem_nat ind p).
  simpl.
  apply get_sup_i_ln_i_v_aux.
  lia.
  simpl.
  apply get_sup_i_ln_i_v_aux.
  lia.
  lia.
  lia.
  cut (ind <=i).
  rewrite <- Nat.leb_le.
  tauto.
  lia.
Qed.

Lemma get_sup_i_ln_i_v : forall (ind:nat) (i:nat) (v : list T) (ln : nat -> T) (p : list nat),
ind >=0 /\ ind <(List.length v)  /\ ind > i -> get ind (ln_i_v i v ln p) = get ind v.
Proof.
   intros.
   unfold ln_i_v.
   apply (get_sup_i_ln_i_v_aux_2 (List.length v) 0 i ind v ln p).
   lia.
Qed.


Lemma get_inf_mem_i_ln_i_v_aux : forall (s ind i j :nat) (v : list T) (ln : nat -> T) (p : list nat),
ind <= i /\ j>=0 /\ j <s /\ j <= (i-ind) /\ mem (ind+j) p-> get j (ln_i_v_aux ind i s v ln p) = get (ind+j) v.
Proof.
  induction s.
  (* cas de base -> pas possible *)
  lia.
  (* cas général *)
  intros.
  simpl.
  cut (ind <=? i = true).
  intro rt.
  rewrite rt.
  destruct j.
  (* j = 0 *)
  unfold get.
  simpl.
  cut (ind+0 = ind).
  intro r0.
  rewrite r0.
  cut (mem_nat ind p=true \/ mem_nat ind p=false).
  intro d.
  destruct d.
  rewrite H0.
  reflexivity.
  cut False.
  tauto.
  destruct H.
  destruct H1.
  destruct H2.
  destruct H3.
  rewrite r0 in H4.
  generalize H4.
  rewrite <- mem_coherent.
  rewrite H0.
  discriminate.
  destruct (mem_nat ind p).
  auto.
  auto.
  lia.
  (* j<>0 *)
  unfold get.
  cut (mem_nat ind p=true \/ mem_nat ind p=false).
  intro d.
  destruct d.
  rewrite H0.
  simpl.
  cut (ind + S j = ind + 1 + j).
  intro r1.
  rewrite r1.
  apply (IHs (ind+1) i j v ln p).
  rewrite r1 in H.
  repeat split ;[lia|lia|lia|lia|apply H].
  lia.
  rewrite H0.
  simpl.
  cut (ind + S j = ind + 1 + j).
  intro r1.
  rewrite r1.
  apply (IHs (ind+1) i j v ln p).
  rewrite r1 in H.
  repeat split ;[lia|lia|lia|lia|apply H].
  lia.
  destruct (mem_nat ind p).
  auto.
  auto.
  cut (ind <= i).
  apply Nat.leb_le.
  apply H.
Qed.

Lemma get_inf_mem_i_ln_i_v : forall (ind:nat) (i:nat) (v : list T) (ln : nat -> T) (p : list nat),
ind >=0 /\ ind <(List.length v)  /\ ind <= i /\ mem ind p -> get ind (ln_i_v i v ln p) = get ind v.
Proof.
   intros.
   unfold ln_i_v.
   apply (get_inf_mem_i_ln_i_v_aux (List.length v) 0 i ind v ln p).
   cut (0+ind = ind).
   intro rind.
   repeat split ; [lia|lia|lia|lia|apply H].
   lia.
Qed.


Lemma get_inf_not_mem_i_ln_i_v_aux : forall (s ind i j :nat) (v : list T) (ln : nat -> T) (p : list nat),
ind <= i /\ j>=0 /\ j <s /\ j <= (i-ind) /\ ~mem (ind+j) p-> get j (ln_i_v_aux ind i s v ln p) = ln (ind+j).
Proof.
  induction s.
  (* cas de base -> pas possible *)
  lia.
  (* cas général *)
  intros.
  simpl.
  cut (ind <=? i = true).
  intro rt.
  rewrite rt.
  destruct j.
  (* j = 0 *)
  unfold get.
  simpl.
  cut (ind+0 = ind).
  intro r0.
  rewrite r0.
  cut (mem_nat ind p=true \/ mem_nat ind p=false).
  intro d.
  destruct d.

  cut False.
  tauto.
  destruct H.
  destruct H1.
  destruct H2.
  destruct H3.
  rewrite r0 in H4.
  generalize H4.
  rewrite <- mem_coherent.
  rewrite H0.
  auto.

  rewrite H0.
  reflexivity.

  destruct (mem_nat ind p).
  auto.
  auto.

  lia.
  (* j<>0 *)
  unfold get.
  cut (mem_nat ind p=true \/ mem_nat ind p=false).
  intro d.
  destruct d.
  rewrite H0.
  simpl.
  cut (ind + S j = ind + 1 + j).
  intro r1.
  rewrite r1.
  apply (IHs (ind+1) i j v ln p).
  rewrite r1 in H.
  repeat split ;[lia|lia|lia|lia|apply H].
  lia.
  rewrite H0.
  simpl.
  cut (ind + S j = ind + 1 + j).
  intro r1.
  rewrite r1.
  apply (IHs (ind+1) i j v ln p).
  rewrite r1 in H.
  repeat split ;[lia|lia|lia|lia|apply H].
  lia.
  destruct (mem_nat ind p).
  auto.
  auto.
  cut (ind <= i).
  apply Nat.leb_le.
  apply H.
Qed.


Lemma get_inf_not_mem_i_ln_i_v : forall (ind:nat) (i:nat) (v : list T) (ln : nat -> T) (p : list nat),
ind >=0 /\ ind <(List.length v)  /\ ind <= i /\ ~ mem ind p -> get ind (ln_i_v i v ln p) = ln ind.
Proof.
   intros.
   unfold ln_i_v.
   apply (get_inf_not_mem_i_ln_i_v_aux (List.length v) 0 i ind v ln p).
   cut (0+ind = ind).
   intro rind.
   repeat split ; [lia|lia|lia|lia|apply H].
   lia.
Qed.

Lemma length_ln_i_v_aux : forall (s ind i :nat) (v : list T) (ln : nat -> T) (p : list nat), length (ln_i_v_aux ind i s v ln p) = s.
Proof.
   induction s.
   simpl.
   auto.
   intros.
   simpl.
   cut (ind <=? i=true \/ ind <=? i=false).
   intro c.
   destruct c.
   rewrite H.
   cut (mem_nat ind p=true \/ mem_nat ind p=false).
   intro d.
   destruct d.
   rewrite H0.
   simpl.
   generalize (IHs (ind+1) i v ln p).
   auto.
   rewrite H0.
   simpl.
   generalize (IHs (ind+1) i v ln p).
   auto.
   destruct (mem_nat ind p).
   auto.
   auto.
   rewrite H.
   simpl.
   generalize (IHs (ind+1) i v).
   auto.
   cut (ind <= i \/ ind > i).
   intro c.
   destruct c.
   left.
   apply Nat.leb_le.
   apply H.
   right.
   cut (not (ind <=i)).
   rewrite <- Nat.leb_le.
   destruct ((ind <=? i)).
   tauto.
   tauto.
   lia.
   lia.
Qed.

Lemma length_ln_i_v : forall (i :nat) (v : list T) (ln : nat -> T) (p : list nat), length (ln_i_v i v ln p) = (length v).
Proof.
   intros.
   unfold ln_i_v.
   apply length_ln_i_v_aux.
Qed.


Lemma preserveR10Cas2_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) <> (k nvu)) /\ 
  (R0 k i v vl vu p /\
  R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
  R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
  R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R10 k (i + 1) v
 (fst
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fst
       (fixAttr i v (fst (freeAttr i vl vu))
          (snd (freeAttr i vl vu)) p)))
 (snd
    (fixAttr i v (fst (freeAttr i vl vu))
       (snd (freeAttr i vl vu)) p)) .
Proof.
   intros. 
   unfold R10.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.
   unfold R5 in HR5.
   unfold R6 in HR6.
   unfold R7 in HR7.
   unfold R9 in HR9.
   unfold R10 in HR10.
   
   cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
   intro varfree.
   destruct varfree as (nvl,varfree).
   destruct varfree as (nvu,varfree).
   rewrite varfree.
   simpl.
   
   cut (exists (nnvl nnvu : list T) (np : list nat), fixAttr i v nvl nvu p = (nnvl,nnvu,np)).
   intro varfix.
   destruct varfix as (nnvl,varfix).
   destruct varfix as (nnvu,varfix).
   destruct varfix as (np,varfix).
   rewrite varfix.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature /\ length nnvl = nb_feature /\ length nnvu = nb_feature).
   intro L.
   destruct L as (Lnvl,L).
   destruct L as (Lnvu,L).
   destruct L as (Lnnvl,Lnnvu).

(* début de la preuve *)
cut (np = i::p).
intro rnp.
rewrite rnp.

intros.

destruct p. (* car si p est vide pas possible d'utiliser la précondition *)
   (* p=nil *)
   cut (x1=nil).
   intro defx1.
   rewrite defx1.
   cut (x=i).
   intro defxi.
   rewrite defxi.
   simpl.

   (* lambda / nu pour feature <= à i et v pour >i *)
   exists (ln_i_v i v lambda nil).
   exists (ln_i_v i v nu nil).
   split.
   rewrite (length_ln_i_v).
   apply HR0.
   split.
   rewrite (length_ln_i_v).
   apply HR0.
   split.
   intros.
   cut (j>i \/ j<=i).
   intro dj.
   destruct dj.
   (* j > 1 *)
   left.
   split.
   auto.
   split.
   apply get_sup_i_ln_i_v.
   lia.
   apply get_sup_i_ln_i_v.
   lia.
   (* j <= i *)
   right.
   split.
   lia.
   split.
   apply get_inf_not_mem_i_ln_i_v.
   repeat split ; [lia|lia|lia|simpl;auto].
   apply get_inf_not_mem_i_ln_i_v.
   repeat split ; [lia|lia|lia|simpl;auto].

   (* j > i \/ j <= i  *)
   lia.

   (* k (lambda_i_v i v) <> k (nu_i_v i v) *)
   generalize Hdif_k.
   rewrite (surjective_pairing (freeAttr i vl vu)).
   rewrite varfree.
   simpl.

   cut (nvl = ln_i_v i v lambda nil /\ nvu = ln_i_v i v nu nil).
   intro defnvlu.
   destruct defnvlu as (defnlv,defnvu).
   rewrite defnlv.
   rewrite defnvu.
   auto.
   
   cut (nvl = ln_i_v i vl lambda nil /\ nvu = ln_i_v i vu nu nil).
   intro defnvlubis.
   destruct defnvlubis as (defnvl2,defnvu2).
   rewrite defnvl2.
   rewrite defnvu2.

   split.
   (* lambda_i_v i vl = lambda_i_v i v *)
   apply id_list.
   split.
   rewrite (length_ln_i_v i vl lambda nil).
   rewrite (length_ln_i_v i v lambda nil).
   destruct HR0 as (HR0v, HR0).
   destruct HR0 as (HR0vl, HR0vu).
   rewrite HR0vl.
   rewrite HR0v.
   auto.
   intros.
   cut (i0<= i \/ i0>i).
   intro di0.
   destruct di0.
   (* i0 <= i *)
   rewrite (get_inf_not_mem_i_ln_i_v i0 i v lambda nil).
   rewrite (get_inf_not_mem_i_ln_i_v i0 i vl lambda nil).
   auto.
   repeat split ; [lia|lia|lia|simpl;auto].
   repeat split ; [lia|lia|lia|simpl;auto].
   (* i0 > i *)
   rewrite (get_sup_i_ln_i_v i0 i v lambda nil).
   rewrite (get_sup_i_ln_i_v i0 i vl lambda nil).
   apply HR9.
   rewrite (length_ln_i_v i vl lambda nil) in H0.
   lia.
   rewrite (length_ln_i_v i vl lambda nil) in H0.
   lia.
   rewrite (length_ln_i_v i vl lambda nil) in H0.
   lia.
   lia.
   auto.
   (* nu_i_v i vl = nu_i_v i v *)
   apply id_list.
   split.
   rewrite (length_ln_i_v i vu nu nil).
   rewrite (length_ln_i_v i v nu nil).
   destruct HR0 as (HR0v, HR0).
   destruct HR0 as (HR0vl, HR0vu).
   rewrite HR0vu.
   rewrite HR0v.
   auto.
   intros.
   cut (i0<= i \/ i0>i).
   intro di0.
   destruct di0.
   (* i0 <= i *)
   rewrite (get_inf_not_mem_i_ln_i_v i0 i v nu nil).
   rewrite (get_inf_not_mem_i_ln_i_v i0 i vu nu nil).
   auto.
   repeat split ; [lia|lia|lia|simpl;auto].
   repeat split ; [lia|lia|lia|simpl;auto].
   (* i0 > i *)
   rewrite (get_sup_i_ln_i_v i0 i v nu nil).
   rewrite (get_sup_i_ln_i_v i0 i vu nu nil).
   apply HR9.
   rewrite (length_ln_i_v i vu nu nil) in H0.
   lia.
   rewrite (length_ln_i_v i vu nu nil) in H0.
   lia.
   rewrite (length_ln_i_v i vu nu nil) in H0.
   lia.
   lia.
   auto.

   split.
   (* nvl = lambda_i_v i vl *)
   apply id_list.
   split.
   rewrite (length_ln_i_v i vl lambda nil).
   destruct HR0 as (HR0v, HR0).
   destruct HR0 as (HR0vl, HR0vu).
   rewrite HR0vl.
   rewrite Lnvl.
   auto.
   intros.
   cut (i0< i \/ i0=i \/ i0>i).
   intro di0.
   unfold R5 in HR5.
   destruct di0.
   (* i0 < i *)
   rewrite (get_inf_not_mem_i_ln_i_v i0 i vl lambda nil).
   cut (get i0 nvl = get i0 vl).
   intro i0nvl.
   rewrite i0nvl.
   apply HR7.
   simpl.
   lia.
   symmetry.
   apply (free_get nb_feature i i0 vl vu nvl nvu).
   repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
   repeat split ; [lia|lia|lia|simpl;auto].
   destruct H1.
   (* i0 = i *)
   rewrite H1.
   rewrite (get_inf_not_mem_i_ln_i_v i i vl lambda nil).
   apply (free_i nb_feature i vl vu nvl nvu).
   repeat split; [lia | lia | lia | apply varfree | apply HR0 | apply HR0].
   repeat split ; [lia|lia|lia|simpl;auto].
   (* i0 > i *)
   rewrite (get_sup_i_ln_i_v i0 i vl lambda nil).
   symmetry.
   apply (free_get nb_feature i i0 vl vu nvl nvu).
   repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
   lia.
   lia.
   (* nvu = nu_i_v i vu *)
   apply id_list.
   split.
   rewrite (length_ln_i_v i vu nu nil).
   destruct HR0 as (HR0v, HR0).
   destruct HR0 as (HR0vl, HR0vu).
   rewrite HR0vu.
   rewrite Lnvu.
   auto.
   intros.
   cut (i0< i \/ i0=i \/ i0>i).
   intro di0.
   destruct di0.
   (* i0 < i *)
   rewrite (get_inf_not_mem_i_ln_i_v i0 i vu nu nil).
   cut (get i0 nvu = get i0 vu).
   intro i0nvl.
   rewrite i0nvl.
   apply HR7.
   simpl.
   lia.
   symmetry.
   apply (free_get nb_feature i i0 vl vu nvl nvu).
   repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
   repeat split ; [lia|lia|lia|simpl;auto].
   destruct H1.
   (* i0 = i *)
   rewrite H1.
   rewrite (get_inf_not_mem_i_ln_i_v i i vu nu nil).
   apply (free_i nb_feature i vl vu nvl nvu).
   repeat split; [lia | lia | lia | apply varfree | apply HR0 | apply HR0].
   repeat split ; [lia|lia|lia|simpl;auto].
   (* i0 > i *)
   rewrite (get_sup_i_ln_i_v i0 i vu nu).
   symmetry.
   apply (free_get nb_feature i i0 vl vu nvl nvu).
   repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
   lia.
   lia.

   (* x=i *)
   apply (destruct_list_1elt x i x0 x1).
   auto.

   (* x1 = nil *)
   apply (destruct_list_1elt x i x0 x1).
   auto.

(* p<>nil -> on peut appliquer la précondition *)

destruct x0.
(* x0 = nil
-> i=x
-> x1=n::p

précondition sur nil n p
*)

(* x0=nil -> x=i *)
cut (x=i).
intro defxx.
rewrite defxx.
cut (x1 = n::p).
intro defxx1.
rewrite defxx1.

(* lambda / nu pour feature <= à i et pas dans p
v si <i et dans p
v pour >i *)

exists (ln_i_v i v lambda (n :: p)).
exists (ln_i_v i v nu (n :: p)).
split.
destruct HR0.
rewrite <- H0.
apply (length_ln_i_v i v lambda (n::p)).
split.
destruct HR0.
rewrite <- H0.
apply (length_ln_i_v i v nu (n::p)).
split.
(*forall j : nat,
j >= 0 /\ j < nb_feature ->
(mem j (n :: p) \/ j > i) /\
get j (ln_i_v i v lambda (n :: p)) = get j v /\
get j (ln_i_v i v nu (n :: p)) = get j v \/
~ (mem j (n :: p) \/ j > i) /\
get j (ln_i_v i v lambda (n :: p)) = lambda j /\
get j (ln_i_v i v nu (n :: p)) = nu j*)
intros.
cut (mem j (n :: p) \/ ~mem j (n :: p)).
intro d.
destruct d.
  (* mem j (n :: p) *)
   cut (j<i).
   intro j_inf_i.
   left.
   split.
   left.
   apply H1.
   split.
   apply (get_inf_mem_i_ln_i_v j i v lambda (n::p)).
   repeat split; [lia|lia|lia|apply H1].
   apply (get_inf_mem_i_ln_i_v j i v nu (n::p)).
   repeat split; [lia|lia|lia|apply H1].
     (* j<i *)
     cut (~(j >= i \/ j < 0 \/ j >= nb_feature)).
     lia.
     cut (~ ~ (mem j (n :: p))).
     generalize (HR5 j).
     apply contrapose.
     tauto.
   (* ~ mem j (n :: p) *)
   cut (j <= i \/ j>i).
   intro dj.
   destruct dj.
      (* j<= i *)
      right.
      split.
      unfold not.
      intro.
      destruct H3.
      tauto.
      lia.
      split.
      apply (get_inf_not_mem_i_ln_i_v j i v lambda (n::p)).
      repeat split; [lia|lia|lia|apply H1].
      apply (get_inf_not_mem_i_ln_i_v j i v nu (n::p)).
      repeat split; [lia|lia|lia|apply H1].
      (* j>i *)
      left.
      split.
      right.
      apply H2.
      split.
      apply (get_sup_i_ln_i_v j i v lambda (n::p)).
      lia.
      apply (get_sup_i_ln_i_v j i v nu (n::p)).
      lia.
      lia.
(* mem j (n :: p) \/ ~ mem j (n :: p) *)
tauto.
(* k (ln_i_v i v lambda (n :: p)) <> k (ln_i_v i v nu (n :: p)) *)
generalize Hdif_k.
rewrite (surjective_pairing (freeAttr i vl vu)).
rewrite varfree.
simpl.

cut (nvl = ln_i_v i v lambda (n::p) /\ nvu = ln_i_v i v nu (n::p)).
intro defnvlu.
destruct defnvlu as (defnlv,defnvu).
rewrite defnlv.
rewrite defnvu.
auto.

split.
(* nvl = ln_i_v i v lambda (n :: p) *)
apply id_list.
split.
  (* length nvl = length (ln_i_v i v lambda (n :: p)) *)
  rewrite (length_ln_i_v i v lambda (n :: p)).
  destruct HR0 as (HR0v, HR0).
  destruct HR0 as (HR0vl, HR0vu).
  rewrite HR0v.
  rewrite Lnvl.
  reflexivity.
  
  intros.
  (* get i0 nvl = get i0 (ln_i_v i v lambda (n :: p)) *)
  cut (i0 < i \/ i0=i \/ i0 > i).
  intro di0.
  destruct di0.
    (* i0 < i *)
    cut (mem i0 (n::p) \/ ~ mem i0 (n::p)).
    intro dmem.
    destruct dmem.
      (* mem i0 (n :: p) *)
      rewrite (get_inf_mem_i_ln_i_v i0 i v lambda (n::p)).
      transitivity ( get i0 vl).
      symmetry.
      apply (free_get nb_feature i i0 vl vu nvl nvu).
      repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
      apply HR6.
      apply H2.
      repeat split; [lia|lia|lia|apply H2].
      (* ~ mem i0 (n :: p) *)
      rewrite (get_inf_not_mem_i_ln_i_v i0 i v lambda (n::p)).
      transitivity ( get i0 vl).
      symmetry.
      apply (free_get nb_feature i i0 vl vu nvl nvu).
      repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
      apply HR7.
      repeat split; [lia|lia|apply H2].
      repeat split; [lia|lia|lia|apply H2].
      (* mem i0 (n :: p) \/ ~ mem i0 (n :: p) *)
      tauto.
     destruct H1.
    (* i0 = i *)
    rewrite H1.
    rewrite (get_inf_not_mem_i_ln_i_v i i v lambda (n::p)).
    apply (free_i nb_feature i vl vu nvl nvu).
    repeat split; [lia | lia | lia | apply varfree | apply HR0 | apply HR0].
    repeat split ; [lia|lia|lia|apply (HR5 i)].
    lia.
    (* i0 > i *)
    rewrite (get_sup_i_ln_i_v i0 i v lambda (n::p)).
    transitivity ( get i0 vl).
    symmetry.
    apply (free_get nb_feature i i0 vl vu nvl nvu).
    repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
    apply HR9.
    lia.
    lia.
   (* i0 < i \/ i0 = i \/ i0 > i *)
   lia.
   (* nvu = ln_i_v i v nu (n :: p) *)
  apply id_list.
  split.
  (* length nvu = length (ln_i_v i v nu (n :: p)) *)
  rewrite (length_ln_i_v i v nu (n :: p)).
  destruct HR0 as (HR0v, HR0).
  destruct HR0 as (HR0vl, HR0vu).
  rewrite HR0v.
  rewrite Lnvu.
  reflexivity.
  
  intros.
  (* get i0 nvu = get i0 (ln_i_v i v nu (n :: p)) *)
  cut (i0 < i \/ i0=i \/ i0 > i).
  intro di0.
  destruct di0.
    (* i0 < i *)
    cut (mem i0 (n::p) \/ ~ mem i0 (n::p)).
    intro dmem.
    destruct dmem.
      (* mem i0 (n :: p) *)
      rewrite (get_inf_mem_i_ln_i_v i0 i v nu (n::p)).
      transitivity ( get i0 vu).
      symmetry.
      apply (free_get nb_feature i i0 vl vu nvl nvu).
      repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
      apply HR6.
      apply H2.
      repeat split; [lia|lia|lia|apply H2].
      (* ~ mem i0 (n :: p) *)
      rewrite (get_inf_not_mem_i_ln_i_v i0 i v nu (n::p)).
      transitivity ( get i0 vu).
      symmetry.
      apply (free_get nb_feature i i0 vl vu nvl nvu).
      repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
      apply HR7.
      repeat split; [lia|lia|apply H2].
      repeat split; [lia|lia|lia|apply H2].
      (* mem i0 (n :: p) \/ ~ mem i0 (n :: p) *)
      tauto.
     destruct H1.
    (* i0 = i *)
    rewrite H1.
    rewrite (get_inf_not_mem_i_ln_i_v i i v nu (n::p)).
    apply (free_i nb_feature i vl vu nvl nvu).
    repeat split; [lia | lia | lia | apply varfree | apply HR0 | apply HR0].
    repeat split ; [lia|lia|lia|apply (HR5 i)].
    lia.
    (* i0 > i *)
    rewrite (get_sup_i_ln_i_v i0 i v nu (n::p)).
    transitivity ( get i0 vu).
    symmetry.
    apply (free_get nb_feature i i0 vl vu nvl nvu).
    repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
    apply HR9.
    lia.
    lia.
   (* i0 < i \/ i0 = i \/ i0 > i *)
   lia.

(* x1 = n :: p *)
cut (nil ++ x :: x1 = i :: n :: p).
apply (destruct_list_debutvide x i (n::p) x1).
generalize H.
auto.
cut (nil ++ x :: x1 = i :: n :: p).
apply (destruct_list_debutvide x i (n::p) x1).
generalize H.
auto.

(* x0 <>nil -> on peut appliquer la précondition  *)
apply (HR10 x x0 x1).
injection H.
tauto.

(* np = i :: p *)
apply (fix_p i v nvl nvu p nnvl nnvu np).
apply varfix.

(* preuve des tailles *)
apply (preserveSizeCas2 i v vl vu nvl nvu nnvl nnvu p np).
repeat split ; [lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree | apply varfix].

(* preuve des cut avec les exists *)
destruct (fixAttr i v nvl nvu p).
destruct p0.
exists l0.
exists l1.
exists l.
reflexivity.

destruct (freeAttr i vl vu).
exists l.
exists l0.
reflexivity.
Qed.


Lemma preserveSizeCas3 : forall (i:nat) (v vl vu nvl nvu : list T),
   i>= 0 /\ i < nb_feature  
/\ List.length v = nb_feature
/\ List.length vl = nb_feature
/\ List.length vu = nb_feature
/\ freeAttr i vl vu = (nvl, nvu)
-> List.length nvl = nb_feature
/\ List.length nvu = nb_feature.
Proof.
   intros.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Lv,H).
   destruct H as (Lvl,H).
   destruct H as (Lvu,Hfree).

   split.

   (* Lnvl*)
   cut (nvl = fst (freeAttr i vl vu)).
   intro rvl.
   rewrite rvl.
   apply (free_size nb_feature i vl vu).
   split. apply Lvl. apply Lvu.
   rewrite Hfree. simpl. reflexivity.

   (* Lnvu *)
   cut (nvu = snd (freeAttr i vl vu)).
   intro rvu.
   rewrite rvu.
   apply (free_size nb_feature i vl vu).
   split. apply Lvl. apply Lvu.
   rewrite Hfree. simpl. reflexivity.
Qed.



Lemma preserveSize_CXp : forall (i:nat) (v vl vu nvl nvu : list T) (p np : list nat),
   i>= 0 /\ i < nb_feature  
/\ List.length v = nb_feature
/\ List.length vl = nb_feature
/\ List.length vu = nb_feature
/\ fixAttr i v vl vu p = (nvl, nvu,np)
-> List.length nvl = nb_feature
/\ List.length nvu = nb_feature.
Proof.
   intros.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Lv,H).
   destruct H as (Lvl,H).
   destruct H as (Lvu,Hfree).

   split.

   (* Lnvl*)
   cut (nvl = fst (fst (fixAttr i v vl vu p))).
   intro rvl.
   rewrite rvl.
   apply (fix_size nb_feature i v vl vu p).
   split. apply Hi_inf. split. apply Hi_sup. split. apply Lv. split. apply Lvl. apply Lvu.
   rewrite Hfree. simpl. reflexivity.

   (* Lnvu *)
   cut (nvu = snd (fst (fixAttr i v vl vu p))).
   intro rvu.
   rewrite rvu.
   apply (fix_size nb_feature i v vl vu p).
   split. apply Hi_inf. split. apply Hi_sup. split. apply Lv. split. apply Lvl. apply Lvu.
   rewrite Hfree. simpl. reflexivity.
Qed.




Lemma preserveR0Cas3_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) = (k nvu)) /\ 
  (R0 k i v vl vu p /\
  R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
  R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
  R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R0 k (i + 1) v (fst (freeAttr i vl vu)) (snd (freeAttr i vl vu)) p.
 Proof.
   intros. 
   unfold R0.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.
   
   cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
   intro varfree.
   destruct varfree as (nvl,varfree).
   destruct varfree as (nvu,varfree).
   rewrite varfree.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature).
   intro L.
   destruct L as (Lnvl,Lnvu).

   (* début de la preuve *)
   repeat split; [apply HR0| apply Lnvl|apply Lnvu].
   
   (* preuve des tailles *)
   apply (preserveSizeCas3 i v vl vu nvl nvu ).
   repeat split ; [lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree].
   
   (* preuve du cut avec les exists *)
   destruct (freeAttr i vl vu).
   exists l.
   exists l0.
   reflexivity.
Qed.

Lemma preserveR1Cas3_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) = (k nvu)) /\ 
  (R0 k i v vl vu p /\
  R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
  R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
  R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R1 k (i + 1) v (fst (freeAttr i vl vu)) (snd (freeAttr i vl vu)) p.
Proof.
   intros. 
   unfold R1.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.
   unfold R1 in HR1.
   
   cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
   intro varfree.
   destruct varfree as (nvl,varfree).
   destruct varfree as (nvu,varfree).
   rewrite varfree.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature).
   intro L.
   destruct L as (Lnvl,Lnvu).

   (* début de la preuve *)
   intros.
   split.
   apply HR1.
   lia.
   split.
   apply HR1.
   lia.
   
   apply (borne_free nb_feature i vl vu nvl nvu).
   split. lia.
   split. lia.
   split. apply HR0.
   split. apply HR0.
   split. apply HR1.
   exact varfree.
   lia.
   
   (* preuve des tailles *)
   apply (preserveSizeCas3 i v vl vu nvl nvu ).
   repeat split ; [lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree].
   
   (* preuve du cut avec les exists *)
   destruct (freeAttr i vl vu).
   exists l.
   exists l0.
   reflexivity.
Qed.
   

Lemma preserveR2Cas3_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu:  list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) = (k nvu)) /\ 
  (R0 k i v vl vu p /\
   R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
   R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9 k i v vl vu p /\ R10 k i v vl vu p /\ (stable k)) 
 -> R2 k (i+1) v (fst (freeAttr i vl vu)) (snd (freeAttr i vl vu)) p.
Proof.
   intros. 
   unfold R2.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,H).
   destruct H as (HR10,k_stable).
   unfold R0 in HR0.
   unfold R1 in HR1.
   unfold R2 in HR2.
   
   cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
   intro varfree.
   destruct varfree as (nvl,varfree).
   destruct varfree as (nvu,varfree).
   rewrite varfree.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature).
   intro L.
   destruct L as (Lnvl,Lnvu).

   (* début de la preuve *)
   generalize Hdif_k.
   rewrite (surjective_pairing (freeAttr i vl vu)).
   rewrite varfree.
   simpl.

   split.
   (* k nvl = k nvu *)
   auto.
   (* k nvl = k v *)
   cut (le_n nvl v).
   cut (le_n v nvu).
   intros le_n_l le_n_u.
   apply (k_stable nvl nvu v).
   split. apply Lnvl.
   split. apply Lnvu.
   split. apply HR0.
   split. intros. split. apply (borne_free nb_feature i vl vu nvl nvu).
   split. lia.
   split. lia.
   split. apply HR0.
   split. apply HR0.
   split. apply HR1.
   exact varfree.
   lia.
   apply (borne_free nb_feature i vl vu nvl nvu).
   split. lia.
   split. lia.
   split. apply HR0.
   split. apply HR0.
   split. apply HR1.
   exact varfree.
   lia.
   split. intros. split. apply (borne_free nb_feature i vl vu nvl nvu).
   split. lia.
   split. lia.
   split. apply HR0.
   split. apply HR0.
   split. apply HR1.
   exact varfree.
   lia.
   apply (borne_free nb_feature i vl vu nvl nvu).
   split. lia.
   split. lia.
   split. apply HR0.
   split. apply HR0.
   split. apply HR1.
   exact varfree.
   lia.
   split.
   intros.
   split.
   apply HR1. lia.
   apply HR1. lia.
   auto.

   (* le_n v nvu *)
   unfold le_n.
   split.
   apply HR0.
   split.
   apply Lnvu.
   intros.
   cut (i0=i \/ i0<>i).
   intro di0.
   destruct di0.
   (* i0 = i *)
   rewrite H0.
   cut (get i nvu = nu i).
   intro rnvu.
   rewrite rnvu.
   apply HR1.
   lia.
   apply (free_i nb_feature i vl vu nvl nvu).
   repeat split; [lia | lia | lia | apply varfree | apply HR0 | apply HR0].
   (* i0 <> i *)
   cut (get i0 nvu = get i0 vu).
   intro rnvu.
   rewrite rnvu.
   unfold R4 in HR4.
   destruct (HR4 i0).
   destruct H1.
   rewrite H2.
   apply HR1.
   lia.
   destruct H1.
   rewrite H2.
   apply led_eq.
   reflexivity.
   symmetry.
   apply (free_get nb_feature i i0 vl vu nvl nvu).
   repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
   lia.

   (* le_n nvl v *)
   unfold le_n.
   split.
   apply Lnvl.
   split.
   apply HR0.
   intros.
   cut (i0=i \/ i0<>i).
   intro di0.
   destruct di0.
   (* i0 = i *)
   rewrite H0.
   cut (get i nvl = lambda i).
   intro rnvl.
   rewrite rnvl.
   apply HR1.
   lia.
   apply (free_i nb_feature i vl vu nvl nvu).
   repeat split; [lia | lia | lia | apply varfree | apply HR0 | apply HR0].
   (* i0 <> i *)
   cut (get i0 nvl = get i0 vl).
   intro rnvl.
   rewrite rnvl.
   unfold R4 in HR4.
   destruct (HR4 i0).
   destruct H1.
   rewrite H1.
   apply HR1.
   lia.
   destruct H1.
   rewrite H1.
   apply led_eq.
   reflexivity.
   symmetry.
   apply (free_get nb_feature i i0 vl vu nvl nvu).
   repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
   lia.
   
   (* preuve des tailles *)
   apply (preserveSizeCas3 i v vl vu nvl nvu ).
   repeat split ; [lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree].
   
   (* preuve du cut avec les exists *)
   destruct (freeAttr i vl vu).
   exists l.
   exists l0.
   reflexivity.
   Qed.

Lemma preserveR3Cas3_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu:  list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) = (k nvu)) /\ 
  (R0 k i v vl vu p /\
   R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
   R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R3 k (i + 1) v (fst (freeAttr i vl vu)) (snd (freeAttr i vl vu)) p.
Proof.
   intros.
   unfold R3.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   unfold R3 in HR3.
   
   (* Début de la preuve *)

  lia.
   Qed.


   Lemma preserveR4_bisCas3_AXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
   i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) = (k nvu)) /\ 
   (R0 k i v vl vu p /\
   R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
   R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9 k i v vl vu p /\ R10 k i v vl vu p) 
  -> R4_bis k (i + 1) v (fst (freeAttr i vl vu)) (snd (freeAttr i vl vu)) p.
 Proof.
   intros. 
   unfold R4_bis.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.
   unfold R4_bis in HR4.
   
   cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
   intro varfree.
   destruct varfree as (nvl,varfree).
   destruct varfree as (nvu,varfree).
   rewrite varfree.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature).
   intro L.
   destruct L as (Lnvl,Lnvu).

   (* début de la preuve *)
   intros.
   cut (i<>j \/ i=j).
   intro di.
   destruct di.
   (* i<>j -> get j nvl = get j vl + HR4 *)
   cut (get j nvl = get j vl).
   intro rnnvl.
   rewrite rnnvl.
   cut (get j nvu = get j vu).
   intro rnnvu.
   rewrite rnnvu.
   apply HR4.
   (*tauto.*)

   symmetry.
   apply (free_get nb_feature i j vl vu nvl nvu).
   repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
   symmetry.
   apply (free_get nb_feature i j vl vu nvl nvu).
   repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].

   (* i=j -> corps de free*)
   left.
   rewrite <- H0.
   apply (free_i nb_feature i vl vu nvl nvu).
   repeat split; [lia | lia | lia | apply varfree | apply HR0 | apply HR0].

   lia.
   
   (* preuve des tailles *)
   apply (preserveSizeCas3 i v vl vu nvl nvu ).
   repeat split ; [lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree].
   
   (* preuve du cut avec les exists *)
   destruct (freeAttr i vl vu).
   exists l.
   exists l0.
   reflexivity.
   Qed.
 


Lemma preserveR4Cas3_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) = (k nvu)) /\ 
  (R0 k i v vl vu p /\
   R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
   R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R4 k (i+1) v (fst (freeAttr i vl vu)) (snd (freeAttr i vl vu)) p.
Proof.
   intros.
   apply R4_bis_implies_R4.
   split.
   apply preserveR0Cas3_AXp.
   apply H.

   cut (R4_bis k i v vl vu p).
   intro.
   apply preserveR4_bisCas3_AXp.
   tauto.
   apply R4_implies_R4_bis.
   apply H.
   Qed.

Lemma preserveR5Cas3_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu:  list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) = (k nvu)) /\ 
  (R0 k i v vl vu p /\
   R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
   R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R5 k (i+1) v (fst (freeAttr i vl vu)) (snd (freeAttr i vl vu)) p.
Proof.
   intros.
   unfold R5.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   unfold R5 in HR5.
   intros.
   apply HR5.
   lia.
   Qed.


Lemma preserveR6Cas3_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu:  list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) = (k nvu)) /\ 
  (R0 k i v vl vu p /\
   R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
   R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R6 k (i+1) v (fst (freeAttr i vl vu)) (snd (freeAttr i vl vu)) p.
Proof.
   intros. 
   unfold R6.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.
   unfold R6 in HR6.
   
   cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
   intro varfree.
   destruct varfree as (nvl,varfree).
   destruct varfree as (nvu,varfree).
   rewrite varfree.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature).
   intro L.
   destruct L as (Lnvl,Lnvu).

   (* début de la preuve *)
   intros.
   (* D'abord des hypothèse liés à la contraposée de HR5 *)
   cut (j<i /\ j >= 0 /\ j < nb_feature).
   intro.
   cut (get j nvl = get j vl).
   intro rnvl.
   rewrite rnvl.
   cut (get j nvu = get j vu).
   intro rnvu.
   rewrite rnvu.
   apply HR6.
   auto.
   symmetry.
   apply (free_get nb_feature i j vl vu nvl nvu).
   repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
   symmetry.
   apply (free_get nb_feature i j vl vu nvl nvu).
   repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
   (* contraposée de HR5 *)
   cut (mem j p -> (j < i /\ j >= 0 /\ j < nb_feature)).
   intro CHR5.
   apply CHR5.
   tauto.
   cut (~~mem j p ->  ~(j >= i \/ j < 0 \/ j >= nb_feature)).
   intros.
   cut (~(j >= i \/ j < 0 \/ j >= nb_feature)).
   lia.
   apply H0.
   tauto.
   unfold R5 in HR5.
   generalize (HR5 j).
   apply contrapose.
   
   (* preuve des tailles *)
   apply (preserveSizeCas3 i v vl vu nvl nvu ).
   repeat split ; [lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree].
   
   (* preuve du cut avec les exists *)
   destruct (freeAttr i vl vu).
   exists l.
   exists l0.
   reflexivity.
   Qed.

Lemma preserveR7Cas3_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu:  list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) = (k nvu)) /\ 
  (R0 k i v vl vu p /\
   R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
   R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R7 k (i+1) v (fst (freeAttr i vl vu)) (snd (freeAttr i vl vu)) p.
Proof.
   intros. 
   unfold R7.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.
   unfold R7 in HR7.
   
   cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
   intro varfree.
   destruct varfree as (nvl,varfree).
   destruct varfree as (nvu,varfree).
   rewrite varfree.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature).
   intro L.
   destruct L as (Lnvl,Lnvu).

   (* début de la preuve *)
   intros.

   cut (i=j \/ i<>j).
   intro di.
   destruct di.

   (*i=j*)
   rewrite <- H0.
   apply (free_i nb_feature i vl vu nvl nvu).
   repeat split; [lia | lia | lia | apply varfree | apply HR0 | apply HR0].

   (* i<> j*)
   cut (get j nvl = get j vl).
   intro rnvl.
   rewrite rnvl.
   cut (get j nvu = get j vu).
   intro rnvu.
   rewrite rnvu.
   apply HR7.
   split.
   lia.
   split.
   lia.
   tauto.
   symmetry.
   apply (free_get nb_feature i j vl vu nvl nvu).
   repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
   symmetry.
   apply (free_get nb_feature i j vl vu nvl nvu).
   repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].

   lia.

   (* preuve des tailles *)
   apply (preserveSizeCas3 i v vl vu nvl nvu ).
   repeat split ; [lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree].
   
   (* preuve du cut avec les exists *)
   destruct (freeAttr i vl vu).
   exists l.
   exists l0.
   reflexivity.
   Qed.


Lemma preserveR8Cas3_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu:  list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) = (k nvu)) /\ 
  (R0 k i v vl vu p /\
   R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
   R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R8 k (i+1) v (fst (freeAttr i vl vu)) (snd (freeAttr i vl vu)) p.
Proof.
   intros.
   unfold R8.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R8 in HR8.
   (* expensions des quadruplets *)
   auto.
   Qed.

Lemma preserveR9Cas3_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) = (k nvu)) /\ 
  (R0 k i v vl vu p /\
   R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
   R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R9 k (i+1) v (fst (freeAttr i vl vu)) (snd (freeAttr i vl vu)) p.
Proof.
   intros. 
   unfold R9.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.
   unfold R9 in HR9.
   
   cut (exists (nvl nvu : list T), freeAttr i vl vu = (nvl,nvu)).
   intro varfree.
   destruct varfree as (nvl,varfree).
   destruct varfree as (nvu,varfree).
   rewrite varfree.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature).
   intro L.
   destruct L as (Lnvl,Lnvu).

   (* début de la preuve *)
   intros.
   
   cut (i<>j).
   intro.
   cut (get j nvl = get j vl).
   intro rnnvl.
   rewrite rnnvl.
   cut (get j nvu = get j vu).
   intro rnnvu.
   rewrite rnnvu.
   apply HR9.
   lia.
   symmetry.
   apply (free_get nb_feature i j vl vu nvl nvu).
   repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
   symmetry.
   apply (free_get nb_feature i j vl vu nvl nvu).
   repeat split; [lia | lia | lia | lia | lia | apply varfree | apply HR0 | apply HR0].
   lia.

   (* preuve des tailles *)
   apply (preserveSizeCas3 i v vl vu nvl nvu ).
   repeat split ; [lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfree].
   
   (* preuve du cut avec les exists *)
   destruct (freeAttr i vl vu).
   exists l.
   exists l0.
   reflexivity.
   Qed.

Lemma preserveR10Cas3_AXp : 
  forall (k : list T -> Tk) (i:nat) (v vl vu:  list T) (p:list nat), 
  i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) = (k nvu)) /\ 
  (R0 k i v vl vu p /\
   R1 k i v vl vu p /\ R2 k i v vl vu p /\ R3 k i v vl vu p /\ R4 k i v vl vu p /\
   R5 k i v vl vu p /\ R6 k i v vl vu p /\ R7 k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9 k i v vl vu p /\ R10 k i v vl vu p) 
 -> R10 k (i+1) v (fst (freeAttr i vl vu)) (snd (freeAttr i vl vu)) p.
Proof.
   intros.
   unfold R10.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R10 in HR10.
   (* Début de la preuve *)
   apply HR10.
   Qed.


Lemma ppost1_AXp :  forall (k : list T -> Tk) (v vl vu: list T) (p:list nat),
  R0 k nb_feature v vl vu p /\
  R1 k nb_feature v vl vu p /\
  R2 k nb_feature v vl vu p /\
  R3 k nb_feature v vl vu p /\
  R4 k nb_feature v vl vu p /\
  R5 k nb_feature v vl vu p /\
  R6 k nb_feature v vl vu p /\
  R7 k nb_feature v vl vu p /\
  R8 k nb_feature v vl vu p /\
  R9 k nb_feature v vl vu p /\
  R10 k nb_feature v vl vu p /\
  stable k
-> is_weak_AXp k v p.
Proof.
   intros.
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR4,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,H).
   destruct H as (HR10,k_stable).
   unfold R0 in HR0.
   unfold R1 in HR1.
   unfold R2 in HR2.
   unfold R6 in HR6.
   unfold R7 in HR7.

   unfold is_weak_AXp.
   intros.
   destruct H as (H1,H).
   destruct H as (H2,H).
   destruct H as (H3,H).

   destruct HR2 as (HR2_1,HR2_2).
   rewrite <- HR2_2.

   (* kx = k vl *)
   symmetry.
   apply (k_stable vl vu x).
   split.
   apply HR0.
   split.
   apply HR0.
   split.
   apply H2.
   split.
   intros.
   repeat split; [apply HR1;lia|apply HR1;lia].
   split.
   intros.
   repeat split; [apply HR1;lia|apply HR1;lia].
   split.
   apply H3.
   split.

   (* le_n vl x *)
   unfold le_n.
   split.
   apply HR0.
   split.
   apply H2.

   intros.
   destruct (H i).
     (* mem i p /\ get i x = get i v *)
     lia.
     destruct H4.
     rewrite H5.
     apply led_eq.
     apply (HR6 i).
     apply H4.
     (* ~ mem i p *)
     cut (get i vl = lambda i).
     intro dgetivl.
     rewrite dgetivl.
     apply H3.
     lia.
     apply (HR7 i).
     repeat split; [apply H0|apply H0|apply H4].
   
   split.

   (* le_n x vu *)
   unfold le_n.
   split.
   apply H2.
   split.
   apply HR0.

   intros.
   destruct (H i).
     (* mem i p /\ get i x = get i v *)
     lia.
     destruct H4.
     rewrite H5.
     apply led_eq.
     symmetry.
     apply (HR6 i).
     apply H4.
     (* ~ mem i p *)
     cut (get i vu = nu i).
     intro dgetivu.
     rewrite dgetivu.
     apply H3.
     lia.
     apply (HR7 i).
     repeat split; [apply H0|apply H0|apply H4].
   
   (* k vl = k vu *)
   apply HR2_1.
Qed.


Lemma R_implies_E_findAXp : forall (k : list T -> Tk) ,
   (stable k) -> (forall (i:nat),  i>=0 /\ i < nb_feature +1 -> R_implies_E_AXp k i).
Proof.
intros k k_stable.
apply (my_induction nb_feature).
(* cas général *)
split.
unfold R_implies_E_AXp.
intros.
destruct H.
unfold E1.
unfold E2.
unfold E3.
(* couper selon les 3 cas du findAxp_aux *)
cut ((i = nb_feature +1) 
  \/ (i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) <> (k nvu))) 
  \/ (i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu) :=  freeAttr i vl vu in (k nvl) = (k nvu)))).
intro cases.
destruct cases.
(* cas terminal, pas possible *)
cut False.
tauto.
lia.
destruct H3.
(* cas 2 *)
destruct H3.
destruct H4.
cut (let '(nvl,nvu) :=  freeAttr i vl vu in let '(nnvl,nnvu,np) := fixAttr i v nvl nvu p in findAXp_aux k i v vl vu p = findAXp_aux k (i+1) v nnvl nnvu np).
rewrite (surjective_pairing (freeAttr i vl vu)).
rewrite (surjective_pairing (fixAttr i v (fst (freeAttr i vl vu)) (snd (freeAttr i vl vu)) p)).
rewrite (surjective_pairing (fst (fixAttr i v (fst (freeAttr i vl vu)) (snd (freeAttr i vl vu)) p))).
intro r.
rewrite r.
apply H0.
(* préservation des require *)
split.
apply preserveR0Cas2_AXp.
tauto.
split.
apply preserveR1Cas2_AXp.
tauto.
split.
apply preserveR2Cas2_AXp.
tauto.
split.
apply preserveR3Cas2_AXp.
tauto.
split.
apply preserveR4Cas2_AXp.
tauto.
split.
apply preserveR5Cas2_AXp.
tauto.
split.
apply preserveR6Cas2_AXp.
tauto.
split.
apply preserveR7Cas2_AXp.
tauto.
split.
apply preserveR8Cas2_AXp.
tauto.
split.
apply preserveR9Cas2_AXp.
tauto.
apply preserveR10Cas2_AXp.
tauto.
(* lien rec *)
apply findAXp_aux_spec2.
auto.
(*  cas 3 *)
destruct H3.
destruct H4.
cut (let '(nvl,nvu) :=  freeAttr i vl vu in findAXp_aux k i v vl vu p = findAXp_aux k (i+1) v nvl nvu p).
rewrite (surjective_pairing (freeAttr i vl vu)).
intro r.
rewrite r.
apply H0.
(* préservation des require *)
split.
apply preserveR0Cas3_AXp.
tauto.
split.
apply preserveR1Cas3_AXp.
tauto.
split.
apply preserveR2Cas3_AXp.
tauto.
split.
apply preserveR3Cas3_AXp.
tauto.
split.
apply preserveR4Cas3_AXp.
tauto.
split.
apply preserveR5Cas3_AXp.
tauto.
split.
apply preserveR6Cas3_AXp.
tauto.
split.
apply preserveR7Cas3_AXp.
tauto.
split.
apply preserveR8Cas3_AXp.
tauto.
split.
apply preserveR9Cas3_AXp.
tauto.
apply preserveR10Cas3_AXp.
tauto.
(* lien rec *)
apply findAXp_aux_spec3.
auto.
(* Prouver qu'on a bien que ces 3 cas possible *)
right.
cut (i >= 0 /\
i < nb_feature /\
((let '(nvl, nvu) := freeAttr i vl vu in k nvl <> k nvu) \/ (let '(nvl, nvu) := freeAttr i vl vu in k nvl = k nvu))).
intro r.
destruct r.
destruct H4.
destruct H5.
left.
auto.
right.
auto.
split.
auto.
split.
lia.
rewrite (surjective_pairing (freeAttr i vl vu)).
apply Tk_tier_exclu.
(* cas terminal *)
unfold R_implies_E_AXp.
intros.
split.
(* post cond 1 *)
unfold E1.
unfold findAXp_aux.
cut (nb_feature - nb_feature = 0).
intro r.
rewrite r.
simpl.
apply (ppost1_AXp k v vl vu p).
tauto.
lia.
(* post cond 2 *)
split.
unfold E2.
unfold findAXp_aux.
cut (nb_feature - nb_feature = 0).
intro r.
rewrite r.
simpl.
unfold R8 in H.
apply H.
lia.
(* post cond 3 *)
unfold E3.
unfold findAXp_aux.
cut (nb_feature - nb_feature = 0).
intro r.
rewrite r.
simpl.
unfold R10 in H.
apply H.
lia.
Qed.

Program Definition findAXp (k : list T -> Tk) (v: list T) : list nat :=
  findAXp_aux k 0 v v v nil.


Lemma R_init_Axp : forall (k : list T -> Tk)  (v: list T), 
(length v = nb_feature
/\ 
(forall (j:nat), j>=0 /\ j< nb_feature -> 
led (lambda j) (get j v) /\ led (get j v) (nu j))
)
-> R0 k 0 v v v nil /\ R1 k 0 v v v nil /\ R2 k 0 v v v nil /\ R3 k 0 v v v nil /\ 
R4 k 0 v v v nil /\ R5 k 0 v v v nil /\ R6 k 0 v v v nil /\ R7 k 0 v v v nil /\ 
R8 k 0 v v v nil /\ R9 k 0 v v v nil /\ R10 k 0 v v v nil.
Proof.
   intros.
   split.
   (* R0 *)
   unfold R0.
   tauto.
   split.
   (* R1 *)
   destruct H.
   unfold R1.
   intros.
   repeat split; [apply (H0 j H1)|apply (H0 j H1)|apply (H0 j)|apply (H0 j H1)|apply (H0 j H1)|apply (H0 j H1)].
   apply H1.
   split.
   (* R2 *)
   unfold R2.
   simpl.
   auto.
   split.
   (* R3 *)
   unfold R3.
   simpl.
   lia.
   split.
   (* R4 *)
   unfold R4.
   simpl.
   right.
   generalize H.
   simpl.
   tauto.
   split.
   (* R5 *)
   unfold R5.
   simpl.
   tauto.
   split.
   (* R6 *)
   unfold R6.
   simpl.
   tauto.
   split.
   (* R7 *)
   unfold R7.
   simpl.
   lia.
   split.
   (* R8 *)
   unfold R8.
   simpl.
   tauto.
   split.
   (* R9 *)
   unfold R9.
   simpl.
   tauto.
   (* R10 *)
   unfold R10.
   simpl.
   intros.
   cut False.
   tauto.
   cut (x0 ++ x :: x1 <> nil).
   intro.
   auto.
   apply (list_mem_not_nil x (x0 ++ x :: x1)).
   apply list_mem_middle.
Qed.

Lemma pre_post_findAXp : forall (k : list T -> Tk)  (v: list T), 
(
stable k
/\
length v = nb_feature
/\ 
(forall (j:nat), j>=0 /\ j< nb_feature -> 
led (lambda j) (get j v) /\ led (get j v) (nu j))
)
-> 
   is_weak_AXp k v (findAXp k v)
/\ is_sorted (findAXp k v)
/\ forall (x:nat), forall (x0 x1 : list nat), ((findAXp k v) = x0++(x::x1)
-> 
exists  (vl vu : list T),
length vl = nb_feature /\
length vu = nb_feature /\
(forall (j:nat), j>=0 /\ j< nb_feature 
->  ((mem j x1 \/ j>x) /\ get j vl=get j v /\ get j vu=get j v) 
\/ ( (not (mem j x1 \/ j>x)) /\ get j vl=lambda j /\ get j vu = nu j) )
/\ (k vl) <> (k vu)).
Proof.
   intros.
   destruct H as (k_stable, H).
   generalize (R_init_Axp k v H).
   intro HR.
   destruct HR as (HR0,HR).
   destruct HR as (HR1,HR).
   destruct HR as (HR2,HR).
   destruct HR as (HR3,HR).
   destruct HR as (HR4,HR).
   destruct HR as (HR5,HR).
   destruct HR as (HR6,HR).
   destruct HR as (HR7,HR).
   destruct HR as (HR8,HR).
   destruct HR as (HR9,HR10).
   split.
   (* post 1 *)
   generalize R_implies_E_findAXp.
   unfold R_implies_E_AXp.
   unfold E1.
   intros.
   unfold findAXp.
   apply H0.
   apply k_stable.
   lia.
   tauto.
   split.
   (* post 2*)
   generalize R_implies_E_findAXp.
   unfold R_implies_E_AXp.
   unfold E2.
   intros.
   unfold findAXp.
   apply H0.
   apply k_stable.
   lia.
   tauto.
   (* post 3*)
   generalize R_implies_E_findAXp.
   unfold R_implies_E_AXp.
   unfold E3.
   intro.
   unfold findAXp.
   apply H0.
   apply k_stable.
   lia.
   tauto.
Qed.

 Fixpoint is_set {a:Type} (l:list a) : Prop :=
  match l with
  | nil => True
  | t::q => not (mem t q) /\ (is_set q)
  end.

Definition is_subset {a:Type} (l1 l2 : list a) : Prop :=
  (is_set l1) /\ (is_set l2) /\ (forall (e : a), mem e l1 -> mem e l2) .
  
Definition is_strict_subset  {a:Type} (l1 : list a) (l2 : list a) : Prop :=
  (is_subset l1 l2) /\ (exists (e : a), mem e l2 /\ not (mem e l1)).

Definition leq {a:Type} (l1 l2: list a) : Prop :=
   forall (e : a), mem e l1 <-> mem e l2.

Lemma is_subset_leq_or_is_strict_subset  {a:Type} : forall (l1 l2: list a),
   is_subset l1 l2 -> leq l1 l2 \/ is_strict_subset l1 l2.
Proof.
   intro l1.
   intro l2.
   intro.
   cut ((exists (e : a), mem e l2 /\ not (mem e l1)) \/ ~(exists (e : a), mem e l2 /\ not (mem e l1))).
   intro d.
   destruct d.
   (* exists (e : a), mem e l2 /\ not (mem e l1) *)
   right.
   unfold is_strict_subset.
   tauto.
   (* ~ exists (e : a), mem e l2 /\ not (mem e l1) *)
   left.
   unfold is_subset in H.
   destruct H.
   destruct H1.
   unfold leq.
   split.
   (* mem e l1 -> mem e l2 *)
   auto.
   (* mem e l2 -> mem e l1 *)
   intro.
   cut (mem e l1 \/ ~mem e l1).
   intro d.
   destruct d.
   auto.
   cut False.
   tauto.
   generalize H0.
   unfold not.
   intro.
   apply H5.
   exists e.
   tauto.
   tauto.
   tauto.
Qed.

Lemma leq_weak_id : forall (k : list T -> Tk ) (v:  list T) (l1 l2: list nat),
leq l1 l2 -> (is_weak_AXp k v l1 <-> is_weak_AXp k v l2).
Proof.
   intros.
   split.
   (* is_weak_AXp v l1 -> is_weak_AXp v l2*)
   unfold is_weak_AXp.
   unfold leq in H.
   intros.
   destruct H1.
   destruct H2.
   destruct H3.
   apply (H0 x).
   split.
   apply H1.
   split.
   apply H2.
   split.
   apply H3.
   intro.
   generalize (H4 j);
   intro.
   generalize (H j).
   intro.
   rewrite H6.
   apply H5.
   (* is_weak_AXp v l2 -> is_weak_AXp v l1 *)
   unfold is_weak_AXp.
   unfold leq in H.
   intros.
   destruct H1.
   destruct H2.
   destruct H3.
   apply (H0 x).
   split.
   apply H1.
   split.
   apply H2.
   split.
   apply H3.
   intro.
   generalize (H4 j);
   intro.
   generalize (H j).
   intro.
   rewrite <- H6.
   apply H5.
Qed.

Definition is_AXp (k : list T -> Tk) (v: list T) (p:list nat) : Prop :=
   is_weak_AXp k v p (* satisfy the constraint *)
/\ forall (q:list nat), (is_strict_subset q p) -> not (is_weak_AXp k v q). (* all subset do not satisfy the constraint *)

Definition is_minus_one {a:Type} (q :list a) (p:list a)   : Prop :=
exists (x: a) (x0 x1 : list a), p=x0++(x::x1) /\ q=x0++x1.

Lemma append_mem {t:Type} : forall (x:t) (x0 x1 : list t),  mem x (x0++(x::x1)).
Proof.
   intros x x0 x1.
   induction x0.
   simpl.
   left.
   auto.
   simpl.
   right.
   apply IHx0.
Qed.   

Lemma mem_append {t:Type}: forall (e :t) (x0 x1 : list t), mem e (x0++x1) -> mem e x0 \/ mem e x1.
Proof.
   intros e x0 x1 h1.
   induction x0.
   cut (mem e (nil ++ x1)).
   simpl.
   auto.
   apply h1.
   cut ( mem e ((a :: x0) ++ x1)).
   simpl.
   intro c.
   destruct c.
   auto.
   cut (e = a \/ (mem e x0 \/ mem e x1)).
   tauto.
   cut (mem e x0 \/ mem e x1).
   auto.
   apply IHx0.
   apply H.
   apply h1.
   Qed.

Lemma mem_append_2  {t:Type} : forall (e:t) (x0 x1 : list t), mem e x0 -> mem e (x0++x1).
Proof.
   intros.
   induction x0.
   cut False.
   tauto.
   generalize H.
   simpl.
   auto.
   simpl.
   generalize H.
   simpl.
   intro d.
   destruct d.
   auto.
   right.
   apply IHx0.
   auto.
Qed.

Lemma mem_append_3  {t:Type} : forall (e:t) (x0 x1 : list t), mem e x1 -> mem e (x0++x1).
Proof.
   intros.
   induction x0.
   (* cas de base *)
   simpl.
   auto.
  (* cas général *)
  simpl.
  right.
  auto.
Qed.

Lemma mem_exists_append {t:Type} : forall (e:t) (l:list t), mem e l -> exists (l1 l2 : list t), l=l1++(e::l2).
Proof.
   intros.
   induction l.
   cut False.
   tauto.
   generalize H.
   simpl.
   auto.
   generalize H.
   simpl.
   intro d.
   destruct d.
   exists nil.
   exists l.
   rewrite H0.
   simpl.
   reflexivity.
   generalize (IHl H0).
   intro.
   destruct H1.
   destruct H1.
   exists (a::x).
   exists x0.
   rewrite H1.
   auto.
Qed.

Lemma sorted_sorted : forall (x0 x1 : list nat), is_sorted (x0++x1) -> is_sorted x0 /\   is_sorted x1.
Proof.
   intros.
   induction x0.
   simpl.
   generalize H.
   simpl.
   tauto.
   generalize H.
   simpl.
   intro.
   destruct H0.
   split.
   split.
   intros.
   apply H0.
   apply mem_append_2.
   exact H2.
   apply IHx0.
   exact H1.
   apply IHx0.
   exact H1.
Qed.

Lemma sorted_middle_x1 : forall (x:nat) (x0 x1 : list nat), 
is_sorted (x0++(x::x1)) -> (forall (e :nat), mem e x1 -> x > e).
Proof.
   intros.
   cut (is_sorted (x::x1)).
   simpl.
   intro.
   destruct H1.
   apply (H1 e).
   exact H0.
   apply (sorted_sorted x0 (x::x1)).
   exact H.
Qed.

Lemma sorted_middle_x0 :  forall (x:nat) (x0 x1 : list nat), 
is_sorted (x0++(x::x1)) -> (forall (e:nat), mem e x0 -> x < e).
Proof.
   intros.
   induction x0.
   cut False.
   tauto.
   generalize H0.
   simpl.
   tauto.
   generalize H0.
   simpl.
   intro.
   destruct H1.
   generalize H.
   rewrite <- H1.
   simpl.
   intro.
   destruct H2.
   apply (H2 x).
   apply append_mem.
   apply IHx0.
   generalize H.
   simpl.
   tauto.
   exact H1.
Qed.

Definition minus_one_AXp (k : list T -> Tk) (v:list T) (p:list nat) : Prop :=
   is_weak_AXp k v p (* satisfy the constraint *)
/\ forall (q:list nat), (is_minus_one q p) -> not (is_weak_AXp k v q). (* all subset do not satisfy the constraint *)

Lemma not_weak_subset : forall (k : list T -> Tk) (v: list T) (p q:list nat),
not (is_weak_AXp k v q) /\ (is_strict_subset p q) -> not (is_weak_AXp k v p).
Proof.
   intros.
   destruct H.
   unfold is_weak_AXp.
   unfold is_weak_AXp in H.
   unfold is_strict_subset in H0.
   destruct H0.
   unfold not.
   intro.
   generalize H.
   unfold not.
   intro.
   apply H3.
   intros.
   destruct H4.
   destruct H5.
   destruct H6.
   unfold is_subset in H0.
   destruct H0 as (setp,H0).
   destruct H0 as (setq,H0).
   apply H2.
   split.
   apply H4.
   split.
   apply H5.
   split.
   intro.
   apply H6.
   intro.
   intro.
   cut (mem j p \/ ~mem j p).
   intro d.
   destruct d.
   left.
   destruct (H7 j).
   lia.
   split.
   apply H9.
   tauto.
   cut False.
   tauto.
   cut (mem j q).
   tauto.
   apply H0.
   apply H9.
   right.
   auto.
   apply mem_not_mem.
Qed.

Lemma set_minus_one_is_set {a:Type} : forall (x:a) (x0 x1:list a),
is_set (x0++x::x1) -> is_set (x0++x1).
Proof.
   intros.
   induction x0.
   generalize H.
   simpl.
   tauto.
   simpl.
   split.
   generalize H.
   simpl.
   intro.
   destruct H0.
   cut (~(mem a0 x0 \/ mem a0 x1)).
   cut ( mem a0 (x0 ++ x1) -> (mem a0 x0 \/ mem a0 x1)).
   apply contrapose.
   apply mem_append.
   cut (~mem a0 x0 /\ ~mem a0 x1).
   tauto.
   cut (~mem a0 x0 /\ ~mem a0 (x::x1)).
   intro.
   split.
   tauto.
   destruct H2.
   generalize H3.
   simpl.
   tauto.
   split.
   cut (~ mem a0 (x0 ++ (x :: x1))).
   cut (mem a0 x0 -> mem a0 (x0 ++ x :: x1)).
   apply contrapose.
   apply mem_append_2.
   apply H0.
   cut (~ mem a0 (x0 ++ (x :: x1))).
   cut (mem a0 (x :: x1) -> mem a0 (x0 ++ (x :: x1))).
   apply contrapose.
   apply mem_append_3.
   auto.
   apply IHx0.
   generalize H.
   simpl.
   tauto.
Qed.

Lemma minus_subset : forall (p q:list nat),
  (is_strict_subset q p )-> (exists (q': list nat), (is_minus_one q' p) /\ is_subset q q').
  Proof.
     intros.
     unfold is_strict_subset in H.
     destruct H.
     destruct H0.
     cut (exists (l1 l2 : list nat), p=l1++x::l2).
     intro.
     destruct H1.
     destruct H1.
     exists (x0++x1).
     split.
     rewrite H1.
     unfold is_minus_one.
     exists x.
     exists x0.
     exists x1.
     auto.
     unfold is_subset.
     unfold is_subset in H.
     destruct H.
     destruct H2.
     split.
     exact H.
     split.
     apply (set_minus_one_is_set x x0 x1).
     rewrite H1 in H2.
     auto.
     intros.
     cut (mem e x0 \/ mem e (x::x1)).
     intro d.
     destruct d.
     apply mem_append_2.
     auto.
     generalize H5.
     simpl.
     intro d.
     destruct d.
     cut False.
     tauto.
     rewrite <- H6 in H0.
     tauto.
     apply mem_append_3.
     auto.
     apply mem_append.
     rewrite <- H1.
     apply H3.
     auto.
     apply mem_exists_append.
     tauto.
  Qed.


Lemma minus_one_implies_subset : forall (k : list T -> Tk) (v: list T) (p: list nat), 
   (forall (q:list nat), (is_minus_one q p) -> not (is_weak_AXp k v q))
-> (forall (q:list nat), (is_strict_subset q p) -> not (is_weak_AXp k v q)).
Proof.
   intros.
   cut (exists (q': list nat), (is_minus_one q' p) /\ is_subset q q').
   intro.
   destruct H1.
   destruct H1.
   cut (leq q x \/ is_strict_subset q x).
   intro d.
   destruct d.
   (* leq q x *)
   generalize (leq_weak_id k v q x).
   intro.
   destruct H4.
   auto.
   cut (~ is_weak_AXp k v x).
   auto.
   apply (H x).
   auto.
   (* is_strict_subset q x *)
   apply (not_weak_subset k v q x).
   cut (~ is_weak_AXp k v x).
   intro.
   tauto.
   apply (H x).
   auto.
   (* leq q x \/ is_strict_subset q x *)
   apply (is_subset_leq_or_is_strict_subset q x).
   auto.
   (* exists q' : list nat, is_minus_one q' p /\ is_subset q q' *)
   apply (minus_subset p q).
   auto.
Qed.

Lemma minus_one_all_aux1 : forall (k : list T -> Tk)  (v :list T),
stable k
/\
length v = nb_feature
/\
(forall (j:nat), j>=0 /\ j< nb_feature -> 
  led (lambda j) (get j v) /\ led (get j v) (nu j))
-> is_weak_AXp k v (findAXp k v).
Proof.
   intros.
   apply pre_post_findAXp.
   simpl.
   tauto.
Qed.


(* Lemmes pour minus_one_all_aux2 *)
Lemma axp_inter_aux2 : forall (k : list T -> Tk)  (v : list T) (x: nat) (x0 x1 : list nat),
stable k 
/\
length v = nb_feature
/\
(forall (j:nat), j>=0 /\ j< nb_feature -> 
  led (lambda j) (get j v) /\ led (get j v) (nu j))
/\  findAXp k v =x0++(x::x1) -> 
(forall (e:nat), mem e x0 -> e > x).
Proof.
   intros.
   destruct H as (k_stable, H).
   destruct H.
   destruct H1.
   cut (x<e).
   lia.
   apply (sorted_middle_x0 x x0 x1).
   rewrite <- H2.
   apply pre_post_findAXp.
   simpl.
   tauto.
   auto.
Qed.

Lemma axp_inter : forall (k : list T -> Tk) ,
stable k
-> (
forall (v : list T),
length v = nb_feature
/\
(forall (j:nat), j>=0 /\ j< nb_feature -> 
  led (lambda j) (get j v) /\ led (get j v) (nu j))
-> 
(forall (x:nat) (x0 x1 : list nat), findAXp k v =x0++(x::x1) -> 
(forall (e:nat), mem e x1 -> e < x)
/\
(forall (e:nat), mem e x0 -> e > x)
/\
(exists  (vl vu : list T),
length vl = nb_feature /\
length vu = nb_feature /\
(forall (j:nat), j>=0 /\ j< nb_feature 
->  ((mem j x1 \/ j>x) /\ get j vl=get j v /\ get j vu=get j v) 
\/ ( (not (mem j x1 \/ j>x)) /\ get j vl=lambda j /\ get j vu = nu j) )
/\ (k vl) <> (k vu)))
).
Proof.
   intros k k_stable.
   intros.
   split.
   (* (forall e : nat, mem e x1 -> e < x) *)
   intros.
   cut (x>e).
   lia.
   apply (sorted_middle_x1 x x0 x1).
   rewrite <- H0.
   apply pre_post_findAXp.
   simpl.
   tauto.
   auto.
   split.
   (* forall e : nat, mem e x0 -> e > x *)
   intros.
   cut (x<e).
   lia.
   apply (sorted_middle_x0 x x0 x1).
   rewrite <- H0.
   apply pre_post_findAXp.
   simpl.
   tauto.
   auto.
   (* exsits .... *)
   generalize (pre_post_findAXp k v).
   intros.
   destruct H1.
   split.
   apply k_stable.
   apply H.
   destruct H2.
   apply (H3 x x0 x1).
   auto.
Qed.

Lemma minus_one_all_aux2 : forall (k : list T -> Tk) (v :list T),
stable k
/\
length v = nb_feature
/\
(forall (j:nat), j>=0 /\ j< nb_feature -> 
  led (lambda j) (get j v) /\ led (get j v) (nu j))
-> forall (q:list nat), (is_minus_one q (findAXp k v)) -> not (is_weak_AXp k v q).
Proof.
(* idée :
p=x0++(Cons x x1) /\ q=x0++x1

quand on appel findAXp_aux x v vl vu x1
on free x dans vl et vu
et comme x est dans le p final, ça veut dire qu'on a un k différent pour k nvl et k nvu
nvl / nvu = 
  - v si dans x1 ou > x
  - borne sinon

Pour les deux si i dans q , i dans x1 -> val de v ou i dans x0 -> val de v (car > x) donc vérifie la prop de weak
mais comme ils sont différents, forcément un des deux qui ne vaut pas la même chose de k v.
*)
intros.
destruct H as (k_stable,H).
cut (exists (x:nat) (x0 x1 :list nat),
  (findAXp k v = (x0++(x::x1))) /\ (q = x0++x1)).
intros.
destruct H1.
destruct H1.
destruct H1.
destruct H1 as (decomp_find,defq).
destruct H as (Lv,H).
cut (exists  (vl vu : list T),
length vl = nb_feature /\ length vu = nb_feature /\
(forall (j:nat), j>=0 /\ j< nb_feature 
->  ((mem j x1 \/ j>x) /\ get j vl=get j v /\ get j vu=get j v) 
\/ ( (not (mem j x1 \/ j>x)) /\ get j vl=lambda j /\ get j vu = nu j))
/\ (k vl) <> (k vu)).
intros (vl,(vu,(Lvl,(Lvu,(vali,difg))))).
unfold not.
unfold is_weak_AXp.
intros.
cut (k vl = k vu /\ k vl <> k vu).
tauto.
split.
(* k vl = k vu *)
cut (k vl = k v).
cut (k vu = k v).
intros kvl kvu.
rewrite kvl.
rewrite kvu.
auto.
(* k vu = k v*)
apply (H1 vu).
split.
apply Lv.
split.
apply Lvu.
split.
intros.
cut (get j vu = get j v \/ get j vu = nu j).
intro val.
destruct val.
rewrite H3.
auto.
rewrite H3.
split.
apply (led_transitivity (lambda j) (get j v) (nu j)).
apply (H j).
lia.
apply led_eq.
reflexivity.
destruct (vali j).
lia.
left.
apply H3.
right.
apply H3.

intros.
cut (mem j q \/ ~ mem j q).
intro c.
destruct c.
left.
split.
apply H3.
cut (mem j x0 \/ mem j x1).
intro c.
destruct c.
cut (x<j).
intro comp.
destruct (vali j).
apply H2.
apply H5.
cut False.
tauto.
lia.
apply (axp_inter_aux2 k v x x0 x1).
split.
apply k_stable.
split.
apply Lv.
split.
apply H.
apply decomp_find.
apply H4.
destruct (vali j).
lia.
apply H5.
cut False.
tauto.
tauto.
cut ( mem j q).
rewrite defq.
apply mem_append.
auto.
right.
auto.
tauto.

(*k vl = k v *)
apply (H1 vl).
split.
apply Lv.
split.
apply Lvl.
split.
intros.
cut (get j vl = get j v \/ get j vl = lambda j).
intro val.
destruct val.
rewrite H3.
auto.
rewrite H3.
split.
apply led_eq.
reflexivity.
apply (led_transitivity (lambda j) (get j v) (nu j)).
apply (H j).
lia.
destruct (vali j).
lia.
left.
apply H3.
right.
apply H3.

intros.
cut (mem j q \/ ~ mem j q).
intro c.
destruct c.
left.
split.
apply H3.
cut (mem j x0 \/ mem j x1).
intro c.
destruct c.
cut (x<j).
intro comp.
destruct (vali j).
apply H2.
apply H5.
cut False.
tauto.
lia.
apply (axp_inter_aux2 k v x x0 x1).
split.
apply k_stable.
split.
apply Lv.
split.
apply H.
apply decomp_find.
apply H4.
destruct (vali j).
lia.
apply H5.
cut False.
tauto.
tauto.
cut ( mem j q).
rewrite defq.
apply mem_append.
auto.
right.
auto.
tauto.

(* k vl <> k vu *)
apply difg.

(* exists vl1 vl2 vl3 vl4 vu1 vu2 vu3 vu4 : T, ... *)
cut (
  (forall (e:nat), mem e x1 -> (e < x)) /\
  (forall (e:nat), mem e x0 -> (x < e)) /\
  (exists vl vu : list T,
  length vl = nb_feature /\
  length vu = nb_feature /\
  (forall j : nat,
   j >= 0 /\ j < nb_feature ->
   (mem j x1 \/ j > x) /\ get j vl = get j v /\ get j vu = get j v \/
   ~ (mem j x1 \/ j > x) /\ get j vl = lambda j /\ get j vu = nu j) /\
  k vl <> k vu)).
intro inter.
destruct inter as (inf,inter).
destruct inter as (sup,inter).
apply inter.
apply axp_inter.
apply k_stable.
split.
apply Lv.
apply H.
apply decomp_find.

generalize H0.
unfold is_minus_one.
auto.
Qed.


Theorem axp_all : forall (k : list T -> Tk) (v:list T),
stable k
-> (
length v = nb_feature
/\
(forall (j:nat), j>=0 /\ j< nb_feature -> 
  led (lambda j) (get j v) /\ led (get j v) (nu j))
-> is_AXp k v (findAXp k v)
).
Proof.
   intros.
   unfold is_AXp.
   split.
   apply minus_one_all_aux1.
   tauto.
   intro.
   apply (minus_one_implies_subset k v (findAXp k v)) .
   apply minus_one_all_aux2.
   tauto.
Qed.

(*******************************************************)
(*******************  CXp  *****************************)
(*******************************************************)


(* moche mais plus facil à manipuler en coq *)
(* La terminaison est évidente et la manipulation est plus simple qu'avec Programm Fixpoint *)
(* i = nb_feature-j *)
Fixpoint findCXp_aux_j (k : list T -> Tk) (j:nat) (v vl vu: list T) (p:list nat) {struct j}:
list nat :=
match j with
| 0 => p 
| S jmoins1 => 
  let '(nvl,nvu,np) := fixAttr (nb_feature-j) v vl vu p in
    match Tk_eq_dec (k nvl) (k nvu) with
    | true => let '(nvl,nvu) := freeAttr (nb_feature-j) nvl nvu in
               findCXp_aux_j k jmoins1 v nvl nvu np
    | false => findCXp_aux_j k jmoins1 v nvl nvu p
    end 
end.


Lemma findCXp_aux_j_spec2 :
 forall  (k : list T -> Tk) (j:nat) (v vl vu: list T) (p:list nat),
   j>0 
/\ ( let '(nvl,nvu,np) :=  fixAttr (nb_feature-j) v vl vu p in (k nvl) = (k nvu))
-> let '(nvl,nvu,np) :=  fixAttr (nb_feature-j) v vl vu p in let '(nnvl,nnvu) := freeAttr (nb_feature-j) nvl nvu in findCXp_aux_j k j v vl vu p = findCXp_aux_j k (j-1) v nnvl nnvu np.
Proof.
intros.
destruct H.
rewrite (surjective_pairing (fixAttr (nb_feature - j) v vl vu p)).
rewrite (surjective_pairing (fst (fixAttr (nb_feature - j) v vl vu p))).
rewrite (surjective_pairing (freeAttr (nb_feature - j) (fst (fst (fixAttr (nb_feature - j) v vl vu p)))
(snd (fst (fixAttr (nb_feature - j) v vl vu p))) )).
   
destruct j.
(* j=0 *)
lia.
(* j <> 0*)
simpl.
cut (j-0=j).
intro rj.
rewrite rj.
rewrite (surjective_pairing (fixAttr (nb_feature - S j) v vl vu p)).
rewrite (surjective_pairing (fst (fixAttr (nb_feature - S j) v vl vu p))).
cut ( Tk_eq_dec (k (fst (fst (fixAttr (nb_feature - S j) v vl vu p))))
(k (snd (fst (fixAttr (nb_feature - S j) v vl vu p)))) = true).
intro r2.
rewrite r2.
rewrite (surjective_pairing (freeAttr (nb_feature - S j)
(fst (fst (fixAttr (nb_feature - S j) v vl vu p)))
(snd (fst (fixAttr (nb_feature - S j) v vl vu p))))).
simpl.
reflexivity.
(* Tk_eq_dec *)
generalize H0.
rewrite (surjective_pairing (fixAttr (nb_feature - S j) v vl vu p)).
rewrite (surjective_pairing (fst (fixAttr (nb_feature - S j) v vl vu p))).
simpl.
apply Tk_eq_coherent_eq.
(* j-0 = j *)
lia.
Qed.


Lemma findCXp_aux_j_spec3 :
forall  (k : list T -> Tk) (j:nat) (v vl vu: list T) (p:list nat),
j>0 /\ ( let '(nvl,nvu,np) :=  fixAttr (nb_feature-j) v vl vu p in (k nvl) <> (k nvu))
-> let '(nvl,nvu,np) :=  fixAttr (nb_feature-j) v vl vu p in findCXp_aux_j k j v vl vu p = findCXp_aux_j k (j-1) v nvl nvu p.
Proof.
intros.
destruct H.
rewrite (surjective_pairing (fixAttr (nb_feature - j) v vl vu p)).
rewrite (surjective_pairing (fst (fixAttr (nb_feature - j) v vl vu p))).
destruct j.
(* j = 0 : 0>0 en hypothèse *)
lia.
(* j > 0 : cas général *)
simpl.
cut (j-0=j).
intro r3.
rewrite r3.
rewrite (surjective_pairing (fixAttr (nb_feature - S j) v vl vu p)).
rewrite (surjective_pairing (fst (fixAttr (nb_feature - S j) v vl vu p))).
 cut ( Tk_eq_dec (k (fst (fst (fixAttr (nb_feature - S j) v vl vu p))))
 (k (snd (fst (fixAttr (nb_feature - S j) v vl vu p)))) = false).
intro r2.
rewrite r2.
simpl.
reflexivity.
(* Tk_eq_dec *)
generalize H0.
rewrite (surjective_pairing (fixAttr (nb_feature - S j) v vl vu p)).
rewrite (surjective_pairing (fst (fixAttr (nb_feature - S j) v vl vu p))).
simpl.
apply Tk_eq_coherent_neq.
(* j-0 = j *)
lia.
Qed.



Definition findCXp_aux  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat):
list nat := findCXp_aux_j k (nb_feature-i) v vl vu p.


Lemma findCXp_aux_spec2 : 
forall  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),
i>= 0 /\ i < nb_feature 
/\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) = (k nvu))
-> let '(nvl,nvu,np) :=  fixAttr i v vl vu p in let '(nnvl,nnvu) := freeAttr i nvl nvu in findCXp_aux k i v vl vu p = findCXp_aux k (i+1) v nnvl nnvu np.
Proof.
intros.
destruct H.
destruct H0.
cut (exists j:nat, j= nb_feature - i).
intro.
destruct H2 as (j,H2).
cut (i = nb_feature - j).
intro ri.
rewrite ri.
unfold findCXp_aux.
cut (nb_feature - (nb_feature - j) = j).
intro rj.
rewrite rj.
cut (nb_feature - (nb_feature - j + 1) = j-1).
intro rjm1.
rewrite rjm1.
apply findCXp_aux_j_spec2.
split.
lia.
rewrite <- ri.
exact H1.
(* egalité *)
lia.
lia.
lia.
exists (nb_feature-i).
reflexivity.
Qed.

Lemma findCXp_aux_spec3 : 
forall  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),
i>= 0 /\ i < nb_feature 
/\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) <> (k nvu))
-> let '(nvl,nvu,np) :=  fixAttr i v vl vu p in  findCXp_aux k i v vl vu p = findCXp_aux k (i+1) v nvl nvu p.
Proof.
intros.
destruct H.
destruct H0.
cut (exists j:nat, j= nb_feature - i).
intro.
destruct H2 as (j,H2).
cut (i = nb_feature - j).
intro ri.
rewrite ri.
unfold findCXp_aux.
cut (nb_feature - (nb_feature - j ) = j).
intro rj.
rewrite rj.
cut (nb_feature - (nb_feature - j + 1) = j-1).
intro rjm1.
rewrite rjm1.
apply findCXp_aux_j_spec3.
split.
lia.
rewrite <- ri.
exact H1.
(* egalité *)
lia.
lia.
lia.
exists (nb_feature-i).
reflexivity.
Qed.



(* bad complexity but call once *)
Fixpoint feature_f (s:nat) (f : nat -> T): list T := 
   match s with
   | 0 => nil 
   | S smoins1 => (feature_f smoins1 f) ++ ((f smoins1)::nil)
   end.

Lemma size_feature_f : forall (s:nat) (f: nat -> T),
length (feature_f s f) = s.
Proof.
   induction s.
   (* s = 0 *)
   simpl.
   reflexivity.
   (* cas general *)
   intros.
   simpl.
   generalize (Coq.Lists.List.app_length (feature_f s f) (f s :: nil)).
   intro.
   rewrite H.
   simpl.
   rewrite IHs.
   lia.
Qed.

Lemma def_feature_f : forall (i:nat) (s:nat) (f : nat -> T),
0 <= i /\ i< s ->
get i (feature_f s f) = (f i).
Proof.
   induction s.
   (* s = O *)
   lia.
   (* cas general *)
   intros.
   cut (0<=i<s \/ i=s).
   intro di.
   destruct di.
   (* i<s *)
   simpl.
   cut (get i (feature_f s f ++ f s :: nil) = get i (feature_f s f)).
   intro.
   rewrite H1.
   apply IHs.
   apply H0.
   unfold get.
   cut (i < length (feature_f s f)).
   intro.
   apply (Coq.Lists.List.app_nth1 (feature_f s f) (f s :: nil) Exception H1).
   generalize (size_feature_f s).
   intro.
   rewrite H1.
   lia.
   (* i = s *)
   simpl.
   cut (get i (feature_f s f ++ f s :: nil) = get (i-(length (feature_f s f))) (f s :: nil)).
   intro.
   rewrite H1.
   generalize (size_feature_f s).
   intro.
   rewrite H2.
   rewrite H0.
   cut (s-s=0).
   intro.
   rewrite H3.
   simpl.
   unfold get.
   simpl.
   reflexivity.
   lia.
   cut (i >= (length (feature_f s f))).
   intro.
   apply (Coq.Lists.List.app_nth2 (feature_f s f) (f s :: nil) Exception H1).
   generalize (size_feature_f s).
   intro.
   rewrite H1.
   lia.
   lia.
Qed.
   

(* missing that it should be the smallest set *)  
Definition is_weak_CXp  (k : list T -> Tk) (v: list T) (p:list nat) : Prop :=
   exists (x: list T),
   List.length v = nb_feature
/\ List.length x = nb_feature
/\ (forall (j:nat), j>=0 /\ j< nb_feature -> (led (lambda j) (get j x) /\ led (get j x) (nu j))) 
/\ (forall (j:nat), j>=0 /\ j< nb_feature -> (((not (mem j p)) /\ get j x = get j v) \/  (mem j p)))
/\ not (k(x)=k(v)).


Definition R2_CXp  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat) : Prop :=
  k vl <> k vu.


Definition R6_CXp  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat) : Prop :=
   forall (j:nat),
   ((mem j p) -> ((get j vl = lambda j ) /\ (get j vu = nu j ))).
   
 Definition R7_CXp  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat) : Prop :=
   forall (j:nat),
  (j>=i /\ j>=0 /\ i>=0 /\ j<nb_feature /\ i<nb_feature) -> ((get j vl = lambda j) /\ (get j vu = nu j)).
  

Definition R9_CXp  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat) : Prop :=
  forall (j:nat),
  ( j<i /\ j>=0 /\ i>=0 /\ j<nb_feature /\ i<=nb_feature /\ not (mem j p)
  -> ((get j vl = get j v) /\ (get j vu = get j v))).
  
Definition R10_CXp  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat) : Prop :=
  forall (x:nat), forall (x0 x1 : list nat), 
  (p = x0++(x::x1)
-> 
exists (nvl nvu : list T),
length nvl = nb_feature /\
length nvu = nb_feature /\
(forall (j:nat), j>=0 /\ j< nb_feature 
  ->  ((mem j x1 \/ j>x) /\ get j nvl =lambda j /\ get j nvu =nu j) 
        \/ ( (not (mem j x1 \/ j>x)) /\ get j nvl=get j v /\ get j nvu =get j v) ) 
/\ (k nvl) = (k nvu)).



(* v pour feature < à i et pas dans p -- lambda/nu sinon *)
Fixpoint ln_i_v_aux_CXp (ind:nat) (i:nat) (s:nat) (v : list T) (ln : nat -> T) (p : list nat): list T  :=
   match s with
   | 0 => nil
   | S smoins1 => if (ind <? i)
          then if (mem_nat ind p)
               then (ln ind)::(ln_i_v_aux_CXp (ind+1) i smoins1 v ln p)
               else (get ind v)::(ln_i_v_aux_CXp (ind+1) i smoins1 v ln p)
          else (ln ind)::(ln_i_v_aux_CXp (ind+1) i smoins1 v ln p)
   end.

Definition ln_i_v_CXp (i:nat) (v : list T) (ln : nat -> T)  (p : list nat) : list T  := ln_i_v_aux_CXp 0 i (List.length v) v ln p.

Lemma get_i_zero_ln_i_v_aux_CXp : forall (s ind i j :nat) (v : list T) (ln : nat -> T)  (p : list nat),
i=0 /\ j>=0 /\ j <s -> get j (ln_i_v_aux_CXp ind i s v ln p) = ln (ind+j).
Proof.
   induction s.
   (* cas de base -> pas possible *)
   lia.
   (* cas général *)
   intros.
   simpl.
   cut (ind <? i = false).
   intro rt.
   rewrite rt.
   destruct j.
   (* j = 0 *)
   unfold get.
   simpl.
   cut (ind+0 = ind).
   intro r0.
   rewrite r0.
   reflexivity.
   lia.
   (* j<>0 *)
   unfold get.
   simpl.
   cut (ind + S j = ind + 1 + j).
   intro r1.
   rewrite r1.
   apply (IHs (ind+1) i j v).
   lia.
   lia.
   cut (not (ind <i)).
   rewrite <- Nat.ltb_lt.
   destruct ((ind <? i)).
   tauto.
   tauto.
   lia.
   Qed.

Lemma get_sup_i_ln_i_v_aux_CXp : forall (s ind i j :nat) (v : list T) (ln : nat -> T)  (p : list nat),
ind >= i /\ j>=0 /\ j <s -> get j (ln_i_v_aux_CXp ind i s v ln p) = ln (ind+j) .
Proof.
induction s.
(* cas de base -> pas possible *)
lia.
(* cas général *)
intros.
simpl.
cut (ind <? i = false).
intro rt.
rewrite rt.
destruct j.
(* j = 0 *)
unfold get.
simpl.
cut (ind+0 = ind).
intro r0.
rewrite r0.
reflexivity.
lia.
(* j<>0 *)
unfold get.
simpl.
cut (ind + S j = ind + 1 + j).
intro r1.
rewrite r1.
apply (IHs (ind+1) i j v).
lia.
lia.
cut (not (ind <i)).
rewrite <- Nat.ltb_lt.
destruct ((ind <? i)).
tauto.
tauto.
lia.
Qed.


Lemma get_sup_i_ln_i_v_aux_2_CXp : forall (s ind i j :nat) (v : list T) (ln : nat -> T)  (p : list nat),
ind < i /\ j<s/\  j>=(i-ind) -> get j (ln_i_v_aux_CXp ind i s v ln p) = ln (ind+j).
Proof.
  induction s.
  (* cas de base -> pas possible *)
  lia.
  (* cas général *)
  intros.
  simpl.
  cut (ind <? i = true).
  intro rt.
  rewrite rt.
  destruct j.
  (* j = 0 -> pas possible *)
  lia.
  (* j<>0 *)
  unfold get.
  simpl.
  cut (ind + S j = ind + 1 + j).
  intro r1.
  rewrite r1.
  cut (ind+1 <i \/ ind+1>=i).
  intro di.
  destruct di.
  (* ind + 1 < i *)
  destruct (mem_nat ind p).
  simpl.
  apply (IHs (ind+1) i j v ln p). 
  lia.
  apply (IHs (ind+1) i j v ln p). 
  lia.
  (* ind + 1 >= i *)
  destruct (mem_nat ind p).
  simpl.
  apply get_sup_i_ln_i_v_aux_CXp.
  lia.
  simpl.
  apply get_sup_i_ln_i_v_aux_CXp.
  lia.
  lia.
  lia.
  cut (ind <i).
  rewrite <- Nat.ltb_lt.
  tauto.
  lia.
Qed.


Lemma get_sup_i_ln_i_v_CXp : forall (ind:nat) (i:nat) (v : list T) (ln : nat -> T) (p : list nat),
ind >=0 /\ ind <(List.length v)  /\ ind >= i -> get ind (ln_i_v_CXp i v ln p) = ln ind .
Proof.
   intros.
   unfold ln_i_v_CXp.
   cut (i=0 \/ 0<i).
   intro.
   destruct H0.
   (* i = 0 *)
   apply (get_i_zero_ln_i_v_aux_CXp (List.length v) 0 i ind v ln p).
   lia.
   (* 0<i *)
   apply (get_sup_i_ln_i_v_aux_2_CXp (List.length v) 0 i ind v ln p).
   lia.
   lia.
Qed.


Lemma get_inf_mem_i_ln_i_v_aux_CXp : forall (s ind i j :nat) (v : list T) (ln : nat -> T) (p : list nat),
ind < i /\ j>=0 /\ j <s /\ j < (i-ind) /\ mem (ind+j) p-> get j (ln_i_v_aux_CXp ind i s v ln p) = ln (ind+j).
Proof.
  induction s.
  (* cas de base -> pas possible *)
  lia.
  (* cas général *)
  intros.
  simpl.
  cut (ind <? i = true).
  intro rt.
  rewrite rt.
  destruct j.
  (* j = 0 *)
  unfold get.
  simpl.
  cut (ind+0 = ind).
  intro r0.
  rewrite r0.
  cut (mem_nat ind p=true \/ mem_nat ind p=false).
  intro d.
  destruct d.
  rewrite H0.
  reflexivity.
  cut False.
  tauto.
  destruct H.
  destruct H1.
  destruct H2.
  destruct H3.
  rewrite r0 in H4.
  generalize H4.
  rewrite <- mem_coherent.
  rewrite H0.
  discriminate.
  destruct (mem_nat ind p).
  auto.
  auto.
  lia.
  (* j<>0 *)
  unfold get.
  cut (mem_nat ind p=true \/ mem_nat ind p=false).
  intro d.
  destruct d.
  rewrite H0.
  simpl.
  cut (ind + S j = ind + 1 + j).
  intro r1.
  rewrite r1.
  apply (IHs (ind+1) i j v ln p).
  rewrite r1 in H.
  repeat split ;[lia|lia|lia|lia|apply H].
  lia.
  rewrite H0.
  simpl.
  cut (ind + S j = ind + 1 + j).
  intro r1.
  rewrite r1.
  apply (IHs (ind+1) i j v ln p).
  rewrite r1 in H.
  repeat split ;[lia|lia|lia|lia|apply H].
  lia.
  destruct (mem_nat ind p).
  auto.
  auto.
  cut (ind < i).
  apply Nat.ltb_lt.
  apply H.
Qed.

Lemma get_inf_mem_i_ln_i_v_CXp : forall (ind:nat) (i:nat) (v : list T) (ln : nat -> T) (p : list nat),
ind >=0 /\ ind <(List.length v)  /\ ind < i /\ mem ind p -> get ind (ln_i_v_CXp i v ln p) = ln ind.
Proof.
   intros.
   unfold ln_i_v_CXp.
   apply (get_inf_mem_i_ln_i_v_aux_CXp (List.length v) 0 i ind v ln p).
   cut (0+ind = ind).
   intro rind.
   repeat split ; [lia|lia|lia|lia|apply H].
   lia.
Qed.


Lemma get_inf_not_mem_i_ln_i_v_aux_CXp : forall (s ind i j :nat) (v : list T) (ln : nat -> T) (p : list nat),
ind < i /\ j>=0 /\ j <s /\ j < (i-ind) /\ ~mem (ind+j) p-> get j (ln_i_v_aux_CXp ind i s v ln p) = get (ind+j) v.
Proof.
  induction s.
  (* cas de base -> pas possible *)
  lia.
  (* cas général *)
  intros.
  simpl.
  cut (ind <? i = true).
  intro rt.
  rewrite rt.
  destruct j.
  (* j = 0 *)
  unfold get.
  simpl.
  cut (ind+0 = ind).
  intro r0.
  rewrite r0.
  cut (mem_nat ind p=true \/ mem_nat ind p=false).
  intro d.
  destruct d.

  cut False.
  tauto.
  destruct H.
  destruct H1.
  destruct H2.
  destruct H3.
  rewrite r0 in H4.
  generalize H4.
  rewrite <- mem_coherent.
  rewrite H0.
  auto.

  rewrite H0.
  reflexivity.

  destruct (mem_nat ind p).
  auto.
  auto.

  lia.
  (* j<>0 *)
  unfold get.
  cut (mem_nat ind p=true \/ mem_nat ind p=false).
  intro d.
  destruct d.
  rewrite H0.
  simpl.
  cut (ind + S j = ind + 1 + j).
  intro r1.
  rewrite r1.
  apply (IHs (ind+1) i j v ln p).
  rewrite r1 in H.
  repeat split ;[lia|lia|lia|lia|apply H].
  lia.
  rewrite H0.
  simpl.
  cut (ind + S j = ind + 1 + j).
  intro r1.
  rewrite r1.
  apply (IHs (ind+1) i j v ln p).
  rewrite r1 in H.
  repeat split ;[lia|lia|lia|lia|apply H].
  lia.
  destruct (mem_nat ind p).
  auto.
  auto.
  cut (ind < i).
  apply Nat.ltb_lt.
  apply H.
Qed.


Lemma get_inf_not_mem_i_ln_i_v_CXp : forall (ind:nat) (i:nat) (v : list T) (ln : nat -> T) (p : list nat),
ind >=0 /\ ind <(List.length v)  /\ ind < i /\ ~ mem ind p -> get ind (ln_i_v_CXp i v ln p) = get ind v.
Proof.
   intros.
   unfold ln_i_v_CXp.
   apply (get_inf_not_mem_i_ln_i_v_aux_CXp (List.length v) 0 i ind v ln p).
   cut (0+ind = ind).
   intro rind.
   repeat split ; [lia|lia|lia|lia|apply H].
   lia.
Qed.

Lemma length_ln_i_v_aux_CXp : forall (s ind i :nat) (v : list T) (ln : nat -> T) (p : list nat), length (ln_i_v_aux_CXp ind i s v ln p) = s.
Proof.
   induction s.
   simpl.
   auto.
   intros.
   simpl.
   cut (ind <? i=true \/ ind <? i=false).
   intro c.
   destruct c.
   rewrite H.
   cut (mem_nat ind p=true \/ mem_nat ind p=false).
   intro d.
   destruct d.
   rewrite H0.
   simpl.
   generalize (IHs (ind+1) i v ln p).
   auto.
   rewrite H0.
   simpl.
   generalize (IHs (ind+1) i v ln p).
   auto.
   destruct (mem_nat ind p).
   auto.
   auto.
   rewrite H.
   simpl.
   generalize (IHs (ind+1) i v).
   auto.
   cut (ind < i \/ ind >= i).
   intro c.
   destruct c.
   left.
   apply Nat.leb_le.
   apply H.
   right.
   cut (not (ind <i)).
   rewrite <- Nat.ltb_lt.
   destruct ((ind <? i)).
   tauto.
   tauto.
   lia.
   lia.
Qed.

Lemma length_ln_i_v_CXp : forall (i :nat) (v : list T) (ln : nat -> T) (p : list nat), length (ln_i_v_CXp i v ln p) = (length v).
Proof.
   intros.
   unfold ln_i_v.
   apply length_ln_i_v_aux_CXp.
Qed.

Lemma get_ln_i_v_CXp : forall (i :nat) (v : list T) (ln : nat -> T) (p : list nat),
forall (j:nat), j>=0 /\ j < (List.length v) -> (get j (ln_i_v_CXp i v ln p) = get j v \/ get j (ln_i_v_CXp i v ln p) = ln j).
Proof.
   intros.
   cut (j>=i \/ (j<i /\ mem j p) \/ (j<i /\ ~mem j p)).
   intro d.
   destruct d.
   right.
   apply (get_sup_i_ln_i_v_CXp j i v ln p).
   lia.
   destruct H0.
   right.
   apply (get_inf_mem_i_ln_i_v_CXp j i v ln p).
   tauto.
   left.
   apply (get_inf_not_mem_i_ln_i_v_CXp j i v ln p).
   tauto.
   cut (j >= i \/ j < i).
   intro.
   destruct H0.
   tauto.
   cut (mem j p \/ ~ mem j p).
   intro.
   right.
   tauto.
   tauto.
   lia.
Qed.



Lemma preserveR0Cas2_CXp : 
   forall  (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) = (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R0 k (i + 1) v
   (fst
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p)))))
  (snd
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p))))) (snd (fixAttr i v vl vu p)) .
Proof.
   intros. 
   unfold R0.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.

   cut (exists (nvl nvu : list T) (np : list nat), fixAttr i v vl vu p = (nvl,nvu,np)).
   intro varfix.
   destruct varfix as (nvl,varfix).
   destruct varfix as (nvu,varfix).
   destruct varfix as (np,varfix).
   rewrite varfix.
   simpl.

   (* Start of the proof *)
   split.
   apply HR0.
   apply (free_size nb_feature i nvl nvu).
   
   cut (nvl = fst(fst (fixAttr i v vl vu p))).
   intro rvl.
   rewrite rvl.
   cut (nvu = snd (fst (fixAttr i v vl vu p))).
   intro rvu.
   rewrite rvu.

   split.
   apply (fix_size nb_feature i v  vl vu p).
   split. lia. split. apply Hi_sup. apply HR0.
   apply (fix_size nb_feature i v  vl vu p).
   split. lia. split. apply Hi_sup. apply HR0.
   rewrite varfix. simpl. reflexivity.
   rewrite varfix. simpl. reflexivity.

   (* Proof of exists *)
   destruct (fixAttr i v vl vu p ).
   destruct p0.
   exists l0.
   exists l1.
   exists l.
   reflexivity.
Qed.

Lemma preserveR1Cas2_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) = (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R1 k (i + 1) v
   (fst
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p)))))
  (snd
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p))))) (snd (fixAttr i v vl vu p)) .
Proof.
   intros. 
   unfold R1.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.
   unfold R1 in HR1.

   cut (exists (nvl nvu : list T) (np : list nat), fixAttr i v vl vu p = (nvl,nvu,np)).
   intro varfix.
   destruct varfix as (nvl,varfix).
   destruct varfix as (nvu,varfix).
   destruct varfix as (np,varfix).
   rewrite varfix.
   simpl.

   cut (exists (nnvl nnvu : list T), freeAttr i nvl nvu = (nnvl,nnvu)).
   intro varfree.
   destruct varfree as (nnvl,varfree).
   destruct varfree as (nnvu,varfree).
   rewrite varfree.
   simpl.

   cut (length nvl = nb_feature /\ length nvu = nb_feature).
   intro L.
   destruct L as (Lnvl,Lnvu).


   (*** Start of the proof ***)
   intros.
   split.
   apply (HR1 j H).
   split.
   apply (HR1 j H).
   cut (i >= 0 /\
   i < nb_feature /\
   length nvl = nb_feature /\
   length nvu = nb_feature /\
   (forall j0 : nat,
    j0 >= 0 /\ j0 < nb_feature ->
    led (lambda j0) (get j0 nvl) /\
    led (get j0 nvl) (nu j0) /\
    led (lambda j0) (get j0 nvu) /\ led (get j0 nvu) (nu j0)) /\
   freeAttr i nvl nvu = (nnvl, nnvu)).
   intro.
   split.
   generalize (borne_free nb_feature i nvl nvu nnvl nnvu H0 j).
   intros.
   apply (H1 H).
   split.
   generalize (borne_free nb_feature i nvl nvu nnvl nnvu H0 j).
   intros.
   apply (H1 H).
   generalize (borne_free nb_feature i nvl nvu nnvl nnvu H0 j).
   intros.
   apply (H1 H).
   (* preuve du gros cut *)
   split.
   apply Hi_inf.
   split.
   apply Hi_sup.
   split.
   apply Lnvl.
   split.
   apply Lnvu.
   cut (i >= 0 /\
   i < nb_feature /\
   length v = nb_feature /\
   length vl = nb_feature /\
   length vu = nb_feature /\
   (forall j0 : nat,
    j0 >= 0 /\ j0 < nb_feature ->
    led (lambda j0) (get j0 v) /\
    led (get j0 v) (nu j0) /\
    led (lambda j0) (get j0 vl) /\
    led (get j0 vl) (nu j0) /\
    led (lambda j0) (get j0 vu) /\ led (get j0 vu) (nu j0)) /\
   fixAttr i v vl vu p = (nvl, nvu, np)).
   intros.
   split.
   intro.
   generalize (borne_fix nb_feature i v vl vu p nvl nvu np H0 j0).
   intros.
   apply (H1 H2).
   apply varfree.
   (* preuve du second gros cut *)
   split.
   apply Hi_inf.
   split.
   apply Hi_sup.
   split.
   apply HR0.
   split.
   apply HR0.
   split.
   apply HR0.
   split.
   apply HR1.
   apply varfix.


   (*** End of the proof ***)
   (* Proof of size *)
   apply (preserveSize_CXp i v vl vu nvl nvu p np).
   repeat split ; [apply Hi_inf | apply Hi_sup| apply HR0 | apply HR0 | apply HR0 | apply varfix].

   (* Proof of exists free *)
   destruct (freeAttr i nvl nvu).
   exists l.
   exists l0.
   reflexivity.

    (* Proof of exists fix *)
   destruct (fixAttr i v vl vu p ).
   destruct p0.
   exists l0.
   exists l1.
   exists l.
   reflexivity.
Qed.


Lemma preserveR2Cas2_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) = (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R2_CXp k (i + 1) v
   (fst
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p)))))
  (snd
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p))))) (snd (fixAttr i v vl vu p)) .
Proof.

intros. 
unfold R2_CXp.
destruct H as (Hi_inf,H).
destruct H as (Hi_sup,H).
destruct H as (Hdif_k,H).
destruct H as (HR0,H).
destruct H as (HR1,H).
destruct H as (HR2,H).
destruct H as (HR3,H).
destruct H as (HR5,H).
destruct H as (HR6,H).
destruct H as (HR7,H).
destruct H as (HR8,H).
destruct H as (HR9,HR10).
unfold R2_CXp in HR2.

cut (exists (nvl nvu : list T) (np : list nat), fixAttr i v vl vu p = (nvl,nvu,np)).
intro varfix.
destruct varfix as (nvl,varfix).
destruct varfix as (nvu,varfix).
destruct varfix as (np,varfix).
rewrite varfix.
simpl.

cut (exists (nnvl nnvu : list T), freeAttr i nvl nvu = (nnvl,nnvu)).
intro varfree.
destruct varfree as (nnvl,varfree).
destruct varfree as (nnvu,varfree).
rewrite varfree.
simpl.

cut (length nvl = nb_feature /\ length nvu = nb_feature).
intro L.
destruct L as (Lnvl,Lnvu).

cut (length nnvl = nb_feature /\ length nnvu = nb_feature).
intro Ln.
destruct Ln as (Lnnvl,Lnnvu).

(*** Start of the proof ***)
   (* cut de nnvl = vl et nnvu = vu *)
   cut (nnvl=vl).
   intro rnnvl.
   rewrite rnnvl.
   cut (nnvu=vu).
   intro rnnvu.
   rewrite rnnvu.
   apply HR2.

   (* nnvu = vu *)
   apply id_list_aux.
      split.
      (* length nnvu = length vu *)
      rewrite Lnnvu.
      symmetry.
      apply HR0.
      (* get égaux *)
      intros.
      cut (i0=i \/ i0 <> i).
      intro di.
      destruct di.
        (* i0=i *)
        cut (get i0 nnvu = nu i0).
        intro rv.
        rewrite rv.
        cut (get i0 vu = nu i0).
        intro rv_2.
        rewrite rv_2.
        reflexivity.
           (* get i0 vu = nu i0 *)
           unfold R7_CXp in HR7.
           apply (HR7 i0).
           lia.
           (* get i0 nnvu = nu i0 *)
           rewrite H0.
           apply (free_i nb_feature i nvl nvu nnvl nnvu).
           repeat split; [lia|lia|lia|apply varfree|apply Lnvl|apply Lnvu].
        (* i0 <> i *)
        cut (get i0 nnvu = get i0 nvu).
        intro rv.
        rewrite rv.
        cut (get i0 vu = get i0 nvu).
        intro rv_2.
        rewrite rv_2.
        reflexivity.
          (* get i0 vu = get i0 nvu *)
         apply (fix_get nb_feature i i0 v vl vu p nvl nvu np).
         repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfix].
          (* get i0 nnvu = get i0 nvu *)
          symmetry.
          apply (free_get nb_feature i i0 nvl nvu nnvl nnvu).
          repeat split; [lia | lia | lia | lia | lia | apply varfree| apply Lnvl | apply Lnvu].
      lia.
   (* nnvl = vl *)
   apply id_list_aux.
      split.
      (* length nnl v= length vl *)
      rewrite Lnnvl.
      symmetry.
      apply HR0.
      (* get égaux *)
      intros.
      cut (i0=i \/ i0 <> i).
      intro di.
      destruct di.
        (* i0=i *)
        cut (get i0 nnvl = lambda i0).
        intro rv.
        rewrite rv.
        cut (get i0 vl = lambda i0).
        intro rv_2.
        rewrite rv_2.
        reflexivity.
           (* get i0 vl = lambda i0 *)
           unfold R7_CXp in HR7.
           apply (HR7 i0).
           lia.
           (* get i0 nnvl = lambda i0 *)
           rewrite H0.
           apply (free_i nb_feature i nvl nvu nnvl nnvu).
           repeat split; [lia|lia|lia|apply varfree|apply Lnvl|apply Lnvu].
        (* i0 <> i *)
        cut (get i0 nnvl = get i0 nvl).
        intro rv.
        rewrite rv.
        cut (get i0 vl = get i0 nvl).
        intro rv_2.
        rewrite rv_2.
        reflexivity.
          (* get i0 vl = get i0 nvl *)
         apply (fix_get nb_feature i i0 v vl vu p nvl nvu np).
         repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfix].
          (* get i0 nnvl = get i0 nvl *)
          symmetry.
          apply (free_get nb_feature i i0 nvl nvu nnvl nnvu).
          repeat split; [lia | lia | lia | lia | lia | apply varfree| apply Lnvl | apply Lnvu].
  lia.

   (*** End of the proof ***)
   generalize (free_size nb_feature i nvl nvu).
   rewrite varfree.
   simpl.
   auto.

   (* Proof of size *)
   apply (preserveSize_CXp i v vl vu nvl nvu p np).
   repeat split ; [apply Hi_inf | apply Hi_sup| apply HR0 | apply HR0 | apply HR0 | apply varfix].

   (* Proof of exists free *)
   destruct (freeAttr i nvl nvu).
   exists l.
   exists l0.
   reflexivity.

    (* Proof of exists fix *)
   destruct (fixAttr i v vl vu p ).
   destruct p0.
   exists l0.
   exists l1.
   exists l.
   reflexivity.
Qed.

Lemma preserveR3Cas2_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) = (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R3 k (i + 1) v
   (fst
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p)))))
  (snd
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p))))) (snd (fixAttr i v vl vu p)) .
Proof.
intros.
unfold R3.
unfold R3 in H.
lia.
Qed.


Lemma preserveR5Cas2_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) = (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R5 k (i + 1) v
   (fst
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p)))))
  (snd
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p))))) (snd (fixAttr i v vl vu p)) .
Proof.
   intros. 
   unfold R5.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R5 in HR5.

   cut (exists (nvl nvu : list T) (np : list nat), fixAttr i v vl vu p = (nvl,nvu,np)).
   intro varfix.
   destruct varfix as (nvl,varfix).
   destruct varfix as (nvu,varfix).
   destruct varfix as (np,varfix).
   rewrite varfix.
   simpl.

   cut (exists (nnvl nnvu : list T), freeAttr i nvl nvu = (nnvl,nnvu)).
   intro varfree.
   destruct varfree as (nnvl,varfree).
   destruct varfree as (nnvu,varfree).

   cut (length nvl = nb_feature /\ length nvu = nb_feature).
   intro L.
   destruct L as (Lnvl,Lnvu).


   (*** Start of the proof ***)
intros.

cut (np = i::p).
intro rnp.
rewrite rnp.
simpl.
intro.
destruct H0.
lia.
cut (~ mem j p).
tauto.
apply (HR5 j).
lia.
apply (fix_p i v vl vu p nvl nvu np).
apply varfix.

   (*** End of the proof ***)
   (* Proof of size *)
   apply (preserveSize_CXp i v vl vu nvl nvu p np).
   repeat split ; [apply Hi_inf | apply Hi_sup| apply HR0 | apply HR0 | apply HR0 | apply varfix].

   (* Proof of exists free *)
   destruct (freeAttr i nvl nvu).
   exists l.
   exists l0.
   reflexivity.

    (* Proof of exists fix *)
   destruct (fixAttr i v vl vu p ).
   destruct p0.
   exists l0.
   exists l1.
   exists l.
   reflexivity.
Qed.

Lemma preserveR6Cas2_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) = (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R6_CXp k (i + 1) v
   (fst
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p)))))
  (snd
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p))))) (snd (fixAttr i v vl vu p)) .
Proof.
intros. 
unfold R6_CXp.
destruct H as (Hi_inf,H).
destruct H as (Hi_sup,H).
destruct H as (Hdif_k,H).
destruct H as (HR0,H).
destruct H as (HR1,H).
destruct H as (HR2,H).
destruct H as (HR3,H).
destruct H as (HR5,H).
destruct H as (HR6,H).
destruct H as (HR7,H).
destruct H as (HR8,H).
destruct H as (HR9,HR10).
unfold R5 in HR5.
unfold R6_CXp in HR6.

cut (exists (nvl nvu : list T) (np : list nat), fixAttr i v vl vu p = (nvl,nvu,np)).
intro varfix.
destruct varfix as (nvl,varfix).
destruct varfix as (nvu,varfix).
destruct varfix as (np,varfix).
rewrite varfix.
simpl.

cut (exists (nnvl nnvu : list T), freeAttr i nvl nvu = (nnvl,nnvu)).
intro varfree.
destruct varfree as (nnvl,varfree).
destruct varfree as (nnvu,varfree).
rewrite varfree.
simpl.

cut (length nvl = nb_feature /\ length nvu = nb_feature).
intro L.
destruct L as (Lnvl,Lnvu).


(*** Start of the proof ***)
intros.
cut (j=i \/ mem j p).
intro d.
destruct d.
(* j=i *)
rewrite H0.
apply (free_i nb_feature i nvl nvu nnvl nnvu).
repeat split; [lia | lia | lia | apply varfree | apply Lnvl | apply Lnvu ].

(* mem j p -> j<i (contraposé de HR5) -> nnvlj = vlj (frix_free_id) ->  (HR6) *)
(* D'abord des hypothèse liés à la contraposée de HR5 *)
cut (j<i /\ j >= 0 /\ j < nb_feature).
intro.
(* preuve en elle même*)
cut (j<>i).
intro difij.
cut (get j nnvl = get j vl).
intro r1.
rewrite r1.
cut (get j nnvu = get j vu).
intro r2.
rewrite r2.
apply HR6.
tauto.
(* get j nnvu = get j vu *)
apply (fix_free_id nb_feature i j v vl vu nvl nvu p nnvl nnvu np).
repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfix | apply varfree].
(* get j nnvl = get j vl *)
apply (fix_free_id nb_feature i j v vl vu nvl nvu p nnvl nnvu np).
repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfix | apply varfree].
(* j<>i *)
cut (j >= 0 /\ j < nb_feature).
lia.
lia.

(* contraposée de HR5 *)
cut (mem j p -> (j < i /\ j >= 0 /\ j < nb_feature)).
intro.
apply H1.
tauto.
cut (~~mem j p ->  ~(j >= i \/ j < 0 \/ j >= nb_feature)).
intros.
cut (~(j >= i \/ j < 0 \/ j >= nb_feature)).
lia.
apply H1.
tauto.
generalize (HR5 j).
apply contrapose.

(* j=i \/ mem j p*)
generalize H.
cut (np = i::p).
intro rnp.
rewrite rnp.
simpl.
auto.
apply (fix_p i v vl vu p nvl nvu np).
apply varfix.


   (*** End of the proof ***)
   (* Proof of size *)
   apply (preserveSize_CXp i v vl vu nvl nvu p np).
   repeat split ; [apply Hi_inf | apply Hi_sup| apply HR0 | apply HR0 | apply HR0 | apply varfix].

   (* Proof of exists free *)
   destruct (freeAttr i nvl nvu).
   exists l.
   exists l0.
   reflexivity.

    (* Proof of exists fix *)
   destruct (fixAttr i v vl vu p ).
   destruct p0.
   exists l0.
   exists l1.
   exists l.
   reflexivity.
Qed.


Lemma preserveR7Cas2_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) = (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R7_CXp k (i + 1) v
   (fst
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p)))))
  (snd
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p))))) (snd (fixAttr i v vl vu p)) .
Proof.
intros. 
unfold R7_CXp.
destruct H as (Hi_inf,H).
destruct H as (Hi_sup,H).
destruct H as (Hdif_k,H).
destruct H as (HR0,H).
destruct H as (HR1,H).
destruct H as (HR2,H).
destruct H as (HR3,H).
destruct H as (HR5,H).
destruct H as (HR6,H).
destruct H as (HR7,H).
destruct H as (HR8,H).
destruct H as (HR9,HR10).
unfold R7_CXp in HR7.

cut (exists (nvl nvu : list T) (np : list nat), fixAttr i v vl vu p = (nvl,nvu,np)).
intro varfix.
destruct varfix as (nvl,varfix).
destruct varfix as (nvu,varfix).
destruct varfix as (np,varfix).
rewrite varfix.
simpl.

cut (exists (nnvl nnvu : list T), freeAttr i nvl nvu = (nnvl,nnvu)).
intro varfree.
destruct varfree as (nnvl,varfree).
destruct varfree as (nnvu,varfree).
rewrite varfree.
simpl.

cut (length nvl = nb_feature /\ length nvu = nb_feature).
intro L.
destruct L as (Lnvl,Lnvu).


(*** Start of the proof ***)
intros.
cut (j<>i /\ ~ mem j p).
intro.
cut (get j nnvl = get j vl).
intro rnnvl.
rewrite rnnvl.
cut (get j nnvu = get j vu).
intro rnnvu.
rewrite rnnvu.
apply (HR7 j).
lia.
(* get j nnvu = get j vu *)
apply (fix_free_id nb_feature i j v vl vu nvl nvu p nnvl nnvu np).
repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfix | apply varfree].
(* get j nnvl = get j vl *)
apply (fix_free_id nb_feature i j v vl vu nvl nvu p nnvl nnvu np).
repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfix | apply varfree].
(* j <> i /\ ~ mem j p *)
split.
lia.
apply HR5.
lia.

   (*** End of the proof ***)
   (* Proof of size *)
   apply (preserveSize_CXp i v vl vu nvl nvu p np).
   repeat split ; [apply Hi_inf | apply Hi_sup| apply HR0 | apply HR0 | apply HR0 | apply varfix].

   (* Proof of exists free *)
   destruct (freeAttr i nvl nvu).
   exists l.
   exists l0.
   reflexivity.

    (* Proof of exists fix *)
   destruct (fixAttr i v vl vu p ).
   destruct p0.
   exists l0.
   exists l1.
   exists l.
   reflexivity.
Qed.




Lemma preserveR8Cas2_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) = (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R8 k (i + 1) v
   (fst
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p)))))
  (snd
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p))))) (snd (fixAttr i v vl vu p)) .
Proof.
   intros. 
   unfold R8.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R8 in HR8.

   cut (exists (nvl nvu : list T) (np : list nat), fixAttr i v vl vu p = (nvl,nvu,np)).
   intro varfix.
   destruct varfix as (nvl,varfix).
   destruct varfix as (nvu,varfix).
   destruct varfix as (np,varfix).
   rewrite varfix.
   simpl.

   cut (exists (nnvl nnvu : list T), freeAttr i nvl nvu = (nnvl,nnvu)).
   intro varfree.
   destruct varfree as (nnvl,varfree).
   destruct varfree as (nnvu,varfree).

   cut (length nvl = nb_feature /\ length nvu = nb_feature).
   intro L.
   destruct L as (Lnvl,Lnvu).

   (*** Start of the proof ***)
cut (np=i::p).
intro rnp.
rewrite rnp.
simpl.
split.
(* forall e : nat, mem e p -> i > e *)
intros.
(* D'abord des hypothèse liés à la contraposée de HR5 *)
unfold R5 in HR5.
cut (e<i /\ e >= 0 /\ e < nb_feature).
intro.
tauto.
(* contraposée de HR5 *)
cut (mem e p -> (e < i /\ e >= 0 /\ e < nb_feature)).
intro CHR5.
apply CHR5.
tauto.
cut (~~mem e p ->  ~(e >= i \/ e < 0 \/ e >= nb_feature)).
intros.
cut (~(e >= i \/ e < 0 \/ e >= nb_feature)).
lia.
apply H0.
tauto.
generalize (HR5 e).
apply contrapose.
(* is_sorted p *)
tauto.
(* np = i :: p *)
apply (fix_p i v vl vu p nvl nvu np).
apply varfix.


   (*** End of the proof ***)
   (* Proof of size *)
   apply (preserveSize_CXp i v vl vu nvl nvu p np).
   repeat split ; [apply Hi_inf | apply Hi_sup| apply HR0 | apply HR0 | apply HR0 | apply varfix].

   (* Proof of exists free *)
   destruct (freeAttr i nvl nvu).
   exists l.
   exists l0.
   reflexivity.

    (* Proof of exists fix *)
   destruct (fixAttr i v vl vu p ).
   destruct p0.
   exists l0.
   exists l1.
   exists l.
   reflexivity.
Qed.


Lemma preserveR9Cas2_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) = (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R9_CXp k (i + 1) v
   (fst
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p)))))
  (snd
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p))))) (snd (fixAttr i v vl vu p)) .
Proof.
intros. 
unfold R9_CXp.
destruct H as (Hi_inf,H).
destruct H as (Hi_sup,H).
destruct H as (Hdif_k,H).
destruct H as (HR0,H).
destruct H as (HR1,H).
destruct H as (HR2,H).
destruct H as (HR3,H).
destruct H as (HR5,H).
destruct H as (HR6,H).
destruct H as (HR7,H).
destruct H as (HR8,H).
destruct H as (HR9,HR10).
unfold R9_CXp in HR9.

cut (exists (nvl nvu : list T) (np : list nat), fixAttr i v vl vu p = (nvl,nvu,np)).
intro varfix.
destruct varfix as (nvl,varfix).
destruct varfix as (nvu,varfix).
destruct varfix as (np,varfix).
rewrite varfix.
simpl.

cut (exists (nnvl nnvu : list T), freeAttr i nvl nvu = (nnvl,nnvu)).
intro varfree.
destruct varfree as (nnvl,varfree).
destruct varfree as (nnvu,varfree).
rewrite varfree.
simpl.

cut (length nvl = nb_feature /\ length nvu = nb_feature).
intro L.
destruct L as (Lnvl,Lnvu).

(*** Start of the proof ***)

intros.
cut (i<>j).
intro.
cut (get j nnvl = get j vl).
intro rnnvl.
rewrite rnnvl.
cut (get j nnvu = get j vu).
intro rnnvu.
rewrite rnnvu.
apply HR9.
cut ( ~ mem j p).
repeat split ; [lia|lia|lia|lia|lia|auto].
(* ~ mem j p *)
cut (np = i::p).
intro.
rewrite H1 in H.
generalize H.
simpl.
tauto.
(* np=i::p *)
apply (fix_p i v vl vu p nvl nvu np varfix).
(* get j nnvu = get j vu *)
apply (fix_free_id nb_feature i j v vl vu nvl nvu p nnvl nnvu np).
repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfix | apply varfree].
(* get j nnvl = get j vl *)
apply (fix_free_id nb_feature i j v vl vu nvl nvu p nnvl nnvu np).
repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfix | apply varfree].

(* i<>j *)
cut (np = i::p).
intro.
rewrite H0 in H.
generalize H.
simpl.
lia.
(* np=i::p *)
apply (fix_p i v vl vu p nvl nvu np varfix).

   (*** End of the proof ***)
   (* Proof of size *)
   apply (preserveSize_CXp i v vl vu nvl nvu p np).
   repeat split ; [apply Hi_inf | apply Hi_sup| apply HR0 | apply HR0 | apply HR0 | apply varfix].

   (* Proof of exists free *)
   destruct (freeAttr i nvl nvu).
   exists l.
   exists l0.
   reflexivity.

    (* Proof of exists fix *)
   destruct (fixAttr i v vl vu p ).
   destruct p0.
   exists l0.
   exists l1.
   exists l.
   reflexivity.
Qed.


Lemma preserveR10Cas2_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) = (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R10_CXp k (i + 1) v
   (fst
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p)))))
  (snd
     (freeAttr i (fst (fst (fixAttr i v vl vu p)))
        (snd (fst (fixAttr i v vl vu p))))) (snd (fixAttr i v vl vu p)) .
Proof.
intros.
unfold R10_CXp.
destruct H as (Hi_inf,H).
destruct H as (Hi_sup,H).
destruct H as (Hdif_k,H).
destruct H as (HR0,H).
destruct H as (HR1,H).
destruct H as (HR2,H).
destruct H as (HR3,H).
destruct H as (HR5,H).
destruct H as (HR6,H).
destruct H as (HR7,H).
destruct H as (HR8,H).
destruct H as (HR9,HR10).
unfold R10_CXp in HR10.
unfold R0 in HR0.
unfold R5 in HR5.
unfold R6_CXp in HR6.
unfold R7_CXp in HR7.
unfold R9_CXp in HR9.

cut (exists (nvl nvu : list T) (np : list nat), fixAttr i v vl vu p = (nvl,nvu,np)).
intro varfix.
destruct varfix as (nvl,varfix).
destruct varfix as (nvu,varfix).
destruct varfix as (np,varfix).
rewrite varfix.
simpl.

cut (exists (nnvl nnvu : list T), freeAttr i nvl nvu = (nnvl,nnvu)).
intro varfree.
destruct varfree as (nnvl,varfree).
destruct varfree as (nnvu,varfree).

cut (length nvl = nb_feature /\ length nvu = nb_feature).
intro L.
destruct L as (Lnvl,Lnvu).

(*** Start of the proof ***)
cut (np = i::p).
intro rnp.
rewrite rnp.

intros.

destruct p. (* car si p est vide pas possible d'utiliser la précondition *)
(* p=nil *)
cut (x1=nil).
intro defx1.
rewrite defx1.
cut (x=i).
intro defxi.
rewrite defxi.
simpl.

(* lambda / nu pour feature <= à i et v pour >i *)
exists (ln_i_v_CXp (i+1) v lambda nil). (* i+1 pour que à i il y ait vi *)
exists (ln_i_v_CXp (i+1) v nu nil).
split.
rewrite (length_ln_i_v_CXp ).
apply HR0.
split.
rewrite (length_ln_i_v_CXp).
apply HR0. 
split.
intros.
cut (j>i \/ j<=i).
intro dj.
destruct dj.
(* j > 1 *)
left.
split.
auto.
split.
apply get_sup_i_ln_i_v_CXp.
lia.
apply get_sup_i_ln_i_v_CXp.
lia.
(* j <= i *)
right.
split.
lia.
split.
apply get_inf_not_mem_i_ln_i_v_CXp.
repeat split ; [lia|lia|lia|simpl;auto].
apply get_inf_not_mem_i_ln_i_v_CXp.
repeat split ; [lia|lia|lia|simpl;auto].

(* j > i \/ j <= i  *)
lia.

(* k (ln_i_v_CXp (i + 1) v lambda nil) = k (ln_i_v_CXp (i + 1) v nu nil) *)
generalize Hdif_k.
rewrite (surjective_pairing (fixAttr i v vl vu nil)).
rewrite (surjective_pairing (fst (fixAttr i v vl vu nil))).
rewrite varfix.
simpl.

cut (nvl = ln_i_v_CXp (i + 1) v lambda nil /\ nvu = ln_i_v_CXp (i + 1) v nu nil).
intro defnvlu.
destruct defnvlu as (defnlv,defnvu).
rewrite defnlv.
rewrite defnvu.
auto.


split.
(* nvl = ln_i_v_CXp (i + 1) v lambda nil *)
apply id_list.
split.
rewrite (length_ln_i_v_CXp (i+1) v lambda nil).
rewrite Lnvl.
symmetry.
apply HR0.
intros.
(* i0 <i \/ i0=i \/ i0>i  *)
cut ( i0 <i \/ i0=i \/ i0 > i).
intro di0.
destruct di0.
   (* i0 < i *)
   cut (get i0 (ln_i_v_CXp (i + 1) v lambda nil) = get i0 v).
   cut (get i0 nvl = get i0 vl).
   cut (get i0 vl = get i0 v).
   intros r1 r2 r3.
   rewrite r3.
   rewrite r2.
   rewrite r1.
   auto.
      (* get i0 vl = get i0 v *)
      apply (HR9 i0).
      repeat split; [lia|lia|lia|lia|lia|auto].
      (* get i0 nvl = get i0 vl *)
      symmetry.
      apply (fix_get nb_feature i i0 v vl vu nil nvl nvu np).
      rewrite varfix.
      repeat split ; [lia|lia|lia|lia|lia|lia|lia|auto].
      apply HR0.
      (* get i0 (ln_i_v_CXp (i + 1) v lambda nil) = get i0 v *)
      apply (get_inf_not_mem_i_ln_i_v_CXp i0 (i+1) v lambda nil).
      repeat split ;[lia|lia|lia|auto].
   destruct H1.
   (* i0 = i *)
   rewrite H1.
   cut (get i (ln_i_v_CXp (i + 1) v lambda nil) = get i v).
   cut (get i nvl = get i v).
   intros r1 r2.
   rewrite r2.
   rewrite r1.
   auto.
      (* get i nvl = get i v *)
      apply (fix_i nb_feature i v vl vu nil nvl nvu np).
      rewrite varfix.
      repeat split ; [lia|lia|lia|lia|auto].
      apply HR0.
      (* get i (ln_i_v_CXp (i + 1) v lambda nil) = get i v *)
      apply (get_inf_not_mem_i_ln_i_v_CXp i (i+1) v lambda nil).
      repeat split ;[lia|lia|lia|auto].
   (* i0 > i *)
   cut (get i0 nvl = get i0 vl).
   cut (get i0 vl = lambda i0).
   cut (get i0 (ln_i_v_CXp (i + 1) v lambda nil) = lambda i0).
   intros r1 r2 r3.
   rewrite r3.
   rewrite r2.
   rewrite r1.
   auto.
      (* get i0 (ln_i_v_CXp (i + 1) v lambda nil) = lambda i0*)
      apply (get_sup_i_ln_i_v_CXp i0 (i+1) v lambda nil).
      lia.
      (* get i0 vl = lambda i0 *)
      apply HR7.
      lia.
      (* get i0 nvl = get i0 vl *)
      symmetry.
      apply (fix_get nb_feature i i0 v vl vu nil nvl nvu np).
      rewrite varfix.
      repeat split ; [lia|lia|lia|lia|lia|lia|lia|auto].
      apply HR0.
   lia.
(* nvu = ln_i_v_CXp (i + 1) v nu nil *)
apply id_list.
split.
rewrite (length_ln_i_v_CXp (i+1) v nu nil).
rewrite Lnvu.
symmetry.
apply HR0.
intros.
(* i0 <i \/ i0=i \/ i0>i  *)
cut ( i0 <i \/ i0=i \/ i0 > i).
intro di0.
destruct di0.
   (* i0 < i *)
   cut (get i0 (ln_i_v_CXp (i + 1) v nu nil) = get i0 v).
   cut (get i0 nvu = get i0 vu).
   cut (get i0 vu = get i0 v).
   intros r1 r2 r3.
   rewrite r3.
   rewrite r2.
   rewrite r1.
   auto.
      (* get i0 vu = get i0 v *)
      apply (HR9 i0).
      repeat split; [lia|lia|lia|lia|lia|auto].
      (* get i0 nvu = get i0 vu *)
      symmetry.
      apply (fix_get nb_feature i i0 v vl vu nil nvl nvu np).
      rewrite varfix.
      repeat split ; [lia|lia|lia|lia|lia|lia|lia|auto].
      apply HR0.
      (* get i0 (ln_i_v_CXp (i + 1) v lambda nil) = get i0 v *)
      apply (get_inf_not_mem_i_ln_i_v_CXp i0 (i+1) v nu nil).
      repeat split ;[lia|lia|lia|auto].
   destruct H1.
   (* i0 = i *)
   rewrite H1.
   cut (get i (ln_i_v_CXp (i + 1) v nu nil) = get i v).
   cut (get i nvu = get i v).
   intros r1 r2.
   rewrite r2.
   rewrite r1.
   auto.
      (* get i nvu = get i v *)
      apply (fix_i nb_feature i v vl vu nil nvl nvu np).
      rewrite varfix.
      repeat split ; [lia|lia|lia|lia|auto].
      apply HR0.
      (* get i (ln_i_v_CXp (i + 1) v nu nil) = get i v *)
      apply (get_inf_not_mem_i_ln_i_v_CXp i (i+1) v nu nil).
      repeat split ;[lia|lia|lia|auto].
   (* i0 > i *)
   cut (get i0 nvu = get i0 vu).
   cut (get i0 vu = nu i0).
   cut (get i0 (ln_i_v_CXp (i + 1) v nu nil) = nu i0).
   intros r1 r2 r3.
   rewrite r3.
   rewrite r2.
   rewrite r1.
   auto.
      (* get i0 (ln_i_v_CXp (i + 1) v nu nil) = nu i0*)
      apply (get_sup_i_ln_i_v_CXp i0 (i+1) v nu nil).
      lia.
      (* get i0 vl = nu i0 *)
      apply HR7.
      lia.
      (* get i0 nvu = get i0 vu *)
      symmetry.
      apply (fix_get nb_feature i i0 v vl vu nil nvl nvu np).
      rewrite varfix.
      repeat split ; [lia|lia|lia|lia|lia|lia|lia|auto].
      apply HR0.
   lia.

(* x=i *)
apply (destruct_list_1elt x i x0 x1).
auto.

(* x1 = nil *)
apply (destruct_list_1elt x i x0 x1).
auto.

(* p<>nil -> on peut appliquer la précondition *)

destruct x0.
(* x0 = nil
-> i=x
-> x1=n::p

précondition sur nil n p
*)

(* x0=nil -> x=i *)
cut (x=i).
intro defxx.
rewrite defxx.
cut (x1 = n::p).
intro defxx1.
rewrite defxx1.

(*  ln_i_v_CXp *)

exists (ln_i_v_CXp (i+1) v lambda (n::p)). (* i+1 pour que à i il y ait vi *)
exists (ln_i_v_CXp (i+1) v nu (n::p)).
split.
rewrite (length_ln_i_v_CXp ).
apply HR0.
split.
rewrite (length_ln_i_v_CXp).
apply HR0. 
split.
intros.
cut (mem j (n :: p) \/ ~mem j (n :: p)).
intro d.
destruct d.
(* mem j (n :: p) *)
cut (j<i).
intro j_inf_i.
left.
split.
left.
apply H1.
split.
apply (get_inf_mem_i_ln_i_v_CXp j (i+1) v lambda (n::p)).
repeat split; [lia|lia|lia|apply H1].
apply (get_inf_mem_i_ln_i_v_CXp j (i+1) v nu (n::p)).
repeat split; [lia|lia|lia|apply H1].
  (* j<i *)
  cut (~(j >= i \/ j < 0 \/ j >= nb_feature)).
  lia.
  cut (~ ~ (mem j (n :: p))).
  generalize (HR5 j).
  apply contrapose.
  tauto.
(* ~ mem j (n :: p) *)
cut (j <= i \/ j>i).
intro dj.
destruct dj.
   (* j<= i *)
   right.
   split.
   unfold not.
   intro.
   destruct H3.
   tauto.
   lia.
   split.
   apply (get_inf_not_mem_i_ln_i_v_CXp j (i+1) v lambda (n::p)).
   repeat split; [lia|lia|lia|apply H1].
   apply (get_inf_not_mem_i_ln_i_v_CXp j (i+1) v nu (n::p)).
   repeat split; [lia|lia|lia|apply H1].
   (* j>i *)
   left.
   split.
   right.
   apply H2.
   split.
   apply (get_sup_i_ln_i_v_CXp j (i+1) v lambda (n::p)).
   lia.
   apply (get_sup_i_ln_i_v_CXp j (i+1) v nu (n::p)).
   lia.
   lia.
(* mem j (n :: p) \/ ~ mem j (n :: p) *)
tauto.

(* k (ln_i_v i v lambda (n :: p)) <> k (ln_i_v i v nu (n :: p)) *)
generalize Hdif_k.
rewrite (surjective_pairing (fixAttr i v vl vu (n :: p))).
rewrite (surjective_pairing (fst (fixAttr i v vl vu (n :: p)))).
rewrite varfix.
simpl.

cut (nvl = ln_i_v_CXp (i + 1) v lambda (n :: p) /\ nvu = ln_i_v_CXp (i + 1) v nu (n :: p)).
intro defnvlu.
destruct defnvlu as (defnlv,defnvu).
rewrite defnlv.
rewrite defnvu.
auto.

split.
(* nvl = ln_i_v_CXp (i + 1) v lambda (n :: p) *)
apply id_list.
split.
rewrite (length_ln_i_v_CXp (i+1) v lambda (n :: p)).
rewrite Lnvl.
symmetry.
apply HR0.
intros.
(* i0 <i \/ i0=i \/ i0>i  *)
cut ( i0 <i \/ i0=i \/ i0 > i).
intro di0.
destruct di0.
   (* i0 < i *)
   cut (not (mem i0 (n::p)) \/ mem i0 (n::p)).
   intro dm.
   destruct dm.
      (* ~ mem i0 (n :: p) *)
      cut (get i0 (ln_i_v_CXp (i + 1) v lambda (n :: p)) = get i0 v).
      cut (get i0 nvl = get i0 vl).
      cut (get i0 vl = get i0 v).
      intros r1 r2 r3.
      rewrite r3.
      rewrite r2.
      rewrite r1.
      auto.
         (* get i0 vl = get i0 v *)
         apply (HR9 i0).
         repeat split; [lia|lia|lia|lia|lia|auto].
         (* get i0 nvl = get i0 vl *)
         symmetry.
         apply (fix_get nb_feature i i0 v vl vu (n :: p) nvl nvu np).
         rewrite varfix.
         repeat split ; [lia|lia|lia|lia|lia|lia|lia|auto].
         apply HR0.
         (* get i0 (ln_i_v_CXp (i + 1) v lambda (n :: p)) = get i0 v *)
         apply (get_inf_not_mem_i_ln_i_v_CXp i0 (i+1) v lambda (n :: p)).
         repeat split ;[lia|lia|lia|auto].
      (* mem i0 (n::p) *)
      cut (get i0 nvl = get i0 vl).
      cut (get i0 vl = lambda i0).
      cut (get i0 (ln_i_v_CXp (i + 1) v lambda (n :: p)) = lambda i0).
      intros r1 r2 r3.
      rewrite r3.
      rewrite r2.
      rewrite r1.
      auto.
         (* get i0 (ln_i_v_CXp (i + 1) v lambda (n :: p)) = lambda i0*)
         apply (get_inf_mem_i_ln_i_v_CXp i0 (i+1) v lambda (n :: p)).
         repeat split ;[lia|lia|lia|auto].
         (* get i0 vl = lambda i0 *)
         apply HR6.
         apply H2.
         (* get i0 nvl = get i0 vl *)
         symmetry.
         apply (fix_get nb_feature i i0 v vl vu (n::p) nvl nvu np).
         rewrite varfix.
         repeat split ; [lia|lia|lia|lia|lia|lia|lia|auto].
         apply HR0.
      tauto.
      
   destruct H1.
   (* i0 = i *)
   rewrite H1.
   cut (get i (ln_i_v_CXp (i + 1) v lambda (n::p)) = get i v).
   cut (get i nvl = get i v).
   intros r1 r2.
   rewrite r2.
   rewrite r1.
   auto.
      (* get i nvl = get i v *)
      apply (fix_i nb_feature i v vl vu (n::p) nvl nvu np).
      rewrite varfix.
      repeat split ; [lia|lia|lia|lia|auto].
      apply HR0.
      (* get i (ln_i_v_CXp (i + 1) v lambda (n::p)) = get i v *)
      apply (get_inf_not_mem_i_ln_i_v_CXp i (i+1) v lambda (n::p)).
      repeat split ;[lia|lia|lia|auto].
   (* i0 > i *)
   cut (get i0 nvl = get i0 vl).
   cut (get i0 vl = lambda i0).
   cut (get i0 (ln_i_v_CXp (i + 1) v lambda (n::p)) = lambda i0).
   intros r1 r2 r3.
   rewrite r3.
   rewrite r2.
   rewrite r1.
   auto.
      (* get i0 (ln_i_v_CXp (i + 1) v lambda (n::p)) = lambda i0*)
      apply (get_sup_i_ln_i_v_CXp i0 (i+1) v lambda (n::p)).
      lia.
      (* get i0 vl = lambda i0 *)
      apply HR7.
      lia.
      (* get i0 nvl = get i0 vl *)
      symmetry.
      apply (fix_get nb_feature i i0 v vl vu (n::p) nvl nvu np).
      rewrite varfix.
      repeat split ; [lia|lia|lia|lia|lia|lia|lia|auto].
      apply HR0.
   lia.
(* nvu = ln_i_v_CXp (i + 1) v nu nil *)
apply id_list.
split.
rewrite (length_ln_i_v_CXp (i+1) v nu (n :: p)).
rewrite Lnvu.
symmetry.
apply HR0.
intros.
(* i0 <i \/ i0=i \/ i0>i  *)
cut ( i0 <i \/ i0=i \/ i0 > i).
intro di0.
destruct di0.
   (* i0 < i *)
   cut (not (mem i0 (n::p)) \/ mem i0 (n::p)).
   intro dm.
   destruct dm.
      (* ~ mem i0 (n :: p) *)
      cut (get i0 (ln_i_v_CXp (i + 1) v nu (n :: p)) = get i0 v).
      cut (get i0 nvu = get i0 vu).
      cut (get i0 vu = get i0 v).
      intros r1 r2 r3.
      rewrite r3.
      rewrite r2.
      rewrite r1.
      auto.
         (* get i0 vu = get i0 v *)
         apply (HR9 i0).
         repeat split; [lia|lia|lia|lia|lia|auto].
         (* get i0 nvu = get i0 vu *)
         symmetry.
         apply (fix_get nb_feature i i0 v vl vu (n :: p) nvl nvu np).
         rewrite varfix.
         repeat split ; [lia|lia|lia|lia|lia|lia|lia|auto].
         apply HR0.
         (* get i0 (ln_i_v_CXp (i + 1) v nu (n :: p)) = get i0 v *)
         apply (get_inf_not_mem_i_ln_i_v_CXp i0 (i+1) v nu (n :: p)).
         repeat split ;[lia|lia|lia|auto].
      (* mem i0 (n::p) *)
      cut (get i0 nvu = get i0 vu).
      cut (get i0 vu = nu i0).
      cut (get i0 (ln_i_v_CXp (i + 1) v nu (n :: p)) = nu i0).
      intros r1 r2 r3.
      rewrite r3.
      rewrite r2.
      rewrite r1.
      auto.
         (* get i0 (ln_i_v_CXp (i + 1) v nu (n :: p)) = nu i0*)
         apply (get_inf_mem_i_ln_i_v_CXp i0 (i+1) v nu (n :: p)).
         repeat split ;[lia|lia|lia|auto].
         (* get i0 vu = nu i0 *)
         apply HR6.
         apply H2.
         (* get i0 nvu = get i0 vu *)
         symmetry.
         apply (fix_get nb_feature i i0 v vl vu (n::p) nvl nvu np).
         rewrite varfix.
         repeat split ; [lia|lia|lia|lia|lia|lia|lia|auto].
         apply HR0.
      tauto.
      
   destruct H1.
   (* i0 = i *)
   rewrite H1.
   cut (get i (ln_i_v_CXp (i + 1) v nu (n::p)) = get i v).
   cut (get i nvu = get i v).
   intros r1 r2.
   rewrite r2.
   rewrite r1.
   auto.
      (* get i nvu = get i v *)
      apply (fix_i nb_feature i v vl vu (n::p) nvl nvu np).
      rewrite varfix.
      repeat split ; [lia|lia|lia|lia|auto].
      apply HR0.
      (* get i (ln_i_v_CXp (i + 1) v nu (n::p)) = get i v *)
      apply (get_inf_not_mem_i_ln_i_v_CXp i (i+1) v nu (n::p)).
      repeat split ;[lia|lia|lia|auto].
   (* i0 > i *)
   cut (get i0 nvu = get i0 vu).
   cut (get i0 vu = nu i0).
   cut (get i0 (ln_i_v_CXp (i + 1) v nu (n::p)) = nu i0).
   intros r1 r2 r3.
   rewrite r3.
   rewrite r2.
   rewrite r1.
   auto.
      (* get i0 (ln_i_v_CXp (i + 1) v nu (n::p)) = nu i0*)
      apply (get_sup_i_ln_i_v_CXp i0 (i+1) v nu (n::p)).
      lia.
      (* get i0 vu = nu i0 *)
      apply HR7.
      lia.
      (* get i0 nvu = get i0 vu *)
      symmetry.
      apply (fix_get nb_feature i i0 v vl vu (n::p) nvl nvu np).
      rewrite varfix.
      repeat split ; [lia|lia|lia|lia|lia|lia|lia|auto].
      apply HR0.
   lia.

(* x1 = n :: p *)
cut (nil ++ x :: x1 = i :: n :: p).
apply (destruct_list_debutvide x i (n::p) x1).
generalize H.
auto.
cut (nil ++ x :: x1 = i :: n :: p).
apply (destruct_list_debutvide x i (n::p) x1).
generalize H.
auto.

(* x0 <>nil -> on peut appliquer la précondition  *)
apply (HR10 x x0 x1).
injection H.
tauto.

(* np = i :: p *)
apply (fix_p i v vl vu p nvl nvu np).
apply varfix.



   (*** End of the proof ***)
   (* Proof of size *)
   apply (preserveSize_CXp i v vl vu nvl nvu p np).
   repeat split ; [apply Hi_inf | apply Hi_sup| apply HR0 | apply HR0 | apply HR0 | apply varfix].

   (* Proof of exists free *)
   destruct (freeAttr i nvl nvu).
   exists l.
   exists l0.
   reflexivity.

    (* Proof of exists fix *)
   destruct (fixAttr i v vl vu p ).
   destruct p0.
   exists l0.
   exists l1.
   exists l.
   reflexivity.
Qed.



Lemma preserveR0Cas3_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) <> (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R0 k (i + 1) v
   (fst (fst (fixAttr i v vl vu p)))
  (snd (fst (fixAttr i v vl vu p))) p .
Proof.
   intros. 
   unfold R0.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R0 in HR0.
   
   cut (exists (nvl nvu : list T) (np : list nat), fixAttr i v vl vu p = (nvl,nvu,np)).
   intro varfix.
   destruct varfix as (nvl,varfix).
   destruct varfix as (nvu,varfix).
   destruct varfix as (np,varfix).
   rewrite varfix.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature).
   intro L.
   destruct L as (Lnvl,Lnvu).

   (* début de la preuve *)
   repeat split; [apply HR0| apply Lnvl|apply Lnvu].
   
   (* preuve des tailles *)
   apply (preserveSize_CXp i v vl vu nvl nvu p np).
   repeat split ; [apply Hi_inf | apply Hi_sup| apply HR0 | apply HR0 | apply HR0 | apply varfix].
   
   (* preuve du cut avec les exists *)
   destruct (fixAttr i v vl vu p).
   destruct p0.
   exists l0.
   exists l1.
   exists l.
   reflexivity.
Qed.

Lemma preserveR1Cas3_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) <> (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R1 k (i + 1) v
   (fst (fst (fixAttr i v vl vu p)))
  (snd (fst (fixAttr i v vl vu p))) p .
Proof.
   intros. 
   unfold R1.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R1 in HR1.
   
   cut (exists (nvl nvu : list T) (np : list nat), fixAttr i v vl vu p = (nvl,nvu,np)).
   intro varfix.
   destruct varfix as (nvl,varfix).
   destruct varfix as (nvu,varfix).
   destruct varfix as (np,varfix).
   rewrite varfix.
   simpl.
   
   cut (length nvl = nb_feature /\ length nvu = nb_feature).
   intro L.
   destruct L as (Lnvl,Lnvu).

   (* début de la preuve *)
   intros.
   cut (i >= 0 /\
   i < nb_feature /\
   length v = nb_feature /\
   length vl = nb_feature /\
   length vu = nb_feature /\
   (forall j0 : nat,
    j0 >= 0 /\ j0 < nb_feature ->
    led (lambda j0) (get j0 v) /\
    led (get j0 v) (nu j0) /\
    led (lambda j0) (get j0 vl) /\
    led (get j0 vl) (nu j0) /\
    led (lambda j0) (get j0 vu) /\ led (get j0 vu) (nu j0)) /\
   fixAttr i v vl vu p = (nvl, nvu, np)).
   intros.
   generalize (borne_fix nb_feature i v vl vu p nvl nvu np H0 j).
   intros.
   split.
   apply HR1.
   apply H.
   split.
   apply HR1.
   apply H.
   apply (H1 H).
   (* preuve du gros cut *)
   split.
   apply Hi_inf.
   split.
   apply Hi_sup.
   split.
   apply HR0.
   split.
   apply HR0.
   split.
   apply HR0.
   split.
   apply HR1.
   apply varfix.

   
   (* preuve des tailles *)
   apply (preserveSize_CXp i v vl vu nvl nvu p np).
   repeat split ; [apply Hi_inf | apply Hi_sup| apply HR0 | apply HR0 | apply HR0 | apply varfix].
   
   (* preuve du cut avec les exists *)
   destruct (fixAttr i v vl vu p).
   destruct p0.
   exists l0.
   exists l1.
   exists l.
   reflexivity.
Qed.

Lemma preserveR2Cas3_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) <> (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R2_CXp k (i + 1) v
   (fst (fst (fixAttr i v vl vu p)))
  (snd (fst (fixAttr i v vl vu p))) p .
Proof.
intros. 
unfold R2_CXp.
destruct H as (Hi_inf,H).
destruct H as (Hi_sup,H).
destruct H as (Hdif_k,H).
destruct H as (HR0,H).
destruct H as (HR1,H).
destruct H as (HR2,H).
destruct H as (HR3,H).
destruct H as (HR5,H).
destruct H as (HR6,H).
destruct H as (HR7,H).
destruct H as (HR8,H).
destruct H as (HR9,HR10).
unfold R2_CXp in HR2.

cut (exists (nvl nvu : list T) (np : list nat), fixAttr i v vl vu p = (nvl,nvu,np)).
intro varfix.
destruct varfix as (nvl,varfix).
destruct varfix as (nvu,varfix).
destruct varfix as (np,varfix).
rewrite varfix.
simpl.

cut (length nvl = nb_feature /\ length nvu = nb_feature).
intro L.
destruct L as (Lnvl,Lnvu).

(* début de la preuve *)
generalize Hdif_k.
rewrite (surjective_pairing (fixAttr i v vl vu p)).
rewrite (surjective_pairing (fst (fixAttr i v vl vu p))).
rewrite varfix.
simpl.
auto.
   
   (* preuve des tailles *)
   apply (preserveSize_CXp i v vl vu nvl nvu p np).
   repeat split ; [apply Hi_inf | apply Hi_sup| apply HR0 | apply HR0 | apply HR0 | apply varfix].
   
   (* preuve du cut avec les exists *)
   destruct (fixAttr i v vl vu p).
   destruct p0.
   exists l0.
   exists l1.
   exists l.
   reflexivity.
Qed.

Lemma preserveR3Cas3_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) <> (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R3 k (i + 1) v
   (fst (fst (fixAttr i v vl vu p)))
   (snd (fst (fixAttr i v vl vu p))) p .
Proof.
intros.
unfold R3.
unfold R3 in H.
lia.
Qed.


Lemma preserveR5Cas3_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) <> (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R5 k (i + 1) v
   (fst (fst (fixAttr i v vl vu p)))
  (snd (fst (fixAttr i v vl vu p))) p.
Proof.
   intros. 
   unfold R5.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R5 in HR5.
   intros.
   apply HR5.
   lia.
Qed.

Lemma preserveR6Cas3_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) <> (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R6_CXp k (i + 1) v
   (fst (fst (fixAttr i v vl vu p)))
  (snd (fst (fixAttr i v vl vu p))) p.
Proof.
intros. 
unfold R6_CXp.
destruct H as (Hi_inf,H).
destruct H as (Hi_sup,H).
destruct H as (Hdif_k,H).
destruct H as (HR0,H).
destruct H as (HR1,H).
destruct H as (HR2,H).
destruct H as (HR3,H).
destruct H as (HR5,H).
destruct H as (HR6,H).
destruct H as (HR7,H).
destruct H as (HR8,H).
destruct H as (HR9,HR10).
unfold R6_CXp in HR6.

cut (exists (nvl nvu : list T) (np : list nat), fixAttr i v vl vu p = (nvl,nvu,np)).
intro varfix.
destruct varfix as (nvl,varfix).
destruct varfix as (nvu,varfix).
destruct varfix as (np,varfix).
rewrite varfix.
simpl.

cut (length nvl = nb_feature /\ length nvu = nb_feature).
intro L.
destruct L as (Lnvl,Lnvu).

(* début de la preuve *)
intros.
(* D'abord des hypothèse liés à la contraposée de HR5 *)
cut (j<i /\ j >= 0 /\ j < nb_feature).
intro.
cut (get j nvl = get j vl).
intro rnvl.
rewrite rnvl.
cut (get j nvu = get j vu).
intro rnvu.
rewrite rnvu.
apply HR6.
auto.
symmetry.
apply (fix_get nb_feature i j v vl vu p nvl nvu np).
repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfix].
symmetry.
apply (fix_get nb_feature i j v vl vu p nvl nvu np).
repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfix].
(* contraposée de HR5 *)
cut (mem j p -> (j < i /\ j >= 0 /\ j < nb_feature)).
intro CHR5.
apply CHR5.
tauto.
cut (~~mem j p ->  ~(j >= i \/ j < 0 \/ j >= nb_feature)).
intros.
cut (~(j >= i \/ j < 0 \/ j >= nb_feature)).
lia.
apply H0.
tauto.
unfold R5 in HR5.
generalize (HR5 j).
apply contrapose.
   
(* preuve des tailles *)
apply (preserveSize_CXp i v vl vu nvl nvu p np).
repeat split ; [apply Hi_inf | apply Hi_sup| apply HR0 | apply HR0 | apply HR0 | apply varfix].

(* preuve du cut avec les exists *)
destruct (fixAttr i v vl vu p).
destruct p0.
exists l0.
exists l1.
exists l.
reflexivity.

Qed.

Lemma preserveR7Cas3_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) <> (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R7_CXp k (i + 1) v
   (fst (fst (fixAttr i v vl vu p)))
  (snd (fst (fixAttr i v vl vu p))) p.
Proof.
intros. 
unfold R7_CXp.
destruct H as (Hi_inf,H).
destruct H as (Hi_sup,H).
destruct H as (Hdif_k,H).
destruct H as (HR0,H).
destruct H as (HR1,H).
destruct H as (HR2,H).
destruct H as (HR3,H).
destruct H as (HR5,H).
destruct H as (HR6,H).
destruct H as (HR7,H).
destruct H as (HR8,H).
destruct H as (HR9,HR10).
unfold R7_CXp in HR7.

cut (exists (nvl nvu : list T) (np : list nat), fixAttr i v vl vu p = (nvl,nvu,np)).
intro varfix.
destruct varfix as (nvl,varfix).
destruct varfix as (nvu,varfix).
destruct varfix as (np,varfix).
rewrite varfix.
simpl.

cut (length nvl = nb_feature /\ length nvu = nb_feature).
intro L.
destruct L as (Lnvl,Lnvu).

(* début de la preuve *)
   intros.

   cut (i=j \/ i<>j).
   intro di.
   destruct di.

   (*i=j*)
   (* hypothèses contradictoires *)
   lia.

   (* i<> j*)
   cut (get j nvl = get j vl).
   intro rnvl.
   rewrite rnvl.
   cut (get j nvu = get j vu).
   intro rnvu.
   rewrite rnvu.
   apply HR7.
   split.
   lia.
   split.
   lia.
   tauto.
   symmetry.
   apply (fix_get nb_feature i j v vl vu p nvl nvu np).
   repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfix].
   symmetry.
   apply (fix_get nb_feature i j v vl vu p nvl nvu np).
   repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfix].
   lia.
   
(* preuve des tailles *)
apply (preserveSize_CXp i v vl vu nvl nvu p np).
repeat split ; [apply Hi_inf | apply Hi_sup| apply HR0 | apply HR0 | apply HR0 | apply varfix].

(* preuve du cut avec les exists *)
destruct (fixAttr i v vl vu p).
destruct p0.
exists l0.
exists l1.
exists l.
reflexivity.

Qed.


Lemma preserveR8Cas3_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) <> (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R8 k (i + 1) v
   (fst (fst (fixAttr i v vl vu p)))
  (snd (fst (fixAttr i v vl vu p))) p .
Proof.
   intros. 
   unfold R8.
   destruct H as (Hi_inf,H).
   destruct H as (Hi_sup,H).
   destruct H as (Hdif_k,H).
   destruct H as (HR0,H).
   destruct H as (HR1,H).
   destruct H as (HR2,H).
   destruct H as (HR3,H).
   destruct H as (HR5,H).
   destruct H as (HR6,H).
   destruct H as (HR7,H).
   destruct H as (HR8,H).
   destruct H as (HR9,HR10).
   unfold R8 in HR8.
   auto.
Qed.


Lemma preserveR9Cas3_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) <> (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R9_CXp k (i + 1) v
   (fst (fst (fixAttr i v vl vu p)))
  (snd (fst (fixAttr i v vl vu p))) p.
Proof.
intros. 
unfold R9_CXp.
destruct H as (Hi_inf,H).
destruct H as (Hi_sup,H).
destruct H as (Hdif_k,H).
destruct H as (HR0,H).
destruct H as (HR1,H).
destruct H as (HR2,H).
destruct H as (HR3,H).
destruct H as (HR5,H).
destruct H as (HR6,H).
destruct H as (HR7,H).
destruct H as (HR8,H).
destruct H as (HR9,HR10).
unfold R9_CXp in HR9.

cut (exists (nvl nvu : list T) (np : list nat), fixAttr i v vl vu p = (nvl,nvu,np)).
intro varfix.
destruct varfix as (nvl,varfix).
destruct varfix as (nvu,varfix).
destruct varfix as (np,varfix).
rewrite varfix.
simpl.

cut (length nvl = nb_feature /\ length nvu = nb_feature).
intro L.
destruct L as (Lnvl,Lnvu).

(* début de la preuve *)
   intros.
   
   cut (i <> j \/ i=j).
   intro d.
   destruct d.
   (* i<>j *)
   cut (get j nvl = get j vl).
   intro rnnvl.
   rewrite rnnvl.
   cut (get j nvu = get j vu).
   intro rnnvu.
   rewrite rnnvu.
   apply HR9.
   repeat split; [lia|lia|lia|lia|lia|apply H].
   symmetry.
   apply (fix_get nb_feature i j v vl vu p nvl nvu np).
   repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfix].
   symmetry.
   apply (fix_get nb_feature i j v vl vu p nvl nvu np).
   repeat split; [lia | lia | lia | lia | lia | apply HR0 | apply HR0 | apply HR0 | apply varfix].
   (* i = j *)
   rewrite <- H0.
   apply (fix_i nb_feature i v vl vu p nvl nvu np).
   repeat split; [lia|lia|apply HR0|apply HR0|apply HR0|apply varfix].

   lia.


(* preuve des tailles *)
apply (preserveSize_CXp i v vl vu nvl nvu p np).
repeat split ; [apply Hi_inf | apply Hi_sup| apply HR0 | apply HR0 | apply HR0 | apply varfix].

(* preuve du cut avec les exists *)
destruct (fixAttr i v vl vu p).
destruct p0.
exists l0.
exists l1.
exists l.
reflexivity.

Qed.


Lemma preserveR10Cas3_CXp : 
   forall (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat),  
   i>= 0 /\ i < nb_feature  /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) <> (k nvu)) /\ 
   (R0 k i v vl vu p /\ R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p  /\
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p) 
   -> R10_CXp k (i + 1) v
   (fst (fst (fixAttr i v vl vu p)))
  (snd (fst (fixAttr i v vl vu p))) p.
Proof.
intros. 
unfold R1.
destruct H as (Hi_inf,H).
destruct H as (Hi_sup,H).
destruct H as (Hdif_k,H).
destruct H as (HR0,H).
destruct H as (HR1,H).
destruct H as (HR2,H).
destruct H as (HR3,H).
destruct H as (HR5,H).
destruct H as (HR6,H).
destruct H as (HR7,H).
destruct H as (HR8,H).
destruct H as (HR9,HR10).
intros.
apply HR10.
Qed.


Definition E1_CXp (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat) : Prop := 
  is_weak_CXp k v (findCXp_aux k i v vl vu p).

Definition E2_CXp (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat) : Prop := 
  is_sorted (findCXp_aux k i v vl vu p).

Definition E3_CXp (k : list T -> Tk) (i:nat) (v vl vu: list T) (p:list nat) : Prop := 
  forall (x:nat), forall (x0 x1 : list nat), ((findCXp_aux k i v vl vu p) = x0++(x::x1)
-> 
exists  (vl vu : list T),
length vl = nb_feature /\
length vu = nb_feature /\
 (forall (j:nat), j>=0 /\ j< nb_feature 
 ->  ((mem j x1 \/ j>x) /\ get j vl=lambda j /\ get j vu = nu j) 
 \/ ( (not (mem j x1 \/ j>x)) /\ get j vl=get j v /\ get j vu=get j v) )
/\ (k vl) = (k vu)).


Definition R_implies_E_CXp (k : list T -> Tk) (i:nat) : Prop :=
  forall (v vl vu: list T) (p:list nat), 
  (R0 k i v vl vu p /\
   R1 k i v vl vu p /\ R2_CXp k i v vl vu p /\ R3 k i v vl vu p /\ 
   R5 k i v vl vu p /\ R6_CXp k i v vl vu p /\ R7_CXp k i v vl vu p /\ R8 k i v vl vu p /\ 
   R9_CXp k i v vl vu p /\ R10_CXp k i v vl vu p )
  -> (E1_CXp k i v vl vu p) /\ (E2_CXp k i v vl vu p) /\ (E3_CXp k i v vl vu p).


Lemma ppost1_CXp :  forall (k : list T -> Tk) (v vl vu: list T) (p:list nat),
R0 k nb_feature v vl vu p /\
R1 k nb_feature v vl vu p /\
R2_CXp k nb_feature v vl vu p /\
R3 k nb_feature v vl vu p /\
R5 k nb_feature v vl vu p /\
R6_CXp k nb_feature v vl vu p /\
R7_CXp k nb_feature v vl vu p /\
R8 k nb_feature v vl vu p /\
R9_CXp k nb_feature v vl vu p /\
R10_CXp k nb_feature v vl vu p
-> is_weak_CXp k v p.
Proof.
 intros.
 destruct H as (HR0,H).
 destruct H as (HR1,H).
 destruct H as (HR2,H).
 destruct H as (HR3,H).
 destruct H as (HR5,H).
 destruct H as (HR6,H).
 destruct H as (HR7,H).
 destruct H as (HR8,H).
 destruct H as (HR9,HR10).
 unfold R0 in HR0.
 unfold R1 in HR1.
 unfold R2_CXp in HR2.

 unfold is_weak_CXp.
 cut (k v = k (ln_i_v_CXp nb_feature v lambda p) \/ k v <> k (ln_i_v_CXp nb_feature v lambda p)).
 intro d.
 destruct d.
 (* k v = k (ln_i_v_CXp nb_feature v lambda p) *)
 (* x -> k (ln_i_v_CXp nb_feature v nu p) *)
 exists (ln_i_v_CXp nb_feature v nu p).
 split.
 (* length v = nb_feature *)
 apply HR0.
 (* length (ln_i_v_CXp nb_feature v nu p) = nb_feature*)
 split.
 generalize (length_ln_i_v_CXp nb_feature v nu p).
 intro.
 rewrite H0.
 apply HR0.
 (* x j dans les bornes lambda / nu *)
 split.
 intros.
 destruct HR0.
 rewrite <- H1 in H0. 
 generalize (get_ln_i_v_CXp nb_feature v nu p j H0).
 intro d.
 destruct d.
   (*  get j (ln_i_v_CXp nb_feature v nu p) = get j v *)
   rewrite H3.
   split.
   apply (HR1 j).
   lia.
   apply (HR1 j).
   lia.
   (* get j (ln_i_v_CXp nb_feature v nu p) = nu j *)
   rewrite H3.
   split.
   apply (led_transitivity (lambda j) (get j v) (nu j)).
   split.
   apply (HR1 j).
   lia.
   apply (HR1 j).
   lia.
   apply (led_eq (nu j)).
   reflexivity.
(* weak CXp *)
split.
   (* ~ mem j p -> x j = v j *)
   intros.
   cut (mem j p \/ ~ mem j p).
   intro d.
   destruct d.
   right.
   apply H1.
   left.
   split.
   apply H1.
   apply (get_inf_not_mem_i_ln_i_v_CXp j nb_feature v nu p).
   destruct HR0.
   rewrite <- H2 in H0.
   rewrite <- H2.
   tauto.
   tauto.
   (* k (ln_i_v_CXp nb_feature v nu p) <> k v *)
   rewrite H.
   cut ((ln_i_v_CXp nb_feature v nu p) = vu).
   cut ((ln_i_v_CXp nb_feature v lambda p) = vl).
   intros rvl rvu.
   rewrite rvl.
   rewrite rvu.
   auto. (*HR2*)
      (* ln_i_v_CXp nb_feature v lambda p = vl *)
      apply id_list.
      cut (length (ln_i_v_CXp nb_feature v lambda p) = nb_feature).
      intro llni.
      rewrite llni.
      split.
      symmetry.
      apply HR0.
      intros.
      cut (mem i p \/ ~ mem i p).
      intro dmem.
      destruct dmem.
         (* mem i p *)
         cut (get i (ln_i_v_CXp nb_feature v lambda p) = lambda i).
         cut (get i vl = lambda i).
         intros r1 r2.
         rewrite r1.
         rewrite r2.
         auto.
            (* get i vl = lambda i *)
            apply HR6.
            apply H1.
            (* get i (ln_i_v_CXp nb_feature v lambda p) = lambda i *)
            apply (get_inf_mem_i_ln_i_v_CXp i nb_feature v lambda p).
            repeat split ; [lia|lia|lia|apply H1].
         (* ~ mem i p *)
         cut (get i (ln_i_v_CXp nb_feature v lambda p) = get i v).
         cut (get i vl = get i v).
         intros r1 r2.
         rewrite r1.
         rewrite r2.
         auto.
            (* get i vl = get i v*)
            apply HR9.
            repeat split;[lia|lia|lia|lia|lia|apply H1].
            (* get i (ln_i_v_CXp nb_feature v lambda p) = get i v*)
            apply (get_inf_not_mem_i_ln_i_v_CXp i nb_feature v lambda p).
            repeat split ; [lia|lia|lia|apply H1].
         apply mem_not_mem.
      (* length (ln_i_v_CXp nb_feature v lambda p) = nb_feature *)
      generalize (length_ln_i_v_CXp nb_feature v lambda p).
      destruct HR0.
      rewrite <- H0.
      auto.
      (* ln_i_v_CXp nb_feature v nu p = vu *)
      apply id_list.
      cut (length (ln_i_v_CXp nb_feature v nu p) = nb_feature).
      intro llni.
      rewrite llni.
      split.
      symmetry.
      apply HR0.
      intros.
      cut (mem i p \/ ~ mem i p).
      intro dmem.
      destruct dmem.
         (* mem i p *)
         cut (get i (ln_i_v_CXp nb_feature v nu p) = nu i).
         cut (get i vu = nu i).
         intros r1 r2.
         rewrite r1.
         rewrite r2.
         auto.
            (* get i vu = nu i *)
            apply HR6.
            apply H1.
            (* get i (ln_i_v_CXp nb_feature v nu p) = nu i *)
            apply (get_inf_mem_i_ln_i_v_CXp i nb_feature v nu p).
            repeat split ; [lia|lia|lia|apply H1].
         (* ~ mem i p *)
         cut (get i (ln_i_v_CXp nb_feature v nu p) = get i v).
         cut (get i vu = get i v).
         intros r1 r2.
         rewrite r1.
         rewrite r2.
         auto.
            (* get i vu = get i v*)
            apply HR9.
            repeat split;[lia|lia|lia|lia|lia|apply H1].
            (* get i (ln_i_v_CXp nb_feature v nu p) = get i v*)
            apply (get_inf_not_mem_i_ln_i_v_CXp i nb_feature v nu p).
            repeat split ; [lia|lia|lia|apply H1].
         apply mem_not_mem.
      (* length (ln_i_v_CXp nb_feature v nu p) = nb_feature *)
      generalize (length_ln_i_v_CXp nb_feature v nu p).
      destruct HR0.
      rewrite <- H0.
      auto.
(* k v <> k (ln_i_v_CXp nb_feature v lambda p) *)
(* x -> (ln_i_v_CXp nb_feature v lambda p)*)
 exists (ln_i_v_CXp nb_feature v lambda p).
 split.
 (* length v = nb_feature *)
 apply HR0.
 (* length (ln_i_v_CXp nb_feature v lambda p) = nb_feature*)
 split.
 generalize (length_ln_i_v_CXp nb_feature v lambda p).
 intro.
 rewrite H0.
 apply HR0.
 (* x j dans les bornes lambda / nu *)
 split.
 intros.
 destruct HR0.
 rewrite <- H1 in H0. 
 generalize (get_ln_i_v_CXp nb_feature v lambda p j H0).
 intro d.
 destruct d.
   (*  get j (ln_i_v_CXp nb_feature v lambda p) = get j v *)
   rewrite H3.
   split.
   apply (HR1 j).
   lia.
   apply (HR1 j).
   lia.
   (* get j (ln_i_v_CXp nb_feature v lambda p) = nu j *)
   rewrite H3.
   split.
   apply (led_eq (lambda j)).
   reflexivity.
   apply (led_transitivity (lambda j) (get j v) (nu j)).
   split.
   apply (HR1 j).
   lia.
   apply (HR1 j).
   lia.
(* weak CXp *)
split.
   (* ~ mem j p -> x j = v j *)
   intros.
   cut (mem j p \/ ~ mem j p).
   intro d.
   destruct d.
   right.
   apply H1.
   left.
   split.
   apply H1.
   apply (get_inf_not_mem_i_ln_i_v_CXp j nb_feature v lambda p).
   destruct HR0.
   rewrite <- H2 in H0.
   rewrite <- H2.
   tauto.
   tauto.
   (* k (ln_i_v_CXp nb_feature v lambda p) <> k v *)
   auto.
(*k v = k (ln_i_v_CXp nb_feature v lambda p) \/
k v <> k (ln_i_v_CXp nb_feature v lambda p) *)
tauto.
Qed.




Lemma R_implies_E_findCXp : 
forall (k : list T -> Tk)  (i:nat),  i>=0 /\ i < nb_feature +1 -> R_implies_E_CXp k i.
Proof.
intro k.
apply (my_induction nb_feature).
(* cas général *)
split.
unfold R_implies_E_CXp.
intros.
destruct H.
unfold E1_CXp.
unfold E2_CXp.
unfold E3_CXp.
(* couper selon les 3 cas du findCxp_aux *)
cut ((i = nb_feature +1) 
\/ (i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) = (k nvu))) 
\/ (i>= 0 /\ i < nb_feature /\ ( let '(nvl,nvu,np) :=  fixAttr i v vl vu p in (k nvl) <> (k nvu)))).
intro cases.
destruct cases.
(* cas terminal, pas possible *)
cut False.
tauto.
lia.
destruct H3.
(* cas 2 *)
destruct H3.
destruct H4.
cut (let '(nvl,nvu,np) :=  fixAttr i v vl vu p in let '(nnvl,nnvu) := freeAttr i nvl nvu  in findCXp_aux k i v vl vu p = findCXp_aux k (i+1) v nnvl nnvu np).
rewrite (surjective_pairing (fixAttr i v vl vu p)).
rewrite (surjective_pairing (fst (fixAttr i v vl vu p))).
rewrite (surjective_pairing (freeAttr i (fst (fst (fixAttr i v vl vu p))) (snd (fst (fixAttr i v vl vu p))))).
intro r.
rewrite r.
apply H0.
(* préservation des require *)
split.
apply preserveR0Cas2_CXp.
tauto.
split.
apply preserveR1Cas2_CXp.
tauto.
split.
apply preserveR2Cas2_CXp.
tauto.
split.
apply preserveR3Cas2_CXp.
tauto.
split.
apply preserveR5Cas2_CXp.
tauto.
split.
apply preserveR6Cas2_CXp.
tauto.
split.
apply preserveR7Cas2_CXp.
tauto.
split.
apply preserveR8Cas2_CXp.
tauto.
split.
apply preserveR9Cas2_CXp.
tauto.
apply preserveR10Cas2_CXp.
tauto.
(* lien rec *)
apply findCXp_aux_spec2.
auto.
(*  cas 3 *)
destruct H3.
destruct H4.
cut (let '(nvl,nvu,np) :=  fixAttr i v vl vu p in findCXp_aux k i v vl vu p = findCXp_aux k (i+1) v nvl nvu p).
rewrite (surjective_pairing (fixAttr i v vl vu p)).
rewrite (surjective_pairing (fst (fixAttr i v vl vu p))).
intro r.
rewrite r.
apply H0.
(* préservation des require *)
split.
apply preserveR0Cas3_CXp.
tauto.
split.
apply preserveR1Cas3_CXp.
tauto.
split.
apply preserveR2Cas3_CXp.
tauto.
split.
apply preserveR3Cas3_CXp.
tauto.
split.
apply preserveR5Cas3_CXp.
tauto.
split.
apply preserveR6Cas3_CXp.
tauto.
split.
apply preserveR7Cas3_CXp.
tauto.
split.
apply preserveR8Cas3_CXp.
tauto.
split.
apply preserveR9Cas3_CXp.
tauto.
apply preserveR10Cas3_CXp.
tauto.
(* lien rec *)
apply findCXp_aux_spec3.
auto.
(* Prouver qu'on a bien que ces 3 cas possible *)
right.
cut (i >= 0 /\
i < nb_feature /\
((let '(nvl,nvu,np) :=  fixAttr i v vl vu p in k nvl = k nvu) \/ (let '(nvl,nvu,np) :=  fixAttr i v vl vu p in k nvl <> k nvu))).
intro r.
destruct r.
destruct H4.
destruct H5.
left.
auto.
right.
auto.
split.
auto.
split.
lia.
rewrite (surjective_pairing (fixAttr i v vl vu p)).
rewrite (surjective_pairing (fst (fixAttr i v vl vu p))).
tauto.
(* cas terminal *)
unfold R_implies_E_CXp.
intros.
split.
(* post cond 1 *)
unfold E1_CXp.
unfold findCXp_aux.
cut (nb_feature - nb_feature = 0).
intro r.
rewrite r.
simpl.
apply (ppost1_CXp k v vl vu p).
auto.
lia.
(* post cond 2 *)
split.
unfold E2_CXp.
unfold findCXp_aux.
cut (nb_feature - nb_feature = 0).
intro r.
rewrite r.
simpl.
unfold R8 in H.
apply H.
lia.
(* post cond 3 *)
unfold E3_CXp.
unfold findCXp_aux.
cut (nb_feature - nb_feature = 0).
intro r.
rewrite r.
simpl.
unfold R10_CXp in H.
apply H.
lia.
Qed.



Program Definition findCXp (k : list T -> Tk) (v: list T) : list nat :=
  findCXp_aux k 0 v (feature_f nb_feature lambda) (feature_f nb_feature nu) nil.


Definition is_CXp (k : list T -> Tk) (v: list T) (p:list nat) : Prop :=
   is_weak_CXp k v p (* satisfy the constraint *)
/\ forall (q:list nat), (is_strict_subset q p) -> not (is_weak_CXp k v q). (* all subset do not satisfy the constraint *)



Lemma R_init_Cxp : 
forall (k : list T -> Tk)  (v: list T), 
(( length v = nb_feature
/\ 
(forall (j:nat), j>=0 /\ j< nb_feature -> 
led (lambda j) (get j v) /\ led (get j v) (nu j)))
/\ stable k
/\ not_trivial k
)
-> R0 k 0 v (feature_f nb_feature lambda) (feature_f nb_feature nu) nil
/\ R1 k 0 v (feature_f nb_feature lambda) (feature_f nb_feature nu) nil
/\ R2_CXp k 0 v (feature_f nb_feature lambda) (feature_f nb_feature nu) nil
/\ R3 k 0 v (feature_f nb_feature lambda) (feature_f nb_feature nu) nil
/\ R5 k 0 v (feature_f nb_feature lambda) (feature_f nb_feature nu) nil
/\ R6_CXp k 0 v (feature_f nb_feature lambda) (feature_f nb_feature nu) nil
/\ R7_CXp k 0 v (feature_f nb_feature lambda) (feature_f nb_feature nu) nil
/\ R8 k 0 v (feature_f nb_feature lambda) (feature_f nb_feature nu) nil
/\ R9_CXp k 0 v (feature_f nb_feature lambda) (feature_f nb_feature nu) nil
/\ R10_CXp k 0 v (feature_f nb_feature lambda) (feature_f nb_feature nu) nil.
Proof.
   intros.
   destruct H as (H,Hp).
   destruct Hp as (k_stable, k_not_trivial).
   split.
   (* R0 *)
   unfold R0.
   split.
   apply H.
   split.
   apply (size_feature_f nb_feature lambda).
   apply (size_feature_f nb_feature nu).
   split.
   (* R1 *)
   destruct H.
   unfold R1.
   intros.
   split.
   apply (H0 j H1).
   split.
   apply (H0 j H1).
   split.
   cut (get j (feature_f nb_feature lambda) = lambda j).
   intro r.
   rewrite r.
   apply led_eq.
   reflexivity.
   apply (def_feature_f j nb_feature lambda H1).
   split.
   cut (get j (feature_f nb_feature lambda) = lambda j).
   intro r.
   rewrite r.
   apply (led_transitivity (lambda j) (get j v) (nu j)).
   apply (H0 j H1).
   apply (def_feature_f j nb_feature lambda H1).
   split.
   cut (get j (feature_f nb_feature nu) = nu j).
   intro r.
   rewrite r.
   apply (led_transitivity (lambda j) (get j v) (nu j)).
   apply (H0 j H1).
   apply (def_feature_f j nb_feature nu H1).
   cut (get j (feature_f nb_feature nu) = nu j).
   intro r.
   rewrite r.
   apply led_eq.
   reflexivity.
   apply (def_feature_f j nb_feature nu H1).
   split.
   (* R2 *)
   unfold R2_CXp.
   unfold not.
   intro.
   unfold not_trivial in k_not_trivial.
   destruct k_not_trivial as (f1,H1).
   destruct H1 as (f2,H1).
   destruct H1.
   destruct H2.
   destruct H3.
   destruct H4.
   cut (k f1 = k (feature_f nb_feature lambda)).
   cut (k f2 = k (feature_f nb_feature lambda)).
   intros.
   generalize H5.
   rewrite H6.
   rewrite H7.
   tauto.
      (* k f2 = k (feature_f nb_feature lambda) *)
      symmetry.
      apply (k_stable (feature_f nb_feature lambda) (feature_f nb_feature nu) f2).
      destruct H.
      split.
      rewrite <- H .
      apply (size_feature_f (length v) lambda).
      split.
      apply (size_feature_f nb_feature nu).
      split.
      apply H2.
      split.
      intros.
      cut (get i (feature_f nb_feature lambda) = lambda i).
      intro r.
      rewrite r.
      split.
      apply led_eq.
      reflexivity.
      apply (led_transitivity (lambda i) (get i v) (nu i)).
      apply (H6 i H7).
      apply (def_feature_f i nb_feature lambda H7).
      split.
      intros.
      cut (get i  (feature_f nb_feature nu) = nu i).
      intro r.
      rewrite r.
      split.
      apply (led_transitivity (lambda i) (get i v) (nu i)).
      apply (H6 i H7).
      apply led_eq.
      reflexivity.
      apply (def_feature_f i nb_feature nu H7).
      split.
      apply H4.
      split.
      unfold le_n.
      split.
      rewrite <- H .
      apply (size_feature_f (length v) lambda).
      split.
      apply H2.
      intros.
      cut (get i (feature_f nb_feature lambda) = lambda i).
      intro r.
      rewrite r.
      apply (H4 i H7).
      apply (def_feature_f i nb_feature lambda H7).
      split.
      unfold le_n.
      split.
      apply H2.
      split.
      rewrite <- H .
      apply (size_feature_f (length v) nu).
      intros.
      cut (get i (feature_f nb_feature nu) = nu i).
      intro r.
      rewrite r.
      apply (H4 i H7).
      apply (def_feature_f i nb_feature nu H7).
      apply H0.
      (* k f1 = k (feature_f nb_feature lambda) *)
      symmetry.
      apply (k_stable (feature_f nb_feature lambda) (feature_f nb_feature nu) f1).
      destruct H.
      split.
      rewrite <- H .
      apply (size_feature_f (length v) lambda).
      split.
      apply (size_feature_f nb_feature nu).
      split.
      apply H1.
      split.
      intros.
      cut (get i (feature_f nb_feature lambda) = lambda i).
      intro r.
      rewrite r.
      split.
      apply led_eq.
      reflexivity.
      apply (led_transitivity (lambda i) (get i v) (nu i)).
      apply (H6 i H7).
      apply (def_feature_f i nb_feature lambda H7).
      split.
      intros.
      cut (get i  (feature_f nb_feature nu) = nu i).
      intro r.
      rewrite r.
      split.
      apply (led_transitivity (lambda i) (get i v) (nu i)).
      apply (H6 i H7).
      apply led_eq.
      reflexivity.
      apply (def_feature_f i nb_feature nu H7).
      split.
      apply H3.
      split.
      unfold le_n.
      split.
      rewrite <- H .
      apply (size_feature_f (length v) lambda).
      split.
      apply H1.
      intros.
      cut (get i (feature_f nb_feature lambda) = lambda i).
      intro r.
      rewrite r.
      apply (H3 i H7).
      apply (def_feature_f i nb_feature lambda H7).
      split.
      unfold le_n.
      split.
      apply H1.
      split.
      rewrite <- H .
      apply (size_feature_f (length v) nu).
      intros.
      cut (get i (feature_f nb_feature nu) = nu i).
      intro r.
      rewrite r.
      apply (H3 i H7).
      apply (def_feature_f i nb_feature nu H7).
      apply H0.
      split.
      (* R3 *)
      unfold R3.
      unfold not.
      lia.
      split.
      (* R5 *)
      unfold R5.
      simpl.
      tauto.
      split.
      (* R6 *)
      unfold R6_CXp.
      simpl.
      tauto.
      split.
      (* R7 *)
      unfold R7_CXp.
      simpl.
      intros.
      split.   
      apply (def_feature_f j nb_feature lambda).
      lia.
      apply (def_feature_f j nb_feature nu).
      lia.
      split.
      (* R8 *)
      unfold R8.
      simpl.
      tauto.
      split.
      (* R9 *)
      unfold R9_CXp.
      simpl.
      lia.
      (* R10 *)
      unfold R10_CXp.
      simpl.
      intros.
      cut False.
      tauto.
      cut (x0 ++ x :: x1 <> nil).
      intro.
      auto.
      apply (list_mem_not_nil x (x0 ++ x :: x1)).
      apply list_mem_middle.
Qed.



Lemma pre_post_findCXp : forall (k : list T -> Tk) (v: list T), 
(
length v = nb_feature
/\ 
(forall (j:nat), j>=0 /\ j< nb_feature -> 
led (lambda j) (get j v) /\ led (get j v) (nu j))
)
/\ (stable k)
/\ (not_trivial k)
-> 
   is_weak_CXp k v (findCXp k v)
/\ is_sorted (findCXp k v)
/\ forall (x:nat), forall (x0 x1 : list nat), ((findCXp k v) = x0++(x::x1)
-> 
exists (nvl nvu : list T),
length nvl = nb_feature /\
length nvu = nb_feature /\
(forall (j:nat), j>=0 /\ j< nb_feature 
  ->  ((mem j x1 \/ j>x) /\ get j nvl =lambda j /\ get j nvu =nu j) 
        \/ ( (not (mem j x1 \/ j>x)) /\ get j nvl=get j v /\ get j nvu =get j v) ) 
/\ (k nvl) = (k nvu)).
Proof.
   intros.
   generalize (R_init_Cxp k v H).
   destruct H as (H,Hp).
   destruct Hp as (k_stable, k_not_trivial).
   intro HR.
   destruct HR as (HR0,HR).
   destruct HR as (HR1,HR).
   destruct HR as (HR2,HR).
   destruct HR as (HR3,HR).
   destruct HR as (HR5,HR).
   destruct HR as (HR6,HR).
   destruct HR as (HR7,HR).
   destruct HR as (HR8,HR).
   destruct HR as (HR9,HR10).
   split.
   (* post 1 *)
   generalize R_implies_E_findCXp.
   unfold R_implies_E_CXp.
   unfold E1_CXp.
   intros.
   unfold findCXp.
   apply H0.
   lia.
   tauto.
   split.
   (* post 2*)
   generalize R_implies_E_findCXp.
   unfold R_implies_E_CXp.
   unfold E2_CXp.
   intros.
   unfold findCXp.
   apply H0.
   lia.
   tauto.
   (* post 3*)
   generalize R_implies_E_findCXp.
   unfold R_implies_E_CXp.
   unfold E3_CXp.
   intro.
   unfold findCXp.
   apply H0.
   lia.
   tauto.
Qed.


Lemma weak_cxp_all : forall (k: list T -> Tk) (v :list T),
not_trivial k /\ stable k ->
(
length v = nb_feature
/\
(forall (j:nat), j>=0 /\ j< nb_feature -> 
  led (lambda j) (get j v) /\ led (get j v) (nu j))
-> is_weak_CXp k v (findCXp k v)).
Proof.
   intros.
   apply pre_post_findCXp.
   simpl.
   tauto.
Qed.



Lemma leq_weak_CXp_id : forall (k: list T -> Tk) (v:  list T) (l1 l2: list nat),
leq l1 l2 -> (is_weak_CXp k v l1 <-> is_weak_CXp k v l2).
Proof.
   intros.
   split.
   (* is_weak_CXp v l1 -> is_weak_CXp v l2*)
   unfold is_weak_CXp.
   unfold leq in H.
   intros.
   destruct H0. 
   destruct H0.
   destruct H1.
   destruct H2.
   exists x.
   split.
   apply H0.
   split.
   apply H1.
   split.
   apply H2.
   destruct H3.
   split.
   intros.
   generalize (H3 j);
   intro.
   generalize (H j).
   intro.
   rewrite <- H7.
   apply H3.
   apply H5.
   apply H4.
   (* is_weak_CXp v l2 -> is_weak_CXp v l1 *)
   unfold is_weak_CXp.
   unfold leq in H.
   intros.
   destruct H0. 
   destruct H0.
   destruct H1.
   destruct H2.
   exists x.
   split.
   apply H0.
   split.
   apply H1.
   split.
   apply H2.
   destruct H3.
   split.
   intros.
   generalize (H3 j);
   intro.
   generalize (H j).
   intro.
   rewrite H7.
   apply H3.
   apply H5.
   apply H4.
Qed.



Lemma not_weak_CXp_subset : forall (k: list T -> Tk) (v: list T) (p q:list nat),
not (is_weak_CXp k v q) /\ (is_strict_subset p q) -> not (is_weak_CXp k v p).
Proof.
   intros.
   destruct H.
   unfold is_weak_CXp.
   unfold is_weak_CXp in H.
   unfold is_strict_subset in H0.
   destruct H0.
   unfold not.
   intro.
   generalize H.
   unfold not.
   intro.
   unfold is_subset in H0.
   destruct H0 as (setp,H0).
   destruct H0 as (setq,H0).
   destruct H2.
   destruct H2.
   destruct H4.
   destruct H5.
   destruct H6.
   destruct H3.
   exists x.
   split.
   apply H2.
   split.
   apply H4.
   split.
   apply H5.
   split.
   intros.
   cut (mem j q \/ ~ mem j q).
   intro d.
   destruct d.
   right.
   apply H8.
   left.
   generalize (H6 j H3).
   intros.
   destruct H9.
   tauto.
   generalize (H0 j H9).
   tauto.
   apply mem_not_mem.
   apply H7.
Qed.


Lemma minus_one_implies_subset_CXp : forall (k: list T -> Tk) (v: list T) (p: list nat), 
   (forall (q:list nat), (is_minus_one q p) -> not (is_weak_CXp k v q))
-> (forall (q:list nat), (is_strict_subset q p) -> not (is_weak_CXp k v q)).
Proof.
   intros.
   cut (exists (q': list nat), (is_minus_one q' p) /\ is_subset q q').
   intro.
   destruct H1.
   destruct H1.
   cut (leq q x \/ is_strict_subset q x).
   intro d.
   destruct d.
   (* leq q x *)
   generalize (leq_weak_CXp_id k v q x).
   intro.
   destruct H4.
   auto.
   cut (~ is_weak_CXp k v x).
   auto.
   apply (H x).
   auto.
   (* is_strict_subset q x *)
   apply (not_weak_CXp_subset k v q x).
   cut (~ is_weak_CXp k v x).
   intro.
   tauto.
   apply (H x).
   auto.
   (* leq q x \/ is_strict_subset q x *)
   apply (is_subset_leq_or_is_strict_subset q x).
   auto.
   (* exists q' : list nat, is_minus_one q' p /\ is_subset q q' *)
   apply (minus_subset p q).
   auto.
Qed.


Lemma not_mem_append : forall (x0 x1  : list nat) (x i : nat),
is_sorted (x0 ++ x :: x1) /\ ~ mem i x1 /\ i <= x -> ~ mem i (x0++x1).
Proof.
   intros.
   destruct H.
   destruct H0.
   unfold not.
   intro.
   generalize (mem_append i x0 x1 H2).
   intro d.
   destruct d.
   generalize (sorted_middle_x0 x x0 x1 H i H3).
   lia.
   tauto.
Qed.


Lemma cxp_inter : forall (k : list T -> Tk),
not_trivial k /\ stable k ->
(
forall (v : list T),
length v = nb_feature
/\
(forall (j:nat), j>=0 /\ j< nb_feature -> 
  led (lambda j) (get j v) /\ led (get j v) (nu j))
-> 
(forall (x:nat) (x0 x1 : list nat), findCXp k v =x0++(x::x1) -> 
(forall (e:nat), mem e x1 -> e < x)
/\
(forall (e:nat), mem e x0 -> e > x)
/\
(exists  (vl vu : list T),
length vl = nb_feature /\
length vu = nb_feature /\
(forall j : nat,
    j >= 0 /\ j < nb_feature ->
    (mem j x1 \/ j > x) /\ get j vl = lambda j /\ get j vu = nu j \/
    ~ (mem j x1 \/ j > x) /\ get j vl = get j v /\ get j vu = get j v) /\
   k vl = k vu))).
Proof.
   intros k Pk.
   destruct Pk as (k_not_trivial,k_stable).
   intros.
   split.
   (* (forall e : nat, mem e x1 -> e < x) *)
   intros.
   cut (x>e).
   lia.
   apply (sorted_middle_x1 x x0 x1).
   rewrite <- H0.
   apply pre_post_findCXp.
   simpl.
   tauto.
   auto.
   split.
   (* forall e : nat, mem e x0 -> e > x *)
   intros.
   cut (x<e).
   lia.
   apply (sorted_middle_x0 x x0 x1).
   rewrite <- H0.
   apply pre_post_findCXp.
   simpl.
   tauto.
   auto.
   (* exsits .... *)
   generalize (pre_post_findCXp k v).
   intros.
   destruct H1.
   split.
   apply H.
   split.
   apply k_stable.
   apply k_not_trivial.
   destruct H2.
   apply (H3 x x0 x1).
   auto.
Qed.


Lemma minus_one_not_weak_CXp : forall (k : list T -> Tk) (v :list T),
not_trivial k /\ stable k
/\
length v = nb_feature
/\
(forall (j:nat), j>=0 /\ j< nb_feature -> 
  led (lambda j) (get j v) /\ led (get j v) (nu j))
-> forall (q:list nat), (is_minus_one q (findCXp k v)) -> not (is_weak_CXp k v q).
Proof.

(* idée :
p=x0++(x::x1) /\ q=x0++x1

quand on appel findCXp_aux x v vl vu x1
on fix x dans vl et vu => nvl, nvu
et comme x est dans le p final, ça veut dire qu'on a (k nvl) = (k nvu)
Et comme k est stable (k nvl) = (k nvu) = (k x)
nvl / nvu = 
  - v si pas dans x1 et =< x (donc v pour x)
  - borne sinon

Si q est weak_CXp de q, il y a f tq :
  - si pas dans q -> v
  - et k(f) <> k (x)
Pas possible car nvl < f < nvu et k stable

nvl < f < nvu car :
  - j < x
      - dans x1
         nvl / nvu : les bornes donc f entre les deux
      - pas dans x1 -> pas dans q
         f à v
         nvl / nvu à v
  - j = x
      x pas dans q donc - f à v
      nvl / nvu à v puisqu'on a fait le fix sur x
  - j > x
    nvl / nvu : les bornes donc f entre les deux
  *)
intros.
destruct H as (k_not_trivial,H).
destruct H as (k_stable,H).
cut (exists (x:nat) (x0 x1 :list nat),
  (findCXp k v = (x0++(x::x1))) /\ (q = x0++x1)).
intros.
destruct H1.
destruct H1.
destruct H1.
destruct H1 as (decomp_find,defq).
destruct H as (Lv,H).
cut (exists  (vl vu : list T),
length vl = nb_feature /\ length vu = nb_feature /\
(forall (j:nat), j>=0 /\ j< nb_feature 
->  ((mem j x1 \/ j>x) /\ get j vl=lambda j /\ get j vu=nu j ) 
\/ ( (not (mem j x1 \/ j>x)) /\ get j vl=get j v/\ get j vu = get j v))
/\ (k vl) = (k vu)).
intros (vl,(vu,(Lvl,(Lvu,(vali,eqclasse))))).
unfold not.
unfold is_weak_CXp.
intros.
cut (k vl <> k vu /\ k vl = k vu).
tauto.
split.
(* k vl <> k vu *)
destruct H1.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
unfold not.
intro.
   (* vl <= x2 <= vu *)
   (* vl <= v <= vu *)
   (* stable + k vl = k vu -> k x2 = k vl *)
   (* stable + k vl = k vu -> k v = k vl *)
   (* contradiction avec k x2 <> k v *)
   cut (k x2 = k v).
   tauto.
   cut (k x2 = k vl).
   cut (k v = k vl).
   intros r1 r2.
   rewrite r1.
   rewrite r2.
   reflexivity.
      (* k v = k vl *)
      generalize k_stable.
      unfold stable.
      intro kstable.
      symmetry.
      apply (kstable vl vu v).
      split.
      apply Lvl.
      split.
      apply Lvu.
      split.
      apply Lv.
      split.
      intros.
      generalize (vali i H7).
      intro d.
      destruct d.
      destruct H8.
      destruct H9.
      rewrite H9.
      split.
      apply led_eq.
      reflexivity.
      apply (led_transitivity (lambda i) (get i v) (nu i)).
      apply (H i H7).
      destruct H8.
      destruct H9.
      rewrite H9.
      apply (H i H7).
      split.
      intros.
      generalize (vali i H7).
      intro d.
      destruct d.
      destruct H8.
      destruct H9.
      rewrite H10.
      split.
      apply (led_transitivity (lambda i) (get i v) (nu i)).
      apply (H i H7).
      apply led_eq.
      reflexivity.
      destruct H8.
      destruct H9.
      rewrite H10.
      apply (H i H7).
      split.
      apply H.
      split.
      unfold le_n.
      split.
      apply Lvl.
      split.
      apply Lv.
      intros.
      generalize (vali i H7).
      intro d.
      destruct d.
      destruct H8.
      destruct H9.
      rewrite H9.
      apply (H i H7).
      destruct H8.
      destruct H9.
      rewrite H9.
      apply led_eq.
      reflexivity.
      split.
      unfold le_n.
      split.
      apply Lv.
      split.
      apply Lvu.
      intros.
      generalize (vali i H7).
      intro d.
      destruct d.
      destruct H8.
      destruct H9.
      rewrite H10.
      apply (H i H7).
      destruct H8.
      destruct H9.
      rewrite H10.
      apply led_eq.
      reflexivity.
      apply H6.
      (* k x2 = k vl *)
      generalize k_stable.
      unfold stable.
      intro kstable.
      symmetry.
      apply (kstable vl vu x2).
      split.
      apply Lvl.
      split.
      apply Lvu.
      split.
      apply H2.
      split.
      intros.
      generalize (vali i H7).
      intro d.
      destruct d.
      destruct H8.
      destruct H9.
      rewrite H9.
      split.
      apply led_eq.
      reflexivity.
      apply (led_transitivity (lambda i) (get i v) (nu i)).
      apply (H i H7).
      destruct H8.
      destruct H9.
      rewrite H9.
      apply (H i H7).
      split.
      intros.
      generalize (vali i H7).
      intro d.
      destruct d.
      destruct H8.
      destruct H9.
      rewrite H10.
      split.
      apply (led_transitivity (lambda i) (get i v) (nu i)).
      apply (H i H7).
      apply led_eq.
      reflexivity.
      destruct H8.
      destruct H9.
      rewrite H10.
      apply (H i H7).
      split.
      apply H3.
      split.
      unfold le_n.
      split.
      apply Lvl.
      split.
      apply H2.
      intros.
      generalize (vali i H7).
      intro d.
      destruct d.
      destruct H8.
      destruct H9.
      rewrite H9.
      apply (H3 i H7).
      destruct H8.
      destruct H9.
      rewrite H9.
      cut (get i x2 = get i v).
      intro.
      rewrite H11.
      apply led_eq.
      reflexivity.
      generalize (H4 i H7).
      cut (~ mem i q).
      tauto.
      rewrite defq.
      apply (not_mem_append x0 x1 x i).
      split.
      rewrite <- decomp_find.
      apply (pre_post_findCXp k v).
      split.
      split.
      apply Lv.
      apply H.
      split.
      apply k_stable.
      apply k_not_trivial.
      split.
      tauto.
      lia.
      split.
      unfold le_n.
      split.
      apply H2.
      split.
      apply Lvu.
      intros.
      generalize (vali i H7).
      intro d.
      destruct d.
      destruct H8.
      destruct H9.
      rewrite H10.
      apply (H3 i H7).
      destruct H8.
      destruct H9.
      rewrite H10.
      cut (get i x2 = get i v).
      intro.
      rewrite H11.
      apply led_eq.
      reflexivity.
      generalize (H4 i H7).
      cut (~ mem i q).
      tauto.
      rewrite defq.
      apply (not_mem_append x0 x1 x i).
      split.
      rewrite <- decomp_find.
      apply (pre_post_findCXp k v).
      split.
      split.
      apply Lv.
      apply H.
      split.
      apply k_stable.
      apply k_not_trivial.
      split.
      tauto.
      lia.
      apply H6.
(* k vl = k vu *)
apply eqclasse.

(* existsvl vu : T, ... *)
cut (
  (forall (e:nat), mem e x1 -> (e < x)) /\
  (forall (e:nat), mem e x0 -> (x < e)) /\
  (exists vl vu : list T,
  length vl = nb_feature /\
  length vu = nb_feature /\
  (forall j : nat,
  j >= 0 /\ j < nb_feature ->
   (mem j x1 \/ j > x) /\ get j vl = lambda j /\ get j vu = nu j \/
   ~ (mem j x1 \/ j > x) /\ get j vl = get j v /\ get j vu = get j v) /\
  k vl = k vu)).
intro inter.
destruct inter as (inf,inter).
destruct inter as (sup,inter).
apply inter.
apply cxp_inter.
split.
apply k_not_trivial.
apply k_stable.
split.
apply Lv.
apply H.
apply decomp_find.

(* exists (x : nat) (x0 x1 : list nat),
  findCXp v = x0 ++ x :: x1 /\ q = x0 ++ x1 *)
generalize H0.
unfold is_minus_one.
auto.
Qed.

Theorem cxp_all : forall (k: list T -> Tk) (v:list T),
not_trivial k /\ stable k ->
(
length v = nb_feature
/\
(forall (j:nat), j>=0 /\ j< nb_feature -> 
  led (lambda j) (get j v) /\ led (get j v) (nu j))
-> is_CXp k v (findCXp k v)).
Proof.
   intros.
   unfold is_CXp.
   split.
   apply weak_cxp_all.
   apply H.
   tauto.
   intro.
   apply (minus_one_implies_subset_CXp k v (findCXp k v)) .
   apply minus_one_not_weak_CXp.
   tauto.
Qed.



End Classifier.

Extraction Language OCaml.
Extraction "findAXpCXp" findAXp findCXp.