Require Import List.
Export ListNotations.

Require Import genT gen.
Require Import ddT.
Require Import gen_tacs.
Require Import gen_seq.
Require Import List_lemmasT.
Require Import existsT.
Require Import univ_gen_ext.
Require Import dd_fc.
Require Import PeanoNat.




Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

Global Parameter V : Set.

Parameter eq_dec_propvar : forall x y : V, {x = y}+{x <> y}.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* In this file we define two calculi based on multisets for the propositonal modal logic
   GL. The first one, called MGL, is the main calculus for GL. The second one, named PSMGL,
   is essentially the calculus MGL with further restrictions on the application of the
   rules. In other words, the calculus PSMGL is a proof-search oriented version of MGL. *)

(* Definitions Language *)

(* First, let us define the propositional formulae we use here. *)

Inductive MPropF (W : Set) : Type :=
 | Var : W -> MPropF W
 | Bot : MPropF W
 | Imp : MPropF W -> MPropF W -> MPropF W
 | Box : MPropF W -> MPropF W
.

Notation "# P" := (Var P) (at level 1) : My_scope.
Notation "A → B" := (Imp A B) (at level 16, right associativity) : My_scope.
Notation "⊥" := Bot (at level 0)  : My_scope.

Lemma eq_dec_form : forall x y : MPropF V, {x = y}+{x <> y}.
Proof.
induction x.
- intros. destruct y.
  * pose (eq_dec_propvar v w). destruct s. left. subst. reflexivity.
    right. intro. inversion H. apply n. symmetry in H1. assumption.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * left. reflexivity.
  * right. intro. inversion H.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * pose (IHx1 y1). pose (IHx2 y2). destruct s. destruct s0. subst. left. reflexivity.
    right. intro. inversion H. apply n. assumption. right. intro. inversion H. apply n.
    assumption.
  * right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * pose (IHx y). destruct s. subst. left. reflexivity.
    right. intro. inversion H. apply n. assumption.
Qed.

Fixpoint size_form (A : MPropF V) : nat :=
match A with
 | # P => 1
 | Bot _ => 1
 | Imp B C => 1 + (size_form B) + (size_form C)
 | Box B => 1 + (size_form B)
end.


(* Now, we can prove that some properties of formulae hold. *)

Definition is_atomicT {V : Set} (A : MPropF V) : Type :=
                  (existsT2 (P : V), A = # P) + (A = Bot V).

Definition is_boxedT {V : Set} (A : MPropF V) : Type :=
                  exists (B : MPropF V), A = Box B.

Definition is_primeT {V : Set} (A : MPropF V) : Type :=
                  is_atomicT A + is_boxedT A.

(* We can define some types of lists formulae. For example, we can define
   lists of formulae which contain only propositional variables, or
   boxed formulae, or a combination of both. These are useful to define
   the rules. *)

Definition is_Atomic {V : Set} (Γ : list (MPropF V)) : Prop :=
    forall (A : MPropF V), (In A Γ) -> ((exists (P : V), A = # P) \/ (A = Bot V)).

Definition is_Boxed_list {V : Set} (Γ : list (MPropF V)) : Prop :=
    forall (A : MPropF V), (In A Γ) -> (exists (B : MPropF V), A = Box B).

Definition is_Prime {V : Set} (Γ : list (MPropF V)) : Prop :=
    forall (A : MPropF V), (In A Γ) ->
    (exists (B : MPropF V), A = Box B) \/ (exists (P : V), A = # P) \/ (A = Bot V).

(* With these properties we can define restrictions of univ_gen_ext on
   formulae. *)

Definition atom_gen_ext {V : Set} := univ_gen_ext (fun x => (@is_atomicT V x)).

Definition nobox_gen_ext {V : Set} := univ_gen_ext (fun x => (@is_boxedT V x) -> False).

Definition prim_gen_ext {V : Set} := univ_gen_ext (fun x => (@is_primeT V x)).

(* Some lemmas about gen_ext. *)

Lemma nobox_gen_ext_injective : forall (l0 l1 l : list (MPropF V)), (is_Boxed_list l0) -> (is_Boxed_list l1) ->
                                (nobox_gen_ext l0 l) -> (nobox_gen_ext l1 l) -> l1 = l0.
Proof.
intros l0 l1 l Hl0 Hl1 gen. generalize dependent l1.
induction gen.
- intros. inversion X. reflexivity.
- intros. inversion X.
  * subst. assert (l0 = l). apply IHgen. intro. intros. apply Hl0. apply in_cons. assumption.
    intro. intros. apply Hl1. apply in_cons. assumption. assumption. rewrite H. reflexivity.
  * subst. exfalso. apply H1. apply Hl0. apply in_eq.
- intros. apply IHgen. intro. intros. apply Hl0. assumption.
  intro. intros. apply Hl1. assumption. inversion X.
  subst. exfalso. apply p. apply Hl1. apply in_eq. subst. assumption.
Qed.

(* The next definitions help to define the combination of a list of boxed
   formulae and the unboxing of all the formulae in that list. *)

Definition unBox_formula {V : Set} (A : MPropF V) : MPropF V :=
  match A with
              | # P => # P
              | Bot _ => Bot _
              | A → B => A → B
              | Box A => A
              end
.

Fixpoint XBoxed_list {V : Set} (Γ : list (MPropF V)) : list (MPropF V):=
  match Γ with
  | [ ] => [ ]
  | h :: t => (unBox_formula h :: h :: XBoxed_list t)
  end
.

Fixpoint top_boxes (l : list (MPropF V)) : list (MPropF V) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Box A => (Box A) :: top_boxes t
                | _ => top_boxes t
              end
end.


(* Now that we have defined these, we can prove some properties about them. *)

Lemma XBox_app_distrib {V : Set} :
  forall (l1 l2: list (MPropF V)), XBoxed_list (l1 ++ l2) = (XBoxed_list l1) ++ (XBoxed_list l2).
Proof.
induction l1.
- intro l2. rewrite app_nil_l with (l:=l2). simpl. reflexivity.
- intro l2. simpl. rewrite IHl1. reflexivity.
Qed.

Lemma subl_of_boxl_is_boxl {V : Set}:
  forall (l1 l2: list (MPropF V)), (incl l1 l2) -> (is_Boxed_list l2) -> (is_Boxed_list l1).
Proof.
intros. unfold is_Boxed_list. intros. apply H in H1. apply H0 in H1.
destruct H1. exists x. assumption.
Qed.

Lemma tl_of_boxl_is_boxl {V : Set}:
  forall (h : MPropF V) (t l : list (MPropF V)) (H: l = h :: t),
         (is_Boxed_list l) -> (is_Boxed_list t).
Proof.
intros. unfold is_Boxed_list. intros. assert (Hyp: In A l).
rewrite H. simpl. right. apply H1. apply H0 in Hyp. destruct Hyp.
exists x. assumption.
Qed.

Lemma list_preserv_XBoxed_list : forall (l : list (MPropF V)), incl l (XBoxed_list l).
Proof.
induction l.
- simpl. unfold incl. intros. inversion H.
- simpl. unfold incl. intros. inversion H.
  * subst. apply in_cons. apply in_eq.
  * apply in_cons. apply in_cons. apply IHl. assumption.
Qed.

Lemma is_box_is_in_boxed_list : forall l (A : MPropF V), In A l -> is_Boxed_list l -> (exists B, Box B = A).
Proof.
induction l.
- intros. inversion H.
- intros. inversion H.
  + subst. unfold is_Boxed_list in H0. pose (H0 A).
    apply e in H. destruct H. exists x. symmetry. assumption.
  + apply IHl. assumption. unfold is_Boxed_list. intros. unfold is_Boxed_list in H0.
    pose (H0 A0). apply e. apply in_cons. assumption.
Qed.


Lemma top_boxes_distr_app : forall (l1 l2 : list (MPropF V)),
      top_boxes (l1 ++ l2) = (top_boxes l1) ++ (top_boxes l2).
Proof.
induction l1.
- intro l2. rewrite app_nil_l. simpl. reflexivity.
- intro l2. simpl. destruct a ; try apply IHl1.
  simpl. rewrite IHl1. reflexivity.
Qed.

Lemma box_in_top_boxes : forall l1 l2 A, existsT2 l3 l4, top_boxes (l1 ++ Box A :: l2) = l3 ++ Box A :: l4.
Proof.
intros. exists (top_boxes l1). exists (top_boxes l2). rewrite top_boxes_distr_app. auto.
Qed.

Lemma is_Boxed_list_top_boxes : forall l, is_Boxed_list (top_boxes l).
Proof.
intros. induction l.
- simpl. intro. intros. inversion H.
- intro. destruct a.
  + simpl. intros. apply IHl in H. assumption.
  + simpl. intros. apply IHl in H. assumption.
  + simpl. intros. apply IHl in H. assumption.
  + simpl. intros. destruct H.
    * exists a. auto.
    * apply IHl. assumption.
Qed.

Lemma nobox_gen_ext_top_boxes : forall l, nobox_gen_ext (top_boxes l) l.
Proof.
induction l.
- simpl. apply univ_gen_ext_refl.
- destruct a.
  * simpl. apply univ_gen_ext_extra. intros. inversion X. inversion H. assumption.
  * simpl. apply univ_gen_ext_extra. intros. inversion X. inversion H. assumption.
  * simpl. apply univ_gen_ext_extra. intros. inversion X. inversion H. assumption.
  * simpl. apply univ_gen_ext_cons. assumption.
Qed.




(* Finally, we can define the rules which constitute our calculi. We gather
   them in cacluli in a definition appearing later.

   We start by giving the rules common to both calculi. *)

Inductive IdPRule {V : Set} : rlsT (rel (list (MPropF V))) :=
  | IdPRule_I : forall (P : V) (Γ0 Γ1 Δ0 Δ1 : list (MPropF V)), 
          IdPRule [] (pair (Γ0 ++ # P :: Γ1) (Δ0 ++ # P :: Δ1))
.

Inductive IdBRule {V : Set} : rlsT (rel (list (MPropF V))) :=
  | IdBRule_I : forall A Γ0 Γ1 Δ0 Δ1, 
          IdBRule [] (pair (Γ0 ++ Box A :: Γ1) (Δ0 ++ Box A :: Δ1))
.

Inductive BotLRule {V : Set} : rlsT (rel (list (MPropF V))) :=
  | BotLRule_I : forall Γ0 Γ1 Δ,
          BotLRule [] (pair (Γ0 ++ (Bot V) :: Γ1) Δ)
.

Inductive ImpRRule {V : Set} : rlsT (rel (list (MPropF V))) :=
  | ImpRRule_I : forall A B Γ0 Γ1 Δ0 Δ1,
          ImpRRule [(pair (Γ0 ++ A :: Γ1) (Δ0 ++ B :: Δ1))]
                    (pair (Γ0 ++ Γ1) (Δ0 ++ (A → B) :: Δ1))
.

Inductive ImpLRule {V : Set} : rlsT (rel (list (MPropF V))) :=
  | ImpLRule_I : forall A B Γ0 Γ1 Δ0 Δ1,
          ImpLRule ((pair (Γ0 ++ Γ1) (Δ0 ++ A :: Δ1)) ::
                     [(pair (Γ0 ++ B :: Γ1) (Δ0 ++ Δ1))])
                    (pair (Γ0 ++ (A → B) :: Γ1) (Δ0 ++ Δ1))
.

(* Then we turn to the distinctive rules of each calculus.

   The next rule contains arbitrary weakening. It will be a crucial
   rule of the MGL calculus. *)

Inductive GLRRule {V : Set} : rlsT (rel (list (MPropF V))) :=
  | GLRRule_I : forall A BΓ Γ0 Δ0 Δ1,
          (is_Boxed_list BΓ) -> (* have MS of boxed formulae prem L*)
          (nobox_gen_ext BΓ Γ0) -> (* extend BΓ in Γ0, the L of the ccl *)
         GLRRule [(pair ((XBoxed_list BΓ) ++ [Box A]) [A])] (pair Γ0 (Δ0 ++ Box A :: Δ1))
.

(* At last we can define our calculus GLS and its proof-search version PSGLS. *)

Inductive GLS_rules {V : Set} : rlsT (rel (list (MPropF V))) :=
  | IdP : forall ps c, IdPRule ps c -> GLS_rules ps c
  | BotL : forall ps c, BotLRule ps c -> GLS_rules ps c
  | ImpR : forall ps c, ImpRRule ps c -> GLS_rules ps c
  | ImpL : forall ps c, ImpLRule ps c -> GLS_rules ps c
  | GLR : forall ps c, GLRRule ps c -> GLS_rules ps c
.

Inductive PSGLS_rules {V : Set} : rlsT (rel (list (MPropF V))) :=
  | PSIdP : forall ps c, IdPRule ps c -> PSGLS_rules ps c
  | PSIdB : forall ps c, IdBRule ps c -> PSGLS_rules ps c
  | PSBotL : forall ps c, BotLRule ps c -> PSGLS_rules ps c
  | PSImpR : forall ps c, ImpRRule ps c ->
                          PSGLS_rules ps c
  | PSImpL : forall ps c, ImpLRule ps c ->
                          PSGLS_rules ps c
  | PSGLR : forall ps c, (IdPRule [] c -> False) ->
                       (IdBRule [] c -> False) ->
                       (BotLRule [] c -> False) ->
                       GLRRule ps c ->
                         PSGLS_rules ps c
.

(* We can show that the rule IdB is derivable in GLS. *)

Lemma Id_all_form : forall (A : MPropF V) l0 l1 l2 l3,
          derrec (@GLS_rules V) (fun _ => False) (l0 ++ A :: l1, l2 ++ A :: l3).
Proof.
assert (DersNilF: dersrec (GLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => False) []).
apply dersrec_nil.

induction A.
- intros. assert (IdPRule [] (l0 ++ # w :: l1, l2 ++ # w :: l3)). apply IdPRule_I. apply IdP in H.
  pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False) (ps:=[])
  (l0 ++ # w :: l1, l2 ++ # w :: l3) H DersNilF). assumption.
- intros. assert (BotLRule [] (l0 ++ ⊥ V :: l1, l2 ++ ⊥ V :: l3)). apply BotLRule_I. apply BotL in H.
  pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False) (ps:=[])
  (l0 ++ ⊥ V :: l1, l2 ++ ⊥ V :: l3) H DersNilF). assumption.
- intros. assert (ImpRRule [(l0 ++ A1 :: A1 → A2 :: l1, l2 ++ A2 :: l3)] (l0 ++ A1 → A2 :: l1, l2 ++ A1 → A2 :: l3)).
  apply ImpRRule_I. apply ImpR in H.
  assert (ImpLRule [((l0 ++ [A1]) ++ l1, l2 ++ A1 :: A2 :: l3); ((l0 ++ [A1]) ++ A2 :: l1, l2 ++ A2 :: l3)] ((l0 ++ [A1]) ++ A1 → A2 :: l1, l2 ++ A2 :: l3)).
  apply ImpLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0. apply ImpL in H0.
  pose (IHA1 l0 l1 l2 (A2 :: l3)). pose (IHA2 (l0 ++ [A1]) l1 l2 l3). repeat rewrite <- app_assoc in d0. simpl in d0.
  pose (dlCons d0 DersNilF). pose (dlCons d d1).
  pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False) (ps:=[(l0 ++ A1 :: l1, l2 ++ A1 :: A2 :: l3); (l0 ++ A1 :: A2 :: l1, l2 ++ A2 :: l3)])
  (l0 ++ A1 :: A1 → A2 :: l1, l2 ++ A2 :: l3) H0 d2). pose (dlCons d3 DersNilF).
  pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False) (ps:=[(l0 ++ A1 :: A1 → A2 :: l1, l2 ++ A2 :: l3)])
  (l0 ++ A1 → A2 :: l1, l2 ++ A1 → A2 :: l3) H d4). assumption.
- intros. assert (GLRRule [(XBoxed_list (top_boxes (l0 ++ Box A :: l1)) ++ [Box A], [A])] (l0 ++ Box A :: l1, l2 ++ Box A :: l3)).
  apply GLRRule_I. apply is_Boxed_list_top_boxes. rewrite top_boxes_distr_app. simpl. apply univ_gen_ext_combine.
  apply nobox_gen_ext_top_boxes. apply univ_gen_ext_cons. apply nobox_gen_ext_top_boxes.
  rewrite top_boxes_distr_app in X. simpl in X. rewrite XBox_app_distrib in X. simpl in X.
  repeat rewrite <- app_assoc in X. simpl in X.
  pose (IHA (XBoxed_list (top_boxes l0)) (Box A :: XBoxed_list (top_boxes l1) ++ [Box A]) [] []).
  simpl in d. pose (dlCons d DersNilF). apply GLR in X.
  pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False) (ps:=[(XBoxed_list (top_boxes l0) ++ A :: Box A :: XBoxed_list (top_boxes l1) ++ [Box A], [A])])
  (l0 ++ Box A :: l1, l2 ++ Box A :: l3) X d0). assumption.
Qed.
