Require Import Program.Equality.
Require Import LibTactics.
Require Import Metalib.Metatheory. 

Require Import Language 
               Infra
               SubDis
               Determinism.

(* --------- lambdai -------- *)
Definition i : Set := nat.

Definition sctx : Set := list ( i * typ ).

Inductive sexp :=  
  | se_i : nat -> sexp
  | se_lit : nat -> sexp
  | se_unit : sexp 
  | se_abs : nat -> sexp -> sexp
  | se_app : sexp -> sexp -> sexp
  | se_merge : sexp -> sexp -> sexp.

Inductive lityp : typ -> Prop :=   
  | li_int : lityp int
  | li_top : lityp top
  | li_arr : forall (A B:typ),
      lityp A ->
      lityp B ->
      lityp (arr A B)
  | li_and : forall (A B:typ),
      lityp A ->
      lityp B ->
      lityp (and A B).

Definition sbinds (x : i) (A : typ) (E : list (i * typ)) : Prop := In (x, A) E.

Fixpoint sdom (E : list (i * typ)) {struct E} : list i :=
  match E with
    | nil => nil
    | (x, A) :: E' => cons x (sdom E')
  end.

Inductive suniq : list (i * typ) -> Prop :=
  | suniq_nil :
      suniq nil
  | suniq_push : forall x A E,
      suniq E ->
      ~ In x (sdom E) ->
      suniq (cons (x, A) E).

(* from normal contexts to types *)
Fixpoint ctx_sw (E : list (i * typ)) {struct E} : typ :=
  match E with
    | nil => top
    | (x, A) :: E' => and (ctx_sw E') (rcd x A)
  end.

Inductive contains: nat -> typ -> Prop:=
  | ct_rcd : forall x A,
      contains x (rcd x A)
  | ct_andl : forall x A B,
      contains x A ->
      contains x (and A B)
  | ct_andr : forall x A B,
      contains x B ->
      contains x (and A B).

Definition fresh x A := ~ (contains x A).

Inductive styping : sctx -> sexp -> typ -> exp -> Prop :=   
  | styping_lit : forall (G:sctx) (i5:i),
      suniq  G  ->
      styping G (se_lit i5) int (lit i5)
  | styping_top : forall (G:sctx),
      suniq  G  ->
      styping G se_unit top unit
  | styping_var : forall (G:sctx) (x:i) (A:typ),
      suniq G  ->
      sbinds  x A G  ->
      lityp A ->
      styping G (se_i x) A (proj  ( (ann ctx (rcd x A)) )  x)
  | styping_abs : forall (G:sctx) (x:i) (A:typ) (ee:sexp) (B:typ) (e:exp),
      styping  (cons ( x , A )  G )  ee B e ->
      lityp A ->
      lityp B ->
      styping G (se_abs x ee) (arr A B) (ann (lam wh e) (arr (rcd x A) B))
  | styping_app : forall (G:sctx) (ee1 ee2:sexp) (B:typ) (e1 e2:exp) (A:typ),
      styping G ee1 (arr A B) e1 ->
      styping G ee2 A e2 ->
      lityp A ->
      lityp B ->
      styping G (se_app ee1 ee2) B (app e1 e2)
  | styping_merge : forall (G:sctx) (ee1 ee2:sexp) (B:typ) (e1 e2:exp) (A:typ) (m:nat),
    styping G ee1 A e1 ->
    styping G ee2 B e2 ->
    lityp A ->
    lityp B ->
    disjoint A B ->
    fresh m A ->
    styping G (se_merge ee1 ee2) (and A B) (box (rec m ctx) (merge (box (proj ctx m) e1) (box (proj (ann ctx (rcd m (ctx_sw G))) m) e2)))
  | styping_sub : forall (G:sctx) (ee1 ee2:sexp) (B:typ) (e1 e2:exp) (A:typ) (m:nat),
    styping G ee1 A e1 ->
    lityp A ->
    lityp B ->
    sub A B ->
    styping G ee1 B (ann e1 B).

#[export]
Hint Constructors sexp lityp suniq contains styping: core.
(* ---------------- *)

Section ListProperties.
  Variables X : Set.
  Variables x y : X.
  Variables l l1 l2 l3 : list X.

Lemma in_one : 
  List.In x [ y ] <-> x = y.
Proof. clear. simpl. intuition congruence. 
Qed.

Lemma in_app :
  List.In x (l1 ++ l2) <-> List.In x l1 \/ List.In x l2.
Proof. clear. split; auto using in_or_app, in_app_or. 
Qed.

Lemma in_cons:
  List.In x (cons y l) -> x = y \/ List.In x l.
Proof.
  clear. simpl. intuition congruence.
Qed.

End ListProperties.


Lemma fresh_and: forall x A B,
  fresh x (and A B) ->
  fresh x A /\ fresh x B.
Proof.
  introv Hf. unfold fresh in *.
  split*.
Qed.

Lemma fresh_rcd: forall x1 x2 A,
  fresh x1 (rcd x2 A) ->
  x1 <> x2.
Proof.
  introv Hf. unfold fresh in *. intros H. subst*. 
Qed.

Lemma not_ct_dis: forall A x,
  fresh x A -> forall B,
  disjoint (rcd x B) A.
Proof.
  intros A. inductions A; introv Hnc; intros B.
  - unfold disjoint. intros Hc. eapply costs_sym in Hc.
    eapply costs_int_rcd; eauto.
  - unfold disjoint. intros Hc. eapply costs_sym in Hc.
    eapply costs_top_any; eauto.
  - forwards* (?&?): fresh_and Hnc.
    forwards* :IHA1 H B. forwards* :IHA2 H0 B.
    eapply dis_sym. eapply dis_to_inter; 
    try solve [eapply dis_sym; eauto].
  - forwards*: fresh_rcd Hnc.
    unfold disjoint. intros Hc.
    forwards*: costs_rcd_rcd_neq H Hc.
  - unfold disjoint. intros Hc. 
    eapply costs_arr_rcd; eauto.
Qed.

Lemma ctx_suniq: forall G ee B e,
  styping G ee B e ->
  suniq G.
Proof.
  introv Typ.
  lets Typ': Typ.
  inductions Typ; try eauto.
  - forwards~: IHTyp Typ. inverts* H1.
Qed.

Lemma notin_dis: forall x G,
  ~ In x (sdom G) -> forall A,
  disjoint (rcd x A) (ctx_sw G).
Proof.
  introv Hnot. inductions G; intros A.
  - simpl. eapply dis_sym. unfold disjoint. eapply costs_top_any. 
  - simpl. simpl in Hnot. destruct a.
    assert (x <> i0) as Hin1. {
      intros Hbot. eapply Hnot. simpl. left. eauto.
    }
    assert (~ In x (sdom G)) as Hin2. {
      intros Hbot. eapply Hnot. simpl. right*.
    }
    eapply dis_sym. eapply dis_to_inter.
    eapply dis_sym. eapply IHG. eauto.
    unfold disjoint. intros Hc. eapply costs_rcd_rcd_neq; eauto. eapply costs_sym. eauto. 
Qed.

Theorem encoding_complete: forall sctx A ee e,
  styping sctx ee A e ->
  has_type (ctx_sw sctx) e inf A.
Proof.
  introv Typ.
  inductions Typ; eauto.
  - econstructor; try eauto. econstructor.
    inductions G.
    + inverts* H0.
    + unfold sbinds in H0.
      forwards~ [He|Hnot]: in_cons H0.
      * simpl. subst. eauto.
      * econstructor.
        econstructor.
        simpl.
        destruct a.
        inverts H.
        forwards~: IHG H4 Hnot.
        inverts H. inverts* H2.
  - econstructor; try eauto. 
    simpl in IHTyp.
    forwards~ Huq: ctx_suniq Typ.
    inverts* Huq.
    eapply dis_sym.
    eapply notin_dis.
    eauto. 
  - econstructor; try eauto.
    econstructor; eauto.
    + econstructor; eauto.
    + eapply not_ct_dis. eauto.
Qed.