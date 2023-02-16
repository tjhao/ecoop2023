Require Import Program.Equality.
Require Import LibTactics.
Require Import Metalib.Metatheory. 
Require Import Language.

Lemma and_inversion : forall A B C,
  sub A (and B C) -> 
  sub A B /\ sub A C.
Proof.
  intros A B C H.
  inductions H; eauto.
  - lets*: IHsub B C.
  - lets*: IHsub B C.
Qed.

Lemma sub_reflexivity : forall A,
  sub A A.
Proof.
  intros A.
  induction* A.
Qed.

Lemma sub_transtivity : forall B A C,
  sub A B -> 
  sub B C -> 
  sub A C.
Proof with eauto.
  introv S1 S2. gen A C.
  induction B; intros;
    try solve [inductions S2; eauto].
  - forwards* (?&?): and_inversion S1.
    inductions S2...
  - inductions S2...
    clear IHS2.
    inductions S1...
  - inductions S2...
    clear IHS2_1 IHS2_2.
    inductions S1...
Qed.

#[export]
Hint Resolve sub_reflexivity sub_transtivity: core.

Lemma sub_inversion_and_l : forall A1 A2 B,
  sub (and A1 A2) B -> 
  sub A1 B \/ sub A2 B \/ exists B1 B2, B = 
  and B1 B2.
Proof.
  intros.
  inverts* H.
Qed.

Lemma sub_inversion_arrow : forall A1 A2 B1 B2,
  sub (arr A1 A2) (arr B1 B2) -> 
  sub B1 A1 /\ sub A2 B2.
Proof.
  intros.
  inverts* H.
Qed.

(* -------- costs -------- *)
Lemma costs_and: forall A B C, 
  cost_spec A (and B C) ->
  cost_spec A B \/ cost_spec A C.
Proof.
  intros; unfold cost_spec in *.
  destruct H. destruct H. destruct H0.
  forwards~ [C1|[C2|C3]]: sub_inversion_and_l H1.
  - left*.
  - right*.
  - inverts* C3. inverts* H2. inverts* H.
Qed.

Lemma costs_sym : forall A B, cost_spec A B -> cost_spec B A.
Proof.
  intros.
  unfold cost_spec in *.
  destruct H.
  dependent destruction H.
  dependent destruction H0.
  exists x; eauto.
Qed.

Lemma costs_to_and_left: forall A B, 
  cost_spec A B -> forall C,
  cost_spec A (and B C).
Proof.
  intros; unfold cost_spec in *.
  destruct H. destruct H. destruct H0. exists* x.
Qed.

Lemma costs_to_and_right: forall A C, 
  cost_spec A C -> forall B,
  cost_spec A (and B C).
Proof.
  intros; unfold cost_spec in *.
  destruct H. destruct H. destruct H0. exists* x.
Qed.

Lemma not_costs_and_left: forall A B C,
  ~ cost_spec A (and B C) ->
  ~ cost_spec A B.
Proof.
  introv H Hc. eapply H. eapply costs_to_and_left. eauto.
Qed.

Lemma not_costs_and_right: forall A B C,
  ~ cost_spec A (and B C) ->
  ~ cost_spec A C.
Proof.
  introv H Hc. eapply H. eapply costs_to_and_right. eauto.
Qed.

Lemma not_costs_to_and: forall A B C,
  ~ cost_spec A B ->
  ~ cost_spec A C ->
  ~ cost_spec A (and B C).
Proof.
  introv Hc1 Hc2 Hc. 
  forwards~ [C1|C2]: costs_and Hc.
Qed.

Lemma costs_rcd_inv : forall l A B, 
  cost_spec (rcd l A) (rcd l B) ->
  cost_spec A B.
Proof.
  introv H. unfold cost_spec in *.
  destruct* H. destruct* H. destruct* H0.
  inverts* H.
  - inverts* H1.
  - inverts* H1.
  - inverts* H1. inverts* H0.
Qed.

Lemma costs_arr_inv : forall A1 A2 B1 B2, 
  cost_spec (arr A1 A2) (arr B1 B2) ->
  cost_spec A2 B2.
Proof.
  introv H. unfold cost_spec in *.
  destruct* H. destruct* H. destruct* H0.
  inverts* H.
  - inverts* H1.
  - inverts* H1. inverts* H0.
  - inverts* H1.
Qed.

Lemma costs_to_arr : forall A1 A2 B1 B2,
  cost_spec A2 B2 -> 
  cost_spec (arr A1 A2) (arr B1 B2).
Proof.
  introv H. unfold cost_spec in *.
  destruct* H. destruct* H. destruct* H0. exists* (arr (and A1 B1) x).
Qed.

Lemma costs_to_rcd : forall l A2 B2,
  cost_spec A2 B2 -> 
  cost_spec (rcd l A2) (rcd l B2).
Proof.
  introv H. unfold cost_spec in *.
  destruct* H. destruct* H. destruct* H0. exists* (rcd l x).
Qed.
  
Lemma not_costs_arr_inv : forall A1 A2 B1 B2,
  ~ cost_spec (arr A1 A2) (arr B1 B2) ->
  ~ cost_spec A2 B2.
Proof.
  introv H Hc. forwards~: costs_to_arr A1 B1 Hc.
Qed.

Lemma not_costs_rcd_inv : forall l A2 B2,
  ~ cost_spec (rcd l A2) (rcd l B2) ->
  ~ cost_spec A2 B2.
Proof.
  introv H Hc. forwards~: costs_to_rcd l Hc.
Qed.

Lemma costs_int_top: 
  cost_spec int top -> False.
Proof.
  introv H. unfold cost_spec in *.
  destruct* H. destruct* H. destruct* H0.
  destruct* H; inverts* H1.
Qed.

Lemma costs_int_rcd: forall l A,
  cost_spec int (rcd l A) -> False.
Proof.
  introv H. unfold cost_spec in *.
  destruct* H. destruct* H. destruct* H0.
  destruct* H; inverts* H1. inverts* H0.
Qed.

Lemma costs_int_arr: forall A B,
  cost_spec int (arr A B) -> False.
Proof.
  introv H. unfold cost_spec in *.
  destruct* H. destruct* H. destruct* H0.
  destruct* H; inverts* H1. inverts* H0.
Qed.

Lemma costs_top_top: 
  cost_spec top top -> False.
Proof.
  introv H. unfold cost_spec in *.
  destruct* H. destruct* H. destruct* H0.
  destruct* H; inverts* H1.
Qed.

Lemma costs_top_rcd: forall l A,
  cost_spec top (rcd l A) -> False.
Proof.
  introv H. unfold cost_spec in *.
  destruct* H. destruct* H. destruct* H0.
  destruct* H; inverts* H1. inverts* H0.
Qed.

Lemma costs_top_arr: forall A B,
  cost_spec top (arr A B) -> False.
Proof.
  introv H. unfold cost_spec in *.
  destruct* H. destruct* H. destruct* H0.
  destruct* H; inverts* H1. inverts* H0.
Qed.

Lemma costs_rcd_rcd_neq: forall l1 l2,
  l1 <> l2 -> forall A B,
  cost_spec (rcd l1 A) (rcd l2 B) ->
  False.
Proof.
  introv Heq H. unfold cost_spec in *.
  destruct* H. destruct* H. destruct* H0.
  destruct* H; inverts* H1. inverts* H0.
Qed.

Lemma costs_arr_rcd: forall l A B C,
  cost_spec (rcd l A) (arr B C) -> False.
Proof.
  introv H. unfold cost_spec in *.
  destruct* H. destruct* H. destruct* H0.
  destruct* H; inverts* H1. inverts* H0.
Qed.

Lemma costs_top_any: forall C,
  ~ cost_spec top C.
Proof.
  intros C. inductions C.
  - introv Hc. eapply costs_sym in Hc. eapply costs_int_top. eauto.
  - introv Hc. eapply costs_sym in Hc. eapply costs_top_top. eauto.
  - forwards~: not_costs_to_and IHC1 IHC2.
  - introv Hc. eapply costs_top_rcd. eauto.
  - introv Hc. eapply costs_top_arr. eauto.
Qed.

(* -------- disjoint -------- *)
Lemma dis_and_inv: forall A B C,
  disjoint (and B C) A -> 
  disjoint B A /\ disjoint C A.
Proof.
  introv H. unfold disjoint in *. split*.
  - introv Hc. eapply H. eapply costs_sym in Hc.
    eapply costs_sym. eapply costs_to_and_left. eauto.
  - introv Hc. eapply H. eapply costs_sym in Hc.
    eapply costs_sym. eapply costs_to_and_right. eauto.
Qed.

Lemma dis_to_inter: forall A B C,
  disjoint B A ->
  disjoint C A ->
  disjoint (and B C) A.
Proof.
  introv D1 D2. unfold disjoint in *.
  intros Hc. eapply costs_sym in Hc.
  forwards~ [C1|C2]: costs_and Hc.
  - eapply costs_sym in C1. exfalso. eapply D1. eauto.
  - eapply costs_sym in C2. exfalso. eapply D2. eauto.
Qed.

Lemma dis_sym: forall A B,
  disjoint A B -> 
  disjoint B A.
Proof.
  intros A B H.
  unfold disjoint in *. intros Hc.
  eapply costs_sym in Hc. eapply H. eauto.
Qed.

Lemma dis_and: forall A B C,
  disjoint A (and B C) <-> disjoint A B /\ disjoint A C.
Proof.
  intros. split; intros.
  - eapply dis_sym in H. 
    forwards~(D1&D2): dis_and_inv H.
    split; eapply dis_sym; eauto.
  - forwards~(D1&D2): H.
    eapply dis_sym. eapply dis_to_inter.
    eapply dis_sym; eauto.
    eapply dis_sym; eauto.
Qed.

Lemma dis_domain_type: forall A B C B',
  disjoint (arr B C) A -> 
  disjoint (arr B' C) A.
Proof.
  intros A B C B' H.
  unfold disjoint in *.
  inductions A; intros Hc.
  - eapply costs_sym in Hc. eapply costs_int_arr. eauto.
  - eapply costs_sym in Hc. eapply costs_top_arr. eauto.
  - forwards~: not_costs_and_left H.
    forwards~: IHA1 B' H0.
    forwards~: not_costs_and_right H.
    forwards~: IHA2 B' H2.
    forwards~: not_costs_to_and H1 H3.
  - eapply costs_sym in Hc. eapply costs_arr_rcd. eauto.
  - forwards~: costs_arr_inv Hc.
    forwards~: costs_to_arr B A1 H0.
Qed.

Lemma dis_dom: forall A B1 B2 C,
  disjoint A (arr B1 C) ->
  disjoint A (arr B2 C).
Proof.
  introv H. eapply dis_sym. eapply dis_sym in H.
  eapply dis_domain_type. eauto.
Qed.


Lemma disjoint_rcd_build: forall l A B,
  disjoint A B -> 
  disjoint (rcd l A) (rcd l B).
Proof.
  introv Hd.
  unfold disjoint in *.
  intros Hc. eapply Hd. 
  eapply costs_rcd_inv. eauto.
Qed.

Lemma disjoint_rcd_inv: forall l A B,
  disjoint (rcd l A) (rcd l B) ->
  disjoint A B.
Proof.
  introv Hd.
  unfold disjoint in *.
  intros Hc. forwards~: costs_to_rcd l Hc.
Qed.

Lemma dis_rcd: forall A B l,
  disjoint A B <-> disjoint (rcd l A) (rcd l B).
Proof.
  intros. split.
  - eapply disjoint_rcd_build.
  - eapply disjoint_rcd_inv.
Qed.


Lemma disjoint_arr_build: forall A B C D,
  disjoint A B -> 
  disjoint (arr C A) (arr D B).
Proof.
  introv Hd.
  unfold disjoint in *.
  intros Hc. eapply Hd. 
  eapply costs_arr_inv. eauto.
Qed.

Lemma disjoint_arr_inv: forall A B C D,
  disjoint (arr C A) (arr D B) ->
  disjoint A B.
Proof.
  introv Hd.
  unfold disjoint in *.
  intros Hc. forwards~: costs_to_arr C D Hc.
Qed.

Lemma dis_arr: forall C D A B,
  disjoint C D <-> disjoint (arr A C) (arr B D).
Proof.
  intros. split; intros.
  - eapply disjoint_arr_build. eauto.
  - eapply disjoint_arr_inv. eauto. 
Qed.


Lemma dis_super: forall A B,
  sub A B -> forall C,
  disjoint A C -> 
  disjoint B C.
Proof. 
  introv Sub. inductions Sub; introv Dis; try solve [eauto].
  - unfold disjoint. eapply costs_top_any.
  - forwards~: IHSub1 Dis. forwards~: IHSub2 Dis. 
    eapply dis_to_inter; eauto.
  - forwards~ (C1&C2): dis_and_inv Dis.
  - forwards~ (C1&C2): dis_and_inv Dis.
  - inductions C; eauto.
    + eapply dis_sym. unfold disjoint. introv Hc.
      eapply costs_int_rcd. eauto.
    + eapply dis_sym. unfold disjoint. eapply costs_top_any.
    + eapply dis_sym in Dis.
      forwards~ (?&?): dis_and_inv Dis.
      eapply dis_sym in H.
      eapply dis_sym in H0.
      forwards~: IHC1 H. forwards~: IHC2 H0.
      eapply dis_sym in H1.
      eapply dis_sym in H2.
      eapply dis_sym. 
      eapply dis_to_inter; eauto.
    + destruct* (x == n).
      * subst. forwards~: disjoint_rcd_inv Dis.
        forwards~: IHSub H. eapply disjoint_rcd_build; eauto.
      * unfold disjoint in *. intros Hc. eapply costs_rcd_rcd_neq; eauto.
    + unfold disjoint. intros Hc. eapply costs_arr_rcd. eauto.
  - inductions C0; eauto.
    + eapply dis_sym. unfold disjoint. introv Hc.
    eapply costs_int_arr. eauto.
    + eapply dis_sym. unfold disjoint. eapply costs_top_any.
    + eapply dis_sym in Dis.
      forwards~ (?&?): dis_and_inv Dis.
      eapply dis_sym in H.
      eapply dis_sym in H0.
      forwards~: IHC0_1 H. forwards~: IHC0_2 H0.
      eapply dis_sym in H1.
      eapply dis_sym in H2.
      eapply dis_sym. 
      eapply dis_to_inter; eauto.
    + eapply dis_sym. unfold disjoint. intros Hc. eapply costs_arr_rcd. eauto.
    + forwards~: disjoint_arr_inv Dis.
      forwards~: IHSub2 H. forwards~: disjoint_arr_build C C0_1 H0.
Qed.


(* -------- algo disjointness -------- *)
Inductive algo_cost : typ -> typ -> Prop :=
  | cint : algo_cost int int
  | candl : forall A B C, algo_cost A C -> algo_cost (and A B) C
  | candr : forall A B C, algo_cost B C -> algo_cost (and A B) C
  | crandl : forall A B C, algo_cost A B -> algo_cost A (and B C)
  | crandr : forall A B C, algo_cost A C -> algo_cost A (and B C)
  | carr : forall A B C D, algo_cost B D -> algo_cost (arr A B) (arr C D)
  | crcd : forall A B l, algo_cost A B -> algo_cost (rcd l A) (rcd l B).

#[export]
Hint Constructors algo_cost : core.

Lemma sound_cost : forall A B, algo_cost A B -> cost_spec A B.
Proof.
  introv Hc; unfold cost_spec in *. inductions Hc.
  - exists* int.
  - destruct* IHHc.
  - destruct* IHHc.
  - destruct* IHHc.
  - destruct* IHHc.
  - destruct* IHHc. destruct* H. destruct* H0.
    exists* (arr (and A C) x).
  - destruct* IHHc. destruct* H. destruct* H0.
    exists* (rcd l x).
Qed.

Lemma complete_cost: forall A B, cost_spec A B -> algo_cost A B.
Proof.
  intros A. inductions A; introv Hcs.
  - inductions B.
    + eauto.
    + exfalso. eapply costs_int_top. eauto.
    + forwards~ [C1|C2]: costs_and Hcs.
    + exfalso. eapply costs_int_rcd. eauto.
    + exfalso. eapply costs_int_arr. eauto.
  - inductions B.
    + exfalso. eapply costs_int_top. eapply costs_sym. eauto.
    + exfalso. eapply costs_top_top. eauto.
    + forwards~ [C1|C2]: costs_and Hcs.
    + exfalso. eapply costs_top_rcd. eauto.
    + exfalso. eapply costs_top_arr. eauto.
  - eapply costs_sym in Hcs.
    forwards~ [C1|C2]: costs_and Hcs.
    + eapply costs_sym in C1. forwards~: IHA1 C1.
    + eapply costs_sym in C2. forwards~: IHA2 C2.
  - inductions B.
    + exfalso. eapply costs_int_rcd. eapply costs_sym. eauto. 
    + exfalso. eapply costs_top_rcd. eapply costs_sym. eauto. 
    + forwards~ [C1|C2]: costs_and Hcs.
    + destruct* (n == n0). 
      * subst*. econstructor. 
        eapply IHA. eapply costs_rcd_inv; eauto.
      * exfalso. eapply costs_rcd_rcd_neq; eauto.
    + exfalso. eapply costs_arr_rcd; eauto.
  - inductions B.
    + exfalso. eapply costs_int_arr. eapply costs_sym. eauto. 
    + exfalso. eapply costs_top_arr. eapply costs_sym. eauto. 
    + forwards~ [C1|C2]: costs_and Hcs.
    + exfalso. eapply costs_arr_rcd. eapply costs_sym. eauto.
    + econstructor. eapply IHA2.
      eapply costs_arr_inv; eauto.
Qed.

Definition algo_dis A B := ~ (algo_cost A B).

Lemma algo_dis_eqv: forall A B,
  disjoint A B <-> algo_dis A B.
Proof.
  intros. split.
  - intros H. unfold disjoint in *. unfold algo_dis in *.
    introv Hc. eapply H. eapply sound_cost. eauto.
  - intros H. unfold disjoint in *. unfold algo_dis in *.
    introv Hc. eapply H. eapply complete_cost. eauto.
Qed.
  