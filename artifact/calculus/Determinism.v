Require Import Program.Equality.
Require Import LibTactics.
Require Import Metalib.Metatheory. 

Require Import Language 
               Infra
               SubDis.

(* -------- properties of typing -------- *)
Lemma check_sub : forall G e m A, 
  has_type G e m A -> forall B, 
  sub A B -> 
  has_type G e chk B.
Proof.
  induction 1; intros; eauto.
Qed.

Lemma chk_inf_sub: forall G e A,
  has_type G e chk A -> exists B,
  has_type G e inf B /\ sub B A.
Proof.
  introv Typ. inductions Typ.
  - exists*.
Qed.

Lemma val_chk_inf_sub: forall G e A,
  value e ->
  has_type G e chk A -> exists B,
  has_type G e inf B /\ sub B A.
Proof.
  introv Val Typ. inductions Typ.
  - exists*.
Qed.
(* ---------------- *)

Lemma genv_progress: forall A, 
  toplike A -> exists v,
  genv A v.
Proof.
  introv Ht. inductions Ht; eauto.
  - destruct* IHHt1. destruct* IHHt2.
  - destruct* IHHt.
  - destruct* IHHt. 
Qed.

Lemma genv_unique: forall A v1,
  genv A v1 -> forall v2,
  genv A v2 ->
  v1 = v2.
Proof.
  introv Hg1. inductions Hg1; introv Hg2; eauto.
  - inverts* Hg2.
  - inverts* Hg2. 
    forwards~: IHHg1 H2. subst*.
  - inverts* Hg2.
    forwards~: IHHg1_1 H1. forwards~: IHHg1_2 H3. subst*.
  - inverts* Hg2. forwards~: IHHg1 H2. subst*.
Qed. 

Lemma casting_top_normal : forall (v v': exp),
    casting v top v' -> v' = unit.
Proof.
  intros v v' H.
  remember top.
  induction H;
    try solve [inverts* Heqt].
Qed.

Lemma genv_casting_eq: forall A v1,
  toplike A -> forall v2,
  casting v1 A v2 -> forall v3,
  genv A v3 ->
  v2 = v3.
Proof.
  introv TL Red. inductions Red; introv Hg.
  - inverts* Hg.
  - inverts* Hg.
  - eapply IHRed; eauto.
  - eapply IHRed; eauto.
  - inverts* Hg. inverts* TL.
    forwards~: IHRed1 H2 H1. forwards~: IHRed2 H4 H3. subst*.
  - inverts* Hg. inverts* TL.
    forwards~: IHRed H0 H2. subst*.
  - inverts* TL.
  - eapply genv_unique; eauto.
Qed. 

Lemma casting_toplike: forall A, 
  toplike A -> forall (v1 v2 v1' v2' : exp), 
  casting v1 A v1' -> 
  casting v2 A v2' -> 
  v1' = v2'.
Proof.
  introv TL R1 R2.
  forwards~ (v'&Hg): genv_progress TL.
  forwards~: genv_casting_eq TL R1 Hg.
  forwards~: genv_casting_eq TL R2 Hg.
  subst*.
Qed.
  
(* principal types for values *)
Fixpoint principal_type (v:exp) : typ :=
  match v with
  | unit => top
  | lit i5 => int
  | box e1 (ann (lam bl e) (arr A B)) => arr A B
  | box e1 (ann (lam wh e) (arr (rcd l A) B)) => arr A B
  | merge v1 v2 => and (principal_type v1) (principal_type v2)
  | rec l v1 => rcd l (principal_type v1)
  | _ => top
  end.

Lemma principal_type_disjoint: forall v,
  value v -> forall G A B,
  has_type G v inf A -> 
  disjoint A B -> 
  disjoint (principal_type v) B.
Proof.
  introv Val.
  inductions Val; introv Typ Dis; try solve [inverts* Typ].
  - simpl. 
    inverts* Typ.
    + eapply dis_and_inv in Dis. destruct* Dis.
      forwards~: IHVal1 H1 H. forwards~: IHVal2 H2 H0. 
      eapply dis_to_inter; eauto.
    + eapply dis_and_inv in Dis. destruct* Dis.
      forwards~: IHVal1 H1 H. forwards~: IHVal2 H2 H0. 
      eapply dis_to_inter; eauto.
  - simpl.
    inverts* Typ. 
    inductions B.
    + unfold disjoint. intros Hc. eapply costs_int_rcd.
      eapply costs_sym. eauto.
    + unfold disjoint. intros Hc. eapply costs_top_rcd.
      eapply costs_sym. eauto.
    + apply dis_sym in Dis.
      apply dis_and_inv in Dis. destruct* Dis.
      eapply dis_sym in H.
      eapply dis_sym in H0.
      forwards~: IHB1 H H1.
      forwards~: IHB2 H0 H1.
      eapply dis_sym in H2.
      eapply dis_sym in H3.
      eapply dis_sym; eauto.
      eapply dis_to_inter; eauto.
    + destruct* (x == n). 
      {
        subst*. eapply disjoint_rcd_build.
        eapply IHVal; eauto. eapply disjoint_rcd_inv. eauto.
      }
      {
        unfold disjoint. intros Hc. eapply costs_rcd_rcd_neq. eauto. eauto.
      }
    + unfold disjoint. intros Hc. eapply costs_arr_rcd. eauto.
  - simpl. inverts* Typ. inverts* H3. 
    eapply dis_domain_type. eauto.
  - simpl. inverts* Typ. inverts* H3. 
    + eapply dis_domain_type. eauto.
    + eapply dis_domain_type. eauto.
Qed.

Lemma principal_types_disjoint: forall v1 A v2 B,
  value v1 -> forall G,
  has_type G v1 inf A -> 
  value v2 -> forall F,
  has_type F v2 inf B -> 
  disjoint A B -> 
  disjoint (principal_type v1) (principal_type v2).
Proof.
  introv Val1 Typ1 Val2 Typ2 Dis.
  forwards* D1: principal_type_disjoint Typ1 Dis.
  apply dis_sym in D1.
  forwards* D2: principal_type_disjoint Typ2 D1.
  apply~ dis_sym.
Qed.

Lemma principal_type_sub: forall v A,
  value v -> forall G,
  has_type G v inf A -> 
  sub (principal_type v) A.
Proof.
  intros v A Val G H.
  inductions H; inverts Val; simpl.
  - eauto.
  - eauto.
  - assert (S1: sub (and (principal_type e1) (principal_type e2)) A) by (econstructor; eauto).
    assert (S2: sub (and (principal_type e1) (principal_type e2)) B) by (econstructor; eauto).
    forwards*: sand S1 S2.
  - assert (S1: sub (and (principal_type v1) (principal_type v2)) A) by (econstructor; eauto).
    assert (S2: sub (and (principal_type v1) (principal_type v2)) B) by (econstructor; eauto).
    forwards*: sand S1 S2.
  - inverts H0. inverts H4. inverts H0. 
    inverts H8. eauto.
  - inverts H0. inverts H4. inverts H0.
    inverts H8. eauto.
  - eauto. 
Qed.

Definition old_dis A B :=
  forall C, sub A C -> sub B C -> toplike C.

Lemma dis_old_spec: forall A B C,
  disjoint A B ->
  sub A C ->
  sub B C ->
  toplike C.
Proof.
  intros A B C. indTypSize (size_typ A + size_typ B + size_typ C).
  lets Sub: H0.
  inverts* H0.
  - eapply dis_sym in H.
    forwards~: dis_super H1 H.
    exfalso. unfold disjoint in H0.
    eapply H0. unfold cost_spec. exists*.
  - forwards~ (C1&C2): and_inversion H1.
    forwards~: IH H H2 C1. elia.
    forwards~: IH H H3 C2. elia.
  - forwards~: IH H2 H1. elia.
    forwards~ (?&?): dis_and_inv H.
  - forwards~: IH H2 H1. elia.
    forwards~ (?&?): dis_and_inv H.
  - inductions B.
    + inverts* H1.
    + inverts* H1.
    + eapply dis_sym in H.
      forwards~ (?&?): dis_and_inv H.
      eapply dis_sym in H0.
      eapply dis_sym in H3.
      inverts H1.

      forwards~: IH H0 Sub H7. elia.
      forwards~: IH H3 Sub H7. elia.
    + inverts* H1.
      forwards~: disjoint_rcd_inv H.
      forwards~: IH H0 H2 H3. elia.
    + inverts* H1.
  - inductions B.
    + inverts* H1.
    + inverts* H1.
    + eapply dis_sym in H.
      forwards~ (?&?): dis_and_inv H.
      eapply dis_sym in H0.
      eapply dis_sym in H4.
      inverts H1.

      forwards~: IH H0 Sub H8. elia.
      forwards~: IH H4 Sub H8. elia.
    + inverts* H1.
    + inverts* H1.
      forwards~: disjoint_arr_inv H.
      forwards~: IH H0 H3 H8. elia.
Qed.

Lemma old_dis_complete: forall A B,
  disjoint A B ->
  old_dis A B.
Proof.
  introv Dis. unfold old_dis. introv S1 S2.
  eapply dis_old_spec; eauto.
Qed.

Lemma gord_not_tl: forall A,
  gord A -> ~ toplike A.
Proof.
  introv H Ht. inductions H; try solve [inverts* Ht].
Qed.

Lemma old_dis_sound: forall A B,
  old_dis A B ->
  disjoint A B.
Proof.
  introv Ho. unfold old_dis in *. unfold disjoint. introv Hc.
  unfold cost_spec in *.
  destruct* Hc. destruct* H. destruct* H0.
  forwards~: Ho H0 H1.
  eapply gord_not_tl; eauto.
Qed.

Lemma sub_casting: forall v v' A,
  value v -> 
  casting v A v' ->
  sub (principal_type v) A.
Proof.
  introv Val Red.
  inductions Red.
  - simpl. eauto.
  - simpl. eauto.
  - simpl. inverts* Val. 
  - simpl. inverts* Val.
  - simpl. eauto.
  - simpl. inverts* Val.
  - inverts H1. 
    + simpl. eauto.
    + simpl. eauto.
  - inverts H1. 
    + simpl. eauto.
    + simpl. eauto.
Qed.

Lemma disjoint_val_consistent: forall A B v1 v2 G F,
  disjoint A B -> 
  value v1 -> 
  value v2 -> 
  has_type G v1 inf A -> 
  has_type F v2 inf B -> 
  consistencySpec v1 v2.
Proof.
  intros A B v1 v2 G F Dis Val1 Val2 Typ1 Typ2.
  unfold consistencySpec.
  introv Red1 Red2.
  forwards* Sub1': sub_casting Red1.
  forwards* Sub2': sub_casting Red2.
  forwards* Dis': principal_types_disjoint Typ1 Typ2.
  assert (Top: toplike A0). {
    eapply dis_old_spec; eauto.
  }
  forwards*: casting_toplike Top Red1 Red2.
Qed.

Lemma value_closed : forall G e m A, 
  has_type G e m A -> 
  value e -> forall F, 
  has_type F e m A.
Proof.
  induction 1; intros Val K; eauto; try solve [inverts* Val].
  - (* merge *) 
    inverts* Val. eapply tcon; try eassumption.
    eapply IHhas_type1; eassumption.
    eapply IHhas_type2; eassumption.
    eapply disjoint_val_consistent.
    eapply H1. eauto. eauto. eauto. eauto.
Qed.

Lemma casting_unique_aux: forall (v v1 v2 : exp) (A: typ),
  value v -> 
  (exists G B, has_type G v inf B) -> 
  casting v A v1 -> 
  casting v A v2 -> 
  v1 = v2.
Proof.
  intros v v1 v2 A Val H R1 R2.
  gen v2.
  lets R1': R1.
  induction R1; introv R2.
  - forwards~: casting_toplike R1' R2.
  - inverts* R2.  
  - (* mergel *)
    lets [B H']: H.
    lets R2': R2.
    inverts Val.
    inverts* R2.
    + forwards~: casting_toplike R1' R2'.
    + inverts* H'. inverts* H1.
    + inverts* H'. inverts* H1.
      forwards~ Cons: disjoint_val_consistent H11 H3 H4 H7 H9. 
      unfold consistencySpec in Cons.
      eapply Cons; try eassumption. 
    + inverts* H0.
  - (* merger *)
    lets [B H']: H.
    lets R2': R2.
    inverts Val.
    inverts* R2.
    + forwards~: casting_toplike R1' R2'.
    + inverts* H'. inverts* H1. 
      * forwards~: disjoint_val_consistent H11 H3 H4 H7 H9. 
      unfold consistencySpec in H1.
        forwards~: H1 H5 R1. 
      * unfold consistencySpec in H13.
        forwards~: H13 H5 R1.    
    + inverts* H'. inverts* H1.
    + inverts* H0.
  - (* and *)
    inverts~ R2. 
    + inverts* H1.
    + inverts* H1.
    + forwards*: IHR1_1.
      forwards*: IHR1_2.
      congruence.
  - (* rcd *)
    inverts* R2.
    + inverts* Val. destruct* H. destruct* H. inverts* H. forwards*: IHR1. subst*.
  - inverts* R2.
  - inverts H2.
    + forwards~: genv_casting_eq R2 H5.
    + forwards~: genv_casting_eq R2 H5.
Qed.

Lemma casting_unique: forall (v v1 v2 : exp) (G A B: typ),
  value v -> 
  has_type G v inf B -> 
  casting v A v1 -> 
  casting v A v2 -> 
  v1 = v2.
Proof.
  introv Val H R1 R2.
  eapply casting_unique_aux; eauto.
Qed.

Lemma gen_step_unique: forall e m A G, 
  has_type G e m A -> forall v e1 e2, 
  has_type top v inf G -> 
  step v e e1 ->
  step v e e2 -> 
  e1 = e2.
Proof.
  intros e m A G H.
  induction H; introv Typv Red1 Red2.
  - inverts* Red1.
  - inverts* Red1.
  - inverts* Red1. inverts* Red2. 
  - inverts Red1; inverts Red2.
    + assert (e' = e'0). {
      eapply IHhas_type2; try eapply H7; try eapply H6.
      econstructor; try eassumption; try eauto.
      eapply value_closed; try eassumption.
      unfold disjoint. eapply costs_top_any.
    }
    subst*.
    + exfalso. forwards~: step_not_value H9. 
    + exfalso. forwards~: step_not_value H7. 
    + forwards~: IHhas_type1 Typv H7 H8. subst*.
  - exfalso. forwards~: step_not_value Red1.  
  - inverts Red1; inverts Red2; try solve [inverts H; inverts H0]; try solve [inverts H6]; try solve [inverts H8].
    + forwards~(B&TypI&?): val_chk_inf_sub H.
      forwards~: casting_unique TypI H4 H7. 
    + exfalso. forwards~: step_not_value H7.
    + exfalso. forwards~: step_not_value H4.
    + forwards~: IHhas_type Typv H5 H4. subst*.
  - inverts Red1; inverts Red2.
    + inverts* H12.
    + inverts* H9.
    + inverts* H9.
    + inverts* H10.
    + inverts* H7.
    + inverts* H7.
    + inverts* H10.
    + inverts* H7.
    + eauto.
  - inverts Red1; inverts Red2.
    + inverts H3. 
      * inverts H. inverts H9. inverts H11. inverts H.
        inverts H14. inverts H10. inverts H20.
        forwards~(D&TypI&?): val_chk_inf_sub H0.
        forwards~: casting_unique TypI H4 H16.  
        subst*.
      * inverts H. inverts H9. inverts H11. inverts H.
        inverts H14. inverts H10. inverts H20.
        forwards~(D&TypI&?): val_chk_inf_sub H0.
        forwards~: casting_unique TypI H4 H16. 
        subst*.
    + inverts H3; exfalso; forwards~: step_not_value H11.
    + exfalso. forwards~: step_not_value H9.
    + inverts H3; exfalso; forwards~: step_not_value H5.
    + forwards~: IHhas_type1 Typv H5 H6. subst*.
    + exfalso. forwards~: step_not_value H5.
    + exfalso. forwards~: step_not_value H4.
    + exfalso. forwards~: step_not_value H7.
    + forwards~: IHhas_type2 Typv H4 H5. subst*.
  - inverts Red1; inverts Red2.
    + eauto.
    + exfalso. forwards~: step_not_value H4.
    + exfalso. forwards~: step_not_value H6.
    + exfalso. forwards~: step_not_value H3.
    + forwards~: step_env H3.
      forwards~: value_closed H top.
      forwards~: IHhas_type2 H3 H4. subst*.
    + forwards~: step_env H3.
      exfalso. forwards~: step_not_value H6.
    + exfalso. forwards~: step_not_value H4.
    + forwards~: step_env H3.
      exfalso. forwards~: step_not_value H4.
    + forwards~: IHhas_type1 H4 H5. subst*.
  - inverts* Red1; inverts* Red2.
  - inverts Red1; inverts Red2.
    forwards~: IHhas_type Typv H4 H5. subst*.
  - inverts Red1; inverts Red2.
    + eauto.
    + exfalso. forwards~: step_not_value H6.
    + exfalso. forwards~: step_not_value H4.
    + forwards~: IHhas_type Typv H4 H5. subst*.
Qed.               


Theorem step_unique: forall e m A, 
  has_type top e m A -> forall e1 e2,
  step unit e e1 ->
  step unit e e2 -> 
  e1 = e2.
Proof.
  introv Typ H1 H2.
  forwards~: gen_step_unique Typ H1 H2.
Qed.