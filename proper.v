Require Import utils.
Require Import nnf.
Require Import closure.
Require Import semantics.
Require Import seqt.
Require Import ptree.

Require Import Arith.
Require Import List.
Require Import ListSet.
Require Import SetoidList.
Import ListNotations.
Require Import Relations.
Require Import Lia.

Set Implicit Arguments.


Definition proper_prinform (x : ptree) : Prop :=
match x with
| talpha _ _ phi => nnf_isalpha phi
| tbeta1 _ _ phi => nnf_isbeta phi
| tbeta2 _ _ phi => nnf_isbeta phi
| talt _ _ _ phi => nnf_isbeta phi
| tjump _ _     => True
| tloop _      => True
end.


Definition proper_downward (x : ptree) : Prop :=
match x with
| talpha c _ phi   => t_dose c = alpha_child phi (t_dose x)
| tbeta1 c _ phi   => t_dose c = beta1_child phi (t_dose x)
| tbeta2 c _ phi   => t_dose c = beta2_child phi (t_dose x)
| talt c1 c2 _ phi => t_dose c1 = beta1_child phi (t_dose x) /\
                    t_dose c2 = beta2_child phi (t_dose x)
|tjump cs fs =>  map t_dose cs = jump_child (t_dose x)
| tloop _        => True
end.



Definition proper_upward (x : ptree) : Prop :=
match x with
| talpha c _ phi   => t_uev x = t_uev c /\ t_mrk x = t_mrk c
| tbeta1 c _ phi   => t_uev x = remove_nnf phi (t_uev c) /\ t_lp x = t_lp c
| tbeta2 c _ phi   => t_uev x = t_uev c /\ t_lp x = t_lp c
| talt c1 c2 _ phi => t_uev x = inter_nnf (remove_nnf phi (t_uev c1)) (t_uev c2) /\
                     t_lp x = min (t_lp c1) (t_lp c2)
| tjump c _      => t_uev x = t_uev c /\ t_lp x = t_lp c
| tloop _        => t_uev x = get_unts (unnext (t_G x)) /\
                     exists h, blocker_seqt h (t_dose x) /\ t_lp x = fst h
end.


Record proper (x : ptree) : Prop :=
{ pfdownseqt   : regular (t_dose x);
  has_prinform : forall phi, t_prinform x = Some phi -> In phi (t_G x);
  prinform_ok  : proper_prinform x;
  downward_ok  : proper_downward x;
  upward_ok    : proper_upward x;
  state_has_sc : t_isstate x -> state_conditions (t_dose x);
  tbeta1_empty_or_unsat : forall c fs phi, x = tbeta1 c fs phi ->
    t_uev x = [] \/ unsatable (s_G (beta2_child phi (t_dose x)));
  tbeta2_unsat : forall c fs phi, x = tbeta2 c fs phi ->
    unsatable (s_G (beta1_child phi (t_dose x)));
  no_unful_case : forall z, z </ x -> t_c z = true ->
    t_uev z = [] \/ t_lp z < t_d z; }.

Definition dproper (x : ptree) := forall y, y </ x -> proper y.

Definition gproper (x : ptree) := proper x /\ dproper x.

Lemma child_proper : forall x, dproper x ->
  forall [y], is_child y x -> proper y.
Proof.
intros x gpx y ych. apply gpx. left. assumption.
Qed.

Lemma child_dproper : forall x, dproper x ->
  forall y, is_child y x -> dproper y.
Proof.
intros x gpx y ych. intros z zlty. apply gpx.
right with y; try assumption. left. assumption.
Qed.

Lemma child_gproper : forall x, gproper x -> forall y, is_child y x -> gproper y.
Proof.
intros x [px gpx] y ych.
split; [apply (child_proper gpx) | apply (child_dproper gpx)]; assumption.
Qed.

Lemma desceq_proper : forall x, gproper x ->
  forall z, z <=/ x -> proper z.
Proof.
intros x [px gpx] z zlex. destruct zlex as [zltx|zeqx].
- apply (gpx _ zltx).
- rewrite zeqx. assumption.
Qed.

Lemma desc_dproper : forall x, dproper x ->
  forall z, z </ x -> dproper z.
Proof.
intros x gpx z zltx. intros w wltz.
apply gpx. right with z; assumption.
Qed.

Lemma desceq_dproper : forall x, dproper x ->
  forall z, z <=/ x -> dproper z.
Proof.
intros x gpx z zlex. destruct zlex as [zltx|zeqx].
- apply (desc_dproper gpx). assumption.
- rewrite zeqx. assumption.
Qed.


Ltac tree_ind_with_eqns x :=
match goal with
| [ px : proper x |- _ ] => let phi := fresh "phi" in
    induction x as [c IHc fs phi|c IHc fs phi|c IHc fs phi
                   |c1 IHc1 c2 IHc2 fs phi|c IHc fs|fs];
    pose proof (prinform_ok px) as Hprin;
    pose proof (downward_ok px) as Heqsec;
    pose proof (upward_ok px) as [Hequev Heqlp];    
    [idtac|idtac|idtac|destruct Heqsec as [Heqsec1 Heqsec2]|idtac|
    destruct Heqlp as [h [ [Hhin Heqset] Heqlp] ]]
end; try (discriminate || contradiction || tauto).

Ltac tree_dest_with_eqns x :=
match goal with
| [ px : proper x |- _ ] => let phi := fresh "phi" in let Heqx := fresh "Heq" x in 
    destruct x as [c fs phi|c fs phi|c fs phi|c1 c2 fs phi|c fs|fs] eqn:Heqx;
    pose proof (prinform_ok px) as Hprin;
    pose proof (downward_ok px) as Heqsec;
    pose proof (upward_ok px) as [Hequev Heqlp];    
    [idtac|idtac|idtac|destruct Heqsec as [Heqsec1 Heqsec2]|idtac|
    destruct Heqlp as [h [ [Hhin Heqset] Heqlp] ]]
end; try (discriminate || contradiction || tauto).


Lemma lp_le_depth : forall x : ptree, gproper x ->
  t_uev x <> [] -> t_lp x <= t_d x.
Proof.
intros x [px gpx]. tree_ind_with_eqns x;
  try (pose proof (child_proper gpx eq_refl) as pc;
  pose proof (child_dproper gpx eq_refl) as gpc).
- rewrite Hequev, Heqlp. unfold t_d in IHc.
  rewrite Heqsec in IHc. simpl in IHc.
  apply IHc; try assumption.
- rewrite Hequev, Heqlp. unfold t_d in IHc.
  rewrite Heqsec in IHc. simpl in IHc. (*fold (t_d x) in IHc.*)
  intro H. apply IHc; try assumption.
  intro Hctr. rewrite Hctr in H. contradiction.
- rewrite Hequev, Heqlp. unfold t_d in IHc.
  rewrite Heqsec in IHc. simpl in IHc.
  apply IHc; try assumption.
- pose proof (child_proper gpx (or_introl eq_refl)) as pc1.
  pose proof (child_dproper gpx (or_introl eq_refl)) as gpc1.
  rewrite Hequev, Heqlp. unfold t_d in IHc1.
  rewrite Heqsec1 in IHc1. simpl in IHc1.
  intro H. apply Nat.le_trans with (t_lp c1); try apply Nat.le_min_l.
  apply IHc1; try assumption.
  intro Hctr. rewrite Hctr in H. simpl in H. contradiction.
- rewrite Hequev, Heqlp.
  intro H. destruct (no_unful_case px) with c as [H0|H0].
  + now left.
  + unfold t_c. rewrite Heqsec. simpl. reflexivity.
  + contradiction.
  + unfold t_d in H0. rewrite Heqsec in H0. simpl in H0.
    apply Arith_prebase.lt_n_Sm_le. assumption.
- rewrite Heqlp. unfold t_d. intro. apply earlier_H; try assumption.
  apply (pfdownseqt px).
Qed.

Lemma uev_incl_child : forall x, proper x ->
  forall y, is_child y x -> incl (t_uev x) (t_uev y).
Proof.
intros x px y ych. tree_dest_with_eqns x;
try contradiction.
- rewrite Hequev, ych. apply incl_refl.
- rewrite Hequev, ych.
  intros xi Hxi. apply (in_remove nnf_eqdec _ _ _ Hxi).
- rewrite Hequev, ych. apply incl_refl.
- rewrite Hequev. destruct ych as [ych|ych].
  + rewrite ych. intros xi Hxi.
    apply (in_remove nnf_eqdec _ _ phi).
    apply (set_inter_elim1 _ _ _ _ Hxi).
  + rewrite ych. intros xi Hxi.
    apply (set_inter_elim2 _ _ _ _ Hxi).
- rewrite Hequev, ych. intros xi Hxi. assumption.
Qed.

Lemma uev_monotone : forall x, gproper x ->
  forall z, desc z x -> incl (t_uev x) (t_uev z).
Proof.
intros x [px gpx] z zltx. apply clos_trans_tn1 in zltx.
induction zltx.
- apply uev_incl_child; assumption.
- apply incl_tran with (t_uev y).
  + apply uev_incl_child; assumption.
  + apply IHzltx.
    * apply (child_proper gpx). assumption.
    * apply (child_dproper gpx). assumption.
Qed.

Corollary uev_not_nil_desc : forall x, gproper x ->
  forall z, desc z x -> t_uev x <> [] -> t_uev z <> [].
Proof.
intros x gpx z zltx. apply incl_not_nil. apply uev_monotone; assumption.
Qed.

Lemma lp_le_child : forall x, proper x ->
  forall y, is_child y x -> t_lp x <= t_lp y.
Proof.
intros x px y ych; tree_dest_with_eqns x;
try contradiction; try (rewrite Heqlp, ych; apply Nat.le_refl).
rewrite Heqlp. destruct ych as [ych|ych].
- rewrite ych. apply Nat.le_min_l.
- rewrite ych. apply Nat.le_min_r.
Qed.

Lemma lp_monotone : forall x, gproper x ->
  forall z, desc z x -> t_lp x <= t_lp z.
Proof.
intros x [px gpx] z zltx. apply clos_trans_tn1 in zltx.
induction zltx.
- apply lp_le_child; assumption.
- apply Nat.le_trans with (t_lp y).
  + apply lp_le_child; assumption.
  + apply IHzltx.
    * apply (child_proper gpx). assumption.
    * apply (child_dproper gpx). assumption.
Qed.

Lemma H_incl_child : forall x, proper x ->
  forall y, is_child y x -> incl (t_H x) (t_H y).
Proof.
intros x px y ych. tree_dest_with_eqns x; try contradiction;
  try (rewrite ych; unfold t_H at 2; rewrite Heqsec;
  simpl; rewrite <- Heqx; fold (t_H x); (apply incl_refl || apply incl_tl, incl_refl)).
destruct ych as [ych|ych].
- rewrite ych. unfold t_H at 2. rewrite Heqsec1.
  simpl. rewrite <- Heqx. fold (t_H x). apply incl_refl.
- rewrite ych. unfold t_H at 2. rewrite Heqsec2.
  simpl. rewrite <- Heqx. fold (t_H x). apply incl_refl.
Qed.

Lemma H_equal_child : forall x, proper x -> ~ t_isstate x ->
  forall y, is_child y x -> t_H x = t_H y.
Proof.
intros x px stx y ych; tree_dest_with_eqns x;
  try (contradict stx; simpl; tauto); clear stx;
  try (rewrite ych; unfold t_H at 2; rewrite Heqsec; simpl;
  rewrite <- Heqx; fold (t_H x); reflexivity).
destruct ych as [ych|ych].
- rewrite ych. unfold t_H at 2. rewrite Heqsec1. simpl.
  rewrite <- Heqx. fold (t_H x). reflexivity.
- rewrite ych. unfold t_H at 2. rewrite Heqsec2. simpl.
  rewrite <- Heqx. fold (t_H x). reflexivity.
Qed.

Lemma depth_le_child : forall x, proper x ->
  forall y, is_child y x -> t_d x <= t_d y.
Proof.
intros x px y ych; tree_dest_with_eqns x; try contradiction;
try (rewrite ych; unfold t_d at 2; rewrite Heqsec; simpl;
     rewrite <- Heqx; fold (t_d x); apply Nat.le_refl).
- destruct ych as [ych|ych].
  + rewrite ych. unfold t_d at 2. rewrite Heqsec1. simpl.
    rewrite <- Heqx. fold (t_d x). apply Nat.le_refl.
  + rewrite ych. unfold t_d at 2. rewrite Heqsec2. simpl.
    rewrite <- Heqx. fold (t_d x). apply Nat.le_refl.
- rewrite ych. unfold t_d at 2. rewrite Heqsec. simpl.
  rewrite <- Heqx. fold (t_d x). apply Nat.le_succ_diag_r.
Qed.

Lemma common_H_child : forall x, proper x -> forall y, is_child y x ->
  forall h, In h (t_H y) -> fst h <= t_d x -> In h (t_H x).
Proof.
intros x px y ych h Hhiny Hhle.
destruct (t_isstate_dec x) as [stx|nstx].
- destruct x as [| | | |c fs|] eqn:Heqx; try contradiction.
  pose proof (downward_ok px) as Heqsec.
  rewrite ych in Hhiny. unfold t_H in Hhiny.
  rewrite Heqsec in Hhiny. simpl in Hhiny.
  destruct Hhiny as [Heqh|Hhinx].
  * rewrite <- Heqh in Hhle. simpl in Hhle.
    fold (t_d (tjump c fs)) in Hhle. lia.
  * assumption.
- rewrite (H_equal_child px nstx y ych). assumption.
Qed.

Theorem desc_common_H : forall x, gproper x ->
  forall z, desc z x -> forall h, In h (t_H z) ->
  fst h <= t_d x -> In h (t_H x).
Proof.
intros x [px gpx] z zltx. apply clos_trans_tn1 in zltx.
induction zltx.
- apply common_H_child; assumption.
- rename z0 into x. intros h Hhinz Hhle.
  assert (In h (t_H y)) as Hhiny.
  { apply IHzltx.
  - apply (child_proper gpx). assumption.
  - apply (child_dproper gpx). assumption.
  - assumption.
  - apply Nat.le_trans with (t_d x); try assumption.
    apply depth_le_child; assumption. }
  apply common_H_child with y; assumption.
Qed.

Theorem unt_only_uev : forall x, gproper x ->
  forall xi, In xi (t_uev x) -> exists phi psi, xi = unt phi psi.
Proof.
intros x [px gpx] xi Hxi.
induction x as [c IHc fs phi|c IHc fs phi|c IHc fs phi
|c1 IHc1 c2 IHc2 fs phi|c IHc fs|fs].
- apply IHc.
  + apply (child_proper gpx eq_refl).
  + apply (child_dproper gpx eq_refl).
  + apply (uev_incl_child px c eq_refl). assumption.
- apply IHc.
  + apply (child_proper gpx eq_refl).
  + apply (child_dproper gpx eq_refl).
  + apply (uev_incl_child px c eq_refl). assumption.
- apply IHc.
  + apply (child_proper gpx eq_refl).
  + apply (child_dproper gpx eq_refl).
  + apply (uev_incl_child px c eq_refl). assumption.
- apply IHc1.
  + apply (child_proper gpx (or_introl eq_refl)).
  + apply (child_dproper gpx (or_introl eq_refl)).
  + apply (uev_incl_child px c1 (or_introl eq_refl)). assumption.
- apply IHc.
  + apply (child_proper gpx eq_refl).
  + apply (child_dproper gpx eq_refl).
  + apply (uev_incl_child px c eq_refl). assumption.
- destruct (upward_ok px) as [Hequev _].
  rewrite Hequev in Hxi. apply (unt_only_get_unts _ Hxi).
Qed.

Lemma beta2_only_uev : forall x, gproper x ->
  forall z phi, In phi (t_uev x) -> z <=/ x ->
  t_isbeta z -> t_prinform z = Some phi -> t_isbeta2 z.
Proof.
intros x [px gpx] z psi Hpsi zlex bz pfz.
induction x as [c IHc fs phi|c IHc fs phi|c IHc fs phi
|c1 IHc1 c2 IHc2 fs phi|c IHc fs|fs].
- destruct zlex as [zltx|zeqx];
  try (contradict bz; rewrite zeqx; tauto).
  apply IHc.
  + apply (child_proper gpx eq_refl).
  + apply (child_dproper gpx eq_refl).
  + apply (uev_incl_child px _ eq_refl). assumption.
  + destruct (desc_desceq_child zltx) as [y [ychx zley]].
    rewrite ychx in zley. assumption.
- destruct zlex as [zltx|zeqx].
  + apply IHc.
    * apply (child_proper gpx eq_refl).
    * apply (child_dproper gpx eq_refl).
    * apply (uev_incl_child px _ eq_refl). assumption.
    * destruct (desc_desceq_child zltx) as [y [ychx zley]].
      rewrite ychx in zley. assumption.
  + rewrite zeqx in pfz. simpl in pfz. injection pfz.
    intro Heqphi. rewrite <- Heqphi in Hpsi.
    rewrite (proj1 (upward_ok px)) in Hpsi.
    apply in_remove in Hpsi. destruct Hpsi as [_ Hctr]. contradiction.
- destruct zlex as [zltx|zeqx].
  + apply IHc.
    * apply (child_proper gpx eq_refl).
    * apply (child_dproper gpx eq_refl).
    * apply (uev_incl_child px _ eq_refl). assumption.
    * destruct (desc_desceq_child zltx) as [y [ychx zley]].
      rewrite ychx in zley. assumption.
  + rewrite zeqx. simpl. tauto.
- destruct zlex as [zltx|zeqx].
  + destruct (desc_desceq_child zltx) as [y [ychx zley]].
    destruct ychx as [ychx|ychx].
    * rewrite ychx in zley. apply IHc1.
     -- apply (child_proper gpx (or_introl eq_refl)).
     -- apply (child_dproper gpx (or_introl eq_refl)).
     -- apply (uev_incl_child px _ (or_introl eq_refl)). assumption.
     -- assumption.
    * rewrite ychx in zley. apply IHc2.
     -- apply (child_proper gpx (or_intror eq_refl)).
     -- apply (child_dproper gpx (or_intror eq_refl)).
     -- apply (uev_incl_child px _ (or_intror eq_refl)). assumption.
     -- assumption.
  + rewrite zeqx in pfz. simpl in pfz. injection pfz.
    intro Heqphi. rewrite <- Heqphi in Hpsi.
    rewrite (proj1 (upward_ok px)) in Hpsi.
    apply set_inter_elim1 in Hpsi.
    apply in_remove in Hpsi. destruct Hpsi as [_ Hctr]. contradiction.
- destruct zlex as [zltx|zeqx].
  + destruct (desc_desceq_child zltx) as [y [ychx zley]].
    rewrite ychx in zley. apply IHc.
    * apply (child_proper gpx eq_refl).
    * apply (child_dproper gpx eq_refl).
    * apply (uev_incl_child px _ eq_refl). assumption.
    * assumption.
  + rewrite zeqx in pfz. simpl in pfz. discriminate.
- destruct zlex as [zltx|zeqx];
  try (contradict zltx; apply tloop_no_desc; simpl; tauto).
  rewrite zeqx in pfz. simpl in pfz. discriminate.
Qed.

Theorem alpha_preserved_child : forall x y phi, gproper x ->
  is_child y x -> nnf_isalpha phi -> In phi (t_G x) ->
  (~ t_isalpha x \/ t_prinform x <> Some phi) -> In phi (t_G y).
Proof.
intros x y phi [px gpx] ychx aphi Hin Hx.
tree_dest_with_eqns x.
- destruct Hx as [Hx|Hx]; try (simpl in Hx; contradiction).
  rewrite ychx. unfold t_G. rewrite Heqsec. right. right.
  apply in_in_remove; try assumption.
  intro Hctr. rewrite Hctr in Hx. contradiction.
- rewrite ychx. unfold t_G. rewrite Heqsec. right.
  apply in_in_remove; try assumption.
  intro Hctr. contradict aphi. apply beta_not_alpha.
  rewrite Hctr. assumption.
- rewrite ychx. unfold t_G. rewrite Heqsec. right.
  apply in_in_remove; try assumption.
  intro Hctr. contradict aphi. apply beta_not_alpha.
  rewrite Hctr. assumption.
- destruct ychx as [ychx|ychx].
  + rewrite ychx. unfold t_G. rewrite Heqsec1. right.
    apply in_in_remove; try assumption.
    intro Hctr. contradict aphi. apply beta_not_alpha.
    rewrite Hctr. assumption.
  + rewrite ychx. unfold t_G. rewrite Heqsec2. right.
    apply in_in_remove; try assumption.
    intro Hctr. contradict aphi. apply beta_not_alpha.
    rewrite Hctr. assumption.
- contradict aphi.
  apply (sc_no_alpha (state_has_sc px I) _ Hin).
Qed.

Theorem beta_preserved_child : forall x y phi, gproper x ->
  is_child y x -> nnf_isbeta phi -> In phi (t_G x) ->
  (~ t_isbeta x \/ t_prinform x <> Some phi) -> In phi (t_G y).
Proof.
intros x y phi [px gpx] ychx bphi Hin Hx.
tree_dest_with_eqns x.
- rewrite ychx. unfold t_G. rewrite Heqsec. right. right.
  apply in_in_remove; try assumption.
  intro Hctr. rewrite Hctr in bphi. apply beta_not_alpha in bphi.
  contradiction.
- destruct Hx as [Hx|Hx]; try (simpl in Hx; contradiction).
  rewrite ychx. unfold t_G. rewrite Heqsec. right.
  apply in_in_remove; try assumption.
  intro Hctr. rewrite Hctr in Hx. contradiction.
- destruct Hx as [Hx|Hx]; try (simpl in Hx; contradiction).
  rewrite ychx. unfold t_G. rewrite Heqsec. right.
  apply in_in_remove; try assumption.
  intro Hctr. rewrite Hctr in Hx. contradiction.
- destruct Hx as [Hx|Hx]; try (simpl in Hx; contradiction).
  destruct ychx as [ychx|ychx].
  + rewrite ychx. unfold t_G. rewrite Heqsec1. right.
    apply in_in_remove; try assumption.
    intro Hctr. rewrite Hctr in Hx. contradiction.
  + rewrite ychx. unfold t_G. rewrite Heqsec2. right.
    apply in_in_remove; try assumption.
    intro Hctr. rewrite Hctr in Hx. contradiction.
- contradict bphi.
  apply (sc_no_beta (state_has_sc px I) _ Hin).
Qed.

Lemma next_preserved : forall x, gproper x ->
  forall z p phi, In (next phi) (t_G x) -> path p x z ->
  (forall y, In y p -> ~ t_isstate y) -> In (next phi) (t_G z).
Proof.
intros x [px gpx] z p psi Hpsi piep ally.
induction piep; try assumption.
apply IHpiep.
- apply (child_proper gpx). assumption.
- apply (child_dproper gpx). assumption.
- tree_dest_with_eqns x.
  + rewrite H.
    unfold t_G. rewrite Heqsec. simpl. right. right.
    apply in_in_remove; try assumption.
    intro Hctr. pose proof Hprin as axpsi.
    contradict axpsi. rewrite <- Hctr. tauto.
  + rewrite H.
    unfold t_G. rewrite Heqsec. simpl. right.
    apply in_in_remove; try assumption.
    intro Hctr. pose proof Hprin as bxpsi.
    contradict bxpsi. rewrite <- Hctr. tauto.
  + rewrite H.
    unfold t_G. rewrite Heqsec. simpl. right.
    apply in_in_remove; try assumption.
    intro Hctr. pose proof Hprin as bxpsi.
    contradict bxpsi. rewrite <- Hctr. tauto.
  + destruct H as [H|H].
    * rewrite H. unfold t_G. rewrite Heqsec1. simpl. right.
      apply in_in_remove; try assumption.
      intro Hctr. pose proof Hprin as bxpsi.
      contradict bxpsi. rewrite <- Hctr. tauto.
    * rewrite H. unfold t_G. rewrite Heqsec2. simpl. right.
      apply in_in_remove; try assumption.
      intro Hctr. pose proof Hprin as bxpsi.
      contradict bxpsi. rewrite <- Hctr. tauto.
  + pose proof (ally _ (or_introl eq_refl)) as nstx.
    contradict nstx. exact I.
- intros w Hwin. apply ally. now right.
Qed.


Lemma alpha_before_state : forall x z p phi, gproper x ->
  nnf_isalpha phi -> In phi (t_G x) -> path p x z -> t_isstate z ->
  exists y, In y p /\ t_isalpha y /\ t_prinform y = Some phi.
Proof.
intros x z p phi [px gpx] aphi Hin piep stz.
induction piep.
- contradict aphi. apply (sc_no_alpha (state_has_sc px stz) _ Hin).
- assert ((t_isalpha x /\ t_prinform x = Some phi) \/
  (~ t_isalpha x \/ t_prinform x <> Some phi)) as H0.
  { destruct (t_isalpha_dec x) as [ax|nax].
  - destruct (option_eqdec nnf_eqdec (t_prinform x) (Some phi))
    as [Heq|Hneq].
    + left. split; assumption.
    + right. right. assumption.
  - right. left. assumption. }
  destruct H0 as [H0|H0].
  + exists x. split; try now left. assumption.
  + destruct IHpiep as [y0 Hy0].
    * apply (child_proper gpx H).
    * apply (child_dproper gpx H).
    * apply alpha_preserved_child with x; unfold gproper; tauto.
    * assumption.
    * exists y0. split; try now right. tauto.
Qed.


Lemma beta_before_state : forall x z p phi, gproper x ->
  nnf_isbeta phi -> In phi (t_G x) -> path p x z -> t_isstate z ->
  exists y, In y p /\ t_isbeta y /\ t_prinform y = Some phi.
Proof.
intros x z p phi [px gpx] bphi Hin piep stz.
induction piep.
- contradict bphi. apply (sc_no_beta (state_has_sc px stz) _ Hin).
- assert ((t_isbeta x /\ t_prinform x = Some phi) \/
  (~ t_isbeta x \/ t_prinform x <> Some phi)) as H0.
  { destruct (t_isbeta_dec x) as [bx|nbx].
  - destruct (option_eqdec nnf_eqdec (t_prinform x) (Some phi))
    as [Heq|Hneq].
    + left. split; assumption.
    + right. right. assumption.
  - right. left. assumption. }
  destruct H0 as [H0|H0].
  + exists x. split; try now left. assumption.
  + destruct IHpiep as [y0 Hy0].
    * apply (child_proper gpx H).
    * apply (child_dproper gpx H).
    * apply beta_preserved_child with x; unfold gproper; tauto.
    * assumption.
    * exists y0. split; try now right. tauto.
Qed.

Lemma path_no_state_same_d : forall p x z, gproper x ->
  path p x z -> (forall y, In y p -> ~ t_isstate y) -> t_d z = t_d x.
Proof.
intros p x z [px gpx] pap nostt. induction pap; try reflexivity.
eapply eq_trans.
- apply IHpap;
  try (apply (child_proper gpx H) || apply (child_dproper gpx H)).
  intros w Hw. apply nostt. now right.
- tree_dest_with_eqns x; try (unfold t_d at 1; rewrite H, Heqsec; reflexivity).
  + destruct H as [H|H].
    * unfold t_d at 1. rewrite H, Heqsec1. reflexivity.
    * unfold t_d at 1. rewrite H, Heqsec2. reflexivity.
  + pose proof (nostt _ (or_introl eq_refl)) as Hctr.
    contradict Hctr. exact I.
Qed.


Lemma tloop_anc_eqset : forall x z, gproper x ->
  z <=/ x -> t_isloop z -> t_c x = true -> t_d x = t_lp z ->
  eqset (t_G x) (unnext (t_G z)).
Proof.
intros x y [px gpx] ylex yisl cox deqlp.
pose proof (desceq_proper (conj px gpx) ylex) as py.
destruct y; try contradiction.
pose proof (upward_ok py) as [Hequev [h [[Hhin Heqset] Heqlp]]].
destruct ylex as [yltx|yeqx].
- unfold t_G at 1. rewrite <- (same_d_HeqG (pfdownseqt px)) with h;
  try assumption.
  + apply (desc_common_H (conj px gpx) yltx h Hhin). rewrite <- Heqlp.
    rewrite <- deqlp. apply le_n.
  + rewrite <- Heqlp. apply eq_sym. assumption.
- rewrite <- yeqx. unfold t_G at 1.
  rewrite <- (same_d_HeqG (pfdownseqt py)) with h; try assumption.
  * rewrite yeqx. assumption.
  * rewrite <- Heqlp. rewrite <- deqlp. rewrite yeqx. reflexivity.
Qed.

Lemma tloop_uev_incl_anc : forall x z, gproper x ->
  z <=/ x -> t_isloop z -> t_c x = true -> t_d x = t_lp z ->
  incl (t_uev z) (t_G x).
Proof.
intros x y [px gpx] ylex yisl cox deqpl phi Hphi.
rewrite (eqset_in_iff (tloop_anc_eqset (conj px gpx) ylex yisl cox deqpl)).
pose proof (desceq_proper (conj px gpx) ylex) as py.
apply get_unts_in. destruct y; try contradiction. rewrite <- (proj1 (upward_ok py)).
assumption.
Qed.



Definition filler (x : ptree) := forall z n, z </ x -> t_d x < n <= t_d z ->
  {y | z <=/ y </ x /\ t_d y = n /\ t_c y = true}.

Definition t_info (x : ptree) (s : doseqt) :=
  {filx : filler x | gproper x /\ t_dose x = s}.

Definition open_info (s : doseqt) := {x & t_info x s}.

Inductive status (s : doseqt) :=
  | open   : open_info s -> status s
  | closed : unsatable (s_G s) -> status s.

Arguments open [s].
Arguments closed [s].

Definition loop_target (x y rt : ptree) :=
  x <=/ y </ rt /\ t_d y = t_lp x /\ t_c y = true /\
  eqset (t_G y) (unnext (t_G x)).

Definition looper (rt : ptree) := forall x : ptree,
  {y | loop_target x y rt} + {~ x <=/ rt \/ ~ t_isloop x}.

Record ltree : Type :=
{ l_root   : ptree;
  l_looper : looper (l_root) }.

Lemma l_desceq_proper [t : ltree] :
  gproper (l_root t) -> forall x, x <=/ l_root t -> proper x.
Proof.
intros gpt x xlert. destruct xlert as [xltrt|xeqrt].
- apply gpt; assumption.
- rewrite xeqrt. exact (proj1 gpt).
Qed.
