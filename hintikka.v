Require Import utils.
Require Import nnf.
Require Import closure.
Require Import semantics.
Require Import seqt.
Require Import ptree.
Require Import proper.
Require Import unravel.

Require Import Arith.
Require Import Nat.
Require Import List.
Require Import ListSet.
Require Import SetoidList.
Import ListNotations.
Require Import Relations.
Require Import Wellfounded.
Require Import Psatz.



Set Implicit Arguments.


Definition builder (L : nat -> list nnf) : kripke :=
{|world := list nnf;
  kseq  := L;
  val   := fun w p => In (var p) w|}.

Record pre_hintikka (hl : list nnf) : Prop :=
{ htk_no_contra : forall n, In (var n) hl -> ~ In (neg n) hl;
  htk_alpha     : forall phi, nnf_isalpha phi -> In phi hl ->
    In (nnf_alpha1 phi) hl /\ In (nnf_alpha2 phi) hl;
  htk_beta      : forall phi, nnf_isbeta phi -> In phi hl ->
    In (nnf_beta1 phi) hl \/ In (nnf_beta2 phi) hl; }.

Record hintikka (L : nat -> list nnf) :=
{ htk_prehin  : forall i, pre_hintikka (L i);
  htk_next    : forall i phi, In (next phi) (L i) -> In phi (L (S i));
  htk_fulfill : forall i phi psi, In (unt phi psi) (L i) ->
    exists k, k >= i /\ In psi (L k) }.

Theorem hintikka_satisfied :
  forall L, hintikka L -> forall i, satable (L i).
Proof.
intros L htkL i. exists (builder L), i. intro phi. revert i.
induction phi as [phi IH] using (well_founded_induction
(wf_inverse_image _ _ _ nnf_size Nat.lt_wf_0)).
intro i. destruct phi.
- simpl. tauto.
- simpl. intro Hctr. intro H. contradict Hctr.
  revert H. apply (htk_no_contra (htk_prehin htkL i)).
- simpl. intro H. set (phi := and phi1 phi2).
  pose proof (I : nnf_isalpha phi) as aphi.
  apply (htk_alpha (htk_prehin htkL i) phi aphi) in H.
  simpl in H. destruct H as [H1 H2].
  split; apply IH; (simpl; lia || assumption).
- simpl. intro H. set (phi := or phi1 phi2).
  pose proof (I : nnf_isbeta phi) as bphi.
  apply (htk_beta (htk_prehin htkL i) phi bphi) in H.
  simpl in H. destruct H as [H1|H2];
  [left|right]; apply IH; (simpl; lia || assumption).
- intro H. set (phi := bef phi1 phi2).
  pose proof (I : nnf_isalpha phi) as aphi.
  assert (forall j, In phi (L j) -> In (neg_nnf phi2) (L j)) as Hphin2.
  { intros j Hphi. apply (htk_alpha (htk_prehin htkL j) phi aphi) in Hphi. tauto. }
  simpl.
  set (psi := or phi1 (next phi)).
  pose proof (I : nnf_isbeta psi) as bpsi.
  pose proof (htk_alpha (htk_prehin htkL i) phi aphi H) as H0.
  simpl in H0. destruct H0 as [H1 H2].
  assert (forall n, n >= i -> (forall j, i <= j <= n -> In phi (L j))
  \/ (exists k, i <= k <= n /\ In phi1 (L k) /\
    (forall j, i <= j <= k -> In (neg_nnf phi2) (L j)))) as Htrav.
  { apply (induction_from_rank i).
  - left. intros j Hj. assert (j = i) as jeqi. { lia. }
    rewrite jeqi. assumption.
  - intros n lgei IHl. destruct IHl as [IHl|IHl].
    + lapply (IHl n); try lia. intro Hphi.
      apply (htk_alpha (htk_prehin htkL _) phi aphi) in Hphi.
      simpl in Hphi. destruct Hphi as [H1l H2l].
      apply (htk_beta (htk_prehin htkL n) psi bpsi) in H2l.
      simpl in H2l. destruct H2l as [H2l|H2l].
      * right. exists n. split; try lia.
        split; try assumption. intros j Hj.
        apply Hphin2. apply IHl. assumption.
      * left. apply (htk_next htkL) in H2l.
        intros j [ilej jleSp].
        destruct (le_lt_eq_dec _ _ jleSp) as [jltSp|jeqSp].
       -- apply IHl. lia.
       -- rewrite jeqSp. assumption.
    + right. destruct IHl as [k [klep Hk]].
      exists k. split; try lia. assumption. }
  intros n ilen forphi2.
  specialize (Htrav n ilen). destruct Htrav as [Htrav|Htrav].
  + contradict forphi2. apply force_neg_not.
    apply IH; try (rewrite size_neg_eq_size; simpl; lia).
    apply Hphin2. apply Htrav. lia.
  + destruct Htrav as [k [ikn [Hphik alln2]]].
    destruct (le_lt_eq_dec _ _ (proj2 ikn)) as [kltl|keql].
    * exists k. split; try tauto.
      apply IH; (simpl; lia || assumption).
    * contradict forphi2. apply force_neg_not.
      apply IH; try (rewrite size_neg_eq_size; simpl; lia).
      apply alln2. lia.
- intro H. set (phi := unt phi1 phi2).
  pose proof (I : nnf_isbeta phi) as bphi.
  set (psi := and phi1 (next phi)).
  pose proof (I : nnf_isalpha psi) as apsi.
  assert (forall n, n >= i -> (forall j, i <= j <= n ->
  In phi (L j) /\ In phi1 (L j) /\ ~ In phi2 (L j))
  \/ (exists k, i <= k <= n /\ In phi2 (L k) /\
    (forall j, i <= j < k -> In phi1 (L j)))) as Htrav.
  { apply (induction_from_rank i).
  - destruct (in_dec nnf_eqdec phi2 (L i)) as [Hphi2i|Hphi2i].
    + right. exists i. split; try (split; left).
      split; try assumption. intros j Hj. lia.
    + left. intros j Hj. assert (j = i) as jeqi. { lia. }
      rewrite jeqi. repeat (split; try assumption).
      apply (htk_beta (htk_prehin htkL _) phi bphi) in H.
      simpl in H. destruct H as [H|H]; try contradiction.
      apply (htk_alpha (htk_prehin htkL _) psi apsi) in H.
      simpl in H. tauto.
  - intros n ngei IHn. destruct IHn as [IHn|IHn].
    + destruct (in_dec nnf_eqdec phi2 (L (S n))) as [Hphi2Sn|Hphi2Sn].
      * right. exists (S n). split; try lia. split; try assumption.
        intros j Hj. lapply (IHn j); try lia. tauto.
      * left. intros j [ilej jleSn].
        destruct (le_lt_eq_dec _ _ jleSn) as [jltSn|jeqSn].
       -- apply IHn. lia.
       -- rewrite jeqSn. lapply (IHn n); try lia.
          intro H0. destruct H0 as [Hphin [Hphi1n Hphi2n]].
          apply (htk_beta (htk_prehin htkL _) phi bphi) in Hphin.
          simpl in Hphin. destruct Hphin as [Hphin|Hphin];
          try contradiction.
          apply (htk_alpha (htk_prehin htkL _) psi apsi) in Hphin.
          simpl in Hphin. destruct Hphin as [_ Hphin].
          apply (htk_next htkL) in Hphin.
          pose proof (htk_beta (htk_prehin htkL _) phi bphi Hphin) as H0.
          simpl in H0. destruct H0 as [H0|H0];
          try contradiction.
          apply (htk_alpha (htk_prehin htkL _) psi apsi) in H0.
          simpl in H0. destruct H0 as [H0 _].
          repeat (split; try assumption).
    + right. destruct IHn as [k [ikn Hk]].
      exists k. split; try lia. assumption. }
  destruct (htk_fulfill htkL _ _ _ H) as [n [ngei Hphi2n]].
  specialize (Htrav n ngei).
  destruct Htrav as [Htrav|Htrav].
  + lapply (Htrav n); try lia. intro Hctr. tauto.
  + simpl. destruct Htrav as [k [ikn [Hphi2k allj]]].
    exists k. split; try tauto. split.
    * apply IH; try (simpl; lia). assumption.
    * intros j Hj. apply IH; try (simpl; lia).
      apply allj. assumption.
- intro H. simpl. apply IH; try (simpl; lia).
  apply (htk_next htkL). assumption.
Qed.


Section BuildHintikka.

  Variable Tl : ltree.
  Hypothesis gpt : gproper (l_root Tl).

  (* Turn tree model Tl into Hintikka structure *)

  Record hin_unit : Set :=
  { hu_htk : list nnf;
    hu_lb  : nat;
    hu_ub  : nat }.

  Definition hu_nlb (hu : hin_unit) : ptree := unravel Tl (hu_lb hu).
  Definition hu_nub (hu : hin_unit) : ptree := unravel Tl (hu_ub hu).
  Definition hu_trail (hu : hin_unit) : list ptree :=
    unravel_from_to Tl (hu_lb hu) (hu_ub hu).

  Record phin_unit (hu : hin_unit) : Prop :=
  { hu_prehin         : pre_hintikka (hu_htk hu);
    hu_orig_tr_or_fi  : In (hu_nlb hu) (hu_trail hu) \/
      hu_nlb hu = hu_nub hu;
    hu_next_in_state  : forall phi, In (next phi) (hu_htk hu) ->
      In (next phi) (t_G (hu_nub hu));
    hu_state_isstate  : t_isstate (hu_nub hu);
    hu_in_htkl_iff    : forall phi, In phi (hu_htk hu) <->
      (In phi (t_G (hu_nlb hu)) \/
      (exists x, In x (hu_trail hu) /\ In phi (t_G x)) \/
      In phi (t_G (hu_nub hu)));
    hu_ix_origlefin   : hu_lb hu <= hu_ub hu; }.

  Definition make_hu (x : ptree) : forall n,
    x = unravel Tl n -> {hu | phin_unit hu /\ hu_lb hu = n}.
  Proof.
  induction x as [c IHc fs phi|c IHc fs phi|c IHc fs phi|
  c1 IHc1 c2 IHc2 fs phi|c IHc fs|fs];
    intros n Heqx; pose proof (unravel_desceq_rt Tl n) as xlert;
    rewrite <- Heqx in xlert; pose proof (l_desceq_proper gpt xlert) as px;
    pose proof (prinform_ok px) as Hprin; simpl in Hprin;
    pose proof (downward_ok px) as Heqsec.
  - set (x := talpha c fs phi). fold x in Heqx.
    pose proof (False_ind _ : ~ t_isloop x) as Hnlx.
    rewrite Heqx in Hnlx.
    pose proof (unravel_child Tl Hnlx) as Hch.
    rewrite <- Heqx in Hch. simpl in Hch. apply eq_sym in Hch.
    pose proof (IHc (S n) Hch) as [huc [phuc Heqfixc]].
    assert (incl (t_G c) (hu_htk huc)) as Ginhtkc.
    { intros psi Hpsi. apply (hu_in_htkl_iff phuc).
    left. unfold hu_nlb.
    rewrite Heqfixc. rewrite <- Hch. assumption. }
    set (phx := {|
    hu_htk     := phi :: (hu_htk huc);
    hu_lb := n;
    hu_ub := hu_ub huc
    |}).
    assert (hu_trail phx = x :: hu_trail huc) as Heqpa.
    { unfold hu_trail. rewrite Heqx, Heqfixc. simpl.
    apply unravel_from_to_eq_cons.
    apply Arith_prebase.le_S_gt_stt.
    rewrite <- Heqfixc. apply (hu_ix_origlefin phuc). }
    assert (incl (t_G x) (hu_htk phx)) as Ginhtkx.
    { intros xi Hxi.
    destruct (nnf_eqdec xi phi) as [Heq|Hneq].
    - left. apply eq_sym. assumption.
    - right. apply Ginhtkc. unfold t_G.
      rewrite Heqsec. right; right. fold (t_G x).
      apply (in_in_remove _ _ Hneq Hxi). }
    exists phx. split; try reflexivity.
    constructor. 1: constructor.
    + intros k Hvark. destruct Hvark as [Hphi|Hphi];
      try (contradict (eq_ind _ _ Hprin _ Hphi)).
      intro Hctr. destruct Hctr as [Hctr|Hctr];
      try (contradict (eq_ind _ _ Hprin _ Hctr)).
      contradict Hctr. apply (htk_no_contra (hu_prehin phuc)).
      assumption.
    + intros psi apsi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
      * split; right; apply Ginhtkc; unfold t_G;
        rewrite Heqsec; simpl; [left|right;left]; rewrite Hpsi; reflexivity.
      * apply (htk_alpha (hu_prehin phuc) psi apsi) in Hpsi.
        split; right; tauto.
    + intros psi bpsi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
      * pose proof (beta_not_alpha bpsi) as Hctr.
        rewrite <- Hpsi in Hctr. contradiction.
      * apply (htk_beta (hu_prehin phuc) psi bpsi) in Hpsi.
        destruct Hpsi as [Hpsi|Hpsi];
        [left|right]; right; assumption.
    + rewrite Heqpa. left. left. assumption.
    + intros xi Hxi. destruct Hxi as [Hxi|Hxi].
      * contradict (eq_ind _ _ Hprin _ Hxi).
      * apply (hu_next_in_state phuc _ Hxi).
    + apply (hu_state_isstate phuc).
    + intro xi. split.
      { intro Hxi. destruct Hxi as [Hxi|Hxi].
      - left. unfold hu_nlb. simpl. rewrite <- Heqx.
        rewrite <- Hxi. apply (has_prinform px). reflexivity.
      - apply (hu_in_htkl_iff phuc) in Hxi.
        destruct Hxi as [Hxi|[Hxi|Hxi]].
        + destruct (hu_orig_tr_or_fi phuc) as [fipa|fist].
          * right; left. exists (hu_nlb huc). rewrite Heqpa.
            split; [now right | assumption].
          * right; right. unfold hu_nub in fist |- *.
            simpl. rewrite <- fist. assumption.
        + right; left. destruct Hxi as [y [Hy Hy0]].
          exists y. rewrite Heqpa. split; [now right | assumption].
        + right; right. assumption. }
      { intro Hxi. destruct Hxi as [Hxi|[Hxi|Hxi]].
      - apply Ginhtkx. rewrite Heqx. assumption.
      - destruct Hxi as [y [Hy Hxi]]. rewrite Heqpa in Hy.
        destruct Hy as [Hy|Hy].
        + rewrite <- Hy in Hxi. apply (Ginhtkx _ Hxi).
        + right. apply (hu_in_htkl_iff phuc).
          right; left. exists y. split; assumption.
      - right. apply (hu_in_htkl_iff phuc).
        right; right. assumption. }
    + simpl. apply Nat.le_trans with (S n); try lia.
      rewrite <- Heqfixc. apply (hu_ix_origlefin phuc).
  - set (x := tbeta1 c fs phi). fold x in Heqx.
    pose proof (False_ind _ : ~ t_isloop x) as Hnlx.
    rewrite Heqx in Hnlx.
    pose proof (unravel_child Tl Hnlx) as Hch.
    rewrite <- Heqx in Hch. simpl in Hch. apply eq_sym in Hch.
    pose proof (IHc (S n) Hch) as [huc [phuc Heqfixc]].
    assert (incl (t_G c) (hu_htk huc)) as Ginhtkc.
    { intros psi Hpsi. apply (hu_in_htkl_iff phuc).
    left. unfold hu_nlb.
    rewrite Heqfixc. rewrite <- Hch. assumption. }
    set (phx := {|
    hu_htk     := phi :: (hu_htk huc);
    hu_lb := n;
    hu_ub := hu_ub huc
    |}).
    assert (hu_trail phx = x :: hu_trail huc) as Heqpa.
    { unfold hu_trail. rewrite Heqx, Heqfixc. simpl.
    apply unravel_from_to_eq_cons.
    apply Arith_prebase.le_S_gt_stt.
    rewrite <- Heqfixc. apply (hu_ix_origlefin phuc). }
    assert (incl (t_G x) (hu_htk phx)) as Ginhtkx.
    { intros xi Hxi.
    destruct (nnf_eqdec xi phi) as [Heq|Hneq].
    - left. apply eq_sym. assumption.
    - right. apply Ginhtkc. unfold t_G.
      rewrite Heqsec. right. fold (t_G x).
      apply (in_in_remove _ _ Hneq Hxi). }
    exists phx. split; try reflexivity.
    constructor. 1: constructor.
    + intros k Hvark. destruct Hvark as [Hphi|Hphi];
      try (contradict (eq_ind _ _ Hprin _ Hphi)).
      intro Hctr. destruct Hctr as [Hctr|Hctr];
      try (contradict (eq_ind _ _ Hprin _ Hctr)).
      contradict Hctr. apply (htk_no_contra (hu_prehin phuc)).
      assumption.
    + intros psi apsi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
      * pose proof (beta_not_alpha Hprin) as H.
        contradict H. rewrite Hpsi. assumption.
      * apply (htk_alpha (hu_prehin phuc) psi apsi) in Hpsi.
        split; right; tauto.
    + intros psi bpsi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
      * left. right. apply Ginhtkc. unfold t_G.
        rewrite Heqsec. simpl. rewrite Hpsi. now left.
      * apply (htk_beta (hu_prehin phuc) psi bpsi) in Hpsi.
        destruct Hpsi as [Hpsi|Hpsi]; [left|right]; now right.
    + rewrite Heqpa. left. left. assumption.
    + intros xi Hxi. destruct Hxi as [Hxi|Hxi].
      * contradict (eq_ind _ _ Hprin _ Hxi).
      * apply (hu_next_in_state phuc _ Hxi).
    + apply (hu_state_isstate phuc).
    + intro xi. split.
      { intro Hxi. destruct Hxi as [Hxi|Hxi].
      - left. unfold hu_nlb. simpl. rewrite <- Heqx.
        rewrite <- Hxi. apply (has_prinform px). reflexivity.
      - apply (hu_in_htkl_iff phuc) in Hxi.
        destruct Hxi as [Hxi|[Hxi|Hxi]].
        + destruct (hu_orig_tr_or_fi phuc) as [fipa|fist].
          * right; left. exists (hu_nlb huc). rewrite Heqpa.
            split; [now right | assumption].
          * right; right. unfold hu_nub in fist |- *.
            simpl. rewrite <- fist. assumption.
        + right; left. destruct Hxi as [y [Hy Hy0]]. rewrite Heqpa.
          exists y. split; [now right | assumption].
        + right; right. assumption. }
      { intro Hxi. destruct Hxi as [Hxi|[Hxi|Hxi]].
      - apply Ginhtkx. rewrite Heqx. assumption.
      - destruct Hxi as [y [Hy Hxi]]. rewrite Heqpa in Hy.
        destruct Hy as [Hy|Hy].
        + rewrite <- Hy in Hxi. apply (Ginhtkx _ Hxi).
        + right. apply (hu_in_htkl_iff phuc).
          right; left. exists y. split; assumption.
      - right. apply (hu_in_htkl_iff phuc).
        right; right. assumption. }
    + simpl. apply Nat.le_trans with (S n); try lia.
      rewrite <- Heqfixc. apply (hu_ix_origlefin phuc).
  - set (x := tbeta2 c fs phi). fold x in Heqx.
    pose proof (False_ind _ : ~ t_isloop x) as Hnlx.
    rewrite Heqx in Hnlx.
    pose proof (unravel_child Tl Hnlx) as Hch.
    rewrite <- Heqx in Hch. simpl in Hch. apply eq_sym in Hch.
    pose proof (IHc (S n) Hch) as [huc [phuc Heqfixc]].
    assert (incl (t_G c) (hu_htk huc)) as Ginhtkc.
    { intros psi Hpsi. apply (hu_in_htkl_iff phuc).
    left. unfold hu_nlb. 
    rewrite Heqfixc. rewrite <- Hch. assumption. }
    set (phx := {|
    hu_htk     := phi :: (hu_htk huc);
    hu_lb := n;
    hu_ub := hu_ub huc
    |}).
    assert (hu_trail phx = x :: hu_trail huc) as Heqpa.
    { unfold hu_trail. rewrite Heqx, Heqfixc. simpl.
    apply unravel_from_to_eq_cons.
    apply Arith_prebase.le_S_gt_stt.
    rewrite <- Heqfixc. apply (hu_ix_origlefin phuc). }
    assert (incl (t_G x) (hu_htk phx)) as Ginhtkx.
    { intros xi Hxi.
    destruct (nnf_eqdec xi phi) as [Heq|Hneq].
    - left. apply eq_sym. assumption.
    - right. apply Ginhtkc. unfold t_G.
      rewrite Heqsec. right. fold (t_G x).
      apply (in_in_remove _ _ Hneq Hxi). }
    exists phx. split; try reflexivity.
    constructor. 1: constructor.
    + intros k Hvark. destruct Hvark as [Hphi|Hphi];
      try (contradict (eq_ind _ _ Hprin _ Hphi)).
      intro Hctr. destruct Hctr as [Hctr|Hctr];
      try (contradict (eq_ind _ _ Hprin _ Hctr)).
      contradict Hctr. apply (htk_no_contra (hu_prehin phuc)).
      assumption.
    + intros psi apsi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
      * pose proof (beta_not_alpha Hprin) as H.
        contradict H. rewrite Hpsi. assumption.
      * apply (htk_alpha (hu_prehin phuc) psi apsi) in Hpsi.
        split; right; tauto.
    + intros psi bpsi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
      * right. right. apply Ginhtkc. unfold t_G.
        rewrite Heqsec. simpl. rewrite Hpsi. now left.
      * apply (htk_beta (hu_prehin phuc) psi bpsi) in Hpsi.
        destruct Hpsi as [Hpsi|Hpsi]; [left|right]; now right.
    + rewrite Heqpa. left. left. assumption.
    + intros xi Hxi. destruct Hxi as [Hxi|Hxi].
      * contradict (eq_ind _ _ Hprin _ Hxi).
      * apply (hu_next_in_state phuc _ Hxi).
    + apply (hu_state_isstate phuc).
    + intro xi. split.
      { intro Hxi. destruct Hxi as [Hxi|Hxi].
      - left. unfold hu_nlb. simpl. rewrite <- Heqx.
        rewrite <- Hxi. apply (has_prinform px). reflexivity.
      - apply (hu_in_htkl_iff phuc) in Hxi.
        destruct Hxi as [Hxi|[Hxi|Hxi]].
        + destruct (hu_orig_tr_or_fi phuc) as [fipa|fist].
          * right; left. exists (hu_nlb huc). rewrite Heqpa.
            split; [now right | assumption].
          * right; right. unfold hu_nub in fist |- *.
            simpl. rewrite <- fist. assumption.
        + right; left. destruct Hxi as [y [Hy Hy0]]. rewrite Heqpa.
          exists y. split; [now right | assumption].
        + right; right. assumption. }
      { intro Hxi. destruct Hxi as [Hxi|[Hxi|Hxi]].
      - apply Ginhtkx. rewrite Heqx. assumption.
      - destruct Hxi as [y [Hy Hxi]]. rewrite Heqpa in Hy.
        destruct Hy as [Hy|Hy].
        + rewrite <- Hy in Hxi. apply (Ginhtkx _ Hxi).
        + right. apply (hu_in_htkl_iff phuc).
          right; left. exists y. split; assumption.
      - right. apply (hu_in_htkl_iff phuc).
        right; right. assumption. }
    + simpl. apply Nat.le_trans with (S n); try lia.
      rewrite <- Heqfixc. apply (hu_ix_origlefin phuc).
  - set (x := talt c1 c2 fs phi). fold x in Heqx.
    destruct Heqsec as [Heqsec1 Heqsec2].
    pose proof (False_ind _ : ~ t_isloop x) as Hnlx.
    rewrite Heqx in Hnlx.
    pose proof (unravel_child Tl Hnlx) as Hch.
    rewrite <- Heqx in Hch.
    destruct (ptree_eqdec c1 (unravel Tl (S n))) as [Heqc1|Hneqc1].
    {
    pose proof (IHc1 (S n) Heqc1) as [huc [phuc Heqfixc]].
    assert (incl (t_G c1) (hu_htk huc)) as Ginhtkc.
    { intros psi Hpsi. apply (hu_in_htkl_iff phuc).
    left. unfold hu_nlb.
    rewrite Heqfixc. rewrite <- Heqc1. assumption. }
    set (phx := {|
    hu_htk     := phi :: (hu_htk huc);
    hu_lb := n;
    hu_ub := hu_ub huc
    |}).
    assert (hu_trail phx = x :: hu_trail huc) as Heqpa.
    { unfold hu_trail. rewrite Heqx, Heqfixc. simpl.
    apply unravel_from_to_eq_cons.
    apply Arith_prebase.le_S_gt_stt.
    rewrite <- Heqfixc. apply (hu_ix_origlefin phuc). }
    assert (incl (t_G x) (hu_htk phx)) as Ginhtkx.
    { intros xi Hxi.
    destruct (nnf_eqdec xi phi) as [Heq|Hneq].
    - left. apply eq_sym. assumption.
    - right. apply Ginhtkc. unfold t_G.
      rewrite Heqsec1. right. fold (t_G x).
      apply (in_in_remove _ _ Hneq Hxi). }
    exists phx. split; try reflexivity.
    constructor. 1: constructor.
    + intros k Hvark. destruct Hvark as [Hphi|Hphi];
      try (contradict (eq_ind _ _ Hprin _ Hphi)).
      intro Hctr. destruct Hctr as [Hctr|Hctr];
      try (contradict (eq_ind _ _ Hprin _ Hctr)).
      contradict Hctr. apply (htk_no_contra (hu_prehin phuc)).
      assumption.
    + intros psi apsi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
      * pose proof (beta_not_alpha Hprin) as H.
        contradict H. rewrite Hpsi. assumption.
      * apply (htk_alpha (hu_prehin phuc) psi apsi) in Hpsi.
        split; right; tauto.
    + intros psi bpsi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
      * left. right. apply Ginhtkc. unfold t_G.
        rewrite Heqsec1. simpl. rewrite Hpsi. now left.
      * apply (htk_beta (hu_prehin phuc) psi bpsi) in Hpsi.
        destruct Hpsi as [Hpsi|Hpsi]; [left|right]; now right.
    + rewrite Heqpa. left. left. assumption.
    + intros xi Hxi. destruct Hxi as [Hxi|Hxi].
      * contradict (eq_ind _ _ Hprin _ Hxi).
      * apply (hu_next_in_state phuc _ Hxi).
    + apply (hu_state_isstate phuc).
    + intro xi. split.
      { intro Hxi. destruct Hxi as [Hxi|Hxi].
      - left. unfold hu_nlb. simpl. rewrite <- Heqx.
        rewrite <- Hxi. apply (has_prinform px). reflexivity.
      - apply (hu_in_htkl_iff phuc) in Hxi.
        destruct Hxi as [Hxi|[Hxi|Hxi]].
        + destruct (hu_orig_tr_or_fi phuc) as [fipa|fist].
          * right; left. exists (hu_nlb huc). rewrite Heqpa.
            split; [now right | assumption].
          * right; right. unfold hu_nub in fist |- *.
            simpl. rewrite <- fist. assumption.
        + right; left. destruct Hxi as [y [Hy Hy0]]. rewrite Heqpa.
          exists y. split; [now right | assumption].
        + right; right. assumption. }
      { intro Hxi. destruct Hxi as [Hxi|[Hxi|Hxi]].
      - apply Ginhtkx. rewrite Heqx. assumption.
      - destruct Hxi as [y [Hy Hxi]]. rewrite Heqpa in Hy.
        destruct Hy as [Hy|Hy].
        + rewrite <- Hy in Hxi. apply (Ginhtkx _ Hxi).
        + right. apply (hu_in_htkl_iff phuc).
          right; left. exists y. split; assumption.
      - right. apply (hu_in_htkl_iff phuc).
        right; right. assumption. }
    + simpl. apply Nat.le_trans with (S n); try lia.
      rewrite <- Heqfixc. apply (hu_ix_origlefin phuc).
    }
    destruct (ptree_eqdec c2 (unravel Tl (S n))) as [Heqc2|Hneqc2].
    {
    pose proof (IHc2 (S n) Heqc2) as [huc [phuc Heqfixc]].
    assert (incl (t_G c2) (hu_htk huc)) as Ginhtkc.
    { intros psi Hpsi. apply (hu_in_htkl_iff phuc).
    left. unfold hu_nlb.
    rewrite Heqfixc. rewrite <- Heqc2. assumption. }
    set (phx := {|
    hu_htk     := phi :: (hu_htk huc);
    hu_lb := n;
    hu_ub := hu_ub huc
    |}).
    assert (hu_trail phx = x :: hu_trail huc) as Heqpa.
    { unfold hu_trail. rewrite Heqx, Heqfixc. simpl.
    apply unravel_from_to_eq_cons.
    apply Arith_prebase.le_S_gt_stt.
    rewrite <- Heqfixc. apply (hu_ix_origlefin phuc). }
    assert (incl (t_G x) (hu_htk phx)) as Ginhtkx.
    { intros xi Hxi.
    destruct (nnf_eqdec xi phi) as [Heq|Hneq].
    - left. apply eq_sym. assumption.
    - right. apply Ginhtkc. unfold t_G.
      rewrite Heqsec2. right. fold (t_G x).
      apply (in_in_remove _ _ Hneq Hxi). }
    exists phx. split; try reflexivity.
    constructor. 1: constructor.
    + intros k Hvark. destruct Hvark as [Hphi|Hphi];
      try (contradict (eq_ind _ _ Hprin _ Hphi)).
      intro Hctr. destruct Hctr as [Hctr|Hctr];
      try (contradict (eq_ind _ _ Hprin _ Hctr)).
      contradict Hctr. apply (htk_no_contra (hu_prehin phuc)).
      assumption.
    + intros psi apsi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
      * pose proof (beta_not_alpha Hprin) as H.
        contradict H. rewrite Hpsi. assumption.
      * apply (htk_alpha (hu_prehin phuc) psi apsi) in Hpsi.
        split; right; tauto.
    + intros psi bpsi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
      * right. right. apply Ginhtkc. unfold t_G.
        rewrite Heqsec2. simpl. rewrite Hpsi. now left.
      * apply (htk_beta (hu_prehin phuc) psi bpsi) in Hpsi.
        destruct Hpsi as [Hpsi|Hpsi]; [left|right]; now right.
    + rewrite Heqpa. left. left. assumption.
    + intros xi Hxi. destruct Hxi as [Hxi|Hxi].
      * contradict (eq_ind _ _ Hprin _ Hxi).
      * apply (hu_next_in_state phuc _ Hxi).
    + apply (hu_state_isstate phuc).
    + intro xi. split.
      { intro Hxi. destruct Hxi as [Hxi|Hxi].
      - left. unfold hu_nlb. simpl. rewrite <- Heqx.
        rewrite <- Hxi. apply (has_prinform px). reflexivity.
      - apply (hu_in_htkl_iff phuc) in Hxi.
        destruct Hxi as [Hxi|[Hxi|Hxi]].
        + destruct (hu_orig_tr_or_fi phuc) as [fipa|fist].
          * right; left. exists (hu_nlb huc). rewrite Heqpa.
            split; [now right | assumption].
          * right; right. unfold hu_nub in fist |- *.
            simpl. rewrite <- fist. assumption.
        + right; left. destruct Hxi as [y [Hy Hy0]]. rewrite Heqpa.
          exists y. split; [now right | assumption].
        + right; right. assumption. }
      { intro Hxi. destruct Hxi as [Hxi|[Hxi|Hxi]].
      - apply Ginhtkx. rewrite Heqx. assumption.
      - destruct Hxi as [y [Hy Hxi]]. rewrite Heqpa in Hy.
        destruct Hy as [Hy|Hy].
        + rewrite <- Hy in Hxi. apply (Ginhtkx _ Hxi).
        + right. apply (hu_in_htkl_iff phuc).
          right; left. exists y. split; assumption.
      - right. apply (hu_in_htkl_iff phuc).
        right; right. assumption. }
    + simpl. apply Nat.le_trans with (S n); try lia.
      rewrite <- Heqfixc. apply (hu_ix_origlefin phuc).
    }
    exfalso. destruct Hch as [Hch|Hch];
    apply eq_sym in Hch; contradiction.
  - set (x := tjump c fs). fold x in Heqx.
    pose proof (state_has_sc px I) as scx.
    set (phx := {|
    hu_htk  := t_G x;
    hu_lb := n;
    hu_ub := n
    |}).
    assert (hu_trail phx = []) as Heqpa.
    { unfold hu_trail. apply unravel_from_to_same. }
    exists phx. split; try reflexivity.
    constructor. 1: constructor.
    all: simpl; try (tauto || contradiction || lia).
    + apply (sc_no_contra scx).
    + intros phi aphi Hphi.
      apply (sc_no_alpha scx) in Hphi. contradiction.
    + intros phi bphi Hphi.
      apply (sc_no_beta scx) in Hphi. contradiction.
    + unfold hu_nub. simpl. rewrite <- Heqx. tauto.
    + unfold hu_nub. simpl. rewrite <- Heqx. exact I.
    + intro phi. split;
      try (unfold hu_nlb; simpl; rewrite <- Heqx; tauto).
      intro Hphi. destruct Hphi as [Hphi|[Hphi|Hphi]].
      * rewrite Heqx. assumption.
      * destruct Hphi as [y [Hctr _]]. rewrite Heqpa in Hctr. contradiction.
      * rewrite Heqx. assumption.
  - set (x := tloop fs). fold x in Heqx.
    pose proof (state_has_sc px I) as scx.
    set (phx := {|
    hu_htk  := t_G x;
    hu_lb := n;
    hu_ub := n
    |}).
    assert (hu_trail phx = []) as Heqpa.
    { unfold hu_trail. apply unravel_from_to_same. }
    exists phx. split; try reflexivity.
    constructor. 1: constructor.
    all: simpl; try (tauto || contradiction || lia).
    + apply (sc_no_contra scx).
    + intros phi aphi Hphi.
      apply (sc_no_alpha scx) in Hphi. contradiction.
    + intros phi bphi Hphi.
      apply (sc_no_beta scx) in Hphi. contradiction.
    + unfold hu_nub. simpl. rewrite <- Heqx. tauto.
    + unfold hu_nub. simpl. rewrite <- Heqx. exact I.
    + intro phi. split;
      try (unfold hu_nlb; simpl; rewrite <- Heqx; tauto).
      intro Hphi. destruct Hphi as [Hphi|[Hphi|Hphi]].
      * rewrite Heqx. assumption.
      * destruct Hphi as [y [Hctr _]]. rewrite Heqpa in Hctr. contradiction.
      * rewrite Heqx. assumption.
  Defined.

  Arguments make_hu: clear implicits.

  Fixpoint munrav (n : nat) : {hu | phin_unit hu} :=
    match n with
    | 0   =>
        match make_hu (l_root Tl) 0 eq_refl
        with exist _ hu (conj phu _) => exist _ hu phu end
    | S m => let index := (S (hu_ub (proj1_sig (munrav m)))) in
        match make_hu (unravel Tl index) index eq_refl
        with exist _ hu (conj phu _) => exist _ hu phu end
    end.

  Lemma munrav_succ_eq : forall n,
    let index := (S (hu_ub (proj1_sig (munrav n)))) in
    munrav (S n) = match make_hu (unravel Tl index)
    index eq_refl with exist _ hu (conj phu _) => exist _ hu phu end.
  Proof.
  intro n. simpl. reflexivity.
  Qed.

  Lemma proj_munrav_succ_eq : forall n,
    let index := (S (hu_ub (proj1_sig (munrav n)))) in
    proj1_sig (munrav (S n)) = proj1_sig (make_hu (unravel Tl index)
    index eq_refl).
  Proof.
  intro n. rewrite munrav_succ_eq.
  remember (S (hu_ub (proj1_sig (munrav n)))) as index.
  cbv zeta.
  destruct (make_hu (unravel Tl index) index eq_refl)
  as [hu [phu H]]. simpl. reflexivity.
  Qed.

  Lemma orix_munrav_succ_eq : forall n,
    hu_lb (proj1_sig (munrav (S n))) =
    S (hu_ub (proj1_sig (munrav n))).
  Proof.
  intro n. rewrite proj_munrav_succ_eq.
  set (index := (S (hu_ub (proj1_sig (munrav n))))).
  destruct (make_hu (unravel Tl index) index eq_refl)
  as [hu [phu Hph]]. simpl. assumption.
  Qed.


  Definition hunrav : nat -> list nnf := fun n => hu_htk (proj1_sig (munrav n)).


  Theorem hunrav_htk_next : forall i phi,
    In (next phi) (hunrav i) -> In phi (hunrav (S i)).
  Proof.
  intros i phi H.
  unfold hunrav. simpl. unfold hunrav in H.
  set (index := (hu_ub (proj1_sig (munrav i)))).
  destruct (make_hu (unravel Tl (S index)) (S index) eq_refl)
  as [pSi [ppSi HeqfipSi]]. simpl.
  destruct (munrav i) as [pi ppi].
  simpl in H, index. apply (hu_next_in_state ppi) in H.
  pose proof (hu_state_isstate ppi) as H0.
  unfold hu_nub in H, H0. fold index in H, H0.
  apply (hu_in_htkl_iff ppSi). left. unfold hu_nlb. rewrite HeqfipSi.
  pose proof (unravel_desceq_rt Tl index) as xlert.
  pose proof (desceq_proper gpt xlert) as px.
  destruct (unravel Tl index) as [| | | |c fs|fs] eqn:Hequtix;
  try contradiction.
  - set (x := tjump c fs) in *.
    pose proof (downward_ok px) as Heqsec.
    pose proof (False_ind _ : ~ t_isloop x) as Hnlx.
    rewrite <- Hequtix in Hnlx.
    pose proof (unravel_child Tl Hnlx) as Hch.
    rewrite Hequtix in Hch. simpl in Hch.
    unfold t_G. rewrite Hch, Heqsec. simpl.
    fold x (t_G x). apply in_next_in_unnext.
    assumption.
  - set (x := tloop fs) in *.
    pose proof (I : t_isloop x) as Hlx.
    rewrite <- Hequtix in Hlx.
    pose proof (unravel_loop_target Tl Hlx) as Hch.
    destruct Hch as [_ [_ [_ Heqset]]].
    apply (eqset_in_iff Heqset). rewrite Hequtix.
    apply in_next_in_unnext. assumption.
  Qed.

  Lemma munrav_ix_catches_all_nat : forall n, exists i,
    hu_lb (proj1_sig (munrav i)) <= n <= hu_ub (proj1_sig (munrav i)).
  Proof.
  induction n.
  - exists 0. simpl.
    destruct (make_hu (l_root Tl) 0 eq_refl) as [hu [phu Heqfiph]].
    simpl. rewrite Heqfiph. lia.
  - destruct IHn as [i [filen nlesi]].
    set (index := hu_ub (proj1_sig (munrav i))).
    destruct (le_lt_eq_dec _ _ nlesi) as [nltsi|neqsi].
    + exists i. lia.
    + exists (S i). split.
      * rewrite orix_munrav_succ_eq, neqsi. apply le_n.
      * rewrite neqsi, <- orix_munrav_succ_eq.
        destruct (munrav (S i)) as [hu phu]. simpl.
        apply (hu_ix_origlefin phu).
  Qed.

  Lemma ub_lt_succ_lb : forall i j, i < j ->
    hu_ub (proj1_sig (munrav i)) < hu_lb (proj1_sig (munrav j)).
  Proof.
  intros i j iltj. unfold lt in iltj. revert j iltj.
  apply induction_from_rank.
  - rewrite orix_munrav_succ_eq. apply le_n.
  - intros j jgeSi IH. eapply Nat.le_trans; try apply IH.
    eapply Nat.le_trans.
    + apply (hu_ix_origlefin (proj2_sig (munrav j))).
    + rewrite orix_munrav_succ_eq. apply le_S, le_n.
  Qed.

  Lemma between_ix_in_hunrav : forall i n,
    hu_lb (proj1_sig (munrav i)) <= n <= hu_ub (proj1_sig (munrav i)) ->
    incl (t_G (unravel Tl n)) (hunrav i).
  Proof.
  intros i n H phi Hphi. unfold hunrav.
  destruct (munrav i) as [hu phu]. simpl in H |- *.
  destruct (le_lt_eq_dec _ _ (proj2 H)) as [nlt|neq].
  - apply (hu_in_htkl_iff phu). right; left.
    exists (unravel Tl n). split; try assumption.
    apply (unravel_from_to_between_in Tl (conj (proj1 H) nlt)).
  - apply (hu_in_htkl_iff phu). right; right.
    unfold hu_nub. rewrite <- neq. assumption.
  Qed.

  Theorem hunrav_htk_fulfill : forall i phi psi,
    In (unt phi psi) (hunrav i) ->
    exists k, k >= i /\ In psi (hunrav k).
  Proof.
  intros i phi psi Hin. unfold hunrav in Hin.
  destruct (munrav i) as [hu phu] eqn:Heqtphti.
  simpl in Hin. assert (hu = proj1_sig (munrav i)) as Heqph.
  { rewrite Heqtphti. simpl. reflexivity. }
  assert (exists k, k >= (hu_lb hu) /\
  In psi (t_G (unravel Tl k))) as Hex.
  { apply (hu_in_htkl_iff phu) in Hin.
  destruct Hin as [Hin|[Hin|Hin]].
  - unfold hu_nlb in Hin.
    apply (unravel_ev_fulfilled _ gpt _ _ _ Hin).
  - destruct Hin as [x [Hx Hin]].
    destruct (unravel_from_to_in_between _ _ _ _ Hx)
    as [x_ix [[filex xltsi] Heqx]].
    rewrite Heqx in Hin.
    apply unravel_ev_fulfilled in Hin; try assumption.
    destruct Hin as [k [kgex H]].
    exists k. split; try assumption.
    apply (Nat.le_trans _ _ _ filex kgex).
  - unfold hu_nub in Hin.
    apply unravel_ev_fulfilled in Hin; try assumption.
    destruct Hin as [k [kgesi H]].
    exists k. split; try assumption.
    eapply Nat.le_trans; try apply kgesi.
    apply (hu_ix_origlefin phu). }
  destruct Hex as [k [kgefi H]].
  destruct (munrav_ix_catches_all_nat k) as [j Hj].
  exists j. split.
  - destruct (le_lt_dec i j) as [|jlti]; try assumption.
    apply (ub_lt_succ_lb) in jlti.
    rewrite Heqph in kgefi. lia.
  - apply (between_ix_in_hunrav _ Hj). assumption.
  Qed.

  Theorem hintikka_hunrav : hintikka hunrav.
  Proof.
  constructor.
  - intro i. unfold hunrav.
    destruct (munrav i) as [hu phu].
    simpl. apply (hu_prehin phu).
  - apply hunrav_htk_next.
  - apply hunrav_htk_fulfill.
  Qed.
      
  Theorem root_in_hunrav_0 :
    incl (t_G (l_root Tl)) (hunrav 0).
  Proof.
  unfold hunrav. simpl.
  destruct (make_hu (l_root Tl) 0 eq_refl) as [hu [phu H]].
  simpl. intros phi Hphi. apply (hu_in_htkl_iff phu).
  left. unfold hu_nlb. rewrite H. assumption.
  Qed.

  Theorem model_existence : satable (t_G (l_root Tl)).
  Proof.
  apply satable_subset with (hunrav 0).
  2:{ apply hintikka_satisfied. apply hintikka_hunrav. }
  apply root_in_hunrav_0.
  Qed.

End BuildHintikka.
