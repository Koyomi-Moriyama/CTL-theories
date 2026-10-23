Require Import utils.
Require Import nnf.
Require Import closure.
Require Import semantics.
Require Import seqt.
Require Import ptree.
Require Import proper.

Require Import Arith.
Require Import List.
Require Import ListSet.
Require Import SetoidList.
Import ListNotations.
Require Import Relations.
Require Import Lia.


Set Implicit Arguments.




(* Requires XM (sat_alpha_child) *)
Lemma traverse_up_to_state (M : kripke) (i:nat) : forall x,
  gproper x -> sat M i (t_G x) -> t_uev x <> [] ->
  exists z, sat M i (t_G z) /\ t_isstate z /\
  exists p, path p x z /\ (forall y, In y p -> ~ t_isstate y)
  /\ (forall y, In y p -> sat M i (t_G y)).
Proof.
assert (forall x c,
is_child c x -> sat M i (t_G x) -> ~ t_isstate x ->
(exists z, sat M i (t_G z) /\ t_isstate z /\ exists p, path p c z /\
(forall y, In y p -> ~ t_isstate y) /\ (forall y, In y p -> sat M i (t_G y))) ->
exists z, sat M i (t_G z) /\ t_isstate z /\ exists p, path p x z /\
(forall y, In y p -> ~ t_isstate y) /\ (forall y, In y p -> sat M i (t_G y))) as HIS.
{ intros x c cchx satx nsttx [z [satz [sttz [p [pap [nostt allsat]]]]]].
exists z. repeat split; try assumption.
exists (x :: p). split; try (right with c; assumption). split.
- intros y Hy. destruct Hy as [Hy|Hy];
  [rewrite <- Hy | apply nostt]; assumption.
- intros y Hy. destruct Hy as [Hy|Hy];
  [rewrite <- Hy | apply allsat]; assumption. }
intros x [px gpx] satx uevnnil.
tree_ind_with_eqns x.
- apply HIS with c; try apply IHc; try (assumption||tauto||reflexivity).
  + apply gpx. now left.
  + apply (child_dproper gpx). reflexivity.
  + unfold t_G. rewrite Heqsec. apply sat_alpha_child;
    try assumption. apply (has_prinform px). reflexivity.
  + apply (uev_not_nil_desc (conj px gpx)); [now left | assumption].
- apply HIS with c; try apply IHc; try (assumption||tauto||reflexivity).
  + apply gpx. now left.
  + apply (child_dproper gpx). reflexivity.
  + unfold t_G. rewrite Heqsec.
    pose proof (tbeta1_empty_or_unsat px eq_refl)
    as [Hemp|Hunsat].
    * contradiction.
    * apply unsat_beta2_sat_beta1; try assumption.
      apply (has_prinform px). simpl. reflexivity.
  + apply (uev_not_nil_desc (conj px gpx)); [now left | assumption].
- apply HIS with c; try apply IHc; try (assumption||tauto||reflexivity).
  + apply gpx. now left.
  + apply (child_dproper gpx). reflexivity.
  + unfold t_G. rewrite Heqsec.
    apply unsat_beta1_sat_beta2; try assumption.
    * apply (has_prinform px). simpl. reflexivity.
    * apply (tbeta2_unsat px eq_refl).
  + apply (uev_not_nil_desc (conj px gpx)); [now left | assumption].
- pose proof (satx _ (has_prinform px eq_refl)) as forphi.
  rewrite (force_beta_iff _ Hprin) in forphi.
  destruct forphi as [for1|for2].
  + apply HIS with c1; try apply IHc1; try (assumption||tauto||now left).
    * apply gpx. left. now left.
    * apply (child_dproper gpx). now left.
    * unfold t_G. rewrite Heqsec1. simpl.
      intros psi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
      -- rewrite <- Hpsi. assumption.
      -- apply satx. unfold t_G. apply (in_remove _ _ _ _ Hpsi).
    * apply (uev_not_nil_desc (conj px gpx)); [left; now left | assumption].
  + apply HIS with c2; try apply IHc2; try (assumption||tauto||now right).
    * apply gpx. left. now right.
    * apply (child_dproper gpx). now right.
    * unfold t_G. rewrite Heqsec2. simpl.
      intros psi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
      -- rewrite <- Hpsi. assumption.
      -- apply satx. unfold t_G. apply (in_remove _ _ _ _ Hpsi).
    * apply (uev_not_nil_desc (conj px gpx)); [left; now right | assumption].
- exists (tjump c fs). repeat split;
  try (assumption || apply I || reflexivity || now right).
  exists []. split; try left. simpl. tauto.
- exists (tloop fs). repeat split;
  try (assumption || apply I || reflexivity || now right).
  exists []. split; try left. simpl. tauto.
Qed.

Lemma traverse_up_to_culprit (phi : nnf) : forall x,
  gproper x ->
  t_c x = true -> satable (t_G x) -> In phi (t_uev x) ->
  (forall y, y <=/ x -> t_isloop y -> t_lp y >= t_d x) ->
  exists z, z <=/ x /\ t_c z = true /\ satable (t_G z) /\
  In phi (t_uev z) /\ In phi (t_G z).
Proof.
intros x [px gpx] cox Hsatx Hphiu Hlvs.
pose proof (In_not_nil Hphiu) as Hunnil.
induction x using desc_ptree_induction.
destruct (in_dec nnf_eqdec phi (t_G x)) as [Hphix|Hnphix].
exists x. split; try now right.
repeat (split; try assumption).
rename Hlvs into Hlvsold.
assert (forall y, y <=/ x -> t_isloop y -> t_lp y >= S (t_d x))
as Hlvs.
{ intros y ylex yisl.
destruct (le_lt_eq_dec _ _ (Hlvsold y ylex yisl)) as [dltlp|deqlp].
- assumption.
- contradict Hnphix.
  apply (tloop_uev_incl_anc (conj px gpx) ylex); try assumption.
  destruct ylex as [yltx|yeqx].
  + apply (uev_monotone (conj px gpx) yltx). assumption.
  + rewrite yeqx. assumption. }
clear Hlvsold. destruct Hsatx as [M [i Hsatx]].
destruct (traverse_up_to_state (conj px gpx) Hsatx Hunnil) as
[y [Hsaty [Hstty [p [pap [Hp _]]]]]].
pose proof (path_no_state_same_d (conj px gpx) pap Hp) as Hdeq.
pose proof (path_end_desceq_start pap) as ylex.
pose proof (desceq_proper (conj px gpx) ylex) as py.
pose proof (desceq_dproper gpx ylex) as gpy.
tree_dest_with_eqns y.
- assert (c </ x) as cltx.
  { apply desc_desceq_desc with y; rewrite Heqy; try assumption. now left. }
  destruct (IH c) as [z [zlec H]].
 -- assumption.
 -- apply (gpx _ cltx).
 -- apply (desc_dproper gpx cltx).
 -- unfold t_c. rewrite Heqsec. reflexivity.
 -- exists M, (S i). unfold t_G. rewrite Heqsec.
    apply sat_jump_child. assumption.
 -- apply (uev_monotone (conj px gpx) cltx). assumption.
 -- intros z zlec. unfold t_d. rewrite Heqsec.
    simpl. unfold t_d in Hdeq. rewrite Hdeq.
    apply Hlvs. left. apply desceq_desc_desc with c; assumption.
 -- apply (uev_not_nil_desc (conj px gpx)); assumption.
 -- exists z. split; try assumption. left.
    apply desceq_desc_desc with c; assumption.
- assert (t_uev y <> []) as Huynnil.
  { rewrite Heqy. destruct ylex as [yltx|yeqx].
  - apply (uev_not_nil_desc (conj px gpx)); assumption.
  - rewrite yeqx. assumption. } rewrite Heqy in Huynnil.
  pose proof (lp_le_depth (conj py gpy) Huynnil) as Hctr.
  contradict Hctr. apply Arith_prebase.lt_not_le_stt.
  unfold lt. rewrite Hdeq. apply Hlvs; assumption.
Qed.


Lemma after_traverse_unful (M : kripke) (i:nat) :
  forall x z p phi psi, gproper x -> path p x z ->
  In (unt phi psi) (t_G x) -> In (unt phi psi) (t_uev x) ->
  t_isstate z -> (forall y, In y p -> ~ t_isstate y) ->
  (forall y, In y p -> sat M i (t_G y)) ->
  ~ force M i psi /\ In (next (unt phi psi)) (t_G z).
Proof.
intros x z p phi psi [px gpx] pap H H0 H1 nostt allsat.
pose proof (path_end_desceq_start pap) as zlex.
pose proof (I : nnf_isbeta (unt phi psi)) as bunt.
pose proof (beta_before_state _ (conj px gpx) bunt H pap H1) as H2.
destruct H2 as [y [Hyp [Hbetay Hpfy]]].
pose proof (in_path_desceq y pap Hyp) as H2.
pose proof (desceq_proper (conj px gpx) H2) as py.
pose proof (beta2_only_uev (conj px gpx) H0 H2 Hbetay Hpfy) as H3.
tree_dest_with_eqns y.
rename phi0 into xi. rename c into yc. rename Heqsec into Heqseyc.
assert (is_child yc y) as ycchy.
{ rewrite Heqy. now simpl. }
injection Hpfy. intro Hxiunt.
pose proof (nostt _ Hyp) as nstty. pose proof (allsat _ Hyp) as saty.
pose proof bunt as bxi. rewrite <- Hxiunt in bxi.
pose proof (tbeta2_unsat py eq_refl) as H4.
unfold t_G in saty. split.
- rewrite Hxiunt in H4. apply (unsat_beta1_not_force_psi saty H4).
- set (chi := (and phi (next (unt phi psi)))).
  assert (In chi (t_G yc)) as H5.
  { unfold t_G. rewrite Heqseyc. simpl. left.
  simpl. rewrite Hxiunt. reflexivity. }
  destruct (cut_path pap _ Hyp) as [p0 [piep0 p0inp]].
  inversion piep0.
  { rewrite <- H8 in H1. contradiction. }
  rewrite H9 in H8. clear x0 H9 z0 H10.
  simpl in H6. rewrite H6 in H7. clear y0 H6.
  rename H7 into piep1. rename H8 into Heqp0. rewrite Heqy in ycchy.
  pose proof (desc_desceq_desc (t_step ptree is_child yc _ ycchy) H2)
  as ycltx.
  pose proof (gpx _ ycltx) as pyc.
  assert (dproper yc) as gpyc.
  { intros u ultyc. apply gpx. right with yc; assumption. }
  pose proof (I : nnf_isalpha chi) as achi.
  destruct (alpha_before_state _ (conj pyc gpyc) achi H5 piep1 H1)
  as [y1 [y1p1 [ay1 pfy1]]].
  destruct y1 as [y2 y2fs chi'| | | | |] eqn:Heqy1; try contradiction.
  simpl in pfy1. injection pfy1. intro Heqchi'.
  rewrite <- Heqy1 in y1p1. rewrite Heqchi' in Heqy1.
  clear chi' ay1 pfy1 Heqchi'. assert (y1 </ x) as y1ltx.
  { apply desceq_desc_desc with yc; try assumption.
  apply (in_path_desceq _ piep1 y1p1). }
  pose proof (gpx _ y1ltx) as py1.
  pose proof (downward_ok py1) as Heqsey2. rewrite Heqy1 in Heqsey2.
  assert (In (next (unt phi psi)) (t_G y2)) as H6.
  { unfold t_G. rewrite Heqsey2. simpl. right. now left. }
  destruct (cut_path piep1 _ y1p1) as [p2 [piep2 p2inp1]].
  inversion piep2.
  { rewrite H9 in Heqy1. rewrite Heqy1 in H1. contradiction. }
  rewrite H10 in H9. clear x0 z0 H10 H11.
  rewrite Heqy1 in H7. simpl in H7. rewrite H7 in H8.
  clear y0 H7. rename H8 into piep3. rename H9 into Heqp2.
  assert (y2 </ x) as y2ltx.
  { right with y1; try assumption. left.
  rewrite Heqy1. reflexivity. }
  pose proof (gpx _ y2ltx) as py2.
  pose proof (desc_dproper gpx y2ltx) as gpy2.
  apply (next_preserved (conj py2 gpy2) _ H6 piep3).
  intros y0 Hy0. apply (nostt y0).
  apply p0inp. rewrite <- Heqp0. right. apply p2inp1.
  rewrite <- Heqp2. now right.
Qed.



Definition unfulfillable_ev (x : ptree) :
  {t_uev x <> [] /\ t_lp x >= t_d x} +
  {t_uev x = [] \/ t_lp x < t_d x}.
Proof.
destruct (t_uev x) as [|phi l].
- right. now left.
- destruct (le_lt_dec (t_d x) (t_lp x)) as [Hle|Hlt].
  + left. split; [discriminate|tauto].
  + right. now right.
Defined.


(* Requires XM *)
Definition jump_rule [ss : rdoseqt] (sc : state_conditions (proj1_sig ss))
  (nb : not_blocked_seqt (proj1_sig ss)) (nu : status (jump_child (proj1_sig ss))) :
  status (proj1_sig ss).
Proof.
refine (
  match nu with
  | closed Hunsat => closed (unsat_jump_child Hunsat)
  | open (existT _ x0 i) =>
      match unfulfillable_ev x0 with
      | left unful   => closed _
      | right nunful => open _
      end
  end).

{
destruct i as [fulx0 Hx0].
destruct ss as [s ps]. simpl in sc, nb, nu, Hx0 |- *.
destruct Hx0 as [[px0 gpx0] Heqx0se].
destruct unful as [nnil lpged].
apply unsat_jump_child.
rewrite <- Heqx0se. intros M' i' Hsat.
fold (t_uev x0) in nnil. destruct (t_uev x0) as [|xi V] eqn:Hequ0
; try contradiction.
assert (In xi (t_uev x0)) as Hxiu0.
{ rewrite Hequ0. now left. }
clear Hequ0 nnil V.
pose proof (unt_only_uev (conj px0 gpx0) xi Hxiu0) as [phi [psi Heqxi]].
pose proof (In_not_nil Hxiu0) as Hu0nnil.
assert (t_c x0 = true) as cox0.
{ unfold t_c. rewrite Heqx0se. reflexivity. }

destruct (@traverse_up_to_culprit xi x0) as
[x1 [x1lex0 [cox1 [[M [i Hsatx1]] [Hxiu1 HxiG]]]]]; try (unfold gproper; tauto).
{ exists M', i'. assumption. }
{ intros y ylex0 yisl. destruct ylex0 as [yltx0|yeqx0].
- eapply Nat.le_trans; try apply lpged. apply lp_monotone; unfold gproper; tauto.
- rewrite yeqx0. assumption. }
pose proof (desceq_proper (conj px0 gpx0) x1lex0) as px1.
pose proof (desceq_dproper gpx0 x1lex0) as gpx1.
pose proof (In_not_nil Hxiu1) as Hu1nnil.

assert (forall n, n >= i -> exists x, x <=/ x0 /\ sat M n (t_G x) /\ t_isstate x
  /\ ~ force M n psi /\ In (next (unt phi psi)) (t_G x)) as alln.
{
apply (induction_from_rank i).
{
destruct (traverse_up_to_state (conj px1 gpx1) Hsatx1 Hu1nnil)
as [z [satz [statez [p [pap [nostt allsat]]]]]].
pose proof (path_end_desceq_start pap) as zlex1.
exists z. split; try apply (desceq_trans zlex1 x1lex0).
split; try assumption. split; try assumption.
rewrite Heqxi in Hxiu1, HxiG.
apply after_traverse_unful with x1 p; try assumption;
unfold gproper; tauto.
}
{
intros n ngei IHn.
destruct IHn as [x [xlex0 [satx [statex [nforn nextinx]]]]].
pose proof (desceq_proper (conj px0 gpx0) xlex0) as px.
tree_dest_with_eqns x.
- rename c into xc. assert (xc </ x0) as xcltx0.
  { apply desc_desceq_desc with x; rewrite Heqx; try assumption.
  left. simpl. reflexivity. }
  pose proof (gpx0 xc xcltx0) as pxc.
  pose proof (desc_dproper gpx0 xcltx0) as gpxc.
  pose proof (@traverse_up_to_state M (S n) xc (conj pxc gpxc))
  as [z [satz [statez [p [pap [nostt allsat]]]]]].
  + unfold t_G. fold (t_dose xc). rewrite Heqsec.
    apply sat_jump_child.
    unfold t_dose. fold (t_G x). assumption.
  + apply (uev_not_nil_desc (conj px0 gpx0)); assumption.
  + pose proof (path_end_desceq_start pap) as zlexc.
    exists z. split.
    { left. apply desceq_desc_desc with xc; assumption. }
    split; try assumption. split; try assumption.
    apply after_traverse_unful with xc p; try assumption;
    try (unfold gproper; tauto).
    * unfold t_G. rewrite Heqsec. simpl. apply in_next_in_unnext.
      fold (t_G x). assumption.
    * apply (uev_monotone (conj px0 gpx0)); try assumption. rewrite <- Heqxi.
      assumption.
- clear Heqset. pose proof (desceq_dproper gpx0 xlex0) as gpx.
  assert (t_uev x <> []) as Huxnnil.
  { destruct xlex0 as [xltx0|xeqx0].
  - apply (uev_not_nil_desc (conj px0 gpx0)); try rewrite Heqx; assumption.
  - rewrite Heqx, xeqx0. assumption. }
  apply (Nat.le_antisymm _ _ (lp_le_depth (conj px0 gpx0) Hu0nnil)) in lpged.
  rename lpged into lpeqd.
  destruct xlex0 as [xltx0|xeqx0].
  { pose proof (lp_monotone (conj px0 gpx0) xltx0) as lp0lelp.
  destruct (le_lt_eq_dec _ _ lp0lelp) as [lp0ltlp|lp0eqlp].
  { rewrite lpeqd in lp0ltlp. rewrite Heqx in Huxnnil.
  pose proof (lp_le_depth (conj px gpx) Huxnnil) as lpxled.
  destruct (fulx0 _ _ xltx0 (conj lp0ltlp lpxled))
  as [xc [Hxc [Hxc0 Hxc1]]].
  destruct Hxc as [xlexc xcltx0].
  pose proof (gpx0 xc xcltx0) as pxc.
  pose proof (desc_dproper gpx0 xcltx0) as gpxc.
  pose proof (tloop_anc_eqset (conj pxc gpxc) xlexc
  (eq_ind_r _ I Heqx) Hxc1 Hxc0) as Heqset.
  pose proof (@traverse_up_to_state M (S n) xc (conj pxc gpxc))
  as [z [satz [statez [p [pap [nostt allsat]]]]]].
  + rewrite (sat_eqset _ Heqset).
    assert (unnext (t_G x) = s_G (jump_child (t_dose x))) as Huneqjc.
    { simpl. unfold t_G. reflexivity. } rewrite Heqx in Huneqjc.
    rewrite Huneqjc. apply sat_jump_child. assumption.
  + apply (uev_not_nil_desc (conj px0 gpx0)); assumption.
  + pose proof (path_end_desceq_start pap) as zlexc.
    exists z. split. { left. apply desceq_desc_desc with xc; assumption. }
    split; try assumption. split; try assumption.
    apply after_traverse_unful with xc p; try assumption;
    try (unfold gproper; tauto).
    * rewrite (eqset_in_iff Heqset).
      apply in_next_in_unnext. assumption.
    * apply (uev_monotone (conj px0 gpx0)); try assumption. rewrite <- Heqxi.
      assumption.
  }
  rewrite lpeqd in lp0eqlp.
  pose proof (tloop_anc_eqset (conj px0 gpx0) (or_introl xltx0)
  (eq_ind_r _ I Heqx) cox0 lp0eqlp) as Heqset.
  pose proof (@traverse_up_to_state M (S n) x0)
  as [z [satz [statez [p [pap [nostt allsat]]]]]]; try assumption;
  try (unfold gproper; tauto).
  + rewrite (sat_eqset _ Heqset).
    assert (unnext (t_G x) = s_G (jump_child (t_dose x))) as Huneqjc.
    { simpl. unfold t_G. reflexivity. } rewrite Heqx in Huneqjc.
    rewrite Huneqjc. apply sat_jump_child. assumption.
  + pose proof (path_end_desceq_start pap) as zlexc.
    exists z. split; try assumption. split; try assumption.
    split; try assumption.
    apply after_traverse_unful with x0 p; try assumption;
    try (unfold gproper; tauto).
    * rewrite (eqset_in_iff Heqset).
      apply in_next_in_unnext. assumption.
    * rewrite <- Heqxi. assumption.
  }
  rewrite xeqx0 in Heqx. assert (t_isloop x0) as lpx0. { rewrite <- xeqx0. tauto. }
  pose proof (tloop_anc_eqset (conj px0 gpx0) (or_intror eq_refl)
                lpx0 cox0 (eq_sym lpeqd)) as Heqset.
  pose proof (@traverse_up_to_state M (S n) x0 (conj px0 gpx0))
  as [z [satz [statez [p [pap [nostt allsat]]]]]]; try assumption.
  + rewrite (sat_eqset _ Heqset).
    assert (unnext (t_G x0) = s_G (jump_child (t_dose x0))) as Huneqjc.
    { simpl. unfold t_G. reflexivity. }
    rewrite Huneqjc. apply sat_jump_child. fold (t_G x0).
    rewrite <- xeqx0. assumption.
  + pose proof (path_end_desceq_start pap) as zlexc.
    exists z. split; try assumption. split; try assumption.
    split; try assumption.
    apply after_traverse_unful with x0 p; try assumption;
    try (unfold gproper; tauto).
    * rewrite (eqset_in_iff Heqset).
      apply in_next_in_unnext. rewrite <- xeqx0. assumption.
    * rewrite <- Heqxi. assumption.
}
}

pose proof (Hsatx1 _ HxiG) as forxi.
rewrite Heqxi in forxi. simpl in forxi.
destruct forxi as [k [ilek [forpsi allj]]].
contradict forpsi. destruct (alln k ilek). tauto.
}


destruct i as [fulx0 Hx0].
destruct ss as [s ps]. simpl in Hx0, sc, nb, nu |- *.
destruct Hx0 as [[px0 gpx0] Heqsex0].
set (xup := {|
  s_uev := t_uev x0;
  s_lp  := t_lp x0
|}).
set (xfs := (s, xup)).
set (x := tjump x0 xfs).
assert (t_d x0 = S (t_d x)) as dx0Sdx.
{ unfold t_d. rewrite Heqsex0. simpl. unfold t_dose.
simpl. reflexivity. }

assert (filler x) as fulx.
{ intros z n zltx Hn.
destruct (desc_child_or_child_dec zltx) as [dch|ch].
- destruct dch as [y [ychx zlty]]. simpl in ychx. rewrite ychx in zlty.
  rename zlty into zltx0. clear y ychx. destruct Hn as [Hnge Hnle].
  destruct (le_lt_eq_dec _ _ Hnge) as [Sxltn|Sxeqn].
  + rewrite <- dx0Sdx in Sxltn.
    destruct (fulx0 z n zltx0 (conj Sxltn Hnle)) as
      [y [zyx0 [dyeqn cytrue]]].
    destruct zyx0 as [zley yltx0].
    exists y. split; try tauto. split; try tauto.
    right with x0; try assumption.
    left. simpl. reflexivity.
  + exists x0. split; try split; try (now left).
    * rewrite <- Sxeqn. assumption.
    * unfold t_c. rewrite Heqsex0. simpl. reflexivity.
- exists x0. simpl in ch. rewrite ch, dx0Sdx in Hn.
  rewrite ch in zltx. split; try split; try assumption.
  + now right.
  + lia.
  + unfold t_c. rewrite Heqsex0. simpl. reflexivity.
}

exists x, fulx.
split. split.
{ constructor; try (discriminate || contradiction || simpl; tauto).
intros z zltx coz.
destruct (desc_child_or_child_dec zltx) as [[y [ychx zlty]]|zchx].
- rewrite ychx in zlty. apply (no_unful_case px0 zlty coz).
- rewrite zchx. assumption.
} 

{ unfold dproper. intros y Hdes. apply clos_trans_tn1 in Hdes.
inversion Hdes.
- simpl in H. rewrite H. assumption.
- simpl in H. rewrite H in H0. apply clos_tn1_trans in H0.
  apply gpx0. assumption.
}
simpl. reflexivity.
Defined.
