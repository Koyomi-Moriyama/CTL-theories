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


(* ALPHA RULE *)

Definition alpha_rule [phi] (aphi : nnf_isalpha phi) [ss : rdoseqt]
  (Hin : In phi (s_G (proj1_sig ss)))
  (nu : status (alpha_child phi (proj1_sig ss))) : status (proj1_sig ss).
Proof.
refine (
  match nu with
  | open i => open _
  | closed unsatable => closed (unsat_alpha_child aphi Hin unsatable)
  end).
destruct i as [c [fusc Hc]].
destruct ss as [s ps]. simpl in Hin, nu, Hc |- *.
destruct Hc as [[pc gpc] Heqsec].
set (xfs := (s, snd (t_fseqt c))).
set (x := talpha c xfs phi).

assert (filler x) as fulx.
{ intros z n zltx Hn.
assert (t_d x = t_d c) as dxeqdc.
{ unfold t_d. rewrite Heqsec. simpl. unfold t_dose. simpl. reflexivity. }
destruct (desc_child_or_child_dec zltx) as [dch|ch].
- destruct dch as [y [ychx zlty]]. simpl in ychx. rewrite ychx in zlty.
  rename zlty into zltc. clear y ychx. 
  rewrite dxeqdc in Hn. destruct (fusc z n zltc Hn) as [y [zyc [dyeqn cytrue]]].
  destruct zyc as [zley yltc].
  exists y. split; try tauto. split; try tauto. right with c; try assumption.
  left. simpl. reflexivity.
- simpl in ch. rewrite ch, dxeqdc in Hn. lia. }

exists x, fulx.

split. split.
{ constructor; try (discriminate || contradiction || assumption).
- intros psi H. simpl in H. injection H. intro Heqpsi.
  rewrite <- Heqpsi. unfold t_G. assumption.
- split; reflexivity.
- intros z zltx coz.
  destruct (desc_child_or_child_dec zltx) as [[y [ychx zlty]]|zchx].
  + rewrite ychx in zlty. apply (no_unful_case pc zlty coz).
  + rewrite zchx in coz. unfold t_c in coz.
    rewrite Heqsec in coz. simpl in coz. discriminate.
} 

{ unfold dproper. intros y Hdes. apply clos_trans_tn1 in Hdes.
inversion Hdes.
- simpl in H. rewrite H. assumption.
- simpl in H. rewrite H in H0. apply clos_tn1_trans in H0.
  apply gpc. assumption.
}
simpl. reflexivity.
Defined.



(* BETA RULES *)

Definition beta1_rule [phi] (bphi : nnf_isbeta phi) [ss : rdoseqt]
  (Hin : In phi (s_G (proj1_sig ss))) (c : ptree)
  (i : t_info c (beta1_child phi (proj1_sig ss)))
  (Halleq : forall psi, In psi (t_uev c) -> psi = phi) : status (proj1_sig ss).
Proof.
destruct i as [fulc Hc].
destruct ss as [s ps]. simpl in Hin, Hc |- *.
destruct Hc as [[pc gpc] Heqsec].
set (xup := {|
  s_uev := [];
  s_lp  := t_lp c
|}).
set (xfs := (s, xup)).
set (x := tbeta1 c xfs phi).

assert (filler x) as fulx.
{ intros z n zltx Hn.
assert (t_d x = t_d c) as dxeqdc.
{ unfold t_d. rewrite Heqsec. simpl. unfold t_dose.
simpl. reflexivity. }
destruct (desc_child_or_child_dec zltx) as [dch|ch].
- destruct dch as [y [ychx zlty]]. simpl in ychx.
  rewrite ychx in zlty. rename zlty into zltc. clear y ychx. 
  rewrite dxeqdc in Hn.
  destruct (fulc z n zltc Hn) as [y [zyc [dyeqn cytrue]]].
  destruct zyc as [zley yltc].
  exists y. split; try tauto. split; try tauto.
  right with c; try assumption.
  left. simpl. reflexivity.
- simpl in ch. rewrite ch, dxeqdc in Hn. lia. }

apply open. exists x, fulx.
split. split.
{ constructor; try (discriminate || contradiction || assumption).
- intros psi H. simpl in H. injection H. intro Heqpsi.
  rewrite <- Heqpsi. unfold t_G. assumption.
- split.
  + rewrite (remove_all nnf_eqdec); try assumption. reflexivity.
  + reflexivity.
- intros c' xfs' phib' H. left. unfold t_uev, t_upse.
  simpl. reflexivity.
- intros z zltx coz.
  destruct (desc_child_or_child_dec zltx) as [[y [ychx zlty]]|zchx].
  + rewrite ychx in zlty. apply (no_unful_case pc zlty coz).
  + rewrite zchx in coz. unfold t_c in coz.
    rewrite Heqsec in coz. simpl in coz. discriminate.
} 

{ unfold dproper. intros y Hdes. apply clos_trans_tn1 in Hdes.
inversion Hdes.
- simpl in H. rewrite H. assumption.
- simpl in H. rewrite H in H0. apply clos_tn1_trans in H0.
  apply gpc. assumption.
}
reflexivity.
Defined.



Definition beta_rule [phi : nnf] (bphi : nnf_isbeta phi) [ss : rdoseqt]
  (Hin : In phi (s_G (proj1_sig ss))) (c1 : ptree)
  (i1 : t_info c1 (beta1_child phi (proj1_sig ss)))
  (Hexneq : exists psi, In psi (t_uev c1) /\ psi <> phi)
  (nu2 : status (beta2_child phi (proj1_sig ss))) : status (proj1_sig ss).
Proof.
refine ((
  match phi as phi' return phi = phi' -> status (proj1_sig ss) with
  | unt _ _ => let uev1' := remove nnf_eqdec phi (t_uev c1) in
      match nu2 with
      | open (existT _ c2 i2) => let xup :=
          {|
            s_uev := inter_nnf uev1' (t_uev c2);
            s_lp  := min (t_lp c1) (t_lp c2)
          |}
          in fun Heqphi => open _
      | closed Hunsat2 => let xup :=
          {|
            s_uev := uev1';
            s_lp  := t_lp c1
          |}
          in fun Heqphi => open _
      end
  | _ =>
      match nu2 with
      | open (existT _ c2 i2) => let xup :=
          {|
            s_uev := inter_nnf (t_uev c1) (t_uev c2);
            s_lp  := min (t_lp c1) (t_lp c2)
          |}
          in fun Heqphi => open _
      | closed Hunsat2 => let xup :=
          {|
            s_uev := t_uev c1;
            s_lp  := t_lp c1
          |}
          in fun Heqphi => open _
      end
  end) eq_refl).

all: try (pose proof bphi as Hctr;
rewrite Heqphi in Hctr; contradiction).

all: rename n into phi1; rename n0 into phi2.

all: destruct i1 as [fulc1 Hc1];
destruct Hc1 as [[pc1 gpc1] Heqsec1];
destruct ss as [s ps].

all: set (xfs := (s, xup)).

(* or open *)
{ destruct i2 as [fulc2 Hc2]. simpl in Hin, Heqsec1, Hc2 |- *.
destruct Hc2 as [[pc2 gpc2] Heqsec2].
set (x := talt c1 c2 xfs phi).

assert (filler x) as fulx.
{ intros z n zltx Hn.
assert (t_d x = t_d c1) as dxeqdc1.
{ unfold t_d. rewrite Heqsec1. simpl. unfold t_dose.
simpl. reflexivity. }
assert (t_d x = t_d c2) as dxeqdc2.
{ unfold t_d. rewrite Heqsec2. simpl. unfold t_dose.
simpl. reflexivity. }
destruct (desc_dec z c1) as [zltc1|nzltc1];
[idtac|destruct (desc_dec z c2) as [zltc2|nzltc2]].
- rewrite dxeqdc1 in Hn.
  destruct (fulc1 z n zltc1 Hn) as [y [zyc1 [dyeqn cytrue]]].
  exists y. split; try split; try assumption; try tauto.
  right with c1; try tauto. left. simpl. now left.
- rewrite dxeqdc2 in Hn.
  destruct (fulc2 z n zltc2 Hn) as [y [zyc2 [dyeqn cytrue]]].
  exists y. split; try split; try assumption; try tauto.
  right with c2; try tauto. left. simpl. now right.
- assert (is_child z x) as zchx.
  { apply not_desc_child_desc; try assumption.
  intros y Hy. destruct Hy as [Hy|Hy]; rewrite Hy; assumption. }
  destruct (ptree_eqdec z c1) as [zeqc1|zneqc1];
  [idtac|destruct (ptree_eqdec z c2) as [zeqc2|zneqc2]].
  + rewrite zeqc1, dxeqdc1 in Hn. lia.
  + rewrite zeqc2, dxeqdc2 in Hn. lia.
  + contradict zchx. intro Hctr.
    destruct Hctr as [Hctr|Hctr]; contradiction. }

assert (t_d x = t_d c1) as dxeqdc1.
{ unfold t_d. rewrite Heqsec1. unfold t_dose.
simpl. reflexivity. }

assert (t_lp x <= t_lp c1) as lpxlelpc1.
{ unfold t_lp at 1, t_upse. simpl. apply Nat.le_min_l. }
assert (t_lp x <= t_lp c2) as lpxlelpc2.
{ unfold t_lp at 1, t_upse. simpl. apply Nat.le_min_r. }

assert (forall xi : nnf,
In xi (t_uev x) -> exists phi psi : nnf, xi = unt phi psi) as untuevx.
{ intros xi Hxi. unfold t_uev, t_upse in Hxi. simpl in Hxi.
apply set_inter_elim1 in Hxi. apply (unt_only_uev (conj pc1 gpc1) _ Hxi). }

assert (incl (t_uev x) (t_uev c1)) as inclxc1.
{ unfold t_uev at 1, t_upse. simpl.
intros psi Hpsi. apply (set_inter_elim1 _ _ _ _ Hpsi). }
assert (incl (t_uev x) (t_uev c2)) as inclxc2.
{ unfold t_uev at 1, t_upse. simpl.
intros psi Hpsi. apply (set_inter_elim2 _ _ _ _ Hpsi). }

exists x, fulx.
split. split.
{ constructor; try (discriminate || contradiction || assumption).
- intros psi H. simpl in H. injection H. intro Heqpsi.
  rewrite <- Heqpsi. unfold t_G. assumption.
- split; unfold t_dose at 2; simpl; assumption.
- split.
  + rewrite (notin_remove nnf_eqdec); try reflexivity. intro Hctr.
    destruct (unt_only_uev (conj pc1 gpc1) _ Hctr) as [psi1 [psi2 Heq]].
    rewrite Heqphi in Heq. discriminate.
  + reflexivity.
- intros z zltx coz.
  destruct (desc_child_or_child_dec zltx) as [[y [ychx zlty]]|zchx].
  + destruct ychx as [yeqc1|yeqc2].
    * rewrite yeqc1 in zlty. apply (no_unful_case pc1 zlty coz).
    * rewrite yeqc2 in zlty. apply (no_unful_case pc2 zlty coz).
  + destruct zchx as [zeqc1|zeqc2].
    * rewrite zeqc1 in coz. unfold t_c in coz.
      rewrite Heqsec1 in coz. simpl in coz. discriminate.
    * rewrite zeqc2 in coz. unfold t_c in coz.
      rewrite Heqsec2 in coz. simpl in coz. discriminate.
} 

{ unfold dproper. intros y Hdes. apply clos_trans_tn1 in Hdes.
inversion Hdes.
- simpl in H. destruct H as [H|H]; rewrite H; assumption.
- simpl in H. destruct H as [H|H].
  + rewrite H in H0. apply clos_tn1_trans in H0.
    apply gpc1. assumption.
  + rewrite H in H0. apply clos_tn1_trans in H0.
    apply gpc2. assumption.
}
reflexivity.
}

(* or closed *)
{
simpl in Hin, Heqsec1, Hunsat2 |- *.
set (x := tbeta1 c1 xfs phi).

assert (filler x) as fulx.
{ intros z n zltx Hn.
assert (t_d x = t_d c1) as dxeqdc.
{ unfold t_d. rewrite Heqsec1. simpl.
unfold t_dose. simpl. reflexivity. }
destruct (desc_child_or_child_dec zltx) as [dch|ch].
- destruct dch as [y [ychx zlty]]. simpl in ychx. rewrite ychx in zlty.
  rename zlty into zltc. clear y ychx. 
  rewrite dxeqdc in Hn.
  destruct (fulc1 z n zltc Hn) as [y [zyc [dyeqn cytrue]]].
  destruct zyc as [zley yltc].
  exists y. split; try tauto. split; try tauto.
  right with c1; try assumption.
  left. simpl. reflexivity.
- simpl in ch. rewrite ch, dxeqdc in Hn. lia. }

assert (t_lp x = t_lp c1) as lpxeqc.
{ unfold t_lp at 1, t_upse. simpl. reflexivity. }

assert (t_d x = t_d c1) as dxeqc.
{ unfold t_d. rewrite Heqsec1. unfold t_dose.
simpl. reflexivity. }

assert (t_uev x = t_uev c1) as uevxeqc.
{ unfold t_uev at 1, t_upse. simpl. reflexivity. }

assert (forall xi : nnf,
In xi (t_uev x) -> exists phi psi : nnf, xi = unt phi psi) as untuevx.
{ rewrite uevxeqc. apply (unt_only_uev (conj pc1 gpc1)). }

exists x, fulx.
split. split.
{ constructor; try (discriminate || contradiction || assumption).
- intros psi H. simpl in H. injection H. intro Heqpsi. rewrite <- Heqpsi.
  unfold t_G. assumption.
- split.
  + rewrite (notin_remove nnf_eqdec); try reflexivity.
    intro Hctr. destruct (unt_only_uev (conj pc1 gpc1) _ Hctr) as [psi1 [psi2 Heq]].
    rewrite Heqphi in Heq. discriminate.
  + reflexivity.
- intros c' xfs' phi' H. injection H.
  intros Heqphi' Heqxfs Heqc. right. rewrite <- Heqphi'. assumption.
- intros z zltx coz.
  destruct (desc_child_or_child_dec zltx) as [[y [ychx zlty]]|zchx].
  + rewrite ychx in zlty. apply (no_unful_case pc1 zlty coz).
  + rewrite zchx in coz. unfold t_c in coz.
    rewrite Heqsec1 in coz. simpl in coz. discriminate.
} 

{ unfold dproper. intros y Hdes. apply clos_trans_tn1 in Hdes.
inversion Hdes.
- simpl in H. rewrite H. assumption.
- simpl in H. rewrite H in H0. apply clos_tn1_trans in H0.
  apply gpc1. assumption.
}
reflexivity.
}

(* unt open *)
{ destruct i2 as [fulc2 Hc2]. simpl in Hin, Heqsec1, Hc2 |- *.
destruct Hc2 as [[pc2 gpc2] Heqsec2].
set (x := talt c1 c2 xfs phi).

assert (filler x) as fulx.
{ intros z n zltx Hn.
assert (t_d x = t_d c1) as dxeqdc1.
{ unfold t_d. rewrite Heqsec1. simpl. unfold t_dose.
simpl. reflexivity. }
assert (t_d x = t_d c2) as dxeqdc2.
{ unfold t_d. rewrite Heqsec2. simpl. unfold t_dose.
simpl. reflexivity. }
destruct (desc_dec z c1) as [zltc1|nzltc1];
[idtac|destruct (desc_dec z c2) as [zltc2|nzltc2]].
- rewrite dxeqdc1 in Hn.
  destruct (fulc1 z n zltc1 Hn) as [y [zyc1 [dyeqn cytrue]]].
  exists y. split; try split; try assumption; try tauto.
  right with c1; try tauto. left. simpl. now left.
- rewrite dxeqdc2 in Hn.
  destruct (fulc2 z n zltc2 Hn) as [y [zyc2 [dyeqn cytrue]]].
  exists y. split; try split; try assumption; try tauto.
  right with c2; try tauto. left. simpl. now right.
- assert (is_child z x) as zchx.
  { apply not_desc_child_desc; try assumption.
  intros y Hy. destruct Hy as [Hy|Hy]; rewrite Hy; assumption. }
  destruct (ptree_eqdec z c1) as [zeqc1|zneqc1];
  [idtac|destruct (ptree_eqdec z c2) as [zeqc2|zneqc2]].
  + rewrite zeqc1, dxeqdc1 in Hn. lia.
  + rewrite zeqc2, dxeqdc2 in Hn. lia.
  + contradict zchx. intro Hctr.
    destruct Hctr as [Hctr|Hctr]; contradiction. }

assert (t_d x = t_d c1) as dxeqdc1.
{ unfold t_d. rewrite Heqsec1. unfold t_dose.
simpl. reflexivity. }

assert (t_lp x <= t_lp c1) as lpxlelpc1.
{ unfold t_lp at 1, t_upse. simpl. apply Nat.le_min_l. }
assert (t_lp x <= t_lp c2) as lpxlelpc2.
{ unfold t_lp at 1, t_upse. simpl. apply Nat.le_min_r. }

assert (incl uev1' (t_uev c1)) as uev1'incl.
{ intros xi Hxi. apply (proj1 (in_remove _ _ _ _ Hxi)). }

assert (forall xi : nnf,
In xi (t_uev x) -> exists phi psi : nnf, xi = unt phi psi) as untuevx.
{ intros xi Hxi. unfold t_uev, t_upse in Hxi. simpl in Hxi.
apply set_inter_elim1 in Hxi. apply (unt_only_uev (conj pc1 gpc1)).
apply (uev1'incl _ Hxi). }

assert (incl (t_uev x) (t_uev c1)) as inclxc1.
{ unfold t_uev at 1, t_upse. simpl.
intros psi Hpsi. apply uev1'incl.
apply (set_inter_elim1 _ _ _ _ Hpsi). }
assert (incl (t_uev x) (t_uev c2)) as inclxc2.
{ unfold t_uev at 1, t_upse. simpl.
intros psi Hpsi. apply (set_inter_elim2 _ _ _ _ Hpsi). }

exists x, fulx.
split. split.
{ constructor; try (discriminate || contradiction || assumption).
- intros psi H. simpl in H. injection H. intro Heqpsi.
  rewrite <- Heqpsi. unfold t_G. assumption.
- simpl. split; unfold t_dose at 2; simpl; assumption.
- split; reflexivity.
- intros z zltx coz.
  destruct (desc_child_or_child_dec zltx) as [[y [ychx zlty]]|zchx].
  + destruct ychx as [yeqc1|yeqc2].
    * rewrite yeqc1 in zlty. apply (no_unful_case pc1 zlty coz).
    * rewrite yeqc2 in zlty. apply (no_unful_case pc2 zlty coz).
  + destruct zchx as [zeqc1|zeqc2].
    * rewrite zeqc1 in coz. unfold t_c in coz.
      rewrite Heqsec1 in coz. simpl in coz. discriminate.
    * rewrite zeqc2 in coz. unfold t_c in coz.
      rewrite Heqsec2 in coz. simpl in coz. discriminate.
} 

{ unfold dproper. intros y Hdes. apply clos_trans_tn1 in Hdes.
inversion Hdes.
- simpl in H. destruct H as [H|H]; rewrite H; assumption.
- simpl in H. destruct H as [H|H].
  + rewrite H in H0. apply clos_tn1_trans in H0.
    apply gpc1. assumption.
  + rewrite H in H0. apply clos_tn1_trans in H0.
    apply gpc2. assumption.
}
reflexivity.
}

(* unt closed *)
{
simpl in Hin, Heqsec1, Hunsat2 |- *.
set (x := tbeta1 c1 xfs phi).

assert (filler x) as fulx.
{ intros z n zltx Hn.
assert (t_d x = t_d c1) as dxeqdc.
{ unfold t_d. rewrite Heqsec1. simpl.
unfold t_dose. simpl. reflexivity. }
destruct (desc_child_or_child_dec zltx) as [dch|ch].
- destruct dch as [y [ychx zlty]]. simpl in ychx. rewrite ychx in zlty.
  rename zlty into zltc. clear y ychx. 
  rewrite dxeqdc in Hn.
  destruct (fulc1 z n zltc Hn) as [y [zyc [dyeqn cytrue]]].
  destruct zyc as [zley yltc].
  exists y. split; try tauto. split; try tauto.
  right with c1; try assumption.
  left. simpl. reflexivity.
- simpl in ch. rewrite ch, dxeqdc in Hn. lia. }

assert (t_lp x = t_lp c1) as lpxeqc.
{ unfold t_lp at 1, t_upse. simpl. reflexivity. }

assert (t_d x = t_d c1) as dxeqc.
{ unfold t_d. rewrite Heqsec1. unfold t_dose.
simpl. reflexivity. }

assert (incl uev1' (t_uev c1)) as uev1'incl.
{ intros xi Hxi. apply (proj1 (in_remove _ _ _ _ Hxi)). }

assert (incl (t_uev x) (t_uev c1)) as uevxinc.
{ unfold t_uev at 1, t_upse. simpl. assumption. }

assert (forall xi : nnf,
In xi (t_uev x) -> exists phi psi : nnf, xi = unt phi psi) as untuevx.
{ intros xi Hxi. apply uevxinc in Hxi.
apply (unt_only_uev (conj pc1 gpc1) _ Hxi). }

exists x, fulx.
split. split.
{ constructor; try (discriminate || contradiction || assumption).
- intros psi H. simpl in H. injection H. intro Heqpsi. rewrite <- Heqpsi.
  unfold t_G. assumption.
- split; reflexivity.
- intros c' xfs' phi' H. injection H.
  intros Heqphi' Heqxfs Heqc. right. rewrite <- Heqphi'. assumption.
- intros z zltx coz.
  destruct (desc_child_or_child_dec zltx) as [[y [ychx zlty]]|zchx].
  + rewrite ychx in zlty. apply (no_unful_case pc1 zlty coz).
  + rewrite zchx in coz. unfold t_c in coz.
    rewrite Heqsec1 in coz. simpl in coz. discriminate.
} 

{ unfold dproper. intros y Hdes. apply clos_trans_tn1 in Hdes.
inversion Hdes.
- simpl in H. rewrite H. assumption.
- simpl in H. rewrite H in H0. apply clos_tn1_trans in H0.
  apply gpc1. assumption.
}
reflexivity.
}
Defined.

Definition beta2_rule [phi] (bphi : nnf_isbeta phi) [ss : rdoseqt]
  (Hin : In phi (s_G (proj1_sig ss)))
  (Hunsat1 : unsatable (s_G (beta1_child phi (proj1_sig ss))))
  (nu2 : status (beta2_child phi (proj1_sig ss))) : status (proj1_sig ss).
Proof.
refine (
  match nu2 with
  | open i2        => open _
  | closed Hunsat2 => closed (unsat_beta_children bphi Hin Hunsat1 Hunsat2)
  end).

destruct i2 as [c2 [fulc2 Hc2]].
destruct Hc2 as [[pc2 gpc2] Heqsec2].
destruct ss as [s ps].
simpl in Hin, Heqsec2, Hunsat1 |- *.
set (xfs := (s, t_upse c2)).
set (x := tbeta2 c2 xfs phi).

assert (filler x) as fulx.
{ intros z n zltx Hn.
assert (t_d x = t_d c2) as dxeqdc.
{ unfold t_d. rewrite Heqsec2. simpl.
unfold t_dose. simpl. reflexivity. }
destruct (desc_child_or_child_dec zltx) as [dch|ch].
- destruct dch as [y [ychx zlty]]. simpl in ychx.
  rewrite ychx in zlty.
  rename zlty into zltc. clear y ychx. 
  rewrite dxeqdc in Hn.
  destruct (fulc2 z n zltc Hn) as [y [zyc [dyeqn cytrue]]].
  destruct zyc as [zley yltc].
  exists y. split; try tauto. split; try tauto.
  right with c2; try assumption.
  left. simpl. reflexivity.
- simpl in ch. rewrite ch, dxeqdc in Hn. lia. }

assert (t_lp x = t_lp c2) as lpxeqc.
{ unfold t_lp at 1, t_upse. simpl. reflexivity. }

assert (t_d x = t_d c2) as dxeqc.
{ unfold t_d. rewrite Heqsec2. unfold t_dose.
simpl. reflexivity. }

assert (t_uev x = t_uev c2) as uevxeqc.
{ unfold t_uev at 1, t_upse. simpl. reflexivity. }

assert (forall xi : nnf,
In xi (t_uev x) -> exists phi psi : nnf, xi = unt phi psi) as untuevx.
{ rewrite uevxeqc. apply (unt_only_uev (conj pc2 gpc2)). }

exists x, fulx.
split. split.
{ constructor; try (discriminate || contradiction || assumption).
- intros psi H. simpl in H. injection H. intro Heqpsi. rewrite <- Heqpsi.
  unfold t_G. assumption.
- split; reflexivity.
- intros c' xfs' phi' H. injection H.
  intros Heqphi' Heqxfs Heqc. rewrite <- Heqphi'. assumption.
- intros z zltx coz.
  destruct (desc_child_or_child_dec zltx) as [[y [ychx zlty]]|zchx].
  + rewrite ychx in zlty. apply (no_unful_case pc2 zlty coz).
  + rewrite zchx in coz. unfold t_c in coz.
    rewrite Heqsec2 in coz. simpl in coz. discriminate.
} 

{ unfold dproper. intros y Hdes. apply clos_trans_tn1 in Hdes.
inversion Hdes.
- simpl in H. rewrite H. assumption.
- simpl in H. rewrite H in H0. apply clos_tn1_trans in H0.
  apply gpc2. assumption.
}
reflexivity.
Defined.


(* CONTRADICTION RULE *)

Definition contra_rule [s n] :
  In (var n) (s_G s) /\ In (neg n) (s_G s) -> status s :=
  fun Hcontra => closed (unsat_contra Hcontra).


(* LOOP RULE *)

Definition loop_rule [ss : rdoseqt] [h] (sc : state_conditions (proj1_sig ss))
  (bs : blocker_seqt h (proj1_sig ss)) : status (proj1_sig ss).
Proof.
destruct ss as [s ps]. simpl in sc, bs |- *.
set (xup := {|
  s_uev := get_unts (unnext (s_G s));
  s_lp  := fst h
|}).
set (xfs := (s, xup)).
set (x := tloop xfs).

assert (filler x) as fulx.
{ intros z n zltx Hn. contradict zltx.
apply tloop_no_desc. exact I. }

apply open. exists x, fulx.
split. split.
{ constructor; try (discriminate || contradiction || assumption || simpl; tauto).
- split; try reflexivity.
  exists h. split; [assumption|reflexivity].
- intros z zltx coz. contradict zltx. apply tloop_no_desc. exact I.
} 

{ unfold dproper. intros y Hdes. contradict Hdes.
apply tloop_no_desc. exact I. }
simpl. reflexivity.
Defined.
