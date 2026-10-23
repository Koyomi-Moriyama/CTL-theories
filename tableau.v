Require Import utils.
Require Import nnf.
Require Import fml.
Require Import semantics.
Require Import closure.
Require Import seqt.
Require Import size.
Require Import ptree.
Require Import proper.
Require Import rules.
Require Import traverse.
Require Import unravel.
Require Import hintikka.

Require Import List.
Import ListNotations.
Require Import Program.
Require Import String.
Open Scope string_scope.



Program Fixpoint tableau (ss : rdoseqt) {measure (seqt_size ss) lexnat2} : status ss :=
match get_contra (s_G ss) with
| inleft (exist _ n Hcontra) => contra_rule Hcontra (* apply (id) rule *)
| inright no_contra          =>
    match get_alpha_seqt ss with
    | inleft (exist _ phi (conj Hin aphi)) => (* apply (alpha) rule *)
        alpha_rule aphi Hin (tableau (alpha_child_sseqt aphi ss Hin))
    | inright no_alpha =>
        match get_beta_seqt ss with
        | inleft (exist _ phi (conj Hin bphi)) => (* apply (beta) rule *)
            match tableau (beta1_child_sseqt bphi ss Hin) with
            | open (existT _ c1 i1) =>
                match all_eq_dec nnf_eqdec (t_uev c1) phi with
                (* prune procrastinating branch if fulfilling branch 
                leads to an empty uev *)
                | left Halleq  => beta1_rule bphi Hin i1 Halleq
                | right Hexneq => beta_rule bphi Hin i1 Hexneq
                    (tableau (beta2_child_sseqt bphi ss Hin))
                end
            (* if fulfilling branch is closed, only keep procrastinating branch *)
            | closed Hunsat1 => beta2_rule bphi Hin Hunsat1
                (tableau (beta2_child_sseqt bphi ss Hin))
            end
        | inright no_beta =>
            (* gather negative responses of get functions to show the current
            sequent only contains next formulae and literals without contradiction *)
            let sc := Build_state_conditions _ no_contra no_alpha no_beta in
            match get_blocker_seqt ss with
            | inleft (exist _ h block) => (* apply (loop) rule *)
                loop_rule sc block (* block is a witness of a blocking ancestor *)
            | inright nb               => (* apply (next) rule *)
                jump_rule sc nb (tableau (jump_child_sseqt ss sc nb))
            end
        end
    end
end.
Next Obligation. apply alpha_child_decr_size; assumption. Qed.
Next Obligation. apply beta1_child_decr_size; assumption. Qed.
Next Obligation. apply beta2_child_decr_size; assumption. Qed.
Next Obligation. apply beta2_child_decr_size; assumption. Qed.
Next Obligation. apply jump_child_decr_size; try assumption.
apply (Build_state_conditions _ no_contra no_alpha no_beta). Qed.
Next Obligation. apply lexnat2_wf. Qed.


Definition mk_root (G : list nnf) : doseqt :=
{|s_G := G;
  s_H := [];
  s_d := 0;
  s_c := false;
  s_R := G|}.

Theorem mk_root_pseqt (G : list nnf) : regular (mk_root G).
Proof.
(* Proof that the root sequent is regular *)
constructor; simpl.
- constructor.
- apply incl_cl_list_self.
- tauto.
- tauto.
- tauto.
Qed.

Definition mk_root_sseqt (G : list nnf) : rdoseqt :=
  exist _ (mk_root G) (mk_root_pseqt G).

Definition tableau_open (G : list nnf) : bool :=
  match tableau (mk_root_sseqt G) with
  | closed _ => false
  | open _   => true
  end.

Theorem ltree_from_G (G : list nnf) :
  tableau_open G = true -> {t : ltree | gproper (l_root t) /\ G = (t_G (l_root t))}.
Proof.
intro H. unfold tableau_open in H.
destruct (tableau (mk_root_sseqt G)) as [o|c]; try discriminate.
clear H. set (se := ` (mk_root_sseqt G)) in o. simpl in se.
pose proof (proj2_sig (mk_root_sseqt G)) as pse. simpl in pse.
destruct o as [rt [fulrt [[prt gprt] Heqsert]]].

assert (looper rt) as fl.
{
intros x.
destruct (t_isloop_dec x) as [lpx|nlpx].
2:{ right. right. assumption. }
destruct (ptree_eqdec x rt) as [xeqrt|xneqrt].
- exfalso. rewrite xeqrt in lpx. destruct rt; try contradiction.
  destruct (upward_ok prt) as [_ [h [[Hhin _] _]]].
  rewrite Heqsert in Hhin. simpl in Hhin. assumption.
- destruct (desc_dec x rt) as [xltrt|xnltrt].
  2:{ right. left. unfold desceq. tauto. }
  pose proof (gprt x xltrt) as px.
  pose proof (pfdownseqt px) as psex.
  pose proof (upward_ok px) as H.
  destruct (fulrt x (t_lp x) xltrt) as [y [xyrt [dylpx cytr]]];
    destruct x; try contradiction.
  { destruct H as [_ [h [[Hhin _] Heqfh ]]].
  unfold t_H in Hhin. unfold t_d. rewrite Heqsert at 1.
  simpl. rewrite Heqfh. apply (earlier_H psex _ Hhin). }
  left. exists y.
  pose proof (gprt y (proj2 xyrt)) as py.
  pose proof (desc_dproper gprt (proj2 xyrt)) as gpy.
  destruct H as [_ [h [[Hhin Heqset] Heqfh ]]].
  split; try assumption. split; try assumption.
  split; try assumption.
  apply (tloop_anc_eqset (conj py gpy) (proj1 xyrt)); assumption.
}

set (t := {|
l_root := rt;
l_looper := fl
|}).
exists t. split; try exact (conj prt gprt). simpl. unfold t_G. rewrite Heqsert.
simpl. reflexivity.
Defined.

Theorem completeness : forall G, satable G -> tableau_open G = true.
Proof.
intros G H. destruct (tableau_open G) eqn:Htab; try reflexivity.
unfold tableau_open in Htab.
destruct (tableau (mk_root_sseqt G)) as [|c]; try discriminate.
simpl in c. destruct H as [M [i H]]. contradict H. apply c.
Qed.

Theorem soundness : forall G, tableau_open G = true -> satable G.
Proof.
intros G H. destruct (ltree_from_G G H) as [t [gpt HeqG]].
rewrite HeqG. apply (model_existence _ gpt).
Qed.

Theorem correctness : forall G, tableau_open G = true <-> satable G.
Proof.
intro G. split; [apply soundness | apply completeness].
Qed.

Definition fml_tableau_open (G : list fml) := tableau_open (map to_nnf G).

Theorem fml_correctness : forall G, fml_tableau_open G = true <-> fml_satable G.
Proof.
unfold fml_tableau_open. unfold fml_satable.
setoid_rewrite sat_fml_nnf_iff.
intro G. apply correctness.
Qed.
