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
| tbeta1  _ _ _ phi => nnf_isbeta phi
| tbeta2 _ _ _ phi => nnf_isbeta phi
| talt _ _ _ _ phi => nnf_isbeta phi
| tjump _ _ phi    => nnf_isjump phi
end.


Definition proper_downward (x : ptree) : Prop :=
match x with
| talpha c _ phi   => t_dose c = alpha_child phi (t_dose x)
| tbeta1 c _ _ phi => t_dose c = beta1_child phi (t_dose x)
| tbeta2 c _ _ phi => t_dose c = beta2_child phi (t_dose x)
| talt c1 c2 _ _ phi   => t_dose c1 = beta1_child phi (t_dose x) /\  t_dose c2 = beta2_child phi (t_dose x)
| tjump cs fs _ =>  map t_dose cs = jump_child (D_rule( t_dose x))
end.

Fixpoint uev_lookup (phi : nnf) (u : list (nnf * nat)) : option nat :=
  match u with
  | [] => None
  | (psi, n) :: us =>
      if nnf_eqdec phi psi
      then Some n
      else uev_lookup phi us
  end.

Fixpoint uev_min (f g : list (nnf * nat)) : list (nnf * nat) :=
  match f with
  | [] => []
  | (phi, n) :: fs =>
      match uev_lookup phi g with
      | None => uev_min fs g
      | Some m => (phi, Nat.min n m) :: uev_min fs g
      end
  end.

Fixpoint uev_excl (phi : nnf) (u : list (nnf * nat)) : list (nnf * nat) :=
  match u with
  | [] => []
  | (psi, n) :: us =>
      if nnf_eqdec phi psi
      then us
      else (psi, n) :: uev_excl phi us
  end.

Fixpoint get_blocked_jump (parent : doseqt) (candidates : list doseqt)
  : list ((list nnf) * nat) :=
  match candidates with
  | [] => []
  | c :: candidates' =>
      match get_blocker_G (s_G c) parent with
      | inleft H => proj1_sig H :: get_blocked_jump parent candidates'
      | inright _ => get_blocked_jump parent candidates'
      end
  end.

Fixpoint blocked_lookup (D : list nnf) (blocked : list ((list nnf) * nat))
  : option nat :=
  match blocked with
  | [] => None
  | (G, n) :: blocked' =>
      if eqset_dec nnf_eqdec G D
      then Some n
      else blocked_lookup D blocked'
  end.

Fixpoint find_real_jump_child (D : list nnf) (cs : list ptree) : option ptree :=
  match cs with
  | [] => None
  | c :: cs' =>
      if eqset_dec nnf_eqdec (t_G c) D
      then Some c
      else find_real_jump_child D cs'
  end.

Definition jump_succ_value (parent : doseqt) (real_cs : list ptree)
 (blocked : list ((list nnf) * nat)) (phi psi : nnf) : option nat :=
  let D := phi :: unanext (s_G parent) in
  match blocked_lookup D blocked with
  | Some n =>
      Some n
  | None =>
      match find_real_jump_child D real_cs with
      | Some c =>
          uev_lookup psi (t_uev c)
      | None =>
          None
      end
  end.

Definition option_max (x y : option nat) : option nat :=
  match x, y with
  | None, None       => None
  | Some n, None     => Some n
  | None, Some m     => Some m
  | Some n, Some m   => Some (Nat.max n m)
  end.


Fixpoint real_children_max (psi : nnf) (cs : list ptree) : option nat :=
  match cs with
  | [] => None
  | c :: cs' => option_max (uev_lookup psi (t_uev c)) (real_children_max psi cs')
  end.

Fixpoint blocked_children_max (blocked : list ((list nnf) * nat)) : option nat :=
  match blocked with
  | [] => None
  | (_, n) :: blocked' => option_max (Some n) (blocked_children_max blocked')
  end.

Definition jump_au_value (real_cs : list ptree) (blocked : list ((list nnf) * nat))
 (psi : nnf) : option nat := option_max (real_children_max psi real_cs) (blocked_children_max blocked).


Fixpoint build_jump_eu (parent : doseqt) (real_cs : list ptree)
 (blocked : list ((list nnf) * nat)) (phis : list nnf) : list (nnf * nat) :=
  match phis with
  | [] => []
  | psi :: phis' =>
      if nnf_iseu psi then
        match jump_succ_value
                parent real_cs blocked psi psi with
        | Some n =>
            (psi, n) ::
            build_jump_eu parent real_cs blocked phis'
        | None =>
            build_jump_eu parent real_cs blocked phis'
        end
      else  build_jump_eu parent real_cs blocked phis'
  end.

Fixpoint build_jump_au (real_cs : list ptree) (blocked : list ((list nnf) * nat))
  (Delta : list nnf) : list (nnf * nat) :=
  match Delta with
  | [] => []
  | psi :: Delta' =>
      if nnf_isau psi then
        match jump_au_value real_cs blocked psi with
        | Some n => (psi, n) :: build_jump_au real_cs blocked Delta'
        | None => build_jump_au real_cs blocked Delta'
        end
      else build_jump_au real_cs blocked Delta'
  end.

Definition t_uev_jump
  (x : ptree) : list (nnf * nat) :=
  match x with
  | tjump cs fs _ =>
      let parent := fst fs in
      let blocked := get_blocked_jump parent (temporary_jump_child parent) in
      build_jump_eu parent cs blocked (unenext (s_G parent))
      ++
      build_jump_au cs blocked (unanext (s_G parent))
  | _ => []
  end.

Definition proper_beta_upward (parent_uev child1_uev child2_uev merged_uev : list (nnf * nat))
(parent_mrk child1_mrk child2_mrk : bool) : Prop :=
(parent_uev = child1_uev /\ parent_mrk = false /\  child1_mrk = false /\ child2_mrk = true)
\/ (parent_uev = child2_uev /\ parent_mrk = false /\ child1_mrk = true /\ child2_mrk = false)
\/ (parent_uev = [] /\ parent_mrk = true /\ child1_mrk = true /\ child2_mrk = true)
\/ (parent_uev = merged_uev /\ parent_mrk = false /\ child1_mrk = false /\ child2_mrk = false).

Definition jump_has_large_uev (x : ptree) (cs : list ptree) : Prop :=
  exists c psi i, In c cs /\ In psi (t_G c) /\ In (psi, i) (t_uev c) /\ i > length (t_H x).

Definition jump_should_mark (x : ptree) (cs : list ptree) : Prop := 
existsb t_mrk cs = true \/ jump_has_large_uev x cs.

Definition proper_upward (x : ptree) : Prop := match x with
  | talpha c _ _ => t_uev x = t_uev c /\ t_mrk x = t_mrk c
  | tbeta1 c _ _ _ => (t_uev x) = (t_uev c)
  | tbeta2 c _ _ _ => (t_uev x) = (t_uev c)
  | talt c1 c2 beta_or _ _ => (t_uev x) = (uev_min (t_uev c1) (t_uev c2)) 
  | talt c1 c2 beta_au _ phi => (t_uev x) = (uev_min (uev_excl phi (t_uev c1)) (t_uev c2))
  | talt c1 c2 beta_eu _ _ => (t_uev x) = (uev_min (t_uev c1) (t_uev c2))
  | tjump cs _ _ => (t_mrk x = true <-> jump_should_mark x cs) /\ eqset (t_uev x) (t_uev_jump x)
  end.

Record proper (x : ptree) : Prop :=
{ pfdownseqt   : regular (t_dose x);
  has_prinform : forall phi, t_prinform x = Some phi -> In phi (t_G x);
  prinform_ok  : proper_prinform x;
  downward_ok  : proper_downward x;
  upward_ok    : proper_upward x;
  state_has_sc : t_isstate x -> state_conditions (t_dose x);
  jump_only_atomic : t_isjump x -> forall phi, In phi (t_G x) -> nnf_isatomic phi \/ nnf_isjump phi;
  proper_history_numbering: forall G n, In (G, n) (t_H x) -> 1 < n ->
   exists G', In (G', n - 1) (t_H x);
  history_numbering_positive: forall G n, In (G, n) (t_H x) -> 0 < n;
  history_numbering_unique: NoDup (map snd (t_H x));
  proper_uev_keys : NoDup (map fst (t_uev x));
  mrk_all_false : t_mrk x = false
  }.

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


(*Ltac tree_ind_with_eqns x :=
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
*)

(**
  Derived structural properties of proper unpruned tableaux.

  These lemmas concern ordinary structural children and paths only.  In
  particular, they make no claim that a node is unmarked or belongs to an
  open tableau.
*)
(*
Lemma nonjump_child_history_equal :
  forall x y,
    proper x ->
    is_child y x ->
    ~ t_isjump x ->
    t_H y = t_H x.
Proof.
  intros x y Hproper Hchild Hnonjump.
  destruct x as [c fs phi | c fs phi |c fs phi | c1 c2 bt fs phi | cs fs phi].
  - simpl in Hchild. subst y.
    pose proof (downward_ok Hproper) as Hdown.
    unfold t_H. rewrite Hdown. reflexivity.
  - simpl in Hchild. destruct Hchild as [-> | ->];
      pose proof (downward_ok Hproper) as Hdown;
      destruct Hdown as [Hdown1 Hdown2];
      unfold t_H; [rewrite Hdown1 | rewrite Hdown2]; reflexivity.
  - exfalso. apply Hnonjump. exact I.
Qed.

Lemma jump_child_history_shape :
  forall x y,
    proper x ->
    is_child y x ->
    t_isjump x ->
    t_H y = (t_G x, S (length (t_H x))) :: t_H x.
Proof.
  intros x y Hproper Hchild Hisjump.
  destruct x as [c fs phi | c1 c2 bt fs phi | cs fs phi];
    try contradiction.
  simpl in Hchild.
  pose proof (downward_ok Hproper) as Hdown.
  simpl in Hdown.
  apply in_map with (f := t_dose) in Hchild.
  rewrite Hdown in Hchild.
  apply jump_child_In_fake in Hchild.
  pose proof (@fake_jump_child_history_shape
                (D_rule (t_dose (tjump cs fs phi))) (t_dose y) Hchild)
    as Hshape.
  exact Hshape.
Qed.

Lemma history_incl_child :
  forall x y,
    proper x ->
    is_child y x ->
    incl (t_H x) (t_H y).
Proof.
  intros x y Hproper Hchild.
  destruct (t_isstate_dec x) as [Hjump | Hnonjump].
  - rewrite (@jump_child_history_shape x y Hproper Hchild Hjump).
    apply incl_tl. apply incl_refl.
  - rewrite (@nonjump_child_history_equal x y Hproper Hchild Hnonjump).
    apply incl_refl.
Qed.

Lemma history_incl_desc :
  forall x z,
    gproper x ->
    desc z x ->
    incl (t_H x) (t_H z).
Proof.
  intros x z [Hproper Hdproper] Hdesc.
  apply clos_trans_tn1 in Hdesc.
  induction Hdesc.
  - apply history_incl_child; assumption.
  - eapply incl_tran.
    + apply history_incl_child; eassumption.
    + apply IHHdesc.
      * apply (child_proper Hdproper). assumption.
      * apply (child_dproper Hdproper). assumption.
Qed.

Lemma tpath_no_jump_same_history :
  forall p x z,
    gproper x ->
    tpath p x z ->
    (forall y, In y p -> ~ t_isjump y) ->
    t_H z = t_H x.
Proof.
  intros p x z [Hproper Hdproper] Hpath.
  induction Hpath; intro Hnojump.
  - reflexivity.
  - rewrite (IHHpath (child_proper Hdproper H)
                         (child_dproper Hdproper H)).
    + apply nonjump_child_history_equal; try assumption.
      apply Hnojump. now left.
    + intros w Hw. apply Hnojump. now right.
Qed.

Corollary tpath_no_jump_same_history_length :
  forall p x z,
    gproper x ->
    tpath p x z ->
    (forall y, In y p -> ~ t_isjump y) ->
    length (t_H z) = length (t_H x).
Proof.
  intros p x z Hproper Hpath Hnojump.
  now rewrite (tpath_no_jump_same_history Hproper Hpath Hnojump).
Qed.

Lemma history_length_le_child :
  forall x y,
    proper x ->
    is_child y x ->
    length (t_H x) <= length (t_H y).
Proof.
  intros x y Hproper Hchild.
  destruct (t_isstate_dec x) as [Hjump | Hnonjump].
  - rewrite (@jump_child_history_shape x y Hproper Hchild Hjump).
    simpl. lia.
  - rewrite (@nonjump_child_history_equal x y Hproper Hchild Hnonjump).
    lia.
Qed.

Lemma history_entry_preserved_to_parent :
  forall x y G n,
    proper x ->
    is_child y x ->
    In (G, n) (t_H y) ->
    n <= length (t_H x) ->
    In (G, n) (t_H x).
Proof.
  intros x y G n Hproper Hchild Hin Hlevel.
  destruct (t_isstate_dec x) as [Hjump | Hnonjump].
  - rewrite (@jump_child_history_shape x y Hproper Hchild Hjump) in Hin.
    destruct Hin as [Heq | Hin]; try assumption.
    injection Heq. intros Hn _. subst n. lia.
  - rewrite (@nonjump_child_history_equal x y Hproper Hchild Hnonjump) in Hin.
    exact Hin.
Qed.

Lemma history_entry_preserved_on_tpath :
  forall p x z G n,
    gproper x ->
    tpath p x z ->
    In (G, n) (t_H z) ->
    n <= length (t_H x) ->
    In (G, n) (t_H x).
Proof.
  intros p x z G n [Hproper Hdproper] Hpath.
  induction Hpath; intros Hin Hlevel; try assumption.
  apply (@history_entry_preserved_to_parent x y G n Hproper H).
  - apply IHHpath.
    + apply (child_proper Hdproper H).
    + apply (child_dproper Hdproper H).
    + exact Hin.
    + eapply Nat.le_trans; [exact Hlevel |].
      apply history_length_le_child; assumption.
  - exact Hlevel.
Qed.

Lemma history_entry_preserved_to_ancestor :
  forall x z G n,
    gproper x ->
    desc z x ->
    In (G, n) (t_H z) ->
    n <= length (t_H x) ->
    In (G, n) (t_H x).
Proof.
  intros x z G n [Hproper Hdproper] Hdesc.
  apply clos_trans_tn1 in Hdesc.
  induction Hdesc; intros Hin Hlevel.
  - eapply history_entry_preserved_to_parent; eassumption.
  - eapply history_entry_preserved_to_parent.
    + exact Hproper.
    + exact H.
    + apply IHHdesc.
      * apply (child_proper Hdproper H).
      * apply (child_dproper Hdproper H).
      * exact Hin.
      * eapply Nat.le_trans; [exact Hlevel |].
        apply history_length_le_child; assumption.
    + exact Hlevel.
Qed.

Lemma alpha_formula_preserved_child :
  forall x y phi,
    proper x ->
    is_child y x ->
    nnf_isalpha phi ->
    In phi (t_G x) ->
    t_prinform x <> Some phi ->
    In phi (t_G y).
Proof.
  intros x y phi Hproper Hchild Halpha Hin Hnotprincipal.
  destruct x as [c fs psi | c1 c2 bt fs psi | cs fs psi].
  - simpl in Hchild. subst y.
    pose proof (downward_ok Hproper) as Hdown.
    unfold t_G. rewrite Hdown. simpl. right; right.
    apply in_in_remove; try assumption.
    intro Heq. apply Hnotprincipal. simpl. now subst psi.
  - simpl in Hchild. destruct Hchild as [-> | ->];
      pose proof (downward_ok Hproper) as Hdown;
      destruct Hdown as [Hdown1 Hdown2]; unfold t_G;
      [rewrite Hdown1 | rewrite Hdown2]; simpl; right;
      apply in_in_remove; try assumption;
      intro Heq; subst psi; exact (beta_not_alpha (prinform_ok Hproper) Halpha).
  - exfalso.
    exact ((sc_no_alpha (state_has_sc Hproper I) phi Hin) Halpha).
Qed.

Lemma beta_formula_preserved_child :
  forall x y phi,
    proper x ->
    is_child y x ->
    nnf_isbeta phi ->
    In phi (t_G x) ->
    t_prinform x <> Some phi ->
    In phi (t_G y).
Proof.
  intros x y phi Hproper Hchild Hbeta Hin Hnotprincipal.
  destruct x as [c fs psi | c1 c2 bt fs psi | cs fs psi].
  - simpl in Hchild. subst y.
    pose proof (downward_ok Hproper) as Hdown.
    unfold t_G. rewrite Hdown. simpl. right; right.
    apply in_in_remove; try assumption.
    intro Heq. subst psi.
    exact ((beta_not_alpha Hbeta) (prinform_ok Hproper)).
  - simpl in Hchild. destruct Hchild as [-> | ->];
      pose proof (downward_ok Hproper) as Hdown;
      destruct Hdown as [Hdown1 Hdown2]; unfold t_G;
      [rewrite Hdown1 | rewrite Hdown2]; simpl; right;
      apply in_in_remove; try assumption;
      intro Heq; apply Hnotprincipal; simpl; now subst psi.
  - exfalso.
    exact ((sc_no_beta (state_has_sc Hproper I) phi Hin) Hbeta).
Qed.

Lemma enext_preserved_before_jump :
  forall p x z phi,
    gproper x ->
    tpath p x z ->
    In (enext phi) (t_G x) ->
    (forall y, In y p -> ~ t_isjump y) ->
    In (enext phi) (t_G z).
Proof.
  intros p x z phi [Hproper Hdproper] Hpath.
  induction Hpath; intros Hin Hnojump; try assumption.
  apply IHHpath.
  - apply (child_proper Hdproper H).
  - apply (child_dproper Hdproper H).
  - destruct x as [c fs psi | c1 c2 bt fs psi | cs fs psi].
    + simpl in H. subst y.
      pose proof (downward_ok Hproper) as Hdown.
      unfold t_G. rewrite Hdown. simpl. right; right.
      apply in_in_remove; try assumption.
      intro Heq. subst psi.
      pose proof (prinform_ok Hproper) as Hok. simpl in Hok. contradiction.
    + simpl in H. destruct H as [-> | ->];
        pose proof (downward_ok Hproper) as Hdown;
        destruct Hdown as [Hdown1 Hdown2]; unfold t_G;
        [rewrite Hdown1 | rewrite Hdown2]; simpl; right;
        apply in_in_remove; try assumption;
        intro Heq; subst psi;
        pose proof (prinform_ok Hproper) as Hok; simpl in Hok; contradiction.
    + exfalso. apply (Hnojump (tjump cs fs psi)). now left. exact I.
  - intros w Hw. apply Hnojump. now right.
Qed.

Lemma anext_preserved_before_jump :
  forall p x z phi,
    gproper x ->
    tpath p x z ->
    In (anext phi) (t_G x) ->
    (forall y, In y p -> ~ t_isjump y) ->
    In (anext phi) (t_G z).
Proof.
  intros p x z phi [Hproper Hdproper] Hpath.
  induction Hpath; intros Hin Hnojump; try assumption.
  apply IHHpath.
  - apply (child_proper Hdproper H).
  - apply (child_dproper Hdproper H).
  - destruct x as [c fs psi | c1 c2 bt fs psi | cs fs psi].
    + simpl in H. subst y.
      pose proof (downward_ok Hproper) as Hdown.
      unfold t_G. rewrite Hdown. simpl. right; right.
      apply in_in_remove; try assumption.
      intro Heq. subst psi.
      pose proof (prinform_ok Hproper) as Hok. simpl in Hok. contradiction.
    + simpl in H. destruct H as [-> | ->];
        pose proof (downward_ok Hproper) as Hdown;
        destruct Hdown as [Hdown1 Hdown2]; unfold t_G;
        [rewrite Hdown1 | rewrite Hdown2]; simpl; right;
        apply in_in_remove; try assumption;
        intro Heq; subst psi;
        pose proof (prinform_ok Hproper) as Hok; simpl in Hok; contradiction.
    + exfalso. apply (Hnojump (tjump cs fs psi)). now left. exact I.
  - intros w Hw. apply Hnojump. now right.
Qed.

Lemma alpha_expanded_before_jump :
  forall p x z phi,
    gproper x ->
    nnf_isalpha phi ->
    In phi (t_G x) ->
    tpath p x z ->
    t_isjump z ->
    exists y, In y p /\ t_prinform y = Some phi.
Proof.
  intros p x z phi [Hproper Hdproper] Halpha Hin Hpath.
  induction Hpath; intro Hzjump.
  - exfalso. exact ((sc_no_alpha (state_has_sc Hproper Hzjump) phi Hin) Halpha).
  - destruct (option_eqdec nnf_eqdec (t_prinform x) (Some phi)) as [Heq | Hneq].
    + exists x. split; [now left | exact Heq].
    + destruct (IHHpath (child_proper Hdproper H)
                        (child_dproper Hdproper H)
                        (@alpha_formula_preserved_child
                           x y phi Hproper H Halpha Hin Hneq)
                        Hzjump) as [w [Hw Hprincipal]].
      exists w. split; [now right | exact Hprincipal].
Qed.

Lemma beta_expanded_before_jump :
  forall p x z phi,
    gproper x ->
    nnf_isbeta phi ->
    In phi (t_G x) ->
    tpath p x z ->
    t_isjump z ->
    exists y, In y p /\ t_prinform y = Some phi.
Proof.
  intros p x z phi [Hproper Hdproper] Hbeta Hin Hpath.
  induction Hpath; intro Hzjump.
  - exfalso. exact ((sc_no_beta (state_has_sc Hproper Hzjump) phi Hin) Hbeta).
  - destruct (option_eqdec nnf_eqdec (t_prinform x) (Some phi)) as [Heq | Hneq].
    + exists x. split; [now left | exact Heq].
    + destruct (IHHpath (child_proper Hdproper H)
                        (child_dproper Hdproper H)
                        (@beta_formula_preserved_child
                           x y phi Hproper H Hbeta Hin Hneq)
                        Hzjump) as [w [Hw Hprincipal]].
      exists w. split; [now right | exact Hprincipal].
Qed.

Lemma proper_uev_key_unique :
  forall x phi n m,
    proper x ->
    In (phi, n) (t_uev x) ->
    In (phi, m) (t_uev x) ->
    n = m.
Proof.
  intros x phi n m Hproper Hin Hjm.
  pose proof (proper_uev_keys Hproper) as Hnodup.
  induction (t_uev x) as [|[psi k] u IHu].
  - contradiction.
  - simpl in Hin, Hjm, Hnodup.
    inversion Hnodup as [|a l Hnotin Hnodup']; subst.
    destruct Hin as [Hin | Hin]; destruct Hjm as [Hjm | Hjm].
    + now injection Hin; injection Hjm; intros; subst.
    + injection Hin; intros; subst psi k.
      exfalso. apply Hnotin. apply in_map_iff.
      exists (phi, m). split; [reflexivity | exact Hjm].
    + injection Hjm; intros; subst psi k.
      exfalso. apply Hnotin. apply in_map_iff.
      exists (phi, n). split; [reflexivity | exact Hin].
    + apply IHu; assumption.
Qed.

*)

(*
Definition open_tpath_from (root x : ptree) : Prop :=
  exists p, unmarked_tpath p root x.

Definition blocked_jump_candidate (source : ptree) (candidate : doseqt) : Prop :=
  t_isjump source /\
  In candidate (fake_jump_child (D_rule (t_dose source))) /\
  blocker_Gamma (s_G candidate) (D_rule (t_dose source)).

Record loop_info (root : ptree) : Type :=
{ li_source : ptree;
  li_target : ptree;
  li_candidate : doseqt;
  li_history_G : list nnf;
  li_level : nat;
  li_path : list ptree;
  li_path_ok : unmarked_tpath li_path root li_source;
  li_target_on_path : In li_target li_path;
  li_target_ancestor : li_source </ li_target;
  li_source_isjump : t_isjump li_source;
  li_target_isjump : t_isjump li_target;
  li_candidate_is_fake :
    In li_candidate (fake_jump_child (D_rule (t_dose li_source)));
  li_history_entry :
    In (li_history_G, li_level) (t_H li_source);
  li_candidate_blocked :
    eqset li_history_G (s_G li_candidate);
  li_target_realizes_entry :
    eqset (t_G li_target) li_history_G
}.

Definition loop_info_matches {root : ptree}
  (source : ptree) (candidate : doseqt) (info : loop_info root) : Prop :=
  li_source info = source /\ li_candidate info = candidate.

Record ltree : Type :=
{ l_root : ptree;
  l_root_gproper : gproper l_root;
  l_root_unmarked : t_mrk l_root = false;
  l_loops : list (loop_info l_root);
  l_loops_complete :
    forall source candidate,
      open_tpath_from l_root source ->
      blocked_jump_candidate source candidate ->
      exists info,
        In info l_loops /\ loop_info_matches source candidate info
}.

Lemma loop_info_source_open : forall root (info : loop_info root),
  open_tpath_from root (li_source info).
Proof.
  intros root info. exists (li_path info). apply li_path_ok.
Qed.

Lemma loop_info_source_unmarked : forall root (info : loop_info root),
  t_mrk (li_source info) = false.
Proof.
  intros root info.
  apply unmarked_tpath_endpoint_unmarked with
    (p := li_path info) (root := root).
  apply li_path_ok.
Qed.

Lemma loop_info_target_unmarked : forall root (info : loop_info root),
  t_mrk (li_target info) = false.
Proof.
  intros root info.
  destruct (li_path_ok info) as [Hpath Hall].
  rewrite Forall_forall in Hall. apply Hall.
  unfold tpath_nodes. right. apply li_target_on_path.
Qed.

Lemma loop_info_target_strict_ancestor : forall root (info : loop_info root),
  li_source info </ li_target info.
Proof.
  intros root info. apply li_target_ancestor.
Qed.

Lemma loop_info_candidate_is_blocked : forall root (info : loop_info root),
  blocked_jump_candidate (li_source info) (li_candidate info).
Proof.
  intros root info. split; [apply li_source_isjump |].
  split; [apply li_candidate_is_fake |].
  unfold blocker_Gamma.
  apply InA_alt. exists (li_history_G info). split.
  - apply eqset_sym. apply li_candidate_blocked.
  - unfold D_rule. simpl. apply in_map_iff.
    exists (li_history_G info, li_level info).
    split; [reflexivity | apply li_history_entry].
Qed.

Lemma ltree_loop_sound : forall (t : ltree) info,
  In info (l_loops t) ->
  open_tpath_from (l_root t) (li_source info) /\
  blocked_jump_candidate (li_source info) (li_candidate info) /\
  li_source info </ li_target info.
Proof.
  intros t info _. split.
  - apply loop_info_source_open.
  - split.
    + apply loop_info_candidate_is_blocked.
    + apply loop_info_target_strict_ancestor.
Qed.

Lemma ltree_loop_complete : forall (t : ltree) source candidate,
  open_tpath_from (l_root t) source ->
  blocked_jump_candidate source candidate ->
  exists info,
    In info (l_loops t) /\ loop_info_matches source candidate info.
Proof. intros t. apply l_loops_complete. Qed.
  *)
(*Lemma*) 

(*
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
*)
(*old version CTL
Definition core_node (y rt : ptree) : Prop :=
  exists p, p <=/ rt /\ t_isjump p /\ is_child y p.

Definition history_filler (rt : ptree) :=
  forall (x : ptree) (h : list nnf * nat),
    x <=/ rt -> In h (t_H x) -> {y : ptree |  x <=/ y /\ y <=/ rt /\
    length (t_H y) = snd h /\ eqset (t_G y) (fst h) /\ core_node y rt}.

Definition filler (x : ptree) := forall z n, z </ x -> length (t_H x) < n <= length (t_H z) ->
  {ly :list ptree | forall y, In y ly <-> z <=/ y </ x /\  length (t_H y) = n /\ t_mrk y = false} .

Definition t_info (x : ptree) (s : doseqt) :=
{filx : filler x | gproper x /\ t_dose x = s}.

Definition open_info (s : doseqt) := {x & t_info x s}.

Inductive status (s : doseqt) :=
  | open   : open_info s -> status s
  | closed : unsatable (s_G s) -> status s.

Arguments open [s].
Arguments closed [s].

Definition loop_target (x y rt : ptree) :=
  x <=/ y </ rt /\ In (length (t_H y)) (map snd (t_uev x)) /\ t_mrk y = false.


Definition looper (rt : ptree) := forall x : ptree,
{ly  |ly <> [] /\ forall y, In y ly <-> loop_target x y rt} + {~ x <=/ rt \/ ~ t_isjump x \/ t_uev x = []}.



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
*)

(* A core node is a real child generated by a jump node. *)
Definition core_node (y rt : ptree) : Prop :=
  exists p,
    p <=/ rt /\
    t_isjump p /\
    is_child y p.


(* A blocked prospective successor. *)
Definition blocked_candidate
  (x : ptree) (c : doseqt) : Prop :=
  t_isjump x /\
  In c (temporary_jump_child (t_dose x)) /\
  exists h,
    In h (t_H x) /\
    eqset (fst h) (s_G c).


(* Every history entry can constructively be traced back
   to the core node which introduced it. *)
Definition filler (rt : ptree) :=
  forall (x : ptree) (h : list nnf * nat),
    x <=/ rt ->
    In h (t_H x) ->
    { y : ptree |
        x <=/ y /\
        y <=/ rt /\
        core_node y rt /\
        eqset (t_G y) (fst h) /\
        length (t_H y) = snd h }.


Definition t_info (x : ptree) (s : doseqt) :=
  { filx : filler x |
      gproper x /\ t_dose x = s }.


Definition open_info (s : doseqt) :=
  { x & t_info x s }.


Inductive status (s : doseqt) :=
  | open   : open_info s -> status s
  | closed : unsatable (s_G s) -> status s.

Arguments open [s].
Arguments closed [s].


(* A blocked candidate is resolved to the earlier core node
   represented by its matching history entry. *)
Definition loop_target
  (x : ptree) (c : doseqt)
  (y rt : ptree) : Prop :=
  exists h,
    In h (t_H x) /\
    eqset (fst h) (s_G c) /\
    x <=/ y /\
    y <=/ rt /\
    core_node y rt /\
    eqset (t_G y) (fst h) /\
    length (t_H y) = snd h.


Definition looper (rt : ptree) :=
  forall (x : ptree) (c : doseqt),
    x <=/ rt ->
    blocked_candidate x c ->
    { y : ptree |
        loop_target x c y rt }.


Record ltree : Type :=
{
  l_root   : ptree;
  l_looper : looper l_root
}.


Lemma l_desceq_proper [t : ltree] :
  gproper (l_root t) ->
  forall x, x <=/ l_root t -> proper x.
Proof.
  intros gpt x xlert.
  destruct xlert as [xltrt | xeqrt].
  - apply gpt; assumption.
  - rewrite xeqrt.
    exact (proj1 gpt).
Qed.