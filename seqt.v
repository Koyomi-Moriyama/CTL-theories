Require Import utils.
Require Import nnf.
Require Import closure.

Require Import String.
Open Scope string_scope.
Require Import Bool.
Require Import Arith.
Require Import List.
Require Import ListSet.
Require Import SetoidList.
Import ListNotations.
Require Import Relations.
Require Import Program.
Require Import Lia.


Set Implicit Arguments.

(*edit mark*)
Record doseqt : Set :=
{ s_G : list nnf;(*Gamma*)
  (* History entries are pushed at the head.  Levels start at one: a new
     entry records [S (length old_history)].  Blocking compares [fst], while
     later UEV bookkeeping may inspect [snd]. *)
  s_H : list ((list nnf * nat));(*HCr*)
  s_R : list nnf; }(*Gamma of previous node*).

Fixpoint history_levels_ok (H : list (list nnf * nat)) : Prop :=
  match H with
  | [] => True
  | (_, n) :: H' =>
      n = S (length H') /\ history_levels_ok H'
  end.

Lemma history_levels_ok_nil : history_levels_ok [].
Proof. exact I. Qed.

Lemma history_levels_ok_push : forall G H,
  history_levels_ok H ->
  history_levels_ok ((G, S (length H)) :: H).
Proof. simpl. auto. Qed.

Lemma history_levels_ok_head : forall G n H,
  history_levels_ok ((G, n) :: H) -> n = S (length H).
Proof. intros G n H Hlevels. exact (proj1 Hlevels). Qed.

Lemma history_levels_ok_tail : forall G n H,
  history_levels_ok ((G, n) :: H) -> history_levels_ok H.
Proof. intros G n H Hlevels. exact (proj2 Hlevels). Qed.

Lemma history_level_positive : forall H G n,
  history_levels_ok H -> In (G, n) H -> 1 <= n.
Proof.
  induction H as [|[G0 k] H IH]; intros G n Hlevels Hin.
  - contradiction.
  - simpl in Hlevels. destruct Hlevels as [Hk Hlevels].
    simpl in Hin. destruct Hin as [Hin | Hin].
    + inversion Hin. subst. lia.
    + apply (IH G n Hlevels Hin).
Qed.

Lemma history_level_le_length : forall H G n,
  history_levels_ok H -> In (G, n) H -> n <= length H.
Proof.
  induction H as [|[G0 k] H IH]; intros G n Hlevels Hin.
  - contradiction.
  - simpl in Hlevels. destruct Hlevels as [Hk Hlevels].
    simpl in Hin. destruct Hin as [Hin | Hin].
    + inversion Hin. subst. simpl. lia.
    + simpl. specialize (IH G n Hlevels Hin). lia.
Qed.

Lemma history_levels_nodup : forall H,
  history_levels_ok H -> NoDup (map snd H).
Proof.
  induction H as [|[G k] H IH]; intro Hlevels.
  - constructor.
  - simpl in Hlevels. destruct Hlevels as [Hk Hlevels].
    simpl. constructor.
    + intro Hink.
      apply in_map_iff in Hink.
      destruct Hink as [[G' n] [Hn Hin]]. simpl in Hn. subst n.
      pose proof (@history_level_le_length H G' k Hlevels Hin). lia.
    + exact (IH Hlevels).
Qed.

Lemma history_entry_at_level_unique : forall H n,
  history_levels_ok H ->
  1 <= n <= length H ->
  exists! h, In h H /\ snd h = n.
Proof.
  induction H as [|[G k] H IH]; intros n Hlevels Hrange.
  - simpl in Hrange. lia.
  - simpl in Hlevels. destruct Hlevels as [Hk Hlevels].
    destruct (Nat.eq_dec n k) as [Hnk | Hnk].
    + exists (G, k). split.
      * split; [now left | simpl; symmetry; exact Hnk].
      * intros [G' k'] [Hin Hlevel].
        simpl in Hlevel. subst k'.
        destruct Hin as [Hin | Hin].
        -- inversion Hin. reflexivity.
        -- pose proof (@history_level_le_length H G' n Hlevels Hin). lia.
    + assert (Hrange_tail : 1 <= n <= length H) by (simpl in Hrange; lia).
      destruct (IH n Hlevels Hrange_tail) as [h [Hh Hunique]].
      exists h. split.
      * split; [right; exact (proj1 Hh) | exact (proj2 Hh)].
      * intros h' [Hin' Hlevel'].
        destruct Hin' as [Hin' | Hin'].
        -- subst h'. simpl in Hlevel'. exfalso. apply Hnk. symmetry. exact Hlevel'.
        -- apply Hunique. split; assumption.
Qed.

Fixpoint history_lookup_level
  (n : nat) (H : list (list nnf * nat)) : option (list nnf * nat) :=
  match H with
  | [] => None
  | h :: H' =>
      if Nat.eq_dec n (snd h) then Some h else history_lookup_level n H'
  end.

Lemma history_lookup_level_sound : forall H n h,
  history_lookup_level n H = Some h -> In h H /\ snd h = n.
Proof.
  induction H as [|h0 H IH]; intros n h Hlookup.
  - discriminate.
  - simpl in Hlookup.
    destruct (Nat.eq_dec n (snd h0)) as [Heq | Hneq].
    + inversion Hlookup. subst h. split; [now left | symmetry; exact Heq].
    + apply IH in Hlookup. destruct Hlookup as [Hin Hlevel].
      split; [now right | exact Hlevel].
Qed.

Lemma history_lookup_level_complete : forall H n h,
  history_levels_ok H -> In h H -> snd h = n ->
  history_lookup_level n H = Some h.
Proof.
  induction H as [|[G k] H IH]; intros n [Gh kh] Hlevels Hin Hlevel.
  - contradiction.
  - simpl in Hlevels. destruct Hlevels as [Hk Hlevels].
    simpl. destruct Hin as [Hin | Hin].
    + inversion Hin. subst Gh kh. simpl in Hlevel. subst n.
      destruct (Nat.eq_dec k k); [reflexivity | contradiction].
    + destruct (Nat.eq_dec n k) as [Hnk | Hnk].
      * pose proof (@history_level_le_length H Gh kh Hlevels Hin) as Hbound.
        simpl in Hlevel, Hbound. lia.
      * apply (IH n (Gh, kh) Hlevels Hin Hlevel).
Qed.

Lemma history_lookup_level_exists : forall H n,
  history_levels_ok H -> 1 <= n <= length H ->
  exists h, history_lookup_level n H = Some h.
Proof.
  intros H n Hlevels Hrange.
  destruct (@history_entry_at_level_unique H n Hlevels Hrange)
    as [h [[Hin Hsnd] _]].
  exists h. apply history_lookup_level_complete with (H := H); assumption.
Qed.

Lemma history_lookup_level_unique : forall H n h1 h2,
  history_levels_ok H ->
  history_lookup_level n H = Some h1 ->
  history_lookup_level n H = Some h2 -> h1 = h2.
Proof. intros H n h1 h2 _ H1 H2. rewrite H1 in H2. now inversion H2. Qed.

Definition seqt_eqdec (s t : doseqt) : {s = t} + {s <> t}.
Proof.
decide equality; apply list_eq_dec. apply nnf_eqdec. intros [a1 b1] [a2 b2]. 
decide equality. apply Nat.eq_dec. apply list_eq_dec. apply nnf_eqdec. apply nnf_eqdec.
Defined.

Record regular (s : doseqt) : Prop :=
{ nodup_H     : NoDupA ( @eqset nnf) (map fst (s_H s));
  G_incl_R    : incl (s_G s) (cl_list (s_R s));
  H_incl_R : forall G, In G (s_H s) -> incl (fst G) (cl_list (s_R s));
 }.

Lemma history_capacity_bound : forall s,
  regular s ->
  length (s_H s) <= length (power_set (cl_list (s_R s))).
Proof.
  intros s Hregular.
  rewrite <- map_length with (f := @fst (list nnf) nat) (l := s_H s).
  apply (@NoDupA_set_incl_length nnf nnf_eqdec).
  - exact (nodup_H Hregular).
  - intros G HG.
    apply InA_alt in HG.
    destruct HG as [G0 [HeqG HG0]].
    apply incl_inset_power_set.
    + exact nnf_eqdec.
    + intros phi Hphi.
      pose proof ((proj1 HeqG) phi Hphi) as Hphi0.
      apply in_map_iff in HG0.
      destruct HG0 as [h [Hfst HinH]].
      apply (H_incl_R Hregular h HinH).
      rewrite Hfst. exact Hphi0.
Qed.

Definition rdoseqt := {s | regular s}.  

Record well_formed_seqt (s : doseqt) : Prop :=
{ wf_regular : regular s;
  wf_history_levels : history_levels_ok (s_H s) }.

Definition wdoseqt := {s | well_formed_seqt s}.

Record upseqt :=
{ s_mrk : bool;
  s_uev : list (nnf * nat)}.

Definition upseqt_eqdec (x y : upseqt) : {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply list_eq_dec. intros [a1 b1] [a2 b2].
    decide equality.  apply Nat.eq_dec. apply nnf_eqdec.
  - apply Bool.bool_dec.
Defined.

Definition full_seqt : Set := doseqt * upseqt.

Definition full_seqt_eqdec (x y : full_seqt) : {x = y} + {x <> y}.
Proof.
  decide equality. apply upseqt_eqdec. apply seqt_eqdec.
Defined.

Definition df_seqt : doseqt :=
  {| s_G := []; s_H := []; s_R := [] |}.

Definition df_upseqt : upseqt := {| s_uev :=[]; s_mrk := false |}.

Definition df_fseqt := (df_seqt, df_upseqt).



Definition alpha_child (phi : nnf) (s : doseqt) : doseqt :=
{|
  s_G := nnf_alpha1 phi :: nnf_alpha2 phi :: remove_nnf phi (s_G s);
  s_H := s_H s;
  s_R := s_R s
|}.

Definition get_alpha_seqt (s : doseqt) :
  {phi : nnf | In phi (s_G s) /\ nnf_isalpha phi} +
  {forall phi, In phi (s_G s) -> ~ nnf_isalpha phi}.
Proof.
destruct (get_alpha (s_G s)) as [phi|H]; [now left | now right].
Defined.


Theorem alpha_child_pseqt [phi : nnf] (Hphi : nnf_isalpha phi)
  (ss : rdoseqt) (Hin : In phi (s_G (`ss))) :
    regular (alpha_child phi (`ss)).
Proof.
destruct ss as [s pse]. simpl in Hin |- *. constructor.
- simpl. apply (nodup_H pse).
- simpl.
  destruct (@in_cl_list_alpha phi (s_R s) Hphi) as [Ha1 Ha2].
  { apply (G_incl_R pse). assumption. }
  intros psi H. destruct H as [H|[H|H]];
  try (rewrite <- H; assumption).
  apply (G_incl_R pse). apply in_remove with nnf_eqdec phi.
  assumption.
- simpl. apply (H_incl_R pse).
Qed.

Definition alpha_child_sseqt [phi : nnf] (Hphi : nnf_isalpha phi)
  (ss : rdoseqt) (Hin : In phi (s_G (`ss))) : rdoseqt :=
  exist _ (alpha_child phi (`ss)) (alpha_child_pseqt Hphi ss Hin).

Definition beta1_child (phi : nnf) (s : doseqt) : doseqt :=
{|
  s_G := nnf_beta1 phi :: remove_nnf phi (s_G s);
  s_H := s_H s;
  s_R := s_R s
|}.

Definition beta2_child (phi : nnf) (s : doseqt) : doseqt :=
{|
  s_G := nnf_beta2 phi :: remove_nnf phi (s_G s);
  s_H := s_H s;
  s_R := s_R s
|}.

Definition get_beta_seqt (s : doseqt) :
  {phi : nnf | In phi (s_G s) /\ nnf_isbeta phi} +
  {forall phi, In phi (s_G s) -> ~ nnf_isbeta phi}.
Proof.
destruct (get_beta (s_G s)) as [phi|H]; [now left | now right].
Defined.

Theorem beta1_child_pseqt [phi : nnf] (Hphi : nnf_isbeta phi)
  (ss : rdoseqt) (Hin : In phi (s_G (`ss))) :
    regular (beta1_child phi (`ss)).
Proof.
destruct ss as [s pse]. simpl in Hin |- *. constructor.
- simpl. apply (nodup_H pse).
- simpl.
  destruct (@in_cl_list_beta phi (s_R s) Hphi) as [Ha1 Ha2].
  { apply (G_incl_R pse). apply Hin. }
  intros psi H. destruct H as [H|H]; try (rewrite <- H; assumption).
  apply (G_incl_R pse). apply in_remove with nnf_eqdec phi.
  assumption.
- simpl. apply (H_incl_R pse).
Qed.

Theorem beta2_child_pseqt [phi : nnf] (Hphi : nnf_isbeta phi)
  (ss : rdoseqt) (Hin : In phi (s_G (`ss))) :
    regular (beta2_child phi (`ss)).
Proof.
destruct ss as [s pse]. simpl in Hin |- *. constructor.
- simpl. apply (nodup_H pse).
- simpl.
  destruct (@in_cl_list_beta phi (s_R s) Hphi) as [Ha1 Ha2].
  { apply (G_incl_R pse). apply Hin. }
  intros psi H. destruct H as [H|H]; try (rewrite <- H; assumption).
  apply (G_incl_R pse). apply in_remove with nnf_eqdec phi.
  assumption.
- simpl. apply (H_incl_R pse).
Qed.

Definition beta1_child_sseqt [phi : nnf] (Hphi : nnf_isbeta phi)
  (ss : rdoseqt) (Hin : In phi (s_G (`ss))) : rdoseqt :=
  exist _ (beta1_child phi (`ss)) (beta1_child_pseqt Hphi ss Hin).

Definition beta2_child_sseqt [phi : nnf] (Hphi : nnf_isbeta phi)
  (ss : rdoseqt) (Hin : In phi (s_G (`ss))) : rdoseqt :=
  exist _ (beta2_child phi (`ss)) (beta2_child_pseqt Hphi ss Hin).



Definition get_contra : forall G : list nnf,
  {s : string | In (var s) G /\ In (neg s) G} +
  {forall s, In (var s) G -> ~ In (neg s) G}.
Proof.
induction G as [|phi G'].
- right. simpl. tauto.
- destruct IHG' as [Hl|Hr].
  * left. destruct Hl as [n Hn].
    exists n. split; simpl; right; tauto.
  * destruct phi as [m|m| | | | | | | |]; try (
    right; intros n H; destruct H as [H|H]; [discriminate|(
    specialize (Hr n H); intro H0; destruct H0;
    [discriminate|contradiction])]).
    + destruct (in_dec nnf_eqdec (neg m) G') as [Hin|Hnin].
     -- left. exists m. split; [(now left)|(now right)].
     -- right. intros n H. destruct H as [H|H].
       ** injection H. intro Heq. rewrite <- Heq. intro Hctr.
          destruct Hctr; [discriminate|contradiction].
       ** specialize (Hr n H). intro Hctr.
          destruct Hctr; [discriminate|contradiction].
    + destruct (in_dec nnf_eqdec (var m) G') as [Hin|Hnin].
     -- left. exists m. split; [(now right)|(now left)].
     -- right. intros n H. destruct H as [H|H]; try discriminate.
        destruct (string_dec m n) as [Heq|Hneq].
       ** rewrite <- Heq in H. contradiction.
       ** specialize (Hr n H). intro Hctr. destruct Hctr as [Hctr|Hctr];
          try contradiction. injection Hctr. contradiction.
Defined.



Definition get_enext : forall G : list nnf,
  {exists phi, In (enext phi) G} + {forall phi, ~ In (enext phi) G}.
Proof.
induction G as [|phi G'].
- now right.
- destruct IHG' as [Hl|Hr].
  * left. destruct Hl as [psi Hin]. exists psi. now right.
  * destruct phi; try (right; intros psi H; specialize (Hr psi);
    destruct H; [discriminate|contradiction]).
    left. exists phi. now left.
Defined.

Definition get_anext : forall G : list nnf,
  {exists phi, In (anext phi) G} + {forall phi, ~ In (anext phi) G}.
Proof.
induction G as [|phi G'].
- now right.
- destruct IHG' as [Hl|Hr].
  * left. destruct Hl as [psi Hin]. exists psi. now right.
  * destruct phi; try (right; intros psi H; specialize (Hr psi);
    destruct H; [discriminate|contradiction]).
    left. exists phi. now left.
Defined.

Fixpoint unanext (G : list nnf) : list nnf :=
  match G with
  | []                => []
  | (anext phi) :: Gtl => phi :: unanext Gtl
  | _ :: Gtl           => unanext Gtl
  end.

Fixpoint unenext (G : list nnf) : list nnf :=
  match G with
  | []                => []
  | (enext phi) :: Gtl => phi :: unenext Gtl
  | _ :: Gtl           => unenext Gtl
  end.

Definition unnext_for (phi : nnf) (G : list nnf) : list nnf :=
  phi :: unanext G.


(* The empty-eventuality case needs a serial successor, not a fresh formula.
   [temporary_jump_child] below supplies that successor directly. *)
Definition D_rule (s : doseqt) : doseqt := s.

Lemma D_rule_regular : forall s, regular s -> regular (D_rule s).
Proof. intros s Hregular. exact Hregular. Qed.

Lemma D_rule_H : forall s, s_H (D_rule s) = s_H s.
Proof. reflexivity. Qed.

Lemma D_rule_R : forall s, s_R (D_rule s) = s_R s.
Proof. reflexivity. Qed.

Definition temporary_jump_child (s : doseqt) : list doseqt :=
  match unenext (s_G s) with
  | [] =>
      let Gchild := unanext (s_G s) in
      [{|
        s_G := Gchild;
        s_H := (Gchild, S (length (s_H s))) :: s_H s;
        s_R := s_R s
      |}]
  | L =>
      map
        (fun phi =>
          let Gchild := phi :: unanext (s_G s) in
          {|
            s_G := Gchild;
            s_H := (Gchild, S (length (s_H s))) :: s_H s;
            s_R := s_R s
          |})
        L
  end.

Definition not_blocked_Gamma (G : list nnf) (s : doseqt) : Prop :=
  ~ InA (@eqset nnf) G (map fst (s_H s)).

(* Candidate-level condition: [G] is a prospective child's Gamma and [s]
   is its parent.  Keep the old name for compatibility. *)
Definition candidate_unblocked (G : list nnf) (parent : doseqt) : Prop :=
  not_blocked_Gamma G parent.

(* Parent-level condition used before pushing the current Gamma to history. *)
Definition parent_unblocked (s : doseqt) : Prop :=
  ~ InA (@eqset nnf) (s_G s) (map fst (s_H s)).

Definition not_blocked_seqt (s : doseqt) : Prop :=
  match unenext (s_G s) with
  | [] =>
      not_blocked_Gamma (unanext (s_G s)) s
  | L =>
      forall phi,
        In phi L ->
        not_blocked_Gamma (phi :: unanext (s_G s)) s
  end.



Definition blocker_Gamma (D : list nnf) (s : doseqt) : Prop :=
  InA (@eqset nnf) D (map fst (s_H s)).

Definition get_blocker : forall (D : list nnf) (H : list ( (list nnf) * nat)),
  {h | In h H /\ eqset (fst h) D} +
  {~ InA (@eqset nnf) D (map fst H)}.
Proof.
induction H as [|(L, d) H'].
- now right.
- destruct IHH' as [Hl|Hr].
  * left. destruct Hl as [h Hh]. exists h. destruct Hh as [Hin Hsnd].
    split; [now right|assumption].
  * destruct (eqset_dec nnf_eqdec L D) as [Heq|Hneq].
    + left. exists (L, d). split; [now left|tauto].
    + right. simpl. intro Hin. inversion Hin.
     -- contradict Hneq. apply eqset_sym. assumption.
     -- contradiction.
Defined.

Definition get_blocker_G (D : list nnf) (s : doseqt) :
  {L | In L (s_H s) /\ eqset (fst L) D} + {not_blocked_Gamma D s}.
Proof.
  destruct (get_blocker D (s_H s)) as [[L HL]|Hnin].
  - left. exists L. assumption.
  - right. assumption.
Defined.

Definition get_parent_blocker (s : doseqt) :
  {h | In h (s_H s) /\ eqset (fst h) (s_G s)} +
  {parent_unblocked s} :=
  get_blocker_G (s_G s) s.

Lemma get_parent_blocker_correct : forall s,
  match get_parent_blocker s with
  | inleft blocked =>
      In (proj1_sig blocked) (s_H s) /\
      eqset (fst (proj1_sig blocked)) (s_G s)
  | inright _ => parent_unblocked s
  end.
Proof.
  intro s.
  destruct (get_parent_blocker s) as [blocked | Hunblocked].
  - exact (proj2_sig blocked).
  - exact Hunblocked.
Qed.

Definition jump_child_blocked
  (parent child : doseqt) : bool :=
  if get_blocker_G (s_G child) parent then
    true
  else
    false.

Definition jump_child (s : doseqt) : list doseqt :=
  filter
    (fun child => negb (jump_child_blocked s child))
    (temporary_jump_child s).

Lemma jump_child_blocked_false_iff : forall parent child,
  jump_child_blocked parent child = false <->
  candidate_unblocked (s_G child) parent.
Proof.
  intros parent child.
  unfold jump_child_blocked, candidate_unblocked.
  destruct (get_blocker_G (s_G child) parent) as [Hblocked | Hunblocked].
  - split.
    + discriminate.
    + intro Hunblocked. exfalso.
      apply Hunblocked.
      apply InA_alt.
      exists (fst (proj1_sig Hblocked)).
      split.
      * apply eqset_sym. exact (proj2 (proj2_sig Hblocked)).
      * apply in_map. exact (proj1 (proj2_sig Hblocked)).
  - split; intro H; [exact Hunblocked | reflexivity].
Qed.

Lemma jump_child_In_iff : forall parent child,
  In child (jump_child parent) <->
  In child (temporary_jump_child parent) /\
  candidate_unblocked (s_G child) parent.
Proof.
  intros parent child.
  unfold jump_child.
  rewrite filter_In.
  rewrite Bool.negb_true_iff.
  rewrite jump_child_blocked_false_iff.
  reflexivity.
Qed.

Lemma jump_child_In_temporary : forall parent child,
  In child (jump_child parent) -> In child (temporary_jump_child parent).
Proof. intros parent child H. apply jump_child_In_iff in H. exact (proj1 H). Qed.

Lemma jump_child_candidate_unblocked : forall parent child,
  In child (jump_child parent) ->
  candidate_unblocked (s_G child) parent.
Proof. intros parent child H. apply jump_child_In_iff in H. exact (proj2 H). Qed.

Lemma temporary_jump_child_history_shape : forall parent child,
  In child (temporary_jump_child parent) ->
  s_H child = (s_G child, S (length (s_H parent))) :: s_H parent.
Proof.
  intros parent child Hchild.
  unfold temporary_jump_child in Hchild.
  destruct (unenext (s_G parent)) as [|phi L].
  - simpl in Hchild. destruct Hchild as [Hchild | []]. subst child. reflexivity.
  - apply in_map_iff in Hchild.
    destruct Hchild as [psi [Hchild _]]. subst child. reflexivity.
Qed.


Lemma alpha_child_history_levels : forall s phi,
  history_levels_ok (s_H s) ->
  history_levels_ok (s_H (alpha_child phi s)).
Proof. intros s phi Hlevels. exact Hlevels. Qed.

Lemma beta1_child_history_levels : forall s phi,
  history_levels_ok (s_H s) ->
  history_levels_ok (s_H (beta1_child phi s)).
Proof. intros s phi Hlevels. exact Hlevels. Qed.

Lemma beta2_child_history_levels : forall s phi,
  history_levels_ok (s_H s) ->
  history_levels_ok (s_H (beta2_child phi s)).
Proof. intros s phi Hlevels. exact Hlevels. Qed.

Lemma D_rule_history_levels : forall s,
  history_levels_ok (s_H s) ->
  history_levels_ok (s_H (D_rule s)).
Proof. intros s Hlevels. exact Hlevels. Qed.

Lemma temporary_jump_child_history_levels : forall parent child,
  history_levels_ok (s_H parent) ->
  In child (temporary_jump_child parent) ->
  history_levels_ok (s_H child).
Proof.
  intros parent child Hlevels Hchild.
  rewrite (@temporary_jump_child_history_shape parent child Hchild).
  apply history_levels_ok_push. exact Hlevels.
Qed.

Lemma jump_child_history_levels : forall parent child,
  history_levels_ok (s_H parent) ->
  In child (jump_child parent) ->
  history_levels_ok (s_H child).
Proof.
  intros parent child Hlevels Hchild.
  apply temporary_jump_child_history_levels with (parent := parent).
  - exact Hlevels.
  - apply jump_child_In_temporary. exact Hchild.
Qed.

Lemma in_unenext_in_enext [G] :
  forall phi, In phi (unenext G) -> In (enext phi) G.
Proof.
induction G as [|psi Gtl].
- simpl. tauto.
- destruct psi;
  try (simpl; intros phi H; right; apply IHGtl; assumption).
  simpl. intros phi H. destruct H as [H|H].
  * rewrite H. now left.
  * right. apply IHGtl. assumption.
Qed.

Lemma in_unanext_in_anext [G] :
  forall phi, In phi (unanext G) -> In (anext phi) G.
Proof.
induction G as [|psi Gtl].
- simpl. tauto.
- destruct psi;
  try (simpl; intros phi H; right; apply IHGtl; assumption).
  simpl. intros phi H. destruct H as [H|H].
  * rewrite H. now left.
  * right. apply IHGtl. assumption.
Qed.

Lemma in_enext_in_unenext [G] :
  forall phi, In (enext phi) G -> In phi (unenext G).
Proof.
induction G as [|psi Gtl].
- simpl. tauto.
- destruct psi; try (simpl; intros phi H;
  destruct H; try discriminate; apply IHGtl; assumption).
  simpl. intros phi H. destruct H as [H|H].
  * injection H. tauto.
  * right. apply IHGtl. assumption.
Qed.

Lemma in_anext_in_unanext [G] :
  forall phi, In (anext phi) G -> In phi (unanext G).
Proof.
induction G as [|psi Gtl].
- simpl. tauto.
- destruct psi; try (simpl; intros phi H;
  destruct H; try discriminate; apply IHGtl; assumption).
  simpl. intros phi H. destruct H as [H|H].
  * injection H. tauto.
  * right. apply IHGtl. assumption.
Qed.

Record state_conditions (s : doseqt) : Prop :=
{ sc_no_contra : forall n, In (var n) (s_G s) -> ~ In (neg n) (s_G s);
  sc_no_alpha  : forall phi, In phi (s_G s) -> ~ nnf_isalpha phi;
  sc_no_beta   : forall phi, In phi (s_G s) -> ~ nnf_isbeta phi }.

Lemma jump_child_in_temporary_and_nodup_H
  (s : doseqt)
  (pse : regular s)
  (child : doseqt)
  (Hin : In child (jump_child s)) :
  In child (temporary_jump_child s) /\
  NoDupA (@eqset nnf) (map fst (s_H child)).
Proof.
 assert (Htemporary :
    In child (temporary_jump_child s)).
  {
    apply jump_child_In_temporary.
    exact Hin.
  }
  pose proof (jump_child_candidate_unblocked _ _ Hin) as Hunblocked.
  constructor.
  - exact Htemporary.
  - rewrite (@temporary_jump_child_history_shape s child Htemporary).
    simpl.
    constructor.
    + exact Hunblocked.
    + exact (nodup_H pse).
Qed.

Theorem jump_child_regular
  (ss : rdoseqt):
  Forall regular (jump_child (`ss)).
 destruct ss as [s pse].
  simpl.
  apply Forall_forall.
  intros child Hchild.

  pose proof
    (jump_child_in_temporary_and_nodup_H pse child Hchild)
    as [Htemporary Hnodup].

  destruct (unenext (s_G s)) as [|phi L] eqn:Hun.

  - unfold temporary_jump_child in Htemporary.
    rewrite Hun in Htemporary.
    simpl in Htemporary.
    destruct Htemporary as [Hchild' | []].
    subst child.

    assert (HG :
      forall xi,
        In xi (unanext (s_G s)) ->
        In xi (cl_list (s_R s))).
    {
      intros xi Hxi.
      apply in_cl_list_anext.
      apply (G_incl_R pse).
      apply in_unanext_in_anext.
      exact Hxi.
    }

    constructor.
    + exact Hnodup.
    + exact HG.
    + intros l Hl.
      simpl in Hl.
      destruct Hl as [Hl | Hl].
      * subst l.
        simpl.
        exact HG.
      * apply (H_incl_R pse).
        exact Hl.

  - unfold temporary_jump_child in Htemporary.
    rewrite Hun in Htemporary.
    apply in_map_iff in Htemporary.
    destruct Htemporary as [psi [Hchild' Hpsi]].
    subst child.

    assert (HG :
      forall xi,
        In xi (psi :: unanext (s_G s)) ->
        In xi (cl_list (s_R s))).
    {
      intros xi Hxi.
      destruct Hxi as [Hxi | Hxi].

      - subst xi.
        apply in_cl_list_enext.
        apply (G_incl_R pse).
        apply in_unenext_in_enext.
        rewrite Hun.
        exact Hpsi.

      - apply in_cl_list_anext.
        apply (G_incl_R pse).
        apply in_unanext_in_anext.
        exact Hxi.
    }

    constructor.
    + exact Hnodup.
    + exact HG.
    + intros l Hl.
      simpl in Hl.
      destruct Hl as [Hl | Hl].
      * subst l.
        simpl.
        exact HG.
      * apply (H_incl_R pse).
        exact Hl.
Qed.

Lemma alpha_child_well_formed : forall s phi,
  nnf_isalpha phi -> In phi (s_G s) -> well_formed_seqt s ->
  well_formed_seqt (alpha_child phi s).
Proof.
  intros s phi Halpha Hin [Hregular Hlevels]. constructor.
  - exact (@alpha_child_pseqt phi Halpha (exist _ s Hregular) Hin).
  - apply alpha_child_history_levels. exact Hlevels.
Qed.

Lemma beta1_child_well_formed : forall s phi,
  nnf_isbeta phi -> In phi (s_G s) -> well_formed_seqt s ->
  well_formed_seqt (beta1_child phi s).
Proof.
  intros s phi Hbeta Hin [Hregular Hlevels]. constructor.
  - exact (@beta1_child_pseqt phi Hbeta (exist _ s Hregular) Hin).
  - apply beta1_child_history_levels. exact Hlevels.
Qed.

Lemma beta2_child_well_formed : forall s phi,
  nnf_isbeta phi -> In phi (s_G s) -> well_formed_seqt s ->
  well_formed_seqt (beta2_child phi s).
Proof.
  intros s phi Hbeta Hin [Hregular Hlevels]. constructor.
  - exact (@beta2_child_pseqt phi Hbeta (exist _ s Hregular) Hin).
  - apply beta2_child_history_levels. exact Hlevels.
Qed.

Lemma D_rule_well_formed : forall s,
  well_formed_seqt s -> well_formed_seqt (D_rule s).
Proof.
  intros s [Hregular Hlevels]. constructor.
  - apply D_rule_regular. exact Hregular.
  - apply D_rule_history_levels. exact Hlevels.
Qed.

Lemma jump_child_well_formed : forall parent child,
  well_formed_seqt parent ->
  In child (jump_child parent) -> well_formed_seqt child.
Proof.
  intros parent child [Hregular Hlevels] Hchild. constructor.
  - pose proof
      (jump_child_regular (exist _ parent Hregular)) as Hall.
    rewrite Forall_forall in Hall. exact (Hall child Hchild).
  - apply jump_child_history_levels with (parent := parent); assumption.
Qed.

(* Compatibility wrapper: state conditions are not needed for regularity. *)
Theorem jump_child_pseqt
  (ss : rdoseqt) :
  Forall regular (jump_child (`ss)).
Proof.
  exact (jump_child_regular ss).
Qed.


Definition rdoseqt_list :=
  { children : list doseqt |
      Forall regular children }.

Definition jump_child_sseqt (ss : rdoseqt) : rdoseqt_list :=
  exist _ (jump_child (`ss)) (jump_child_regular ss).

Fixpoint get_eunts (G : list nnf) : list nnf :=
  match G with
  | []             => []
  | eunt phi psi :: Gtl => eunt phi psi :: get_eunts Gtl
  | _ :: Gtl       => get_eunts Gtl
  end.

Fixpoint get_aunts (G : list nnf) : list nnf :=
  match G with
  | []             => []
  | aunt phi psi :: Gtl => aunt phi psi :: get_aunts Gtl
  | _ :: Gtl       => get_aunts Gtl
  end.

Lemma eunt_in_get_eunts : forall phi psi G,
  In (eunt phi psi) G -> In (eunt phi psi) (get_eunts G).
Proof.
intros phi psi. induction G as [|xi G].
- contradiction.
- intro H. destruct H as [H|H].
  + rewrite H. simpl. now left.
  + destruct xi; simpl; try apply (IHG H).
    right. apply (IHG H).
Qed.

Lemma aunt_in_get_aunts : forall phi psi G,
  In (aunt phi psi) G -> In (aunt phi psi) (get_aunts G).
Proof.
intros phi psi. induction G as [|xi G].
- contradiction.
- intro H. destruct H as [H|H].
  + rewrite H. simpl. now left.
  + destruct xi; simpl; try apply (IHG H).
    right. apply (IHG H).
Qed.

Lemma eunt_only_get_eunts [G] : forall xi, In xi (get_eunts G) ->
  exists phi psi, xi = eunt phi psi.
Proof.
induction G as [|chi Gtl].
- simpl. tauto.
- intros xi Hxi. destruct chi; simpl in Hxi;
  try (apply (IHGtl _ Hxi)).
  destruct Hxi as [Hxi|Hxi].
  * exists chi1, chi2. rewrite Hxi. reflexivity.
  * apply IHGtl. assumption.
Qed.

Lemma aunt_only_get_aunts [G] : forall xi, In xi (get_aunts G) ->
  exists phi psi, xi = aunt phi psi.
Proof.
induction G as [|chi Gtl].
- simpl. tauto.
- intros xi Hxi. destruct chi; simpl in Hxi;
  try (apply (IHGtl _ Hxi)).
  destruct Hxi as [Hxi|Hxi].
  * exists chi1, chi2. rewrite Hxi. reflexivity.
  * apply IHGtl. assumption.
Qed.


Lemma get_eunts_in : forall G xi, In xi (get_eunts G) -> In xi G.
Proof.
induction G as [|phi G].
- simpl. tauto.
- intros xi Hxi. simpl in Hxi. destruct phi;
  try (right; apply IHG; assumption).
  destruct Hxi as [Hxi|Hxi].
  + now left.
  + right. apply IHG. assumption.
Qed.

Lemma get_aunts_in : forall G xi, In xi (get_aunts G) -> In xi G.
Proof.
induction G as [|phi G].
- simpl. tauto.
- intros xi Hxi. simpl in Hxi. destruct phi;
  try (right; apply IHG; assumption).
  destruct Hxi as [Hxi|Hxi].
  + now left.
  + right. apply IHG. assumption.
Qed.
