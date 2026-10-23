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
  s_H : list ((list nnf * nat));(*HCr*)
  s_R : list nnf }(*Gamma of previous node*).

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

Definition rdoseqt := {s | regular s}.  

Record upseqt :=
{ s_mrk : bool;
  s_uev : list(nnf * nat)}.

Definition upseqt_eqdec (s t : upseqt) : {s = t} + {s <> t}.
Proof.
decide equality. apply list_eq_dec. intros [a1 b1] [a2 b2]. 
decide equality. apply Nat.eq_dec. apply nnf_eqdec.
decide equality. 
Defined.

Definition full_seqt : Set := doseqt * upseqt.

Definition full_seqt_eqdec (fs1 fs2 : full_seqt) : {fs1 = fs2} + {fs1 <> fs2}.
Proof.
decide equality; [apply upseqt_eqdec | apply seqt_eqdec].
Defined.

Definition df_seqt : doseqt :=
  {| s_G := []; s_H := []; s_R := [] |}.

Definition df_upseqt : upseqt := {| s_uev := []; s_mrk := false |}.

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

Definition jump_child (s : doseqt) : list doseqt :=
  match unenext (s_G s) with
  | [] =>
      [{|
        s_G := unanext (s_G s);
        s_H := (s_G s,length (s_H s)) :: s_H s;
        s_R := s_R s
      |}]
  | L =>
      map
        (fun phi =>
          {|
            s_G := phi :: unanext (s_G s);
            s_H := (s_G s,length (s_H s)) :: s_H s;
            s_R := s_R s
          |})
        L
  end.

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

Definition not_blocked_Gamma (G : list nnf) (s : doseqt) : Prop :=
  ~ InA (@eqset nnf) G (map fst (s_H s)).

Definition not_blocked_seqt (s : doseqt) : Prop :=
  match unenext (s_G s) with
  | [] =>
      not_blocked_Gamma (unanext (s_G s)) s
  | L =>
      forall phi,
        In phi L ->
        not_blocked_Gamma (phi :: unanext (s_G s)) s
  end.

Record state_conditions (s : doseqt) : Prop :=
{ sc_no_contra : forall n, In (var n) (s_G s) -> ~ In (neg n) (s_G s);
  sc_no_alpha  : forall phi, In phi (s_G s) -> ~ nnf_isalpha phi;
  sc_no_beta   : forall phi, In phi (s_G s) -> ~ nnf_isbeta phi }.


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

Theorem jump_child_pseqt
  (ss : rdoseqt)
  (sc : state_conditions (`ss))
  (nb : not_blocked_seqt (`ss))
  (parent_not_in_H :
    ~ InA (@eqset nnf) (s_G (`ss)) (map fst (s_H (`ss)))) :
  Forall regular (jump_child (`ss)).
Proof.
  destruct ss as [s pse].
  simpl in sc, nb |- *.
  unfold jump_child.
  destruct (unenext (s_G s)) as [|phi L] eqn:Hun.
  - simpl.
    constructor.
    + simpl.
      constructor.
      -- simpl. constructor.
      --- simpl in parent_not_in_H. exact parent_not_in_H.
      --- exact (nodup_H pse). 
      -- 
      * intros xi Hxi. apply in_cl_list_anext.
        apply (G_incl_R pse). apply in_unanext_in_anext.
        assumption.
      -- intros l Hl. destruct Hl as [Hl | Hl].
        --- rewrite <- Hl. apply (G_incl_R pse).
        --- apply (H_incl_R pse). assumption.
    + constructor.
  - apply Forall_forall.
    intros child Hchild.
    apply in_map_iff in Hchild.
    destruct Hchild as [psi [Hchild Hpsi]].
    rewrite <- Hchild.
    simpl. constructor.
    -- constructor.
     + simpl in parent_not_in_H. exact parent_not_in_H.
     + exact (nodup_H pse).
    -- intros xi Hxi.
      destruct Hxi as [Hxi | Hxi].
      + rewrite <- Hxi.
        apply in_cl_list_enext.
        apply (G_incl_R pse).
        apply in_unenext_in_enext.
        rewrite Hun.
        assumption.
      + apply in_cl_list_anext.
        apply (G_incl_R pse).
        apply in_unanext_in_anext.
        assumption.
    -- intros l Hl.
      destruct Hl as [Hl | Hl].
     + rewrite <- Hl.
       intros xi Hxi.
       apply (G_incl_R pse).
        assumption.
    + apply (H_incl_R pse).
      assumption.
Qed.

Definition all_jump_children_regular
  (ss : rdoseqt)
  (sc : state_conditions (`ss))
  (nb : not_blocked_seqt (`ss))
  (parent_not_in_H :
    ~ InA (@eqset nnf) (s_G (`ss)) (map fst (s_H (`ss))))
  : Forall regular (jump_child (`ss)) :=
  jump_child_pseqt ss sc nb parent_not_in_H.

Definition rdoseqt_list :=
  { children : list doseqt |
      Forall regular children }.

Definition jump_child_sseqt
  (ss : rdoseqt)
  (sc : state_conditions (`ss))
  (nb : not_blocked_seqt (`ss))
  (parent_not_in_H :
    ~ InA (@eqset nnf) (s_G (`ss)) (map fst (s_H (`ss))))
  : rdoseqt_list :=
  exist _ (jump_child (`ss))
    (jump_child_pseqt ss sc nb parent_not_in_H).
    
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