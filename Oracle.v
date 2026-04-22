(** * Introduction
    [Oracle.v] contains the formalization of the oracle protocol and theorems in the Orb Oracle paper.

    This file is also documented and organized to follow the paper.

    Sections and subsections directly paralleling the paper are indexed, e.g. "(3): Datatypes, Parameters" refers to "Section 3" in the paper.

    Some sections or subsections are formalization specific and are not indexed relative to the paper.

    The table of contents [toc.html] is included for convenience.
 *)

(** * Imports *)

Require Import Reals.

Require ZArith.
Require Import List.
Require Import String.
Require Import Lia.
Require Import Lra.

Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.FSets.FMapFacts.
Local Open Scope R_scope.

(** * (3): Datatypes, Parameters
    Paper: Section 3, Protocol Specification

    This section details the datatypes and parameters used in the formalization of Orb.

    Most of the oracle parameters and arguments to time-dependent functions are defined as non-negative real numbers in the paper.

    The majority of them are defined as [R], most importantly timestamps, user weights, user/oracle token balances, and user-submitted oracle values.
 *)

(** ** Numbers *)

Definition Rpos : Type := {x : R | 0 < x}.

Lemma proj1_rpos_pos : forall x : Rpos, 0 < proj1_sig x.
Proof.
  intros. destruct x. simpl. apply r.
Qed.

(** Summing real number lists *)

Definition sum_list_R (l : list R) : R :=
  fold_right Rplus 0 l.

(** ** Boolean comparisons for [R]
    We define alternative boolean comparisons for [R] since the oracle operations which uses conditions are defined in the functional language of Coq.
 *)

Definition Rleb (x y : R) : bool :=
  match Rle_dec x y with
  | left _ => true
  | right _ => false
  end.

Definition Rltb (x y : R) : bool :=
  match Rlt_dec x y with
  | left _  => true
  | right _ => false
  end.

Definition Rgeb (x y : R) : bool :=
  Rleb y x.

Definition Rgtb (x y : R) : bool :=
  Rltb y x.

Infix "<=b" := Rleb (at level 70).
Infix "<b"  := Rltb (at level 70).
Infix ">=b" := Rgeb (at level 70).
Infix ">b"  := Rgtb (at level 70).

(** ** Users and UserSets
    [User]s are defined as [nat] for simplicity.
    The global universe of users [Users] is defined as a list instead of a set.
    This is because we define our own summation over real numbers [sum_list_R], which is simplest to do as mapping addition over a list.
 *)

Definition User : Type := nat.
Definition UserSet := list User.

Parameter Users : UserSet.
Axiom Users_NoDup : NoDup Users.

(** UserSets *)

Definition mem_user (u : User) (s : UserSet) : bool :=
  existsb (fun x => Nat.eqb x u) s.

Lemma mem_user_In :       (* [TODO]: del *)
  forall (u : User) (s : UserSet),
    mem_user u s = true <-> In u s.
Proof.
  unfold mem_user.
  intros.
  rewrite existsb_exists.
  split.
  - intros [x []].
    apply EqNat.beq_nat_true_stt in H0.
    subst.
    apply H.
  - intros.
    exists u.
    split; auto.
    apply Nat.eqb_refl.
Qed.


Lemma negb_mem_user_not_In : (* [TODO]: del *)
  forall (u : User) (s : UserSet),
    mem_user u s = false <-> not (In u s).
Proof.
  intros.
  split.
  - unfold not.
    intros.
    apply mem_user_In in H0.
    rewrite H in H0.
    discriminate.
  - intros Hnotin.
    destruct (mem_user u s) eqn:Hmem.
    -- apply mem_user_In in Hmem.
       unfold not in Hnotin. apply Hnotin in Hmem.
       destruct Hmem.
    -- reflexivity.
Qed.

(** ** Time
    Timestamps are used in time-dependent functions used by operations in the oracle, most notably for decay.
    Timestamps are a non-negative real number in the paper, but we use [R] for simplicity.
 *)

Definition timestamp : Type := R.

(** ** Weights, Balances and Values
    Like time, weights, balances and values are a non-negative real number in the paper, but we use [R] for simplicity.
    When simpler and needed in the proof, the non-negativity of oracle parameters that are weights, balances and values.
 *)

Definition weight : Type := R.

Definition value : Type := R.

Definition balance : Type := R.

Definition history : Type := list (timestamp * value * value).

(** ** Maps
    Maps are from Coq's [FMapList].
    They are used for the oracle's mappings from user to timestamp/weight/balances/values/UserSet.
*)

Module UserOT := Nat_as_OT.

Module UserMap := FMapList.Make(UserOT).

Module UMFacts := WFacts_fun UserOT UserMap.

(** [User] to [elt],  fmaps *)

Definition getR (u : User) (m : UserMap.t R) : R :=
  match UserMap.find u m with
  | Some x => x
  | None => 0
  end.

Definition getBool (u : User) (m : UserMap.t bool) : bool :=
  match UserMap.find u m with
  | Some x => x
  | None => false
  end.

Definition setR (u : User) (v : R) (m : UserMap.t R) : UserMap.t R :=
  UserMap.add u v m.

Definition setBool (u : User) (v : bool) (m : UserMap.t bool) : UserMap.t bool :=
  UserMap.add u v m.

Definition addR (u : User) (dv : R) (m : UserMap.t R) : UserMap.t R :=
  setR u (getR u m + dv) m.

Definition UMap_forall {elt : Type} (pred : User * elt -> Prop) (um : UserMap.t elt) : Prop :=
  Forall pred (UserMap.elements um).

Lemma getR_setR_eq :
  forall m u v,
    getR u (setR u v m) = v.
Proof.
  intros. unfold getR, setR.
  erewrite UserMap.find_1.
  - reflexivity.
  - apply UserMap.add_1. reflexivity.
Qed.

Lemma getR_setR_neq :
  forall m u u' v,
    u' <> u ->
    getR u' (setR u v m) = getR u' m.
Proof.
  intros. unfold getR, setR.
  rewrite UMFacts.add_neq_o by auto.
  reflexivity.
Qed.

(** [UserPair] fmaps
    Used for the blacklist and whitelist oracle operation.
 *)

Module UserPairOT := PairOrderedType UserOT UserOT.
Module UserPairMap := FMapList.Make(UserPairOT).

Definition getR2 (u v : User) (m : UserPairMap.t R) : R :=
  match UserPairMap.find (u, v) m with
  | Some x => x
  | None => 0
  end.

Definition setR2 (u v : User) (x : R) (m : UserPairMap.t R) : UserPairMap.t R :=
  UserPairMap.add (u, v) x m.

Definition addR2 (u v : User) (dx : R) (m : UserPairMap.t R) : UserPairMap.t R :=
  setR2 u v (getR2 u v m + dx) m.

Definition UPairMap_forall {elt : Type}
  (pred : (User * User) * elt -> Prop)
  (upm : UserPairMap.t elt) : Prop :=
  Forall pred (UserPairMap.elements upm).

(** [UserSet] fmaps
    Used for the blacklist and whitelist oracle operation.
 *)

Definition getUserSet (u : User) (m : UserMap.t UserSet) : UserSet :=
  match UserMap.find u m with
  | Some s => s
  | None => nil
  end.

Definition setUserSet (u : User) (s : UserSet) (m : UserMap.t UserSet)
  : UserMap.t UserSet :=
  UserMap.add u s m.

Definition addUser (x : User) (s : UserSet) : UserSet :=
  x :: s.

(** ** (Equation 1): Parameters

    These are immutable parameters chosen by the oracle creator at the moment of deployment.
 *)

Parameter h : Rpos.                    (* half-life constant *)

Parameter q : R.                       (* quorum constant *)

Parameter Delta_dep : timestamp.       (* deposit locking period *)

Parameter Delta_wd : timestamp.        (* deposit locking period *)

Parameter alpha : R.                   (* reward factor *)

(** ** (Equation 2): State

    These include the parameters, plus the state variables that change as users interact with the oracle.
    The [State] record contains balances and the [OracleState], which contain amongst others the [GovernanceState].
    The distinction between these records is arbitrary, so we simply mirror the paper.
 *)

(** *** Governance State *)

Record GovernanceState := {
    B : UserMap.t bool;                (* blacklist indicator for each user *)
    V_black : UserMap.t weight;        (* accumulated blacklist weight *)
    V_white : UserMap.t weight;        (* accumulated whitelist weight *)
    M_black : UserMap.t UserSet;       (* set of targets each voter has blacklisted *)
    M_white : UserMap.t UserSet;       (* set of targets each voter has whitelisted *)
    W_black : UserPairMap.t weight;    (* per target blacklist stored weight *)
    W_white : UserPairMap.t weight;    (* per target whitelist stored weight *)
  }.

(** *** Oracle State *)

Record OracleState := {
    L_l    : UserMap.t balance;        (* locked token balances of users *)
    L_f    : UserMap.t balance;        (* unlocked token balances of users *)
    T_dep  : UserMap.t timestamp;      (* last deposit timestamp of users *)
    T_op   : UserMap.t timestamp;      (* last operation timestamp of users *)
    P_user : UserMap.t value;          (* last reported value of each submitter *)
    W_user : UserMap.t weight;         (* last submission weight of users *)
    T_user : UserMap.t timestamp;      (* last submission time of users *)
    pbar   : value;                    (* stored aggregated value *)
    ptilde : value;                    (* latest submitted value *)
    Q      : weight;                   (* stored aggregate weight *)
    Phist  : history;                  (* time-ordered value history. Renamed from curly P *)
    t_sub  : timestamp;                (* last value submission time*)
    t_last : timestamp;                (* last oracle interaction time *)
    L_tot  : balance;                  (* current total of deposited tokens *)
    G      : GovernanceState           (* governance state *)
  }.

(** *** State *)

Record State := {
    V : OracleState;                   (* oracle state *)
    B_user_w : UserMap.t balance;      (* external oracle token balance of users *)
    B_user_r : UserMap.t balance;      (* external reward token balance of users *)
    B_oracle_w : balance;              (* oracle token balance of oracle *)
    B_oracle_r : balance;              (* reward token balance of oracle *)
  }.

(** ** Well-formedness of a state
    So far, the parameters and state are mostly syntactic in the sense that they are definitions of what the state is, but not how it behaves.

    For instance, we would like the behavior/invariant that [B_oracle_w] is non-negative, amongst others, since in the paper, it is defined as a non-negative real, yet we kept it as [R].
    We might also want other behavior/invariants such as the maps being total, or that the last user submission time should be less than or equal to the last interaction (any operation including submission) time.
    Some parameters/fields are not touched by the proof of the theorems at all, such as [Phist], but we might still expect for instance that [Phist], the time-ordered value history updated at every submission, remains time-ordered with every submission.

    A comprehensive approach would have been to instead define a predicate called "well-formedness of a state" consisting of all the invariants we expect or want, and then prove the invariants hold over a [Run] of operations.
    We attempted this, but since our focus was to prove the theorems in the paper about the oracle, we instead decided to be more pragmatic and (minimally) assume simple invariants as needed.

    We retain the preliminary code defining a well-formed state here - but they are not used in the theorems.
 *)

Definition UPairMap_nonneg (upm : UserPairMap.t R) : Prop :=
  UPairMap_forall (fun ke =>
    match ke with
    | (_, e) => 0 <= e
    end) upm.

Definition UMap_nonneg (um : UserMap.t R) :=
  UMap_forall (fun ke => match ke with | (_, e) => 0 <= e end) um.

Definition all_user_pairs_keys {elt : Type} (U : UserSet) (upm : UserPairMap.t elt) : Prop :=
  forall u1 u2, In u1 U -> In u2 U -> UserPairMap.In (u1, u2) upm.

Definition all_users_keys {elt : Type} (U : UserSet) (um : UserMap.t elt) :=
  forall u, In u U -> UserMap.In u um.

Definition wf_governance (U : UserSet) (G : GovernanceState) : Prop :=
  (* Totality of UserMaps on U *)
  (* UserMaps must have an entry for every user in U *)
  all_users_keys U (B G)             /\
  all_users_keys U (V_black G)       /\
  all_users_keys U (V_white G)       /\
  all_users_keys U (M_black G)       /\
  all_users_keys U (M_white G)       /\
  (* UserPairMaps must have an entry for every user pair in U * U *)
  all_user_pairs_keys U (W_black G)  /\
  all_user_pairs_keys U (W_white G)  /\
  (* UserMap.t weight must have nonnegative values *)
  UMap_nonneg (V_black G)            /\
  UMap_nonneg (V_white G)            /\
  UPairMap_nonneg (W_black G)        /\
  UPairMap_nonneg (W_white G)
  (* [maybe] M_black(u) and M_black(u) partitions U for every u in U *)
  (* TODO: other predicates *)
.

Definition wf_oracle (U : UserSet) (st : OracleState) : Prop :=
  wf_governance U (G st) /\

  (* UserMaps must have an entry for every user in U *)
  all_users_keys U (L_l st) /\
  all_users_keys U (L_f st) /\
  all_users_keys U (T_dep st) /\
  all_users_keys U (T_op st) /\
  all_users_keys U (P_user st) /\
  all_users_keys U (W_user st) /\
  all_users_keys U (T_user st) /\

  (* UserMap.t weight/balance/timestamp/value must have nonnegative values *)
  UMap_nonneg (L_l st) /\
  UMap_nonneg (L_f st) /\
  UMap_nonneg (T_dep st) /\
  UMap_nonneg (T_op st) /\
  UMap_nonneg (P_user st) /\
  UMap_nonneg (W_user st) /\
  UMap_nonneg (T_user st) /\

  (* variables weight/balance/timestamp/value must have nonnegative values *)
  0 <= pbar st /\
  0 <= ptilde st /\
  0 <= Q st /\
  0 <= t_sub st /\
  0 <= t_last st /\
  0 <= L_tot st /\

  (* total deposited tokens equals sum of (locked+free) balance *)
  (forall u, In u U ->
      getR u (L_l st) + getR u (L_f st) <= L_tot st) /\

  (* last submission time shouldn't be after last interaction time *)
  t_sub st <= t_last st.

  (* TODO: other predicates *)

Definition wf_state (U : UserSet) (St : State) : Prop :=
  wf_oracle U (V St) /\
  (* user external balances: total on U *)
  all_users_keys U (B_user_w St) /\
  all_users_keys U (B_user_r St) /\
  (*  nonnegativity *)
  UMap_nonneg (B_user_w St) /\
  UMap_nonneg (B_user_r St) /\
  (* oracle balances are nonnegative *)
  0 <= B_oracle_w St /\
  0 <= B_oracle_r St .
  (* TODO: other predicates *)

(** * (3.1): Auxiliary Definitions *)

(** ** (Definition 1):  Exponential Decay Factor *)

Definition decay (Delta : R) : R :=
  Rpower 2 ((-1 * Delta) / (proj1_sig h)).

(** ** Exponential decay factor lemmas *)

Lemma decay_add :
  forall a b : R,
    decay a * decay b = decay (a + b).
Proof.
  intros.
  unfold decay.
  unfold Rpower.
  rewrite <- exp_plus.
  f_equal.
  lra.
Qed.

Lemma decay_0 : decay 0 = 1.
Proof.
  unfold decay.
  rewrite Rmult_0_r.
  rewrite Rdiv_0_l.
  rewrite Rpower_O; lra.
Qed.

Lemma decay_pos :
  forall Delta,
    0 < decay Delta.
Proof.
  unfold decay.
  unfold Rpower.
  intros.
  apply exp_pos.
Qed.

Lemma exp_neg_lt_1 :
  forall x, x < 0 -> exp x < 1.
Proof.
  intros x Hx.
  assert (H : exp x < exp 0).
  { apply exp_increasing; exact Hx. }
  rewrite exp_0 in H.
  exact H.
Qed.

Lemma ln_gt_1_gt_0 :
  forall x : R, 1 < x -> 0 < ln x.
Proof.
  intros.
  assert (ln 1 < ln x).
  {
    apply ln_increasing. lra. auto.
  }
  rewrite ln_1 in H0.
  apply H0.
Qed.

Lemma decay_between_0_1 :
  forall Delta,
    0 < Delta ->
    0 < decay Delta < 1.
Proof.
  intros.
  unfold decay.
  split.
  - (* 0 < decay Delta *)
    unfold Rpower.
    apply exp_pos.
  - (* decay Delta < 1 *)
    unfold Rpower.
    destruct h.
    simpl.
    apply exp_neg_lt_1.
    assert (1 < 2) by lra.
    pose proof (ln_gt_1_gt_0 2 H0).
    rewrite Rdiv_def.
    pose proof (Rinv_pos x r).
    apply Rmult_neg_pos.
    -- apply Rmult_neg_pos; lra.
    -- lra.
Qed.

(** ** (Definition 2): Time-dependent functions

    Given the current state and timestamp, the following functions are defined:
 *)

Definition W_decayed (st : OracleState) (u : User) (t : timestamp) : R :=
  (getR u (W_user st)) * decay (t - ((getR u (T_user st)))).

Definition Q_decayed (t : timestamp) (st : OracleState) : R :=
  (Q st) * decay (t - t_sub st).

Definition pbar_decayed (st : OracleState) (t : timestamp) : R :=
  pbar st * decay (t - t_sub st).

(** Also known as ideal decayed weighted mean at time [t], [P(t)]. (Equation 4): *)

Definition P_ (st : OracleState) (t : timestamp) : R :=
  (sum_list_R (map (fun x => Rmult (getR x (P_user st)) (W_decayed st x t))  Users))
    / (sum_list_R (map (fun x => (W_decayed st x t)) Users)).

Hypothesis B_user_w_nonneg_hyp : forall u st, getR u (W_user st) >= 0. (* TODO *)

Lemma W_decayed_nonneg :
  forall u st t,
    0 <= W_decayed st u t .
Proof.
  intros u st t.
  unfold W_decayed, decay, Rpower.
  apply Rmult_le_pos.
  - pose proof (B_user_w_nonneg_hyp u st).
    unfold Rge in H.
    lra.
  - left. apply exp_pos.
Qed.

(** * (3.2): Auxiliary state update operations
 *)

(** [Unlock] is called by any operation that requires knowing the current unlocked oracle token balance of the user.
    - Precondition:
    - [t >= 0] (implicit)
 *)
Definition Unlock (st : OracleState) (u : User) (t : timestamp) : OracleState :=
  let tdep := getR u (T_dep st) in
  let ll   := getR u (L_l st) in
  let lf   := getR u (L_f st) in
  if andb (t >=b (tdep + Delta_dep)) (ll >b 0)
  then
    let L_f' := setR u (lf + ll) (L_f st) in
    let L_l' := setR u 0 (L_l st) in
    {|
      L_l    := L_l';
      L_f    := L_f';
      T_dep  := T_dep st;
      T_op   := T_op st;
      P_user := P_user st;
      W_user := W_user st;
      T_user := T_user st;
      pbar   := pbar st;
      ptilde := ptilde st;
      Q      := Q st;
      Phist   := Phist st;
      t_sub  := t_sub st;
      t_last := t_last st;
      L_tot  := L_tot st;
      G      := G st
    |}
  else st.

(** [Recompute] is called whenever users vote to blacklist or whitelist. *)
Definition Recompute (x : User) (st : OracleState) : OracleState :=
  let gx := G st in
  let vx_black := getR x (V_black gx) in
  let vx_white := getR x (V_white gx) in
  let bx' : bool :=
    (vx_black - vx_white)
    >b (q * (L_tot st) - (vx_black + vx_white))
  in
  let G' : GovernanceState :=
    {|
      B       := setBool x bx' (B gx);
      V_black := V_black gx;
      V_white := V_white gx;
      M_black := M_black gx;
      M_white := M_white gx;
      W_black := W_black gx;
      W_white := W_white gx
    |}
  in
  {|
    L_l    := L_l st;
    L_f    := L_f st;
    T_dep  := T_dep st;
    T_op   := T_op st;
    P_user := P_user st;
    W_user := W_user st;
    T_user := T_user st;
    pbar   := pbar st;
    ptilde := ptilde st;
    Q      := Q st;
    Phist  := Phist st;
    t_sub  := t_sub st;
    t_last := t_last st;
    L_tot  := L_tot st;
    G      := G'
  |}.

(** Helper for the body of the loop over [M_black] in [Reweight]. *)
Definition reweight_black_step (u : User) (w : weight) (x : User) (st : OracleState)
  : OracleState :=
  let gx := G st in
  let old := getR2 x u (W_black gx) in
  let Vb' := setR x (getR x (V_black gx) - old + w) (V_black gx) in
  let Wb' := setR2 x u w (W_black gx) in
  let G'  := {|
              B       := B gx;
              V_black := Vb';
              V_white := V_white gx;
              M_black := M_black gx;
              M_white := M_white gx;
              W_black := Wb';
              W_white := W_white gx
            |} in
  let st' := {|
              L_l := L_l st;
              L_f := L_f st;
              T_dep := T_dep st;
              T_op := T_op st;
              P_user := P_user st;
              W_user := W_user st;
              T_user := T_user st;
              pbar := pbar st;
              ptilde := ptilde st;
              Q := Q st;
              Phist := Phist st;
              t_sub := t_sub st;
              t_last := t_last st;
              L_tot := L_tot st;
              G := G'
            |} in
  Recompute x st'.

(** Helper for the body of the loop over [M_white] in [Reweight]. *)
Definition reweight_white_step (u : User) (w : weight) (x : User) (st : OracleState)
  : OracleState :=
  let gx := G st in
  let old := getR2 x u (W_white gx) in
  let Vw' := setR x (getR x (V_white gx) - old + w) (V_white gx) in
  let Ww' := setR2 x u w (W_white gx) in
  let G'  := {|
              B       := B gx;
              V_black := V_black gx;
              V_white := Vw';
              M_black := M_black gx;
              M_white := M_white gx;
              W_black := W_black gx;
              W_white := Ww'
            |}
  in
  let st' := {|
              L_l := L_l st;
              L_f := L_f st;
              T_dep := T_dep st;
              T_op := T_op st;
              P_user := P_user st;
              W_user := W_user st;
              T_user := T_user st;
              pbar := pbar st;
              ptilde := ptilde st;
              Q := Q st;
              Phist := Phist st;
              t_sub := t_sub st;
              t_last := t_last st;
              L_tot := L_tot st;
              G := G'
            |}
  in
  Recompute x st.

(** [Reweight] updates the weights of every blacklist/whitelist vote cast by a user.
    Precondition:
    - [w >= 0] (implicit)
 *)
Definition Reweight (u : User) (w : weight) (st : OracleState) : OracleState :=
  let gx := G st in
  let blacklisteds := getUserSet u (M_black gx) in
  let whitelisteds := getUserSet u (M_white gx) in
  let st1 := fold_left (fun acc x => reweight_black_step u w x acc) blacklisteds st in
  let st2 := fold_left (fun acc x => reweight_white_step u w x acc) whitelisteds st1 in
  st2.

(** * (3.3): Operations
    Each operation is an action that a user may perform to interact with an oracle.

    An operation takes its arguments and the current [State] or [OracleState] and returns the resulting [State] or [OracleState].

    Some of these operations have preconditions.

    We use the names of the operations - e.g. [token_deposit u a t St] instead of [delta_dep(u, a, t)(V)] as in the paper for token deposit.
 *)

(** ** (3.3.1): Token Deposit
   Precondition(s):
   - [a >= 0].
   - [t >= 0] (implicit).
 *)

Definition token_deposit (u : User) (a : balance) (t : timestamp) (St : State) : State :=
  if (a <=b 0) then
    (* TODO: add t >= 0*)
    St
  else
    let V0  := V St in
    let V1  := Unlock V0 u t in

    let L_l'   := addR u a (L_l V1) in
    let T_dep' := setR u t (T_dep V1) in
    let T_op'  := setR u t (T_op V1) in

    let B_user_w'   := addR u (-a) (B_user_w St) in
    let B_oracle_w' := (B_oracle_w St + a) in

    let V2 : OracleState :=
      {|
        L_l    := L_l';
        L_f    := L_f V1;
        T_dep  := T_dep';
        T_op   := T_op';
        P_user := P_user V1;
        W_user := W_user V1;
        T_user := T_user V1;
        pbar   := pbar V1;
        ptilde := ptilde V1;
        Q      := Q V1;
        Phist      := Phist V1;
        t_sub  := t_sub V1;
        t_last := t;
        L_tot  := (L_tot V1 + a);
        G      := G V1
      |}
    in

    {|
      V := V2;
      B_user_w := B_user_w';
      B_user_r := B_user_r St;
      B_oracle_w := B_oracle_w';
      B_oracle_r := B_oracle_r St;
    |}.

(** ** (3.3.2): Token Withdrawal
    Precondition(s):
     - [t >= 0] (implicit).
     - [a > 0].
     - [getR u (L_f (V st)) >= a].
     - [getR u (T_op (V st)) + Delta_wd <= t].
 *)

Definition token_withdrawal (u : User) (a : balance) (t : timestamp) (St : State) : State :=
  (* TODO: add t >= 0 *)
  let cond1 := a >b 0 in
  let cond2 := getR u (L_f (V St)) >=b a in
  let cond3 := getR u (T_op (V St)) + Delta_wd <=b t in
  if negb ((andb cond1 (andb cond2 cond3))) then
    St
  else
    let v0 := V St in

    (* oracle-local updates *)
    let L_f'  := addR u (-a) (L_f v0) in
    let T_op' := setR u t (T_op v0) in
    let v1 : OracleState :=
      {|
        L_l    := L_l v0;
        L_f    := L_f';
        T_dep  := T_dep v0;
        T_op   := T_op';
        P_user := P_user v0;
        W_user := W_user v0;
        T_user := T_user v0;
        pbar   := pbar v0;
        ptilde := ptilde v0;
        Q      := Q v0;
        Phist      := Phist v0;
        t_sub  := t_sub v0;
        t_last := t;
        L_tot  := (L_tot v0 - a);
        G      := G v0
      |}
    in

    (* balance updates *)
    let B_user_w'   := addR u a (B_user_w St) in
    let B_oracle_w' := (B_oracle_w St - a) in

    {|
      V := v1;
      B_user_w := B_user_w';
      B_user_r := B_user_r St;
      B_oracle_w := B_oracle_w';
      B_oracle_r := B_oracle_r St;
    |}.

(** ** (3.3.3): Value Submission
    Users can submit values, updating the aggregate weight and value.
    Users are then paid with [reward_payout].
 *)

(** *** Predefinition local variables *)

Definition w (u : User) (st : OracleState) := getR u (L_f st).
Definition pu (u : User) (st : OracleState) := getR u (P_user st).
Definition wu (u : User) (st : OracleState) := getR u (W_user st).
Definition tu (u : User) (st : OracleState) := getR u (T_user st).

(** *** (Equation 10-12): Updated aggregate weight and value, and reward payout *)

Definition Q' (u : User) (t : timestamp) (st : OracleState) : R :=
  ((Q st) - (wu u st) * (decay (t_sub st - tu u st))) * (decay (t - t_sub st)) + (w u st).

Definition pbar' (u : User) (v : value) (t : timestamp) (st : OracleState) : value :=
  (((((pbar st) * (Q st)) -  ((pu u st) * (wu u st) * (decay (t_sub st - tu u st))))
    * (decay (t - t_sub st))) + (v * (w u st))) / (Q' u t st).

(*** renamed from [n] in the paper *)

Definition reward_payout (u : User) (t : timestamp) (St : State) : R :=
  alpha * (B_oracle_r St) * ((w u (V St)) / (Q' u t (V St))) * (1 - decay (t - tu u (V St))).

Definition value_submission (u : User) (v : value) (t : timestamp) (St : State) : State :=
  let v0 := V St in
  let v1 := Unlock v0 u t in

  (* local values after Unlock *)
  let w_   := w u v1 in
  let vR   := v in
  let Qp   := Q' u t v1 in
  let pbarp := pbar' u vR t v1 in
  let St1 : State :=
    {| V := v1;
      B_user_w := B_user_w St;
      B_user_r := B_user_r St;
      B_oracle_w := B_oracle_w St;
      B_oracle_r := B_oracle_r St;
    |}
  in
  let n    := reward_payout u t St1 in

  (* update per-user submission fields *)
  let P_user' := setR u v (P_user v1) in
  let W_user' := setR u w_ (W_user v1) in
  let T_user' := setR u t (T_user v1) in

  (* update history *)
  let Phist' := (Phist v1) ++ ((t, pbarp, vR) :: nil) in

  (* new oracle state *)
  let v2 : OracleState :=
    {|
      L_l    := L_l v1;
      L_f    := L_f v1;
      T_dep  := T_dep v1;
      T_op   := T_op v1;
      P_user := P_user';
      W_user := W_user';
      T_user := T_user';
      pbar   := pbarp;
      ptilde := vR;
      Q      := Qp;
      Phist      := Phist';
      t_sub  := t;
      t_last := t;
      L_tot  := L_tot v1;
      G      := G v1
    |}
  in

  (* reward token balance transfer *)
  let B_user_r'   := addR u n (B_user_r St) in
  let B_oracle_r' := (B_oracle_r St - n) in

  {|
    V := v2;
    B_user_w := B_user_w St;
    B_user_r := B_user_r';
    B_oracle_w := B_oracle_w St;
    B_oracle_r := B_oracle_r';
  |}.

(** ** (3.3.4) Value reading
    Precondition(s):
    - [t >= 0] (implicit)
    - [u] is not blacklisted.
 *)

Definition isBlacklisted (u : User) (st : OracleState) : bool :=
  getBool u (B (G st)). (* true = blacklisted, false = whitelisted *)

Definition value_reading (u : User) (t : timestamp) (st : OracleState) : OracleState :=
  if isBlacklisted u st then
    st
  else
    {|
      L_l    := L_l st;
      L_f    := L_f st;
      T_dep  := T_dep st;
      T_op   := T_op st;
      P_user := P_user st;
      W_user := W_user st;
      T_user := T_user st;
      pbar   := pbar st;
      ptilde := ptilde st;
      Q      := Q st;
      Phist      := Phist st;
      t_sub  := t_sub st ;
      t_last := t;
      L_tot  := L_tot st;
      G      := G st
    |}.

(** ** (3.3.5) Vote to blacklist
    Precondition(s):
  - [t >= 0] (implicit)
  - [u] not blacklisted.
  - [w(u) = L_f(u) > 0].
  - [u] has not voted on x before ([x] not in [M_black(u)]).
 *)

Definition blacklist_vote (u x : User) (t : timestamp) (st : OracleState) : OracleState :=
  let cond1 := negb (isBlacklisted u st) in
  let cond2 := getR u (L_f st) >b 0 in
  let cond3 := negb (mem_user x (getUserSet u (M_black (G st)))) in
  if negb (andb cond1 (andb cond2 cond3)) then
    st
  else
    let v0 := Unlock st u t in

    (* V_black(x) := V_black(x) + L_f(u) *)
    let V_black' := addR x (getR u (L_f v0)) (V_black (G v0)) in

    (* W_black(x,u) := L_f(u) *)
    let W_black' := setR2 x u (getR u (L_f v0)) (W_black (G v0)) in

    (* M_black(u) := M_black(u) ∪ {x} *)
    let M_black' := setUserSet u (addUser x (getUserSet u (M_black (G v0)))) (M_black (G v0)) in

    let g1 : GovernanceState :=
      {|
        B       := B (G v0);
        V_black := V_black';
        V_white := V_white (G v0);
        M_black := M_black';
        M_white := M_white (G v0);
        W_black := W_black';
        W_white := W_white (G v0)
      |}
    in

    (* update oracle state timestamps + governance *)
    let T_op' := setR u t (T_op v0) in
    let v1 : OracleState :=
      {|
        L_l    := L_l v0;
        L_f    := L_f v0;
        T_dep  := T_dep v0;
        T_op   := T_op';
        P_user := P_user v0;
        W_user := W_user v0;
        T_user := T_user v0;
        pbar   := pbar v0;
        ptilde := ptilde v0;
        Q      := Q v0;
        Phist      := Phist v0;
        t_sub  := t_sub v0;
        t_last := t;
        L_tot  := L_tot v0;
        G      := g1
      |}
    in

    (* Recompute(x) *)
    Recompute x v1.

(** ** (3.3.6) Vote to whitelist
    Precondition(s):
    - [t >= 0] (implicit)
    - [u] not blacklisted ([getBool u (B (G st)) = false]).
    - [L_f(u) > 0].
    - [u] has not voted on x before ([x] not in [M_white(u)]).
*)

Definition whitelist_vote (u x : User) (t : timestamp) (st : OracleState) : OracleState :=
  let cond1 := negb (isBlacklisted u st) in
  let cond2 := getR u (L_f st) >b 0 in
  let cond3 := negb (mem_user x (getUserSet u (M_white (G st)))) in
  if negb (andb cond1 (andb cond2 cond3)) then
    st
  else
    let v0 := Unlock st u t in

    (* V_white(x) := V_white(x) + L_f(u) *)
    let V_white' := addR x (getR u (L_f v0)) (V_white (G v0)) in

    (* W_white(x,u) := L_f(u) *)
    let W_white' := setR2 x u (getR u (L_f v0)) (W_white (G v0)) in

    (* M_white(u) := M_white(u) ∪ {x} *)
    let Mu := getUserSet u (M_white (G v0)) in
    let Mu' := addUser x Mu in
    let M_white' := setUserSet u Mu' (M_white (G v0)) in

    let g1 : GovernanceState :=
      {|
        B       := B (G v0);
        V_black := V_black (G v0);
        V_white := V_white';
        M_black := M_black (G v0);
        M_white := M_white';
        W_black := W_black (G v0);
        W_white := W_white'
      |}
    in

    (* update oracle state timestamps + governance *)
    let T_op' := setR u t (T_op v0) in
    let v1 : OracleState :=
      {|
        L_l    := L_l v0;
        L_f    := L_f v0;
        T_dep  := T_dep v0;
        T_op   := T_op';
        P_user := P_user v0;
        W_user := W_user v0;
        T_user := T_user v0;
        pbar   := pbar v0;
        ptilde := ptilde v0;
        Q      := Q v0;
        Phist      := Phist v0;
        t_sub  := t_sub v0;
        t_last := t;
        L_tot  := L_tot v0;
        G      := g1
      |}
    in

    (* Recompute(x) *)
    Recompute x v1.

(** ** (3.3.7) Weight synchronization
    - Precondition:
    - [t >= 0] (implicit)
 *)

Definition weight_synchronization (u : User) (t : timestamp) (st : OracleState) : OracleState :=
  let v0 := Unlock st u t in
  let v1 := Reweight u (getR u (L_f v0)) v0 in
  {|
    L_l    := L_l v1;
    L_f    := L_f v1;
    T_dep  := T_dep v1;
    T_op   := T_op v1;
    P_user := P_user v1;
    W_user := W_user v1;
    T_user := T_user v1;
    pbar   := pbar v1;
    ptilde := ptilde v1;
    Q      := Q v1;
    Phist      := Phist v1;
    t_sub  := t_sub v1;
    t_last := t;                (* updated *)
    L_tot  := L_tot v1;
    G      := G v1
  |}.

(** ** (3.3.8) Reward Token Funding
    - Preconditions:
    - [a >= 0] (implicit)
    - [t >= 0] (implicit)
 *)

Definition reward_funding (u : User) (a : balance) (t : timestamp) (St : State) : State :=
  let B_user_r' := addR u (-a) (B_user_r St) in
  let B_oracle_r' := (B_oracle_r St) + a in
  let v0 := V St in
  let V' := {|
             L_l    := L_l v0;
             L_f    := L_f v0;
             T_dep  := T_dep v0;
             T_op   := T_op v0;
             P_user := P_user v0;
             W_user := W_user v0;
             T_user := T_user v0;
             pbar   := pbar v0;
             ptilde := ptilde v0;
             Q      := Q v0;
             Phist      := Phist v0;
             t_sub  := t_sub v0;
             t_last := t;
             L_tot  := L_tot v0;
             G      := G v0
           |} in
  {|
    V := V';
    B_user_w := B_user_w St;
    B_user_r := B_user_r';
    B_oracle_w := B_oracle_w St;
    B_oracle_r := B_oracle_r';
  |}.

(** * Traces
    We define a datatype [Operation] corresponding to each of the oracle operations.
    A [Trace] is then a list of operations.
    We then define an initial [State].
    Execution of an [Operation] with respect to a state is simply running the associated oracle operation on that state,
    and execution of a trace is cumulative execution of the list of operations on the initial state.
 *)

Inductive Operation : Type :=
| Deposit (u : User) (a : balance) (t : timestamp)
| Withdrawal (u : User) (a : balance) (t : timestamp)
| Submission (u : User) (v : value) (t : timestamp)
| Reading (u : User) (t : timestamp)
| VoteBlacklist (u : User) (x : User) (t : timestamp)
| VoteWhitelist (u : User) (x : User) (t : timestamp)
| WeightSync (u : User) (t : timestamp)
| RewardFunding (u : User) (a : balance) (t : timestamp)
| NoneOp (t : timestamp).

Definition Trace : Type := list Operation.

Definition lift_oracle_state  (f : OracleState -> OracleState) (St : State) : State :=
  {| V := f (V St);
    B_user_w := B_user_w St;
    B_user_r := B_user_r St;
    B_oracle_w := B_oracle_w St;
    B_oracle_r := B_oracle_r St;
  |}.

(** ** Initial state *)

Definition init_B_user_w : UserMap.t balance := UserMap.empty balance.
Definition init_B_user_r : UserMap.t balance := UserMap.empty balance.
Definition init_B_oracle_w : balance := 0.
Definition init_B_oracle_r : balance := 0.

Definition init_governance : GovernanceState :=
  {|
    B       := UserMap.empty bool;
    V_black := UserMap.empty weight;
    V_white := UserMap.empty weight;
    M_black := UserMap.empty UserSet;
    M_white := UserMap.empty UserSet;
    W_black := UserPairMap.empty weight;
    W_white := UserPairMap.empty weight
  |}.

Definition init_oracle : OracleState :=
  {|
    L_l    := UserMap.empty balance;
    L_f    := UserMap.empty balance;
    T_dep  := UserMap.empty timestamp;
    T_op   := UserMap.empty timestamp;
    P_user := UserMap.empty value;
    W_user := UserMap.empty weight;
    T_user := UserMap.empty timestamp;
    pbar   := 0;
    ptilde := 0;
    Q      := 0;
    Phist   := nil;
    t_sub  := 0;
    t_last := 0;
    L_tot  := 0;
    G      := init_governance
  |}.

Definition init_state : State :=
  {|
    V := init_oracle;
    B_user_w := init_B_user_w;
    B_user_r := init_B_user_r;
    B_oracle_w := init_B_oracle_w;
    B_oracle_r := init_B_oracle_r;
  |}.

(** ** Execution of an operation/trace *)

Definition exec_op (op : Operation) (St : State) : State :=
  match op with
  | Deposit u a t => token_deposit u a t St
  | Withdrawal u a t => token_withdrawal u a t St
  | Submission u v t => value_submission u v t St
  | Reading u t => lift_oracle_state (fun st => value_reading u t st) St
  | VoteBlacklist u x t => lift_oracle_state (fun st => blacklist_vote u x t st) St
  | VoteWhitelist u x t => lift_oracle_state (fun st => whitelist_vote u x t st) St
  | WeightSync u t => lift_oracle_state (fun st => weight_synchronization u t st) St
  | RewardFunding u a t => reward_funding u a t St
  | NoneOp t => St
  end.

Definition is_submission_by (u:User) (op:Operation) : Prop :=
  match op with
  | Submission u' _ _ => u' = u
  | _ => False
  end.

Definition is_submission (op:Operation) : Prop :=
  match op with
  | Submission _ _ _ => True
  | _ => False
  end.

Definition is_reward_funding (op : Operation) : Prop :=
  match op with
  | RewardFunding _ _ _ => True
  | _ => False
  end.

(** The following lemmas show that executing an non-submission operation preserves TW.
    They are used in Theorem 6's proof, specifically in showing that an inactive operator (no submissions) will eventually have a constant [T_user] and [W_user]. *)

Lemma Unlock_preserves_TW :
  forall st u t u',
    getR u' (T_user (Unlock st u t)) = getR u' (T_user st) /\
    getR u' (W_user (Unlock st u t)) = getR u' (W_user st).
Proof.
  intros. unfold Unlock.
  destruct (andb (t >=b (getR u (T_dep st) + Delta_dep)) (getR u (L_l st) >b 0));
  simpl; split; reflexivity.
Qed.

Lemma fold_left_preserves_TW :
  forall (A:Type) (f: OracleState -> A -> OracleState) (l:list A) st u,
    (forall acc x,
        getR u (T_user (f acc x)) = getR u (T_user acc) /\
        getR u (W_user (f acc x)) = getR u (W_user acc)) ->
    getR u (T_user (fold_left f l st)) = getR u (T_user st) /\
    getR u (W_user (fold_left f l st)) = getR u (W_user st).
Proof.
  intros A f l.
  induction l as [|a l IH]; intros st u Hstep.
  - simpl. split; reflexivity.
  - simpl.
    destruct (Hstep st a) as [HT HW].
    specialize (IH (f st a) u Hstep).
    destruct IH as [HT' HW'].
    split; etransitivity; eauto.
Qed.

Lemma Recompute_preserves_T_user :
  forall x st u,
    getR u (T_user (Recompute x st)) = getR u (T_user st).
Proof. intros; unfold Recompute; simpl; reflexivity. Qed.

Lemma Recompute_preserves_W_user :
  forall x st u,
    getR u (W_user (Recompute x st)) = getR u (W_user st).
Proof. intros; unfold Recompute. simpl. reflexivity. Qed.


Lemma reweight_black_step_preserves_T_user :
  forall u0 w x st u,
    getR u (T_user (reweight_black_step u0 w x st)) = getR u (T_user st).
Proof.
  intros; unfold reweight_black_step; simpl.
  reflexivity.
Qed.

Lemma reweight_black_step_preserves_W_user :
  forall u0 w x st u,
    getR u (W_user (reweight_black_step u0 w x st)) = getR u (W_user st).
Proof.
  intros; unfold reweight_black_step.
  simpl.
  reflexivity.
Qed.

Lemma reweight_white_step_preserves_T_user :
  forall u0 w x st u,
    getR u (T_user (reweight_white_step u0 w x st)) = getR u (T_user st).
Proof.
  intros; unfold reweight_white_step; simpl.
  reflexivity.
Qed.

Lemma reweight_white_step_preserves_W_user :
  forall u0 w x st u,
    getR u (W_user (reweight_white_step u0 w x st)) = getR u (W_user st).
Proof.
  intros; unfold reweight_white_step; simpl.
  reflexivity.
Qed.

Lemma fold_left_preserves_getR_T_user :
  forall (A:Type) (f: OracleState -> A -> OracleState) l st u,
    (forall acc x, getR u (T_user (f acc x)) = getR u (T_user acc)) ->
    getR u (T_user (fold_left f l st)) = getR u (T_user st).
Proof.
  intros A f l; induction l as [|a l IH]; intros st u Hstep; simpl.
  - reflexivity.
  - rewrite <- (Hstep st a). apply IH.
    apply Hstep.
Qed.

Lemma fold_left_preserves_getR_W_user :
  forall (A:Type) (f: OracleState -> A -> OracleState) l st u,
    (forall acc x, getR u (W_user (f acc x)) = getR u (W_user acc)) ->
    getR u (W_user (fold_left f l st)) = getR u (W_user st).
Proof.
  intros A f l; induction l as [|a l IH]; intros st u Hstep; simpl.
  - reflexivity.
  - rewrite <- (Hstep st a). apply IH.
    apply Hstep.
Qed.

Lemma Reweight_preserves_T_user :
  forall u0 w st u,
    getR u (T_user (Reweight u0 w st)) = getR u (T_user st).
Proof.
  intros u0 w st u.
  unfold Reweight.
  (* first fold *)
  rewrite <- (fold_left_preserves_getR_T_user
            User
            (fun acc x => reweight_black_step u0 w x acc)
            (getUserSet u0 (M_black (G st)))
            st u).
  2:{ intros acc x; apply reweight_black_step_preserves_T_user. }
  (* second fold *)
  rewrite (fold_left_preserves_getR_T_user
            User
            (fun acc x => reweight_white_step u0 w x acc)
            (getUserSet u0 (M_white (G st)))
            (fold_left (fun acc x => reweight_black_step u0 w x acc)
                       (getUserSet u0 (M_black (G st))) st)
            u).
  2:{ intros acc x; apply reweight_white_step_preserves_T_user. }
  reflexivity.
Qed.

Lemma Reweight_preserves_W_user :
  forall u0 w st u,
    getR u (W_user (Reweight u0 w st)) = getR u (W_user st).
Proof.
  intros u0 w st u.
  unfold Reweight.
  rewrite <- (fold_left_preserves_getR_W_user
            User
            (fun acc x => reweight_black_step u0 w x acc)
            (getUserSet u0 (M_black (G st)))
            st u).
  2:{ intros acc x; apply reweight_black_step_preserves_W_user. }
  rewrite (fold_left_preserves_getR_W_user
            User
            (fun acc x => reweight_white_step u0 w x acc)
            (getUserSet u0 (M_white (G st)))
            (fold_left (fun acc x => reweight_black_step u0 w x acc)
                       (getUserSet u0 (M_black (G st))) st)
            u).
  2:{ intros acc x; apply reweight_white_step_preserves_W_user. }
  reflexivity.
Qed.

Lemma exec_op_preserves_TW_if_not_submit :
  forall (St:State) (op:Operation) (u:User),
    ~ is_submission_by u op ->
    getR u (T_user (V (exec_op op St))) = getR u (T_user (V St)) /\
    getR u (W_user (V (exec_op op St))) = getR u (W_user (V St)).
Proof.
  intros St op u Hn.
  destruct op; simpl in *.
  try (unfold lift_oracle_state; simpl; split; reflexivity).

  - unfold token_deposit.
    destruct (a <=b 0); simpl; split; try reflexivity;
    unfold Unlock;
    destruct ((t >=b getR u0 (T_dep (V St)) + Delta_dep) && (getR u0 (L_l (V St)) >b 0));
    simpl; reflexivity.

  - unfold token_withdrawal.
    destruct (negb (andb (a >b 0) (andb (getR u0 (L_f (V St)) >=b a)
                      (getR u0 (T_op (V St)) + Delta_wd <=b t)))); simpl;
    split; reflexivity.

  - unfold Unlock.
    destruct ((t >=b getR u0 (T_dep (V St)) + Delta_dep) && (getR u0 (L_l (V St)) >b 0)); simpl; split;
    apply getR_setR_neq; symmetry; apply Hn.

  - unfold value_reading.
    destruct (isBlacklisted u0 (V St)); simpl; split; reflexivity.

  - unfold blacklist_vote.
    destruct (negb
           (negb (isBlacklisted u0 (V St)) &&
            ((getR u0 (L_f (V St)) >b 0) && negb (mem_user x (getUserSet u0 (M_black (G (V St)))))))); simpl;
      split; try reflexivity;
      unfold Unlock;
      destruct ((t >=b getR u0 (T_dep (V St)) + Delta_dep) && (getR u0 (L_l (V St)) >b 0)); simpl; split.

  - unfold whitelist_vote.
    destruct (negb
           (negb (isBlacklisted u0 (V St)) &&
            ((getR u0 (L_f (V St)) >b 0) && negb (mem_user x (getUserSet u0 (M_white (G (V St)))))))); simpl;
      split; try reflexivity;
      unfold Unlock;
      destruct ((t >=b getR u0 (T_dep (V St)) + Delta_dep) && (getR u0 (L_l (V St)) >b 0)); simpl; split.

  - set (st0 := V St).
    set (st1 := Unlock st0 u0 t).
    set (w0  := getR u0 (L_f st1)).

    pose proof (Reweight_preserves_T_user u0 w0 st1 u) as HTre.

    assert (HTun : getR u (T_user st1) = getR u (T_user st0)).
    { subst st1 st0. unfold Unlock.
      destruct ((t >=b getR u0 (T_dep (V St)) + Delta_dep) && (getR u0 (L_l (V St)) >b 0));
        reflexivity. }

    pose proof (Reweight_preserves_W_user u0 w0 st1 u) as HWre.

    assert (HWun : getR u (W_user st1) = getR u (W_user st0)).
    { subst st1 st0. unfold Unlock.
      destruct ((t >=b getR u0 (T_dep (V St)) + Delta_dep) && (getR u0 (L_l (V St)) >b 0));
        reflexivity. }

    split.
    rewrite HTre. rewrite HTun. reflexivity.
    rewrite HWre. rewrite HWun. reflexivity.

  - split; reflexivity.
  - split; reflexivity.
Qed.

(** Definition of an execution of a trace. *)

Fixpoint exec_trace (tr : Trace) (St : State) : State :=
  match tr with
  | nil => St
  | op :: tr' => exec_trace tr' (exec_op op St)
  end.

Definition reachable (tr : Trace) (St : State) : Prop :=
  St = exec_trace tr init_state.

(** ** Run (infinite traces)
    A [Run] is a function from a natural number to an operation.
    Thus, a run indexes an infinite trace / stream of operations.
    The theorems deal mostly with [Runs] and not [Trace]s.
*)

Definition Run : Type := nat -> Operation.

Fixpoint exec_prefix (run : Run) (n : nat) (St : State) : State :=
  match n with
  | O => St
  | S n' => exec_op (run n') (exec_prefix run n' St)
  end.

Definition state_at (run : Run) (n : nat) : State :=
  exec_prefix run n init_state.

Definition op_at (run : Run) (n : nat) : Operation := run n .

Lemma state_at_S :
  forall (run : Run) (n : nat),
    state_at run (S n) = exec_op (run n) (state_at run n).
Proof.
  intros run n.
  unfold state_at.
  simpl.
  reflexivity.
Qed.

(** ** Internal lemmas about reals and summations *)

Lemma div_le_1 :
  forall a b : R,
    0 <= a ->
    0 < b ->
    a <= b ->
    a / b <= 1.
Proof.
  intros a b Ha Hb Hab.
  unfold Rdiv.
  (* multiply a<=b by /b > 0 *)
  assert (Hinvpos : 0 < / b).
  { apply Rinv_0_lt_compat; exact Hb. }
  assert (Hmul : a * / b <= b * / b).
  { apply Rmult_le_compat_r; [left; exact Hinvpos | exact Hab]. }
  (* simplify RHS *)
  replace (b * / b) with 1 in Hmul.
  - exact Hmul.
  - field; lra.
Qed.

Lemma mul_le_1_of_le_1 :
  forall a b : R,
    0 <= a <= 1 ->
    0 <= b <= 1 ->
    a * b <= 1.
Proof.
  intros a b [Ha0 Ha1] [Hb0 Hb1].
  (* a*b <= 1*b <= 1 *)
  eapply Rle_trans.
  - apply Rmult_le_compat_r; try lra. exact Ha1.
  - rewrite Rmult_1_l. exact Hb1.
Qed.

Lemma sum_list_R_le :
  forall l1 l2,
    Forall2 Rle l1 l2 ->
    sum_list_R l1 <= sum_list_R l2.
Proof.
  intros l1 l2 H.
  induction H.
  - simpl. apply Rle_refl.
  - simpl. unfold sum_list_R in *.
    eapply Rplus_le_compat. apply H. apply IHForall2.
Qed.

Lemma Forall2_map_l :
  forall (A B : Type) (R : B -> B -> Prop) (f g : A -> B) l,
    (forall x, In x l -> R (f x) (g x)) ->
    Forall2 R (map f l) (map g l).
Proof.
  intros A B R f g l H.
  induction l.
  - constructor.
  - simpl. constructor.
    -- apply H. simpl. auto.
    -- apply IHl. intros. apply H. simpl. auto.
Qed.

Lemma sum_list_R_map_mult_const :
  forall (c : R) (f : User -> R) (l : list User),
    sum_list_R (map (fun u => c * f u) l) = c * sum_list_R (map f l).
Proof.
  intros c f l.
  induction l.
  - simpl. symmetry. apply Rmult_0_r.
  - simpl.
    rewrite Rmult_plus_distr_l.
    apply Rplus_eq_compat_l.
    apply IHl.
Qed.

Lemma sum_list_R_nonneg_nonneg :
  forall (f : User -> R) (l : list User),
    (forall x, f x >= 0) ->
    sum_list_R (map f l) >= 0.
Proof.
  intros.
  induction l.
  - simpl. apply Rge_refl.
  - simpl. specialize (H a). replace 0 with (0 + 0) by lra.
    apply Rplus_ge_compat; assumption.
Qed.

Lemma sum_list_R_nn_exists_pos_pos :
  forall (l:list User) (f: User -> R),
    (forall x, 0 <= f x) ->
    (exists x, In x l /\ 0 < f x) ->
    0 < sum_list_R (map f l).
Proof.
  intros l; induction l as [|a l IH]; intros f Hnn [x [Hin Hpos]].
  - simpl in Hin. contradiction.
  - simpl in Hin. simpl.
    destruct Hin as [Hx | Hin].
    + subst x.
      simpl in Hnn.
      apply Rplus_lt_le_0_compat. apply Hpos.

      assert (sum_list_R (map f l) >= 0). {
        apply sum_list_R_nonneg_nonneg. intros.
        specialize (Hnn x). lra.
      }

      lra.
    + specialize (IH f Hnn).
      apply Rplus_le_lt_0_compat.
      apply Hnn.
      apply IH.
      exists x. auto.
Qed.

Lemma sum_list_R_ge_member :
  forall (l : list R) (a : R),
    Forall (fun x => 0 <= x) l ->
    In a l ->
    a <= sum_list_R l.
Proof.
  intros l a Hfor Hin.
  induction Hfor.
  - contradiction.
  - simpl in *.
    destruct Hin as [<- | Hin].
    + assert (0 <= sum_list_R l).
      { clear -Hfor. induction Hfor. simpl; lra. simpl; lra. }
      lra.
    + specialize (IHHfor Hin). lra.
Qed.

Lemma remove_not_in :
  forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y})
         (x : A) (l : list A),
    ~ In x l ->
    (remove eq_dec x l) = l.
Proof.
  intros A eq_dec x l.
  induction l as [|a l IH]; intro Hnin; simpl; auto.
  destruct (eq_dec x a) as [Heq|Hneq].
  - subst. exfalso. apply Hnin. left. reflexivity.
  - f_equal. apply IH. intro Hin.
    apply Hnin. right. exact Hin.
Qed.

Lemma sum_split_remove :
  forall (l : list User) u (f : User -> R),
    NoDup l -> In u l ->
    sum_list_R (map f l) = sum_list_R (map f (remove Nat.eq_dec u l)) + f u.
Proof.
  intros l u f Hnodup Hin.
  induction l as [|a l IH]; simpl in *.
  - contradiction.
  - inversion Hnodup as [|a' l' Hnotin Hnodup']; subst.
    destruct Hin as [Hu_eq | Hu_in].
    -- subst a.
       simpl.
       destruct (Nat.eq_dec u u) as [_ | H]; [| contradiction].
       rewrite (remove_not_in User _ u l Hnotin).
       ring.
    -- destruct (Nat.eq_dec u a) as [Hu_eq | Hu_neq].
       --- subst a. contradiction.
       --- simpl.
           specialize (IH Hnodup' Hu_in).
           rewrite IH.
           ring.
Qed.

Lemma Rpower_2_pos :
  forall x : R, 0 < Rpower 2 x.
Proof.
  intro x. unfold Rpower. apply exp_pos.
Qed.

Lemma Rpower_2_nonneg :
  forall x : R, 0 <= Rpower 2 x.
Proof.
  intro x. left. apply Rpower_2_pos.
Qed.

Lemma Rabs_div :
  forall p q,
  Rabs (p / q) = (Rabs p) / (Rabs q).
Proof.
  intros.
  unfold Rdiv.
  rewrite Rabs_mult.
  rewrite (Rabs_inv).
  reflexivity.
Qed.

(** * (4) Theorems about the oracle protocol
    The main content of this formalization.
 *)

(** ** (Theorem 3): Equivalence of the ideal decayed weight mean function and the constant time update rule

      The ideal decayed weighted mean function [P(t)] and the constant-time update rule [pbar_k(t) - pbar] are equal
      where [k] is the [k-th] update.

      [P(t) = pbar_k(t)]
 *)

(** *** Operations preserve mean fields
    The following lemmas state that operations leave mean / [P(t)] relevant oracle fields unchanged.
 *)

Lemma Unlock_preserves_mean_fields :
  forall (st : OracleState) (u : User) (t : timestamp),
    P_user (Unlock st u t) = P_user st /\
    W_user (Unlock st u t) = W_user st /\
    T_user (Unlock st u t) = T_user st /\
    pbar   (Unlock st u t) = pbar   st /\
    Q      (Unlock st u t) = Q      st /\
    t_sub  (Unlock st u t) = t_sub  st.
Proof.
  intros st u t.
  unfold Unlock.
  destruct ((t >=b getR u (T_dep st) + Delta_dep) &&
            (getR u (L_l st) >b 0)); simpl; repeat split; reflexivity.
Qed.

Lemma token_deposit_preserves_mean_fields :
  forall (St : State) (u : User) (a : balance) (t : timestamp),
    P_user (V (token_deposit u a t St)) = P_user (V St) /\
    W_user (V (token_deposit u a t St)) = W_user (V St) /\
    T_user (V (token_deposit u a t St)) = T_user (V St) /\
    pbar   (V (token_deposit u a t St)) = pbar   (V St) /\
    Q      (V (token_deposit u a t St)) = Q      (V St) /\
    t_sub  (V (token_deposit u a t St)) = t_sub  (V St).
Proof.
  intros St u a t.
  unfold token_deposit.
  destruct (a <=b 0) eqn:Ha.
  - simpl. repeat split; reflexivity.
  - simpl.
    unfold Unlock.
    destruct ((t >=b getR u (T_dep (V St)) + Delta_dep) &&
              (getR u (L_l (V St)) >b 0)) eqn:Hunlock;
    simpl; repeat split; reflexivity.
Qed.

Lemma token_withdrawal_preserves_mean_fields :
  forall (St : State) (u : User) (a : balance) (t : timestamp),
    P_user (V (token_withdrawal u a t St)) = P_user (V St) /\
    W_user (V (token_withdrawal u a t St)) = W_user (V St) /\
    T_user (V (token_withdrawal u a t St)) = T_user (V St) /\
    pbar   (V (token_withdrawal u a t St)) = pbar   (V St) /\
    Q      (V (token_withdrawal u a t St)) = Q      (V St) /\
    t_sub  (V (token_withdrawal u a t St)) = t_sub  (V St).
Proof.
  intros St u a t.
  unfold token_withdrawal.
  destruct (negb ((a >b 0) &&
                  ((getR u (L_f (V St)) >=b a) &&
                   (getR u (T_op (V St)) + Delta_wd <=b t)))) eqn:Hcond.
  - simpl. repeat split; reflexivity.
  - simpl. repeat split; reflexivity.
Qed.

Lemma value_reading_preserves_mean_fields :
  forall (st : OracleState) (u : User) (t : timestamp),
    P_user (value_reading u t st) = P_user st /\
    W_user (value_reading u t st) = W_user st /\
    T_user (value_reading u t st) = T_user st /\
    pbar   (value_reading u t st) = pbar   st /\
    Q      (value_reading u t st) = Q      st /\
    t_sub  (value_reading u t st) = t_sub  st.
Proof.
  intros st u t.
  unfold value_reading.
  destruct (isBlacklisted u st); simpl; repeat split; reflexivity.
Qed.

Lemma blacklist_vote_preserves_mean_fields :
  forall (st : OracleState) (u x : User) (t : timestamp),
    P_user (blacklist_vote u x t st) = P_user st /\
    W_user (blacklist_vote u x t st) = W_user st /\
    T_user (blacklist_vote u x t st) = T_user st /\
    pbar   (blacklist_vote u x t st) = pbar   st /\
    Q      (blacklist_vote u x t st) = Q      st /\
    t_sub  (blacklist_vote u x t st) = t_sub  st.
Proof.
  intros st u x t.
  unfold blacklist_vote.
  destruct (negb
           (negb (isBlacklisted u st) &&
            ((getR u (L_f st) >b 0) &&
             negb (mem_user x (getUserSet u (M_black (G st))))))) eqn:Hcond.
  - simpl. repeat split; reflexivity.
  - simpl.
    unfold Unlock.
    destruct ((t >=b getR u (T_dep st) + Delta_dep) &&
              (getR u (L_l st) >b 0)) eqn:Hunlock;
    simpl; repeat split; reflexivity.
Qed.

Lemma whitelist_vote_preserves_mean_fields :
  forall (st : OracleState) (u x : User) (t : timestamp),
    P_user (whitelist_vote u x t st) = P_user st /\
    W_user (whitelist_vote u x t st) = W_user st /\
    T_user (whitelist_vote u x t st) = T_user st /\
    pbar   (whitelist_vote u x t st) = pbar   st /\
    Q      (whitelist_vote u x t st) = Q      st /\
    t_sub  (whitelist_vote u x t st) = t_sub  st.
Proof.
  intros st u x t.
  unfold whitelist_vote.
  destruct (negb
           (negb (isBlacklisted u st) &&
            ((getR u (L_f st) >b 0) &&
             negb (mem_user x (getUserSet u (M_white (G st))))))) eqn:Hcond.
  - simpl. repeat split; reflexivity.
  - simpl.
    unfold Unlock.
    destruct ((t >=b getR u (T_dep st) + Delta_dep) &&
              (getR u (L_l st) >b 0)) eqn:Hunlock;
    simpl; repeat split; reflexivity.
Qed.

Lemma reward_funding_preserves_mean_fields :
  forall (St : State) (u : User) (a : balance) (t : timestamp),
    P_user (V (reward_funding u a t St)) = P_user (V St) /\
    W_user (V (reward_funding u a t St)) = W_user (V St) /\
    T_user (V (reward_funding u a t St)) = T_user (V St) /\
    pbar   (V (reward_funding u a t St)) = pbar   (V St) /\
    Q      (V (reward_funding u a t St)) = Q      (V St) /\
    t_sub  (V (reward_funding u a t St)) = t_sub  (V St).
Proof.
  intros St u a t.
  unfold reward_funding.
  simpl.
  repeat split; reflexivity.
Qed.

(** *** Submission subcase **)

(** The ideal decayed denominator evaluated at submission time. *)

Definition ideal_Q_at_submission_time (st : OracleState) : R :=
  sum_list_R
    (map (fun x =>
            getR x (W_user st) *
            decay (t_sub st - getR x (T_user st)))
         Users).

(** The ideal decayed numerator evaluated at submission time. *)

Definition ideal_num_at_submission_time (st : OracleState) : R :=
  sum_list_R
    (map (fun x =>
            getR x (P_user st) *
            getR x (W_user st) *
            decay (t_sub st - getR x (T_user st)))
         Users).

(** Argument corresponding to lines (19) to (24) on page 8.
    This proves the updated [Q'] equals the ideal decayed weight sum after submission. *)

Lemma Q'_eq_sum_Wdecay:
  forall (st : OracleState) (u : User) (t : timestamp),
    In u Users ->
    NoDup Users ->
    Q st =
      sum_list_R
        (map (fun x =>
                getR x (W_user st) *
                decay (t_sub st - getR x (T_user st)))
             Users) ->
    Q' u t st =
      sum_list_R
        (map (fun x =>
                if Nat.eq_dec x u
                then w u st
                else getR x (W_user st) *
                     decay (t - getR x (T_user st)))
             Users).
Proof.
  intros st u t Hu Hnodup HQideal.
  unfold Q'.
  unfold w, wu, tu.

  rewrite HQideal.

  rewrite (sum_split_remove
             Users
             u
             (fun x =>
                getR x (W_user st) *
                decay (t_sub st - getR x (T_user st)))
          ); try assumption.

  replace
    ((sum_list_R
        (map
           (fun x : User =>
              getR x (W_user st) *
              decay (t_sub st - getR x (T_user st)))
           (remove Nat.eq_dec u Users))
      +
      getR u (W_user st) * decay (t_sub st - getR u (T_user st))
      -
      getR u (W_user st) * decay (t_sub st - getR u (T_user st)))
     * decay (t - t_sub st) + getR u (L_f st))
  with
    ((sum_list_R
        (map
           (fun x : User =>
              getR x (W_user st) *
              decay (t_sub st - getR x (T_user st)))
           (remove Nat.eq_dec u Users)))
      * decay (t - t_sub st) + getR u (L_f st))
  by ring.

  rewrite Rmult_comm.
  rewrite <- (sum_list_R_map_mult_const
                (decay (t - t_sub st))
                (fun x : User =>
                   getR x (W_user st) *
                     decay (t_sub st - getR x (T_user st)))
                (remove Nat.eq_dec u Users)).

  rewrite (map_ext
             (fun x : User =>
                decay (t - t_sub st) *
                (getR x (W_user st) *
                 decay (t_sub st - getR x (T_user st))))
             (fun x : User =>
                getR x (W_user st) *
                decay (t - getR x (T_user st)))
          ).
  2:{
    intro x.
    rewrite <- Rmult_assoc.
    rewrite (Rmult_comm (decay (t - t_sub st)) (getR x (W_user st))).
    rewrite Rmult_assoc.
    rewrite decay_add.
    f_equal.
    f_equal.
    ring.
  }

  replace (getR u (L_f st))
    with
      ((fun x : User =>
          if Nat.eq_dec x u
          then w u st
          else getR x (W_user st) * decay (t - getR x (T_user st))) u).
  2:{
    unfold w.
    destruct (Nat.eq_dec u u) as [_|Hneq]; [reflexivity|contradiction].
  }

    assert (Hmap_remove :
    map (fun x : User =>
           getR x (W_user st) * decay (t - getR x (T_user st)))
        (remove Nat.eq_dec u Users)
    =
    map (fun x : User =>
           if Nat.eq_dec x u
           then w u st
           else getR x (W_user st) * decay (t - getR x (T_user st)))
        (remove Nat.eq_dec u Users)).
  {
    apply map_ext_in.
    intros x Hxin.
    destruct (Nat.eq_dec x u) as [Heq|Hneq].
    - subst x.
      apply remove_In in Hxin.
      contradiction.
    - reflexivity.
  }

  rewrite Hmap_remove.

  rewrite <- (sum_split_remove
                Users
                u
                (fun x : User =>
                   if Nat.eq_dec x u
                   then w u st
                   else getR x (W_user st) *
                        decay (t - getR x (T_user st)))
             ); try assumption.

  simpl.
  destruct (Nat.eq_dec u u) as [_|Hneq]; [reflexivity|contradiction].
Qed.

(** Argument corresponding to lines (25) to (29) in the paper proof.
    This proves the updated [pbar'] is the updated numerator divided by the updated denominator. *)

Lemma pbar'_eq_sum_PWdecay :
  forall (st : OracleState) (u : User) (v : value) (t : timestamp),
    In u Users ->
    NoDup Users ->
    pbar st * Q st =
      ideal_num_at_submission_time st ->
    pbar' u v t st =
      (sum_list_R
         (map (fun x =>
                 if Nat.eq_dec x u
                 then v * w u st
                 else getR x (P_user st) *
                      getR x (W_user st) *
                      decay (t - getR x (T_user st)))
              Users))
      / (Q' u t st).
Proof.
  intros st u v t Hu Hnodup HNum.
  unfold pbar'.
  unfold ideal_num_at_submission_time in HNum.
  unfold w, pu, wu, tu.

  rewrite HNum.

  rewrite (sum_split_remove
             Users
             u
             (fun x =>
                getR x (P_user st) *
                getR x (W_user st) *
                decay (t_sub st - getR x (T_user st)))
          ); try assumption.

  replace
    (((sum_list_R
         (map
            (fun x : User =>
               getR x (P_user st) *
               getR x (W_user st) *
               decay (t_sub st - getR x (T_user st)))
            (remove Nat.eq_dec u Users))
       +
       getR u (P_user st) *
       getR u (W_user st) *
       decay (t_sub st - getR u (T_user st))
       -
       getR u (P_user st) *
       getR u (W_user st) *
       decay (t_sub st - getR u (T_user st)))
      * decay (t - t_sub st) + v * getR u (L_f st)))
  with
    ((sum_list_R
        (map
           (fun x : User =>
              getR x (P_user st) *
              getR x (W_user st) *
              decay (t_sub st - getR x (T_user st)))
           (remove Nat.eq_dec u Users)))
      * decay (t - t_sub st) + v * getR u (L_f st))
  by ring.

  rewrite Rmult_comm.
  rewrite <- (sum_list_R_map_mult_const
                (decay (t - t_sub st))
                (fun x : User =>
                   getR x (P_user st) *
                   getR x (W_user st) *
                   decay (t_sub st - getR x (T_user st)))
                (remove Nat.eq_dec u Users)).

  rewrite (map_ext
             (fun x : User =>
                decay (t - t_sub st) *
                (getR x (P_user st) *
                 getR x (W_user st) *
                 decay (t_sub st - getR x (T_user st))))
             (fun x : User =>
                getR x (P_user st) *
                getR x (W_user st) *
                decay (t - getR x (T_user st)))).
  2:{
    intro a.
    repeat rewrite <- Rmult_assoc.
    rewrite (Rmult_comm (decay (t - t_sub st)) (getR a (P_user st))).
    rewrite (Rmult_assoc (getR a (P_user st)) (decay (t - t_sub st)) (getR a (W_user st))).
    rewrite (Rmult_comm (decay (t - t_sub st)) (getR a (W_user st))).
    rewrite <- (Rmult_assoc (getR a (P_user st)) (getR a (W_user st)) (decay (t - t_sub st))).
    rewrite (Rmult_assoc (getR a (P_user st) * getR a (W_user st))
               (decay (t - t_sub st))
               (decay (t_sub st - getR a (T_user st)))).
    rewrite decay_add.
    f_equal.
    f_equal.
    ring.
  }

  replace (v * getR u (L_f st))
    with
      ((fun x : User =>
          if Nat.eq_dec x u
          then v * w u st
          else getR x (P_user st) *
               getR x (W_user st) *
               decay (t - getR x (T_user st))) u).
  2:{
    unfold w.
    destruct (Nat.eq_dec u u) as [_|Hneq]; [reflexivity|contradiction].
  }

  assert (Hmap_remove :
    map (fun x : User =>
           getR x (P_user st) *
           getR x (W_user st) *
           decay (t - getR x (T_user st)))
        (remove Nat.eq_dec u Users)
    =
    map (fun x : User =>
           if Nat.eq_dec x u
           then v * w u st
           else getR x (P_user st) *
                getR x (W_user st) *
                decay (t - getR x (T_user st)))
        (remove Nat.eq_dec u Users)).
  {
    apply map_ext_in.
    intros x Hxin.
    destruct (Nat.eq_dec x u) as [Heq|Hneq].
    - subst x.
      apply remove_In in Hxin.
      contradiction.
    - reflexivity.
  }

  rewrite Hmap_remove.

  rewrite <- (sum_split_remove
                Users
                u
                (fun x : User =>
                   if Nat.eq_dec x u
                   then v * w u st
                   else getR x (P_user st) *
                        getR x (W_user st) *
                        decay (t - getR x (T_user st)))
             ); try assumption.

  simpl.
  destruct (Nat.eq_dec u u) as [_|Hneq]; [reflexivity|contradiction].
Qed.

(** The oracle state after performing a submission update. *)

Definition submitted_oracle_state
  (st : OracleState) (u : User) (v : value) (t : timestamp) : OracleState :=
  {|
    L_l    := L_l st;
    L_f    := L_f st;
    T_dep  := T_dep st;
    T_op   := T_op st;
    P_user := setR u v (P_user st);
    W_user := setR u (w u st) (W_user st);
    T_user := setR u t (T_user st);
    pbar   := pbar' u v t st;
    ptilde := v;
    Q      := Q' u t st;
    Phist  := Phist st;
    t_sub  := t;
    t_last := t;
    L_tot  := L_tot st;
    G      := G st
  |}.

(** Rewrites submission numerator sum into the numerator expression of [submitted_oracle_state] **)

Lemma submission_num_eq_factored_num :
  forall (st : OracleState) (u : User) (v : value) (t : timestamp),
    sum_list_R
      (map (fun x =>
              if Nat.eq_dec x u
              then v * w u st
              else getR x (P_user st) *
                   getR x (W_user st) *
                   decay (t - getR x (T_user st)))
           Users)
    =
    sum_list_R
      (map (fun x =>
              getR x (P_user (submitted_oracle_state st u v t)) *
              W_decayed (submitted_oracle_state st u v t) x t)
           Users).
Proof.
  intros st u v t.
  unfold W_decayed, submitted_oracle_state, w.
  apply f_equal.
  apply map_ext.
  intro x.
  destruct (Nat.eq_dec x u) as [Heq|Hneq].

  - subst x.
    simpl.
    repeat rewrite getR_setR_eq.
    replace (t - t) with 0 by ring.
    rewrite decay_0.
    ring.
  - simpl.
    repeat rewrite getR_setR_neq by assumption.
    ring.
Qed.

(** This rewrites the submission denominator sum into the denominator expression of [submitted_oracle_state] *)

Lemma submission_den_eq_factored_den :
  forall (st : OracleState) (u : User) (v : value) (t : timestamp),
    sum_list_R
      (map (fun x =>
              if Nat.eq_dec x u
              then w u st
              else getR x (W_user st) *
                   decay (t - getR x (T_user st)))
           Users)
    =
    sum_list_R
      (map (fun x =>
              W_decayed (submitted_oracle_state st u v t) x t)
           Users).
Proof.
  intros st u v t.
  unfold W_decayed, submitted_oracle_state, w.
  apply f_equal.
  apply map_ext.
  intro x.
  destruct (Nat.eq_dec x u) as [Heq|Hneq].
  - subst x.
    simpl.
    repeat rewrite getR_setR_eq.
    replace (t - t) with 0 by ring.
    rewrite decay_0.
    ring.
  - simpl.
    repeat rewrite getR_setR_neq by assumption.
    ring.
Qed.

(** This shows that [pbar'] equals the ideal mean of the submitted state at the submission time. *)

Lemma pbar'_eq_P_submitted_state :
  forall (st : OracleState) (u : User) (v : value) (t : timestamp),
    In u Users ->
    NoDup Users ->
    pbar st * Q st = ideal_num_at_submission_time st ->
    Q st = ideal_Q_at_submission_time st ->
    pbar' u v t st = P_ (submitted_oracle_state st u v t) t.
Proof.
  intros st u v t Hu Hnodup HNum HQ.

  rewrite pbar'_eq_sum_PWdecay by assumption.
  rewrite (Q'_eq_sum_Wdecay st u t Hu Hnodup HQ).
  rewrite submission_num_eq_factored_num.
  erewrite submission_den_eq_factored_den.
  unfold P_.
  reflexivity.
Qed.

Lemma submission_den_sum_pos :
  forall st u t,
    In u Users ->
    NoDup Users ->
    (forall x, 0 <= getR x (W_user st)) ->
    0 < w u st ->
    0 <
    sum_list_R
      (map
         (fun x =>
            if Nat.eq_dec x u
            then w u st
            else getR x (W_user st) *
                 decay (t - getR x (T_user st)))
         Users).
Proof.
  intros st u t Hu Hnodup Hnonneg Hwu_pos.

  set (f := fun x : nat =>
              if Nat.eq_dec x u
              then w u st
              else getR x (W_user st) *
                   decay (t - getR x (T_user st))).

  replace (sum_list_R (map f Users))
    with (sum_list_R (map f (remove Nat.eq_dec u Users)) + f u).
  2:{
    symmetry.
    apply sum_split_remove; assumption.
  }

  unfold f.
  simpl.
  rewrite Rplus_comm.


  assert (Hsum_ge :
    sum_list_R
      (map
         (fun x : nat =>
            if Nat.eq_dec x u
            then w u st
            else getR x (W_user st) * decay (t - getR x (T_user st)))
         (remove Nat.eq_dec u Users)) >= 0).
  {
    apply sum_list_R_nonneg_nonneg.
    intros x.
    destruct (Nat.eq_dec x u) as [Heq|Hneq].
    - lra.
    - apply Rle_ge.
      apply Rmult_le_pos.
      + apply Hnonneg.
      + left. apply decay_pos.
  }

  destruct (Nat.eq_dec u u) as [_|Hneq].
  - lra.
  - contradiction.
Qed.

(** *** Invariants and theorem statement *)

(** The stored [Q] is the ideal denominator at [t_sub], and [pbar * Q] is the ideal numerator at [t_sub]. *)

Definition mean_raw_eq (st : OracleState) : Prop :=
  Q st = ideal_Q_at_submission_time st /\
  pbar st * Q st = ideal_num_at_submission_time st.

Lemma init_mean_raw :
  mean_raw_eq init_oracle.
Proof.
  unfold init_oracle.
  unfold mean_raw_eq.
  split.
  - unfold ideal_Q_at_submission_time.
    simpl.
    rewrite (map_ext
      (fun x : User =>
         getR x (UserMap.empty weight) *
         decay (0 - getR x (UserMap.empty timestamp)))
      (fun _ : User => 0)).
    2:{
      intro x.
      unfold getR.
      simpl.
      ring.
    }
    induction Users as [|x xs IH].
    + simpl. reflexivity.
    + simpl. rewrite <- IH. rewrite Rplus_0_r. reflexivity.

  - unfold ideal_num_at_submission_time.
    simpl.
    rewrite (map_ext
      (fun x : User =>
         getR x (UserMap.empty value) *
         getR x (UserMap.empty weight) *
         decay (0 - getR x (UserMap.empty timestamp)))
      (fun _ : User => 0)).
    2:{
      intro x.
      unfold getR.
      simpl.
      ring.
    }
    induction Users as [|x xs IH].
    + simpl. ring.
    + simpl. rewrite IH. ring.
Qed.

(** Submission preserves [mean_raw_eq]. *)

Lemma mean_raw_eq_preserved_submission :
  forall (St : State) (u : User) (v : value) (t : timestamp),
    In u Users ->
    NoDup Users ->
    0 < w u (Unlock (V St) u t) -> (* only users who have positive unlocked stake can submit.
                                      also to ensure denominator stays positive. *)
    mean_raw_eq (V St) ->
    mean_raw_eq (V (value_submission u v t St)).
Proof.
  intros St u v t Hu Hnodup Hwu_pos [HQraw HNraw].

  set (st0 := V St).
  set (st1 := Unlock st0 u t).
  set (st2 := V (value_submission u v t St)).

  assert (Hunlock : mean_raw_eq st1).
  {
    subst st1 st0.
    destruct (Unlock_preserves_mean_fields (V St) u t) as
      [HPuser [HWuser [HTuser [Hpbar [HQ Htsub]]]]].
    unfold mean_raw_eq in *.
    split.
    - unfold ideal_Q_at_submission_time.
      simpl.
      rewrite HQ.
      rewrite (map_ext
        (fun x : User =>
           getR x (W_user (Unlock (V St) u t)) *
           decay (t_sub (Unlock (V St) u t) - getR x (T_user (Unlock (V St) u t))))
        (fun x : User =>
           getR x (W_user (V St)) *
           decay (t_sub (V St) - getR x (T_user (V St))))).
      2:{
        intro x.
        rewrite HWuser, HTuser, Htsub.
        reflexivity.
      }
      exact HQraw.
    - unfold ideal_num_at_submission_time.
      simpl.
      rewrite Hpbar, HQ.
      rewrite (map_ext
        (fun x : User =>
           getR x (P_user (Unlock (V St) u t)) *
           getR x (W_user (Unlock (V St) u t)) *
           decay (t_sub (Unlock (V St) u t) - getR x (T_user (Unlock (V St) u t))))
        (fun x : User =>
           getR x (P_user (V St)) *
           getR x (W_user (V St)) *
           decay (t_sub (V St) - getR x (T_user (V St))))).
      2:{
        intro x.
        rewrite HPuser, HWuser, HTuser, Htsub.
        reflexivity.
      }
      exact HNraw.
  }

  destruct Hunlock as [HQ1 HN1].
  unfold mean_raw_eq.
  split.

  - (* denominator equality for st2 *)
    subst st2 st1 st0.
    unfold value_submission.
    simpl.
    rewrite (Q'_eq_sum_Wdecay (Unlock (V St) u t) u t Hu Hnodup HQ1).
    unfold ideal_Q_at_submission_time.
    simpl.
    rewrite (map_ext
      (fun x : User =>
         getR x
           (W_user
              {|
                L_l := L_l (Unlock (V St) u t);
                L_f := L_f (Unlock (V St) u t);
                T_dep := T_dep (Unlock (V St) u t);
                T_op := T_op (Unlock (V St) u t);
                P_user := setR u v (P_user (Unlock (V St) u t));
                W_user := setR u (w u (Unlock (V St) u t)) (W_user (Unlock (V St) u t));
                T_user := setR u t (T_user (Unlock (V St) u t));
                pbar := pbar' u v t (Unlock (V St) u t);
                ptilde := v;
                Q := Q' u t (Unlock (V St) u t);
                Phist := Phist (Unlock (V St) u t) ++ (t, pbar' u v t (Unlock (V St) u t), v) :: nil;
                t_sub := t;
                t_last := t;
                L_tot := L_tot (Unlock (V St) u t);
                G := G (Unlock (V St) u t)
              |}) *
         decay
           (t -
            getR x
              (T_user
                 {|
                   L_l := L_l (Unlock (V St) u t);
                   L_f := L_f (Unlock (V St) u t);
                   T_dep := T_dep (Unlock (V St) u t);
                   T_op := T_op (Unlock (V St) u t);
                   P_user := setR u v (P_user (Unlock (V St) u t));
                   W_user := setR u (w u (Unlock (V St) u t)) (W_user (Unlock (V St) u t));
                   T_user := setR u t (T_user (Unlock (V St) u t));
                   pbar := pbar' u v t (Unlock (V St) u t);
                   ptilde := v;
                   Q := Q' u t (Unlock (V St) u t);
                   Phist := Phist (Unlock (V St) u t) ++ (t, pbar' u v t (Unlock (V St) u t), v) :: nil;
                   t_sub := t;
                   t_last := t;
                   L_tot := L_tot (Unlock (V St) u t);
                   G := G (Unlock (V St) u t)
                 |})))
      (fun x : User =>
         if Nat.eq_dec x u
         then w u (Unlock (V St) u t)
         else getR x (W_user (Unlock (V St) u t)) *
              decay (t - getR x (T_user (Unlock (V St) u t))))).
    2:{
      intro x.
      destruct (Nat.eq_dec x u) as [Heq|Hneq].
      - subst x.
        simpl.
        repeat rewrite getR_setR_eq.
        replace (t - t) with 0 by ring.
        rewrite decay_0.
        ring.
      - simpl.
        repeat rewrite getR_setR_neq by assumption.
        reflexivity.
    }
    reflexivity.

  - (* numerator equality for st2 *)
    subst st2 st1 st0.
    unfold value_submission.
    simpl.
    rewrite (pbar'_eq_sum_PWdecay (Unlock (V St) u t) u v t Hu Hnodup HN1).
    rewrite (Q'_eq_sum_Wdecay (Unlock (V St) u t) u t Hu Hnodup HQ1).
    unfold ideal_num_at_submission_time.
    simpl.
        set (den :=
      sum_list_R
        (map
           (fun x : nat =>
              if Nat.eq_dec x u
              then w u (Unlock (V St) u t)
              else getR x (W_user (Unlock (V St) u t)) *
                   decay (t - getR x (T_user (Unlock (V St) u t))))
           Users)).

    assert (Hdenpos : 0 < den).
    {
      unfold den.
      apply submission_den_sum_pos.
      - exact Hu.
      - apply Hnodup.
      - intros x.
        pose proof (B_user_w_nonneg_hyp x (Unlock (V St) u t)).
        lra.
      - exact Hwu_pos.
    }

    unfold Rdiv.
    rewrite Rmult_assoc.
    rewrite Rinv_l; try lra.
    rewrite Rmult_1_r.
    rewrite submission_num_eq_factored_num.
    unfold W_decayed.
    simpl.
    apply f_equal.
    apply map_ext.
    intro x.
    ring.
Qed.

(** Main predicate that [P(t) = pbar]. *)

Definition mean_eq_curr_pbar (st : OracleState) : Prop :=
  0 < Q st ->
  P_ st (t_sub st) = pbar st.

Lemma mean_raw_eq_implies_mean_eq_curr_pbar :
  forall st,
    mean_raw_eq st ->
    mean_eq_curr_pbar st.
Proof.
  intros st [HQraw HNraw].
  unfold mean_eq_curr_pbar.
  intro HQpos.
  unfold ideal_Q_at_submission_time in HQraw.
  unfold ideal_num_at_submission_time in HNraw.
  unfold P_.
    assert (Hnum_map :
    map (fun x : User => getR x (P_user st) * W_decayed st x (t_sub st)) Users
    =
    map (fun x : User =>
           getR x (P_user st) *
           getR x (W_user st) *
           decay (t_sub st - getR x (T_user st))) Users).
  {
    apply map_ext.
    intro x.
    unfold W_decayed.
    ring.
  }
  rewrite Hnum_map.

  assert (Hden_map :
    map (fun x : User => W_decayed st x (t_sub st)) Users
    =
    map (fun x : User =>
           getR x (W_user st) *
           decay (t_sub st - getR x (T_user st))) Users).
  {
    apply map_ext.
    intro x.
    unfold W_decayed.
    reflexivity.
  }
  rewrite Hden_map.

  rewrite <- HNraw.
  rewrite <- HQraw.

  unfold Rdiv.
  rewrite Rmult_assoc.
  rewrite Rinv_r.
  - rewrite Rmult_1_r.
    reflexivity.
  - lra.
Qed.

Lemma mean_eq_curr_pbar_preserved_submission :
  forall (St : State) (u : User) (v : value) (t : timestamp),
    In u Users ->
    NoDup Users ->
    0 < w u (Unlock (V St) u t) ->
    mean_raw_eq (V St) ->
    mean_eq_curr_pbar (V (value_submission u v t St)).
Proof.
  intros St u v t Hu Hnodup Hwu_pos Hraw.
  apply mean_raw_eq_implies_mean_eq_curr_pbar.
  eapply mean_raw_eq_preserved_submission; eauto.
Qed.

(** Needed assumptions (for submission case):
   - [In u Users] (needed to factor out [u] from a sum across [Users]
   - and [0 < w u (Unlock (V (state_at run n)) u t)],
     that only users with positive unlocked stake can submit.
 *)

Definition submission_assumptions_at (run : Run) (n : nat) : Prop :=
  match run n with
  | Submission u v t =>
      In u Users /\
      0 < w u (Unlock (V (state_at run n)) u t)
  | _ => True
  end.

Definition submission_assumptions (run : Run) : Prop :=
  forall n, submission_assumptions_at run n.

(** *** [mean_raw_eq_preserved_step] and subcases
    The next few lemmas show that [mean_raw_eq], the main predicate,
 *)

Lemma mean_raw_eq_preserved_deposit :
  forall (St : State) (u : User) (a : balance) (t : timestamp),
    mean_raw_eq (V St) ->
    mean_raw_eq (V (token_deposit u a t St)).
Proof.
  intros St u a t [HQraw HNraw].

  destruct (token_deposit_preserves_mean_fields St u a t) as
    [HPuser [HWuser [HTuser [Hpbar [HQ Htsub]]]]].

  unfold mean_raw_eq.
  split.
  - unfold ideal_Q_at_submission_time.
    simpl.
    rewrite HQ.
    rewrite (map_ext
      (fun x : User =>
         getR x (W_user (V (token_deposit u a t St))) *
         decay (t_sub (V (token_deposit u a t St)) - getR x (T_user (V (token_deposit u a t St)))))
      (fun x : User =>
         getR x (W_user (V St)) *
         decay (t_sub (V St) - getR x (T_user (V St))))).
    2:{
      intro x.
      rewrite HWuser, HTuser, Htsub.
      reflexivity.
    }
    exact HQraw.

  - unfold ideal_num_at_submission_time.
    simpl.
    rewrite Hpbar, HQ.
    rewrite (map_ext
      (fun x : User =>
         getR x (P_user (V (token_deposit u a t St))) *
         getR x (W_user (V (token_deposit u a t St))) *
         decay (t_sub (V (token_deposit u a t St)) - getR x (T_user (V (token_deposit u a t St)))))
      (fun x : User =>
         getR x (P_user (V St)) *
         getR x (W_user (V St)) *
         decay (t_sub (V St) - getR x (T_user (V St))))).
    2:{
      intro x.
      rewrite HPuser, HWuser, HTuser, Htsub.
      reflexivity.
    }
    exact HNraw.
Qed.

Lemma mean_raw_eq_preserved_withdrawal :
  forall (St : State) (u : User) (a : balance) (t : timestamp),
    mean_raw_eq (V St) ->
    mean_raw_eq (V (token_withdrawal u a t St)).
Proof.
  intros St u a t [HQraw HNraw].

  destruct (token_withdrawal_preserves_mean_fields St u a t) as
    [HPuser [HWuser [HTuser [Hpbar [HQ Htsub]]]]].

  unfold mean_raw_eq.
  split.
  - unfold ideal_Q_at_submission_time.
    simpl.
    rewrite HQ.
    rewrite (map_ext
      (fun x : User =>
         getR x (W_user (V (token_withdrawal u a t St))) *
         decay (t_sub (V (token_withdrawal u a t St)) - getR x (T_user (V (token_withdrawal u a t St)))))
      (fun x : User =>
         getR x (W_user (V St)) *
         decay (t_sub (V St) - getR x (T_user (V St))))).
    2:{
      intro x.
      rewrite HWuser, HTuser, Htsub.
      reflexivity.
    }
    exact HQraw.

  - unfold ideal_num_at_submission_time.
    simpl.
    rewrite Hpbar, HQ.
    rewrite (map_ext
      (fun x : User =>
         getR x (P_user (V (token_withdrawal u a t St))) *
         getR x (W_user (V (token_withdrawal u a t St))) *
         decay (t_sub (V (token_withdrawal u a t St)) - getR x (T_user (V (token_withdrawal u a t St)))))
      (fun x : User =>
         getR x (P_user (V St)) *
         getR x (W_user (V St)) *
         decay (t_sub (V St) - getR x (T_user (V St))))).
    2:{
      intro x.
      rewrite HPuser, HWuser, HTuser, Htsub.
      reflexivity.
    }
    exact HNraw.
Qed.

Lemma mean_raw_eq_preserved_reading :
  forall (St : State) (u : User) (t : timestamp),
    mean_raw_eq (V St) ->
    mean_raw_eq (value_reading u t (V St)).
Proof.
  intros St u t [HQraw HNraw].

  destruct (value_reading_preserves_mean_fields (V St) u t) as
    [HPuser [HWuser [HTuser [Hpbar [HQ Htsub]]]]].

  unfold mean_raw_eq.
  split.
  - unfold ideal_Q_at_submission_time.
    simpl.
    rewrite HQ.
    rewrite (map_ext
      (fun x : User =>
         getR x (W_user (value_reading u t (V St))) *
         decay (t_sub (value_reading u t (V St)) - getR x (T_user (value_reading u t (V St)))))
      (fun x : User =>
         getR x (W_user (V St)) *
         decay (t_sub (V St) - getR x (T_user (V St))))).
    2:{
      intro x.
      rewrite HWuser, HTuser, Htsub.
      reflexivity.
    }
    exact HQraw.

  - unfold ideal_num_at_submission_time.
    simpl.
    rewrite Hpbar, HQ.
    rewrite (map_ext
      (fun x : User =>
         getR x (P_user (value_reading u t (V St))) *
         getR x (W_user (value_reading u t (V St))) *
         decay (t_sub (value_reading u t (V St)) - getR x (T_user (value_reading u t (V St)))))
      (fun x : User =>
         getR x (P_user (V St)) *
         getR x (W_user (V St)) *
         decay (t_sub (V St) - getR x (T_user (V St))))).
    2:{
      intro x.
      rewrite HPuser, HWuser, HTuser, Htsub.
      reflexivity.
    }
    exact HNraw.
Qed.

Lemma mean_raw_eq_preserved_blacklist_vote :
  forall (St : State) (u x : User) (t : timestamp),
    mean_raw_eq (V St) ->
    mean_raw_eq (blacklist_vote u x t (V St)).
Proof.
  intros St u x t [HQraw HNraw].

  destruct (blacklist_vote_preserves_mean_fields (V St) u x t) as
    [HPuser [HWuser [HTuser [Hpbar [HQ Htsub]]]]].

  unfold mean_raw_eq.
  split.
  - unfold ideal_Q_at_submission_time.
    simpl.
    rewrite HQ.
    rewrite (map_ext
      (fun y : User =>
         getR y (W_user (blacklist_vote u x t (V St))) *
         decay (t_sub (blacklist_vote u x t (V St)) - getR y (T_user (blacklist_vote u x t (V St)))))
      (fun y : User =>
         getR y (W_user (V St)) *
         decay (t_sub (V St) - getR y (T_user (V St))))).
    2:{
      intro y.
      rewrite HWuser, HTuser, Htsub.
      reflexivity.
    }
    exact HQraw.

  - unfold ideal_num_at_submission_time.
    simpl.
    rewrite Hpbar, HQ.
    rewrite (map_ext
      (fun y : User =>
         getR y (P_user (blacklist_vote u x t (V St))) *
         getR y (W_user (blacklist_vote u x t (V St))) *
         decay (t_sub (blacklist_vote u x t (V St)) - getR y (T_user (blacklist_vote u x t (V St)))))
      (fun y : User =>
         getR y (P_user (V St)) *
         getR y (W_user (V St)) *
         decay (t_sub (V St) - getR y (T_user (V St))))).
    2:{
      intro y.
      rewrite HPuser, HWuser, HTuser, Htsub.
      reflexivity.
    }
    exact HNraw.
Qed.

Lemma mean_raw_eq_preserved_whitelist_vote :
  forall (St : State) (u x : User) (t : timestamp),
    mean_raw_eq (V St) ->
    mean_raw_eq (whitelist_vote u x t (V St)).
Proof.
  intros St u x t [HQraw HNraw].

  destruct (whitelist_vote_preserves_mean_fields (V St) u x t) as
    [HPuser [HWuser [HTuser [Hpbar [HQ Htsub]]]]].

  unfold mean_raw_eq.
  split.
  - unfold ideal_Q_at_submission_time.
    simpl.
    rewrite HQ.
    rewrite (map_ext
      (fun y : User =>
         getR y (W_user (whitelist_vote u x t (V St))) *
         decay (t_sub (whitelist_vote u x t (V St)) - getR y (T_user (whitelist_vote u x t (V St)))))
      (fun y : User =>
         getR y (W_user (V St)) *
         decay (t_sub (V St) - getR y (T_user (V St))))).
    2:{
      intro y.
      rewrite HWuser, HTuser, Htsub.
      reflexivity.
    }
    exact HQraw.

  - unfold ideal_num_at_submission_time.
    simpl.
    rewrite Hpbar, HQ.
    rewrite (map_ext
      (fun y : User =>
         getR y (P_user (whitelist_vote u x t (V St))) *
         getR y (W_user (whitelist_vote u x t (V St))) *
         decay (t_sub (whitelist_vote u x t (V St)) - getR y (T_user (whitelist_vote u x t (V St)))))
      (fun y : User =>
         getR y (P_user (V St)) *
         getR y (W_user (V St)) *
         decay (t_sub (V St) - getR y (T_user (V St))))).
    2:{
      intro y.
      rewrite HPuser, HWuser, HTuser, Htsub.
      reflexivity.
    }
    exact HNraw.
Qed.

Lemma Recompute_preserves_mean_fields :
  forall (x : User) (st : OracleState),
    P_user (Recompute x st) = P_user st /\
    W_user (Recompute x st) = W_user st /\
    T_user (Recompute x st) = T_user st /\
    pbar   (Recompute x st) = pbar   st /\
    Q      (Recompute x st) = Q      st /\
    t_sub  (Recompute x st) = t_sub  st.
Proof.
  intros x st.
  unfold Recompute.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma reweight_black_step_preserves_mean_fields :
  forall (u x : User) (w : weight) (st : OracleState),
    P_user (reweight_black_step u w x st) = P_user st /\
    W_user (reweight_black_step u w x st) = W_user st /\
    T_user (reweight_black_step u w x st) = T_user st /\
    pbar   (reweight_black_step u w x st) = pbar   st /\
    Q      (reweight_black_step u w x st) = Q      st /\
    t_sub  (reweight_black_step u w x st) = t_sub  st.
Proof.
  intros u x w st.
  unfold reweight_black_step.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma reweight_white_step_preserves_mean_fields :
  forall (u x : User) (w : weight) (st : OracleState),
    P_user (reweight_white_step u w x st) = P_user st /\
    W_user (reweight_white_step u w x st) = W_user st /\
    T_user (reweight_white_step u w x st) = T_user st /\
    pbar   (reweight_white_step u w x st) = pbar   st /\
    Q      (reweight_white_step u w x st) = Q      st /\
    t_sub  (reweight_white_step u w x st) = t_sub  st.
Proof.
  intros u x w st.
  unfold reweight_white_step.
  simpl.
  repeat split; reflexivity.
Qed.

Lemma fold_left_black_preserves_mean_fields :
  forall (xs : list User) (u : User) (w : weight) (st : OracleState),
    P_user (fold_left (fun acc x => reweight_black_step u w x acc) xs st) = P_user st /\
    W_user (fold_left (fun acc x => reweight_black_step u w x acc) xs st) = W_user st /\
    T_user (fold_left (fun acc x => reweight_black_step u w x acc) xs st) = T_user st /\
    pbar   (fold_left (fun acc x => reweight_black_step u w x acc) xs st) = pbar   st /\
    Q      (fold_left (fun acc x => reweight_black_step u w x acc) xs st) = Q      st /\
    t_sub  (fold_left (fun acc x => reweight_black_step u w x acc) xs st) = t_sub  st.
Proof.
  induction xs as [|x xs IH]; intros u w st.
  - simpl. repeat split; reflexivity.
  - simpl.
    destruct (IH u w (reweight_black_step u w x st)) as
      [HP' [HW' [HT' [Hp' [HQ' Ht']]]]].
    destruct (reweight_black_step_preserves_mean_fields u x w st) as
      [HP [HW [HT [Hp [HQ Ht]]]]].
    rewrite <- HP, <- HW, <- HT, <- Hp, <- HQ, <- Ht.
    exact (conj HP' (conj HW' (conj HT' (conj Hp' (conj HQ' Ht'))))).
Qed.

Lemma fold_left_white_preserves_mean_fields :
  forall (xs : list User) (u : User) (w : weight) (st : OracleState),
    P_user (fold_left (fun acc x => reweight_white_step u w x acc) xs st) = P_user st /\
    W_user (fold_left (fun acc x => reweight_white_step u w x acc) xs st) = W_user st /\
    T_user (fold_left (fun acc x => reweight_white_step u w x acc) xs st) = T_user st /\
    pbar   (fold_left (fun acc x => reweight_white_step u w x acc) xs st) = pbar   st /\
    Q      (fold_left (fun acc x => reweight_white_step u w x acc) xs st) = Q      st /\
    t_sub  (fold_left (fun acc x => reweight_white_step u w x acc) xs st) = t_sub  st.
Proof.
  induction xs as [|x xs IH]; intros u w st.
  - simpl. repeat split; reflexivity.
  - simpl.
    destruct (IH u w (reweight_white_step u w x st)) as
      [HP' [HW' [HT' [Hp' [HQ' Ht']]]]].
    destruct (reweight_white_step_preserves_mean_fields u x w st) as
      [HP [HW [HT [Hp [HQ Ht]]]]].
    rewrite <- HP, <- HW, <- HT, <- Hp, <- HQ, <- Ht.
    exact (conj HP' (conj HW' (conj HT' (conj Hp' (conj HQ' Ht'))))).
Qed.

Lemma Reweight_preserves_mean_fields :
  forall (u : User) (w : weight) (st : OracleState),
    P_user (Reweight u w st) = P_user st /\
    W_user (Reweight u w st) = W_user st /\
    T_user (Reweight u w st) = T_user st /\
    pbar   (Reweight u w st) = pbar   st /\
    Q      (Reweight u w st) = Q      st /\
    t_sub  (Reweight u w st) = t_sub  st.
Proof.
  intros u w st.
  unfold Reweight.
  set (blacklisteds := getUserSet u (M_black (G st))).
  destruct (fold_left_black_preserves_mean_fields blacklisteds u w st) as
    [HP1 [HW1 [HT1 [Hp1 [HQ1 Ht1]]]]].
  rewrite <- HP1, <- HW1, <- HT1, <- Hp1, <- HQ1, <- Ht1.
  apply fold_left_white_preserves_mean_fields.
Qed.

Lemma weight_synchronization_preserves_mean_fields :
  forall (st : OracleState) (u : User) (t : timestamp),
    P_user (weight_synchronization u t st) = P_user st /\
    W_user (weight_synchronization u t st) = W_user st /\
    T_user (weight_synchronization u t st) = T_user st /\
    pbar   (weight_synchronization u t st) = pbar   st /\
    Q      (weight_synchronization u t st) = Q      st /\
    t_sub  (weight_synchronization u t st) = t_sub  st.
Proof.
  intros st u t.
  unfold weight_synchronization.
  destruct (Unlock_preserves_mean_fields st u t) as
    [HP0 [HW0 [HT0 [Hp0 [HQ0 Ht0]]]]].
  destruct (Reweight_preserves_mean_fields
              u (getR u (L_f (Unlock st u t))) (Unlock st u t)) as
    [HP1 [HW1 [HT1 [Hp1 [HQ1 Ht1]]]]].
  rewrite HP0, HW0, HT0, Hp0, HQ0, Ht0 in *.
  simpl.
  repeat split; assumption.
Qed.

Lemma mean_raw_eq_preserved_weight_sync :
  forall (St : State) (u : User) (t : timestamp),
    mean_raw_eq (V St) ->
    mean_raw_eq (weight_synchronization u t (V St)).
Proof.
  intros St u t [HQraw HNraw].
  destruct (weight_synchronization_preserves_mean_fields (V St) u t) as
    [HPuser [HWuser [HTuser [Hpbar [HQ Htsub]]]]].
  unfold mean_raw_eq.
  split.
  - unfold ideal_Q_at_submission_time.
    rewrite HQ.
    simpl.
    rewrite (map_ext
      (fun x : User =>
         getR x (W_user (weight_synchronization u t (V St))) *
         decay (t_sub (weight_synchronization u t (V St)) - getR x (T_user (weight_synchronization u t (V St)))))
      (fun x : User =>
         getR x (W_user (V St)) *
         decay (t_sub (V St) - getR x (T_user (V St))))).
    2:{
      intro x.
      rewrite HWuser, HTuser, Htsub.
      reflexivity.
    }
    exact HQraw.
  - unfold ideal_num_at_submission_time.
    rewrite Hpbar, HQ.
    simpl.
    rewrite (map_ext
      (fun x : User =>
         getR x (P_user (weight_synchronization u t (V St))) *
         getR x (W_user (weight_synchronization u t (V St))) *
         decay (t_sub (weight_synchronization u t (V St)) - getR x (T_user (weight_synchronization u t (V St)))))
      (fun x : User =>
         getR x (P_user (V St)) *
         getR x (W_user (V St)) *
         decay (t_sub (V St) - getR x (T_user (V St))))).
    2:{
      intro x.
      rewrite HPuser, HWuser, HTuser, Htsub.
      reflexivity.
    }
    exact HNraw.
Qed.

Lemma mean_raw_eq_preserved_reward_funding :
  forall (St : State) (u : User) (a : balance) (t : timestamp),
    mean_raw_eq (V St) ->
    mean_raw_eq (V (reward_funding u a t St)).
Proof.
  intros St u a t [HQraw HNraw].
  destruct (reward_funding_preserves_mean_fields St u a t) as
    [HPuser [HWuser [HTuser [Hpbar [HQ Htsub]]]]].
  unfold mean_raw_eq.
  split.
  - simpl.
    rewrite <- HQ.
    exact HQraw.
  - simpl.
    rewrite <- Hpbar.
    rewrite <- HQ.
    exact HNraw.
Qed.

Lemma mean_raw_eq_preserved_noneop :
  forall (St : State) (t : timestamp),
    mean_raw_eq (V St) ->
    mean_raw_eq (V St).
Proof.
  intros St t Hraw.
  exact Hraw.
Qed.

Lemma mean_raw_eq_preserved_step :
  forall (run : Run) (n : nat),
    submission_assumptions run ->
    mean_raw_eq (V (state_at run n)) ->
    mean_raw_eq (V (state_at run (S n))).
Proof.
  intros run n Hsubm Hraw.
  rewrite state_at_S.
  destruct (run n) as
      [u a t
      |u a t
      |u v t
      |u t
      |u x t
      |u x t
      |u t
      |u a t
      |t] eqn:Hop.
  - simpl. apply mean_raw_eq_preserved_deposit. exact Hraw.
  - simpl. apply mean_raw_eq_preserved_withdrawal. exact Hraw.
  - specialize (Hsubm n).
    unfold submission_assumptions_at in Hsubm.
    rewrite Hop in Hsubm.
    destruct Hsubm as [Hinu Hwu_pos].
    eapply mean_raw_eq_preserved_submission. exact Hinu. apply Users_NoDup. exact Hwu_pos. exact Hraw.
  - simpl. apply mean_raw_eq_preserved_reading. exact Hraw.
  - simpl. apply mean_raw_eq_preserved_blacklist_vote. exact Hraw.
  - simpl. apply mean_raw_eq_preserved_whitelist_vote. exact Hraw.
  - simpl. apply mean_raw_eq_preserved_weight_sync. exact Hraw.
  - simpl. apply (mean_raw_eq_preserved_reward_funding (state_at run n) u a). exact Hraw.
  - simpl. exact Hraw.
Qed.

(** *** Raw invariant along runs *)

Lemma mean_raw_eq_along_run :
  forall (run : Run) (n : nat),
    submission_assumptions run ->
    mean_raw_eq (V (state_at run n)).
Proof.
  intros run n Hsubm.
  induction n as [|n IH].
  - unfold state_at. simpl. unfold init_state. simpl. exact init_mean_raw.
  - apply mean_raw_eq_preserved_step.
    + exact Hsubm.
    + exact IH.
Qed.

(** *** Theorem 3 main statement *)

Theorem thm3 :
  forall (run : Run) (n : nat),
    submission_assumptions run ->
    mean_eq_curr_pbar (V (state_at run n)).
Proof.
  intros run n Hsubm.
  apply mean_raw_eq_implies_mean_eq_curr_pbar.
  apply mean_raw_eq_along_run.
  exact Hsubm.
Qed.

(** ** (Theorem 6): Inactive oracle operator delay

      If an oracle operator [u] in [U] becomes inactive,
      the operator delay [Lambda_u(t)] caused by this inactivity converges to 0.

      That is, [lim_{t -> \inf} Lambda_u(t) = 0].

      Proof: By manipulating the definition of [Lambda_u(t)] and getting it into a certain form equivalent to line (39) in the paper such that we can take the limit to be zero.
 *)

(** *** Decay definition *)

Definition Lambda_x (x : User) (t : timestamp) (st : OracleState): R :=
  (W_decayed st x t) * (t - getR x (T_user st)) /
                         sum_list_R (map (fun u => W_decayed st u t) Users).

Definition Lambda (t : timestamp) (st : OracleState) : R :=
  sum_list_R (map (fun u => Lambda_x u t st) Users).

Definition Lambda_run (run : Run) (u : User) (n : nat) : R :=
  let St := state_at run n in
  let st := V St in
  Lambda_x u (t_last st) st.

(** *** Inactivity definition
    A user [u] is inactive for a trace [tr] if there exists a timestamp [t_end], such that
    there are no submission operations [Submission u v t] with [t >= t_end] in [tr], and
    that any extensions of the trace [tr] will not contain a [Submission u v t] with [t >= t_end].
 *)

(** Meaning that there exists a step index N such that after step N, the run never contains [Submission _ _] again. *)

Definition inactive_along_run (run : Run) (u : User) : Prop :=
  exists N, forall n, (n >= N)%nat -> ~ is_submission_by u (op_at run n).

(** If a user is inactive in a run, then [T_user] and [W_user] are eventually constant.
    The lemmas for these are in the section about executing operations.
 *)

Lemma inactive_implies_TW_eventually_constant :
  forall run u,
    inactive_along_run run u ->
    exists N,
      forall n, (n >= N)%nat ->
        getR u (T_user (V (state_at run n))) = getR u (T_user (V (state_at run N))) /\
        getR u (W_user (V (state_at run n))) = getR u (W_user (V (state_at run N))).
Proof.
  intros run u [Nend Hno].
  exists Nend.
  intros n Hnge.

  (* Induction on k, where n = Nend + k *)
  remember (n - Nend)%nat as k eqn:Hk.
  assert (Hn : n = (Nend + k)%nat).
  { subst k. lia. }

  subst n.
  clear Hnge Hk.

  induction k as [|k IH].
  - rewrite <- plus_n_O. split; reflexivity.
  - replace (Nend + S k)%nat with (S (Nend + k))%nat by lia.
    rewrite state_at_S.
    specialize (Hno (Nend + k)%nat).
    assert (Hge_cut : (Nend + k >= Nend)%nat) by lia.
    specialize (Hno Hge_cut).

    destruct IH as [HTIH HWIH].

    pose proof (exec_op_preserves_TW_if_not_submit
                  (state_at run (Nend + k))
                  (run (Nend + k)%nat)
                  u
                  Hno) as [HTstep HWstep].

    split.
    + rewrite HTstep.
      exact HTIH.
    + rewrite HWstep.
      exact HWIH.
Qed.

(** *** Convergence / limit to zero formalization definition **)

Definition tends_to_0_nat (f : nat -> R) : Prop :=
  forall eps : R,
    eps > 0 ->
    exists N : nat, forall n : nat, (n >= N)%nat -> Rabs (f n) < eps.

Lemma tends_to_0_nat_ext :
  forall f g : nat -> R,
    (forall n, f n = g n) ->
    tends_to_0_nat f ->
    tends_to_0_nat g.
Proof.
  intros f g Heq Ht eps Heps.
  specialize (Ht eps Heps).
  destruct Ht as [N HN].
  exists N. intros n Hnge.
  rewrite <- Heq.
  apply HN; exact Hnge.
Qed.

(** *** Exponential dominates linear
    Crucial lemma that states that an exponential function dominates a linear function. *)

Lemma exp2_dominates_linear :
  forall (A B K c : R),
    0 <= A -> 0 < B -> 0 <= K -> 0 < c ->
    exists X0 : R, forall X : R,
      X0 <= X ->
      A * (X + K) < B * Rpower 2 (X / c).
Proof.
  intros A B K c HA HB HK Hc.

  set (a := (ln 2) / c).

  assert (Hln2_pos : 0 < ln 2).
  {
    assert (Hexp_ln2 : exp (ln 2) = 2).
    {
      apply exp_ln.
      lra.
    }

    assert (Hexp0 : exp 0 = 1).
    { apply exp_0. }

    assert (Hlt : exp 0 < exp (ln 2)).
    {
      rewrite Hexp0.
      rewrite Hexp_ln2.
      lra.
    }

    apply (exp_lt_inv 0 (ln 2)).
    exact Hlt.
  }

  assert (Ha_pos : 0 < a).
  {
    unfold a.
    apply Rmult_lt_0_compat.
    - exact Hln2_pos.
    - apply Rinv_0_lt_compat.
      exact Hc.
  }

  set (C := B * (a * a) / 4).

  assert (HC_pos : 0 < C).
  {
    unfold C.
    apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat.
      exact HB.
      apply Rmult_lt_0_compat; apply Ha_pos.
    - lra.
  }

  set (X0 := 1 + (2*A/C) + (2*A*K/C)).

  exists X0.
  intros X HX0.

    unfold Rpower.
  replace ((X / c) * ln 2) with (a * X).

  2:{
    unfold a.
    field.
    lra.
  }

  set (t := (a * X) / 2).

  assert (Hsplit : exp (a * X) = exp t * exp t).
  {
    replace (a * X) with ((a*X)/2 + (a*X)/2).
    - unfold t. apply exp_plus.
    - field.
  }

  assert (Hineq : 1 + t <= exp t).
  {
    apply exp_ineq1_le.
  }

  assert (HC_nonneg : 0 <= C) by (left; exact HC_pos).
  assert (HX0_ge_1 : 1 <= X0).
  {
    unfold X0.
    assert (Hterm1 : 0 <= 2 * A / C).
    {
      unfold Rdiv.
      apply Rmult_le_pos.
      - nra.
      - left.
        apply Rinv_0_lt_compat.
        lra.
    }
    assert (Hterm2 : 0 <= 2 * A * K / C).
    {
      unfold Rdiv.
      apply Rmult_le_pos.
      - nra.
      - left.
        apply Rinv_0_lt_compat.
        lra.
    }
    lra.
  }

  assert (HX_ge_1 : 1 <= X) by lra.
  assert (HX_nonneg : 0 <= X) by lra.

  assert (Ht_nonneg : 0 <= t).
  {
    unfold t.
    unfold Rdiv.
    apply Rmult_le_pos.
    - apply Rmult_le_pos.
      -- apply Rlt_le; exact Ha_pos.
      -- exact HX_nonneg.
    - apply Rlt_le; lra.
  }

  assert (H1t_nonneg : 0 <= 1 + t) by lra.
  assert (Hexp_nonneg : 0 <= exp t) by (left; apply exp_pos).

  assert (Ht2_le : t * t <= (1 + t) * (1 + t)) by nra.

  assert (Hsquare : (1 + t) * (1 + t) <= exp (a * X)).
  {
    rewrite Hsplit.
    apply Rmult_le_compat; lra.
  }

  assert (Hquad : t * t <= exp (a * X)).
  {
    eapply Rle_trans.
    - exact Ht2_le.
    - exact Hsquare.
  }

  assert (HquadB : B * (t * t) <= B * exp (a * X)).
  {
    apply Rmult_le_compat_l.
    - lra.
    - exact Hquad.
  }

  assert (Ht2_form : t * t = (a*a/4) * (X*X)).
  {
    unfold t.
    field.
  }

  rewrite Ht2_form in HquadB.

  assert (HC : 0 < C) by (unfold C; exact HC_pos).

  assert (Haff : A * (X + K) < C * (X * X)).
  {
    assert (Hpos1_2AK : 0 < 1 + 2 * A * K / C).
    {
      assert (Hnonneg_2AK : 0 <= 2 * A * K / C).
      {
        unfold Rdiv.
        apply Rmult_le_pos.
        - apply Rmult_le_pos; [|exact HK].
          apply Rmult_le_pos; lra.
        - apply Rlt_le.
          apply Rinv_0_lt_compat; lra.
      }
      lra.
    }

    assert (H2A_overC_ltX : 2 * A / C < X).
    {
      assert (Hlt : 2 * A / C < 2 * A / C + (1 + 2 * A * K / C)) by lra.

      assert (Hle : 2 * A / C + (1 + 2 * A * K / C) <= X).
      { replace (2 * A / C + (1 + 2 * A * K / C))
          with (1 + 2 * A / C + 2 * A * K / C) by ring;
          exact HX0. }

      exact (Rlt_le_trans _ _ _ Hlt Hle).
    }

    assert (Hpos1_2A : 0 < 1 + 2 * A / C).
    {
      assert (Hnonneg_2A : 0 <= 2 * A / C).
      {
        unfold Rdiv.
        apply Rmult_le_pos.
        - lra.
        - apply Rlt_le.
          apply Rinv_0_lt_compat; lra.
      }
      lra.
    }

    assert (H2AK_overC_ltX : 2 * A * K / C < X).
    {
      assert (Hlt : 2 * A * K / C < 2 * A * K / C + (1 + 2 * A / C)) by lra.
      assert (Hle : 2 * A * K / C + (1 + 2 * A / C) <= X).
      {
        replace (2 * A * K / C + (1 + 2 * A / C))
          with (1 + 2 * A / C + 2 * A * K / C) by ring;
          exact HX0.
      }

      exact (Rlt_le_trans _ _ _ Hlt Hle).
    }

    assert (HX_pos : 0 < X).
    {
      assert (H2A_overC_nonneg : 0 <= 2 * (A / C)).
      {
        apply Rmult_le_pos.
        - lra.
        - apply Rmult_le_pos.
          + exact HA.
          + left. apply Rinv_0_lt_compat. exact HC_pos.
      }
      lra.
    }

    assert (HAX_lt_halfCX2 : A * X < (C/2) * (X * X)).
    {
      assert (H2A_lt_CX : 2 * A < C * X).
      {
        assert (Htmp : (2 * A / C) * C < X * C).
        {
          apply Rmult_lt_compat_r; lra.
        }
        unfold Rdiv in Htmp.
        field_simplify in Htmp; lra.
      }
      assert (HA_lt_halfCX : A < (C/2) * X).
      {
        assert (Hhalf : 0 < /2) by lra.
        assert (Htmp : (2 * A) * (/2) < (C * X) * (/2)).
        {
          apply Rmult_lt_compat_r; lra.
        }
        field_simplify in Htmp; lra.
      }
      assert (Htmp : A * X < ((C/2) * X) * X).
      {
        apply Rmult_lt_compat_r; lra.
      }
      ring_simplify in Htmp.
      ring_simplify.
      exact Htmp.
    }

    assert (HAK_le_halfCX2 : A * K <= (C/2) * (X * X)).
    {
      assert (H2AK_lt_CX : 2 * A * K < C * X).
      {
        assert (Htmp : (2 * A * K / C) * C < X * C).
        { apply Rmult_lt_compat_r; lra. }
        unfold Rdiv in Htmp.
        field_simplify in Htmp; lra.
      }

      assert (HAK_lt_halfCX : A * K < (C/2) * X).
      {
        assert (Hhalf : 0 < /2) by lra.
        assert (Htmp : (2 * A * K) * (/2) < (C * X) * (/2)).
        { apply Rmult_lt_compat_r; lra. }
        field_simplify in Htmp; lra.
      }

      assert (HX_le_X2 : X <= X * X).
      {
        replace X with (X * 1) by ring.
        replace (X * 1) with ((X * 1) * 1) at 1 by ring.
        apply Rmult_le_compat_l; lra.
      }

      assert (HhalfCX_le_halfCX2 : (C/2) * X <= (C/2) * (X * X)).
      {
        apply Rmult_le_compat_l.
        - lra.
        - exact HX_le_X2.
      }

      eapply Rlt_le; eapply Rlt_le_trans.
      - exact HAK_lt_halfCX.
      - exact HhalfCX_le_halfCX2.
    }

    replace (A * (X + K)) with (A * X + A * K) by ring.
    eapply Rlt_le_trans.
    - apply Rplus_lt_le_compat; [exact HAX_lt_halfCX2 | exact HAK_le_halfCX2].
    - lra.

  }
  eapply Rlt_le_trans.
  - exact Haff.
  - unfold C.
    replace (B * (a * a) / 4 * (X * X)) with (B * (a * a / 4 * (X * X))) by lra.
    exact HquadB.
Qed.

(** *** Rewriting to form in line 38 in paper
The lemmas rewriting [Lambda(u)] (oracle operator delay) to the form in line 38. *)

Lemma Lambda_u_rewrite_38 :
  forall (st : OracleState) (t : timestamp) (u : User),
    (* these two assumptions are needed because we factor out a term in the bounds of the sum *)
    (* yet we have Users as a list and not a true set - we make it act like a set in that there is no duplicates *)
    (* so that removing a term in the summation is sound *)
    In u Users ->
    NoDup Users ->
    (* these two are needed so that the denominator is non-zero so we do not divide by zero *)
    (* 1. that the weights of users are nonnegative (assumed in a wellformed state anyway) *)
    (* 2. one weight needs to be positive so that the denominator is positive i.e. non zero *)
    (forall x, getR x (W_user st) >= 0) ->
    (exists u0, In u0 Users /\ getR u0 (W_user st) > 0) ->
    Lambda_x u t st =
      ((getR u (W_user st)) * (t - (getR u (T_user st)))) /
        ((sum_list_R
            (map
               (fun x => (getR x (W_user st)) *
                           (Rpower 2 (((getR x (T_user st)) - (getR u (T_user st))) / proj1_sig h)))
               (remove Nat.eq_dec u Users)))
         + (getR u (W_user st))).
Proof.
  intros st t u Huin Hnodup Hwunn Hu0.
  unfold Lambda_x.
  unfold W_decayed.
  unfold decay.
  set (h := proj1_sig h).
  destruct Oracle.h as [h_ r]. simpl in h.
  assert (Hexp : forall x,
             (-1 * (t - getR x (T_user st)) / h)
             = (-1 * (t - getR u (T_user st)) / h)
               + ((getR x (T_user st) - getR u (T_user st)) / h)).
  {
    intro x.
    field.
    subst h.
    lra.
  }

  rewrite Hexp.

  rewrite (Rpower_plus _ _ 2).

  assert (Hmap :
           map (fun x => getR x (W_user st) *
                           Rpower 2 (-1 * (t - getR x (T_user st)) / h)) Users
           =
             map (fun x => Rpower 2 (-1 * (t - getR u (T_user st)) / h) * (getR x (W_user st) *
                                                                             Rpower 2 ((getR x (T_user st) - getR u (T_user st)) / h))) Users).
  {
    apply map_ext. intro x.
    rewrite Hexp.
    rewrite Rpower_plus.
    lra.
  }

  rewrite Hmap in *.

  rewrite (sum_list_R_map_mult_const (Rpower 2 (-1 * (t - getR u (T_user st)) / h))
             (fun x => getR x (W_user st) *
                         Rpower 2 ((getR x (T_user st) - getR u (T_user st)) / h))
             Users).

  rewrite * Rdiv_def.

  replace ((getR u (T_user st) - getR u (T_user st)) / h) with 0.
  2 : {  field. subst h. lra. }

  rewrite (Rpower_O 2) by lra.

  rewrite Rmult_1_r.

  rewrite (sum_split_remove _ _ _ Hnodup Huin).

  replace ((getR u (T_user st) - getR u (T_user st)) / h) with 0.
  2 : {  field. subst h. lra. }

  rewrite (Rpower_O 2) by lra.
  rewrite Rmult_1_r.

  field.

  split; auto.
  - apply Rgt_not_eq.
    destruct Hu0 as [u0 [Hu0in Hu0']].
    destruct (Nat.eq_dec u u0).
    -- subst. replace 0 with (0 + 0) by field.
       apply Rplus_ge_gt_compat.
       apply sum_list_R_nonneg_nonneg.
       intros.
       specialize (Hwunn x).
       unfold Rpower.
       apply Rle_ge.
       apply Rmult_le_pos.
       lra.
       unfold Rle. left.
       apply exp_pos.
       auto.
    -- apply Rlt_gt.
       pose proof (Hwunn u).
       apply Rplus_lt_le_0_compat; try lra.
       apply sum_list_R_nn_exists_pos_pos.
       --- intros. apply Rmult_le_pos. pose proof (Hwunn x). lra.
           unfold Rle. left. apply exp_pos.
       --- exists u0. split. apply in_in_remove; auto.
           unfold Rpower.
           apply Rmult_lt_0_compat. lra. apply exp_pos.
  - unfold Rpower.
    pose proof (exp_pos (-1 * (t - getR u (T_user st)) / h * ln 2)).
    apply Rlt_not_eq in H. symmetry. apply H.
Qed.

Definition eq38_at (st : OracleState) (u : User) (t : timestamp) : R :=
  ((getR u (W_user st)) * (t - getR u (T_user st))) /
    ((sum_list_R (map (fun x =>
       getR x (W_user st) *
         Rpower 2 (((getR x (T_user st)) - (getR u (T_user st))) / proj1_sig h))
     (remove Nat.eq_dec u Users)))
     + getR u (W_user st)).

Lemma Lambda_x_eq38_at :
  forall st t u,
    In u Users ->
    NoDup Users ->
    (forall x, getR x (W_user st) >= 0) ->
    (exists u0, In u0 Users /\ getR u0 (W_user st) > 0) ->
   Lambda_x u t st = eq38_at st u t.
Proof.
  intros st t u Hu Hnodup Hnn Hpos.
  unfold eq38_at.
  apply Lambda_u_rewrite_38; auto.
Qed.

Hypothesis W_user_nonneg_hyp : forall u st, 0 <= getR u (W_user st).

(* that there is one positive weight inside W_user *)

Definition some_positive_weight (st : OracleState) : Prop :=
  exists u0, In u0 Users /\ getR u0 (W_user st) > 0.

(* That for all time, there is a submission by y in the run with a greater timestamp. *)

Definition unbounded_submissions (run : Run) (y : User) : Prop :=
  forall T : R,
    exists n,
      is_submission_by y (op_at run n) /\
      T <= getR y (T_user (V (state_at run n))).

(** *** Theorem 6 main statement *)

Theorem inactive_oracle_operator_delay :
  forall (run : Run) (u : User),
    (* for inactive operator *)
    In u Users ->
    inactive_along_run run u ->
    (* user submissions are monotonic in time *)
    (forall z n,
    getR z (T_user (V (state_at run n))) <=
    getR z (T_user (V (state_at run (S n))))) ->
    (* needed for the non-zeroness (i.e. positivity) of the denominator  *)
(*
    ( for all x in Users, 0 <= W_user(x) )
     exists x in users, 0 < W_user(x) ?   *)
    (forall i x, 0 <= getR x (W_user (V (state_at run i)))) ->
    (forall i, some_positive_weight (V (state_at run i))) ->
    (* that there is one other user that never becomes inactive *)
    (* for any time T, there is some other user that will make a submission after *)
    (exists y,
        In y Users /\
        y <> u /\
        unbounded_submissions run y /\
        (* To ensure that the numerator grows at most linearly in
        the same variable as the denominator *)
        (forall n : nat,
            getR y (T_user (V (state_at run n))) <= t_last (V (state_at run n))) /\

        (* TODO: try to show it follows from 2180 *)
        (exists K : R,
            0 <= K /\
            forall n : nat,
              t_last (V (state_at run n))
              <= getR y (T_user (V (state_at run n))) + K) /\
        (* To ensure that the denominator behaves as constant * exponential *)
        (* TODO: try to prove also and simplify... move to near  *)
        (exists wy_min : R,
            0 < wy_min /\
            exists Ny : nat,
              forall n : nat, (n >= Ny)%nat -> (* Can be simplified with just 0 *)
                wy_min <= getR y (W_user (V (state_at run n))))) ->
      tends_to_0_nat (Lambda_run run u).
Proof.

  intros run u Hinu Hinact_run T_user_mono.
  intros Hwunn Hposw [y [Hiny [Hneqyu [Hysub [Hytime [HK Hyposw]]]]]].
  destruct HK as [K [HK_nonneg Htlast_le_tyK]].
  (* first, rewrite Lambda to the form in eq38, then *)
  unfold Lambda_run.
  eapply tends_to_0_nat_ext with
    (f := fun n =>
            eq38_at (V (state_at run n)) u (t_last (V (state_at run n)))).
  - intro n.
    symmetry.
    apply Lambda_x_eq38_at. (* majority of the rewriting part *)
    apply Hinu.
    apply Users_NoDup.
    intro. apply Rle_ge.
    exact (Hwunn n x).
    exact (Hposw n).
  - unfold tends_to_0_nat.
    intros eps Heps.
    (* inactive means constant as run goes on *)
    pose proof (inactive_implies_TW_eventually_constant run u Hinact_run) as [N0 Hconst].
    set (wu0 := getR u (W_user (V (state_at run N0)))).
    set (tu0 := getR u (T_user (V (state_at run N0)))).


    destruct (Req_dec wu0 0) as [Hwu0_eq0 | Hwu0_neq0].
    -- (* wu = 0  *)
      exists N0. intros n Hn_ge.  unfold eq38_at.
      specialize (Hconst n Hn_ge) as [Htu Hwu].
      subst wu0.
      rewrite Htu.
      rewrite Hwu.
      rewrite Hwu0_eq0.
      rewrite Rmult_0_l.
      rewrite Rdiv_0_l.
      rewrite Rabs_R0.
      unfold Rgt in Heps.
      exact Heps.
    -- (* wu <> 0 *)
      (* that we can replace tu and wu with tu0 and wu0, their eventual constant value *)
      assert (Htu_eventually :
               forall n, (n >= N0)%nat ->
                         getR u (T_user (V (state_at run n))) = tu0).
      { intros n Hge. unfold tu0.
        destruct (Hconst n Hge) as [Htu _]. exact Htu. }

      assert (Hwu_eventually :
               forall n, (n >= N0)%nat ->
                         getR u (W_user (V (state_at run n))) = wu0).
      { intros n Hge. unfold wu0.
        destruct (Hconst n Hge) as [_ Hwu]. exact Hwu. }

      (* ty is eventually >= any threshold *)
      assert (Hty_eventually_ge :
               forall T : R, exists N1 : nat,
               forall n : nat, (n >= N1)%nat ->
                               T <= getR y (T_user (V (state_at run n)))).
      {
        intro T.
        destruct (Hysub T) as [n0 [_ HT0]].
        exists n0.

        intros n Hnge.
        (* prove ty(n0) <= ty(n) by T_user_mono *)
        assert (Hmono_iter :
                 getR y (T_user (V (state_at run n0))) <=
                   getR y (T_user (V (state_at run n)))).
        {
          (* induction on (n - n0) *)
          remember (n - n0)%nat as k.
          assert (Hn : n = (n0 + k)%nat) by (subst k; lia).
          subst n.
          clear Heqk Hnge.
          induction k as [|k IH].
          - rewrite Nat.add_0_r. lra.
          - replace (n0 + S k)%nat with (S (n0 + k))%nat by lia.
            eapply Rle_trans.
            -- exact IH.
            -- apply (T_user_mono y (n0 + k)%nat).
        }
        (* finish: T <= ty(n0) <= ty(n) *)
        eapply Rle_trans; eauto.
      }

      destruct Hyposw as [wy_min [Hwy_min_pos [Ny Hwy_lb]]].

      (* critical lemma *)
      pose proof (exp2_dominates_linear (Rabs wu0) (wy_min * eps) K (proj1_sig h)) as Hdom.
      destruct Hdom as [x' Hdom].
      apply Rabs_pos.
      apply Rmult_lt_0_compat.
      apply Hwy_min_pos.
      apply Heps.
      auto.
      apply proj1_rpos_pos.

      destruct (Hty_eventually_ge tu0) as [N1 Hty_ge_tu0].
      destruct (Hty_eventually_ge (tu0 + x')) as [N2 Hty_ge_tu0x'].

      set (N := Nat.max (Nat.max (Nat.max (Nat.max N0 Ny) N1) N2) 0%nat).
      exists N.
      intros n Hn_ge.

      assert (Hn_ge_N0 : (n >= N0)%nat) by (unfold N in Hn_ge; lia).
      assert (Hn_ge_Ny : (n >= Ny)%nat) by (unfold N in Hn_ge; lia).
      assert (Hn_ge_N1 : (n >= N1)%nat) by (unfold N in Hn_ge; lia).
      assert (Hn_ge_N2 : (n >= N2)%nat) by (unfold N in Hn_ge; lia).

      unfold eq38_at.
      (* now, we foc188us on proving that the denominator is positive *)
      (* define the state at n *)
      set (stn := V (state_at run n)).
      set (tu_n := getR u (T_user stn)).
      set (ty_n := getR y (T_user stn)).
      set (wu_n := getR u (W_user stn)).
      set (wy_n := getR y (W_user stn)).
      specialize (Hdom (ty_n - tu0)) as Hdom.

      (* rewrite tu_n and wu_n to constants (as they are eventually constants) *)
      assert (Htu_n : tu_n = tu0).
      {
        unfold tu_n. subst stn. apply (Htu_eventually n Hn_ge_N0).
      }

      assert (Hwu_n : wu_n = wu0).
      {
        unfold wu_n. subst stn. apply (Hwu_eventually n Hn_ge_N0).
      }

      (* show y is in the sum ranging over Users / {u} *)
      assert (Hy_in_remove : In y (remove Nat.eq_dec u Users)).
      {
        apply in_in_remove; auto.
      }

      (* build the y-term and prove its in the mapped list *)
      set (yterm :=
             wy_n * Rpower 2 ((ty_n - tu_n) / proj1_sig h)).

      assert (Hyterm_in :
               In yterm
                 (map
                    (fun x : User =>
                       getR x (W_user stn) * Rpower 2 ((getR x (T_user stn) - tu_n) / proj1_sig h))
                    (remove Nat.eq_dec u Users))
             ). {
        unfold yterm.
        eapply in_map_iff.
        exists y.
        split.
        - reflexivity.
        - apply Hy_in_remove.
      }

      (* prove mapped terms are nonnegative hence sum is >= yterm *)
      (* forall nonnegativity of the mapped list *)
      assert (Hmap_nonneg:
               Forall (fun r => 0 <= r)
                 (map (fun x : User =>
                         getR x (W_user stn) *
                           Rpower 2 ((getR x (T_user stn) - tu_n) / proj1_sig h))
                    (remove Nat.eq_dec u Users))).
      {
        apply Forall_forall.
        intros r Hrin.
        apply in_map_iff in Hrin.
        destruct Hrin as [x [Hreq Hxin]].
        subst r.
        apply Rmult_le_pos.
        - exact (Hwunn n x).
        - apply Rpower_2_nonneg.
      }
      (* so, sum dominates member *)
      assert (Hsum_ge_yterm :
               yterm <=
                 sum_list_R
                   (map (fun x : User =>
                           getR x (W_user stn) *
                             Rpower 2 ((getR x (T_user stn) - tu_n) / proj1_sig h))
                      (remove Nat.eq_dec u Users))).
      {
        eapply sum_list_R_ge_member; eauto.
      }

      (* now a lower bound on the denominator *)
      set (denom :=
             sum_list_R
               (map (fun x : User =>
                       getR x (W_user stn) *
                         Rpower 2 ((getR x (T_user stn) - tu_n) / proj1_sig h))
                  (remove Nat.eq_dec u Users))
             + wu_n).

      assert (Hdenom_ge_yterm : yterm <= denom). {
        unfold denom.
        unfold wu_n.
        unfold stn.
        eapply Rle_trans.
        - exact Hsum_ge_yterm.
        -     replace
            (sum_list_R
               (map
                  (fun x : User =>
                     getR x (W_user stn) *
                       Rpower 2 ((getR x (T_user stn) - tu_n) / proj1_sig h))
                  (remove Nat.eq_dec u Users)))
            with
            (sum_list_R
               (map
                  (fun x : User =>
                     getR x (W_user stn) *
                       Rpower 2 ((getR x (T_user stn) - tu_n) / proj1_sig h))
                  (remove Nat.eq_dec u Users)) + 0) at 1
            by lra.
              apply Rplus_le_compat_l.
              apply (Hwunn n u).
      }

      assert (Hwymin_le_wy : wy_min <= wy_n).
      {
        unfold wy_n. exact (Hwy_lb n Hn_ge_Ny).
      }

      assert (Hscaled : wy_min * Rpower 2 ((ty_n - tu_n) / proj1_sig h)
                        <=
                          wy_n * Rpower 2 ((ty_n - tu_n) / proj1_sig h)).
      {
        apply Rmult_le_compat_r.
        - apply Rpower_2_nonneg.
        - exact Hwymin_le_wy.
      }

      assert (Hdenom_ge_wymin :
               wy_min * Rpower 2 ((ty_n - tu_n) / proj1_sig h) <= denom).
      {
        eapply Rle_trans.
        - exact Hscaled.
        - unfold yterm in Hdenom_ge_yterm.
          exact Hdenom_ge_yterm.
      }


      assert (Hdenom_pos : 0 < denom).
      {
        unfold denom.
        eapply Rlt_le_trans.
        - apply Rmult_lt_0_compat. exact Hwy_min_pos. apply Rpower_2_pos.
        - exact Hdenom_ge_wymin.
      }

      rewrite Rabs_div.
      rewrite Hwu_n.
      rewrite Htu_n.
      rewrite Rabs_mult.

      replace (Rabs denom) with denom by (symmetry; apply Rabs_pos_eq; lra).


      apply Rle_lt_trans with
        (Rabs wu0 * Rabs (t_last stn - tu0)
                      / (wy_min * Rpower 2 ((ty_n - tu0)/proj1_sig h))).

      --- (* closed by the bound on the denominator *)
        set (A := Rabs wu0 * Rabs (t_last stn - tu0)).
        set (B := denom).
        set (C := wy_min * Rpower 2 ((ty_n - tu0) / proj1_sig h)).

        assert (HCpos : 0 < C).
        {
          unfold C.
          apply Rmult_lt_0_compat; [exact Hwy_min_pos |].
          unfold Rpower. apply exp_pos.
        }

        assert (Hinv : / B <= / C).
        {
          apply Rinv_le_contravar.
          exact HCpos.
          unfold B, C. rewrite Htu_n in Hdenom_ge_wymin. exact Hdenom_ge_wymin.
        }

        unfold Rdiv.
        apply Rmult_le_compat_l.
        ---- unfold A. apply Rmult_le_pos; apply Rabs_pos.
        ---- exact Hinv.

      --- (* now bound numerator *)

        assert (Htu0_le_ty : tu0 <= ty_n).
        { unfold ty_n. subst stn. apply (Hty_ge_tu0 n Hn_ge_N1). }

        assert (Hty_le_tlast : ty_n <= t_last stn).
        { unfold ty_n. subst stn. exact (Hytime n). }

        assert (Htl_ge_tu0 : tu0 <= t_last stn).
        { eapply Rle_trans; eauto. }

        assert (Hdiff_nonneg : 0 <= t_last stn - tu0) by lra.
        rewrite (Rabs_pos_eq _ Hdiff_nonneg).

        assert (Htl_ty_nonneg : 0 <= t_last stn - ty_n) by lra.

        replace (t_last stn - tu0) with ((t_last stn - ty_n) + (ty_n - tu0)) by ring.
        (* multiply both sides by positive denom C *)
        apply (Rmult_lt_reg_r (wy_min * Rpower 2 ((ty_n - tu0) / proj1_sig h))).
        ---- (* show denom positive *)
          apply Rmult_lt_0_compat; [exact Hwy_min_pos |].
          unfold Rpower; apply exp_pos.
        ----
          unfold Rdiv.

          field_simplify.

          2 : {  split.
                 apply Rgt_not_eq.
                 apply Rlt_gt.
                 apply Rpower_2_pos.
                 apply Rgt_not_eq.
                 apply Rlt_gt.
                 apply Hwy_min_pos.
          }

          replace (Rabs wu0 * t_last stn - Rabs wu0 * tu0)
            with (Rabs wu0 * (t_last stn - tu0)) by ring.

          assert (Htl_bound : t_last stn - tu0 <= (ty_n - tu0) + K).
          {
            pose proof (Htlast_le_tyK n).
            subst stn ty_n.
            lra.
          }

          assert (Hlhs_le : Rabs wu0 * (t_last stn - tu0) <= Rabs wu0 * (ty_n - tu0 + K)).
          {
            apply Rmult_le_compat_l.
            - apply Rabs_pos.
            - exact Htl_bound.
          }

          (* transitivity *)
          eapply Rle_lt_trans.

    + apply Hlhs_le.

    + replace (ty_n - tu0 + K) with ((ty_n - tu0) + K) by ring.

      rewrite Rmult_assoc.
      rewrite (Rmult_comm _ eps).
      rewrite <- Rmult_assoc.

      apply Hdom.

      (* now, show tu0 + x <= ty_n, that is, ty_n is unbounded *)
      assert (Hty_unbounded : tu0 + x' <= ty_n).
      {
        apply Hty_ge_tu0x'.
        apply Hn_ge_N2.
      }

      lra.
Qed.

(** ** (Theorem 7): Optimally small oracle delay

      The oracle delay [Lambda(t)] is bounded above by [(t - t* )] where [t* = min_{x in U} t_x].

      Proof: Expand the definitions of oracle delay and oracle operator's delay
             and manipulate to get [Lambda(t) = (t - t* )] by (47), so that [Lambda(t) <= (t - t* )].

      Formalization proof: prove first [tstar_le_tu], that is, [t* <= T_user u] for any [u].
      Then, prove [Lambda_x le], that [Lambda(x) <=  (t - t* ) / denom] (see definition of [denom] further).

 *)

Definition tstar (st : OracleState) : timestamp :=
  RList.MinRlist (map (fun x => getR x (T_user st)) Users).

Lemma tstar_le_tu :
  forall st u,
    In u Users ->
    tstar st <= getR u (T_user st).
Proof.
  intros st u Hu.
  unfold tstar.
  apply RList.MinRlist_P1.
  apply in_map_iff.
  exists u.
  split; [reflexivity | exact Hu].
Qed.

(** *** Theorem 7 main statement *)
Lemma Lambda_x_le :
  forall u t st,
    In u Users ->
    0 <= W_decayed st u t ->
    sum_list_R (map (fun u0 => W_decayed st u0 t) Users) > 0 ->
    W_decayed st u t * (t - getR u (T_user st)) /
                         sum_list_R (map (fun u0 : User => W_decayed st u0 t) Users)  <=
      (t - tstar st) * W_decayed st u t /
                         sum_list_R (map (fun u0 => W_decayed st u0 t) Users).
Proof.
  intros u t st Hu Hw.
  set (denom := sum_list_R (map (fun u0 : User => W_decayed st u0 t) Users)).
  intro Hdenompos.
  rewrite 2 Rdiv_def.
  apply Rmult_le_compat_r.
  apply Rinv_0_lt_compat in Hdenompos.
  apply Rlt_le. apply Hdenompos.
  rewrite Rmult_comm.
  apply Rmult_le_compat_r.
  apply Hw.
  rewrite 2 Rminus_def.
  rewrite Rplus_comm.
  replace (t + - tstar st) with (- tstar st + t) by field.
  apply Rplus_le_compat_r.
  apply Ropp_le_cancel.
  rewrite 2 Ropp_involutive.
  apply tstar_le_tu.
  apply Hu.
Qed.

Theorem optimally_small_oracle_delay :
  forall (t : timestamp) (st : OracleState),
    sum_list_R (map (fun u => W_decayed st u t) Users) > 0 -> (* that the denominator of Lambda is not zero: true *)
    Lambda t st <= t - tstar st.
Proof.
  intros t st Hdenompos.
  unfold Lambda.
  set (denom := sum_list_R (map (fun u0 : User => W_decayed st u0 t) Users)) in *.

  assert (sum_list_R (map (fun u : User => Lambda_x u t st) Users)  <=
            sum_list_R (map (fun u : User => (t - tstar st) * W_decayed st u t / denom) Users)).
  {
    apply sum_list_R_le.
    apply Forall2_map_l.
    intros u Hu.
    apply Lambda_x_le; auto.
    apply W_decayed_nonneg.
  }

  unfold Lambda_x.
  subst denom.
  set (denom := sum_list_R (map (fun u0 : User => W_decayed st u0 t) Users)) in *.

  apply (Rle_trans _ _ _ H).

  rewrite (map_ext
             (fun u : User => (t - tstar st) * W_decayed st u t / denom)
             (fun u : User => (/ denom) * ((t - tstar st) * W_decayed st u t))
          ).
  2: { intro u0.
       rewrite Rdiv_def.
       ring. }

  rewrite (sum_list_R_map_mult_const (/ denom) _ Users).
  rewrite (sum_list_R_map_mult_const (t - tstar st) (fun u => W_decayed st u t) Users).

  replace
    (/ denom *
       ((t - tstar st) *  sum_list_R (map (fun u : User => W_decayed st u t) Users)))
    with (t - tstar st).

  - apply Rle_refl.
  - unfold denom in *. field. lra.
Qed.

(** ** (Theorem 8): Sustainable rewards
      If [0 <= \alpha < 1] and [B_oracle(tau_r) > 0] at a given time [t],
      then [B_oracle(\tau_r) > 0] for all times [t' > t].

      Proof: We check the oracle balance at any (subsequent relative to when the balance is first funded) update, which happens at a time [t' > t].
             The balance would be [B_oracle(tau_r) - n(t')], where [n(t')] means the submission reward for the value submission that happens at time [t'].
 *)

Hypothesis L_f_nonneg_hyp : forall u st, 0 <= getR u (L_f st).

Lemma B_oracle_step_no_reward :
  forall run k,
    ~ is_submission (op_at run k) ->
    ~ is_reward_funding (op_at run k) ->
    B_oracle_r (state_at run (S k)) = B_oracle_r (state_at run k).
Proof.
  intros run k Hnsub Hnfund.
  rewrite state_at_S.
  unfold exec_op.
  destruct (run k) eqn:Hop; try reflexivity.
  - unfold token_deposit.
    destruct (a <=b 0); reflexivity.
  - unfold token_withdrawal.
    destruct (negb
        ((a >b 0) &&
         ((getR u (L_f (V (state_at run k))) >=b a) && (getR u (T_op (V (state_at run k))) + Delta_wd <=b t)))); reflexivity.
  - exfalso. unfold op_at in Hnsub. apply Hnsub. rewrite Hop. simpl. exact I.
  - exfalso. unfold op_at in Hnfund. apply Hnfund. rewrite Hop. simpl. exact I.
Qed.

Lemma Unlock_preserves_tu :
  forall st u t, tu u (Unlock st u t) = tu u st.
Proof.
  intros; unfold tu; simpl. unfold Unlock.
  destruct ((t >=b getR u (T_dep st) + Delta_dep) && (getR u (L_l st) >b 0)); reflexivity.
Qed.

Lemma B_oracle_step_reward :
  forall run k u v t',
    op_at run k = Submission u v t' ->
    let st := V (state_at run k) in
    let st1 := Unlock st u t' in
    B_oracle_r (state_at run (S k))
    = B_oracle_r (state_at run k)
      * (1 - alpha * ((w u st1) / (Q' u t' st1))
             * (1 - decay (t' - tu u st1))).
Proof.
  intros run k u v t' Hop.
  rewrite state_at_S.
  unfold op_at in Hop.
  rewrite Hop.
  simpl.

  unfold value_submission.
  simpl.

  unfold reward_payout.
  simpl.

  set (st := V (state_at run k)).
  set (st1 := Unlock st u t').
  set (B := B_oracle_r (state_at run k)).
  set (X1 := (w u st1 / Q' u t' st1)).
  set (X2 := (1 - decay (t' - tu u st1))).

  replace (B - alpha * B * X1 * X2) with (B * (1 - alpha * X1 * X2)) by ring.
  reflexivity.
Qed.

Lemma B_oracle_step_funding :
  forall run k u a t,
    op_at run k = RewardFunding u a t ->
    B_oracle_r (state_at run (S k)) = B_oracle_r (state_at run k) + a.
Proof.
  intros run k u a t Hop.
  rewrite state_at_S.
  unfold op_at in Hop.
  rewrite Hop.
  simpl.
  unfold reward_funding.
  simpl.
  reflexivity.
Qed.

Lemma is_submission_dec :
  forall op : Operation,
    { is_submission op } + { ~ is_submission op }.
Proof.
  intros op.
  destruct op; try (right; intros H; exact H).
  left. simpl. exact I.
Qed.

Lemma is_reward_funding_dec :
  forall op, { is_reward_funding op } + { ~ is_reward_funding op }.
Proof.
  intro op. destruct op; try (right; intros H; exact H).
  left. exact I.
Qed.

Lemma one_minus_alpha_x_pos :
  forall alpha x : R,
    0 <= alpha < 1 ->
    0 <= x <= 1 ->
    0 < 1 - alpha * x.
Proof.
  intros alpha x [Ha0 Ha1] [Hx0 Hx1].

  assert (Hax_le_a : alpha * x <= alpha).
  { rewrite <- Rmult_1_r.
    apply Rmult_le_compat; try lra. }

  assert (Hax_lt_1 : alpha * x < 1).
  { eapply Rle_lt_trans; eauto. }

  lra.
Qed.

Lemma w_le_Q' :
  forall u t st,
    (forall u st, wu u st * decay (t_sub st - tu u st) <= Q st) ->
    w u st <= Q' u t st.
Proof.
  intros u t st Hwu_decay_le_Q.
  unfold Q'.
  assert (Hdec : 0 < decay (t - t_sub st)) by apply decay_pos.
  assert (Hmain : 0 <= Q st - wu u st * decay (t_sub st - tu u st)).
  { pose proof (Hwu_decay_le_Q u st). lra. }
  assert (Hprod :
    0 <= (Q st - wu u st * decay (t_sub st - tu u st)) * decay (t - t_sub st)).
  {
    apply Rmult_le_pos.
    - exact Hmain.
    - left; exact Hdec.
  }
  lra.
Qed.

Lemma B_oracle_pos_preserved_step :
  forall run k,
    (0 <= alpha < 1) ->
    (* Q, a sum, bounds its summands *)
    (forall u st, wu u st * decay (t_sub st - tu u st) <= Q st) ->
    (* whenever a reward funding operation occurs, the amount is nonneg *)
    (forall run k u a t,
      op_at run k = RewardFunding u a t ->
      0 <= a) ->
    (* whenever a submission occurs, its timestamp is strictly after the user's previous submission time *)
    (forall run k u v t',
      op_at run k = Submission u v t' ->
      0 < t' - tu u (V (state_at run k))) ->
    (* whenever a submission occurs, the denominator Q' used in the reward update is strictly positive *)
    (forall run k u v t',
      op_at run k = Submission u v t' ->
      0 < Q' u t' (Unlock (V (state_at run k)) u t')) ->
    B_oracle_r (state_at run k) > 0 ->
    B_oracle_r (state_at run (S k)) > 0.
Proof.
  intros run k Halpha Hwu_decay_le_Q Hrf_nonneg Hsub_time HQ'_pos_sub Hbpos.
  destruct (is_submission_dec (op_at run k)) as [Hsub | Hnsub].
  - destruct (op_at run k) as
      [u a t | u a t | u v t' | u t | u x t | u x t | u t | u a t | t']
      eqn:Hop; try contradiction.

    erewrite (B_oracle_step_reward run k u v t') by exact Hop.
    apply Rmult_lt_0_compat; [exact Hbpos|].

    set (st  := V (state_at run k)).
    set (st1 := Unlock st u t').
    set (x := (w u st1 / Q' u t' st1) * (1 - decay (t' - tu u st1))).

    assert (Hx : 0 <= x <= 1).
    {
      assert (Hqpos : 0 < Q' u t' st1).
      {
        unfold st1.
        apply HQ'_pos_sub with (run:=run) (k:=k) (u:=u) (v:=v).
        exact Hop.
      }

      assert (Hw0 : 0 <= w u st1).
      { unfold w; apply L_f_nonneg_hyp. }

      assert (Hfrac0 : 0 <= w u st1 / Q' u t' st1).
      {
        unfold Rdiv.
        apply Rmult_le_pos; [exact Hw0|].
        left. apply Rinv_0_lt_compat. exact Hqpos.
      }

      assert (Hfrac1 : w u st1 / Q' u t' st1 <= 1).
      {
        apply div_le_1.
        - exact Hw0.
        - exact Hqpos.
        - apply w_le_Q'. exact Hwu_decay_le_Q.
      }

      assert (Htu_pres : tu u st1 = tu u st).
      {
        unfold tu, st1.
        destruct (Unlock_preserves_TW st u t' u) as [HT _].
        exact HT.
      }

      assert (Hdec : 0 < decay (t' - tu u st1) < 1).
      {
        rewrite Htu_pres.
        apply decay_between_0_1.
        apply Hsub_time with (run:=run) (k:=k) (u:=u) (v:=v); exact Hop.
      }

      assert (Hone_minus : 0 <= 1 - decay (t' - tu u st1) <= 1) by lra.

      assert (Hx_le_1 : x <= 1).
      {
        unfold x.
        apply mul_le_1_of_le_1.
        - split; [exact Hfrac0 | exact Hfrac1].
        - exact Hone_minus.
      }

      split.
      - unfold x. apply Rmult_le_pos; [exact Hfrac0 | lra].
      - exact Hx_le_1.
    }

    replace (alpha * (w u st1 / Q' u t' st1) * (1 - decay (t' - tu u st1)))
      with (alpha * x).
    + apply (one_minus_alpha_x_pos alpha x Halpha Hx).
    + subst x. ring.

  - destruct (is_reward_funding_dec (op_at run k)) as [Hfund | Hnfund].
    + destruct (op_at run k) as
        [u a t|u a t|u v t|u t|u x t|u x t|u t|u a t|t] eqn:Hop; try contradiction.
      rewrite (B_oracle_step_funding run k u a t Hop).
      pose proof (Hrf_nonneg run k u a t Hop).
      lra.
    + rewrite (B_oracle_step_no_reward run k Hnsub Hnfund).
      exact Hbpos.
Qed.

(** *** Theorem 8 main statement *)

Theorem sustainable_rewards :
  forall (run : Run) (n0 : nat),
    (* hypotheses for B_oracle_preserved_st *)
    (forall u st, wu u st * decay (t_sub st - tu u st) <= Q st) ->
    (forall run k u a t,
      op_at run k = RewardFunding u a t ->
      0 <= a) ->
    (forall run k u v t',
      op_at run k = Submission u v t' ->
      0 < t' - tu u (V (state_at run k))) ->
    (forall run k u v t',
      op_at run k = Submission u v t' ->
      0 < Q' u t' (Unlock (V (state_at run k)) u t')) ->
    (0 <= alpha < 1) ->
    B_oracle_r (state_at run n0) > 0 ->
    forall n : nat,
      (n >= n0)%nat ->
      B_oracle_r (state_at run n) > 0.
Proof.
  intros run n0 Hwu_decay_le_Q Hrf_nonneg Hsub_time HQ'_pos_sub Halpha Hb0 n Hge.

  remember (n - n0)%nat as d.
  assert (Hn : n = (n0 + d)%nat) by (subst d; lia).
  subst n.
  clear Heqd Hge.

  induction d as [|d IH].
  - rewrite Nat.add_0_r. exact Hb0.
  - replace (n0 + S d)%nat with (S (n0 + d))%nat by lia.
    apply (B_oracle_pos_preserved_step run (n0 + d)
             Halpha Hwu_decay_le_Q Hrf_nonneg Hsub_time HQ'_pos_sub).
    exact IH.
Qed.
