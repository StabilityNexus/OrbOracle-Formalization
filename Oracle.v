Require Import Reals.

Require ZArith.
Require Import List.
Require Import String.
Require Import Lra.

Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Classes.RelationClasses.

Local Open Scope R_scope.

(** * Datatypes, Parameters *)

(** ** Boolean versions of comparisons between reals *)
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

(** ** Numbers *)
Definition Rnn : Type := {x : R | Rle 0 x}.
Definition mk_Rnn (x : R) (knowledge : Rle 0 x) := exist (fun x => Rle 0 x) x knowledge.

Example R0_nn : Rle 0 R0.
Proof.
  unfold Rle.
  right.
  reflexivity.
Qed.

Definition Rnn0 : Rnn := mk_Rnn R0 R0_nn.

Check existT.

Definition R_ (nr : Rnn) : R :=
  proj1_sig nr.

(** ** Users *)
Definition User : Type := nat.
Parameter Users : list User.
Axiom Users_NoDup : NoDup Users.

(** *** UserSets *)
Definition UserSet := list User.

Definition mem_user (u : User) (s : UserSet) : bool :=
  existsb (fun x => Nat.eqb x u) s.

Lemma mem_user_In :
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

Lemma negb_mem_user_not_In :
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

(** ** User fmaps *)
Module UserOT := Nat_as_OT.
Module UserMap := FMapList.Make(UserOT).

(** ** Time *)
Definition timestamp : Type := R.

(** ** Weights, Balances and Values *)
Definition weight : Type := R.
Definition value : Type := R.
Definition balance : Type := R.

Definition history : Type := list (timestamp * value * value). (* type for time-ordered value history *)

(** ** Operations *)
Inductive operation : Type :=
  | Deposit (u : User) (a : balance) (t : timestamp)
  | Withdrawal (u : User) (a : balance) (t : timestamp)
  | Submission (u : User) (v : value) (t : timestamp)
  | Reading (u : User) (t : timestamp)
  | VoteBlacklist (u x : User) (t : timestamp)
  | VoteWhitelist (u x : User) (t : timestamp)
  | WeightSync (u : User) (t : timestamp)
  | RewardFunding (u : User) (a : balance) (t : timestamp)
  | NoneOp (t : timestamp).

Definition Trace : Type := list operation.

Definition getR (u : User) (m : UserMap.t R) : R :=
  match UserMap.find u m with
  | Some x => x
  | None => 0
  end.

Definition getRnn (u : User) (m : UserMap.t Rnn) : Rnn :=
  match UserMap.find u m with
  | Some x => x
  | None => Rnn0
  end.

Definition getNat (u : User) (m : UserMap.t nat) : nat :=
  match UserMap.find u m with
  | Some x => x
  | None => 0
  end.

Definition getZ (u : User) (m : UserMap.t Z) : Z :=
  match UserMap.find u m with
  | Some x => x
  | None =>  0
  end.

Definition getBool (u : User) (m : UserMap.t bool) : bool :=
  match UserMap.find u m with
  | Some x => x
  | None => false
  end.

(* set user u value to exactly v *)
Definition setR (u : User) (v : R) (m : UserMap.t R) : UserMap.t R :=
  UserMap.add u v m.

Definition setBool (u : User) (v : bool) (m : UserMap.t bool) : UserMap.t bool :=
  UserMap.add u v m.

Definition setNat (u : User) (v : nat) (m : UserMap.t nat) : UserMap.t nat :=
  UserMap.add u v m.

Definition setZ (u : User) (v : Z) (m : UserMap.t Z) : UserMap.t Z :=
  UserMap.add u v m.

(* increase user u value by dv *)
Definition addR (u : User) (dv : R) (m : UserMap.t R) : UserMap.t R :=
  setR u (getR u m + dv) m.

Definition addNat (u : User) (dv : nat) (m : UserMap.t nat) : UserMap.t nat :=
  setNat u (getNat u m + dv) m.

Definition addZ (u : User) (dv : Z) (m : UserMap.t Z) : UserMap.t Z :=
  setZ u (getZ u m + dv) m.

(** ** User pair fmaps *)
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

(** ** UserSet maps *)
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

(** ** Parameters *)
Parameter h : R.                       (* half-life constant *)
Parameter q : R.                       (* quorum constant *)
Parameter Delta_dep : timestamp.       (* deposit locking period *)
Parameter Delta_wd : timestamp.        (* deposit locking period *)
Parameter alpha : R.                   (* reward factor *)

(*
Definition TokenType := bool.          (* false if tau_w, true if tau_r *)
Parameter tau_w : string.              (* oracle token identifier *)
Parameter tau_r : string.              (* reward token identifier *)
*)

(** ** State *)

Record GovernanceState := {
    B : UserMap.t bool;                (* blacklist indicator for each user *)
    V_black : UserMap.t weight;        (* accumulated blacklist weight *)
    V_white : UserMap.t weight;        (* accumulated whitelist weight *)
    M_black : UserMap.t UserSet;       (* set of targets each voter has blacklisted *)
    M_white : UserMap.t UserSet;       (* set of targets each voter has whitelisted *)
    W_black : UserPairMap.t weight;    (* per target blacklist stored weight *)
    W_white : UserPairMap.t weight;    (* per target whitelist stored weight *)
  }.

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
    P      : history;                  (* time-ordered value history *)
    t_sub  : timestamp;                (* last value submission time*)
    t_last : timestamp;                (* last oracle interaction time *)
    L_tot  : balance;                  (* current total of deposited tokens *)
    G      : GovernanceState           (* governance state *)
  }.


Record State := {
    V : OracleState;                   (* oracle state *)
    B_user_w : UserMap.t balance;      (* external oracle token balance of users *)
    B_user_r : UserMap.t balance;      (* external reward token balance of users *)
    B_oracle_w : balance;              (* oracle token balance of oracle *)
    B_oracle_r : balance;              (* reward token balance of oracle *)
    trace : Trace;
  }.

Definition lift_oracle_state  (f : OracleState -> OracleState) (st : State) : State :=
  {| V := f (V st);
     B_user_w := B_user_w st;
     B_user_r := B_user_r st;
     B_oracle_w := B_oracle_w st;
     B_oracle_r := B_oracle_r st;
     trace := trace st;
  |}.

Section Auxiliary.

  (** ** Exponential Decay Factor *)
  Definition decay (Delta : R) : R :=
    Rpower 2 ((-1 * Delta) / h).

  (** ** Time-dependent Functions *)
  Definition W_decayed (st : OracleState) (u : User) (t : timestamp) : R :=
    (getR u (W_user st)) * decay (t - ((getR u (T_user st)))).

  Hypothesis B_user_w_nonneg : forall u st, getR u (W_user st) >= 0.

  Lemma W_decayed_nonneg :
    forall u st t,
      0 <= W_decayed st u t .
  Proof.
    intros.
    unfold W_decayed.
    unfold decay.
    unfold Rpower.
    unfold Rge.
    specialize (B_user_w_nonneg u st) as H_.
    unfold Rge in H_.
    destruct H_ as [Ha | Hb].
    - left. apply Rmult_lt_0_compat; try auto. apply exp_pos.
    - right. rewrite Hb. lra.
  Qed.

  Definition Q_decayed (t : timestamp) (st : OracleState) : R :=
    (Q st) * decay (t - t_sub st).

  Definition pbar_decayed (st : OracleState) (t : timestamp) : R :=
    pbar st * decay (t - t_sub st).

  (* helper of summing real number lists *)
  Definition sum_list_R (l : list R) : R :=
    fold_right Rplus 0 l.

  Definition P_ (st : OracleState) (t : timestamp) : R :=
    (sum_list_R (map (fun x => Rmult (getR x (P_user st)) (W_decayed st x t))  Users))
    / (sum_list_R (map (fun x => (W_decayed st x t)) Users)).

  (** ** Auxiliary state update operations *)
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
      P      := P st;
      t_sub  := t_sub st;
      t_last := t_last st;
      L_tot  := L_tot st;
      G      := G st
    |}
  else st.

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
    P      := P st;
    t_sub  := t_sub st;
    t_last := t_last st;
    L_tot  := L_tot st;
    G      := G'
  |}.

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
                P := P st;
                t_sub := t_sub st;
                t_last := t_last st;
                L_tot := L_tot st;
                G := G'
              |} in
    Recompute x st'.

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
              P := P st;
              t_sub := t_sub st;
              t_last := t_last st;
              L_tot := L_tot st;
              G := G'
            |}
  in
  Recompute x st.

  Definition Reweight (u : User) (w : weight) (st : OracleState) : OracleState :=
    let gx := G st in
    let blacklisteds := getUserSet u (M_black gx) in
    let whitelisteds := getUserSet u (M_white gx) in
    let st1 := fold_left (fun acc x => reweight_black_step u w x acc) blacklisteds st in
    let st2 := fold_left (fun acc x => reweight_white_step u w x acc) whitelisteds st1 in
    st2.

End Auxiliary.

(** * Operations *)
Section Operations.
  (** *** Token Deposit *)
  (** precondition(s):
   *  - requires a > 0, a t non-negative reals
   *)
  Definition token_deposit (u : User) (a : balance) (t : timestamp) (st : State) : State :=
    if (a <=b 0) then
      st
    else
      let V0  := V st in
      let V1  := Unlock V0 u t in

      let L_l'   := addR u a (L_l V1) in
      let T_dep' := setR u t (T_dep V1) in
      let T_op'  := setR u t (T_op V1) in

      let B_user_w'   := addR u (-a) (B_user_w st) in
      let B_oracle_w' := (B_oracle_w st + a) in

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
          P      := P V1;
          t_sub  := t_sub V1;
          t_last := t;
          L_tot  := (L_tot V1 + a);
          G      := G V1
        |}
      in

      {|
        V := V2;
        B_user_w := B_user_w';
        B_user_r := B_user_r st;
        B_oracle_w := B_oracle_w';
        B_oracle_r := B_oracle_r st;
        trace := trace st;
      |}.

  (** ** Token Withdrawal *)
  Definition token_withdrawal (u : User) (a : balance) (t : timestamp) (st : State) : State :=
  (** precondition(s):
   *  - a > 0
   *  - getR u (L_f (V st)) >= a
   *  -  getR u (T_op (V st)) + Delta_wd <= t
   *)
  let cond1 := a >b 0 in
  let cond2 := getR u (L_f (V st)) >=b a in
  let cond3 := getR u (T_op (V st)) + Delta_wd <=b t in
  if negb ((andb cond1 (andb cond2 cond3))) then
    st
  else
    let v0 := V st in

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
        P      := P v0;
        t_sub  := t_sub v0;
        t_last := t;
        L_tot  := (L_tot v0 - a);
        G      := G v0
      |}
    in

    (* balance updates *)
    let B_user_w'   := addR u a (B_user_w st) in
    let B_oracle_w' := (B_oracle_w st - a) in

    {|
      V := v1;
      B_user_w := B_user_w';
      B_user_r := B_user_r st;
      B_oracle_w := B_oracle_w';
      B_oracle_r := B_oracle_r st;
      trace := trace st;
    |}.

  (** ** Value Submission *)
  (** *** Predefinition local variables *)
  Definition w (u : User) (st : OracleState) := getR u (L_f st).
  Definition pu (u : User) (st : OracleState) := getR u (P_user st).
  Definition wu (u : User) (st : OracleState) := getR u (W_user st).
  Definition tu (u : User) (st : OracleState) := getR u (T_user st).

  (** *** Updated aggregate weight and value, and reward payout *)
  Definition Q' (u : User) (t : timestamp) (st : OracleState) : R :=
    ((Q st) - (wu u st) * (decay (t_sub st - tu u st))) * (decay (t - t_sub st)) + (w u st).

  Definition pbar' (u : User) (v : value) (t : timestamp) (st : OracleState) : value :=
  (((((pbar st) * (Q st)) -  ((pu u st) * (wu u st) * (decay (t_sub st - tu u st))))
  * (decay (t - t_sub st))) + (v * (w u st))) / (Q' u t st).

  Definition reward_payout (u : User) (t : timestamp) (st : State) : R :=
  alpha * (B_oracle_r st) * ((w u (V st)) / (Q' u t (V st))) * (1 - decay (t - tu u (V st))).

  Definition value_submission (u : User) (v : value) (t : timestamp) (st : State) : State :=
  let v0 := V st in
  let v1 := Unlock v0 u t in

  (* local values after Unlock *)
  let w_   := w u v1 in
  let vR   := v in
  let Qp   := Q' u t v1 in
  let pbarp := pbar' u vR t v1 in
  let st1 : State :=
    {| V := v1;
      B_user_w := B_user_w st;
      B_user_r := B_user_r st;
      B_oracle_w := B_oracle_w st;
      B_oracle_r := B_oracle_r st;
      trace := trace st;
    |}
  in
  let n    := reward_payout u t st1 in

  (* update per-user submission fields *)
  let P_user' := setR u v (P_user v1) in
  let W_user' := setR u w_ (W_user v1) in
  let T_user' := setR u t (T_user v1) in

  (* update history *)
  let P' := (P v1) ++ ((t, pbarp, vR) :: nil) in

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
      P      := P';
      t_sub  := t;
      t_last := t;
      L_tot  := L_tot v1;
      G      := G v1
    |}
  in

  (* reward token balance transfer *)
  let B_user_r'   := addR u n (B_user_r st) in
  let B_oracle_r' := (B_oracle_r st - n) in

  {|
    V := v2;
    B_user_w := B_user_w st;
    B_user_r := B_user_r';
    B_oracle_w := B_oracle_w st;
    B_oracle_r := B_oracle_r';
    trace := trace st;
  |}.

  (** ** Value reading *)
  (** precondition(s):
   *  - u is not blacklisted
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
      P      := P st;
      t_sub  := t_sub st ;
      t_last := t;
      L_tot  := L_tot st;
      G      := G st
    |}.

  (** ** Vote to blacklist *)
  (** precondition(s):
   *  - u not blacklisted
   *  - w(u) = L_f(u) > 0
   *  - u has not voted on x before (x ∉ M_black(u))
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
        P      := P v0;
        t_sub  := t_sub v0;
        t_last := t;
        L_tot  := L_tot v0;
        G      := g1
      |}
    in

    (* Recompute(x) *)
    Recompute x v1.

  (** ** Vote to whitelist *)
  (** precondition(s):
   *  - u not blacklisted (getBool u (B (G st)) = false)   (* adjust to your getBool helper *)
   *  - L_f(u) > 0
   *  - u has not voted on x before (x ∉ M_white(u))
   *)
Definition whitelist_vote (u x : User) (t : timestamp) (st : OracleState) : OracleState :=
  let cond1 := negb (getBool u (B (G st))) in
  let cond2 := getR u (L_f st) >b 0 in
  let cond3 := negb (mem_user x (getUserSet u (M_black (G st)))) in
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
        P      := P v0;
        t_sub  := t_sub v0;
        t_last := t;
        L_tot  := L_tot v0;
        G      := g1
      |}
    in

    (* Recompute(x) *)
    Recompute x v1.

  (** ** Weight synchronization *)
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
      P      := P v1;
      t_sub  := t_sub v1;
      t_last := t;
      L_tot  := L_tot v1;
      G      := G v1
    |}.


  (** ** Reward Token Funding *)
  Definition reward_funding (u : User) (a : balance) (t : timestamp) (st : State) : State :=
    let B_user_r' := addR u (-a) (B_user_r st) in
    let B_oracle_r' := (B_oracle_r st) + a in
    let v0 := V st in
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
      P      := P v0;
      t_sub  := t_sub v0;
      t_last := t;
      L_tot  := L_tot v0;
      G      := G v0
    |} in
    {|
      V := V';
      B_user_w := B_user_w st;
      B_user_r := B_user_r';
      B_oracle_w := B_oracle_w st;
      B_oracle_r := B_oracle_r';
      trace := trace st;
    |}.

End Operations.

Section Theorems.

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

  (** * Theorem 3: Equivalence of the ideal decayed weight mean function and the constant time update rule

      The ideal decayed weighted mean function P(t) and the constant-time update rule pbar_k(t) - pbar are equal
      where k is the k-th update.

      P(t) = pbar_k(t) - pbar

      Proof: By manipulating the definition of Lambda_u(t)
             and getting it into a certain form at (39)
             such that we can take the limit to be zero.
   *)

  Theorem ideal_decayed_weight_mean_function_is_constant :
    True = True.
  Proof.
    (* TODO: *) Admitted.

  Definition Lambda_x (x : User) (t : timestamp) (st : OracleState): R :=
    (W_decayed st x t) * (t - getR x (T_user st)) /
      sum_list_R (map (fun u => W_decayed st u t) Users).

  Definition Lambda (t : timestamp) (st : OracleState) : R :=
    sum_list_R (map (fun u => Lambda_x u t st) Users).

  (** * Theorem 6: Inactive oracle operator delay
      If an oracle operator u in U becomes inactive,
      the operator delay Lambda_u(t) caused by this inactivity converges to 0.

      That is, lim_{t -> \inf} Lambda_u(t) = 0.

      Proof: By manipulating the definition of Lambda_u(t) and getting it into a certain form at (39)
             such that we can take the limit to be zero.
   *)

  (** ** Inactivity
   * A user [u] is inactive for a trace [tr] if there exists a timestamp [t_end], such that
   * there are no submission operations [Submission u v t] with [t >= t_end] in [tr].
   *)

  Definition inactive_after (u : User) (t_end : timestamp) (tr : Trace) :=
     Forall (fun op => match op with
                       | Submission u' v t => u = u' \/ t <= t_end
                       | _ => True
                       end) tr.

  Definition inactive_operator (u : User) (tr : Trace) :=
    exists t_end, t_end >= 0 /\ inactive_after u t_end tr.


    (* alternative definition with In *)
  Definition no_submit_after (u : User) (t_end : timestamp) (tr : Trace) : Prop :=
    forall t v, ~ In (Submission u v t) tr \/ t <= t_end.

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

  Lemma Lambda_u_rewrite_38 :
  forall (st : OracleState) (t : timestamp) (u : User),
    In u Users ->
    NoDup Users -> (* needed because we adjusted the bounds of the sum to factor out one term  *)
    h > 0 ->       (* dividing by h *)
    (forall x, getR x (W_user st) >= 0) ->  (* these two are needed so that the denominator is positive *)
    (exists u0, In u0 Users /\ getR u0 (W_user st) > 0) ->
    Lambda_x u t st =
      ((getR u (W_user st)) * (t - (getR u (T_user st)))) /
      ((sum_list_R
          (map
             (fun x => (getR x (W_user st)) *
                         (Rpower 2 (((getR x (T_user st)) - (getR u (T_user st))) / h)))
             (remove Nat.eq_dec u Users)))
       + (getR u (W_user st))).
  Proof.
    intros st t u Huin Hnodup Hnz Hwunn Hu0.
    unfold Lambda_x.
    unfold W_decayed.
    unfold decay.

    assert (Hexp : forall x,
    (-1 * (t - getR x (T_user st)) / h)
    = (-1 * (t - getR u (T_user st)) / h)
      + ((getR x (T_user st) - getR u (T_user st)) / h)).
    {
      intro x.
      field. lra.
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
    2 : {  field. apply Rgt_not_eq in Hnz. auto. }

    rewrite (Rpower_O 2) by lra.

    rewrite Rmult_1_r.

    rewrite (sum_split_remove _ _ _ Hnodup Huin).

    replace ((getR u (T_user st) - getR u (T_user st)) / h) with 0.
    2 : {  field. apply Rgt_not_eq in Hnz. auto. }

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

  (** Definition for the limit argument *)
  (** Alternatively, might use: http://coquelicot.saclay.inria.fr/html/Coquelicot.Continuity.html#is_lim *)
  Definition tends_to_0 (f : R -> R) : Prop :=
    forall eps : R,
      eps > 0 ->
      exists T : R, forall t : R, t >= T -> Rabs (f t) < eps.

  Lemma tends_to_0_ext :
  forall f g : R -> R,
    (forall t, f t = g t) ->
    tends_to_0 f ->
    tends_to_0 g.
  Proof.
    intros f g Heq Ht eps Heps.
    specialize (Ht eps Heps).
    destruct Ht as [T HT].
    exists T. intros t Htge.
    rewrite <- Heq.
    apply HT; exact Htge.
  Qed.

  Theorem inactive_oracle_operator_delay :
    forall (st : OracleState) (t : timestamp) (tr : Trace) (u : User),
      inactive_operator u tr -> tends_to_0 (fun t => Lambda_x u t st).
  Proof.
    intros.
    set (eq38 := fun t =>
                ((getR u (W_user st)) * (t - getR u (T_user st))) /
                  ((sum_list_R (map (fun x =>
                                       getR x (W_user st) *
                                         Rpower 2 (((getR x (T_user st)) - (getR u (T_user st))) / h))
                                  (remove Nat.eq_dec u Users)))
                   + getR u (W_user st))).

    assert (Heq38 : forall t, (fun t => Lambda_x u t st) t = eq38 t).
            {
              intro.
              unfold eq38.
              apply Lambda_u_rewrite_38; admit. (* TODO: add the assumptions *)
            }

    eapply tends_to_0_ext.
    - intro. symmetry. apply Heq38.
    Admitted.
  Qed.

  (** * Theorem 7 : Optimally small oracle delay
      The oracle delay Lambda(t) is bounded above by (t - t* ) where t* = min_{x in U} t_x

      Proof: Expand the definitions of oracle delay and oracle operator's delay
             and manipulate to get Lambda(t) = (t - t* ) by (47), so that Lambda(t) <= (t - t* ).

      Formalization proof: prove first tstar_le_tu, that is, t* <= T_user u for any u.
      Then, prove Lambda_x le, that Lambda(x) <=  (t - t* ) / denom (see denom further).

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

Hypothesis B_user_w_nonneg : forall u st, getR u (W_user st) >= 0.

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
    apply B_user_w_nonneg.
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

  (** * Theorem 8: Sustainable rewards:
      If 0 <= \alpha < 1 and B_oracle(tau_r) > 0 at a given time t,
      then B_oracle(\tau_r) > 0 for all times t' > t.

      Proof: We check the oracle balance at any (subsequent relative to when the balance is first funded) update, which happens at a time t' > t.
             The balance would be B_oracle(tau_r) - n(t'), where n(t') means the submission reward for the value submission that happens at time t'.
   *)
  Theorem sustainable_rewards :
    forall (t : timestamp) (St : State),
      (0 <= alpha < 1) /\ (B_oracle_r St > 0) -> (* need to get the balance of the oracle at that given time t*)
      forall (t' : timestamp),
        (t' > t) -> B_oracle_r St > 0.           (* need to get the balance of the oracle at times t' *)
  Proof.
    (* TODO: *) Admitted.


End Theorems.
