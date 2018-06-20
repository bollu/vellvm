(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ZArith Omega.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Program Classical.
Require Import paco.
Require Import Morphisms.
Require Import Setoid.
Require Import Relation_Definitions.

Set Implicit Arguments.
Set Contextual Implicit.

(** An [M E X] is the denotation of a program as coinductive (possibly
    infinite) tree where the leaves are labeled with [X] and every node
    is either a [Tau] node with one child, or a branching node [Vis]
    with a visible event [E Y] that branches on the values of [Y]. *)
CoInductive M (Event : Type -> Type) X := 
| Ret (x:X)
| Vis {Y: Type} (e : Event Y) (k : Y -> M Event X)
| Tau (k: M Event X)
| Err (s:String.string)
.
(** Note: One could imagine an alternative definition with an explicit
    Bind constructor (and a Prim constructor), but this might not be
    as nice / might not work at all -- this way makes productivity
    easier to deal with.  (Also, this one can be turned into a real
    monad.)  We should compare at some point. *)

(** N.b. This is related to the Free Monad construction, which is not
    possible with Coq due to the positivity requirement. But when
    the functor that we want to build the Free Monad from is
    representable (or "Naperian", as it is called by Peter Hancock),
    we can use this encoding to avoid the problem.
    Update: that comment would apply only if we had
    [Event : Type -> Type] and [Vis (Event -> M Event X)].
    *)

(** [M] is known as the "Freer monad".
    "Freer Monads, More Extensible Effects",
    Oleg Kiselyov, Hiromi Ishii.
    The [Vis] constructor corresponds to a free functor construction
    also called Co-Yoneda or left Kan extension.
    Note that [Event] is meant to be an indexed type, and generally
    not a functor, but we have a monad in any case. *)

(** The existence of [spin] makes this not quite free:
    amounts more or less to an additional [Event Void]
    constructor.  *)

(** In order to unfold a cofixpoint we have to rewrite it with
    [matchM].  (Is this relevant only in proofs?  Maybe it should be
    defined near the Ltac that uses it.) *)
Definition idM E X (i: M E X) :=
  match i with 
  | Ret x => Ret x
  | Vis e k => Vis e k
  | Tau k => Tau k
  | Err s => Err s
  end.
Lemma matchM : forall E X (i: M E X), i = idM i.
Proof. destruct i; auto. Qed.


(* Allow rewrite on both LHS and RHS *)
Lemma matchM' : forall E X (i1 i2: M E X), i1 ≡ i2 <-> idM i1 ≡ idM i2.
Proof.
  split; intros.
  - congruence.
  - rewrite matchM.
    rewrite @matchM with (i := i2).
    auto.
Qed.

Inductive TraceFinite {E: Type -> Type} {X: Type}: M E X -> Type :=
| TFRet: forall (x: X), TraceFinite (Ret x)
| TFErr: forall (s: String.string), TraceFinite (Err s)
| TFTau: forall (mex: M E X) (FIN: TraceFinite mex),
    TraceFinite (Tau mex)
| TFVis: forall {Y: Type} (e: E Y) (k: Y -> M E X)
           (FINK: forall (y: Y), TraceFinite (k y)),
    TraceFinite (Vis e k)
.

  

(** [M E] forms a [Monad] *)
(* N.b.: Possible variant: remove the Tau in the Ret case.  Not clear
   whether this is a global win (we have to then put some extra Taus
   in programs/specifications, which Joachim finds to be a breach of
   abstraction), but it makes this a monad. *)
Definition bindM {E X Y} (s: M E X) (t: X -> M E Y) : M E Y :=
  let cofix go (s : M E X) := 
      match s with
      | Ret x => Tau (t x)
      | Vis e k => Vis e (fun y => go (k y))
      | Tau k => Tau (go k)
      | Err s => Err s
      end
  in go s.

Definition mapM {E X Y} (f:X -> Y) (s: M E X) : M E Y :=
  let cofix go (s : M E X) :=
      match s with
      | Ret x => Ret (f x)
      | Vis e k => Vis e (fun y => go (k y))
      | Tau k => Tau (go k)
      | Err s => Err s
      end
  in go s.

Instance functor_M {E} : Functor (M E) := (@mapM E).
Instance monad_M {E} : (@Monad (M E)) (@mapM E) := { mret X x := Ret x; mbind := @bindM E }.

(* Properties of  ----------------------------------------------------- *)

CoInductive equiv {E X} : M E X -> M E X -> Prop :=
| equiv_Ret : forall x, equiv (Ret x) (Ret x)
| equiv_Vis : forall {Y} e k1 k2, (forall (v:Y), equiv (k1 v) (k2 v)) -> equiv (Vis e k1) (Vis e k2)
| equiv_Tau : forall k1 k2, equiv k1 k2 -> equiv (Tau k1) (Tau k2)
| equiv_Err : forall s1 s2, equiv (Err s1) (Err s2)
.
                             
(* Properties of  ----------------------------------------------------- *)

Module MonadVerif.
(* Monad laws:
   - return x >>= k   =   k x
   - s >>= return   =   w
   - s >>= (\x -> k x >>= h)   =   (s >>= k) >>= h
 *)

(** Get rid of absurd cases such as
    - forall t, Tau t <> Tau s
    - Tau t = Vis e k
 *)
Ltac dispatch_contra :=
  first
    [ let dispatch H tac := solve [exfalso; eapply H; tac] in
      match goal with
      | H : forall t, ?f t <> ?f ?s |- _ => dispatch H auto
      | H : forall t, ?f t <> ?s, _ : ?f ?u = ?s |- _ => dispatch H eauto
      end
    | discriminate
    ].

Inductive UnTau E X : M E X -> M E X -> Prop :=
| OneTau : forall s t, UnTau s t -> UnTau (Tau s) t
| NoTau : forall s, (forall t, ~(Tau t = s)) -> UnTau s s.


CoInductive EquivUpToTau E X :
  M E X -> M E X -> Prop :=
| EquivRet : forall x, EquivUpToTau (Ret x) (Ret x)
| EquivVis : forall Y (e : E Y) (k1 k2 : Y -> M E X),
    (forall y, EquivUpToTau (k1 y) (k2 y)) ->
    EquivUpToTau (Vis e k1) (Vis e k2)
(* Equality with spin is undecidable,
   but one can coinductively generate a proof with this. *)
| EquivTau : forall s t,
    EquivUpToTau s t -> EquivUpToTau (Tau s) (Tau t)
| EquivTauLeft : forall s s' t,
    (forall t', ~(Tau t' = t)) ->
    UnTau s s' ->
    EquivUpToTau s' t ->
    EquivUpToTau (Tau s) t
| EquivTauRight : forall s t t',
    (forall s', ~(Tau s' = s)) ->
    UnTau t t' ->
    EquivUpToTau s t' ->
    EquivUpToTau s (Tau t)
| EquivErr : forall s1 s2, EquivUpToTau (Err s1) (Err s2)
.



(* Tractic to force a Trace computation *)
Ltac forcetrace :=
  simpl;
  match goal with
  | [ |- ?X ≡ ?Y ] => rewrite matchM with (i := X);
                    rewrite matchM with (i := Y);
                    simpl; auto
  | [H : _ |- _] => idtac H
  | [ |- _ ] => idtac
    end.


Inductive EquivUpToTauGen E X (Rel: M E X -> M E X -> Prop) : M E X -> M E X -> Prop :=
| _EquivRet : forall x, EquivUpToTauGen Rel (Ret x) (Ret x)
| _EquivVis : forall Y (e : E Y) (k1 k2 : Y -> M E X)
    (RELK: forall y,  Rel (k1 y) (k2 y)),
    EquivUpToTauGen Rel (Vis e k1) (Vis e k2)
(* Equality with spin is undecidable,
   but one can coinductively generate a proof with this. *)
| _EquivTau : forall s t (REL:  Rel s t),
    EquivUpToTauGen Rel (Tau s) (Tau t)
| _EquivTauLeft : forall s s' t (NOTAUT': forall t', ~(Tau t' = t))
                    (UNTAUS: UnTau s s')
                    (REL: Rel s' t),
    EquivUpToTauGen Rel (Tau s) t
| _EquivTauRight : forall s t t',
    (forall s', ~(Tau s' = s)) ->
    UnTau t t' ->
    Rel s t' ->
    EquivUpToTauGen Rel s (Tau t)
| _EquivErr : forall s1 s2, EquivUpToTauGen Rel (Err s1) (Err s2)
.


(* Parametrized equiv up to tau relation *)
Definition pEquivUpToTau E X mex1 mex2 :=
  paco2 (@EquivUpToTauGen E X) bot2 mex1 mex2.
Check (pEquivUpToTau).

Hint Unfold pEquivUpToTau.
Lemma pEquivUpToTauGen_monotone: forall E X,
    monotone2 (@EquivUpToTauGen E X).
Proof.
  intros until X.
  unfold monotone2.
  intros.
  induction IN.
  - constructor.
  - constructor.
    intros.
    apply LE.
    apply RELK.
  - constructor.
    auto.
  - eapply _EquivTauLeft; eauto.
  - eapply _EquivTauRight; eauto.
  - constructor.
Qed.
Hint Resolve pEquivUpToTauGen_monotone : paco.

Lemma peutt_refl : forall E X (s : M E X),
    pEquivUpToTau s s.
Proof.
  intros until X.
  pcofix CIH.
  intros; destruct s.
  - pfold. constructor.
  - apply paco2_fold.
    constructor.
    intros.
    right.
    apply CIH.

    
  - pfold. constructor.
    right. auto.
    
  - pfold. constructor.
Qed.

Lemma eutt_refl : forall E X (s : M E X),
    EquivUpToTau s s.
Proof.
  cofix eutt_refl.
  intros.
  destruct s; constructor;
    intros;
    apply eutt_refl.
Qed.

Lemma eutt_sym : forall E X (s t : M E X),
    EquivUpToTau s t -> EquivUpToTau t s.
Proof.
  cofix eutt_sym.
  intros.
  destruct H; try constructor.
  - intro y. apply eutt_sym. apply H.
  - apply eutt_sym. apply H.
  - econstructor. assumption. eassumption. apply eutt_sym. assumption.
  - econstructor. assumption. eassumption. apply eutt_sym. assumption.
Qed.

Lemma peutt_sym : forall E X (s : M E X),
    pEquivUpToTau s s.
Proof.
  intros until X.
  pcofix CIH.
  intros; destruct s.
  - pfold. constructor.
  - apply paco2_fold.
    constructor.
    intros.
    right.
    apply CIH.

    
  - pfold. constructor.
    right. auto.
    
  - pfold. constructor.
Qed.


Fixpoint tauN {E X} (n: nat) (s': M E X): M E X :=
  match n with
  | 0 => s'
  | S n' =>  Tau (tauN n' s')
  end.

Lemma tauN_destruct: forall {E X} (n: nat) (s': M E X),
    tauN (n + 1) s' = Tau (tauN n s').
Proof.
  intros.
  assert (N_PLUS_1: n + 1 = S n).
  omega.
  rewrite N_PLUS_1.
  auto.
Defined.


Lemma tauN_untau:
  forall E X
    (n: nat)
    (a: M E X),
    (forall t: M E X, a <> Tau t) ->
    UnTau (tauN n a) a.
Proof.
  intros until n.
  induction n.
  - intros. simpl.
    constructor. auto.
  - intros.
    specialize (IHn a H).
    replace (S n) with (n + 1)%nat.
    rewrite tauN_destruct.
    constructor. auto.
    omega.
Defined.


Hint Resolve tauN_untau.
    
Lemma tauN_destruct_2:
  forall {E X}
    (n: nat)
    (a: M E X),
    tauN n (Tau a) = tauN (n + 1) a.
Proof.
  intros until n.
  induction n.
  - simpl. auto.
  - simpl.
    intros.
    rewrite <- IHn.
    auto.
Defined.

Lemma tauN_eutt: forall {E X}
                   (n: nat)
                   (a: M E X),
    EquivUpToTau a (tauN n a).
Proof.
  intros until X.
  cofix.

  intros.


  assert (NCASES: (n = 0 \/ n > 0)%nat).
  omega.

  destruct NCASES as [NZERO | NNONZERO].
  - subst. apply eutt_refl.
  - assert (N_AS_N': exists n', n = S n').
    induction n.
    omega.
    eauto.

    destruct N_AS_N' as [N' N'WITNESS].
    subst.

    replace (S N') with (N' + 1)%nat.
    rewrite tauN_destruct.
    Guarded.

    destruct a;
      try (eapply EquivTauRight; eauto; apply eutt_refl).

    Guarded.
    rewrite tauN_destruct_2.
    Guarded.
    constructor.
    apply tauN_eutt.
    Guarded.
    omega.
Defined.


(* 
Lemma tauN_peutt_left: forall {E X}
                         (n: nat)
                         (a: M E X),
    pEquivUpToTau (tauN n a) a.
Proof.
  intros.
  pcofix CIH.

  assert (NCASES: (n = 0 \/ n > 0)%nat).
  omega.

  destruct NCASES as [NZERO | NNONZERO].
  - rewrite NZERO in *. simpl in *.
    apply eutt_refl.
  - assert (N_AS_N': exists n', n = S n').
    induction n.
    omega.
    eauto.
    generalize dependent a.
    intros.

    destruct N_AS_N' as [N' N'WITNESS].
    rewrite N'WITNESS in *.
           

    replace (S N') with (N' + 1)%nat; try omega.
    rewrite tauN_destruct.
    
      
    
    destruct a; pfold.
    eapply _EquivTauLeft.
    eauto.
    eauto.
    pauto.
    eapply eutt_refl.
    pfold.

    
    Guarded.
    rewrite tauN_destruct_2.
    Guarded.
    constructor.
    apply tauN_eutt.
    Guarded.
    omega.
Abort.
*)


(* Simple helpers for small applications of Tau *)
Lemma tauN_eutt_1: forall {E X} (a: M E X),
    EquivUpToTau a (Tau a).
Proof.
  intros.
  replace (Tau a) with (tauN 1 a).
  apply tauN_eutt.
  auto.
Defined.


(* Simple helpers for small applications of Tau *)
Lemma tauN_eutt_2: forall {E X} (a: M E X),
    EquivUpToTau a (Tau (Tau a)).
Proof.
  intros.
  replace (Tau (Tau a)) with (tauN 2 a).
  apply tauN_eutt.
  auto.
Qed.
    
(* 
Lemma tauN_destruct_2: forall {E X} (n: nat) (s': M E X),
    tauN (S n) (Tau s') = tauN n s'.
Proof.
Qed.
*)
               

(* Note that backward is not true, since this whole is lazy,
you could have an INIFNITE stream of Tau (Tau (Tau (...)))) *)
Lemma untau_count_layers:
  forall E X (s t: M E X),
    UnTau s t ->
    exists (n: nat), s = tauN n t.
Proof.
  intros.
  induction H.
  - destruct IHUnTau as [n WITNESS].
    exists (n + 1).
    rewrite tauN_destruct.
    rewrite WITNESS.
    reflexivity.
  - exists 0.
    simpl.
    reflexivity.
Qed.
  

Lemma untau_notau : forall E X (s t : M E X), ~(UnTau s (Tau t)).
Proof.
  intros E X s t H.
  remember (Tau t) as t'.
  induction H.
  - auto.
  - eapply H; eauto.
Qed.

Lemma untau_untau : forall E X (s t : M E X),
    UnTau s t -> UnTau t t.
Proof.
  intros E X s t H.
  induction H.
  - auto.
  - constructor; assumption.
Qed.

Lemma untau_inj : forall E X (s s' s'' : M E X),
    UnTau s s' -> UnTau s s'' -> s' = s''.
Proof.
  intros E X s s' s'' H.
  induction H; intro H'; inversion H'.
  - auto.
  - dispatch_contra.
  - dispatch_contra.
  - reflexivity.
Qed.

Lemma eutt_untau : forall E X (s s' t : M E X),
    UnTau s s' -> EquivUpToTau s t ->
    exists t', UnTau t t' /\ EquivUpToTau s' t'.
Proof.
  intros E X s s' t HUnTau.
  generalize dependent t.
  induction HUnTau as [ s s' HUnTau IH | s HNoTau ]; intros t H.
  - inversion H as [ | | s1 t1 H1 | s1 s1' ? HtNoTau | | ].
    + apply IH in H1; destruct H1 as [t' H1]; destruct H1.
      eexists; split.
      * constructor; eassumption.
      * assumption.
    + eexists; split. constructor.
      * assumption.
      * replace s' with s1'.
        -- assumption.
        -- eapply untau_inj; eassumption.
    + dispatch_contra.
  - inversion H; subst.
    + eexists; split; constructor; assumption.
    + eexists; split; constructor.
      * intros t I. inversion I.
      * assumption.
    + dispatch_contra.
    + dispatch_contra.
    + eexists; split.
      * constructor. eassumption.
      * assumption.
    + eexists; split.
      * constructor. intros. unfold not. intros. inversion H0.
      * assumption.
Qed.

Lemma eutt_tau_2 : forall E X (s s' t t' : M E X),
    UnTau s s' -> UnTau t t' -> EquivUpToTau s' t' ->
    EquivUpToTau s t.
Proof.
  cofix eutt_tau_2.
  intros E X s s' t t' Hs Ht H.
  destruct Hs, Ht.
  - constructor.
    eapply eutt_tau_2; eassumption.
  - econstructor; eassumption.
  - econstructor; eassumption.
  - destruct H;
      try (constructor; assumption);
      dispatch_contra.
Qed.

Lemma eutt_untau_2 : forall E X (s s' t t' : M E X),
    UnTau s s' -> UnTau t t' -> EquivUpToTau s t ->
    EquivUpToTau s' t'.
Proof.
  intros E X s s' t t' Hs.
  generalize dependent t'.
  generalize dependent t.
  induction Hs as [ s s' | s He ].
  - intros t t' Ht H. inversion H; subst; inversion Ht; subst; try dispatch_contra.
    + eapply IHHs. eassumption. assumption.
    + replace s'0 with s' in *. assumption.
      eapply untau_inj; eassumption.
  - intros t t' Ht H.
    destruct H;
      inversion Ht;
      subst;
      try dispatch_contra.
    + constructor.
    + constructor; assumption.
    + replace t'0 with t' in *.
      * assumption.
      * eapply untau_inj; eassumption.
    + constructor.
Qed.


Lemma eutt_untau_3: forall {E X} (t t': M E X),
    UnTau t t' -> EquivUpToTau t t'.
Proof.
  intros.
  assert (T_TAU: exists n, t = tauN n t').
  apply untau_count_layers; auto.

  destruct T_TAU as [N T_TAU].
  rewrite T_TAU.
  apply eutt_sym.
  apply tauN_eutt.
Qed.

Lemma eutt_untau_trans : forall E X (s s' t : M E X),
    UnTau s s' -> EquivUpToTau s' t -> EquivUpToTau s t.
Proof.
  cofix eutt_untau_trans.
  intros E X s s' t H I.
  destruct H.
  { inversion I; subst.
    - econstructor.
      + intros t' J; inversion J.
      + eassumption.
      + assumption.
    - econstructor.
      + intros t' J; inversion J.
      + eassumption.
      + assumption.
    - exfalso.
      apply (untau_notau H).
    - econstructor.
      + assumption.
      + eassumption.
      + assumption.
    - constructor.
      eapply eutt_untau_trans.
      + eassumption.
      + eapply eutt_tau_2.
        * eapply untau_untau. eassumption.
        * eassumption.
        * assumption.
    - econstructor.
      + intros t' J; inversion J.
      + eassumption.
      + assumption.
  }
  assumption.
Qed.



(* bindM relationship with eutt*)
Lemma eutt_bindM_through_tau: forall {E X Y} (x: M E X) (f: X -> M E Y),
    EquivUpToTau (bindM (Tau x) f)  (bindM x f).
Proof.
  intros until Y.
  cofix.

  intros.
  rewrite matchM.
  simpl.

  unfold bindM.


  remember (((cofix go (s : M E X) : M E Y :=
        match s with
        | Ret x0 => Tau (f x0)
        | @Vis _ _ Y e k => Vis e (fun y : Y => go (k y))
        | Tau k => Tau (go k)
        | Err s0 => Err (Event:=E) (X:=Y) s0
        end) x)) as BIND.
  apply eutt_sym.
  apply tauN_eutt_1.
Qed.

    
    


Import Logic.ProofIrrelevance.

Lemma eutt_err_t : forall E X s1 s2 (t : M E X) , EquivUpToTau (Err s1) t -> EquivUpToTau (Err s2) t.
Proof.  
  cofix eutt_err_t.
  intros E X s1 s2 t H.
  inversion H. subst.
  econstructor; auto. apply H1. eapply eutt_err_t. apply H2.
  econstructor.
Qed.  

Lemma eutt_trans : forall E X (s t u : M E X),
    EquivUpToTau s t -> EquivUpToTau t u -> EquivUpToTau s u.
Proof.
  cofix eutt_trans.
  intros E X s t u H1 H2.

  destruct H1 as [ | ? e1 ks kt | | | | ];
    inversion H2 as [ | ? e2 kt' ku | | t2 t2' u2 | | ].
  - (* Ret, Ret, Ret *) constructor.
  - (* Ret, Ret, Tau *) econstructor; try eassumption.
  - (* Vis, Vis, Vis *)
    (* induction Hk as [? Hk] using eq_sigT_rect. *) replace e2 with e1.
    + constructor.
      intro y.
      eapply eutt_trans.
      * auto.
      * replace kt with kt'.
        -- auto.
        -- apply inj_pair2 with (P := fun Y => Y -> M E X).
           auto.
    + symmetry. apply inj_pair2 with (P := E). auto.

  - (* Vis, Vis, Tau *) econstructor.
    + intros ? I. inversion I.
    + eassumption.
    + eapply eutt_trans.
      * constructor. eassumption.
      * assumption.

  - (* Tau, Tau, Tau *) econstructor.
    eapply eutt_trans; try eassumption.

  - (* Tau, Tau, ~Tau *)
    assert (I : exists s', UnTau s s' /\ EquivUpToTau t2' s').
    { apply eutt_untau with (s := t) (s' := t2').
      * assumption.
      * apply eutt_sym. assumption. }
    destruct I as [s' [I1 I2]].
    econstructor.
    + assumption.
    + eassumption.
    + eapply eutt_trans.
      * eapply eutt_sym; apply I2.
      * assumption.

  - (* Tau, Tau & ~Tau, Tau *)
    dispatch_contra.

  - (* Tau, Ret, Ret *)
    subst. eapply EquivTauLeft.
    * intros t' I; inversion I.
    * eassumption.
    * assumption.

  - (* Tau, Vis, Vis *)
    subst. eapply EquivTauLeft.
    * intros t' I; inversion I.
    * eassumption.
    * eapply eutt_trans; eassumption.

  - (* Tau, ~Tau & Tau, Tau *)
    dispatch_contra.
  - (* Tau, ~Tau & Tau, ~Tau *)
    dispatch_contra.

  - (* Tau, ~Tau, Tau *)
    constructor.
    eapply eutt_trans.
    + eapply eutt_untau_trans.
      * eassumption.
      * eassumption.
    + eapply eutt_sym.
      eapply eutt_untau_trans. eassumption.
      eapply eutt_sym.
      assumption.

  - subst. eapply EquivTauLeft.
    + intros t' I; inversion I.
    + eassumption.
    + eapply eutt_trans. apply H1. apply H2.

      
  - (* ~Tau, Tau, Tau *)
    assert (I : exists u', UnTau u u' /\ EquivUpToTau t' u').
    { eapply eutt_untau. apply OneTau. eassumption. eassumption. }
    destruct I as [u' [I ?]].
    destruct I.
    + econstructor.
      * assumption.
      * inversion H5. eassumption.
      * eapply eutt_trans; eassumption.
    + dispatch_contra.

  - (* ~Tau, Tau, ~Tau *)
    assert (I : t' = t2').
    { eapply untau_inj; eassumption. }
    rewrite <- I in *.
    inversion H1;
      inversion H5;
      subst;
      try assumption;
      try dispatch_contra.
    + inversion H12. subst.
      replace e0 with e.
      replace k0 with k2 in *.
      * constructor.
        intro y.
        eapply eutt_trans; eauto.
      * apply inj_pair2 with (P := fun Y => Y -> M E X); auto.
      * apply inj_pair2 with (P := E); auto.
    + exfalso. eapply untau_notau. eassumption.
    + constructor.

  - (* ~Tau, Tau & ~Tau, Tau *)
    dispatch_contra.

  - subst. econstructor.
    + intros u I; inversion I.
    + eassumption.
    + eapply eutt_err_t. apply H1.

  - econstructor.
Qed.


(** Register EUTT as an equivalence relation **)
Add Parametric Relation (E: Type -> Type) (X: Type): (M E X) (@EquivUpToTau E X)
    reflexivity proved by (@eutt_refl E X)
    symmetry proved by (@eutt_sym E X)
    transitivity proved by (@eutt_trans E X) as EUTT.


(* Placed this here because i need transitivity of EUTT *)
Lemma eutt_bindM_through_tauN: forall {E X Y} (n: nat) (x: M E X) (f: X -> M E Y),
    EquivUpToTau (bindM (tauN n x) f)  (bindM x f).
Proof.
  intros until Y.
  intros n.
  induction n.
  - intros.
    simpl.
    apply eutt_refl.

  - intros.
    replace (S n) with (n + 1).
    rewrite tauN_destruct.

    assert (ONE_STEP: EquivUpToTau
                        (bindM (Tau (tauN n x)) f)
                        (bindM (tauN n x) f)).
    apply eutt_bindM_through_tau.

    assert (N_STEPS: EquivUpToTau
               (bindM (tauN n x) f)
               (bindM x f)).
    auto.

    eapply eutt_trans; eauto.
    omega.
Qed.


Lemma eutt_bindM_through_unTau: forall {E X Y}  (t t': M E X) (f: X -> M E Y),
    UnTau t t' ->
    EquivUpToTau (bindM t f)  (bindM t' f).
Proof.
  intros.
  assert (T_TAU: exists n: nat, t = tauN n t').
  apply untau_count_layers; auto.

  destruct T_TAU as [n T_TAU].
  subst.
  apply eutt_bindM_through_tauN.
Qed.

(* This is not true, consider t' = Ret x, then it cannot be the
RHS of an UnTau in the result since Ret x >>= f = (Tau (f x)))
*)
Lemma untau_bindM: forall {E X Y} (t t': M E X) (f: X -> M E Y),
    (forall x: X, t' <> Ret x) -> 
    UnTau t t' -> UnTau (bindM t f) (bindM t' f).
Proof.
  intros until f.
  intros T'_NOT_RET.
  intros UNTAU.
  induction UNTAU.
  - rewrite (@matchM) with (i := bindM (Tau s) f).
    simpl.
    unfold bindM in *.
    apply OneTau.
    apply IHUNTAU; auto.

  - destruct s.
    + specialize (T'_NOT_RET x).
      contradiction.
    + apply NoTau.
      intros.
      rewrite (@matchM) with (i := bindM (Vis e k) f).
      simpl.
      discriminate.
    + specialize (H s).
      contradiction.
    + rewrite (@matchM) with (i := bindM (Err s) f).
      simpl.
      apply NoTau; auto.
Qed.
 
    
  
 
  

Instance reflexive_eutt {E} X : Reflexive (@EquivUpToTau E X).
Proof.
  unfold Reflexive.
  intros.
  apply eutt_refl.
Qed.


Instance symmetric_eutt{E} X : Symmetric (@EquivUpToTau E X).
Proof.
  unfold Symmetric.
  intros.
  apply eutt_sym; auto.
Qed.


Instance transitive_eutt{E} X : Transitive (@EquivUpToTau E X).
Proof.
  unfold Transitive.
  intros.
  eapply eutt_trans; eauto.
Qed.

  

Instance equivalence_eutt {E} X: Equivalence (@EquivUpToTau E X).
Proof.
  split.
  apply reflexive_eutt.
  apply symmetric_eutt.
  apply transitive_eutt.
Qed.

Instance equiv_eutt {E} X : Equiv (M E X) := (@EquivUpToTau E X).


Lemma tauN_eutt_upto_untau: forall {E X}
                              (n: nat)
                              (a b: M E X)
                              (EQ: UnTau a b),
    EquivUpToTau a (tauN n b).
Proof.
  intros.
  assert (EQ_A_B: EquivUpToTau a b).
  apply eutt_untau_3. auto.

  assert (EQ_B_TAUN: EquivUpToTau b (tauN n b)).
  apply tauN_eutt.
  rewrite eutt_trans; eauto.
  apply eutt_refl.
Qed.


(* Show theorems about bind being proper wrt equivalences *)
Lemma bindM_Ret: forall (A B: Type) (E: Type -> Type ) (a: A) (f: A -> M E B),
    bindM (Ret a) f ≡ f a.
Proof.
  intros.
  rewrite (@matchM) with (i := bindM (_) _).
  simpl.
  symmetry.
  apply tauN_eutt_1.
  Guarded.
Defined.






Lemma bindM_proper_wrt_eutt:
  forall {A B: Type} {E: Type -> Type} (a a': M E A) (f: A -> M E B),
    a ≡ a' -> bindM a f ≡ bindM a' f.
Proof.
  intros A B.
  cofix.

  intros until f.
  intros EQUIV.

  destruct a.
  - inversion EQUIV; subst; try reflexivity.
    destruct t'.
    ++ assert (LAYERS_IN_T: exists n, t = tauN n (Ret x0)).
       apply untau_count_layers.
       auto.
       destruct LAYERS_IN_T as [n LAYERS_WITNESS].
       rewrite LAYERS_WITNESS.
       rewrite <- tauN_destruct.

       assert (REMOVE_LAYERS: bindM (tauN (n + 1) (Ret x0)) f ≡
                                    bindM (Ret x0) f).
       apply eutt_bindM_through_tauN.
       rewrite REMOVE_LAYERS.

       assert (X_EQ_X0: x = x0).
       inversion H1. auto.

       rewrite X_EQ_X0.
       reflexivity.
    ++ inversion H1.
    ++ assert (~ (UnTau t (Tau t'))).
       apply untau_notau.
       contradiction.
    ++ inversion H1.
       Guarded.
       
  -
    inversion EQUIV; subst.
     
    ++ replace e with e1.
       replace k with k0.
       *** rewrite (@matchM) with (i := bindM (Vis e1 k0) f).
           rewrite (@matchM) with (i := bindM (Vis e1 k2) f).
           intros.
           simpl.
           constructor.
           intros.
           Guarded.
           unfold bindM in bindM_proper_wrt_eutt.
           apply bindM_proper_wrt_eutt with (f := f)
                                            (a := (k0 y))
                                            (a' := k2 y).
           apply H3.
           Guarded.

       *** apply inj_pair2 with (P := fun Y => Y -> M E A).
         assumption.

       *** apply inj_pair2 with (P := fun Y => E Y).
         assumption.

    ++ inversion H1; subst.
       *** 

           
           rewrite (@matchM) with (i := bindM (Vis e _) f).
           rewrite (@matchM) with (i := bindM (Tau t ) f).
           simpl.
           eapply EquivTauRight with (t' := bindM (Vis e1 k2) f).
           intros. discriminate.
           Check (t).
           Check (untau_bindM).
           Check (Vis e1 k2).
           

           (* 
            Lemma untau_bindM: forall {E X Y} (t t': M E X) (f: X -> M E Y),
                (forall x: X, t' <> Ret x) -> 
                UnTau t t' -> UnTau (bindM t f) (bindM t' f). *)
           (* TODO: Understand why the variables got named
           t0 and f0 *)
           apply untau_bindM with
               (t0 := t)
               (t' := (Vis e1 k2))
               (f0 := f); auto.
           Guarded.
           rewrite (@matchM) with (i := bindM (Vis e1 _) f).
           simpl.
           replace e1 with e.
           
           constructor.
           Guarded.
           intros.
           Guarded.
           apply bindM_proper_wrt_eutt with  (f:= f)
                                             (a := k y)
                                             (a' := k2 y).
           replace k with k0.
           apply H6.
           Guarded.

           apply inj_pair2 with (P := fun Y => Y -> M E A); auto.
           apply inj_pair2 with (P := fun Y => E Y); auto.

       
       *** assert (CONTRA: ~ (UnTau t (Tau t0))).
           apply untau_notau.
           contradiction.


  - Guarded.
    inversion EQUIV.
    ++ subst.
       rewrite (@matchM) with (i := bindM (Tau a) f).
       rewrite (@matchM) with (i := bindM (Tau t) f).
       simpl.
       constructor.

       assert (A_EQUIV_T: a ≡ t).
       auto.

       apply bindM_proper_wrt_eutt with (a := a) (a':= t) (f := f); auto.
       Guarded.
       
    ++ subst.
       destruct s'.
       *** inversion H2; subst.
           assert (A_AS_TAU_RET_X: exists n, a = tauN n (Ret x)).
           apply untau_count_layers; auto.
           
           destruct A_AS_TAU_RET_X as [N A_AS_TAU_RET_X].
           rewrite A_AS_TAU_RET_X.
           rewrite <- tauN_destruct.

           assert (REMOVE_TAUN: bindM (tauN (N + 1) (Ret x)) f ≡ bindM (Ret x) f).
           replace (N + 1)%nat with (S N).
           apply eutt_bindM_through_tauN.
           omega.

           rewrite REMOVE_TAUN.
           Guarded.

           rewrite (@matchM) with (i := bindM (Ret _) _).
           simpl.
           reflexivity.
           Guarded.

           
           rewrite (@matchM) with (i := bindM (Tau a) _).
           rewrite (@matchM) with (i := bindM (Tau t) _).
           simpl.
           constructor.
           apply bindM_proper_wrt_eutt with (f := f)
                                            (a := a)
                                            (a' := t).
           Guarded.

           assert (A_EQUIV_RET_X: a ≡ Ret x).
           apply eutt_untau_3; auto.

           assert (T_EQUIV_T': t ≡ t').
           apply eutt_untau_3; auto.

           rename H4 into RET_X_EQUIV_T'.

           rewrite A_EQUIV_RET_X.
           rewrite T_EQUIV_T'.
           rewrite RET_X_EQUIV_T'.
           reflexivity.
           Guarded.

       *** inversion H2; subst.
           ---- 
             rewrite (@matchM) with (i := bindM (Tau a) _).
             rewrite (@matchM) with (i := bindM (Vis e1 k2) _).
             simpl.
             eapply EquivTauLeft with (s' := bindM (Vis e k) f).
             intros. discriminate.
             apply untau_bindM with (f0 := f)
                                    (t := a)
                                    (t' := (Vis e k)).
             intros. discriminate.
             assumption.

             
             rewrite (@matchM) with (i := bindM (Vis e k) _).
             simpl.
             Guarded.
             replace e with e1.
             replace k with k0.
             constructor.
             Guarded.
             intros.
             apply  bindM_proper_wrt_eutt with (f := f)
                                               (a := k0 y)
                                               (a' := k2 y).
             apply H6.
             Guarded.
             apply inj_pair2 with (P := fun Y => Y -> M E A); auto.
             apply inj_pair2 with (P := fun Y =>  E Y); auto.
             
             
           ---- specialize (H0 t).
                rename H0 into CONTRA.
                contradiction.
           
         
       *** assert (CONTRA: ~ (UnTau a (Tau s'))).
           apply untau_notau.
           contradiction.
           Guarded.
       *** inversion H2; subst.
           rewrite (@matchM) with (i := bindM (Tau a) _).
           rewrite (@matchM) with (i := bindM (Tau t) _).
           simpl.
           constructor.
           apply bindM_proper_wrt_eutt with (f := f)
                                            (a := a)
                                            (a' := t).
           Guarded.

           assert (A_EQUIV_ERR: a ≡ Err s).
           apply eutt_untau_3; auto.
           rewrite A_EQUIV_ERR.
           rewrite H2.
           symmetry.
           apply tauN_eutt_1.

           rewrite (@matchM) with (i := bindM (Tau a) _).
           rewrite (@matchM) with (i := bindM (Err _) _).
           simpl.
           apply EquivTauLeft with (s' := bindM (Err s) f).
           Guarded.
           intros; discriminate.
           apply untau_bindM with
               (f0 := f)
               (t := a)
               (t' := (Err s)).
           intros. discriminate.
           auto.
           Guarded.
           rewrite (@matchM) with (i := bindM (Err _) _).
           simpl.
           constructor.
           
           

    ++ subst.
       specialize (H a).
       contradiction.

  -  inversion EQUIV; subst.
     
     + rewrite (@matchM) with (i := bindM (Err s) f).
       rewrite (@matchM) with (i := bindM (Tau _) f).
       simpl.
       apply EquivTauRight with (t' := bindM t' f).

       **  intros; discriminate.
       ** apply untau_bindM
            with (f0 := f)
                 (t0 := t)
                 (t'0 := t').
          inversion H1; subst; intros; discriminate.
          auto.
       ** replace (Err s) with (bindM (Err s) f).
          apply bindM_proper_wrt_eutt; auto.
          rewrite (@matchM) with (i := bindM (Err s) f).
          auto.
          Guarded.
    
       
       
     +  
       rewrite (@matchM) with (i := bindM (Err s) f).
       rewrite (@matchM) with (i := bindM (Err s2) f).
       simpl.
       constructor.
       Guarded.
Qed.

Lemma bindM_rewrite_fn: 
  forall {E: Type -> Type } {X Y: Type} (f g: X -> M E Y)
  (EXT: forall (x: X), f x ≡ g x) (ex: M E X), bindM ex f ≡ bindM ex g.
Proof.
  intros until g.
  intros EXT.
  cofix.
  destruct ex.
  - rewrite @matchM  with (i := bindM (Ret x) f).
    rewrite @matchM  with (i := bindM (Ret x) g).
    simpl.
    constructor.
    apply EXT.
    Guarded.

  - rewrite @matchM  with (i := bindM (Vis e k) f).
    rewrite @matchM  with (i := bindM (Vis e k) g).
    simpl.
    constructor.
    intros.
    apply bindM_rewrite_fn.
    Guarded.

  - rewrite @matchM  with (i := bindM (Tau ex) f).
    rewrite @matchM  with (i := bindM (Tau ex) g).
    simpl.
    constructor.
    apply bindM_rewrite_fn.
    Guarded.

  - rewrite @matchM  with (i := bindM (Err s) f).
    rewrite @matchM  with (i := bindM (Err s) g).
    simpl.
    constructor.
    Guarded.
Qed.

    
    
    
Create HintDb eutt.
Hint Resolve bindM_proper_wrt_eutt : eutt.

Instance bindm_eutt_proper {E X Y}:
  Proper ((@EquivUpToTau E X) ==> eq ==> (@EquivUpToTau E Y)) (@bindM E X Y).
Proof.
  intros.
  intros MEX MEX'.
  intros MEX_EQ_MEX'.

  intros F G.
  intros F_EQ_G.
  subst.

  apply bindM_proper_wrt_eutt.
  assumption.
Qed.

Check (@bindM).
Add Parametric Morphism (E: Type -> Type) (X Y : Type) : (@bindM E X Y) with
      signature ((@EquivUpToTau E X) ==> eq ==> (@EquivUpToTau E Y)) as bind.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.
  



Lemma eutt_coinduction_principle: forall E X (P: M E X -> M E X -> Prop)
    (RET: forall t1 t2 x, P t1 t2 -> t1 = Ret x -> t2 = Ret x)
    (VIS: forall {Y: Type }t1 t2 (e: E Y) (k1: Y -> M E X),
        P t1 t2 ->
        t1 = Vis e k1 ->
        (exists (k2: Y -> M E X),
            t2 = Vis e k2 /\
            ((forall (y: Y), P (k1 y) (k2 y)))))
    (TAU: forall t1 t2 t1',
        P t1 t2 ->
            t1 = Tau t1' /\
            (exists t2', t2 = Tau t2' /\ P t1' t2'))
    (ERR: forall t1 t2 s , t1 = Err (Event:=E) (X:=X) s ->
                exists s', t2 = Err (Event:=E) (X:=X) s'),
    (forall (t1 t2 : M E X), P t1 t2 -> EquivUpToTau t1 t2).
Proof.
  intros until P.
  cofix.
  intros until t2.
  intros P_TRACES.
  destruct t1.
  + assert (T2_RET: t2 = Ret x).
    eapply RET; eauto.
    subst.
    constructor.
  + assert (T2_VIS: exists k2, t2 = Vis e k2 /\ (forall y:Y, P (k y) (k2 y))).
    eapply VIS; eauto.
    destruct T2_VIS as [k2' [T2_VIS KEQUIV]].
    rewrite T2_VIS in *.
    subst.
    constructor.
    Guarded.
    intros.
    apply eutt_coinduction_principle; auto.
  + assert (T2TAU:  exists t2' : M E X, t2 = Tau t2' /\ P t1 t2').
    eapply TAU; eauto.
    destruct T2TAU as [t2' [T2TAu TEQUIV]].
    subst.
    constructor.
    apply eutt_coinduction_principle; auto.
  +
    assert (T2ERR: exists s', t2 = Err s').
    apply ERR with (t1 := (Err s)) (s := s); eauto.
    
    destruct T2ERR as [s' T2ERR].
    subst.
    constructor.
Qed.

(** Rewrite Rules **)


Lemma bindM_Vis: forall {E: Type -> Type} {A B Y: Type} (e: E Y) (f: A -> M E B) (k: Y -> M E A),
    bindM (Vis e k) f ≡ Vis e (fun y => bindM (k y) f).
Proof.
  intros until Y.
  intros until k.
  cofix.
  intros.
  rewrite @matchM with (i := (bindM (Vis e k) f)).
  rewrite @matchM with (i := (Vis e (fun y => bindM (k y) f))).
  simpl.

  constructor.
  intros.

  destruct (k y) eqn:ky.
  - rewrite @matchM. simpl.
    rewrite @matchM with (i := ((cofix go (s : M E A) : M E B :=
        match s with
        | Ret x0 => Tau (f x0)
        | @Vis _ _ Y0 e0 k0 => Vis e0 (fun y0 : Y0 => go (k0 y0))
        | Tau k0 => Tau (go k0)
        | Err s0 => Err (Event:=E) (X:=B) s0
        end) (Ret x))). simpl. reflexivity. Guarded.

  - rewrite @matchM with (i := ((cofix go (s : M E A) : M E B :=
        match s with
        | Ret x => Tau (f x)
        | @Vis _ _ Y1 e1 k1 => Vis e1 (fun y0 : Y1 => go (k1 y0))
        | Tau k1 => Tau (go k1)
        | Err s0 => Err (Event:=E) (X:=B) s0
        end) (Vis e0 k0))).
    rewrite @matchM.
    simpl.
    constructor.
    intros.
    reflexivity.
    Guarded.

  - rewrite @matchM.
    rewrite @matchM with (i :=
                                  ((cofix go (s : M E A) : M E B :=
                                      match s with
                                      | Ret x => Tau (f x)
                                      | @Vis _ _ Y0 e0 k0 => Vis e0 (fun y0 : Y0 => go (k0 y0))
                                      | Tau k0 => Tau (go k0)
                                      | Err s0 => Err (Event:=E) (X:=B) s0
                                      end) (Tau m))).
    simpl.
    Guarded.
    constructor. reflexivity.
    Guarded.

  - rewrite @matchM with (i :=
                                  ((cofix go (s0 : M E A) : M E B :=
                                      match s0 with
                                      | Ret x => Tau (f x)
                                      | @Vis _ _ Y0 e0 k0 => Vis e0 (fun y0 : Y0 => go (k0 y0))
                                      | Tau k0 => Tau (go k0)
                                      | Err s1 => Err (Event:=E) (X:=B) s1
                                      end) (Err s))).
    rewrite @matchM.
    simpl.
    reflexivity.
    Guarded.
Defined.


(* SAZ: 
Functoriality of (M E) probably holds only up to coinductively defined
bisimulation of eq.  Or, we should assume as an Aximo that eq coincides
with that bisimulation.
*)
Instance M_functor_eutt_laws {E} : (@FunctorLaws (M E)) (@mapM E) (@equiv_eutt E).
Proof.
Admitted.  

(* (x >>= f) >> g ~= x >>= (fun x' => f x' >>= g ) *)
Lemma bindM_assoc: forall {E: Type -> Type} {A B C: Type} (a: M E A) (f: A -> M E B)
                     (g: B -> M E C),
    (bindM (bindM a f) g) ≡ bindM  a (fun a' => bindM (f a') g).
Admitted.

Program Instance M_monad_eutt_laws {E} : (@MonadLaws (M E)) (@functor_M E) (@monad_M E) _ _ _.
Next Obligation.
  Admitted.
Next Obligation.
  Admitted.
Next Obligation.
Admitted.

Check (M_monad_eutt_laws).



Lemma remove_tau: forall {X: Type} {E: Type -> Type} (x: M E X), Tau x ≡ x.
Proof.
  intros.
  repeat (rewrite <- tauN_eutt_1).
  auto.
Defined.


Lemma bindM_Ret_2: forall {E: Type -> Type} {X: Type}  (mex: M E X),
    bindM mex (Ret (X:=X)) ≡ mex.
Proof.
  intros until X.
  cofix CIH.
  
  intros.
  rewrite @matchM with (i := bindM _ _).
  simpl.
  destruct mex; simpl.
  - rewrite remove_tau.
    reflexivity.
  - constructor.
    intros.
    apply CIH.
  - constructor.
    apply CIH.
  - constructor.
Defined.

Lemma bindM_Err: forall {X Y :Type} {E: Type -> Type} (e: String.string) (f: X -> M E Y),
  bindM (Err e) f ≡ Err e.
Proof.
  intros.
  rewrite @matchM with (i := (bindM _ _)).
  auto.
Defined.

Create HintDb euttnormdb.
Hint Rewrite (@bindM_assoc) : euttnormdb.
Hint Rewrite (@bindM_Ret) : euttnormdb.
Hint Rewrite (@bindM_Ret_2) : euttnormdb.
Hint Rewrite (@bindM_Vis) : euttnormdb.
Hint Rewrite (@remove_tau) : euttnormdb.
Hint Rewrite (@bindM_Err) : euttnormdb.

Ltac euttnorm := simpl; autorewrite with euttnormdb; simpl; auto.
    

Add Parametric Morphism (E: Type -> Type) (X : Type) : (@Tau E X) with
      signature ((@EquivUpToTau E X) ==>(@EquivUpToTau E X)) as Tau.
Proof.
  intros.
  constructor. auto.
Qed.



(** Show that we can rewrite functions which agree pointwise with respect to EUTT
under bind **)
Definition PointwiseEUTT {E: Type -> Type} {X Y: Type} (f: X -> M E Y) (g: X -> M E Y) : Prop :=
  forall (x: X), f x ≡ g x.

Instance bindm_function_pointwise_proper {E X Y}:
  Proper ((@EquivUpToTau E X)
            ==> (@PointwiseEUTT E X Y)
            ==>  (@EquivUpToTau E Y))
         (@bindM E X Y).
Proof.
  intros MEX MEX' MEXEQUIV.
  intros F G FEQUIV.
  unfold PointwiseEUTT in FEQUIV.

  generalize dependent MEX.
  generalize dependent MEX'.
  generalize dependent F.
  generalize dependent G.
  cofix.
  Guarded.
  intros.
  Guarded.
  destruct MEX.
  - inversion MEXEQUIV; subst.
    + euttnorm.
      Guarded.
      rewrite FEQUIV.
      Guarded.
      reflexivity.
Admitted.


End MonadVerif.
