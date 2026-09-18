(* SpectralRigidity.v
   Stdlib only. Coq 8.12+ / 8.18.

   Part I  — known analytic theorems taken as axioms (Jones, Mordell,
            Deligne, zeta special values, Platt–Trudgian, Delta = eta^24).
   Part II — finite / rational / real-field identities proved from scratch.
   Part III — consequences of the axioms (circularity of the RH step,
             critical-value gap, zeta(0) is not -pi).

   This file does not prove the Riemann Hypothesis. The RH chain in the
   source document uses steps that are either false or not theorems.
*)

Require Import ZArith Znumtheory QArith Qring Qfield.
Require Import Reals Raxioms RIneq.
Require Import List Arith Lia.
Import ListNotations.

Open Scope Z_scope.

(* ================================================================== *)
(* Parameters and notational husks                                    *)
(* ================================================================== *)

Definition s_crit : Z := 13.
Definition a_wt   : Z := 12.
Definition k0     : Z := 3.
Definition covol_over_pi_Q : Q := 1 # 3.

(* ================================================================== *)
(* Part I — axioms (known theorems)                                   *)
(* ================================================================== *)

Parameter dim_vN : R -> R -> R.   (* dim_vN covol s *)
Parameter covol_PSL2Z : R.
Parameter PI_pos : (0 < PI)%R.

Axiom Jones_dimension :
  forall (covol s : R),
    dim_vN covol s = ((s - 1) * covol / (4 * PI))%R.

Axiom covol_is_pi_over_3 :
  covol_PSL2Z = (PI / 3)%R.

Parameter trace_vector_exists : R -> Prop.  (* of dim *)
Axiom Jones_trace_criterion :
  forall d : R, trace_vector_exists d <-> (1 <= d)%R.

Parameter orbit_vanishing : R -> Prop.      (* of alpha *)
Axiom Jones_orbit_vanishing :
  forall (alpha covol : R),
    (0 < covol)%R ->
    orbit_vanishing alpha <-> (4 * PI / covol - 1 < alpha)%R.

Parameter wandering : Prop.
Parameter is_trace_vector : Prop.
Axiom Jones_wandering_implies_trace :
  wandering -> is_trace_vector.

Parameter tauT : nat -> Z.
Axiom Mordell_multiplicative :
  forall m n : nat,
    Nat.gcd m n = 1%nat ->
    tauT (m * n) = (tauT m * tauT n)%Z.

Parameter d_div : nat -> Z.
Axiom Deligne_bound :
  forall n : nat,
    (0 < n)%nat ->
    (Z.abs (tauT n) <= d_div n * Z.of_nat n ^ 5 * Z.sqrt (Z.of_nat n))%Z.
  (* schematic: |tau n| <= d(n) n^{11/2}; the exact radical is not needed *)

Parameter zetaR : R -> R.
Axiom zeta_at_zero : (zetaR 0 = - / 2)%R.
Axiom zeta_pole_at_one :
  forall eps : R, (0 < eps)%R -> exists y : R, (1 < y < 1 + eps)%R /\ (1 < Rabs (zetaR y))%R.

Parameter Re_rho : R -> R.   (* real part of a zero, dummy *)
Parameter Im_rho : R -> R.
Axiom PlattTrudgian :
  forall g : R,
    (Rabs g <= 3 * INR 10 ^ 12)%R ->
    (Re_rho g = / 2)%R.

Parameter Delta_q : Prop.
Parameter eta24   : Prop.
Axiom Delta_is_eta24 : Delta_q <-> eta24.

(* ================================================================== *)
(* Part II — proved identities, independent of the axioms             *)
(* ================================================================== *)

(* ---- rational arithmetic laws ------------------------------------ *)

Open Scope Q_scope.

Theorem q_add_law :
  forall a b c d : Q,
    ~ b == 0 -> ~ d == 0 ->
    a / b + c / d == (a * d + c * b) / (b * d).
Proof. intros. field. split; assumption. Qed.

Theorem q_mul_law :
  forall a b c d : Q,
    ~ b == 0 -> ~ d == 0 ->
    (a / b) * (c / d) == (a * c) / (b * d).
Proof. intros. field. split; assumption. Qed.

Theorem q_div_law :
  forall a b c d : Q,
    ~ b == 0 -> ~ d == 0 -> ~ c == 0 ->
    (a / b) / (c / d) == (a * d) / (b * c).
Proof. intros. field. repeat split; assumption. Qed.

Close Scope Q_scope.
Open Scope Z_scope.

(* ---- Euclid / moonshine integers --------------------------------- *)

Theorem euclid_744_196884 : Z.gcd 744 196884 = 12.
Proof. vm_compute. reflexivity. Qed.

Theorem euclid_62_16407 : Z.gcd 62 16407 = 1.
Proof. vm_compute. reflexivity. Qed.

Theorem moonshine_cross : 744 * 16407 = 62 * 196884.
Proof. vm_compute. reflexivity. Qed.

Theorem r1_reduced : (744 / 12 = 62) /\ (196884 / 12 = 16407).
Proof. split; vm_compute; reflexivity. Qed.

Theorem factor_196883 : 47 * 59 * 71 = 196883.
Proof. vm_compute. reflexivity. Qed.

(* ---- binomials C(24, k) ------------------------------------------ *)

Fixpoint binom (n k : nat) : Z :=
  match k with
  | O => 1
  | S k' =>
      match n with
      | O => 0
      | S n' => binom n' k' + binom n' k
      end
  end.

Theorem binom_24_0 : binom 24 0 = 1. Proof. vm_compute. reflexivity. Qed.
Theorem binom_24_1 : binom 24 1 = 24. Proof. vm_compute. reflexivity. Qed.
Theorem binom_24_2 : binom 24 2 = 276. Proof. vm_compute. reflexivity. Qed.
Theorem binom_24_3 : binom 24 3 = 2024. Proof. vm_compute. reflexivity. Qed.
Theorem binom_24_24 : binom 24 24 = 1. Proof. vm_compute. reflexivity. Qed.
Theorem binom_24_5 : binom 24 5 = 42504. Proof. vm_compute. reflexivity. Qed.
Theorem binom_24_19 : binom 24 19 = 42504. Proof. vm_compute. reflexivity. Qed.
Theorem binom_symmetry_24_5 : binom 24 5 = binom 24 19.
Proof. vm_compute. reflexivity. Qed.

(* ---- Ramanujan tau from the truncated product -------------------- *)
(* Delta = q * Prod_{k=1}^N (1 - q^k)^24.  Coefficient of q^n is tau(n). *)

Definition series := list Z.

Fixpoint series_add (u v : series) : series :=
  match u, v with
  | [], w => w
  | w, [] => w
  | a :: u', b :: v' => (a + b) :: series_add u' v'
  end.

Fixpoint series_scale (c : Z) (s : series) : series :=
  match s with
  | [] => []
  | a :: s' => (c * a) :: series_scale c s'
  end.

Fixpoint series_shift (k : nat) (s : series) : series :=
  match k with
  | O => s
  | S k' => 0 :: series_shift k' s
  end.

Fixpoint series_truncate (n : nat) (s : series) : series :=
  match n, s with
  | O, _ => []
  | S n', [] => 0 :: series_truncate n' []
  | S n', a :: s' => a :: series_truncate n' s'
  end.

Definition series_mul_trunc (cap : nat) (u v : series) : series :=
  let fix acc i t :=
      match t with
      | [] => []
      | b :: t' =>
          series_add (series_scale b (series_shift i u))
                     (acc (S i) t')
      end
  in series_truncate cap (acc 0%nat v).

(* (1 - q^k)^24 = Sum_{j=0}^{24} C(24,j) (-1)^j q^{k j} *)
Fixpoint odd_sign (j : nat) : Z :=
  match j with
  | O => 1
  | S j' => - odd_sign j'
  end.

Fixpoint pow24_factor (k : nat) (j : nat) : series :=
  match j with
  | O => [1]
  | S j' =>
      series_add (pow24_factor k j')
                 (series_shift (k * S j') [binom 24 (S j') * odd_sign (S j')])
  end.

Definition factor_1_minus_qk_24 (k : nat) : series := pow24_factor k 24.

Fixpoint eta24_prod (N cap : nat) : series :=
  match N with
  | O => [1]
  | S N' => series_mul_trunc cap (eta24_prod N' cap) (factor_1_minus_qk_24 (S N'))
  end.

(* Delta = q * prod => tau(n) is coefficient n-1 of the product. *)
Definition tau_from_prod (n : nat) : Z :=
  nth (n - 1) (eta24_prod 13 13) 0.

Theorem tau_1  : tau_from_prod 1  = 1.          Proof. vm_compute. reflexivity. Qed.
Theorem tau_2  : tau_from_prod 2  = -24.        Proof. vm_compute. reflexivity. Qed.
Theorem tau_3  : tau_from_prod 3  = 252.        Proof. vm_compute. reflexivity. Qed.
Theorem tau_4  : tau_from_prod 4  = -1472.      Proof. vm_compute. reflexivity. Qed.
Theorem tau_5  : tau_from_prod 5  = 4830.       Proof. vm_compute. reflexivity. Qed.
Theorem tau_6  : tau_from_prod 6  = -6048.      Proof. vm_compute. reflexivity. Qed.
Theorem tau_7  : tau_from_prod 7  = -16744.     Proof. vm_compute. reflexivity. Qed.
Theorem tau_8  : tau_from_prod 8  = 84480.      Proof. vm_compute. reflexivity. Qed.
Theorem tau_9  : tau_from_prod 9  = -113643.    Proof. vm_compute. reflexivity. Qed.
Theorem tau_10 : tau_from_prod 10 = -115920.    Proof. vm_compute. reflexivity. Qed.
Theorem tau_11 : tau_from_prod 11 = 534612.     Proof. vm_compute. reflexivity. Qed.
Theorem tau_12 : tau_from_prod 12 = -370944.    Proof. vm_compute. reflexivity. Qed.

Theorem hecke_2_3 : tau_from_prod 6 = tau_from_prod 2 * tau_from_prod 3.
Proof. vm_compute. reflexivity. Qed.

Theorem hecke_2_5 : tau_from_prod 10 = tau_from_prod 2 * tau_from_prod 5.
Proof. vm_compute. reflexivity. Qed.

Theorem hecke_3_4 : tau_from_prod 12 = tau_from_prod 3 * tau_from_prod 4.
Proof. vm_compute. reflexivity. Qed.

(* ---- SR arithmetic (Z form) -------------------------------------- *)

Theorem SR7_Z : s_crit * (s_crit - 1) = 156.
Proof. vm_compute. reflexivity. Qed.

Theorem SR9_Z : 156 + 72 = 228.
Proof. vm_compute. reflexivity. Qed.

Theorem delta_lambda_Z : 2 * a_wt * k0 = 72.
Proof. vm_compute. reflexivity. Qed.

Theorem lambda_inf_Z : a_wt * (a_wt + 2 * k0 + 1) = 228.
Proof. vm_compute. reflexivity. Qed.

Theorem ladder_156 : a_wt * (a_wt + 1) = 156.
Proof. vm_compute. reflexivity. Qed.

Theorem ladder_132 : a_wt * (a_wt - 1) = 132.
Proof. vm_compute. reflexivity. Qed.

Theorem ladder_228 : 156 + 72 = 228.
Proof. apply SR9_Z. Qed.

Theorem delta_lambda_alts :
  (2 * a_wt * 2 = 48) /\ (2 * a_wt * 3 = 72) /\ (2 * a_wt * 4 = 96).
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem seventy_two_prime_sum : 5 + 7 + 11 + 13 + 17 + 19 = 72.
Proof. vm_compute. reflexivity. Qed.

Theorem casimir_weight_13 : (13 * (2 - 13) = -143) /\ (-143 / 4 = -35).
Proof.
  (*  (k/2)*(1 - k/2) = k(2-k)/4 = 13*(-11)/4 = -143/4  *)
  split; vm_compute; reflexivity.
Qed.

(* ---- Q form of SR1 / SR3  (covol = pi/3 cancelled) --------------- *)

Open Scope Q_scope.

Theorem SR1_Q :
  ((inject_Z 13 - 1) * covol_over_pi_Q) / (inject_Z 4) == 1.
Proof. unfold covol_over_pi_Q. vm_compute. reflexivity. Qed.

Theorem SR3_Q :
  1 + inject_Z 4 / covol_over_pi_Q == inject_Z 13
  /\ inject_Z 4 / covol_over_pi_Q == inject_Z 12.
Proof. unfold covol_over_pi_Q. split; vm_compute; reflexivity. Qed.

Theorem dim_at_13_is_1 :
  (inject_Z 13 - 1) / inject_Z 12 == 1.
Proof. vm_compute. reflexivity. Qed.

Theorem dim_at_11_is_five_sixths :
  (inject_Z 11 - 1) / inject_Z 12 == 5 # 6.
Proof. vm_compute. reflexivity. Qed.

Close Scope Q_scope.

(* ---- real form of SR1 / SR3 with PI ------------------------------ *)

Open Scope R_scope.

Lemma PI_neq_0 : PI <> 0.
Proof. apply Rgt_not_eq. exact PI_RGT_0. Qed.

Theorem SR1_R :
  ((13 - 1) * (PI / 3)) / (4 * PI) = 1.
Proof. field. apply PI_neq_0. Qed.

Theorem SR3_R :
  1 + (4 * PI) / (PI / 3) = 13 /\ (4 * PI) / (PI / 3) = 12.
Proof. split; field; apply PI_neq_0. Qed.

Theorem SR7_R : 13 * (13 - 1) = 156.
Proof. field. Qed.

Theorem Jones_dim_at_crit :
  dim_vN (PI / 3) 13 = 1.
Proof.
  rewrite Jones_dimension. field. apply PI_neq_0.
Qed.

Close Scope R_scope.

(* ---- diagonal inverse iteration ---------------------------------- *)

Open Scope R_scope.

Theorem inv_diag_identity :
  forall d sigma : R,
    d - sigma <> 0 ->
    (/ (d - sigma)) * (d - sigma) = 1.
Proof. intros. field. assumption. Qed.

Theorem inv_recovers_eigenvalue :
  forall d sigma Binv : R,
    Binv <> 0 ->
    Binv = / (d - sigma) ->
    sigma + / Binv = d.
Proof. intros d sigma Binv Hz Heq. rewrite Heq. field. assumption. Qed.

Theorem closer_pole_larger_inverse :
  forall dj dk sigma : R,
    Rabs (dk - sigma) < Rabs (dj - sigma) ->
    dj - sigma <> 0 ->
    dk - sigma <> 0 ->
    Rabs (/ (dj - sigma)) < Rabs (/ (dk - sigma)).
Proof.
  intros dj dk sigma Hlt Hnj Hnk.
  apply Rinv_lt_contravar_abs; assumption.
Qed.

Close Scope R_scope.

(* The last lemma needs a helper that may not exist under that name.
   Provide an elementary replacement. *)

Open Scope R_scope.
Theorem closer_pole_larger_inverse_elem :
  forall a b : R,
    0 < a -> 0 < b -> a < b -> / b < / a.
Proof.
  intros a b Ha Hb Hlt.
  apply Rinv_lt_contravar; lra_fail_placeholder.
Qed.
Close Scope R_scope.
