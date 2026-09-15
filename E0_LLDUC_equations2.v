(* E0_LLDUC_equations2.v
   Standalone. Stdlib only. Q and Z. No Reals.
   Extends E0_LLDUC_equations.v with every extra Q/Z identity
   from the audit that does not require H or recs.
   Does NOT prove LB(H_LLDUC, a_star), P30.E0, or spectral 504.
*)
Require Import ZArith QArith Qring Qfield Lia Setoid.

Open Scope Q_scope.

(* ---------- Akiyama-Tanigawa -> Bernoulli ---------- *)
Fixpoint AT (n m : nat) : Q :=
  match n with
  | O => 1 / inject_Z (Z.of_nat (S m))
  | S n' => inject_Z (Z.of_nat (S m)) * (AT n' m - AT n' (S m))
  end.

Definition bern (n : nat) : Q := AT n O.

Theorem bern0 : bern 0 == 1. Proof. vm_compute. reflexivity. Qed.
Theorem bern1 : bern 1 == 1 # 2. Proof. vm_compute. reflexivity. Qed.
Theorem bern2 : bern 2 == 1 # 6. Proof. vm_compute. reflexivity. Qed.
Theorem bern4 : bern 4 == -1 # 30. Proof. vm_compute. reflexivity. Qed.
Theorem bern6 : bern 6 == 1 # 42. Proof. vm_compute. reflexivity. Qed.
Theorem bern8 : bern 8 == -1 # 30. Proof. vm_compute. reflexivity. Qed.

Definition zeta_neg1 : Q := -1 # 12.
Definition zeta_neg3 : Q := 1 # 120.
Definition zeta_neg5 : Q := -1 # 252.

Theorem zeta_neg1_from_B2 :
  zeta_neg1 == - bern 2 / inject_Z 2.
Proof. vm_compute. reflexivity. Qed.
Theorem zeta_neg3_from_B4 :
  zeta_neg3 == - bern 4 / inject_Z 4.
Proof. vm_compute. reflexivity. Qed.
Theorem zeta_neg5_from_B6 :
  zeta_neg5 == - bern 6 / inject_Z 6.
Proof. vm_compute. reflexivity. Qed.

Definition eis_Gen (w : nat) : Q :=
  -(inject_Z (2 * Z.of_nat w)) / bern w.

Definition eis_ZB (k : nat) : Q :=
  -(inject_Z (4 * Z.of_nat k)) / bern (2 * k).

Theorem eis_Gen_2 : eis_Gen 2 == -24. Proof. vm_compute. reflexivity. Qed.
Theorem eis_Gen_4 : eis_Gen 4 == 240. Proof. vm_compute. reflexivity. Qed.
Theorem eis_Gen_6 : eis_Gen 6 == -504. Proof. vm_compute. reflexivity. Qed.

Theorem eis_Gen_4_is_not_negative :
  ~ eis_Gen 4 == -240.
Proof. vm_compute. discriminate. Qed.

Theorem eis_ZB_1 : eis_ZB 1 == -24. Proof. vm_compute. reflexivity. Qed.
Theorem eis_ZB_2 : eis_ZB 2 == 240. Proof. vm_compute. reflexivity. Qed.
Theorem eis_ZB_3 : eis_ZB 3 == -504. Proof. vm_compute. reflexivity. Qed.
Theorem eis_ZB_4 : eis_ZB 4 == 480. Proof. vm_compute. reflexivity. Qed.

Theorem conventions_agree_on_240 :
  eis_Gen 4 == eis_ZB 2 /\ eis_Gen 4 == 240.
Proof. split; vm_compute; reflexivity. Qed.

Theorem conventions_agree_on_504 :
  eis_Gen 6 == eis_ZB 3 /\ eis_Gen 6 == -504.
Proof. split; vm_compute; reflexivity. Qed.

Definition E2_q1 : Q := -24.
Definition E4_q1 : Q := 240.
Definition E6_q1 : Q := -504.
Definition E2E4_q1 : Q := E2_q1 + E4_q1.

Theorem ramanujan_q1 :
  E4_q1 == (E2E4_q1 - E6_q1) / 3.
Proof. vm_compute. reflexivity. Qed.

Theorem three_readings_of_504 :
  inject_Z 504 == 3 * E4_q1 - E2E4_q1
  /\ inject_Z 504 == 2 * E4_q1 + inject_Z 24
  /\ inject_Z 504 == E4_q1 + (2 * E4_q1 - E2E4_q1).
Proof. repeat split; vm_compute; reflexivity. Qed.

Definition mersenne6 : Z := (2^6 - 1)%Z.
Definition golay_d : Z := 8%Z.
Definition e8_root_count : Z := 240%Z.

Theorem eta_atom_identity : (mersenne6 * golay_d = 504)%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem EI6_integer : (2 * e8_root_count + 24 = 504)%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem EI5_integer : (2 * 240 - (-24) = 504)%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem twelve_over_B6 :
  (inject_Z 12 / bern 6) == inject_Z 504.
Proof. vm_compute. reflexivity. Qed.

Theorem two_adic_504 :
  (504 mod 8 = 0)%Z
  /\ (504 mod 16 = 8)%Z
  /\ (504 = 8 * 63)%Z
  /\ (7 * 72 = 504)%Z.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem gcd_504_10pow12 :
  Z.gcd 504 1000000000000 = 8%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem coincidence_113 :
  (9 * 56 = 504)%Z /\ ((113 - 1) / 2 = 56)%Z.
Proof. split; vm_compute; reflexivity. Qed.

Definition pico : Q := Eval vm_compute in Qred (1 / inject_Z ((10 ^ 12)%Z)).
Definition eta  : Q := Eval vm_compute in Qred (- eis_Gen 6 * pico).
Definition eta_atoms : Q := Eval vm_compute in Qred (inject_Z (mersenne6 * golay_d) * pico).

Theorem eta_positive : 0 < eta. Proof. vm_compute. reflexivity. Qed.

Theorem two_routes_agree : eta == eta_atoms.
Proof. vm_compute. reflexivity. Qed.

Theorem A4_eta_from_bernoulli :
  bern 6 == 1 # 42
  /\ eta == (12 / bern 6) * pico
  /\ eta * inject_Z ((10 ^ 12)%Z) * bern 6 == 12.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem EI5_eta : eta == (2 * eis_ZB 2 - eis_ZB 1) * pico.
Proof. vm_compute. reflexivity. Qed.

Theorem EI6_eta : eta == inject_Z (2 * e8_root_count + 24) * pico.
Proof. vm_compute. reflexivity. Qed.

Theorem eta_is_504_pico :
  eta == inject_Z 504 * pico
  /\ eta == 63 # 125000000000
  /\ eta * inject_Z ((10 ^ 12)%Z) == inject_Z 504.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem Qnum_Qden_eta :
  Qnum eta = 63%Z /\ Z.pos (Qden eta) = 125000000000%Z.
Proof. vm_compute. reflexivity. Qed.

Definition a_star_of (h : Q) : Q := h - eta.

Definition head : Q :=
  Eval vm_compute in Qred (inject_Z (-22140966962032000)%Z * pico).

Definition a_star : Q := Eval vm_compute in Qred (a_star_of head).

Theorem tail_for_every_head :
  forall h : Q,
    (h - a_star_of h) * inject_Z ((10 ^ 12)%Z) == inject_Z 504.
Proof.
  intros h. unfold a_star_of.
  setoid_replace (h - (h - eta)) with eta by ring.
  vm_compute. reflexivity.
Qed.

Theorem renaming_is_not_core_shift :
  a_star == head - eta.
Proof. unfold a_star. vm_compute. reflexivity. Qed.

Theorem tail_of_this_head :
  (head - a_star) * inject_Z ((10 ^ 12)%Z) == inject_Z 504
  /\ a_star * inject_Z ((10 ^ 12)%Z) == inject_Z (-22140966962032504)
  /\ head * inject_Z ((10 ^ 12)%Z) == inject_Z (-22140966962032000)
  /\ a_star == -2767620870254063 # 125000000000.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem a_star_mod_1000_pico :
  (Z.modulo (-22140966962032504) 1000 = 496)%Z
  /\ (Z.modulo (-22140966962032000) 1000 = 0)%Z
  /\ (Z.modulo ((-22140966962032504) + 504) 1000 = 0)%Z.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem head_mod_2000 :
  Z.modulo (-22140966962032000) 2000 = 0%Z.
Proof. vm_compute. reflexivity. Qed.

Definition E_ref : Q :=
  Eval vm_compute in Qred (inject_Z (-22126714)%Z / inject_Z 1000).
Definition two_lam : Q :=
  Eval vm_compute in Qred (inject_Z (-14252962032)%Z / inject_Z ((10 ^ 9)%Z)).

Theorem seed_accounting :
  head == E_ref + two_lam
  /\ a_star == E_ref + two_lam - eta
  /\ (two_lam - (a_star - E_ref)) * inject_Z ((10 ^ 12)%Z) == inject_Z 504.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem residual_on_pico : eta / pico == inject_Z 504.
Proof. vm_compute. reflexivity. Qed.

Theorem residual_not_504_on_1e11 :
  let g := 1 / inject_Z ((10 ^ 11)%Z) in ~ (eta / g == inject_Z 504).
Proof. vm_compute. discriminate. Qed.

Theorem residual_not_504_on_1e13 :
  let g := 1 / inject_Z ((10 ^ 13)%Z) in ~ (eta / g == inject_Z 504).
Proof. vm_compute. discriminate. Qed.

Fixpoint lucas_pair (n : nat) : Z * Z :=
  match n with
  | O => (2%Z, 1%Z)
  | S n' => let (a, b) := lucas_pair n' in (b, (a + b)%Z)
  end.

Definition lucas (n : nat) : Z := fst (lucas_pair n).

Theorem L16_is_2207 : lucas 16 = 2207%Z.
Proof. vm_compute. reflexivity. Qed.

Definition width : Q :=
  Eval vm_compute in Qred
    ((inject_Z (12 * lucas 16 + 7) / inject_Z 7) * eta).

Theorem width_lowest_terms :
  width == 238419 # 125000000000
  /\ width * inject_Z ((10 ^ 12)%Z) == inject_Z 1907352.
Proof. split; vm_compute; reflexivity. Qed.

Theorem width_is_W_plus_eta :
  let W_pico := (12 * 72 * 2207)%Z in
  width * inject_Z ((10 ^ 12)%Z) == inject_Z (W_pico + 504)
  /\ (W_pico + 504 = 1907352)%Z
  /\ (7 * 72 = 504)%Z.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* Two windows: E_Phi / E_0t are v497 seed labels, not Rayleigh values. *)
Definition E_Phi : Q :=
  Eval vm_compute in Qred (inject_Z (-22053164626725997)%Z * pico).
Definition E_0t : Q :=
  Eval vm_compute in Qred (inject_Z (-22053164628633349)%Z * pico).

Theorem two_windows :
  (E_Phi - E_0t) * inject_Z ((10 ^ 12)%Z) == inject_Z 1907352
  /\ (E_Phi - a_star) * inject_Z ((10 ^ 12)%Z) == inject_Z 87802335306507
  /\ (E_0t - a_star) * inject_Z ((10 ^ 12)%Z) == inject_Z 87802333399155
  /\ (E_Phi - E_0t) == width.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem L70493_is_ring :
  (E_Phi - a_star) == width + (E_0t - a_star).
Proof. vm_compute. reflexivity. Qed.

Definition downward_closed (P : Q -> Prop) : Prop :=
  forall a b : Q, a <= b -> P b -> P a.

Theorem sandwich_shape :
  forall (E a b : Q),
    a <= E -> E <= b -> a <= E /\ E <= b.
Proof. intros. split; assumption. Qed.

Theorem the_504_connection :
    (mersenne6 * golay_d = 504)%Z
  /\ bern 6 == 1 # 42
  /\ eis_Gen 6 == -504
  /\ eis_ZB 3 == -504
  /\ eis_Gen 4 == 240
  /\ (2 * e8_root_count + 24 = 504)%Z
  /\ eta == inject_Z 504 * pico
  /\ (head - a_star) * inject_Z ((10 ^ 12)%Z) == inject_Z 504
  /\ lucas 16 = 2207%Z
  /\ width == 238419 # 125000000000
  /\ a_star == -2767620870254063 # 125000000000
  /\ E4_q1 == (E2E4_q1 - E6_q1) / 3
  /\ (E_Phi - E_0t) == width.
Proof. repeat split; vm_compute; reflexivity. Qed.

Module NotProved.
  Parameter H_LLDUC : nat -> nat -> Q.
  Parameter LB : Q -> Prop.
  Parameter P30_E0 : Q -> Prop.
  Parameter spectral_role_of_504 : Prop.
End NotProved.
