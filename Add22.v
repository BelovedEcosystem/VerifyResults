(* Add22.v
   Inventory husks that live in Q and Z.
   Stdlib only. No Reals, no Qreals, no Lra, no Interval, no Coquelicot.

   Criterion: every theorem is a finite rational/integer identity.
   None of these is an analytic zeta, an L-function, a non-trivial zero,
   or an RH criterion.
*)
Require Import ZArith QArith Qring Qfield Lia List Arith.
Import ListNotations.

Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Akiyama-Tanigawa Bernoulli numbers (B1 = +1/2 convention)          *)
(* ------------------------------------------------------------------ *)
Fixpoint AT (n m : nat) : Q :=
  match n with
  | O => 1 / inject_Z (Z.of_nat (S m))
  | S n' => inject_Z (Z.of_nat (S m)) * (AT n' m - AT n' (S m))
  end.

Definition bern (n : nat) : Q := AT n O.

Theorem bern0 : bern 0 == 1. Proof. vm_compute. reflexivity. Qed.
Theorem bern1 : bern 1 == 1 # 2. Proof. vm_compute. reflexivity. Qed.
Theorem bern2 : bern 2 == 1 # 6. Proof. vm_compute. reflexivity. Qed.
Theorem bern3 : bern 3 == 0. Proof. vm_compute. reflexivity. Qed.
Theorem bern4 : bern 4 == -1 # 30. Proof. vm_compute. reflexivity. Qed.
Theorem bern5 : bern 5 == 0. Proof. vm_compute. reflexivity. Qed.
Theorem bern6 : bern 6 == 1 # 42. Proof. vm_compute. reflexivity. Qed.
Theorem bern7 : bern 7 == 0. Proof. vm_compute. reflexivity. Qed.
Theorem bern8 : bern 8 == -1 # 30. Proof. vm_compute. reflexivity. Qed.
Theorem bern9 : bern 9 == 0. Proof. vm_compute. reflexivity. Qed.
Theorem bern10 : bern 10 == 5 # 66. Proof. vm_compute. reflexivity. Qed.
Theorem bern11 : bern 11 == 0. Proof. vm_compute. reflexivity. Qed.
Theorem bern12 : bern 12 == -691 # 2730. Proof. vm_compute. reflexivity. Qed.

(* Item 17 fragment: odd Bernoulli vanish for 3,5,7,9,11. *)
Theorem odd_bern_vanish_3_to_11 :
  bern 3 == 0 /\ bern 5 == 0 /\ bern 7 == 0 /\ bern 9 == 0 /\ bern 11 == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Rational zeta at negative odds: ζQ(1-2k) := -B_{2k}/(2k)           *)
(* ------------------------------------------------------------------ *)
Definition zetaQ_neg (k : nat) : Q :=
  - bern (2 * k) / inject_Z (Z.of_nat (2 * k)).

Theorem zetaQ_neg1 : zetaQ_neg 1 == -1 # 12.
Proof. vm_compute. reflexivity. Qed.
Theorem zetaQ_neg3 : zetaQ_neg 2 == 1 # 120.
Proof. vm_compute. reflexivity. Qed.
Theorem zetaQ_neg5 : zetaQ_neg 3 == -1 # 252.
Proof. vm_compute. reflexivity. Qed.
Theorem zetaQ_neg7 : zetaQ_neg 4 == 1 # 240.
Proof. vm_compute. reflexivity. Qed.
Theorem zetaQ_neg9 : zetaQ_neg 5 == -1 # 132.
Proof. vm_compute. reflexivity. Qed.
Theorem zetaQ_neg11 : zetaQ_neg 6 == 691 # 32760.
Proof. vm_compute. reflexivity. Qed.

(* Eisenstein constants 2 / ζQ(1-2k) = -4k / B_{2k} *)
Definition eis_from_zetaQ (k : nat) : Q := 2 / zetaQ_neg k.

Theorem eis_k1 : eis_from_zetaQ 1 == -24. Proof. vm_compute. reflexivity. Qed.
Theorem eis_k2 : eis_from_zetaQ 2 == 240. Proof. vm_compute. reflexivity. Qed.
Theorem eis_k3 : eis_from_zetaQ 3 == -504. Proof. vm_compute. reflexivity. Qed.
Theorem eis_k6 : eis_from_zetaQ 6 == 65520 # 691. Proof. vm_compute. reflexivity. Qed.

Definition eis_weight (w : nat) : Q :=
  - inject_Z (2 * Z.of_nat w) / bern w.

Theorem eis_E2 : eis_weight 2 == -24. Proof. vm_compute. reflexivity. Qed.
Theorem eis_E4 : eis_weight 4 == 240. Proof. vm_compute. reflexivity. Qed.
Theorem eis_E6 : eis_weight 6 == -504. Proof. vm_compute. reflexivity. Qed.
Theorem eis_E12 : eis_weight 12 == 65520 # 691. Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Item 41: 240 ζ(4)/π^4 = 2^4 / 3! as rationals                     *)
(* Using the classical identity ζ(4)=π^4/90 only as a Q-skeleton.    *)
(* ------------------------------------------------------------------ *)
Theorem item41_rational :
  inject_Z 240 / inject_Z 90 == inject_Z (Z.pow 2 4) / inject_Z 6
  /\ inject_Z 240 / inject_Z 90 == 8 # 3.
Proof. split; vm_compute; reflexivity. Qed.

(* Item 42: 65520/691 * ζ(12)/π^12 = 2^12 / 11! *)
(* Using ζ(12)=π^12 * 691 / 638512875 as a Q-skeleton. *)
Theorem item42_rational :
  inject_Z 65520 / inject_Z 638512875
    == inject_Z (Z.pow 2 12) / inject_Z 39916800
  /\ inject_Z 65520 / inject_Z 638512875 == 16 # 155925.
Proof. split; vm_compute; reflexivity. Qed.

(* Item 96: (s-1)/12 = -(s-1) ζQ(-1) *)
Theorem item96_palindrome :
  forall s : Q, (s - 1) / 12 == - (s - 1) * zetaQ_neg 1.
Proof. intros s. rewrite zetaQ_neg1. field. Qed.

(* Item 40 husk *)
Theorem item40_husk : inject_Z 240 / inject_Z 60 == inject_Z 4.
Proof. vm_compute. reflexivity. Qed.

(* Item 35: ζ(0)L(0,χ_{-4}) arithmetic and -h/w for Q(i) *)
Theorem item35_arith :
  (-1 # 2) * (1 # 2) == -1 # 4
  /\ - inject_Z 1 / inject_Z 4 == -1 # 4.
Proof. split; vm_compute; reflexivity. Qed.

(* Item 81: prefactor s(s-1) is palindromic *)
Theorem item81_prefactor :
  forall s : Q, s * (s - 1) == (1 - s) * ((1 - s) - 1).
Proof. intros s. ring. Qed.

(* Item 17 poles of Γ(s/2): s/2 = -k ↔ s = -2k *)
Theorem item17_poles :
  forall s k : Q, s / 2 == - k <-> s == - (2 * k).
Proof. intros s k. split; intros H; field_simplify in H; exact H. Qed.

(* ------------------------------------------------------------------ *)
(* Item 22: rational skeleton of Γ(1/2-k)/√π                         *)
(* F(k) = (-4)^k k! / (2k)! , F(k+1) = -2/(2k+1) F(k)                 *)
(* ------------------------------------------------------------------ *)
Fixpoint factZ (n : nat) : Z :=
  match n with
  | O => 1%Z
  | S n' => (Z.of_nat (S n') * factZ n')%Z
  end.

Definition Fcoeff (k : nat) : Q :=
  inject_Z (Z.pow (-4)%Z (Z.of_nat k) * factZ k) / inject_Z (factZ (2 * k)).

Theorem Fcoeff_0 : Fcoeff 0 == 1. Proof. vm_compute. reflexivity. Qed.
Theorem Fcoeff_1 : Fcoeff 1 == -2. Proof. vm_compute. reflexivity. Qed.
Theorem Fcoeff_2 : Fcoeff 2 == 4 # 3. Proof. vm_compute. reflexivity. Qed.
Theorem Fcoeff_3 : Fcoeff 3 == -8 # 15. Proof. vm_compute. reflexivity. Qed.
Theorem Fcoeff_4 : Fcoeff 4 == 16 # 105. Proof. vm_compute. reflexivity. Qed.
Theorem Fcoeff_5 : Fcoeff 5 == -32 # 945. Proof. vm_compute. reflexivity. Qed.

Theorem Fcoeff_rec_0_to_4 :
  Fcoeff 1 == (-2 / 1) * Fcoeff 0
  /\ Fcoeff 2 == (-2 / 3) * Fcoeff 1
  /\ Fcoeff 3 == (-2 / 5) * Fcoeff 2
  /\ Fcoeff 4 == (-2 / 7) * Fcoeff 3
  /\ Fcoeff 5 == (-2 / 9) * Fcoeff 4.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Item 2: λ1 term = 1/ρ                                              *)
(* ------------------------------------------------------------------ *)
Theorem item2_lambda1_term :
  forall r : Q, ~ r == 0 -> 1 - (1 - 1 / r) == 1 / r.
Proof. intros r Hz. field. exact Hz. Qed.

(* ------------------------------------------------------------------ *)
(* Item 6 pair weight over Q                                          *)
(* ------------------------------------------------------------------ *)
Definition pair_lhs (b g : Q) : Q :=
  (1 - 2 * b) / (b * b + g * g)
  + (2 * b - 1) / ((1 - b) * (1 - b) + g * g).

Definition pair_rhs (b g : Q) : Q :=
  (1 - 2 * b) * (1 - 2 * b)
  / ((b * b + g * g) * ((1 - b) * (1 - b) + g * g)).

Theorem item6_pair_identity :
  forall b g : Q,
    ~ (b * b + g * g) == 0 ->
    ~ ((1 - b) * (1 - b) + g * g) == 0 ->
    pair_lhs b g == pair_rhs b g.
Proof.
  intros b g H1 H2. unfold pair_lhs, pair_rhs. field. split; assumption.
Qed.

Theorem item6_vanishes_on_the_line :
  forall g : Q,
    ~ ((1 # 2) * (1 # 2) + g * g) == 0 ->
    pair_lhs (1 # 2) g == 0.
Proof.
  intros g H. unfold pair_lhs. field. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* Item 8 on the critical line, as a Q-identity in γ                  *)
(* Re(ρ^{-2}) for ρ = 1/2 + iγ written without i:                     *)
(*   (1/4 - γ²) / (1/4 + γ²)²                                          *)
(* two-zero sum = 2(1/4-γ²)/(1/4+γ²)²                                 *)
(* ------------------------------------------------------------------ *)
Definition re_inv_sq (g : Q) : Q :=
  ((1 # 4) - g * g) / ((1 # 4) + g * g) * (1 / ((1 # 4) + g * g)).

Theorem item8_two_zero_form :
  forall g : Q,
    ~ ((1 # 4) + g * g) == 0 ->
    re_inv_sq g + re_inv_sq g
      == inject_Z 2 * ((1 # 4) - g * g)
           / ((1 # 4) + g * g) / ((1 # 4) + g * g).
Proof. intros g H. unfold re_inv_sq. field. exact H. Qed.

(* ------------------------------------------------------------------ *)
(* Item 45: Jacobian / modulus identity over Q                        *)
(* ------------------------------------------------------------------ *)
Theorem item45_mod_sq_sq :
  forall x y : Q,
    (x * x - y * y) * (x * x - y * y) + (2 * x * y) * (2 * x * y)
      == (x * x + y * y) * (x * x + y * y).
Proof. intros x y. ring. Qed.

(* ------------------------------------------------------------------ *)
(* Item 99: σ_k = 1 * n^k as a finite divisor sum                     *)
(* ------------------------------------------------------------------ *)
Fixpoint sum_upto (n : nat) (f : nat -> Z) : Z :=
  match n with
  | O => 0%Z
  | S n' => (sum_upto n' f + f (S n'))%Z
  end.

Definition divides_nat (d n : nat) : bool :=
  match d with
  | O => false
  | S _ => Nat.eqb (Nat.modulo n d) 0
  end.

Definition sigma_k (k n : nat) : Z :=
  sum_upto n (fun d =>
    if divides_nat d n then Z.pow (Z.of_nat d) (Z.of_nat k) else 0%Z).

Theorem sigma3_1 : sigma_k 3 1 = 1%Z. Proof. vm_compute. reflexivity. Qed.
Theorem sigma3_2 : sigma_k 3 2 = 9%Z. Proof. vm_compute. reflexivity. Qed.
Theorem sigma3_3 : sigma_k 3 3 = 28%Z. Proof. vm_compute. reflexivity. Qed.
Theorem sigma3_4 : sigma_k 3 4 = 73%Z. Proof. vm_compute. reflexivity. Qed.
Theorem sigma3_5 : sigma_k 3 5 = 126%Z. Proof. vm_compute. reflexivity. Qed.
Theorem sigma3_6 : sigma_k 3 6 = 252%Z. Proof. vm_compute. reflexivity. Qed.
Theorem sigma3_7 : sigma_k 3 7 = 344%Z. Proof. vm_compute. reflexivity. Qed.
Theorem sigma3_8 : sigma_k 3 8 = 585%Z. Proof. vm_compute. reflexivity. Qed.

Theorem sigma1_12 : sigma_k 1 12 = 28%Z. Proof. vm_compute. reflexivity. Qed.
Theorem sigma1_1 : sigma_k 1 1 = 1%Z. Proof. vm_compute. reflexivity. Qed.
Theorem sigma1_2 : sigma_k 1 2 = 3%Z. Proof. vm_compute. reflexivity. Qed.
Theorem sigma1_5040 : sigma_k 1 5040 = 19344%Z. Proof. vm_compute. reflexivity. Qed.

(* convolution form: σ_k(n) = Σ_{ab=n} b^k *)
Definition sigma_k_conv (k n : nat) : Z :=
  sum_upto n (fun a =>
    if divides_nat a n
    then Z.pow (Z.of_nat (Nat.div n a)) (Z.of_nat k)
    else 0%Z).

Theorem sigma3_conv_eq_1_to_8 :
  sigma_k 3 1 = sigma_k_conv 3 1
  /\ sigma_k 3 2 = sigma_k_conv 3 2
  /\ sigma_k 3 3 = sigma_k_conv 3 3
  /\ sigma_k 3 4 = sigma_k_conv 3 4
  /\ sigma_k 3 5 = sigma_k_conv 3 5
  /\ sigma_k 3 6 = sigma_k_conv 3 6
  /\ sigma_k 3 7 = sigma_k_conv 3 7
  /\ sigma_k 3 8 = sigma_k_conv 3 8.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* Harmonic numbers as Q, item 21 data *)
Fixpoint harm (n : nat) : Q :=
  match n with
  | O => 0
  | S n' => harm n' + 1 / inject_Z (Z.of_nat (S n'))
  end.

Theorem harm1 : harm 1 == 1. Proof. vm_compute. reflexivity. Qed.
Theorem harm2 : harm 2 == 3 # 2. Proof. vm_compute. reflexivity. Qed.
Theorem harm12 : harm 12 == 86021 # 27720. Proof. vm_compute. reflexivity. Qed.

(* Item 21 at n=1: σ(1)=1 ≤ H_1=1 *)
Theorem item21_n1 : (sigma_k 1 1 <= 1)%Z /\ harm 1 == 1.
Proof. split. vm_compute. lia. apply harm1. Qed.

(* ------------------------------------------------------------------ *)
(* Item 104: Hasse bound is the integer inequality a² ≤ 4p            *)
(* ------------------------------------------------------------------ *)
Theorem item104_hasse_Z :
  forall a p : Z, (a * a <= 4 * p)%Z <-> (a * a - 4 * p <= 0)%Z.
Proof. intros a p. lia. Qed.

(* p|a and a^2<=4p, p>=5 => a=0  (removed item 49, recorded again) *)
Theorem item104_divides_vanishes :
  forall a p : Z,
    (5 <= p)%Z ->
    (a * a <= 4 * p)%Z ->
    (a mod p = 0)%Z ->
    a = 0%Z.
Proof.
  intros a p Hp Hsq Hdiv.
  assert (exists k, a = (k * p)%Z) as [k Hk].
  { exists (a / p)%Z. pose proof (Z.div_mod a p). lia. }
  rewrite Hk in Hsq.
  assert (k = 0%Z) by nia.
  subst. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* E8 counts and Leech kissing number as integer arithmetic           *)
(* ------------------------------------------------------------------ *)
Theorem e8_root_count :
  (4 * 28 = 112)%Z /\ (Z.pow 2 7 = 128)%Z /\ (112 + 128 = 240)%Z.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* C(8,2)=28 *)
Theorem binom_8_2 : (8 * 7 / 2 = 28)%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem e4_q1_is_root_count : (240 = 240)%Z.
Proof. reflexivity. Qed.

Theorem e43_q1 : (3 * 240 = 720)%Z.
Proof. vm_compute. reflexivity. Qed.

(* [q^2] E4^3 = 3*240*σ3(2) + 3*240^2 = 6480 + 172800 = 179280 *)
Theorem e43_q2 : (3 * 240 * 9 + 3 * 240 * 240 = 179280)%Z.
Proof. vm_compute. reflexivity. Qed.

(* Leech: [q^2](E4^3 - 720 Δ) = 179280 - 720*(-24) = 196560 *)
Theorem leech_kissing :
  (179280 - 720 * (-24) = 196560)%Z.
Proof. vm_compute. reflexivity. Qed.

(* moonshine rationals, AQMT bands, no claim of meaning *)
Definition r1 : Q := 744 # 196884.
Definition r2 : Q := 196884 # 21493760.
Definition r3 : Q := 196560 # 196884.

Theorem r1_reduced : r1 == 62 # 16407.
Proof. vm_compute. reflexivity. Qed.

Theorem band_ratio_d3_over_d2 :
  r3 / (10 * r2) == 977966080 # 89729883.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Divided difference of x^3 is a+b+c (Triples)                       *)
(* ------------------------------------------------------------------ *)
Definition dd3 (a b c : Q) : Q :=
  a*a*a / ((a-b)*(a-c)) + b*b*b / ((b-a)*(b-c)) + c*c*c / ((c-a)*(c-b)).

Theorem dd3_is_sum :
  forall a b c : Q,
    ~ a == b -> ~ b == c -> ~ c == a ->
    dd3 a b c == a + b + c.
Proof. intros a b c Hab Hbc Hca. unfold dd3. field; repeat split; auto. Qed.

Definition gram3 (a b c : Q) : Q := 1 + 2*a*b*c - a*a - b*b - c*c.

Theorem gram_equal :
  forall t : Q, gram3 t t t == (1 - t) * (1 - t) * (1 + 2 * t).
Proof. intros t. unfold gram3. ring. Qed.

(* ------------------------------------------------------------------ *)
(* Item 27 skeleton: c1 = 1/ζ(2) - 1/ζ(4) with classical even values  *)
(* written as rationals times inverse even powers of an indeterminate *)
(* ------------------------------------------------------------------ *)
Definition c1_num_over_pi4 (pi2 : Q) : Q := 6 * pi2 - 90.

Theorem item27_c1_numerator :
  forall p2 : Q, c1_num_over_pi4 p2 == 6 * (p2 - 15).
Proof. intros p2. unfold c1_num_over_pi4. ring. Qed.

(* ------------------------------------------------------------------ *)
(* Combined ledger matching the inventory husks                       *)
(* ------------------------------------------------------------------ *)
Theorem inventory_Q_ledger :
    bern 12 == -691 # 2730
  /\ zetaQ_neg 1 == -1 # 12
  /\ zetaQ_neg 6 == 691 # 32760
  /\ eis_from_zetaQ 1 == -24
  /\ eis_from_zetaQ 2 == 240
  /\ eis_from_zetaQ 3 == -504
  /\ eis_from_zetaQ 6 == 65520 # 691
  /\ inject_Z 240 / inject_Z 90 == 8 # 3
  /\ inject_Z 65520 / inject_Z 638512875 == 16 # 155925
  /\ Fcoeff 1 == -2
  /\ Fcoeff 2 == 4 # 3
  /\ Fcoeff 3 == -8 # 15
  /\ Fcoeff 4 == 16 # 105
  /\ Fcoeff 5 == -32 # 945
  /\ (112 + 128 = 240)%Z
  /\ (179280 - 720 * (-24) = 196560)%Z
  /\ sigma_k 1 5040 = 19344%Z
  /\ harm 12 == 86021 # 27720.
Proof. repeat split; vm_compute; reflexivity. Qed.
