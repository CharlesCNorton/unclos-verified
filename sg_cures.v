(* Cures for sovereign_geometer.v, built integratively on the compiled module.
   Installment 1: the asin bound kernel (eliminates two Admitted lemmas). *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
Require Import sovereign_geometer.

Open Scope R_scope.

(* Foundation: sin has the order-3 Taylor lower bound on [0,1).
   sin u >= u - u^3/6.  Derived from the standard library SIN bracket plus the
   positivity of the degree-5/7 remainder already proved in the development. *)
Lemma sin_lower_cubic : forall u, 0 <= u -> u < 1 -> sin u >= u - u * u * u / 6.
Proof.
  intros u Hge Hlt1.
  destruct (Req_dec u 0) as [Hz | Hnz]; [subst u; rewrite sin_0; lra |].
  assert (Hupos : 0 < u) by lra.
  assert (HuPI : u <= PI) by (pose proof PI_gt_3; lra).
  pose proof (proj1 (SIN u Hge HuPI)) as Hlb.   (* sin_lb u <= sin u *)
  pose proof (taylor_sin_higher_terms_pos u Hupos Hlt1) as Hhi.
  assert (Hsum : sin_lb u =
    (u - u * u * u / 6) +
    (u * u * u * u * u / 120 - u * u * u * u * u * u * u / 5040)).
  { unfold sin_lb, sin_approx, sin_term. simpl. field. }
  lra.
Qed.

(* CURE (admit 2 of 4): asin x <= x + x^3 for x in [0, 1/3].
   Stated exactly as the Admitted lemma asin_upper_bound_small in the file. *)
Lemma cure_asin_upper_bound_small :
  forall x, 0 <= x -> x <= 1/3 -> asin x <= x + x * x * x.
Proof.
  intros x Hge Hle.
  destruct (Req_dec x 0) as [Hz | Hnz]; [subst x; rewrite asin_0; lra |].
  assert (Hxpos : 0 < x) by lra.
  set (u := x + x * x * x).
  assert (Hu_ge : 0 <= u) by (unfold u; nra).
  assert (Hu_lt1 : u < 1) by (unfold u; nra).
  (* x <= sin u *)
  assert (Hsin_lb : sin u >= u - u * u * u / 6) by (apply sin_lower_cubic; assumption).
  assert (Hx2 : x * x <= 1/9) by nra.
  assert (Hx4 : x * x * x * x <= 1/81) by nra.
  assert (Hx6 : x * x * x * x * x * x <= 1/729) by nra.
  assert (Hcube : (1 + x*x) * (1 + x*x) * (1 + x*x) <= 6) by nra.
  assert (Hx3_nn : 0 <= x * x * x) by nra.
  assert (Hprod_nn : 0 <= x * x * x * (6 - (1 + x*x) * (1 + x*x) * (1 + x*x))) by nra.
  assert (Hcubic : u - u * u * u / 6 >= x).
  { assert (Hid : u - u * u * u / 6 - x =
                  x * x * x * (6 - (1 + x*x) * (1 + x*x) * (1 + x*x)) / 6)
      by (unfold u; field).
    lra. }
  assert (Hx_le_sin : x <= sin u) by lra.
  (* lift through asin *)
  assert (Hsin_bnd : -1 <= sin u <= 1) by (pose proof (SIN_bound u); lra).
  assert (Hx_bnd : -1 <= x <= 1) by lra.
  assert (Hmono : asin x <= asin (sin u)).
  { apply asin_increasing; [exact Hx_bnd | exact Hsin_bnd | exact Hx_le_sin]. }
  assert (Hasin_sin : asin (sin u) = u).
  { apply asin_sin. pose proof PI_gt_3. unfold u in *. split; nra. }
  rewrite Hasin_sin in Hmono. unfold u in Hmono. exact Hmono.
Qed.

(* CURE (admit 3 of 4): (asin (sqrt a))^2 <= 2a for a in [0, 1/9].
   Stated exactly as the Admitted lemma Rsqr_asin_sqrt_bound in the file. *)
Lemma cure_Rsqr_asin_sqrt_bound :
  forall a, 0 <= a -> a <= 1/9 -> Rsqr (asin (sqrt a)) <= a * 2.
Proof.
  intros a Hge Hle.
  destruct (Req_dec a 0) as [Hz | Hnz].
  { subst a. rewrite sqrt_0, asin_0. unfold Rsqr. lra. }
  assert (Hapos : 0 < a) by lra.
  assert (Hs_nonneg : 0 <= sqrt a) by apply sqrt_pos.
  assert (Hss : sqrt a * sqrt a = a) by (apply sqrt_sqrt; lra).
  (* sqrt a <= 1/3 *)
  assert (Hs_le : sqrt a <= 1/3).
  { assert (Hmono : sqrt a <= sqrt (1/9)) by (apply sqrt_le_1_alt; lra).
    replace (1/9) with (Rsqr (1/3)) in Hmono by (unfold Rsqr; lra).
    rewrite sqrt_Rsqr in Hmono by lra. exact Hmono. }
  (* asin bound on sqrt a *)
  pose proof (cure_asin_upper_bound_small (sqrt a) Hs_nonneg Hs_le) as Hasin_ub.
  assert (Hasin_nonneg : 0 <= asin (sqrt a)).
  { apply asin_nonneg_on_0_1. split; [exact Hs_nonneg | lra]. }
  set (R := sqrt a + sqrt a * sqrt a * sqrt a) in *.
  assert (HR_nonneg : 0 <= R) by (unfold R; nra).
  (* square the inequality 0 <= asin(sqrt a) <= R *)
  assert (Hsq : Rsqr (asin (sqrt a)) <= Rsqr R).
  { unfold Rsqr. nra. }
  (* Rsqr R <= 2a using sqrt a * sqrt a = a *)
  assert (HRsqr : Rsqr R <= a * 2).
  { unfold Rsqr, R.
    assert (HRR : (sqrt a + sqrt a * sqrt a * sqrt a) *
                  (sqrt a + sqrt a * sqrt a * sqrt a)
                  = a + 2 * (a * a) + a * a * a).
    { assert (Hexp : (sqrt a + sqrt a * sqrt a * sqrt a) *
                     (sqrt a + sqrt a * sqrt a * sqrt a)
                   = sqrt a * sqrt a
                     + 2 * (sqrt a * sqrt a * (sqrt a * sqrt a))
                     + sqrt a * sqrt a * (sqrt a * sqrt a) * (sqrt a * sqrt a)) by ring.
      rewrite Hexp, !Hss. ring. }
    rewrite HRR. nra. }
  lra.
Qed.
