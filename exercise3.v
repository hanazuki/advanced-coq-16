From mathcomp Require Import all_ssreflect.

Definition onext n (x: 'I_n): 'I_n.
  move: x => [i Hi].
  suff: (if i.+1 < n then i.+1 else 0) < n; first exact: Ordinal.
  case: ifP => // _.
  by apply: (@leq_ltn_trans i 0 n).
Defined.

Definition injectiveb {aT: finType} {rT: eqType} (f: aT -> rT): bool :=
  uniq (map f (enum aT)).

Lemma injectiveP (aT: finType) (rT: eqType) (f: aT -> rT): reflect (injective f) (injectiveb f).
  rewrite /injectiveb /injective.
  apply: (iffP idP).
  - give_up.
  - give_up.
Admitted.

Lemma gauss_ex: forall n, (\sum_(i < n) i).*2 = n * n.-1.
  elim => // [|n IH].
  - by rewrite big_ord0.
  - rewrite big_ord_recr /= doubleD {}IH.
    case: n => //= n.
    by rewrite -muln2; ring.
Qed.

Lemma sum_odd1: forall n, \sum_(i < n) (2*i + 1) = n^2.
  elim => // [|n IH].
  - by rewrite big_ord0.
  - by rewrite big_ord_recr /= {}IH; ring.
Qed.

Lemma sum_exp: forall x n, 0 < x -> x ^ n.+1 - 1 = (x - 1) * \sum_(i < n.+1) x ^ i.
  case => //= x n _.
  rewrite big_ord_recr /= [in RHS]subn1 succnK mulnDr.
  elim: n => [|n IH].
  - by rewrite big_ord0 expn1 expn0 subn1 succnK; ring.
  - rewrite big_ord_recr expnSr /=.
    have <-: x.+1 ^ n.+1 - 1 + 1 = x.+1 ^ n.+1.
    -- rewrite subn1 addn1.
       apply: prednK.
       rewrite expn_gt0.
       by apply/orP; left.
    rewrite {}IH.
    set s := \sum_(i < n) x.+1 ^ i.
    rewrite !mulnDl !mulnDr mul1n subn1.
    have <-: forall a b, a + b = (a + b.+1).-1.
    -- elim => //= a IHa b.
       rewrite -addn1 -addnAC {}IHa addn1.
       apply: prednK.
       apply: (@leq_ltn_trans a) => //=.
       rewrite -{1}(addn0 a).
       exact: ltn_add2l.
    by ring.
Qed.

Lemma bound_space: forall n, \sum_(i < n) i ^ 2 <= n ^ 3.
  move=> n.
  have <-: \sum_(i < n) n ^ 2 = n ^ 3.
  - rewrite big_const_ord [RHS]expnS.
    elim: {1 3}n => //= m ->.
    by rewrite -[in m.+1]addn1 mulnDl; ring.
  have: n <= n => //.
  elim: {-2 12}n => [|m IH m_ltn_n].
  - by rewrite !big_ord0.
  - have m_leq_n: m <= n.
    by rewrite leq_eqVlt; apply/orP; right.
    have IH0 := IH m_leq_n.
    rewrite !big_ord_recr /=.
    rewrite (@leq_trans (\sum_(i < m) n ^ 2 + m ^2)) //.
    -- by rewrite leq_add2r.
    -- by rewrite leq_add2l leq_sqr.
Qed.

Section cex.
  Variable op2 : nat -> nat -> nat.
  Hypothesis op2n0 : right_id 0 op2.
  Hypothesis op20n : left_id 0 op2.
  Hypothesis op2A : associative op2.
  Hypothesis op2add : forall x y, op2 x y = x + y.

  Canonical Structure op2Mon : Monoid.law 0 :=
    Monoid.Law op2A op20n op2n0.

  Lemma ex_op2 : \big[op2/0]_(i < 3) i = 3.
    by rewrite !big_ord_recr big_ord0 /= !op2add.
  Qed.
End cex.
