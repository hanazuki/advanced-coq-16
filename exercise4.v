From mathcomp Require Import all_ssreflect.

Section Kosaraju.

  Variable T: finType.
  Implicit Types s: {set T}.
  Implicit Types l: seq T.
  Implicit Types A B C: pred T.
  Implicit Types x y z: T.

  Section Lib.

    Lemma disjoint_setU s1 s2 A: [disjoint s1 :|: s2 & A] = [disjoint s1 & A] && [disjoint s2 & A].
      apply/pred0P.
      case: ifP.
      - move/andP => [/pred0P D1 /pred0P D2] x /=.
        rewrite in_setU.
        have: (x \in s1) && (x \in A) = false by exact: D1.
        have: (x \in s2) && (x \in A) = false by exact: D2.
        by case: (x \in A); case: (x \in s1); case: (x \in s2).
      - move/andP => I H; apply: I.
        split; apply/pred0P => x; have := H x => //=;
        rewrite in_setU;
        by case: (x \in A); case: (x \in s1); case: (x \in s2).
    Qed.

    Lemma disjoint_predsetC A s: [disjoint A & s] = [disjoint s & A].
      apply/pred0P; case: ifP => /pred0P => [H|I H]; last apply: I;
      move => x /=; rewrite andbC; exact: H.
    Qed.

    Lemma disjoint_setUr s1 s2 A: [disjoint A & s1 :|: s2] = [disjoint A & s1] && [disjoint A & s2].
      rewrite !disjoint_predsetC.
      exact: disjoint_setU.
    Qed.

    Lemma disjoint_catr l1 l2 A: [disjoint A & l1 ++ l2] = [disjoint A & l1] && [disjoint A & l2].
      apply/pred0P; case: ifP => /andP.
      - move => [/pred0P D1 /pred0P D2] x /=.
        rewrite mem_cat andb_orr.
        have [/andP H1]: (x \in A) && (x \in l1) = false by exact: D1.
        have [/andP H2]: (x \in A) && (x \in l2) = false by exact: D2.
        apply/orP; case; move/andP => //.
      - move => I H; apply: I.
        split; apply/pred0P => x /=.
        all: have: (x \in A) && ((x \in l1 ++ l2)) = false by apply: H.
        all: rewrite mem_cat andb_orr; move/orP => H0; apply/negP => H1; apply: H0; by [left|right].
    Qed.

    Lemma disjoint_set1 x A: [disjoint [set x] & A] = (x \notin A).
      apply/pred0P; case: ifP.
      - move => /negP H y /=.
        rewrite in_set1.
        apply/andP; move => [/eqP -> H1].
        exact: H.
      - move => /negP H H0.
        apply: H => H.
        have /negP H1: (x \in [set x]) && (x \in A) = false by exact: H0.
        apply: H1.
        apply/andP.
        by rewrite in_set1.
    Qed.

    Lemma disjoint_setU1 x s A: [disjoint x |: s & A] = (x \notin A) && [disjoint s & A].
      apply/pred0P/andP.
      - move => H.
        split.
        -- apply/negP => H0.
           move: H => /(_ x) /= /andP; apply.
           split => //; exact: setU11.
        -- apply/pred0P => y /=.
           apply/andP; move => [H0 H1].
           move: H => /(_ y) /= /andP; apply.
           split => //; exact: setU1r.
      - move => [/negP H0 /pred0P H1] y /=.
        rewrite in_setU1.
        apply/andP; move => [/orP H2 H3].
        move: H1 => /(_ y) /= /andP; apply.
        split; case: H2 => // /eqP H.
        subst; contradiction.
    Qed.

    Lemma disjoint_setU1r x s A: [disjoint A & x |: s] = (x \notin A) && [disjoint A & s].
      rewrite !disjoint_predsetC.
      exact: disjoint_setU1.
    Qed.

    Lemma disjoint_consr x l A: [disjoint A & x :: l] = (x \notin A) && [disjoint A & l].
      apply/pred0P/andP.
      - move => H.
        split.
        -- apply/negP => H0.
           move: H => /(_ x) /= /andP; apply.
           split => //; exact: mem_head.
        -- apply/pred0P; move => y /=.
           apply/andP; move => [H0 H1].
           move: H => /(_ y) /= /andP; apply.
           split => //; exact: mem_behead.
      - move => [/negP H0 /pred0P H1] y /=.
        rewrite in_cons.
        apply/andP; move => [H2 /orP H3].
        move: H1 => /(_ y) /= /andP; apply.
        split; case: H3 => // /eqP H.
        subst; contradiction.
    Qed.

    Lemma in_subset A B x: A \subset B -> x \in A -> x \in B.
      rewrite subsetE => /pred0P /(_ x)/= /andP.
      rewrite /(x \notin _).
        by case: (x \in A); case: (x \in B); tauto.
    Qed.

    Lemma disjoint_transr A B C: B \subset C -> [disjoint A & C] -> [disjoint A & B].
      move => H /pred0P D.
      apply/pred0P; move => x /=.
      apply/andP; move => [H0 H1].
      move: D => /(_ x) /= /andP; apply.
      split => //.
      exact: (in_subset B C x).
    Qed.
  End Lib.

End Kosaraju.

