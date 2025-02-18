From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Implicit Type p q r : bool.
Implicit Type m n i j k : nat.
(**
* Part 1: Booleans and Natural numbers

 ** Exercise 1:
    - use no lemma to prove the following statement
*)
Lemma orbC p q : p || q = q || p.
Proof. by case: p; case: q. Qed.

(**
** Exercise 2:
   - look up what [==>] is check if there are relevant views
   - prove that as you like
*)
Lemma Pierce p q : ((p ==> q) ==> p) ==> p.
Proof.
  apply /implyP.
  move=> /implyP H.
  apply: (H).
  (* we're trying to prove constructively something
  that isn't contructively provable. Oops! *)
  Restart.
  by case: p; case q.
Qed.

(**
** Exercise 3:
    - look for lemmas supporting contrapositive reasoning
*)
Lemma bool_gimmics1 i : i != i.-1 -> i != 0.
Proof.
  case: (eqVneq i 0).
  move=> ->.
  by apply /implyP.
  done.
  Restart.
  Print contra_neq.
  by apply /contra_neq => ->.
  Restart.
  apply /implyP.
  rewrite Bool.implb_contrapositive.
  by case: i.
Qed.

(**
** Exercise 4:
    - what is [(+)] ?
    - find the right view to prove this statement
    - now find another proof without the view
*)
Lemma find_me p q :  (~~ p) = q -> p (+) q.
Proof.
  move=> /addbP.
  apply.
  Restart.
  rewrite -negb_eqb.
  move=>/eqP.
  apply /implyP.
  by case: p; case: q.
  Restart.
  by case: p; case: q.

Qed.

(**
** Exercise 5:
   - it helps to find out what is behind [./2] and [.*2] in order to [Search]
   - any proof would do, but there is one not using [implyP]
*)
Print doubleK.
Print half_double.
Lemma view_gimmics1 p a b : p -> (p ==> (a == b.*2)) -> a./2 = b.
Proof.
  move=> -> /= /eqP ->. 
  apply half_double.
  Restart.
  case: p.
  - move=> _.
    rewrite implyTb.
    move=> /eqP ->.
    apply half_double.
  - by [].
Qed.

(**
** Exercise 6:
    - prove that using [case:]
    - then prove that without using case:
*)
Search (_ == _) "eqb".
Lemma bool_gimmics2 p q r : ~~ p && (r == q) -> q ==> (p || r).
Proof.
  move=> /andP [] /negPf -> /= /eqP ->.
  by apply /implyP.
  Restart.
  move=> /andP [_ /eqP ->].
  apply /implyP => ->.
  apply orbT.
  Restart.
  by case: p; case: q; case: r.
Qed.

(**
** Exercise 7:
    - look up the definition of [iter]
    - prove this statement by induction
*)
Print iter.
Lemma iterSr A n (f : A -> A) x : iter n.+1 f x = iter n f (f x).
Proof.
  by elim: n => [//| n /= <- /=].
Qed.

(**
** Exercise 8:
    - look up the definition of [iter] (note there is an accumulator varying
      during recursion)
    - prove the following statement by induction
*)
Print subnS.
Lemma iter_predn m n : iter n predn m = m - n.
Proof.
  elim: n => [ /= | n /= ->].
  by rewrite subn0.
  by rewrite subnS.
Qed.

(**
** Exercise 9:
   - the only tactics allowed are [rewrite] and [by]
   - use [Search] to find the relevant lemmas (all are good but for
     [ltn_neqAle]) or browse the #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.ssrnat.html">online doc</a>#
   - proof sketch:
<<
        m < n = ~~ (n <= m)
              = ~~ (n == m || n < m)
              = n != m && ~~ (n < m)
              = ...
>>
*)
Lemma ltn_neqAle m n : (m < n) = (m != n) && (m <= n).
Proof.
  rewrite eqn.
Admitted.

(**
** Exercise 10:
  - there is no need to prove [reflect] with [iffP]: here just use [rewrite] and [apply]
  - check out the definitions and theory of [leq] and [maxn]
  - proof sketch:
<<
   n <= m = n - m == 0
          = m + n - m == m + 0
          = maxn m n == m
>>
*)
Lemma maxn_idPl m n : reflect (maxn m n = m) (m >= n).
Proof.

Admitted.
