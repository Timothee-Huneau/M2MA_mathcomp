(**
---
customTheme : "solarized"
slideNumber: true
title: "M2MA Mathcomp 1"
minScale: 0.2
width : 2000
height: 1250
---

<style type="text/css">
  .reveal p {
    text-align: left;
  }
  .diamond {
  text-align: center;
  }
  .reveal h4 {
    text-align: left;
  }
  .reveal h5 {
    text-align: left;
  }
  .reveal ul {
    display: block;
  }
  .reveal ol {
    display: block;
  }  
</style>

## Intro

---

### Objectives of the two next lectures


#### Give you quick access to the Mathematical Components library

- formalization techniques
- proof language
- familiarize with some theories

<div class="diamond">⋄</div>

<small>
Thanks to Yves Bertot, Laurence Rideau, Enrico Tassi and Laurent Thery for the contents.
Thanks to Emilio Jesús Gallego Arias for the `.mv` experience.
</small>

---

#### Program for the two lectures

1. An overview of mathcomp
2. More SSReflect tactics and style, with examples from basic libraries.
3. Applications to linear algebra in finite dimension and matrices
4. If time allows, some topology.

---

<!-- ### Disclaimer

#### Captatio benevolentiae (as would say [Enrico Tassi](https://www-sop.inria.fr/members/Enrico.Tassi/))

- I won't take comment on the syntax, I can give rationales, but I'm not responsible. :)
- it is not easy to appreciate the benefits on small examples, but we will try hard ;-)
- not enough time to explain everything, I'll focus on intuition rather than technical details

--- -->

### Resources

- Greatly inspired by Enrico Tassi's and Yves Bertot's lectures at [Math Comp School & Workshop - 2022.](https://mathcomp-schools.gitlabpages.inria.fr/2022-12-school/school)
- The [Cheat Sheet](https://www-sop.inria.fr/teams/marelle/MC-2022/cheatsheet.pdf) (various versions [here](https://math-comp.github.io/documentation.html#org3b59844)) and the [interactive cheat sheet](https://perso.crans.org/cohen/IRIF-mathcomp-2021/irif.cheat_sheet.html)
- The [Mathcomp Book](https://math-comp.github.io/mcb/) (needs to be updated to mathcomp v2) <center><br/><img src="images/cover-front-web.png"></image><br/></center> and the [documentation](https://math-comp.github.io/)

- The [SSReflect User Manual](https://coq.inria.fr/doc/v8.20/refman/proof-engine/ssreflect-proof-language.html)

---

Example setup of a file using the mathcomp library:
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup.
From mathcomp Require Import all_algebra all_solvable all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(**

<div class="diamond">⋄</div>

This setup is interactive using Vscode and Coq-lsp
*)
Lemma test : True. Proof. by []. Qed.
(**

---

## An overview of The Mathematical Components library

---

### Common features of Rocq/mathcomp and Lean/mathlib

- large, consistent, library organized as a programming language library (interfaces, overloading, naming conventions, ...)
- proof language tuned to the library recommended coding practices,
- contributions are reworked until they match the standards of the library,
- we strive to achieve as general results as possible (within time and technical limits).

---

### Main differences between Rocq/mathcomp and Lean/mathlib

- Mathcomp is 10 years older.
- It's not monolithic.
- Mathcomp "core packages" are formalized without axioms (fully constructive).
- Because of that there are some limitations to the generality of some statements (WIP).
- It relies on a specific proof language: SSReflect.
- It uses bundled structures instead of (semi-)unbundled classes..

The mathematical components library was used to formalize the
[Odd Order Theorem (a.k.a. Feit Thompson)](https://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_theorem), a 250 pages book.
Such proof amounts to 40k lines of Rocq scripts, on top of 120k lines of mathematical components. The library has been maintained for **18 years now**.

---


### "mathcomp core" consists of 6 packages:
  - [`mathcomp-ssreflect`](https://github.com/math-comp/math-comp/tree/mathcomp-2.2.0/mathcomp/ssreflect): bigops, sequences (lists) and tuples,
    natural number arithmetic, divisibility and primality,
    finite types and sets, quotients, equalities, orders.
  - [`mathcomp-fingroup`](https://github.com/math-comp/math-comp/tree/mathcomp-2.2.0/mathcomp/fingroup): basic finite group theory, group morphisms,
    permutations, actions and group quotients.
  - [`mathcomp-algebra`](https://github.com/math-comp/math-comp/tree/mathcomp-2.2.0/mathcomp/algebra): hierarchy of algebraic structures,
    integer arithmetic, Z/pZ and rational numbers,
    univariate polynomials, polynomial arithmetic and fraction fields,
    ring quotients, matrices and vector spaces.
  - [`mathcomp-solvable`](https://github.com/math-comp/math-comp/tree/mathcomp-2.2.0/mathcomp/solvable): advanced results in group theory, including
    Sylow's theorems and group series.
  - [`mathcomp-field`](https://github.com/math-comp/math-comp/tree/mathcomp-2.2.0/mathcomp/field): field theory, finite field theory,
    field extension theory, Galois theory and algebraic numbers.
  - [`mathcomp-character`](https://github.com/math-comp/math-comp/tree/mathcomp-2.2.0/mathcomp/character): character and representation theory.

---

### Extensions consists of more packages

  - [`mathcomp-zify`](https://github.com/math-comp/mczify): compatibility layer between mathcomp and lia tactics.
  - [`mathcomp-algebra-tactics`](https://github.com/math-comp/algebra-tactics): compatibility layer between mathcomp and ring/field tactics.
  - [`mathcomp-finmap`](https://github.com/math-comp/finmap): finite sets and finite maps.
  - [`mathcomp-real-closed`](https://github.com/math-comp/real-closed): theory of real closed fields and quantifier elimination.
  - [`mathcomp-multinomials`](https://github.com/math-comp/multinomials): multivariate polynomials.
  - [`mathcomp-classical`](https://github.com/math-comp/analysis/tree/1.5.0/classical): compatibility layer to do classical reasonning on top of mathcomp,
    theory of injective, surjective, bijective functions and cardinality.
  - [`mathcomp-analysis`](https://github.com/math-comp/analysis/tree/1.5.0/theories): topology, normed vector spaces, real functions,
    Bachman-Landau notations, infinite sequences,
    measure theory, Lebesgue measure and integral,
- [`Coq-Combi`](https://github.com/math-comp/Coq-Combi/tree/v1.0.0beta2): various theorems  in combinatorics
- [`Graph theory`](https://github.com/coq-community/graph-theory/tree/v0.9.5): various theorems in graph theory
- [`Monae`](https://github.com/affeldt-aist/monae): theorems about monads
- [`infotheo`](https://github.com/affeldt-aist/infotheo): information theory package
- [`coq-robot`](https://github.com/affeldt-aist/coq-robot): basics of robotics
- ...

---

### Searching information

Strategy:
1. Read the header of dedicated files in the library (e.g. [ssrnat](https://github.com/math-comp/math-comp/blob/mathcomp-2.2.0/mathcomp/ssreflect/ssrnat.v))
2. Use `Search` using a mix of:
  - patterns (e.g. `(_ + _)`) found in the header
	- constant names (use  `Locate` if necessary)
	- substrings of name using the [naming conventions](https://github.com/math-comp/math-comp/blob/master/CONTRIBUTING.md#naming-conventions-for-lemmas-non-exhaustive)
	- restrictions (e.g. `in algebra` etc)

<div class="diamond">⋄</div>

Examples:
*)
Add Search Blacklist "__canonical__" "__to__" "HB_unamed_mixin". (* HB bug #418 to fix *)

Search addn muln.
Search (_ * _.+1) inside ssrnat.
Search "add" "M".
Search "Gauss".
(**

---

##  An introduction to SSReflect tactics and style

with examples from basic libraries.

---

### The Small Scale approach

<div class="diamond">⋄</div>

#### Small scale tactics and theorems
  - Designed to **compress "Bookkeeping" steps**, i.e. on the fly moving,
    reordering, renaming, generalizing.
  - Emphasis on **combinators** and high-order functions
  - Tactics with a small and very-well **delimited effect**
  - The proof language eases **composability** by preserving strong invariants

<div class="diamond">⋄</div>

#### Booleans at the center of the methodolgy
  - when a concept is "computable", we represent it as a
    **computable** function, not as an inductive relation
  - Rocq knows how to compute, even symbolically, and computation is
    a very stable form of **automation**
  - Proposition as `bool` is a "simple" concept in CIC
    - EM holds
    - UIP holds
    - equivalence is equality

---

### Bookkeeping 101

---

#### Heap & Stack model of a Goal **vs** Curry-Howard

```
(* begining of heap *)
ci : Ti
…
dj := ej : Tj
…
Fk : Pk ci
…
(* end of heap *)
=================
forall (xl : Tl) (* top of the stack *)
…,
Pn xl ->         (* nth element of the stack *)
… ->
Conclusion       (* bottom of the stack = no more elements *)
```

---

### Handling the heap with tactics and tacticials

Handled via
- tacticial `=>`, with syntax `tactic=> names`,
  moves UP and names the first items from the stack to the heap,
- tacticial `:`, with syntax `tactic: names`,
  moves DOWN the named items as elements of the stack,
- all mathcomp tactics operate on the stack
  - `case`, `elim` and most intro items (`=> items`) operate on the top of the stack,
  - `apply`, `rewrite`, `have` operate on the whole stack
    in particular `apply: lem x y` should be read as: "apply `lem` after adding `x` and `y`` to the top of the stack".

---

### Example of bookkeeping

*)
Module GoalModel.
Section GoalModel.
Variables (Ti Tj Tl : Type) (ej : Tj).
Variables (Pk : Ti -> Type) (Pn : Tl -> Type).
Variables (Conclusion : Ti -> Tj -> Tl -> Type).

Lemma goal_model_example (ci : Ti) (dj : Tj := ej) (Fk : Pk ci) :
  forall (xl : Tl), Pn xl -> Conclusion ci dj xl.
Proof.
move=> xl pnxl.
Fail move: xl.
move: ci Fk.
Abort.
End GoalModel.
End GoalModel.
(**

---

#### Giving arguments to tactics


- Tatics `case`, `elim`, `apply` are all overloaded to respect this invariant.

- Using them with arguments switches them back to "Vanilla Rocq" mode...

- In order to use the "ssreflect" version, one must combine them with the discharge (`:`) tacticial:

*)
Module ArgumentsToTactics.

Lemma negb_and : forall b c, ~~ (b && c) = ~~ b || ~~ c.
Proof.
move=> b. move=> c. move: b. move: c.
by case; case.
(*
Restart.
move=> c b. move: b c.
Restart.
move=> b; case: b; move=> c; case: c.
Restart.
by case; case.
*)
Qed.

Lemma test_modus_ponens P Q (toto : Prop) : P -> (P -> Q) -> Q.
Proof.
move=> p H.
apply H. (* equivalent to `move=> pq; apply: pq` *)
by []. (* or simply `exact` instead of `by apply`. *)
Qed.

End ArgumentsToTactics.
(**

---

### Bookkeeping idioms in a nutshell

SSReflect invariants
 - if you don't name it, you can't use it
 - no tactic should alter the context silently

<div class="diamond">⋄</div>

Tactics
- `move=> stuff` replaces `intros`${}^\star$
- `move: stuff` replaces `discharge`${}^\star$
- `case: x => stuff` replaces `case x as stuff`${}^\star$
- `elim: x => stuff` replaces `elim x as stuff`${}^\star$
- `apply: H => stuff` replaces `apply H; intros stuff`${}^\star$
- `by []` or `done` applies a set of "trivial" tactics and enforces goal closure
- `by apply` $\simeq$ `exact`

<div align=right>${}^\star$ but more powerful</div>

---

## Boolean reflection

---

### A taste of boolean reflection by examples

##### Warning
  - these examples are artificial and deliberately simplified
  - in the library, this is done in a slightly different way

---

##### The first predicate
   - order relation on `nat` is a program outputting a boolean
   - `if`-`is`-`then` syntax (is simply sugar for a 2-way `match`-`with`-`end`)
   - `.+1` syntax (postfix notations .something are recurrent, e.g. `.1`, `.2`, `.-tuple`, etc)

*)
Module BooleanReflection.

Fixpoint leq (n m : nat) : bool :=
  if n is p.+1 then
    if m is q.+1 then leq p q
    else false
  else true.

Arguments leq !n !m.
Infix "<=" := leq.
(**

---

#### The first proof about `leq`

- `... = true` to "state" something
- proof by computation
- `by []` to say, provable by trivial means
  (no tactic is inside `[]`, general syntax is `by [tac1|..|tacn]`).
- `by tac` to say: `tac` must solve the goal (up to trivial leftovers)
- naming convention: head symbol of the LHS, and suffix `0` and `n`

*)
Lemma leq0n n : (0 <= n) = true.
Proof. by []. Qed.
(**

---

#### The second proof about `leq`
- equality as a double implication
- naming convention: head symbol of the LHS, and suffix `S`

*)
Lemma leqSS n m : (n.+1 <= m.+1) = (n <= m).
Proof. (* simpl *) by []. Qed.
(**

---

##### The third proof about `leq`

Let's use these lemmas (or not):
- tactic `elim` with naming and automatic clear of n
- tactic `apply`, `exact`, `rewrite`
- indentation for subgoals
- no need to mention lemmas proved by computation

*)
Lemma leqnn n : (n <= n) = true.
Proof.
elim: n => [|n IHn].
  by [].
rewrite leqSS.
by apply: IHn.
Qed.
(**

---

#### Connectives can be booleans too

- naming convention: suffix `b`

*)
Definition andb (b1 b2 : bool) : bool :=
  if b1 then b2 else false.
Infix "&&" := andb.

Definition orb (b1 b2 : bool) : bool :=
  if b1 then true else b2.
Infix "||" := orb.

Definition negb b : bool :=
  if b then false else true.
Notation "~~ b" := (negb b).
(**

---

#### Proofs by truth tables
- we can use EM to reason about boolean predicates and connectives
- intro/rewrite item: `/=`
- naming convention: `C` suffix

*)
Lemma andbC b1 b2 : (b1 && b2) = (b2 && b1).
Proof.
case: b1 => /=.
  case: b2.
    by [].
  by [].
by case: b2.
(* by case: b1; case: b2. *)
Qed.
End BooleanReflection.
(**

---


## Examples from MathComp library

---

### Things to know:
- `Search head_symbol (pat _ term) "string" inside library`
- `(a < b)` is a notation for `(a.+1 <= b)`
- `==` stands for computable equality (overloaded)
- `!=` is a mere notation for `~~ (_ == _)`
- `is_true` automatic coercion

*)
Search (_ <= _) inside ssrnat.
Locate "_ < _".
Check (forall x, x.+1 <= x).
Search orb "C" inside ssr.ssrbool.
Print commutative.
Check (3 == 4) || (3 <= 4).
Eval compute in (3 == 4) || (3 <= 4).
Check (true == false).
Check (3 != 4).

Lemma test_is_true_coercion : true.
Proof. rewrite /is_true. by []. Qed.
(**

---

### Equality 1/2
- privileged role (many lemmas are stated with `_ = _` rather than `is_true (_ == _)`)
- the `eqP` view: `is_true (a == b)   <->    a = b`
- `=> /eqP` (both directions)
- `apply/eqP`
- `=> ->` (on the fly rewrite, "subst")
- notation `.*2`

*)
Lemma test_eqP n m : n == m -> n.+1 + m.+1 = m.+1.*2.
Proof.
move=> /eqP.
move=> ->.
rewrite addnn.
by [].
Qed.
(**

---

### Equality 2/2

- Infix `==` is overloaded (see next lecture)
- and `eqP` is too

*)
Lemma test2_eqP b1 b2 : b1 == ~~ b2 -> b1 || b2.
Proof.
(*
Search orb inside ssrbool.
*)
by move=> /eqP->; exact: orNb.
Qed.
(**

---

### Views are just lemmas (plus some automatic adaptors)

- lemmas like `A -> B` can be used as views too
- boolean connectives all have associated views
- `case`/dispatch as an intro item `=> [ ... ]`

*)
Lemma test_leqW i j k : (i <= k) && (k.+1 <= j) -> i <= j.+1.
Proof.
(* move=> /andP. case. move=> /leqW. move=> leq_ik1. *)
move=> /andP[/leqW leq_ik1 /leqW leq_k1j1].
exact: leq_trans leq_ik1 leq_k1j1.
Qed.
(**

---

### The reflect predicate
`reflect P b` is the preferred way to state that the predicate `P` (in `Prop`)
  is logically equivalent to [b = true]

*)
Module reflect_for_eqP.

Print reflect.

Fixpoint eqn m n :=
  match m, n with
  | 0, 0 => true
  | j.+1,k.+1 => eqn j k
  | _, _ => false
  end.
Arguments eqn !m !n.
(**

---

### Proving the reflection lemma for eqn
- the convenience lemma `iffP`
- the `congr` tactic
- trivial branches pruning intro/rewrite item `//`
- loaded induction `elim: n m`

*)
Lemma myeqP m n : reflect (m = n) (eqn m n).
Proof.
apply: (iffP idP) => [|->]; last by elim: n.
by elim: m n => [|m IHm] // [|n] // /IHm->.
Qed.

Lemma test_myeqP n m : (eqn n m) -> m = n.
Proof. by move=> /myeqP ->. Qed.

End reflect_for_eqP.
(**

---

## Recap 1/2

- Proof language:
  - the stack model
  - `move` is the default tactic that "does nothing",
  - `by []`, `by tac` to close goals,
  - `: names`, to prepare the goal for a tactic,
  - `case` performs a case analysis on the top of the stack,
  - `=> name // /view /= {name} [|..|]`, to post-process the goal,
  - `rewrite lem -lem // /= /def`,
  - `apply: lem` to use a lemma in backward reasoning,
  - `apply/view` to use a view on the stack,
  - `apply` to apply the top of the stack to the rest of the stack,
  - `elim` to do elimination,
  - `elim: n m` to do elimination on `n` while generalizing on `m`.

---

## Recap 2/2

- Library:
  - naming convention: `addnC`, `eqP`, `orbN`, `orNb`, ...
  - notations: `.+1`, `if-is-then-else`,
  - `Search (_ + _) inside ssrnat`,
  - `Search addn "C" inside ssrnat`,
  - Use the HTML doc!
- Methodology:
  - boolean predicates, (e.g. `<=`, `\in`, `==`)
  - indentation of subgoals,
  - `reflect P b` to link `bool` with `Prop`.
  - convenience lemma `iffP` for proving `reflect`

---

### Advanced Bookkeeping

---

#### Bookkeeping 102 Operations:

- More stack intro-items:
  - skip `move=> +`, dup `move=> /[dup]` and `move=> /[swap]`
  - case analysis at the top: `move=> []`
  - applications at the top `move=> /(_ x)` and  `move=> /[apply]`

- Control flow operations:
  - `first`, `last`, `last first`, `last n first`, etc
  - `have`, `suff`, `pose`

- On the fly generalization and abbreviation:
  - `move: (pattern)`
  - `set x := (pattern)`

---

#### Skip, Dup and Swap (More intro items 1/3)

- The syntax of Dup and Swap is the combination of `/` and `[dup]` or `[swap]`

*)
Lemma test_dup_and_swap m n (P := fun b => m <= (if b then n else 0) <= m) :
  n <= m <= n -> P (m <= n).
Proof.
move=> /andP[].
move=> /[swap].
Fail by move=> ->.
rewrite /P.
Fail by move=> ->.
by move=> /[dup] + -> -> => ->.
Qed.
(**

---

#### Intro-item case (More intro items 2/3)

- Case analysis can be performed as part of an intro pattern
- One can continue the intro pattern in two ways:
  1. inside the brackets (with the right number of cases)
  2. outside the brackets


*)
Lemma test_intro_case (P : pred nat) : P 0 -> (forall m, P 0 -> P m.+1) -> forall n, P n.
Proof.
move=> P0 PS [//|n].
by rewrite PS.
(*
Restart.
move=> P0 /[swap].
Fail rewrite P0 => [|].
by rewrite P0 => - []// n ->.
*)
Qed.
(**


---

#### Intro-item application (More intro items 3/3)

- Specialization of top of the stack lemma is `/(_ t)`.
- Indeed: `(_ t)` is `fun f => f t`, which has type `(forall x : A, B x) -> B t`

*)
Lemma test_intro_apply (P : pred nat) k : P 0 ->
  forall n, P k -> (forall m, P k -> P m.+1) -> P n.
Proof.
move=> P0 [//|n] Pk.
by move=> /(_ n Pk).
(*
Restart.
move=> P0 [//|n] /[swap].
move=> /[apply]. (* same as `=> H /H` *)
by [].
*)
Qed.
(**

---

#### Reordering goals (Control flow operations 1/3)

Simple forms:
- `tac1; first tac2.` or - `tac1; last tac2.`
- `tac1; last first.` or `tac1; first last`
- `tac1; last 2 first.` or `tac1; first 2 last`

Demo:
*)
Lemma test_first_last (G P1 P2 P3 : Prop) (p1 : forall u : unit, P1) :
   (P1 -> P2 -> P3 -> G) -> G.
Proof.
apply; first exact: p1.
(*
Restart.
apply; last first.
Restart.
apply; first 2 last.
*)
Abort.
(**

---

#### Have (Control flow operations 2/3)

- `have` is the equivalent of Coq's `assert`
- it has 2 $\times$ two variants
- `have: stuff; first by tac` is abbreviated `have: stuff by tac`

| | `have := proof` | `have : statement` |
|---|---|---|
| identified  | `have f x := S x` | `have f x : list x` |
| introductive | `have [n] := ubnP`  | `have [p] : exists p, prime p` |


Try me:
*)
Goal False.
have f x := S x.            have l x : list x by exact: [::].
have [n n_gt0] := ubnP 0.   have [p p_prime] : exists p, prime p by exists 2.
Abort.
(**

---

#### Suff and pose (Control flow operations 3/3)

- `suff` is almost like `have: stuff; last first.`
- `pose idents :=` is almost like `have idents := ` but transparent.

Try me:
*)

Goal False.
pose f n := n + 1.
suff : forall n, f n != f (n + 1).
Abort.

(**

---

## Rewrite: one command to rule them all.

---

### Chaining rewrites

- 1/3 of the lines of Math Comp proofs are rewrite
- side conditions handling via // and ?
- rewrite a boolean predicate (is_true hides an equation)

*)
Lemma test_leq_cond p : prime p -> p.-1.+1 + p = p.*2.
Proof.
(*
move=> pr_p.
Search predn inside ssrnat.
rewrite prednK. (* main step *)
  by rewrite addnn. (* side condition *)
Search prime leq 0.
by apply: prime_gt0. (* conclusion *)
#*)
(* idiomatic use of conditional rewrite rules *)
by move=> pr_p; rewrite prednK ?addnn // prime_gt0.
Qed.
(**

---

### rewrite and subterm selection

- keyed matching drives the search
- specialization via argument passing
- specialization via pattern `rewrite [pat]stuff`
- localization via contextual pattern (approximate or precise)
- LHS and RHS notations
- subterm selection also works with `move: (pat)` and `set := (pat)`

*)
Lemma subterm_selection n m :
  n + (m * 2).+1 = n * (m + m.+1).
Proof.
rewrite addnC.
rewrite (addnC m).
rewrite [_ + m]addnC.
rewrite [in n * _]addnC.
rewrite [X in _ = _ * X]addnC.
rewrite [in RHS]addnC.
rewrite -[n in RHS]addn0.
set k := (X in _ = _ * X).
move: (0 in RHS).
Abort.
(**

---

## Linear algebra in MathComp

Extensive documentation in the header of:
  + the library [matrix](https://math-comp.github.io/htmldoc_2_3_0/mathcomp.algebra.matrix.html)
  + and the library [mxalgebra](https://math-comp.github.io/htmldoc_2_3_0/mathcomp.algebra.mxalgebra.html)


Roadmap:
  + definition of matrices
  + main theorems
  + help with depend types
  + vector spaces as matrices

---

### Preamble on algebraic hierarchies

Lean uses (semi-)bundled typeclasses ```∀ (α : Type) [Ring α], ...``` while Rocq uses bundled structures: ```∀ (R : ringType), etc```. Inheritance is handled automatically.

Here are common structures we will use:
*)
Check zmodType.
Check ringType.
Check (fun R : ringType => R : zmodType).

HB.graph "hierarchy.dot".
(**

---

### (Re)Defining Matrices

(Credits "ITP 2013 tutorial: The Mathematical Components library" by Enrico Tassi and Assia Mahboubi)

Some notations:
*)
Module MatrixDefinitions.

Reserved Notation "''M[' R ]_ n"
  (at level 8, n at level 2, format "''M[' R ]_ n").
Reserved Notation "''M[' R ]_ ( m , n )"
  (at level 8, format "''M[' R ]_ ( m ,  n )").

Reserved Notation "\matrix_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix_ ( i ,  j )  E").

Reserved Notation "x %:M"   (at level 8, format "x %:M").
Reserved Notation "A *m B" (at level 40, left associativity, format "A  *m  B").
Reserved Notation "A ^T"    (at level 8, format "A ^T").
Reserved Notation "\tr A"   (at level 10, A at level 8, format "\tr  A").
(**

---

#### A matrix is a 2-dimension array

*)
Inductive matrix (R : Type) (m n : nat) : Type :=
  Matrix of {ffun 'I_m * 'I_n -> R}.
(**
Some notations : size inside parentheses, type of coefficients inside
square brackets. NB: In the library, the type of coefficients can also
be ommitted.

*)
Notation "''M[' R ]_ ( m , n )" := (matrix R m n) : type_scope.
Notation "''M[' R ]_ n" := 'M[R]_(n, n) : type_scope.

(* Test *)
Check 'M[nat]_(2,3).
Check 'M[nat]_2.
(**

---


#### Matrix inherit structure

The type "matrix" is just a tag over ffun: it inherits from its structure.
We can "transfer" automatically all structures from the type of finite
functions by "trivial subTyping".

*)
Definition mx_val R m n (A : 'M[R]_(m,n)) : {ffun 'I_m * 'I_n -> R} :=
  let: Matrix g := A in g.

HB.instance Definition _ R m n := [isNew for @mx_val R m n].

HB.instance Definition _ (R : eqType) m n     := [Equality of 'M[R]_(m, n) by <:].
HB.instance Definition _ (R : choiceType) m n := [Choice of 'M[R]_(m, n) by <:].
HB.instance Definition _ (R : countType) m n  := [Countable of 'M[R]_(m, n) by <:].
HB.instance Definition _ (R : finType) m n    := [Finite of 'M[R]_(m, n) by <:].
(**

---

#### Testing overloading


Test overloaded `_ == _`` notation

*)
Check 'M[nat]_2 : eqType.
Check forall A : 'M[nat]_2, A == A.
(**

Since matrices over nat are comparable with `_ == _`, matrices over
matrices over nat are also comparable
*)
Check forall AA : 'M[ 'M[nat]_3 ]_2, AA == AA.
(**

---

#### Matrix as functions

We define a coercion in order to access elements as if matrices were
functions.

*)
Definition fun_of_mx R m n (A : 'M[R]_(m,n)) : 'I_m -> 'I_n -> R :=
fun i j => mx_val A (i, j).  Coercion fun_of_mx : matrix >-> Funclass.

Check forall (A : 'M[nat]_3) i j, A i j == 37%N.
(**

We provide a notation to build matrices from a general term.

---

### Matrix as their general term

*)
Definition mx_of_fun R m n (F : 'I_m -> 'I_n -> R) : 'M[R]_(m,n) :=
  Matrix [ffun ij => F ij.1 ij.2].
Notation "\matrix_ ( i , j ) E" := (mx_of_fun (fun i j => E))
  (at level 36, E at level 36, i, j at level 50).

Check \matrix_(i,j) (i - j)%N  :  'M[nat]_(3,4).

End MatrixDefinitions.

Local Open Scope ring_scope.
Import GRing.Theory.
(**

---



### Main Theorems

We now show the most used theorems for matrix manipulation.

#### `mxE`

`mxE` is an equation to compute a term in the matrix at given
coordinates: it extracts the general term of the matrix and compute
the substitution of indexes. It is generally the right move when you
have <pre>(A complicated matrix) i j</pre>

in your goal.

```
Check mxE.
```

---


#### `matrixP`

`matrixP` is the "extensionality theorem" for matrices, it says two
matrices are equal if and only if all their coefficients are pairwise
equal.

```
Check matrixP.
```

---


#### Trace and transpose

*)
Print mxtrace.
Locate "\tr".
(**

*)
Print trmx.
Locate "^T".
(**

#### "Diagonal" matrix

*)
Print scalar_mx.
Locate "%:M".
(**

---


#### General operations

- Matrices on rings are provided with a R-module canonical structure.
- But not a ring since the multiplication is heterogeneous.
- Instead there is an ad-hoc matrix product.

*)
Lemma test1 (R : ringType) m n (A B : 'M[R]_(m,n)) : A + B = B + A.
Proof. exact: addrC. Qed.

Print mulmx.

Lemma test2 (R : ringType) m n (a : R) (A : 'M[R]_(m,n)) : a *: A = a%:M *m A.
Proof. by rewrite mul_scalar_mx. Qed.
(**

---


#### Ring structure

- Square matrices with explicit non zero size have a ring canonical structure.
- This ring product coincides with the matrix product.

*)
Lemma test3 (R : ringType) n (A B : 'M[R]_n.+1) : A * B = A *m B.
Proof. reflexivity. Qed.
(**

---



#### The determinant and `unitRingType` structure

There is a determinant function:
*)
Print determinant.
Locate "\det".
(**

- Square matrices on a commutative unit ring with explicit non zero size have a "unit ring" structure.
- the notions of inversibility are definitionally equivalent.

*)
Lemma test4 (R : comUnitRingType) n (A : 'M[R]_n.+1) :
  (unitmx A) = (A \is a GRing.unit)
  /\ (A \is a GRing.unit) = (\det A \is a GRing.unit).
Proof. split; reflexivity. Qed.
(**

---

## SUB VECTOR SPACES AS MATRICES

General understanding

 - A specificity of the mathematical components library is to allow to
  reason on matrices as if they represented their own image.

 - The doc and the code are in #<a href="https://math-comp.github.io/htmldoc_2_3_0/mathcomp.algebra.mxalgebra.html">mxalgebra</a>#

 - rows can be seen as vectors, and matrix can be seen as the familiy
  of its row vectors.

 - ⚠️ Following the diagramatic convention (which is
    opposite to the usual convention), composition/application of
    linear maps represented by matrices should be done left to right:
    applying A to u is <pre>u *m A</pre>

 - the scope MS (matrix space) contains all notions about this vision
   of matrices (comparison, addition, intersection of spaces).

 - as a consequence, membership to a space is the same operation as
   comparison of spaces.

---

### Consequences

#### The trivial ones

The rank of a matrix is also the dimension of the space it represents

*)
Locate "\rank".
About mxrank.
(**

Inclusion can be used both for elements (row vectors) and subspaces (matrices).

*)
Locate "_ <= _".
About submx.
(**

The total space is represented by 1, and the trivial space by 0.

*)
About submx1.
About sub1mx.
About sub0mx.
About submx0.
(**

---

#### Trivial but tricky...

Addition of subspaces is not the same thing as addition of matrices.
(In Coq: same notation, different scope)


*)
Locate "_ + _".
About addsmx.
(**

<div class="diamond">⋄</div>


#### Intersection of subspaces

*)
Locate "_ :&: _".
About capmx.
About sub_capmx.
(**

---


#### Equality of subspaces is double inclusion.

Alternatively, the library provides an equivalent definition (via
eqmxP) that can be used for rewriting in inclusion statements or rank.

*)
Locate "_ == _".
Check (_ == _)%MS.

Locate "_ :=: _".
About eqmx.
Print eqmx.

About mxdirectE.
About mxdirect_addsP.
(**

---


#### Image and Kernel.

 - $\mathrm{Im} A$ is represented by the matrix `A` itself.

 - vectors of a space represented by the matrix `A` are linear
   combinations of the rows of `A`, which amount to making a product by
   an element (i.e. row of coefficients, or coordinates in the family
   generated by `A`) on the left.

*)
About submxP.
About row_subP.
About submxMl.
(**

 - $\mathrm{Im} A$ is represented by the square matrix `kermx A`.

*)
About kermx.
About sub_kermxP.
(**


---


### Let's do an example together

*)
Section ex_6_12.

Variables (F : fieldType) (n' : nat).
Let n := n'.+1.
Variable (u : 'M[F]_n) (S : 'M[F]_n).
Hypothesis eq_keru_imu : (kermx u :=: u)%MS.
Hypothesis S_u_direct : (S :&: u)%MS = 0.
Hypothesis S_u_eq1 : (S + u :=: 1)%MS.
Implicit Types (x y z : 'rV[F]_n).

Lemma Su_rect (x : 'rV_n) : exists (y : 'rV_n) (z : 'rV_n),
  x = y + z *m u /\ (y <= S)%MS && (z <= S)%MS.
Proof.
pose y := x *m proj_mx S u.
have /submxP [z'] := proj_mx_sub u S x => xpu.
pose z := z' *m proj_mx S u.
exists y, z => /=; split; last by rewrite !proj_mx_sub.
rewrite -{1}(@add_proj_mx _ _ _ S u x) ?S_u_direct ?S_u_eq1 ?submx1 //.
congr (_ + _); apply/eqP; rewrite xpu -subr_eq0 -mulmxBl.
apply/eqP/sub_kermxP.
by rewrite eq_keru_imu proj_mx_compl_sub ?S_u_eq1 ?submx1.
Qed.

Lemma Su_dec_eq0 y z : (y <= S)%MS -> (z <= S)%MS ->
  (y + z *m u == 0) = (y == 0) && (z == 0).
Proof.
move=> yS zS; apply/idP/idP; last first.
  by move=> /andP[/eqP -> /eqP ->]; rewrite add0r mul0mx.
rewrite addr_eq0 -mulNmx => /eqP eq_y_Nzu.
have : (y <= S :&: u)%MS by rewrite sub_capmx yS eq_y_Nzu submxMl.
rewrite S_u_direct // submx0 => /eqP y_eq0.
move/eqP: eq_y_Nzu; rewrite y_eq0 eq_sym mulNmx oppr_eq0 eqxx /= => /eqP.
move=> /sub_kermxP; rewrite eq_keru_imu => z_keru.
have : (z <= S :&: u)%MS by rewrite sub_capmx zS.
by rewrite S_u_direct // submx0.
Qed.

End ex_6_12.
(**
*)
