(* A formal model of Ruby's Proc#refined (bugs.ruby-lang.org #22097).

   Part 1 -- refinement tables: activation of module sequences as a
             left fold, last-wins dispatch, and re-activation as a
             no-op.
   Part 2 -- closures: Proc#refined as an environment extension, its
             commutative square with "using", and the monoid action
             laws.

   The model deliberately abstracts a Proc to (body, refinement part
   of the captured cref); iseq copies, memoization and visibility are
   outside its scope.

   Theorems marked [PR #132] state properties that hold only with the
   revised design of github.com/shugo/ruby/pull/132, which permits
   zero-argument application (returning the receiver) and chained
   application.  Under the original design both were rejected with
   ArgumentError, so `refined` was a partial function: the marked
   statements would either be inexpressible (their left-hand sides are
   undefined) or false.  Unmarked theorems already hold for the
   original one-shot design. *)

Require Import List.
Import ListNotations.

Section Refinements.

Variable M : Type.                  (* modules *)
Variable K : Type.                  (* dispatch keys: (class, method) *)
Variable refines : M -> K -> bool.  (* does module m refine key k? *)

(* ============ Part 1: refinement tables ============ *)

Definition table := K -> option M.

(* Activating one module: its refinements override existing entries
   (last wins), everything else is inherited. *)
Definition activate (T : table) (m : M) : table :=
  fun k => if refines m k then Some m else T k.

(* Activating a sequence, left to right -- the cref accumulation,
   shared by sequential "using" and by variadic refined. *)
Definition apply_seq (T : table) (w : list M) : table :=
  fold_left activate w T.

(* [PR #132]  Staged activation equals one-shot activation of the
   concatenated sequence.  The fold identity itself is a stock fact
   (fold_left_app); what depends on PR #132 is its reading: it is the
   semantic claim that stacking new modules on the receiver's cref
   (the chained implementation) coincides with applying the
   concatenated sequence to the captured cref in one call.  Without
   chaining there is no staged activation to compare. *)
Theorem staged_eq_oneshot : forall (a b : list M) (T : table),
  apply_seq T (a ++ b) = apply_seq (apply_seq T a) b.
Proof.
  intros. unfold apply_seq. apply fold_left_app.
Qed.

(* Dispatch is last-wins: looking up k after activating w finds the
   last module in w that refines k, else falls through to T. *)
Fixpoint find_last (w : list M) (k : K) : option M :=
  match w with
  | [] => None
  | m :: rest =>
      match find_last rest k with
      | Some m' => Some m'
      | None => if refines m k then Some m else None
      end
  end.

Lemma lookup_apply_seq : forall w T k,
  apply_seq T w k = match find_last w k with
                    | Some m => Some m
                    | None => T k
                    end.
Proof.
  induction w as [| m rest IH]; intros T k.
  - reflexivity.
  - unfold apply_seq in *. simpl. rewrite IH.
    destruct (find_last rest k) as [m'|].
    + reflexivity.
    + unfold activate. destruct (refines m k); reflexivity.
Qed.

(* Observational equivalence of module sequences: acting the same on
   every table at every key.  The congruence defining the quotient
   monoid of refinement states. *)
Definition seq_equiv (w1 w2 : list M) : Prop :=
  forall T k, apply_seq T w1 k = apply_seq T w2 k.

(* Re-activation is a no-op, as with nested "using" of the same
   module -- an instance showing the quotient is proper. *)
Theorem reactivation_noop : forall a : M, seq_equiv [a; a] [a].
Proof.
  intros a T k. unfold apply_seq. simpl. unfold activate.
  destruct (refines a k); reflexivity.
Qed.

(* ============ Part 2: closures and Proc#refined ============ *)

Variable B : Type.                  (* block bodies (code) *)

Definition env := list M.           (* refinement part of a cref *)
Definition closure := (B * env)%type.

Definition close (b : B) (rho : env) : closure := (b, rho).

(* The effect of "using S" on a lexical environment. *)
Definition extend (rho : env) (S : list M) : env := rho ++ S.

(* Proc#refined: re-close the same body over the extended environment.
   Non-mutating by construction.  NOTE: modelled as a total function;
   the original design's domain restrictions (rejecting S = [] and
   already-refined receivers) are not represented, so each theorem
   below states explicitly whether it needs PR #132. *)
Definition refined (p : closure) (S : list M) : closure :=
  let (b, rho) := p in (b, extend rho S).

(* The commutative square: refining the closure of b over rho equals
   closing b over the "using"-extended environment.  Holds already for
   the original one-shot design: it concerns a single application and
   follows from non-mutation alone (the proof is reflexivity and uses
   neither app_nil_r nor app_assoc, so it is independent of the unit
   and associativity laws below). *)
Theorem square : forall (b : B) (rho : env) (S : list M),
  refined (close b rho) S = close b (extend rho S).
Proof. reflexivity. Qed.

(* [PR #132]  Unit law.  Requires zero-argument application; the
   original design rejected refined() with ArgumentError, so this
   statement had no defined left-hand side.  Note the proof needs
   app_nil_r: the law is propositional, not definitional, mirroring
   the design decision that refined() returns the receiver itself. *)
Theorem refined_unit : forall p : closure, refined p [] = p.
Proof.
  intros [b rho]. unfold refined, extend. now rewrite app_nil_r.
Qed.

(* [PR #132]  Associativity (compatibility) law.  Requires chained
   application; the original design rejected refined on an
   already-refined receiver, so the left-hand side was undefined. *)
Theorem refined_assoc : forall (p : closure) (S1 S2 : list M),
  refined (refined p S1) S2 = refined p (S1 ++ S2).
Proof.
  intros [b rho] S1 S2. unfold refined, extend. now rewrite app_assoc.
Qed.

(* Uniqueness of the lift: any operation r making the square commute
   agrees with refined everywhere, because every block-based closure
   is in the image of close.  Like the square itself, this concerns a
   single application and holds for the original design (restricted to
   its domain). *)
Theorem refined_uniqueness :
  forall (r : closure -> list M -> closure),
    (forall b rho S, r (close b rho) S = close b (extend rho S)) ->
    forall p S, r p S = refined p S.
Proof.
  intros r Hsq [b rho] S. exact (Hsq b rho S).
Qed.

(* Bridge to Part 1: the dispatch table in effect when a closure's
   body runs, starting from a base table T0. *)
Definition table_of (p : closure) (T0 : table) : table :=
  apply_seq T0 (snd p).

(* [PR #132]  Chained and one-shot refined procs yield the same
   dispatch table.  Requires chaining to be defined at all; with it,
   the equality is immediate from refined_assoc. *)
Corollary chained_table : forall (p : closure) (S1 S2 : list M) T0,
  table_of (refined (refined p S1) S2) T0
  = table_of (refined p (S1 ++ S2)) T0.
Proof.
  intros. now rewrite refined_assoc.
Qed.

(* Behavior depends only on the equivalence class of the captured
   sequence: equivalent sequences give equal dispatch at every key.
   Independent of PR #132. *)
Corollary table_respects_equiv : forall (b : B) (w1 w2 : list M) T0 k,
  seq_equiv w1 w2 ->
  table_of (close b w1) T0 k = table_of (close b w2) T0 k.
Proof.
  intros b w1 w2 T0 k H. apply H.
Qed.

End Refinements.
