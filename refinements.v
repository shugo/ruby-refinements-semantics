(* A formal model of Ruby's Proc#refined (bugs.ruby-lang.org #22097).

   Part 1 -- refinement state: activation of module sequences as a
             left fold, last-wins dispatch, and re-activation as a
             no-op.
   Part 2 -- closures: Proc#refined as an environment extension, its
             commutative square with "using", and the monoid action
             laws.

   The model deliberately abstracts a Proc to (body, refinement part
   of the captured cref); iseq copies, memoization and visibility are
   outside its scope.  A Proc not created from a Ruby block has no
   such pair and is outside the scope as well: the implementation
   still rejects it with ArgumentError unless the module sequence is
   empty.

   Theorems marked [PR #18052] state properties that hold only with the
   revised design of github.com/ruby/ruby/pull/18052, which permits
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
Variable eq_dec : forall x y : M, {x = y} + {x <> y}.
Variable K : Type.                  (* dispatch keys: (class, method) *)
Variable refines : M -> K -> bool.  (* does module m refine key k? *)

(* ============ Part 1: refinement state ============ *)

(* The refinement part of a cref, as the active modules in activation
   order.  rb_using_refinement returns early for a module already in
   the iclass chain, so the state is duplicate-free and a module keeps
   the position of its first activation. *)
Definition state := list M.

Definition activate (s : state) (m : M) : state :=
  if in_dec eq_dec m s then s else s ++ [m].

(* Activating a sequence, left to right -- the cref accumulation,
   shared by sequential "using" and by variadic refined. *)
Definition apply_seq (s : state) (w : list M) : state :=
  fold_left activate w s.

Lemma in_activate : forall (s : state) (m : M), In m (activate s m).
Proof.
  intros s m. unfold activate. destruct (in_dec eq_dec m s) as [H | _].
  - exact H.
  - apply in_or_app. right. left. reflexivity.
Qed.

Lemma activate_mono : forall (s : state) (m x : M), In x s -> In x (activate s m).
Proof.
  intros s m x H. unfold activate. destruct (in_dec eq_dec m s).
  - exact H.
  - apply in_or_app. left. exact H.
Qed.

Lemma activate_fresh : forall (s : state) (m : M), ~ In m s -> activate s m = s ++ [m].
Proof.
  intros s m H. unfold activate. destruct (in_dec eq_dec m s).
  - contradiction.
  - reflexivity.
Qed.

Lemma activate_nil : forall m : M, activate [] m = [m].
Proof.
  intro m. apply activate_fresh. intros [].
Qed.

(* [PR #18052]  Staged activation equals one-shot activation of the
   concatenated sequence.  The fold identity itself is a stock fact
   (fold_left_app); what depends on PR #18052 is its reading: it is the
   semantic claim that stacking new modules on the receiver's cref
   (the chained implementation) coincides with applying the
   concatenated sequence to the captured cref in one call.  Without
   chaining there is no staged activation to compare. *)
Theorem staged_eq_oneshot : forall (a b : list M) (s : state),
  apply_seq s (a ++ b) = apply_seq (apply_seq s a) b.
Proof.
  intros. unfold apply_seq. apply fold_left_app.
Qed.

(* Dispatch is last-wins over the state: the last module activated
   among those refining k. *)
Fixpoint find_last (s : state) (k : K) : option M :=
  match s with
  | [] => None
  | m :: rest =>
      match find_last rest k with
      | Some m' => Some m'
      | None => if refines m k then Some m else None
      end
  end.

Definition table := K -> option M.

(* The module in effect for k, falling through to the base table. *)
Definition lookup (s : state) (T0 : table) (k : K) : option M :=
  match find_last s k with
  | Some m => Some m
  | None => T0 k
  end.

Lemma find_last_snoc : forall (s : state) (m : M) (k : K),
  find_last (s ++ [m]) k = if refines m k then Some m else find_last s k.
Proof.
  induction s as [| a rest IH]; intros m k; simpl.
  - destruct (refines m k); reflexivity.
  - rewrite IH. destruct (refines m k).
    + reflexivity.
    + destruct (find_last rest k); reflexivity.
Qed.

(* Activating a module not yet active makes it win for every key it
   refines.  The freshness hypothesis is essential: an already active
   module keeps the position of its first activation, so re-applying
   it does not raise its precedence (see reactivation_equiv). *)
Lemma lookup_activate_fresh : forall (s : state) (T0 : table) (m : M) (k : K),
  ~ In m s -> refines m k = true -> lookup (activate s m) T0 k = Some m.
Proof.
  intros s T0 m k Hfresh Href. unfold lookup.
  rewrite (activate_fresh s m Hfresh), find_last_snoc, Href. reflexivity.
Qed.

(* Observational equivalence of module sequences: acting the same on
   every state at every key.  The congruence defining the quotient
   monoid of refinement states. *)
Definition seq_equiv (w1 w2 : list M) : Prop :=
  forall (s : state) (T0 : table) (k : K),
    lookup (apply_seq s w1) T0 k = lookup (apply_seq s w2) T0 k.

(* Re-activation is a no-op, as with nested "using" of the same
   module. *)
Theorem reactivation_noop : forall (s : state) (m : M), In m s -> activate s m = s.
Proof.
  intros s m H. unfold activate. destruct (in_dec eq_dec m s).
  - reflexivity.
  - contradiction.
Qed.

(* A no-op in the strong sense: re-applying a module does not move it
   past one activated later.  `using a; using b; using a` and
   `p.refined(a, b, a)` both dispatch to b, not a. *)
Corollary reactivation_seq : forall (s : state) (a b : M),
  apply_seq s [a; b; a] = apply_seq s [a; b].
Proof.
  intros s a b. unfold apply_seq. simpl.
  rewrite reactivation_noop.
  - reflexivity.
  - apply activate_mono, in_activate.
Qed.

Corollary reactivation_equiv : forall a b : M, seq_equiv [a; b; a] [a; b].
Proof.
  intros a b s T0 k. now rewrite reactivation_seq.
Qed.

(* The same at the level of dispatch: when both modules refine k, the
   re-applied a does not win it back. *)
Corollary reactivation_dispatch : forall (a b : M) (T0 : table) (k : K),
  a <> b -> refines a k = true -> refines b k = true ->
  lookup (apply_seq [] [a; b; a]) T0 k = Some b.
Proof.
  intros a b T0 k Hab Ha Hb. rewrite reactivation_seq.
  unfold apply_seq. cbn [fold_left].
  rewrite activate_nil, activate_fresh.
  - unfold lookup. simpl. rewrite Hb. reflexivity.
  - intros [H | H]; [congruence | contradiction].
Qed.

(* ============ Part 2: closures and Proc#refined ============ *)

Variable B : Type.                  (* block bodies (code) *)

Definition env := state.            (* refinement part of a cref *)
Definition closure := (B * env)%type.

Definition close (b : B) (rho : env) : closure := (b, rho).

(* The effect of "using S" on a lexical environment. *)
Definition extend (rho : env) (S : list M) : env := apply_seq rho S.

(* Proc#refined: re-close the same body over the extended environment.
   Non-mutating by construction.  NOTE: modelled as a total function;
   the original design's domain restrictions (rejecting S = [] and
   already-refined receivers) are not represented, so each theorem
   below states explicitly whether it needs PR #18052. *)
Definition refined (p : closure) (S : list M) : closure :=
  let (b, rho) := p in (b, extend rho S).

(* The commutative square: refining the closure of b over rho equals
   closing b over the "using"-extended environment.  Holds already for
   the original one-shot design: it concerns a single application and
   follows from non-mutation alone. *)
Theorem square : forall (b : B) (rho : env) (S : list M),
  refined (close b rho) S = close b (extend rho S).
Proof. reflexivity. Qed.

(* [PR #18052]  Unit law.  Requires zero-argument application; the
   original design rejected refined() with ArgumentError, so this
   statement had no defined left-hand side.  The law is definitional
   here -- the empty fold is the identity -- which is as close as the
   model gets to the design decision that refined() returns the
   receiver itself rather than an equivalent copy. *)
Theorem refined_unit : forall p : closure, refined p [] = p.
Proof.
  intros [b rho]. reflexivity.
Qed.

(* [PR #18052]  Associativity (compatibility) law.  Requires chained
   application; the original design rejected refined on an
   already-refined receiver, so the left-hand side was undefined. *)
Theorem refined_assoc : forall (p : closure) (S1 S2 : list M),
  refined (refined p S1) S2 = refined p (S1 ++ S2).
Proof.
  intros [b rho] S1 S2. unfold refined, extend. now rewrite staged_eq_oneshot.
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

(* Bridge to Part 1: the dispatch in effect when a closure's body
   runs, starting from a base table T0. *)
Definition table_of (p : closure) (T0 : table) : table :=
  lookup (snd p) T0.

(* [PR #18052]  Chained and one-shot refined procs yield the same
   dispatch.  Requires chaining to be defined at all; with it, the
   equality is immediate from refined_assoc. *)
Corollary chained_table : forall (p : closure) (S1 S2 : list M) (T0 : table),
  table_of (refined (refined p S1) S2) T0
  = table_of (refined p (S1 ++ S2)) T0.
Proof.
  intros. now rewrite refined_assoc.
Qed.

(* Behavior depends only on the equivalence class of the activated
   sequence: equivalent sequences give equal dispatch at every key.
   Independent of PR #18052. *)
Corollary table_respects_equiv :
  forall (b : B) (w1 w2 : list M) (s : env) (T0 : table) (k : K),
    seq_equiv w1 w2 ->
    table_of (close b (apply_seq s w1)) T0 k
    = table_of (close b (apply_seq s w2)) T0 k.
Proof.
  intros b w1 w2 s T0 k H. apply H.
Qed.

End Refinements.
