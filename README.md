# ruby-refinements-semantics

A small Coq formalization of the semantics of Ruby's `Proc#refined`
([Feature #22097](https://bugs.ruby-lang.org/issues/22097)), covering the
activation of refinements in a cref and the algebraic laws of `refined`
introduced by the revised design in
[shugo/ruby#132](https://github.com/shugo/ruby/pull/132) (zero-argument
application returns the receiver; chained application behaves like a single
application of the concatenated module sequence).  The method was called
`Proc#with_refinements` earlier in the proposal's history.

Everything lives in a single file, [`refinements.v`](refinements.v), which
depends only on the Coq standard library:

```console
$ coqc refinements.v
```

## The model

- A **module** `m : M` refines a set of dispatch keys `k : K`
  (a key abstracts a (class, method) pair), given by
  `refines : M -> K -> bool`.
- A **refinement table** `T : K -> option M` says which module's
  refinement, if any, is in effect for each key.  `activate T m`
  overrides the entries refined by `m` (last wins) and inherits the
  rest; `apply_seq` folds `activate` over a module sequence, mirroring
  how both sequential `using` and variadic `refined` accumulate
  refinements in a cref.
- A **closure** is a pair `(body, env)` where `env` is the refinement
  part of the captured cref, i.e. the sequence of modules activated so
  far.  `refined p S` re-closes the same body over the extended
  environment `env ++ S`; it is non-mutating by construction.

Deliberately outside the model: iseq copying and memoization, scope
visibility, the `using`-in-body rejection, Ractor concerns, and the
lexical scoping of `using` itself.  The model captures what a refined
proc *means*, not how the implementation caches it.

## Theorems

Statements marked **[PR #132]** hold only under the revised design.  In
the original one-shot design `refined` was a partial function
(zero-argument and chained calls raised `ArgumentError`), so their
left-hand sides were undefined.  Unmarked statements already hold for
the original design.

| Theorem | Statement | Needs PR #132 |
| --- | --- | --- |
| `staged_eq_oneshot` | Activating `a ++ b` equals activating `a`, and then `b` on the result | yes (the fold identity is stock; its staged reading requires chaining) |
| `lookup_apply_seq` | Dispatch after activating `w` finds the *last* module in `w` refining the key, else falls through | no |
| `reactivation_noop` | `[a; a]` and `[a]` are observationally equivalent (re-`using` a module is a no-op) | no |
| `square` | `refined (close b rho) S = close b (extend rho S)`: refining a closure equals closing over the `using`-extended environment | no |
| `refined_unit` | `refined p [] = p` | yes |
| `refined_assoc` | `refined (refined p S1) S2 = refined p (S1 ++ S2)` | yes |
| `refined_uniqueness` | Any operation making the square commute agrees with `refined` everywhere | no |
| `chained_table` | Chained and one-shot refined procs dispatch identically | yes |
| `table_respects_equiv` | Dispatch depends only on the observational equivalence class of the captured sequence | no |

## Correspondence to the implementation

| Model | CRuby |
| --- | --- |
| `apply_seq` | `rb_using_module_recursive` accumulating refinements in a cref (the feature branch's export of upstream's static `using_module_recursive`, eval.c) |
| last-wins in `activate` | later `using` / later `refined` argument takes precedence |
| `extend rho S` (`env ++ S`) | a chained call stacks new modules on a duplicate of the receiver's cref |
| `refined p [] = p` | `Proc#refined` with no arguments returns the receiver itself |
| `refined_assoc` | `p.refined(a).refined(b)` behaves like `p.refined(a, b)` |
| `seq_equiv` | procs whose crefs activate the same refinements are indistinguishable by dispatch |

The implementation caches iseq copies in a single-entry memo on each
source iseq, keyed by the receiver's refinement state (the captured
cref, or the frozen refinements table for a chained call) and the
module arguments.  `p.refined(a).refined(b)` and `p.refined(a, b)`
therefore produce *distinct* copies with equal behavior: the model's
equalities correspond to observational equivalence of procs, not object
identity -- except `refined()`, which returns the receiver itself.
