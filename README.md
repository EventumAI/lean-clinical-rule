# A clinical rule in Lean 4

Two Lean 4 files from posts by Eventum, an AI engineering consultancy, on checking clinical recommendations. Core library only, no Mathlib, checked with Lean 4.35.0 (pinned in `lean-toolchain`). The pathway is an illustration, not a prescribing protocol.

## Part7.lean

The worked example from [The Recommendation Explained Itself. Did Anything Check the Explanation?](https://www.eventum.ai/blog/the-recommendation-explained-itself-did-anything-check-the-explanation) (Compile-Time Intelligence, Part 7): a five-condition statin pathway and one patient on dialysis.

- The approved rule is a type. A proof that a patient is eligible is a bundle of five proofs, one per condition. A bundle that leaves out dialysis is rejected with ``Fields missing: `noDialysis` ``, and the file pins that message with `#guard_msgs`.
- Two checkers read an untrusted justification. `checkerB_sound`: whatever Checker B accepts, the approved rule supports, for every patient and every justification. `checkerB_accepts_honest`: B accepts the honest justification for every patient. `checkerA_unsound`: Checker A, which checks only the conditions the justification lists, has no such guarantee, and the article's patient is the counterexample.
- A version of the rule that forgot dialysis (`EligibleUnderForgetfulRule`) compiles too, and the article's patient is eligible under it. The theorems hold relative to the rule as written.
- The file pins the axioms its three main theorems depend on (at most `propext`, `Classical.choice` and `Quot.sound`). It uses no `sorry` and no `native_decide`.

## TwoCheckers.lean

The same pathway, split between the part a proof checker can settle and the part it cannot. An evidence layer reports each condition as `holds`, `fails` or `unresolved`. A decision procedure returns `recommend_start`, `no_recommendation` (with the failed conditions) or `unresolved` (with the open ones).

- `start_iff`: a start is recommended exactly when all five conditions are reported as holding.
- `start_sound` and `noRecommendation_sound`: if everything the report calls settled is true of the patient, either answer is right.
- `exact_complete`: if such a report also leaves nothing unresolved, the procedure recommends starting exactly when the patient is eligible.

Whether the evidence is true is outside the proofs. That is the evidence layer's job.

The file is also the program that makes the decisions. It reads a JSON array of reports:

```
lean --run TwoCheckers.lean < cases_example.json
```

```
{"conditions":["noDialysis"],"decision":"no_recommendation","id":"on-dialysis"}
{"conditions":["noDialysis"],"decision":"unresolved","id":"dialysis-unknown"}
{"conditions":[],"decision":"recommend_start","id":"all-five-hold"}
```

## Checking the proofs

With [elan](https://github.com/leanprover/elan) installed, from this folder:

```
lean Part7.lean
lean TwoCheckers.lean
```

Each command prints nothing and exits with status 0 when every proof checks.

Questions and corrections are welcome as issues.
