/-!
# Part 7 in Lean: a recommendation that carries its proof

A Lean 4 restatement of the worked example in "The Recommendation Explained Itself.
Did Anything Check the Explanation?" (Compile-Time Intelligence, Part 7):
https://www.eventum.ai/blog/the-recommendation-explained-itself-did-anything-check-the-explanation

The article runs two checkers on three justifications for one patient. This file
proves the claim behind that table for every patient and every justification:
whatever Checker B accepts is supported by the approved rule. For a recommendation
to start, that is because B takes its list of requirements from the rule and not
from the justification. Checker A checks the argument it is given, and for a
recommendation to start it has no such guarantee; the article's patient is the
counterexample.

Core Lean 4 only, no Mathlib. Checked with Lean 4.35.0 (the `#guard_msgs` blocks
pin that version's messages). The pathway is the article's illustration, not a
prescribing protocol.
-/

namespace Part7

/-! ## Patient inputs, taken as given -/

/-- The inputs the pathway reads. The article assumes they "have been confirmed as
current", and so does this file: nothing below says whether the record is right. -/
structure Patient where
  age : Nat
  dyslipidemia : Bool
  diabetes : Bool
  hypertension : Bool
  smoking : Bool
  /-- Estimated ten-year cardiovascular risk, in tenths of a percent (12.4% is 124). -/
  risk : Nat
  onDialysis : Bool
  onStatin : Bool

/-! ## The approved rule -/

/-- The five conditions of the approved pathway. -/
inductive Cond where
  | age | riskFactor | risk | noDialysis | noStatin
  deriving DecidableEq

/-- What each condition means on a patient's inputs. -/
def Cond.Holds (p : Patient) : Cond → Prop
  | .age => 40 ≤ p.age ∧ p.age ≤ 75
  | .riskFactor => p.dyslipidemia ∨ p.diabetes ∨ p.hypertension ∨ p.smoking
  | .risk => 100 ≤ p.risk
  | .noDialysis => p.onDialysis = false
  | .noStatin => p.onStatin = false

instance (p : Patient) : (c : Cond) → Decidable (c.Holds p)
  | .age => inferInstanceAs (Decidable (_ ∧ _))
  | .riskFactor => inferInstanceAs (Decidable (_ ∨ _))
  | .risk => inferInstanceAs (Decidable (_ ≤ _))
  | .noDialysis => inferInstanceAs (Decidable (_ = _))
  | .noStatin => inferInstanceAs (Decidable (_ = _))

/-- The approved rule as a type. A proof of `Eligible p` is a bundle of five proofs,
one per condition, and there is no other way to build one. -/
structure Eligible (p : Patient) : Prop where
  age : Cond.age.Holds p
  riskFactor : Cond.riskFactor.Holds p
  risk : Cond.risk.Holds p
  noDialysis : Cond.noDialysis.Holds p
  noStatin : Cond.noStatin.Holds p

/-- What a recommendation to start must establish. Checker B reads this list. -/
def required : List Cond := [.age, .riskFactor, .risk, .noDialysis, .noStatin]

/-- The list the checker reads says exactly what the approved rule says. -/
theorem eligible_iff (p : Patient) : Eligible p ↔ ∀ c ∈ required, c.Holds p := by
  constructor
  · intro h c _
    cases c
    · exact h.age
    · exact h.riskFactor
    · exact h.risk
    · exact h.noDialysis
    · exact h.noStatin
  · intro h
    exact ⟨h .age (by decide), h .riskFactor (by decide), h .risk (by decide),
      h .noDialysis (by decide), h .noStatin (by decide)⟩

/-! ## Proof-carrying recommendations -/

/-- The two things the pathway can say. -/
inductive Output where
  | recommendStart | noRecommendation
  deriving DecidableEq

/-- `Supports p o`: the approved rule, applied to `p`, supports output `o`. Starting
needs all five proofs. Not starting needs one failed condition (in the article's
example, the dialysis exclusion), which settles the result without evaluating
every branch. -/
inductive Supports (p : Patient) : Output → Prop where
  | start (basis : Eligible p) : Supports p .recommendStart
  | noStart (c : Cond) (fails : ¬ c.Holds p) : Supports p .noRecommendation

/-- `Supports` is no weaker than it should be: the rule supports "no recommendation"
exactly when the patient is not eligible. -/
theorem supports_noRecommendation_iff (p : Patient) :
    Supports p .noRecommendation ↔ ¬ Eligible p := by
  constructor
  · intro h he
    cases h with
    | noStart c fails => exact fails ((eligible_iff p).mp he c (by cases c <;> decide))
  · intro hne
    have h : ¬ ∀ c ∈ required, c.Holds p := fun hall => hne ((eligible_iff p).mpr hall)
    simp only [Classical.not_forall] at h
    obtain ⟨c, _, fails⟩ := h
    exact .noStart c fails

/-- A recommendation that carries its proof. -/
structure Recommendation (p : Patient) where
  output : Output
  basis : Supports p output

/-! ## The article's patient -/

/-- Age 63, hypertension and dyslipidemia, estimated risk 12.4%, no current statin,
hemodialysis three times a week. -/
def patient : Patient where
  age := 63
  dyslipidemia := true
  diabetes := false
  hypertension := true
  smoking := false
  risk := 124
  onDialysis := true
  onStatin := false

/-- The complete justification, as a term: the dialysis exclusion applies. -/
def patientRecommendation : Recommendation patient where
  output := .noRecommendation
  basis := .noStart .noDialysis (by decide)

-- The justification that is silent on dialysis. Four true statements do not make a
-- wrong proof of `Eligible patient`. They make no proof: Lean names the missing field,
-- and `#guard_msgs` checks that this is the error it reports.
/-- error: Fields missing: `noDialysis` -/
#guard_msgs in
example : Eligible patient where
  age := by decide
  riskFactor := by decide
  risk := by decide
  noStatin := rfl

/-- And the missing proof cannot be supplied, by this producer or any other. -/
theorem patient_not_eligible : ¬ Eligible patient :=
  fun h => absurd h.noDialysis (by decide)

/-! ## The two checkers, as programs that read an untrusted justification -/

/-- One line of a justification: a condition and the producer's claim about it.
(The article's justification also carries values, sources and dates. This model
keeps what the table turns on.) -/
structure Line where
  cond : Cond
  claimedToHold : Bool

/-- What the producer submits. The producer chooses which conditions to mention. -/
structure Justification where
  lines : List Line
  proposes : Output

/-- What a checker answers. -/
inductive Verdict where
  | accepts
  /-- Required evidence is absent. Neither a yes nor a no. -/
  | unresolved (absent : List Cond)
  | rejects
  deriving DecidableEq

/-- Every claim in the justification agrees with the confirmed inputs. -/
def claimsMatch (p : Patient) (j : Justification) : Bool :=
  j.lines.all fun l => l.claimedToHold == decide (l.cond.Holds p)

/-- Every condition the justification lists holds for the patient, as the checker
itself evaluates it. -/
def listedHold (p : Patient) (j : Justification) : Bool :=
  j.lines.all fun l => decide (l.cond.Holds p)

/-- The required conditions the justification never mentions. -/
def missing (j : Justification) : List Cond :=
  required.filter fun c => !j.lines.any fun l => l.cond == c

/-- Checker A checks the submitted argument: its claims, and whether the proposed
output agrees with the listed results. It never asks whether the list is complete. -/
def checkerA (p : Patient) (j : Justification) : Verdict :=
  if !claimsMatch p j then .rejects else
  match j.proposes, listedHold p j with
  | .recommendStart, true => .accepts
  | .noRecommendation, false => .accepts
  | _, _ => .rejects

/-- Checker B checks the approved rule's requirements. It learns what a
recommendation to start must establish from `required`, not from the
justification. A missing condition stays unresolved. -/
def checkerB (p : Patient) (j : Justification) : Verdict :=
  if !claimsMatch p j then .rejects else
  match j.proposes, listedHold p j, missing j with
  | .recommendStart, true, [] => .accepts
  | .recommendStart, true, m => .unresolved m
  | .recommendStart, false, _ => .rejects
  | .noRecommendation, false, _ => .accepts
  | .noRecommendation, true, [] => .rejects
  | .noRecommendation, true, m => .unresolved m

/-! ## The article's table, row by row -/

def complete : Justification where
  lines := [⟨.age, true⟩, ⟨.riskFactor, true⟩, ⟨.risk, true⟩, ⟨.noDialysis, false⟩, ⟨.noStatin, true⟩]
  proposes := .noRecommendation

def silentOnDialysis : Justification where
  lines := [⟨.age, true⟩, ⟨.riskFactor, true⟩, ⟨.risk, true⟩, ⟨.noStatin, true⟩]
  proposes := .recommendStart

def wrongAboutDialysis : Justification where
  lines := [⟨.age, true⟩, ⟨.riskFactor, true⟩, ⟨.risk, true⟩, ⟨.noDialysis, true⟩, ⟨.noStatin, true⟩]
  proposes := .recommendStart

example : checkerA patient complete = .accepts := by decide
example : checkerB patient complete = .accepts := by decide

-- The middle row: every statement true, the list incomplete.
example : checkerA patient silentOnDialysis = .accepts := by decide
example : checkerB patient silentOnDialysis = .unresolved [.noDialysis] := by decide

-- Both reject the false claim for the same reason: it conflicts with the confirmed input.
example : checkerA patient wrongAboutDialysis = .rejects := by decide
example : checkerB patient wrongAboutDialysis = .rejects := by decide

-- Two edge cases the table does not show. A confirmed exclusion alone settles
-- "no recommendation". And an empty justification is enough for A to accept a
-- recommendation to start, which is the point: A never asks what should be there.
example : checkerB patient ⟨[⟨.noDialysis, false⟩], .noRecommendation⟩ = .accepts := by decide
example : checkerA patient ⟨[], .recommendStart⟩ = .accepts := by decide
example : checkerB patient ⟨[], .recommendStart⟩ = .unresolved required := by decide

/-! ## What holds for every patient and every justification -/

theorem listedHold_iff (p : Patient) (j : Justification) :
    listedHold p j = true ↔ ∀ l ∈ j.lines, l.cond.Holds p := by
  simp only [listedHold, List.all_eq_true, decide_eq_true_eq]

theorem listedHold_false_iff (p : Patient) (j : Justification) :
    listedHold p j = false ↔ ∃ l ∈ j.lines, ¬ l.cond.Holds p := by
  simp only [listedHold, List.all_eq_false, decide_eq_true_eq]

theorem missing_nil_iff (j : Justification) :
    missing j = [] ↔ ∀ c ∈ required, ∃ l ∈ j.lines, l.cond = c := by
  simp [missing]

/-- Checker B is sound: whatever it accepts, the approved rule supports. The proof
never uses the producer's claims (`claimedToHold`). They decide which producers get
rejected, not what an acceptance guarantees. -/
theorem checkerB_sound (p : Patient) (j : Justification)
    (h : checkerB p j = .accepts) : Supports p j.proposes := by
  have hc : claimsMatch p j = true := by
    cases hc : claimsMatch p j <;> simp_all [checkerB]
  cases hp : j.proposes with
  | recommendStart =>
    -- Every listed condition holds and nothing required is missing.
    have hl : listedHold p j = true := by
      cases hl : listedHold p j <;> simp_all [checkerB]
    have hm : missing j = [] := by
      cases hm : missing j <;> simp_all [checkerB]
    refine .start ((eligible_iff p).mpr fun c hc => ?_)
    obtain ⟨l, hmem, rfl⟩ := (missing_nil_iff j).mp hm c hc
    exact (listedHold_iff p j).mp hl l hmem
  | noRecommendation =>
    -- Some listed condition fails.
    have hl : listedHold p j = false := by
      cases hl : listedHold p j <;> cases hm : missing j <;> simp_all [checkerB]
    obtain ⟨l, _, hfail⟩ := (listedHold_false_iff p j).mp hl
    exact .noStart l.cond hfail

/-- So a justification that B accepts can be turned into a recommendation that
carries its proof. -/
def certify (p : Patient) (j : Justification) (h : checkerB p j = .accepts) :
    Recommendation p :=
  ⟨j.proposes, checkerB_sound p j h⟩

/-- In particular: if B accepts a recommendation to start, all five conditions hold. -/
theorem checkerB_start (p : Patient) (j : Justification)
    (h : checkerB p j = .accepts) (hs : j.proposes = .recommendStart) : Eligible p := by
  have := checkerB_sound p j h
  rw [hs] at this
  cases this with
  | start basis => exact basis

/-- The justification an honest producer would send: all five conditions, each
reported as the checker itself would evaluate it. -/
def honest (p : Patient) : Justification where
  lines := required.map fun c => ⟨c, decide (c.Holds p)⟩
  proposes := if required.all (fun c => decide (c.Holds p)) then .recommendStart else .noRecommendation

/-- B's soundness is not vacuous: it accepts the honest justification, for every
patient. -/
theorem checkerB_accepts_honest (p : Patient) : checkerB p (honest p) = .accepts := by
  have hc : claimsMatch p (honest p) = true := by simp [claimsMatch, honest]
  have hm : missing (honest p) = [] := by simp [missing, honest, required]
  have hl : listedHold p (honest p) = required.all (fun c => decide (c.Holds p)) := by
    simp [listedHold, honest, Function.comp_def]
  unfold checkerB
  rw [hc, hm, hl]
  cases h : required.all (fun c => decide (c.Holds p)) <;> simp [honest, h]

/-- For a recommendation to start, Checker A has no such guarantee. The article's
patient is the counterexample. -/
theorem checkerA_unsound :
    ∃ p j, checkerA p j = .accepts ∧ j.proposes = .recommendStart ∧ ¬ Eligible p :=
  ⟨patient, silentOnDialysis, by decide, rfl, patient_not_eligible⟩

/-! ## What this does not show -/

/-- A rule whose reviewers forgot dialysis. Lean has no objection to it. -/
structure EligibleUnderForgetfulRule (p : Patient) : Prop where
  age : Cond.age.Holds p
  riskFactor : Cond.riskFactor.Holds p
  risk : Cond.risk.Holds p
  noStatin : Cond.noStatin.Holds p

/-- Under that rule the article's patient is eligible, with a complete proof. The
soundness theorem is relative to the rule the receiving side wrote. -/
example : EligibleUnderForgetfulRule patient :=
  ⟨by decide, by decide, by decide, rfl⟩

end Part7

/-! ## What the proofs rest on

At most Lean's three standard axioms: no `sorry`, no `native_decide`.
`#guard_msgs` fails the build if that changes. -/

/-- info: 'Part7.checkerB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Part7.checkerB_sound

/-- info: 'Part7.checkerB_accepts_honest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Part7.checkerB_accepts_honest

/-- info: 'Part7.checkerA_unsound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Part7.checkerA_unsound
