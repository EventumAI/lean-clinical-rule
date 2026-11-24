import Lean.Data.Json

/-!
# Two checkers, one policy

The Part 7 statin pathway, split into the part a proof checker can settle and the
part it cannot.

* Lean checks the rule's logic: given a report of what is established about each
  condition, it decides, and for every report that is true of the patient the
  decision is proved right.
* Whether a note really establishes a fact (is dialysis documented, is it about
  this patient, is it current) is not something Lean can see. That is the evidence
  layer's job. In the demo a cheap typed judge (Jev) does it, and anything it is
  not sure of is reported as `unresolved`.

The theorems below make the split exact. `Report.SoundFor` is the evidence layer's
whole obligation: what it reports as settled must be true of the patient. Under
that one assumption a recommendation to start implies the patient is eligible and
"no recommendation" implies the patient is not. `unresolved` makes no claim about
the patient; it lists exactly the conditions that are open. Without any
assumption, a recommendation to start is issued exactly when all five conditions
are reported as holding, so the procedure cannot pass by always answering
"unresolved", and never starts while a condition is unresolved.

The JSON layer at the bottom is ordinary code and is not part of what is proved.
An evidence object with a repeated key follows Lean's JSON parser (the last value
wins); the demo's driver never writes one.

Run: `lean --run TwoCheckers.lean < cases.json` (reads a JSON array of
`{"id": ..., "evidence": {"age": "holds" | "fails" | "unresolved", ...}}`).
Core Lean 4 and the `Lean` JSON library; no Mathlib. Checked with Lean 4.35.0.
-/

namespace TwoCheckers

/-! ## The approved rule (as in the Part 7 file) -/

structure Patient where
  age : Nat
  dyslipidemia : Bool
  diabetes : Bool
  hypertension : Bool
  smoking : Bool
  /-- Estimated ten-year cardiovascular risk, in tenths of a percent. -/
  risk : Nat
  onDialysis : Bool
  onStatin : Bool

inductive Cond where
  | age | riskFactor | risk | noDialysis | noStatin
  deriving DecidableEq, Repr

def Cond.Holds (p : Patient) : Cond → Prop
  | .age => 40 ≤ p.age ∧ p.age ≤ 75
  | .riskFactor => p.dyslipidemia ∨ p.diabetes ∨ p.hypertension ∨ p.smoking
  | .risk => 100 ≤ p.risk
  | .noDialysis => p.onDialysis = false
  | .noStatin => p.onStatin = false

structure Eligible (p : Patient) : Prop where
  age : Cond.age.Holds p
  riskFactor : Cond.riskFactor.Holds p
  risk : Cond.risk.Holds p
  noDialysis : Cond.noDialysis.Holds p
  noStatin : Cond.noStatin.Holds p

def required : List Cond := [.age, .riskFactor, .risk, .noDialysis, .noStatin]

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

/-! ## What the evidence layer reports -/

/-- What is established about one condition. `unresolved` covers silence, a
statement about someone else, a stale statement, and a judge that is not sure. -/
inductive Evidence where
  | holds | fails | unresolved
  deriving DecidableEq, Repr

/-- The evidence layer's report: one `Evidence` per condition. -/
abbrev Report := Cond → Evidence

/-- The evidence layer's whole obligation: whatever it reports as settled is true
of the patient. It may leave anything unresolved. Lean cannot check this; it is
the assumption the theorems are stated under. -/
def Report.SoundFor (r : Report) (p : Patient) : Prop :=
  ∀ c, (r c = .holds → c.Holds p) ∧ (r c = .fails → ¬ c.Holds p)

/-! ## The decision procedure -/

inductive Decision where
  | recommendStart
  /-- The pathway does not recommend starting: these conditions are reported as failing. -/
  | noRecommendation (conds : List Cond)
  /-- Neither: these conditions are reported as unresolved, and none as failing. -/
  | unresolved (pending : List Cond)
  deriving DecidableEq, Repr

def failed (r : Report) : List Cond := required.filter fun c => r c == .fails
def unsettled (r : Report) : List Cond := required.filter fun c => r c == .unresolved

/-- An established failure settles the answer. Otherwise every condition must be
established before a start is recommended. -/
def decision (r : Report) : Decision :=
  match failed r, unsettled r with
  | [], [] => .recommendStart
  | [], o => .unresolved o
  | f, _ => .noRecommendation f

/-! ## What Lean proves about it -/

theorem failed_nil_iff (r : Report) : failed r = [] ↔ ∀ c ∈ required, r c ≠ .fails := by
  simp [failed]

theorem unsettled_nil_iff (r : Report) : unsettled r = [] ↔ ∀ c ∈ required, r c ≠ .unresolved := by
  simp [unsettled]

theorem decision_eq_start (r : Report) :
    decision r = .recommendStart ↔ failed r = [] ∧ unsettled r = [] := by
  unfold decision
  split <;> simp_all

/-- With no assumption at all about the evidence: a start is recommended only when
every one of the five conditions is reported as holding. -/
theorem start_needs_all (r : Report) (h : decision r = .recommendStart) :
    ∀ c ∈ required, r c = .holds := by
  obtain ⟨hf, hu⟩ := (decision_eq_start r).mp h
  intro c hc
  have h1 := (failed_nil_iff r).mp hf c hc
  have h2 := (unsettled_nil_iff r).mp hu c hc
  cases h : r c with
  | holds => rfl
  | fails => exact absurd h h1
  | unresolved => exact absurd h h2

/-- And the other way round: when all five are reported as holding, a start is
recommended. The procedure does not hide behind "unresolved". -/
theorem start_iff (r : Report) :
    decision r = .recommendStart ↔ ∀ c ∈ required, r c = .holds := by
  refine ⟨start_needs_all r, fun h => ?_⟩
  have hf : failed r = [] := (failed_nil_iff r).mpr fun c hc => by simp [h c hc]
  have hu : unsettled r = [] := (unsettled_nil_iff r).mpr fun c hc => by simp [h c hc]
  simp [decision, hf, hu]

/-- "No recommendation" is returned exactly when some condition is reported as
failing, and it lists exactly those conditions. -/
theorem decision_noRecommendation_iff (r : Report) (f : List Cond) :
    decision r = .noRecommendation f ↔ failed r = f ∧ f ≠ [] := by
  unfold decision
  split <;> simp_all <;> (rintro rfl; assumption)

/-- "Unresolved" is returned exactly when nothing is reported as failing and
something is unresolved, and it lists exactly the unresolved conditions. -/
theorem decision_unresolved_iff (r : Report) (o : List Cond) :
    decision r = .unresolved o ↔ failed r = [] ∧ unsettled r = o ∧ o ≠ [] := by
  unfold decision
  split <;> simp_all <;> (rintro rfl; assumption)

/-- If the evidence is sound for the patient, a recommendation to start is right:
the patient is eligible. -/
theorem start_sound (r : Report) (p : Patient) (hs : r.SoundFor p)
    (h : decision r = .recommendStart) : Eligible p :=
  (eligible_iff p).mpr fun c hc => (hs c).1 (start_needs_all r h c hc)

/-- If the evidence is sound for the patient, "no recommendation" is right: the
patient is not eligible. -/
theorem noRecommendation_sound (r : Report) (p : Patient) (hs : r.SoundFor p)
    (f : List Cond) (h : decision r = .noRecommendation f) : ¬ Eligible p := by
  have hne : failed r ≠ [] := fun hf => by
    cases hu : unsettled r <;> simp [decision, hf, hu] at h
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
  have hmem : c ∈ required ∧ r c = .fails := by simpa [failed] using hc
  intro he
  exact (hs c).2 hmem.2 ((eligible_iff p).mp he c hmem.1)

/-- One unresolved condition is enough to stop a recommendation to start. -/
theorem unresolved_blocks_start (r : Report) (c : Cond) (hc : c ∈ required)
    (hu : r c = .unresolved) : decision r ≠ .recommendStart :=
  fun h => by simpa [hu] using start_needs_all r h c hc

/-- When the evidence is sound and leaves nothing unresolved, the procedure is
complete as well as sound: it recommends starting exactly when the patient is
eligible. -/
theorem exact_complete (r : Report) (p : Patient) (hs : r.SoundFor p)
    (hx : ∀ c, r c ≠ .unresolved) : decision r = .recommendStart ↔ Eligible p := by
  refine ⟨fun h => start_sound r p hs h, fun he => (start_iff r).mpr fun c _ => ?_⟩
  have := (eligible_iff p).mp he c (by cases c <;> simp [required])
  cases h : r c
  · rfl
  · exact absurd this ((hs c).2 h)
  · exact absurd h (hx c)

end TwoCheckers

/-! ## The executable: reports in, decisions out -/

open Lean TwoCheckers

def condName : Cond → String
  | .age => "age" | .riskFactor => "riskFactor" | .risk => "risk"
  | .noDialysis => "noDialysis" | .noStatin => "noStatin"

def parseEvidence (j : Json) (key : String) : Except String Evidence := do
  let str ← (← j.getObjVal? key).getStr? |>.mapError (s!"{key}: " ++ ·)
  match str with
  | "holds" => pure .holds
  | "fails" => pure .fails
  | "unresolved" => pure .unresolved
  | s => throw s!"{key}: unknown evidence value {s}"

def parseReport (j : Json) : Except String Report := do
  let a ← parseEvidence j "age"
  let rf ← parseEvidence j "riskFactor"
  let r ← parseEvidence j "risk"
  let d ← parseEvidence j "noDialysis"
  let s ← parseEvidence j "noStatin"
  pure fun
    | .age => a | .riskFactor => rf | .risk => r | .noDialysis => d | .noStatin => s

def decisionJson (id : String) : Decision → Json
  | .recommendStart => Json.mkObj [("id", id), ("decision", "recommend_start"), ("conditions", Json.arr #[])]
  | .noRecommendation f =>
    Json.mkObj [("id", id), ("decision", "no_recommendation"), ("conditions", Json.arr (f.map (Json.str ∘ condName)).toArray)]
  | .unresolved o =>
    Json.mkObj [("id", id), ("decision", "unresolved"), ("conditions", Json.arr (o.map (Json.str ∘ condName)).toArray)]

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input with
  | .error e => throw (IO.userError s!"input is not JSON: {e}")
  | .ok j =>
    match j.getArr? with
    | .error e => throw (IO.userError s!"input must be a JSON array: {e}")
    | .ok cases =>
      let mut n := 0
      for c in cases do
        n := n + 1
        -- a case without a string id is named by its position in the input
        let id := (c.getObjValAs? String "id").toOption.getD s!"#{n}"
        match (c.getObjVal? "evidence") >>= parseReport with
        | .ok r => IO.println (decisionJson id (decision r)).compress
        | .error e => IO.println (Json.mkObj [("id", id), ("error", e)]).compress
