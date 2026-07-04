import Eureka

/-!
Axiom audit: every headline theorem is checked to depend on no axioms at all.
Run with `lake env lean Audit.lean` (also enforced by `#guard_msgs` at build
time when this file is elaborated).
-/

/-- info: 'Eureka.discovery_sound' does not depend on any axioms -/
#guard_msgs in #print axioms Eureka.discovery_sound

/-- info: 'Eureka.discovery_provenance' does not depend on any axioms -/
#guard_msgs in #print axioms Eureka.discovery_provenance

/-- info: 'Eureka.ruleGated_heuristics_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms Eureka.ruleGated_heuristics_invariant

/-- info: 'Eureka.UngatedCollapse.ungated_reaches_unsound' does not depend on any axioms -/
#guard_msgs in #print axioms Eureka.UngatedCollapse.ungated_reaches_unsound

/-- info: 'Eureka.UngatedCollapse.gated_immune' does not depend on any axioms -/
#guard_msgs in #print axioms Eureka.UngatedCollapse.gated_immune

/-- info: 'Eureka.concept_birth_conservative' does not depend on any axioms -/
#guard_msgs in #print axioms Eureka.concept_birth_conservative

/-- info: 'Eureka.concept_birth_sound' does not depend on any axioms -/
#guard_msgs in #print axioms Eureka.concept_birth_sound

/-- info: 'Eureka.defGated_sound' does not depend on any axioms -/
#guard_msgs in #print axioms Eureka.defGated_sound

/-- info: 'Eureka.defGated_concepts_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms Eureka.defGated_concepts_invariant
