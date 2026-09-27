import Goudlokje.Exercise
import Goudlokje.Finding
import Goudlokje.Probe

/-!
# Shortcuts

Finds *shortcuts*: steps where a probe tactic (`goudlokje.probes`) closes the goal before the proof
is over, which suggests the exercise is too easy.

Only steps that do not close their goal themselves are probed (the student has to write a step
there anyway). The probed steps form goal chains (see `goalChains`); per chain only the first step
in an input area at which some probe succeeds is reported, together with every probe that succeeds
there.
-/

namespace Goudlokje.Checks

open Lean Elab Command

/-- The shortcuts in `e`, or `none` if no probes are configured. -/
def shortcuts (e : Exercise) : CommandElabM (Option (Array Issue)) := do
  let opts ← getOptions
  let probes ← match parseProbes (← getEnv) (goudlokje.probes.get opts) with
    | .ok probes => pure probes
    | .error msg => logErrorAt e.stx msg; return none
  if probes.isEmpty then return none
  let heartbeats := goudlokje.probeHeartbeats.get opts
  let mut issues : Array Issue := #[]
  let mut cache : ProbeCache := {}
  for chain in goalChains e.steps do
    for step in chain do
      unless e.inInputArea step do continue
      let mut closing := #[]
      for probe in probes do
        let (outcome, cache') ← (runProbeCached step probe heartbeats).run cache
        cache := cache'
        if outcome == .closed then closing := closing.push probe
      unless closing.isEmpty do
        issues := issues ++ closing.map fun probe => {
          check := .shortcut, step, ref := step.stx, tactic? := probe.name
          message := m!"`{probe.name}` closes the goal at step {e.stepNumber step} of exercise \
            {repr e.name}, so the rest of this part of the proof can be skipped" }
        break
  return issues

end Goudlokje.Checks
