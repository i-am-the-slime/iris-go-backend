#!/usr/bin/env bash
set -euo pipefail

verification_directory="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$verification_directory/../../../.agents/scripts/tlc.sh" "$verification_directory" EventLoop.tla

invariants=(
  OnePureScriptRunner
  BatonHolderIsKnown
  AwaitWaitsForEveryone
)

write_config() {
  local name="$1" mutation="$2"
  local config="$scratch_directory/$name.cfg"
  {
    echo "CONSTANTS"
    echo "    Mutation = \"$mutation\""
    echo "SPECIFICATION Spec"
    for invariant in "${invariants[@]}"; do
      echo "INVARIANT $invariant"
    done
  } > "$config"
  echo "$config"
}

ensure_tools
echo "Properties that must hold:"
expect_pass "EventLoop" "$(write_config EventLoop None)"

echo
echo "Mutations that must be caught:"
expect_violation "mutant-TurnSkipsBaton" "$(write_config TurnSkipsBaton TurnSkipsBaton)" \
  "Invariant OnePureScriptRunner is violated"
expect_violation "mutant-ResolverRunsFiber" "$(write_config ResolverRunsFiber ResolverRunsFiber)" \
  "Invariant OnePureScriptRunner is violated"
expect_violation "mutant-LostWakeup" "$(write_config LostWakeup LostWakeup)" \
  "Invariant AwaitWaitsForEveryone is violated|Deadlock reached"
expect_violation "mutant-NoHold" "$(write_config NoHold NoHold)" \
  "Invariant AwaitWaitsForEveryone is violated"

finish_checks
