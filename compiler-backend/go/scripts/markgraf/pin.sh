#!/usr/bin/env bash
#
# Pins the Markgraf revision the gates build: checks REVISION out in the jj
# workspace the gate scripts default to, clones the Spago, npm and Cargo caches
# into it from the Markgraf checkout, and records the commit in REVISION.
#
#   compiler-backend/go/scripts/markgraf/pin.sh <revision>   # move the pin
#   compiler-backend/go/scripts/markgraf/pin.sh              # restore the recorded pin
#
# Moving the pin is a deliberate change of what the gates measure: run the
# gates on the new revision and commit REVISION with the change that needs it.
#
# Environment: MARKGRAF_REPOSITORY (the Markgraf checkout; only read),
# MARKGRAF_GATES (the pinned workspace).

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPOSITORY="${MARKGRAF_REPOSITORY:-/Users/mark/Developer/markgraf}"
GATES="${MARKGRAF_GATES:-/Users/mark/Developer/markgraf-gates}"
revision="${1:-$(cat "$HERE/REVISION")}"

# --ignore-working-copy: the Markgraf checkout is someone's work in progress.
# Creating a workspace cannot skip it; jj then snapshots the checkout once, as
# any jj command run there does, without changing a file.
commit="$(jj -R "$REPOSITORY" --ignore-working-copy log --no-graph -r "exactly($revision, 1)" -T commit_id)"
if [ ! -d "$GATES/.jj" ]; then
  jj -R "$REPOSITORY" workspace add --name "$(basename "$GATES")" "$GATES" >/dev/null 2>&1
fi
# Operations in other workspaces of the repository can leave this one stale.
jj -R "$GATES" workspace update-stale >/dev/null 2>&1
jj -R "$GATES" new "$commit" >/dev/null 2>&1
if [ -n "$(jj -R "$GATES" diff --summary)" ]; then
  echo "$GATES has changes on top of $commit" >&2
  exit 1
fi

# APFS clones: the caches cost no space until either copy changes. A later
# revision's Spago and npm steps fetch what its lock files add.
for cache in .spago cli/.spago cli/target npm/node_modules node_modules; do
  if [ -d "$REPOSITORY/$cache" ] && [ ! -e "$GATES/$cache" ]; then
    cp -c -R "$REPOSITORY/$cache" "$GATES/$cache"
  fi
done

echo "$commit" > "$HERE/REVISION"
echo "Markgraf gates pinned to $commit in $GATES"
