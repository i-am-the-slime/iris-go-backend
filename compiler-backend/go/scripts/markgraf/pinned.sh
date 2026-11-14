# Sourced by the Markgraf gate scripts. MARKGRAF defaults to a jj workspace of
# the Markgraf repository at the revision in REVISION, so that the edits in
# progress in the Markgraf working copy never change what the gates build.
# MARKGRAF=<checkout> still overrides; pin.sh moves the pin.
#
# Environment: MARKGRAF, MARKGRAF_GATES (the pinned workspace).

MARKGRAF_GATES="${MARKGRAF_GATES:-/Users/mark/Developer/markgraf-gates}"
if [ -z "${MARKGRAF:-}" ]; then
  pinned_revision="$(cat "$(dirname "${BASH_SOURCE[0]}")/REVISION")"
  # --ignore-working-copy: concurrent gates read the workspace without each
  # snapshotting it.
  checked_out="$(jj -R "$MARKGRAF_GATES" --ignore-working-copy log --no-graph -r @- -T commit_id 2>/dev/null || true)"
  if [ "$checked_out" != "$pinned_revision" ]; then
    echo "$MARKGRAF_GATES is not at the pinned Markgraf revision $pinned_revision;" \
      "run $(dirname "${BASH_SOURCE[0]}")/pin.sh $pinned_revision" >&2
    exit 1
  fi
  MARKGRAF="$MARKGRAF_GATES"
fi
export MARKGRAF MARKGRAF_GATES
