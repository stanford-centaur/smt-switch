#!/usr/bin/env bash
# Works out, for the CI workflow's queue job, whether a merge queue commit
# was already tested, and if so writes tested=true to $GITHUB_OUTPUT.
set -euo pipefail

: "${GITHUB_OUTPUT:?}" "${GITHUB_REPOSITORY:?}" "${GITHUB_REF:?}"
: "${GITHUB_SHA:?}" "${CHECK_NAME:?}"
repo=repos/$GITHUB_REPOSITORY

# The queue names its branches gh-readonly-queue/<base>/pr-<number>-<sha>,
# after the last pull request in the group.
if [[ ! $GITHUB_REF =~ /pr-([0-9]+)-[0-9a-f]+$ ]]; then
  echo "untested: $GITHUB_REF names no pull request"
  exit 0
fi
pr=${BASH_REMATCH[1]}
pr_head=$(gh api "$repo/pulls/$pr" --jq .head.sha)
pr_tree=$(gh api "$repo/git/commits/$pr_head" --jq .tree.sha)
this_tree=$(gh api "$repo/git/commits/$GITHUB_SHA" --jq .tree.sha)
if [[ $this_tree != "$pr_tree" ]]; then
  echo "untested: the tree differs from that of #$pr's head $pr_head"
  exit 0
fi

passed=$(
  gh api -X GET "$repo/commits/$pr_head/check-runs" \
    -f check_name="$CHECK_NAME" \
    --jq '[.check_runs[] | select(.conclusion == "success")] | length'
)
if ((passed == 0)); then
  echo "untested: $CHECK_NAME has not passed on #$pr's head $pr_head"
  exit 0
fi

echo "tested: the tree is that of #$pr's head $pr_head where $CHECK_NAME passed"
echo "tested=true" >>"$GITHUB_OUTPUT"
