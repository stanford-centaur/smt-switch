#!/usr/bin/env bash
# Works out, for the CI workflow's plan job, which solver builds are missing
# from the cache, and writes to $GITHUB_OUTPUT:
#
#   build    the missing ones, as {solver, runner} objects, the matrix of the
#            deps job; solver first, so that its job names list it first
#   entries  every solver's {solver, key, path} for each runner, which the
#            full build restores and enables
#
# RUNNERS and SOLVERS are whitespace-separated lists. An entry only counts if
# it was saved on this run's ref or on the default branch, the only ones
# whose caches this run can restore.
set -euo pipefail

: "${GITHUB_OUTPUT:?}" "${GITHUB_REPOSITORY:?}" "${GITHUB_REF:?}"
: "${DEFAULT_BRANCH:?}" "${RUNNERS:?}" "${SOLVERS:?}"

# Split on any whitespace, so the lists may be written one item per line.
read -r -d '' -a runners < <(printf '%s\0' "$RUNNERS")
read -r -d '' -a solvers < <(printf '%s\0' "$SOLVERS")

cd "$(dirname "$0")/.."

# Prints how many restorable entries have exactly this key.
count_cached() {
  local key=$1
  # The API matches keys by prefix, hence the comparison here.
  gh api -X GET "repos/$GITHUB_REPOSITORY/actions/caches" \
    -f key="$key" -f per_page=100 |
    jq --arg key "$key" --arg ref "$GITHUB_REF" \
      --arg main "refs/heads/$DEFAULT_BRANCH" \
      '[.actions_caches[]
        | select(.key == $key and (.ref == $ref or .ref == $main))]
       | length'
}

entries='{}'
build='[]'
for runner in "${runners[@]}"; do
  for solver in "${solvers[@]}"; do
    entry=$(ci-scripts/compute-dep-cache-entry.sh "$runner" "$solver")
    entry=$(jq -c --arg solver "$solver" '{solver: $solver} + .' <<<"$entry")
    key=$(jq -r .key <<<"$entry")
    entries=$(
      jq -c --arg runner "$runner" --argjson entry "$entry" \
        '.[$runner] += [$entry]' <<<"$entries"
    )
    count=$(count_cached "$key")
    if ((count > 0)); then
      echo "cached: $key"
    else
      echo "missing: $key"
      build=$(
        jq -c --arg solver "$solver" --arg runner "$runner" \
          '. + [{solver: $solver, runner: $runner}]' <<<"$build"
      )
    fi
  done
done

{
  echo "build=$build"
  echo "entries=$entries"
} >>"$GITHUB_OUTPUT"
