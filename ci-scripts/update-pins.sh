#!/usr/bin/env bash
# Checks every dependency pin against its latest upstream release, and
# optionally rewrites the ones that have moved.
#
# The pins are cmake/provision/*/pin.cmake, plus the MathSAT version and
# checksums in ci-scripts/download-mathsat.sh. A pin naming a COMMIT rather than
# a TAG is left alone.
set -euo pipefail
shopt -s inherit_errexit

root_dir=$(realpath "$(dirname "$0")/..")
provision_dir=$root_dir/cmake/provision
mathsat_script=$root_dir/ci-scripts/download-mathsat.sh
mathsat_site=https://mathsat.fbk.eu

usage() {
  cat <<EOF
Usage: $0 [<option> ...]

Shows the edits that would bring every dependency pin up to its latest
upstream release. Writes nothing unless asked to.

-h, --help      display this message and exit
-l, --list      report where every pin stands, instead of the edits
-j, --json      the same report as JSON, for the workflow
-a, --apply     make the edits
-p, --pin NAME  restrict to one pin; may be repeated
EOF
  exit 0
}

die() {
  echo "error: $*" >&2
  exit 1
}

warn() {
  echo "warning: $*" >&2
}

curl() {
  # --disable: ignore ~/.curlrc, must come first
  # --fail: abort on HTTP 4xx/5xx (without output)
  # --location: follow HTTP 3xx redirects
  # --show-error: print error messages despite the --silent
  # --silent: hide messages and progress meter
  command curl --disable --fail --location --show-error --silent "$@"
}

pin_file() {
  local pin=$1
  echo "$provision_dir/$pin/pin.cmake"
}

# Asks CMake for a pin's URL rather than recomputing it here, so that the
# mirror and the archive layouts stay defined in one place.
pin_url() {
  local dep=$1 file
  file=$(pin_file "$dep")
  cmake -P /dev/stdin <<CMAKE
include("$provision_dir/Helpers.cmake")
include("$file")
file(WRITE "/dev/stdout" "\${${dep^^}_URL}")
CMAKE
}

# One keyword of a pin, or nothing when it does not carry that keyword.
pin_value() {
  local pin=$1 keyword=$2 file
  file=$(pin_file "$pin")
  sed -n "s|^  $keyword ||p" "$file"
}

gh_api() {
  local path=$1 auth="Authorization:"
  if [[ -n ${GITHUB_TOKEN-} ]]; then
    auth="Authorization: Bearer $GITHUB_TOKEN"
  fi
  curl --no-fail --retry 3 --max-time 30 \
    -H "Accept: application/vnd.github+json" \
    -H "X-GitHub-Api-Version: 2022-11-28" -H "$auth" \
    "https://api.github.com/$path"
}

latest_release_tag() {
  local repo=$1 body tag message
  body=$(gh_api "repos/$repo/releases/latest")
  tag=$(jq -r '.tag_name // empty' <<<"$body")
  if [[ -z $tag ]]; then
    message=$(jq -r '.message // "no release"' <<<"$body")
    warn "$repo: $message"
  fi
  echo "$tag"
}

# The newest release tarball in a GNU project's mirror directory.
latest_gnu_version() {
  local project=$1 url listing
  url=$(pin_url "$project")
  listing=$(curl --max-time 30 "${url%/*}/")
  sed -n "s|.*$project-\([^\"<> ]*\)\.tar\.gz.*|\1|p" <<<"$listing" |
    highest_version
}

highest_version() {
  sort -V | tail -1
}

newer_of() {
  printf '%s\n%s\n' "$1" "$2" | highest_version
}

# Emit a message if candidate version is older than current or incomparable.
check_candidate() {
  local current=$1 candidate=$2 prefix from to winner
  prefix=${current%%[0-9]*}
  if [[ $candidate != "$prefix"[0-9]* ]]; then
    echo "upstream '$candidate' is not shaped like '$current'"
    return
  fi
  from=${current#"$prefix"}
  to=${candidate#"$prefix"}
  winner=$(newer_of "$from" "$to")
  if [[ $winner != "$to" ]]; then
    echo "upstream '$candidate' is older than pinned '$current'"
  fi
}

replace_line() {
  local file=$1 prefix=$2 value=$3 count escaped
  if [[ -z $value ]]; then
    die "$file: refusing to write an empty value"
  fi
  escaped=${value//\\/\\\\} # \ begins an escape, so it goes first
  escaped=${escaped//&/\\&} # & stands for the whole match
  escaped=${escaped//|/\\|} # | ends the replacement
  count=$(grep -c -E "^$prefix" "$file") || count=0
  if ((count != 1)); then
    die "$file: '$prefix' matched $count lines in $file, expected 1"
  fi
  sed -i -E "s|^($prefix).*|\\1$escaped|" "$file"
}

# checksum_linux_x86_64 holds the hash for linux-x86_64: the first
# underscore stands for the dash, the rest belong to the architecture.
mathsat_platforms() {
  sed -n \
    -e 's|^checksum_\([a-z0-9]*\)_\(.*\)=[0-9a-f]\{64\}$|\1-\2|p' \
    -e 's|^checksum_\([a-z0-9]*\)=[0-9a-f]\{64\}$|\1|p' \
    "$mathsat_script"
}

mathsat_archive_url() {
  local version=$1 platform=$2
  echo "$mathsat_site/release/mathsat-$version-$platform.tar.gz"
}

# The download page always lists only the latest release, so it can be used as
# the source of truth. Every archive's URL is checked to make sure it is valid.
latest_mathsat_version() {
  local page newest platforms platform url code
  page=$(curl --max-time 30 "$mathsat_site/download.html")
  newest=$(
    sed -n 's|.*mathsat-\([0-9][^-]*\)-.*|\1|p' <<<"$page" | highest_version
  )
  if [[ -z $newest ]]; then
    return
  fi
  platforms=$(mathsat_platforms)
  while read -r platform; do
    url=$(mathsat_archive_url "$newest" "$platform")
    code=$(curl --no-fail --max-time 30 --head --output /dev/null \
      --write-out '%{http_code}' "$url")
    if [[ $code != 200 ]]; then
      warn "mathsat: the page offers $newest but $platform answered $code"
      return
    fi
  done <<<"$platforms"
  echo "$newest"
}

# Rewrites a provisioned pin's TAG or VERSION, then has CMake record the
# checksum of whatever the new URL serves.
apply_provisioned() {
  local pin=$1 file=$2 prefix=$3 value=$4
  replace_line "$file" "$prefix" "$value"
  cmake -P "$provision_dir/update-checksums.cmake" "$pin"
}

# Rewrites the MathSAT version, then every platform's checksum. Those
# have to be computed here: update-checksums.cmake knows only the pins it
# can reach through smt_switch_pin.
apply_mathsat() {
  local version=$1 platforms platform url sum
  replace_line "$mathsat_script" 'version=' "$version"
  platforms=$(mathsat_platforms)
  while read -r platform; do
    url=$(mathsat_archive_url "$version" "$platform")
    sum=$(curl --max-time 300 "$url" | sha256sum)
    replace_line "$mathsat_script" "checksum_${platform//-/_}=" "${sum%% *}"
  done <<<"$platforms"
}

# Shows the line this would rewrite, without writing it.
show_edit() {
  local file=$1 prefix=$2 value=$3 old
  old=$(grep -E "^$prefix" "$file")
  printf '%s\n-%s\n+%s%s\n' "${file#"$root_dir/"}" "$old" "$prefix" "$value"
  echo "  its checksum is recorded afterwards, on --apply"
}

# Turns a verdict about a pin into whatever the mode asks for: a row of
# JSON, a line of prose, a diff, or the edit itself.
record() {
  local pin=$1 status=$2 current=$3 latest=$4 file=${5-} prefix=${6-}
  if [[ $mode == json ]]; then
    rows+=$(jq -cn --arg pin "$pin" --arg current "$current" \
      --arg latest "$latest" --arg status "$status" \
      '{pin: $pin, current: $current, latest: $latest, status: $status}')
    rows+=$'\n'
    return
  fi
  case $status in
    failed) ;; # specific warnings are emitted before calling record
    held)
      if [[ $mode == list ]]; then
        echo "$pin: held at a commit, not checked"
      fi
      ;;
    current)
      if [[ $mode == list ]]; then
        echo "$pin: $current is current"
      fi
      ;;
    behind)
      case $mode in
        list) echo "$pin: $current -> $latest" ;;
        show) show_edit "$file" "$prefix" "$latest" ;;
        apply)
          echo "$pin: $current -> $latest"
          if [[ $pin == mathsat ]]; then
            apply_mathsat "$latest"
          else
            apply_provisioned "$pin" "$file" "$prefix" "$latest"
          fi
          ;;
        *) die "unreachable mode '$mode'" ;;
      esac
      ;;
    *) die "unreachable status '$status'" ;;
  esac
}

# Reports one pin, and edits it when it is behind.
handle_pin() {
  local pin=$1 file prefix keyword current latest commit tag version
  local project repo errmsg

  if [[ $pin == mathsat ]]; then
    file=$mathsat_script
    prefix='version='
    current=$(sed -n 's|^version=||p' "$file")
  else
    file=$(pin_file "$pin")
    commit=$(pin_value "$pin" COMMIT)
    if [[ -n $commit ]]; then
      record "$pin" held "$commit" "$commit"
      return
    fi
    tag=$(pin_value "$pin" TAG)
    version=$(pin_value "$pin" VERSION)
    if [[ -n $tag ]]; then
      keyword=TAG
      current=$tag
    elif [[ -n $version ]]; then
      keyword=VERSION
      current=$version
    else
      warn "$pin: names neither a TAG, a COMMIT nor a VERSION"
      record "$pin" failed "" ""
      failed=true
      return
    fi
    prefix="  $keyword "
  fi

  if [[ $pin == mathsat ]]; then
    latest=$(latest_mathsat_version)
  elif [[ $keyword == VERSION ]]; then
    project=$(pin_value "$pin" GNU_PROJECT)
    latest=$(latest_gnu_version "$project")
  else
    repo=$(pin_value "$pin" GITHUB_REPO)
    latest=$(latest_release_tag "$repo")
  fi
  if [[ -z $latest ]]; then
    warn "$pin: could not find the latest version upstream"
    record "$pin" failed "$current" ""
    failed=true
    return
  fi

  errmsg=$(check_candidate "$current" "$latest")
  if [[ -n $errmsg ]]; then
    warn "$pin: $errmsg"
    record "$pin" failed "$current" "$latest"
    failed=true
    return
  fi

  if [[ $latest == "$current" ]]; then
    record "$pin" current "$current" "$latest"
    return
  fi

  record "$pin" behind "$current" "$latest" "$file" "$prefix"
}

pins=()
declare -A known=()
for path in "$provision_dir"/*/pin.cmake; do
  directory=${path%/*}
  pins+=("${directory##*/}")
  known[${directory##*/}]=1
done
pins+=(mathsat)
known[mathsat]=1

mode=show
selected=()
while (($# > 0)); do
  case $1 in
    -h | --help) usage ;;
    -l | --list) mode=list ;;
    -j | --json) mode=json ;;
    -a | --apply) mode=apply ;;
    -p | --pin)
      if (($# < 2)); then
        die "$1 needs the name of a pin"
      fi
      if [[ ! -v known[$2] ]]; then
        die "there is no pin named '$2'"
      fi
      selected+=("$2")
      shift
      ;;
    *) die "unexpected argument: $1" ;;
  esac
  shift
done
if ((${#selected[@]} == 0)); then
  selected=("${pins[@]}")
fi

rows=""
failed=false
for pin in "${selected[@]}"; do
  handle_pin "$pin"
done

if [[ $mode == json ]]; then
  jq -cs . <<<"$rows"
fi

if [[ $failed == true ]]; then
  die "could not check every pin"
fi
