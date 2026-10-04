#!/bin/bash
# fetch.sh TAG KIND JOB: the asset of chunk job JOB of kind KIND (unpack.sh: data, the generated data modules; stmt,
# the loader modules of the job's statement) from the draft release whose tag name is TAG (GH_TOKEN with read access
# to drafts: contents write), then unpack.sh checks it against the sha256 pinned in .github/d3-pilot/ASSETS.sha256 and
# unpacks it. The data and the loader modules live only in the draft release, never in the branch: an empty TAG is
# refused.
set -euo pipefail
tag=$1; kind=$2; job=$3
case $kind in data) f=d3-pilot-$job.tar.xz ;; stmt) f=d3-pilot-$job-stmt.tar.xz ;; *) echo "unknown kind $kind"; exit 1 ;; esac
[ -n "$tag" ] || { echo "input data_release is empty: give the tag name of the draft release that holds $f"; exit 1; }
id=$(gh api --paginate "repos/$GITHUB_REPOSITORY/releases?per_page=100" \
  | jq -rs --arg t "$tag" --arg f "$f" '[add // [] | .[] | select(.tag_name == $t) | .assets[] | select(.name == $f) | .id] | first // empty')
[ -n "$id" ] || { echo "no release or draft with tag name $tag holds $f"; exit 1; }
gh api -H 'Accept: application/octet-stream' "repos/$GITHUB_REPOSITORY/releases/assets/$id" > "$RUNNER_TEMP/$f"
echo "$f: from the release with tag name $tag"
bash "$(dirname "$0")/unpack.sh" "$RUNNER_TEMP/$f" "$kind" "$job"
rm "$RUNNER_TEMP/$f"
