#!/usr/bin/env bash
#
# Fill in the address of the repository.
#
# Until the repository is published, the files that have to name it use the placeholders
# `<owner>` and `<repository>`.  Run this script once, from the root of the repository,
# with the GitHub owner and repository name:
#
#     scripts/set-repository-url.sh my-user AbstractVoronoi
#
# It replaces the placeholders everywhere (README, CITATION.cff, the documentation and the
# workflows), uncomments the `repository-code:` line of `CITATION.cff` and the CI badge of
# `README.md`, and prints the files it changed.  Review the diff before committing.

set -euo pipefail

if [ "$#" -ne 2 ]; then
  echo "usage: $0 <owner> <repository>" >&2
  exit 2
fi

owner="$1"
repo="$2"

if [ ! -f lakefile.toml ] || [ ! -f README.md ]; then
  echo "error: run this script from the root of the repository" >&2
  exit 2
fi

files=$(grep -rl -e '<owner>' -e '<repository>' \
          --exclude-dir=.git --exclude-dir=.lake --exclude-dir=docbuild/.lake \
          . || true)

if [ -z "$files" ]; then
  echo "nothing to do: no placeholder left"
  exit 0
fi

for f in $files; do
  # The script itself documents the placeholders; leave it alone.
  case "$f" in
    ./scripts/set-repository-url.sh) continue ;;
  esac
  sed -i "s|<owner>|$owner|g; s|<repository>|$repo|g" "$f"
  echo "updated $f"
done

# Reveal the two lines that are only meaningful once the address is known: the
# `repository-code:` field of the citation metadata and the CI badge of the README.
sed -i 's|^# repository-code: |repository-code: |' CITATION.cff
sed -i '/^<!-- BADGE-START/d; /^BADGE-END -->$/d' README.md

echo
echo "done; check the result with 'git diff' before committing"
