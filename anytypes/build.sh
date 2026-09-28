#!/usr/bin/env bash
# Compile the files of this folder against a built tree, and print the
# axioms of the main results.
#   anytypes/build.sh [TREE]
#       ccs-main + PR #18 (by default the tree one level up): AnyTypes.v,
#       AnyTypesExtra.v, NoAnyExternals.v, RecompNoAny.v, RecompNoAnyClosed.v
#   anytypes/build.sh --bt TREE
#       a built tree of ccs-backtranslation + PR #19: the files in
#       ccs-backtranslation/
# The tree must be configured and built with `make`. Build products are
# written next to the .v files.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
COQC="${COQBIN:-}coqc"
if [ "${1:-}" = "--bt" ]; then
  TREE="$(cd "$2" && pwd)"; DIR="${HERE}/ccs-backtranslation"
  FILES="AnyTypesBT.v AnyTypesExtraBT.v PrintAssumptionsBT.v"
else
  TREE="$(cd "${1:-${HERE}/..}" && pwd)"; DIR="${HERE}"
  FILES="AnyTypes.v AnyTypesExtra.v NoAnyExternals.v RecompNoAny.v RecompNoAnyClosed.v PrintAssumptions.v"
fi
INCS=()
for d in $(make -s -C "${TREE}" print-includes | sed -e 's/-R //g' -e 's/ /\n/g' | paste - - | tr '\t' ':'); do
  INCS+=(-R "${TREE}/${d%%:*}" "${d##*:}")
done
cd "${DIR}"
for f in ${FILES}; do
  echo "=== coqc ${f}"
  "${COQC}" -q "${INCS[@]}" -R . anytypes "${f}"
done
