#!/usr/bin/env bash
# Compile the files of this folder against the built tree one level up.
# Prerequisite: the tree is configured and built with `make` (see ../README.md).
# security/BacktranslationProof2.v is not in the Makefile, so this script
# compiles it first if needed. The output of the Print Assumptions commands
# goes to stdout.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "${HERE}/.." && pwd)"
COQC="${COQBIN:-}coqc"
read -r -a INCS <<< "$(make -s -C "${ROOT}" print-includes)"

cd "${ROOT}"
if [ ! -f security/BacktranslationProof2.vo ] || [ security/BacktranslationProof2.v -nt security/BacktranslationProof2.vo ]; then
  echo "=== coqc security/BacktranslationProof2.v"
  "${COQC}" -q "${INCS[@]}" security/BacktranslationProof2.v
fi

cd "${HERE}"
for f in StepFixChecks.v StepFixFixCommon.v StepFixFixCheckpub.v StepFixFixCallsig.v \
         StepFixFixBuiltinRes.v StepFixFixEccMemcpy.v StepFixFixMain.v \
         InitMemPublic.v AsmToClightStepFix.v; do
  echo "=== coqc stepfix/${f}"
  (cd "${ROOT}" && "${COQC}" -q "${INCS[@]}" -R stepfix StepFixFix "stepfix/${f}")
done
