#!/usr/bin/env bash
# Build generated certificates sequentially: their proof checks dominate memory use.
set -euo pipefail
cd "$(dirname "$0")"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-6}
lake build ToeplitzSOS
for n in {3..20}; do
  lake build "ToeplitzSOS.Certificates.Generated.N${n}"
done
lake build ToeplitzSOSRelease
