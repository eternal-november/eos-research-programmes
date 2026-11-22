#!/usr/bin/env bash
# Focused only: run from a checkout with its pinned Lake environment hydrated.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
if [[ ${INSIDE_NATIVE_CHECK:-0} != 1 ]]; then
  export INSIDE_NATIVE_CHECK=1
  exec lake env bash "$root/checks/native-dependent-fubini.sh"
fi
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
mkdir "$tmp/ContextualComposition"
export LEAN_PATH="$tmp:${LEAN_PATH:-}"
lean --version
sources="OppositeTypeFamilies NativeFinitePush DependentFibre AddressedFubini RectangularFibre DependentCarrier NativePartition DependentAugmentation FubiniIso GlobalAugmentation DependentComposition DistributorShuffle RaggedFubini ReverseTypeRig NativeFibreAdapter AbsorbingZero OppositeNativeBridge RigGrid RigGridMonoidal RigGridNativeAdapter NativeRouteReduction ReverseNativeRoutes PartitionInverse AddressedChartNaturality ReverseFlatCoherence RawDependentAddresses"
for n in $sources; do
  lean -DwarningAsError=true -o "$tmp/ContextualComposition/$n.olean" "ContextualComposition/$n.lean"
done
for n in NativeDependentFubiniAudit NativeParityBoundary RigGridNativeAdapterAudit NativeRouteAudit; do
  lean -DwarningAsError=true "checks/$n.lean" | tee -a "$tmp/audit"
done
if grep -E 'sorryAx|implementedBy|unsafeCast' "$tmp/audit"; then exit 1; fi
printf 'Focused native dependent Fubini checks passed.\n'
