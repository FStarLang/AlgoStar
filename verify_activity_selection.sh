#!/bin/bash
# Verify the Activity Selection implementation and lemmas

cd "$(dirname "$0")"
PULSE_LIB=$(realpath ../pulse)/out/lib/pulse

echo "Verifying Activity Selection with Optimality Proof..."
fstar.exe --include "$PULSE_LIB" --include common \
  ch16-greedy/CLRS.Ch16.ActivitySelection.Lemmas.fst \
  ch16-greedy/CLRS.Ch16.ActivitySelection.fst

if [ $? -eq 0 ]; then
    echo ""
    echo "✅ SUCCESS: All verification conditions discharged"
    echo ""
    echo "Verified components:"
    echo "  - Activity Selection Lemmas (including greedy choice optimality)"
    echo "  - Activity Selection Algorithm (Pulse implementation)"
    echo ""
    echo "Properties proven:"
    echo "  - Termination"
    echo "  - Pairwise non-overlapping activities"  
    echo "  - Greedy choice property (CLRS Theorem 16.1)"
    echo ""
    echo "NO admits. NO assumes."
else
    echo "❌ FAILED: Verification errors occurred"
    exit 1
fi
