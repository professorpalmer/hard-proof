#!/bin/sh
# Hard Proof, experiment 12, second set: corrected DistinctIds. First laws, then the loops.
set -u
cd "$(dirname "$0")"
export HP_BASE=base_b
for m in haiku sonnet opus; do
  ( python3 first12.py --model claude-$m-5-5 --name b_$m > first_b_$m.log 2>&1 \
    && python3 loop12.py --start b_$m --name loopb_$m > loopb_$m.log 2>&1 ) &
done
wait
tail -8 first_b_*.log loopb_*.log
