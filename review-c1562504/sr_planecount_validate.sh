#!/bin/bash
# Small-size validation of sr_planecount against the exact reference (PlaneCount review of bp1_c1562504, draft).
# Usage: bash sr_planecount_validate.sh BINARY OUTDIR      (BINARY = gcc -O2 -Wall build of sr_planecount.c)
set -u
bin=$1; out=$2; here=$(cd "$(dirname "$0")" && pwd); mkdir -p "$out"
for cfg in "16 4 11 10" "16 4 9 10" "16 6 10 8" "16 6 10 9" "16 6 12 8" "16 6 13 9" "16 6 8 8" "16 6 8 9" "16 8 12 7"; do
  f="$out/all_${cfg// /_}.txt"; "$bin" $cfg all > "$f"
  python3 -I "$here/sr_planecount_check.py" compare $cfg "$f"
done
for cfg in "16 4 11 10" "16 4 9 10" "16 6 10 8" "16 6 13 9" "16 6 8 9"; do
  f="$out/line_${cfg// /_}.txt"; "$bin" $cfg line 20000 1 > "$f"
  python3 -I "$here/sr_planecount_check.py" rotclose $cfg "$f"
  python3 -I "$here/sr_planecount_check.py" verify $cfg "$f" | tail -1
done
