#!/bin/bash
cd "$(dirname "$0")"
xargs -P4 -L1 bash -c 'out="job_$(echo "$@" | tr " " "_").txt"; s=$(date +%s); ../sr_planecount "$@" > "$out"; echo "elapsed $(( $(date +%s) - s )) s" >> "$out"' _ < sr_planecount_jobs.txt
echo ALLDONE > done.flag
