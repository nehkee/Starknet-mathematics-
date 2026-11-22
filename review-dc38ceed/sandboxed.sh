#!/bin/sh
# Run a command with no network and without access to credentials or the repository.
# - new network namespace: no interfaces except a down loopback
# - new mount namespace: /root/.config (pvfast key), /root/.ccr (proxy credentials), /root/.ssh hidden behind
#   empty tmpfs; git credential files hidden; /workspace remounted read-only
exec unshare -m -n sh -c '
  for d in /root/.config /root/.ccr /root/.ssh; do [ -d "$d" ] && mount -t tmpfs -o size=1m none "$d"; done
  for f in /root/.git-credentials /root/.gitconfig /root/.netrc; do [ -f "$f" ] && mount --bind /dev/null "$f"; done
  mount --bind /workspace /workspace && mount -o remount,bind,ro /workspace
  exec "$@"' sh "$@"
