#!/usr/bin/env bash

UNRELEASED_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.changelog-unreleased" 2>/dev/null && pwd)"
if [ -z "$UNRELEASED_DIR" ]; then
  echo "Error: .changelog-unreleased directory not found" >&2
  exit 1
fi

status=0
for f in "$UNRELEASED_DIR"/*; do
  [ -f "$f" ] || continue
  [ "$(basename "$f")" = ".keep" ] && continue

  if ! awk '
    NR == 1 && substr($0, 1, 2) != "* " {
      print FILENAME ": line must begin with \"* \"" > "/dev/stderr"
      failed = 1
    }
    NR > 1 {
      print FILENAME ": must contain exactly one line" > "/dev/stderr"
      failed = 1
    }
    END {
      if (NR == 0) {
        print FILENAME ": must contain exactly one line beginning with \"* \"" > "/dev/stderr"
        failed = 1
      }
      exit failed
    }
  ' "$f"; then
    status=1
  fi
done

if [ "$status" -ne 0 ]; then
  exit 1
fi

echo "Unreleased changelog files are valid"
