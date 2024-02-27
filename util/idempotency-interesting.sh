#! /bin/bash

################################################################################
#
# This script is used to test the idempotency of the formatter.
#
# Usage:
#   creduce ./util/idempotency-interesting.sh foo.rs
#
################################################################################

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"

if [ $# -eq 1 ]; then
	FILE=$1
else
	echo "[!] No file specified, using foo.rs" 1>&2
	FILE="foo.rs"
fi

if "$DIR/../target/release/verusfmt" "$FILE" -Z idempotency-test; then
	exit 0
else
	exit 1
fi
