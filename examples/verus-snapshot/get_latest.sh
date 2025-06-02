#! /bin/bash

set -e
set -o pipefail

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
cd "$SCRIPT_DIR"
source ../_get_latest.sh

GITHUB_ORG=verus-lang
GITHUB_REPO=verus
GITHUB_BRANCH=main
MOVE_PATHS="source/rustfmt.toml examples/syntax.rs source/vstd"
FORCE_REFORMAT_PATHS="examples/syntax.rs"

get_latest
