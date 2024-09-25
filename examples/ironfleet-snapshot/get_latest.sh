#! /bin/bash

set -e
set -o pipefail

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
cd "$SCRIPT_DIR"
source ../_get_latest.sh

GITHUB_ORG=verus-lang
GITHUB_REPO=verified-ironkv
GITHUB_BRANCH=main
MOVE_PATHS="ironsht/src"
FORCE_REFORMAT_PATHS="ironsht/src"

get_latest
