#! /bin/bash

set -e
set -o pipefail

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
cd "$SCRIPT_DIR"
source ../_get_latest.sh

GITHUB_ORG=verus-lang
GITHUB_REPO=verified-node-replication
GITHUB_BRANCH=main
MOVE_PATHS="verified-node-replication/src"
FORCE_REFORMAT_PATHS=""

get_latest
