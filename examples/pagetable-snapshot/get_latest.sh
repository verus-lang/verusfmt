#! /bin/bash

set -e
set -o pipefail

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
cd "$SCRIPT_DIR"
source ../_get_latest.sh

GITHUB_ORG=utaal
GITHUB_REPO=verified-nrkernel
GITHUB_BRANCH=main
MOVE_PATHS="page-table"
FORCE_REFORMAT_PATHS="page-table"

get_latest
