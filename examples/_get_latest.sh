#! /bin/bash

# This script exposes the `get_latest` function that reads the following
# variables:
#
#    GITHUB_ORG
#    GITHUB_REPO
#    GITHUB_BRANCH
#    MOVE_PATHS
#    FORCE_REFORMAT_PATHS
#
# It then downloads the project, moves all the paths from `MOVE_PATHS` into the
# directory, and if `FORCE_REFORMAT_PATHS` is set, then forcefully reformats the
# files in those paths.

function get_latest() {
    echo "[INFO] Cleaning any existing files"
    rm -rf "${GITHUB_REPO}.zip" "${GITHUB_REPO}-${GITHUB_BRANCH}"
    # shellcheck disable=SC2086
    rm -rf $MOVE_PATHS

    echo "[INFO] Downloading latest version of ${GITHUB_ORG}/${GITHUB_REPO}"
    wget --quiet -O "${GITHUB_REPO}.zip" "https://github.com/${GITHUB_ORG}/${GITHUB_REPO}/archive/refs/heads/${GITHUB_BRANCH}.zip"

    echo "[INFO] Unzipping ${GITHUB_REPO}"
    unzip -q "${GITHUB_REPO}.zip"

    echo "[INFO] Moving files"
    for path in $MOVE_PATHS; do
        echo "       ... $path"
        if [ -d "${GITHUB_REPO}-${GITHUB_BRANCH}/$path" ]; then
            # Directory, move all the .rs files, including those in subdirectories, creating the necessary directories
            mkdir -p "$path"
            find "${GITHUB_REPO}-${GITHUB_BRANCH}/$path" -name '*.rs' -print0 | while IFS= read -r -d '' file; do
                relative_path=$(realpath --relative-to="${GITHUB_REPO}-${GITHUB_BRANCH}" "$file")
                dirname=$(dirname "$relative_path")
                mkdir -p "$dirname"
                mv "$file" "$relative_path"
            done
        else
            # File
            mkdir -p "$(dirname "$path")"
            mv "${GITHUB_REPO}-${GITHUB_BRANCH}/$path" "$path"
        fi
    done

    # Until these files are formatted on the branch, we want to just manually
    # reformat it locally, to minimize the diff for the snapshots
    if [ "$FORCE_REFORMAT_PATHS" != "" ]; then
        echo "[INFO] Reformatting paths not yet already formatted within ${GITHUB_REPO} '${GITHUB_BRANCH}'"
        for path in $FORCE_REFORMAT_PATHS; do
            echo "       ... $path"
            if [ -d "$path" ]; then
                find "$path" -name '*.rs' -exec verusfmt {} \;
            else
                verusfmt "$path"
            fi
        done
    fi

    echo "[INFO] Cleaning up"
    rm -rf "${GITHUB_REPO}-${GITHUB_BRANCH}" "${GITHUB_REPO}.zip"
}
