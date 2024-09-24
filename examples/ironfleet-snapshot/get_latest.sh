#! /bin/bash

set -e
set -o pipefail

echo "[INFO] Cleaning any existing files"
rm -rf verified-ironkv.zip verified-ironkv-main ironsht

echo "[INFO] Downloading latest version of Verus"
wget --quiet -O verified-ironkv.zip https://github.com/verus-lang/verified-ironkv/archive/refs/heads/main.zip

echo "[INFO] Unzipping Verified IronKV"
unzip -q verified-ironkv.zip

MOVE_PATHS="ironsht/src"

echo "[INFO] Moving files"
for path in $MOVE_PATHS; do
    echo "       ... $path"
    if [ -d "verified-ironkv-main/$path" ]; then
        # Directory, move all the .rs files, including those in subdirectories, creating the necessary directories
        mkdir -p "$path"
        find "verified-ironkv-main/$path" -name '*.rs' -print0 | while IFS= read -r -d '' file; do
            relative_path=$(realpath --relative-to="verified-ironkv-main" "$file")
            dirname=$(dirname "$relative_path")
            mkdir -p "$dirname"
            mv "$file" "$relative_path"
        done
    else
        # File
        mkdir -p "$(dirname "$path")"
        mv "verified-ironkv-main/$path" "$path"
    fi
done

echo "[INFO] Cleaning up"
rm -rf verified-ironkv.zip verified-ironkv-main
