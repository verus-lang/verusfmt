#! /bin/bash

set -e
set -o pipefail

echo "[INFO] Cleaning any existing files"
rm -rf verus.zip verus-main source

echo "[INFO] Downloading latest version of Verus"
wget --quiet -O verus.zip https://github.com/verus-lang/verus/archive/refs/heads/main.zip

echo "[INFO] Unzipping Verus"
unzip -q verus.zip

MOVE_PATHS="source/rustfmt.toml source/rust_verify/example/syntax.rs source/vstd"

echo "[INFO] Moving files"
for path in $MOVE_PATHS; do
    echo "       ... $path"
    if [ -d "verus-main/$path" ]; then
        # Directory, move all the .rs files, including those in subdirectories, creating the necessary directories
        mkdir -p "$path"
        find "verus-main/$path" -name '*.rs' -print0 | while IFS= read -r -d '' file; do
            relative_path=$(realpath --relative-to="verus-main" "$file")
            dirname=$(dirname "$relative_path")
            mkdir -p "$path/$dirname"
            mv "$file" "$path/$relative_path"
        done
    else
        # File
        mkdir -p "$(dirname "$path")"
        mv "verus-main/$path" "$path"
    fi
done

# Until these files are formatted on Verus `main`, we want to just manually
# reformat it locally, to minimize the diff for the snapshots
FORCE_REFORMAT_PATHS="source/rust_verify/example/syntax.rs"
if [ "$FORCE_REFORMAT_PATHS" != "" ]; then
    echo "[INFO] Reformatting paths not yet already formatted within Verus 'main'"
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
rm -rf verus-main verus.zip
