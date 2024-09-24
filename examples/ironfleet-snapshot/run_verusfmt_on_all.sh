#! /bin/bash

set -e
set -o pipefail

if [ $# -eq 1 ]; then
    if [ "$1" == "--check" ]; then
        echo "Checking all files with verusfmt..."
        cargo build --release
        find . -name "*.rs" -exec cargo run --release --quiet -- --check {} \;
    else
        echo "Invalid argument: $1"
    fi
elif [ $# -eq 0 ]; then
    echo "Running verusfmt on all files..."
    cargo build --release
    find . -name "*.rs" -print0 | xargs -0 cargo run --release --quiet --
else
    echo "Invalid number of arguments: $#"
fi
