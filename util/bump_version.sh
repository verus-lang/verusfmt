#! /bin/bash

if [ $# -lt 1 ]; then
  echo "Usage: $0 {version|--patch|--minor|--major}"
  exit 1
fi

input_version=$1

if [[ "$input_version" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
  version_type="manual"
elif [[ "$input_version" == "--patch" || "$input_version" == "--minor" || "$input_version" == "--major" ]]; then
  version_type=$input_version
else
  echo "Error: Invalid argument. Please use the format X.Y.Z or --patch, --minor, --major."
  exit 1
fi

if git rev-parse --show-toplevel 2>/dev/null >/dev/null; then
  ROOT_DIR=$(git rev-parse --show-toplevel)
  VCS_TYPE=git
elif jj workspace root 2>/dev/null >/dev/null; then
  ROOT_DIR=$(jj workspace root)
  VCS_TYPE=jj
else
  echo "FATAL: Could not find jj or git root dir"
fi

cd "$ROOT_DIR" || exit 1

existing_versions=$(grep -oP '# v\K[0-9]+\.[0-9]+\.[0-9]+' CHANGELOG.md || echo "")
latest_version=$(echo "$existing_versions" | sort -V | tail -n 1)

if [ "$version_type" == "manual" ]; then
  proposed_version="$input_version"
else
  IFS='.' read -r major minor patch <<<"$latest_version"
  case "$version_type" in
  "--patch")
    proposed_version="${major}.${minor}.$((patch + 1))"
    commit_msg="chore: bump the patch version"
    ;;
  "--minor")
    proposed_version="${major}.$((minor + 1)).0"
    commit_msg="chore: bump the minor version"
    ;;
  "--major")
    proposed_version="$((major + 1)).0.0"
    commit_msg="chore: bump the major version"
    ;;
  esac
fi

if printf "%s\n" "$latest_version" "$proposed_version" | sort -V | head -n1 | grep -q "$proposed_version"; then
  echo "Error: provided version $proposed_version is not newer than the latest version ($latest_version)"
  exit 1
fi
echo "Using $proposed_version (tested valid and newer than the latest version)"

echo "Updating versions in files, and running 'cargo check'"
sed -i "s/# Unreleased/# Unreleased\n\n# v${proposed_version}/" CHANGELOG.md
sed -i "s/^version = \".*\"/version = \"${proposed_version}\"/" Cargo.toml
cargo check -q
echo "Done"

if [ "$version_type" == "manual" ]; then
  echo "Not committing and tagging a manually defined version"
elif [ "$VCS_TYPE" == "git" ]; then
  echo "Making a commit, and tagging it"
  git add CHANGELOG.md Cargo.toml Cargo.lock
  git commit -m "$commit_msg"
  git tag "v${proposed_version}"
  echo "Done... Now you need to push with 'git push --tags'"
elif [ "$VCS_TYPE" == "jj" ]; then
  echo "Making a commit, and tagging it"
  jj commit -m "$commit_msg" CHANGELOG.md Cargo.toml Cargo.lock
  # From
  # <https://jj-vcs.github.io/jj/v0.25.0/git-compatibility/#supported-features>:
  # Tags: Partial. You can check out tagged commits by name (pointed to be
  # either annotated or lightweight tags), but you cannot create new tags.
  #
  # Related: <https://github.com/jj-vcs/jj/issues/5426>
  echo "jj currently doesn't support creating tags."
  echo "We would have created the tag 'v${proposed_version}' if possible."
  echo "For now, you'll have to do it manually on GitHub."
else
  echo "FATAL: Unknown VCS TYPE. Updates were done, but cannot tag."
  exit 1
fi
