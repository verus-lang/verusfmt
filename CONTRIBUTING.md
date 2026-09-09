# Release Process

1. Ensure release notes are listed under `# Unreleased` in `CHANGELOG.md`.
2. Create a temporary release branch and run:
    ```
    ./util/bump_version.sh --patch  
    # or --minor, --major, or an explicit version such as 0.8.0
    ```
   This updates versions and tweaks the changelog and creates a commit.

3. Open and merge a release PR. The title should be `chore: release vX.Y.Z.` (with your new version number).

4. Tag the merged release commit and push the tag:
    ```
    git tag vX.Y.Z <merge-commit-hash>
    git push origin vX.Y.Z
    ```
   The tag version must match the version in Cargo.toml.

5. Wait for the release workflow to complete.

6. Confirm that the new release showed up at the [releases page](https://github.com/verus-lang/verusfmt/releases) and the new version appears on [crates.io](https://crates.io/crates/verusfmt). If it does not, then likely some update is needed to the auto-release process.  In such a case, the tagged `vX.Y.Z` should be considered "used", and the next attempt should be `vX.Y.{Z+1}`.
