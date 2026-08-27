# Release Process

1. Ensure release notes are listed under `# Unreleased` in `CHANGELOG.md`.
2. Create a temporary release branch and run:
    ```
    ./util/bump_version.sh --patch  
    # or --minor, --major, or an explicit version such as 0.8.0
    ```
 This:
  - Adds # vX.Y.Z below # Unreleased.
  - Updates the version in Cargo.toml.
  - Runs `cargo check`, updating `Cargo.lock`.
  - Commits the changes automatically for --patch/--minor/--major. An explicit version leaves them uncommitted.

3. Open and merge a release PR. The title should be `chore: release v0.7.2.` (with your new version number).
   CI runs formatting, clippy, build, and the full test suite; the release workflow also validates the cargo-dist plan on PRs.

4. Tag the merged release commit and push the tag:
    ```
    git tag vX.Y.Z <merge-commit-hash>
    git push origin vX.Y.Z
    ```
   The tag version must match the version in Cargo.toml.

5. The GitHub workflow in `.github/workflows/release.yml` then:
  - Builds binaries for macOS ARM/x86, Linux x86, and Windows x86.
  - Generates shell and PowerShell installers.
  - Creates a GitHub Release with notes derived from CHANGELOG.md.
  - Uploads binaries, installers, and checksums.
  - Invokes `.github/workflows/publish-crates.yml`, which runs `cargo publish -p verusfmt` 
    using the `CRATES_TOKEN` repository secret.

6. Confirm that the GitHub Release completed and the new version appears on crates.io.

