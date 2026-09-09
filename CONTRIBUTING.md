# Contributing to Verusfmt

We consider it a bug in `verusfmt` if you provide `verusfmt` with code
that [Verus](https://github.com/verus-lang/verus) accepts, and `verusfmt` either does not accept/parse it, or
produces code that Verus does not accept (or has different semantics from the original).
When this happens, please open a GitHub issue with a minimal example of the offending code
before (and after) formatting.

If `verusfmt` produces valid code but you dislike the formatting, please open
a GitHub pull request with your proposed changes and rationale for those changes.
Please ensure that existing test cases still pass (see below for more details),
unless your goal is to change how some of those test cases are handled.  Please
also include new/updated tests that exercise your proposed changes.

## Tips for Developing a Fix or an Improvement

1. Write out a small example `.rs` file focusing on the specific thing you want
   to improve.  Test `verusfmt` on your reduced example to make sure the issue
   still manifests; running with `--check` is very helpful with this process.
   The smaller your example file, the easier subsequent steps will be.
2. When running with `--check`, you can also add `-dd` to see 2nd level debug
   output, which includes the parse tree.  Look through the parse tree and
   identify rules relevant to your particular example.
3. Once you find the relevant rule names, if the issue seems to be a misparse,
   jump over to `src/verus.pest` to find the relevant rule(s) and see if the
   grammar needs to be fixed or improved.
4. If the parsing is fine but the printing is an issue, then look for the
   relevant rule(s) in the `to_doc` function in `src/lib.rs`. This might be a
   bit difficult to understand immediately, so having the [pretty] docs handy
   is quite helpful.  Also, it is helpful to look at the relevant debug print
   (using `-d` or `-dd`), which gives a serialized version of the recursively
   expanded `doc`, right before it has been optimized, so figuring out which
   particular bit of it is not behaving as you like is quite helpful.
5. Attempt fixes until the small example succeeds.
6. Add the example into the tests---see the [Testing](#testing) section below.
7. If fixing the rule for your small example succeeds but breaks other tests,
   you may need to split the relevant rule in the parsing grammar into two
   separate cases, so that each case can be formatted independently.  See
   `comma_delimited_exprs_for_verus_clauses`  and
   `groupable_comma_delimited_exprs_for_verus_clauses`, for example.

## Testing

### Rust-like formatting

In general, we try to adhere to Rust's style guide.  Tests for such adherence live in
[tests/rustfmt-matching.rs](tests/rustfmt-matching.rs).  These tests will compare the output
of [`rustfmt`] to that of `verusfmt`.  You can run them via `cargo test`.

### Verus-like formatting

In various places, we deviate from Rust's style, either to simplify the
formatter or to handle [Verus](https://github.com/verus-lang/verus)-specific syntax.  Tests for formatting such code
live in [tests/verus-consistency.rs](tests/verus-consistency.rs).  You can add
a new test or modify an existing one by writing/changing the input code.  The
test's correct answer is maintained via the [Insta testing framework](https://insta.rs).

Insta recommends installing the `cargo-insta` tool for an improved review experience:
```
cargo install cargo-insta
```

You can run the tests normally with `cargo test`, but it's often more convenient
to run the tests and review the results via:
```
cargo insta test
cargo insta review
```
or more succinctly:
```
cargo insta test --review
```

## Release Process

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
