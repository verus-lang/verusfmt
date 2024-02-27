# Unreleased

# v0.2.5

* Fix `FnSpec` parsing
  - Despite Verus having deprecated `FnSpec` with the introduction of `spec_fn`, verusfmt still supports it for projects on older Verus
* Fix idempotency issue of macro-items inside `verus!` inside in-file `mod`ules
* Fix multi-line inline comment treatment
  - Only treat multi-line comments as inline if the entire comment is on a single line

# v0.2.4

* Move verusfmt to the verus-lang organization: https://github.com/verus-lang/verusfmt

# v0.2.3

* Don't drop "?" or "~" from type bounds

# v0.2.2

* Allow (bare) trigger attributes to be inline, rather than always on their own line

# v0.2.1

* Add support for new `spec_fn`
* Update handling for `fn_trait_types`
* Add support for `const` params
* Add support for `opens_invariants`
* Improve handling of complex self-params (e.g., `tracked '&a self`)
* Introduce `#[verusfmt::skip]` (#31)
* Add support for new `->` and `matches` expressions (#32)

# v0.2.0

* Reduce collapsing of various multiple single-line comments
* Fixed extra spaces in if-expressions with negation (#24)
* Fixed precedence for quantifiers and `&&&` and `|||` (#26)
* Handle macro call statements (#27)
* Improved handling of non-inline single-line comments (#28)

# v0.1.6

* Treat comments inside function signatures as inline by default

# v0.1.5

* Improved output for `--check`

# v0.1.4

Initial public release!
