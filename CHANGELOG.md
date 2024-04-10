# Unreleased

* Support attributes on `broadcast group` items
* Improve styling of `broadcast use`s, ensuring trailing newline
* Add support for the `no_unwind` clause on functions

# v0.2.11

* Improve handling of `rustfmt.toml` for non-`verus!` code
  - Rather than picking up `rustfmt.toml` based on working directory, it is now picked up based on the file being formatted. This now matches the search that `rustfmt` itself does.

# v0.2.10

* Add support for `broadcast proof`, `broadcast group`, and `broadcast use` (see [verus#1022](https://github.com/verus-lang/verus/pull/1022))

# v0.2.9

* Add support for `invariant_except_break` clauses, recently added to Verus
* Support arbitrary permutation of clauses in loops, rather than a pre-specified order

# v0.2.8

* Add support for `for` loops with invariants, recently added to Verus
* Improve parsing of range expressions (e.g., `0..(1 + 2)`) that start "float-like"

# v0.2.7

* Improve `verus!{ ... }` macro collapsing inside indented contexts (#39)

# v0.2.6

* When running verusfmt on multiple files, continue attempting files even if one in the middle fails (#37)
* Fix collection of idempotency issues caused by rustfmt (#38)
  - rustfmt would modify code inside of `verus! { ... }` after verusfmt has already formatted it in certain cases
  - Verusfmt now prevents rustfmt from modifying code inside the Verus macro, through a collapse/expand operation  

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
