mod rustfmt;
mod visitor;
pub use crate::rustfmt::{rustfmt, RustFmtConfig};

use pest::{iterators::Pair, iterators::Pairs, Parser};
use pest_derive::Parser;
use pretty::*;
use regex::Regex;
use std::collections::HashSet;
use tracing::{debug, enabled, error, info, Level};

#[derive(Parser)]
#[grammar = "verus.pest"]
struct VerusParser;

// JB: Should we expose these to the user as configurable options where we pick a default?
// I think even this should be opinionated, but might be useful to expose this as an unstable option or something.
// rustfmt sets this to 100: https://rust-lang.github.io/rustfmt/?version=v1.6.0&search=#max_width
const NUMBER_OF_COLUMNS: usize = 100;
const INDENT_SPACES: isize = 4;
// Number of spaces between an inline comment and the preceding text
const INLINE_COMMENT_SPACE: usize = 2;

struct Context {
    inline_comment_lines: HashSet<usize>,
}

// When in doubt, we should generally try to stick to Rust style guidelines:
//   https://doc.rust-lang.org/beta/style-guide/items.html

/// Adds a comma that vanishes in single-line mode
fn conditional_comma<'a>(arena: &'a Arena<'a, ()>) -> DocBuilder<'a, Arena<'a>> {
    arena.text(",").flat_alt(arena.nil()) //.group()
}

/// Comma-delimited list with an optional final comma
fn comma_delimited<'a>(
    ctx: &Context,
    arena: &'a Arena<'a, ()>,
    pair: Pair<'a, Rule>,
    is_tuple: bool,
) -> DocBuilder<'a, Arena<'a>> {
    let pairs = pair.into_inner();
    if pairs.clone().count() == 0 {
        arena.nil()
    } else {
        let num_comments = pairs
            .clone()
            .filter(|p| matches!(p.as_rule(), Rule::COMMENT))
            .count();
        let num_non_comments = pairs.len() - num_comments;
        debug!(
            "Found {} non-comments out of {} pairs",
            num_non_comments,
            pairs.len()
        );
        let mut non_comment_index = 0;
        let mut trailing_comment = false;
        let comma_separated = pairs.map(|p| match p.as_rule() {
            Rule::COMMENT => {
                trailing_comment = true;
                to_doc(ctx, p, arena)
            }
            _ => {
                trailing_comment = false;
                if non_comment_index < num_non_comments - 1 {
                    non_comment_index += 1;
                    to_doc(ctx, p, arena).append(docs![
                        arena,
                        ",",
                        if num_comments > 0 {
                            arena.hardline()
                        } else {
                            arena.line()
                        }
                    ])
                } else if num_non_comments > 0
                    && !matches!(p.as_rule(), Rule::struct_update_base)
                    && !matches!(p.as_rule(), Rule::rest_pat)
                {
                    // Even if we would normally include a trailing comma,
                    // never add one for struct_update_base (`..foo`) or
                    // for a struct pattern etc (`..`)
                    if num_non_comments == 1 && is_tuple {
                        // We need to always include the comma, or it will
                        // be interpreted as a parenthesized expression,
                        // rather than a one-tuple
                        to_doc(ctx, p, arena).append(arena.text(","))
                    } else {
                        to_doc(ctx, p, arena).append(conditional_comma(arena))
                    }
                } else {
                    to_doc(ctx, p, arena)
                }
            }
        });
        let doc = arena.line_().append(arena.concat(comma_separated));
        if trailing_comment {
            debug!("Trailing comment: Yes");
            doc.nest(INDENT_SPACES)
        } else {
            debug!("Trailing comment: No");
            doc.nest(INDENT_SPACES).append(arena.line_())
        }
    }
}

/// Comma-delimited list with a required final comma
fn comma_delimited_full<'a>(
    ctx: &Context,
    arena: &'a Arena<'a, ()>,
    pair: Pair<'a, Rule>,
) -> DocBuilder<'a, Arena<'a>> {
    let pairs = pair.into_inner();
    let num_comments = pairs
        .clone()
        .filter(|p| matches!(p.as_rule(), Rule::COMMENT))
        .count();
    let num_non_comments = pairs.len() - num_comments;
    debug!(
        "Found {} non-comments out of {} pairs",
        num_non_comments,
        pairs.len()
    );
    let mut non_comment_index = 0;
    let comma_separated = pairs.map(|p| match p.as_rule() {
        Rule::COMMENT => to_doc(ctx, p, arena),
        _ => {
            if non_comment_index < num_non_comments - 1 {
                non_comment_index += 1;
                to_doc(ctx, p, arena).append(docs![
                    arena,
                    ",",
                    if num_comments > 0 {
                        arena.hardline()
                    } else {
                        arena.line()
                    }
                ])
            } else {
                to_doc(ctx, p, arena).append(arena.text(","))
            }
        }
    });
    arena
        .line()
        .append(arena.concat(comma_separated))
        .nest(INDENT_SPACES)
}

enum Enclosure {
    Braces,
    Brackets,
    Parens,
}

/// Wrap a document in delimiters where the opening delimter tries to "stick" to the previous line if needed
fn sticky_delims<'a>(
    ctx: &Context,
    arena: &'a Arena<'a, ()>,
    pair: Pair<'a, Rule>,
    enc: Enclosure,
    nest: bool,
) -> DocBuilder<'a, Arena<'a>> {
    use Enclosure::*;
    let opening = match enc {
        Braces => "{",
        Brackets => "[",
        Parens => "(",
    };
    let opening_space = arena.line_();
    let closing = match enc {
        Braces => "}",
        Brackets => "]",
        Parens => ")",
    };
    let closing_space = match enc {
        Braces => arena.line(),
        Brackets => arena.nil(),
        Parens => arena.nil(),
    };
    let pairs = pair.into_inner();
    if pairs.clone().count() == 0 {
        // Don't allow breaks in the list when the list is empty
        docs![arena, opening, closing].group()
    } else {
        let docs = arena.concat(pairs.map(|p| to_doc(ctx, p, arena)));
        let prefix = docs![arena, opening, opening_space]
            .group()
            .append(if matches!(enc, Braces) {
                arena.line()
            } else {
                arena.nil()
            })
            .append(docs);
        let prefix = if nest {
            prefix.nest(INDENT_SPACES)
        } else {
            prefix
        };
        prefix
            .group()
            .append(closing_space)
            .append(arena.text(closing))
            .group()
    }
}

/// Surround the doc with braces that have inner spacing only if on a single line
fn spaced_braces<'a>(
    arena: &'a Arena<'a, ()>,
    doc: DocBuilder<'a, Arena<'a>>,
) -> DocBuilder<'a, Arena<'a>> {
    docs![
        arena,
        arena.nil().flat_alt(arena.space()),
        doc,
        arena.nil().flat_alt(arena.space()),
    ]
    .braces()
}

/// Pad spaced_braces with an additional space before the opening brace
fn extra_spaced_braces<'a>(
    arena: &'a Arena<'a, ()>,
    doc: DocBuilder<'a, Arena<'a>>,
) -> DocBuilder<'a, Arena<'a>> {
    arena.space().append(spaced_braces(arena, doc))
}

fn block_braces<'a>(
    arena: &'a Arena<'a, ()>,
    doc: DocBuilder<'a, Arena<'a>>,
    terminal_expr: bool,
) -> DocBuilder<'a, Arena<'a>> {
    let doc = arena.hardline().append(doc).nest(INDENT_SPACES);
    let doc = if terminal_expr {
        doc.append(arena.hardline())
    } else {
        doc
    };
    doc.braces()
}

/// Produce a document that simply combines the result of calling `to_doc` on each child
fn map_to_doc<'a>(
    ctx: &Context,
    arena: &'a Arena<'a, ()>,
    pair: Pair<'a, Rule>,
) -> DocBuilder<'a, Arena<'a>> {
    arena.concat(pair.into_inner().map(|p| to_doc(ctx, p, arena)))
}

/// Produce a document that combines the result of calling `to_doc` on each child, interspersed
/// with newlines.  This requires special handling for comments, so we don't add excessive
/// newlines around `//` style comments.
fn map_to_doc_lines<'a>(
    ctx: &Context,
    arena: &'a Arena<'a, ()>,
    pair: Pair<'a, Rule>,
) -> DocBuilder<'a, Arena<'a>> {
    let pairs = pair.into_inner();
    if pairs.clone().count() == 0 {
        arena.nil()
    } else {
        let num_comments = pairs
            .clone()
            .filter(|p| matches!(p.as_rule(), Rule::COMMENT))
            .count();
        let num_non_comments = pairs.len() - num_comments;
        debug!(
            "Found {} non-comments out of {} pairs",
            num_non_comments,
            pairs.len()
        );
        let mut non_comment_index = 0;
        let newline_separated = pairs.map(|p| match p.as_rule() {
            Rule::COMMENT => to_doc(ctx, p, arena),
            _ => {
                if non_comment_index < num_non_comments - 1 {
                    non_comment_index += 1;
                    to_doc(ctx, p, arena).append(docs![arena, arena.line(), arena.line(),])
                } else {
                    to_doc(ctx, p, arena)
                }
            }
        });
        arena.concat(newline_separated)
    }
}

/// Produce a document that simply combines the result of calling `to_doc` on each pair
fn map_pairs_to_doc<'a>(
    ctx: &Context,
    arena: &'a Arena<'a, ()>,
    pairs: &Pairs<'a, Rule>,
) -> DocBuilder<'a, Arena<'a>> {
    arena.concat(pairs.clone().map(|p| to_doc(ctx, p, arena)))
}

// During formatting, rather than trying to dynamically decide when a single-line comment should be
// placed on its own line based on its context, when we encounter a single-line comment, we add a
// marker indicating whether it was originally inline.  If it wasn't inline, we also add a
// destination marker on the next line.  After everything is formatted, in `fix_inline_comments`,
// we can scan for the markers.  If an originally inline comment has been moved to its own line, we
// move it back.  If an originally non-inline comment has been inlined, we move it to its
// corresponding destination marker.  We need the destination marker to tells us how much the
// comment should be indented when moved to the next line.
fn comment_to_doc<'a>(
    ctx: &Context,
    arena: &'a Arena<'a, ()>,
    pair: Pair<'a, Rule>,
    add_newline: bool,
) -> DocBuilder<'a, Arena<'a>> {
    assert!(matches!(pair.as_rule(), Rule::COMMENT));
    let (line, _col) = pair.line_col();
    let s = arena.text(pair.as_str().trim());
    if ctx.inline_comment_lines.contains(&line) {
        debug!(
            "contains(line = <<{}>>) = {}, with add_newline: {}",
            pair.as_str(),
            ctx.inline_comment_lines.contains(&line),
            add_newline,
        );
        let d = arena
            .text(format!("{:indent$}", "", indent = INLINE_COMMENT_SPACE))
            .append(s)
            .append(arena.text(INLINE_COMMENT_FIXUP))
            .append(if add_newline {
                arena.line()
            } else {
                arena.nil()
            });
        debug!("result: {:?}", d);
        d
    } else if !is_multiline_comment(&pair) {
        s.append(NONINLINE_COMMENT_MARKER)
            .append(arena.hardline())
            .append(NONINLINE_COMMENT_DST)
            .append(arena.hardline())
    } else {
        s.append(arena.line())
    }
}

fn items_to_doc<'a>(
    ctx: &Context,
    arena: &'a Arena<'a, ()>,
    pair: Pair<'a, Rule>,
    braces: bool,
) -> DocBuilder<'a, Arena<'a>> {
    let items = pair.into_inner();
    let len = items.clone().count();
    let mut prev_is_use = false;
    let mut res = arena.nil();
    for (i, item) in items.enumerate() {
        if item.as_rule() == Rule::COMMENT {
            debug!("FOUND a comment!");
            if prev_is_use {
                // Add an extra line break, since we don't put line breaks
                // between use declarations
                res = res.append(arena.line());
            }
            prev_is_use = false;
            let multiline_comment = is_multiline_comment(&item);
            res = res.append(to_doc(ctx, item, arena));
            if multiline_comment {
                res = res.append(arena.line());
            }
        } else {
            let is_use = matches!(
                item.clone().into_inner().next().unwrap().as_rule(),
                Rule::r#use
            );
            if prev_is_use && !is_use {
                // Add an extra line break, since we don't put line breaks
                // between use declarations
                res = res.append(arena.line());
            }
            prev_is_use = is_use;

            let is_broadcast_uses = matches!(
                item.clone().into_inner().next().unwrap().as_rule(),
                Rule::broadcast_uses
            );
            res = res.append(to_doc(ctx, item, arena));
            if !is_broadcast_uses {
                // Add the newline, but don't add extra newlines between `broadcast use`s since
                // those already add newlines
                res = res.append(arena.line());
            }
            // Add extra space between items, except for use declarations
            if i < len - 1 && !is_use {
                res = res.append(arena.line());
            }
        }
    }

    if braces {
        // Special case of sticky_delims
        if len == 0 {
            // Don't allow breaks in the list when the list is empty
            arena.text("{}")
        } else {
            let prefix = docs![arena, " {", arena.line_()]
                .group()
                .append(arena.line())
                .append(res);
            let prefix = prefix.nest(INDENT_SPACES);
            prefix
                .group()
                .append(arena.line())
                .append(arena.text("}"))
                .group()
        }
    } else {
        res
    }
}

fn format_doc(doc: RefDoc<()>) -> String {
    let mut w = Vec::new();
    doc.render(NUMBER_OF_COLUMNS, &mut w).unwrap();
    String::from_utf8(w).unwrap()
}

/// Provide some details for parsing rules we don't (yet) support
fn unsupported(pair: Pair<Rule>) -> DocBuilder<Arena> {
    let (line, col) = pair.line_col();
    error!(
        "Unsupported parsing object '{:?}', starting at line {}, col {}: {}",
        pair.as_rule(),
        line,
        col,
        pair.as_str()
    );
    todo!()
}

fn if_expr_to_doc<'a>(
    ctx: &Context,
    arena: &'a Arena<'a, ()>,
    pair: Pair<'a, Rule>,
) -> DocBuilder<'a, Arena<'a>> {
    arena.concat(pair.into_inner().map(|p| {
        if p.as_rule() == Rule::condition {
            to_doc(ctx, p, arena).append(arena.space())
        } else {
            to_doc(ctx, p, arena)
        }
    }))
}

fn loop_to_doc<'a>(
    ctx: &Context,
    arena: &'a Arena<'a, ()>,
    pair: Pair<'a, Rule>,
) -> DocBuilder<'a, Arena<'a>> {
    // We need to add a newline after the very last clause,
    // so that the opening brace of the loop body is on a fresh line
    let mut last_clause_span = None;
    // We also need to supress the space after the `for x in y`
    // if we see a colon indicating `for x in y: e`
    let mut colon_expr = false;
    pair.clone().into_inner().for_each(|p| {
        if p.as_rule() == Rule::loop_clause {
            last_clause_span = Some(p.as_span())
        }
        if p.as_rule() == Rule::colon_str {
            colon_expr = true;
        }
    });
    arena.concat(pair.into_inner().map(|p| {
        if p.as_rule() == Rule::condition {
            to_doc(ctx, p, arena).append(arena.space())
        } else if p.as_rule() == Rule::in_str {
            // Used for for-loops
            arena.space().append(to_doc(ctx, p, arena))
        } else if p.as_rule() == Rule::expr_no_struct && !colon_expr {
            to_doc(ctx, p, arena).append(arena.space())
        } else if let Some(c) = last_clause_span {
            if p.as_span() == c {
                to_doc(ctx, p, arena).append(arena.line())
            } else {
                to_doc(ctx, p, arena)
            }
        } else {
            to_doc(ctx, p, arena)
        }
    }))
}

/// Checks if this expr rule is either an &&& or an ||| expression
fn is_prefix_triple(pair: Pair<Rule>) -> bool {
    assert!(matches!(pair.as_rule(), Rule::expr));
    match pair
        .into_inner()
        .find(|p| matches!(p.as_rule(), Rule::expr_inner))
    {
        None => false,
        Some(pair) => match pair.into_inner().find(|p| {
            matches!(p.as_rule(), Rule::prefix_expr)
                || matches!(p.as_rule(), Rule::prefix_expr_no_struct)
        }) {
            None => false,
            Some(pair) => pair
                .into_inner()
                .any(|p| matches!(p.as_rule(), Rule::triple_and | Rule::triple_or)),
        },
    }
}

/// Checks if this rule is a trigger attribute without specific expressions
fn is_bare_trigger(pair: Pair<Rule>) -> bool {
    assert!(matches!(pair.as_rule(), Rule::attr) || matches!(pair.as_rule(), Rule::attr_inner));
    let core = pair
        .into_inner()
        .find(|p| matches!(p.as_rule(), Rule::attr_core));
    match core {
        None => false,
        Some(core) => match core
            .into_inner()
            .find(|p| matches!(p.as_rule(), Rule::trigger_attribute))
        {
            None => false,
            Some(trigger) => !trigger
                .into_inner()
                .any(|p| matches!(p.as_rule(), Rule::comma_delimited_exprs)),
        },
    }
}

/// Checks if a block may be written on a single line.  Rust says this is okay if:
/// - it is either used in expression position (not statement position) or is an unsafe block in statement position
/// - contains a single-line expression and no statements
/// - contains no comments
fn expr_only_block(r: Rule, pairs: &Pairs<Rule>) -> bool {
    assert!(matches!(r, Rule::stmt_list));
    let count = pairs.clone().fold(0, |count, p| {
        count
            + match p.as_rule() {
                Rule::attr | Rule::stmt | Rule::COMMENT | Rule::MULTI_NEWLINE => 1,
                Rule::expr => {
                    // We don't want to treat a triple expr as an expr only block,
                    // since that would result in it being grouped with its surrounding braces
                    if is_prefix_triple(p.clone()) {
                        1
                    } else {
                        -1
                    }
                }
                _ => 0,
            }
    });
    count == -1
}

/// Checks if a block terminates in an expression
fn terminal_expr(pairs: &Pairs<Rule>) -> bool {
    let e = pairs.clone().find(|p| matches!(p.as_rule(), Rule::expr));
    e.is_some()
}

fn debug_print(pair: Pair<Rule>, indent: usize) {
    if pair.as_rule() == Rule::COMMENT {
        print!(
            "{:indent$}{:?} {{ {comment:?} ",
            "",
            pair.as_rule(),
            indent = indent,
            comment = pair.as_str()
        );
    } else {
        print!("{:indent$}{:?} {{", "", pair.as_rule(), indent = indent);
    }
    let pairs = pair.clone().into_inner();
    if pairs.peek().is_some() {
        println!();
        pairs.for_each(|p| debug_print(p, indent + 2));
        println!("{:indent$}}}", "", indent = indent);
    } else {
        println!("}}");
    }
}

fn to_doc<'a>(
    ctx: &Context,
    pair: Pair<'a, Rule>,
    arena: &'a Arena<'a, ()>,
) -> DocBuilder<'a, Arena<'a>> {
    let s = arena.text(pair.as_str().trim());
    info!("Processing rule {:?}", pair.as_rule());
    match pair.as_rule() {
        //***********************//
        // General common things //
        //***********************//
        Rule::identifier_string
        | Rule::identifier
        | Rule::hex_number
        | Rule::keyword
        | Rule::decimal_number
        | Rule::octal_number
        | Rule::binary_number
        | Rule::int_number
        | Rule::float_decimal
        | Rule::float_exp
        | Rule::float_number
        | Rule::lifetime_ident
        | Rule::string
        | Rule::raw_string
        | Rule::raw_string_interior
        | Rule::byte_string
        | Rule::raw_byte_string
        | Rule::r#char
        | Rule::byte => s,

        //****************//
        // verusfmt::skip //
        //****************//
        Rule::verusfmt_skip_attribute => arena.text("#[verusfmt::skip]").append(arena.hardline()),
        Rule::verusfmt_skipped_item
        | Rule::verusfmt_skipped_assoc_item
        | Rule::verusfmt_skipped_stmt
        | Rule::verusfmt_skipped_expr
        | Rule::verusfmt_skipped_expr_no_struct => s,

        //***********************************************************//
        // Fixed strings we want to preserve in the formatted output //
        //***********************************************************//
        Rule::amp_str
        | Rule::at_str
        | Rule::bang_str
        | Rule::colons_str
        | Rule::comma_str
        | Rule::dash_str
        | Rule::dollar_str
        | Rule::dot_str
        | Rule::dot_dot_str
        | Rule::dot_dot_eq_str
        | Rule::ellipses_str
        | Rule::fatarrow_str
        | Rule::langle_str
        | Rule::lbrace_str
        | Rule::lbracket_str
        | Rule::lparen_str
        | Rule::pound_str
        | Rule::pub_str
        | Rule::question_str
        | Rule::rangle_str
        | Rule::rbrace_str
        | Rule::rbracket_str
        | Rule::rparen_str
        | Rule::semi_str
        | Rule::star_str
        | Rule::tilde_str
        | Rule::underscore_str
        | Rule::arrow_expr_str => s,
        Rule::fn_traits | Rule::impl_str => s,
        Rule::calc_str | Rule::seq_str => s,
        Rule::pipe_str => docs!(arena, arena.line(), s, arena.space()),
        //        Rule::triple_and |
        //        Rule::triple_or =>
        //            docs![arena, arena.hardline(), s, arena.space()].nest(INDENT_SPACES),
        Rule::colon_str => docs![arena, s, arena.line_(), arena.space()]
            .nest(INDENT_SPACES - 1)
            .group(),
        Rule::eq_str | Rule::eq_eq_str => {
            docs![arena, arena.space(), s, arena.line_(), arena.space()]
                .nest(INDENT_SPACES - 1)
                .group()
        }
        Rule::plus_str | Rule::rarrow_str | Rule::else_str => {
            docs![arena, arena.space(), s, arena.space()]
        }
        Rule::assert_space_str
        | Rule::async_str
        | Rule::auto_str
        | Rule::await_str
        | Rule::box_str
        | Rule::break_str
        | Rule::closed_str
        | Rule::const_str
        | Rule::continue_str
        | Rule::crate_str
        | Rule::default_str
        | Rule::do_str
        | Rule::dyn_str
        | Rule::enum_str
        | Rule::extern_str
        | Rule::f32_str
        | Rule::f64_str
        | Rule::fn_str
        | Rule::FnOnce_str
        | Rule::FnMut_str
        | Rule::FnSpec_str
        | Rule::Fn_str
        | Rule::for_str
        | Rule::ghost_str
        | Rule::global_str
        | Rule::i128_str
        | Rule::i16_str
        | Rule::i32_str
        | Rule::i64_str
        | Rule::i8_str
        | Rule::if_str
        | Rule::in_str
        | Rule::int_str
        | Rule::isize_str
        | Rule::layout_str
        | Rule::let_str
        | Rule::loop_str
        | Rule::macro_str
        | Rule::macro_rules_str
        | Rule::match_str
        | Rule::mod_str
        | Rule::move_str
        | Rule::mut_str
        | Rule::nat_str
        | Rule::open_str
        | Rule::proof_space_str
        | Rule::r_str
        | Rule::raw_str
        | Rule::ref_str
        | Rule::return_str
        | Rule::Self_str
        | Rule::sizeof_str
        | Rule::spaced_comma_str
        | Rule::spec_fn_str
        | Rule::static_str
        | Rule::struct_str
        | Rule::super_str
        | Rule::tracked_str
        | Rule::trait_str
        | Rule::trigger_str
        | Rule::triple_and
        | Rule::triple_or
        | Rule::try_str
        | Rule::type_str
        | Rule::u128_str
        | Rule::u16_str
        | Rule::u32_str
        | Rule::u64_str
        | Rule::u8_str
        | Rule::union_str
        | Rule::unsafe_str
        | Rule::use_str
        | Rule::usize_str
        | Rule::where_str
        | Rule::while_str
        | Rule::yeet_str
        | Rule::yield_str
        | Rule::broadcast_str
        | Rule::group_str
        | Rule::broadcast_group_identifier => s.append(arena.space()),

        Rule::as_str
        | Rule::by_str_inline
        | Rule::has_str
        | Rule::implies_str
        | Rule::is_str
        | Rule::matches_str => arena.space().append(s).append(arena.space()),

        Rule::by_str | Rule::via_str | Rule::when_str => arena
            .line()
            .append(s)
            .append(arena.space())
            .nest(INDENT_SPACES),

        Rule::decreases_str
        | Rule::ensures_str
        | Rule::invariant_except_break_str
        | Rule::invariant_str
        | Rule::invariant_ensures_str
        | Rule::opens_invariants_str
        | Rule::recommends_str
        | Rule::no_unwind_str
        | Rule::requires_str => arena.hardline().append(s).nest(INDENT_SPACES),

        Rule::no_unwind_when_str => arena.space().append(s).append(arena.space()),

        Rule::any_str
        | Rule::assert_str
        | Rule::assume_str
        | Rule::checked_str
        | Rule::choose_str
        | Rule::exec_str
        | Rule::exists_str
        | Rule::false_str
        | Rule::forall_str
        | Rule::none_str
        | Rule::proof_str
        | Rule::self_str
        | Rule::spec_str
        | Rule::true_str => s,
        //*************************//
        // Names, Paths and Macros //
        //*************************//
        Rule::name | Rule::name_ref => s,
        Rule::lifetime => s.append(arena.space()),
        Rule::lifetime_no_space => s,
        Rule::path => map_to_doc(ctx, arena, pair),
        Rule::path_no_generics => map_to_doc(ctx, arena, pair),
        Rule::path_segment => map_to_doc(ctx, arena, pair),
        Rule::path_segment_no_generics => map_to_doc(ctx, arena, pair),
        Rule::generic_arg_list => map_to_doc(ctx, arena, pair),
        Rule::generic_arg_list_with_colons => map_to_doc(ctx, arena, pair),
        Rule::generic_args => comma_delimited(ctx, arena, pair, false).group(),
        Rule::generic_arg => map_to_doc(ctx, arena, pair),
        Rule::type_arg => map_to_doc(ctx, arena, pair),
        Rule::assoc_type_arg => unsupported(pair),
        Rule::lifetime_arg => map_to_doc(ctx, arena, pair),
        Rule::const_arg => map_to_doc(ctx, arena, pair),
        Rule::generic_args_binding => map_to_doc(ctx, arena, pair),
        Rule::calc_macro_reln => s,
        Rule::calc_macro_body => {
            let mut inner = arena.nil();
            let pairs = pair.into_inner();
            let mut first_reln_done = false;
            for p in pairs.clone() {
                let doc = to_doc(ctx, p.clone(), arena);
                match p.as_rule() {
                    Rule::calc_macro_reln if !first_reln_done => {
                        inner = inner.append(doc).append(arena.hardline());
                        first_reln_done = true;
                    }
                    Rule::calc_macro_reln => {
                        inner = inner.append(doc).append(arena.space());
                    }
                    Rule::expr => {
                        inner = inner.append(doc);
                    }
                    Rule::semi_str => {
                        inner = inner.append(doc).append(arena.space());
                    }
                    Rule::block_expr => {
                        inner = inner.append(doc).append(arena.hardline());
                    }
                    Rule::COMMENT => {
                        inner = inner.append(doc);
                    }
                    rule @ _ => unreachable!("Unreachable rule {rule:?}"),
                }
            }
            arena.space().append(block_braces(
                arena,
                inner,
                pairs.rev().next().unwrap().as_rule() == Rule::semi_str,
            ))
        }
        Rule::calc_macro_call => map_to_doc(ctx, arena, pair),
        Rule::seq_macro_call => map_to_doc(ctx, arena, pair),
        Rule::macro_call | Rule::macro_call_stmt => {
            if pair
                .clone()
                .into_inner()
                .any(|x| matches!(x.as_rule(), Rule::calc_macro_call | Rule::seq_macro_call))
            {
                map_to_doc(ctx, arena, pair)
            } else {
                s
            }
        }
        Rule::punctuation => map_to_doc(ctx, arena, pair),
        Rule::token => map_to_doc(ctx, arena, pair),
        Rule::delim_token_tree => map_to_doc(ctx, arena, pair),
        Rule::token_tree => map_to_doc(ctx, arena, pair),
        Rule::macro_items => unsupported(pair),
        Rule::macro_stmts => unsupported(pair),

        //*************************//
        //          Items          //
        //*************************//
        Rule::item => map_to_doc(ctx, arena, pair),
        Rule::item_no_macro_call => map_to_doc(ctx, arena, pair),
        Rule::macro_rules => s, // Don't attempt to format macro rules
        Rule::global_sizeof => map_to_doc(ctx, arena, pair),
        Rule::global_layout => map_to_doc(ctx, arena, pair),
        Rule::global_inner => map_to_doc(ctx, arena, pair),
        Rule::global => map_to_doc(ctx, arena, pair),
        Rule::macro_def => unsupported(pair),
        Rule::module => map_to_doc(ctx, arena, pair),
        Rule::item_list => items_to_doc(ctx, arena, pair, true),
        Rule::extern_crate => unsupported(pair),
        Rule::rename => map_to_doc(ctx, arena, pair),
        Rule::r#use => map_to_doc(ctx, arena, pair),
        Rule::use_tree => map_to_doc(ctx, arena, pair),
        Rule::use_tree_list => comma_delimited(ctx, arena, pair, false).braces().group(),
        Rule::broadcast_use_list => comma_delimited(ctx, arena, pair, false).group(),
        Rule::broadcast_group_member => map_to_doc(ctx, arena, pair),
        Rule::broadcast_group_list => comma_delimited(ctx, arena, pair, false).braces(),
        Rule::fn_qualifier => map_to_doc(ctx, arena, pair),
        Rule::fn_terminator => map_to_doc(ctx, arena, pair),
        Rule::r#fn => {
            let pairs = pair.into_inner();
            let has_qualifier = pairs.clone().any(|p| {
                matches!(p.as_rule(), Rule::fn_qualifier) && p.clone().into_inner().count() > 0
            });
            let has_ret_type = pairs.clone().any(|p| {
                matches!(p.as_rule(), Rule::ret_type) && p.clone().into_inner().count() > 0
            });
            let mut saw_param_list = false;
            let mut saw_comment_after_param_list = false;
            let mut pre_ret_type = true;
            arena.concat(pairs.map(|p| {
                let d = to_doc(ctx, p.clone(), arena);
                match p.as_rule() {
                    Rule::fn_terminator => {
                        if has_qualifier {
                            // The terminator (fn_block_expr or semicolon) goes on a new line
                            arena.hardline().append(d)
                        } else {
                            // If the function has a body, and there isn't a comment up against
                            // the parameter list, then we need a space before the opening brace
                            if matches!(
                                p.into_inner().next().unwrap().as_rule(),
                                Rule::fn_block_expr
                            ) && !saw_comment_after_param_list
                            {
                                arena.space().append(d)
                            } else {
                                d
                            }
                        }
                    }
                    Rule::ret_type => {
                        pre_ret_type = false;
                        d
                    }
                    Rule::COMMENT => {
                        if saw_param_list {
                            saw_comment_after_param_list = true;
                        };
                        // Special case where we don't want an extra newline after the possibly inline comment
                        comment_to_doc(
                            ctx,
                            arena,
                            p,
                            !has_qualifier
                                || !saw_comment_after_param_list
                                || (has_ret_type && pre_ret_type),
                        )
                    }
                    Rule::param_list => {
                        saw_param_list = true;
                        d
                    }
                    _ => d,
                }
            }))
        }
        Rule::abi => map_to_doc(ctx, arena, pair).append(arena.space()),
        Rule::param_list => comma_delimited(ctx, arena, pair, false).parens().group(),
        Rule::closure_param_list => comma_delimited(ctx, arena, pair, false)
            .enclose(arena.text("|"), arena.text("|"))
            .group()
            .append(arena.softline_()),
        Rule::self_param => map_to_doc(ctx, arena, pair),
        Rule::param => map_to_doc(ctx, arena, pair),
        Rule::ret_type => map_to_doc(ctx, arena, pair),
        Rule::type_alias => map_to_doc(ctx, arena, pair),
        Rule::r#struct => map_to_doc(ctx, arena, pair),
        Rule::struct_update_base => arena.text("..").append(map_to_doc(ctx, arena, pair)),
        Rule::record_field_list => {
            extra_spaced_braces(arena, comma_delimited(ctx, arena, pair, false))
        }
        Rule::condensable_record_field_list => {
            let doc = extra_spaced_braces(arena, comma_delimited(ctx, arena, pair.clone(), false));
            if pair
                .into_inner()
                .clone()
                .filter(|p| matches!(p.as_rule(), Rule::COMMENT))
                .count()
                == 0
            {
                doc.group()
            } else {
                // Don't group if we detected any comments
                doc
            }
        }
        Rule::record_field => map_to_doc(ctx, arena, pair),
        Rule::tuple_field_list => comma_delimited(ctx, arena, pair, false).parens().group(),
        Rule::tuple_field => map_to_doc(ctx, arena, pair),
        Rule::field_list => map_to_doc(ctx, arena, pair),
        Rule::r#enum => map_to_doc(ctx, arena, pair),
        Rule::variant_list => arena
            .space()
            .append(comma_delimited(ctx, arena, pair, false).braces()),
        Rule::variant => map_to_doc(ctx, arena, pair),
        Rule::union => unsupported(pair),
        //Rule::initializer => soft_indent(arena, map_to_doc(ctx, arena, pair)),
        Rule::r#const | Rule::r#static =>
        // In this context, if there's an ensures clause, we need to add a line
        {
            arena.concat(pair.into_inner().map(|p| match p.as_rule() {
                Rule::ensures_clause => to_doc(ctx, p, arena).append(arena.line()),
                _ => to_doc(ctx, p, arena),
            }))
        }
        Rule::r#trait => map_to_doc(ctx, arena, pair),
        Rule::trait_alias => unsupported(pair),
        Rule::assoc_items => map_to_doc_lines(ctx, arena, pair),
        Rule::assoc_item_list => {
            arena
                .space()
                .append(block_braces(arena, map_to_doc(ctx, arena, pair), true))
        }
        Rule::assoc_item => map_to_doc(ctx, arena, pair),
        Rule::r#impl => {
            let has_generic_params = pair
                .clone()
                .into_inner()
                .find(|p| matches!(p.as_rule(), Rule::spaced_generic_param_list));
            arena.concat(pair.into_inner().map(|p| {
                let r = p.as_rule();
                let d = to_doc(ctx, p, arena);
                match r {
                    Rule::impl_str => {
                        if has_generic_params.is_none() {
                            d.append(arena.space())
                        } else {
                            d
                        }
                    }
                    Rule::for_str => arena.space().append(d),
                    _ => d,
                }
            }))
        }
        Rule::extern_block => unsupported(pair),
        Rule::extern_item_list => unsupported(pair),
        Rule::extern_item => unsupported(pair),
        Rule::generic_param_list => comma_delimited(ctx, arena, pair, false).angles().group(),
        Rule::spaced_generic_param_list => map_to_doc(ctx, arena, pair).append(arena.space()),
        Rule::generic_param => map_to_doc(ctx, arena, pair),
        Rule::type_param => map_to_doc(ctx, arena, pair),
        Rule::const_param => map_to_doc(ctx, arena, pair),
        Rule::lifetime_param => map_to_doc(ctx, arena, pair),
        Rule::where_clause => arena.space().append(map_to_doc(ctx, arena, pair)),
        Rule::where_preds => comma_delimited(ctx, arena, pair, false).group(),
        Rule::where_pred => map_to_doc(ctx, arena, pair),
        Rule::visibility => map_to_doc(ctx, arena, pair).append(arena.space()),
        Rule::attr_core => arena.text(pair.as_str()),
        Rule::attr => {
            let d = map_to_doc(ctx, arena, pair.clone());
            if is_bare_trigger(pair) {
                // As a special case, allow trigger attributes the option of staying inline
                d.append(arena.space())
            } else {
                d.append(arena.hardline())
            }
        }
        Rule::attr_inner => map_to_doc(ctx, arena, pair),
        Rule::meta => unsupported(pair),
        Rule::broadcast_use => map_to_doc(ctx, arena, pair),
        Rule::broadcast_uses => arena.concat(pair.into_inner().map(|p| {
            if matches!(p.as_rule(), Rule::broadcast_use) {
                to_doc(ctx, p, arena).append(arena.hardline())
            } else {
                // Handle the comments
                to_doc(ctx, p, arena)
            }
        })),
        Rule::broadcast_group => map_to_doc(ctx, arena, pair),

        //****************************//
        // Statements and Expressions //
        //****************************//
        Rule::stmt => map_to_doc(ctx, arena, pair).append(arena.hardline()),
        // NOTE: The code for let_stmt does not explicitly attempt to replicate the (complex) rules described here:
        //       https://doc.rust-lang.org/beta/style-guide/statements.html#let-statements
        Rule::let_stmt => map_to_doc(ctx, arena, pair).group(),
        Rule::let_else => map_to_doc(ctx, arena, pair),
        Rule::assignment_stmt => map_to_doc(ctx, arena, pair).group(),
        Rule::expr => map_to_doc(ctx, arena, pair),
        Rule::expr_inner => map_to_doc(ctx, arena, pair),
        Rule::expr_inner_no_struct => map_to_doc(ctx, arena, pair),
        Rule::expr_with_block => map_to_doc(ctx, arena, pair),
        Rule::expr_as => map_to_doc(ctx, arena, pair),
        Rule::expr_has => map_to_doc(ctx, arena, pair),
        Rule::expr_is => map_to_doc(ctx, arena, pair),
        Rule::expr_matches => map_to_doc(ctx, arena, pair),
        Rule::expr_outer => map_to_doc(ctx, arena, pair),
        Rule::expr_outer_no_struct => map_to_doc(ctx, arena, pair),
        Rule::expr_no_struct => map_to_doc(ctx, arena, pair),
        Rule::bulleted_expr => block_braces(arena, map_to_doc(ctx, arena, pair), true),
        Rule::bulleted_expr_inner => {
            let pairs = pair.into_inner();
            let mut prefix_hardline = false;
            arena.concat(pairs.map(|p| {
                let d = to_doc(ctx, p.clone(), arena);
                match p.as_rule() {
                    Rule::COMMENT => {
                        // Prevent an unnecessary additional newline after comments
                        prefix_hardline = false;
                        d
                    }
                    Rule::triple_and | Rule::triple_or => {
                        if !prefix_hardline {
                            prefix_hardline = true;
                            d
                        } else {
                            arena.hardline().append(d)
                        }
                    }
                    _ => {
                        if p.into_inner().flatten().last().unwrap().as_rule() == Rule::COMMENT {
                            // Prevent an unnecessary additional newline after comments
                            prefix_hardline = false;
                        }
                        d
                    }
                }
            }))
        }
        Rule::macro_expr => unsupported(pair),
        Rule::literal => map_to_doc(ctx, arena, pair),
        Rule::path_expr => map_to_doc(ctx, arena, pair),
        Rule::path_expr_no_generics => map_to_doc(ctx, arena, pair),
        Rule::stmt_list => {
            let rule = pair.as_rule();
            let pairs = pair.clone().into_inner();
            if pairs.len() == 0 {
                // Rust says: "An empty block should be written as {}"
                arena.text("{}")
            } else if expr_only_block(rule, &pairs) {
                // A block may be written on a single line if:
                // - it is either used in expression position (not statement position) or is an unsafe block in statement position
                // - contains a single-line expression and no statements
                // - contains no comments
                //spaced_braces(arena, map_pairs_to_doc(ctx, arena, &pairs)).nest(INDENT_SPACES) //.group()
                debug!("Processing an expr_only_block");
                sticky_delims(ctx, arena, pair, Enclosure::Braces, true)
            } else {
                debug!("Processing that's not empty and not an expr_only_block");
                let mapped = arena.concat(pairs.clone().map(|i| to_doc(ctx, i, arena)));
                block_braces(arena, mapped, terminal_expr(&pairs))
            }
        }
        Rule::ref_expr => map_to_doc(ctx, arena, pair),
        Rule::proof_block => map_to_doc(ctx, arena, pair),
        Rule::block_expr => map_to_doc(ctx, arena, pair),
        Rule::fn_block_expr => {
            let pairs = pair.into_inner();
            let mapped = map_pairs_to_doc(ctx, arena, &pairs);
            block_braces(
                arena,
                mapped,
                terminal_expr(&pairs)
                    || pairs
                        .clone()
                        .any(|x| x.as_rule() == Rule::bulleted_expr_inner),
            )
        }
        Rule::prefix_expr => map_to_doc(ctx, arena, pair),
        Rule::prefix_expr_no_struct => map_to_doc(ctx, arena, pair),
        Rule::assignment_ops => docs![arena, arena.space(), s, arena.line()],
        Rule::bin_expr_ops_normal => docs![arena, arena.line(), s, arena.space()]
            .nest(INDENT_SPACES)
            .group(),
        Rule::bin_expr_ops => map_to_doc(ctx, arena, pair),
        Rule::paren_expr_inner => sticky_delims(ctx, arena, pair, Enclosure::Parens, false),
        Rule::paren_expr => map_to_doc(ctx, arena, pair),
        Rule::array_expr_inner => sticky_delims(ctx, arena, pair, Enclosure::Brackets, false),
        Rule::array_expr => map_to_doc(ctx, arena, pair),
        Rule::tuple_comma_delimited_exprs => {
            // This requires special handling, so that we can tell comma_delimited that
            // we're processing a tuple (which requires a comma if only one element is present)
            comma_delimited(ctx, arena, pair.into_inner().next().unwrap(), true).group()
        }
        Rule::tuple_expr_inner => sticky_delims(ctx, arena, pair, Enclosure::Parens, false),
        Rule::tuple_expr => map_to_doc(ctx, arena, pair),
        Rule::struct_expr => map_to_doc(ctx, arena, pair),
        Rule::record_expr_field_list => {
            extra_spaced_braces(arena, comma_delimited(ctx, arena, pair, false)).group()
        }
        Rule::record_expr_field => map_to_doc(ctx, arena, pair),
        Rule::arg_list => sticky_delims(ctx, arena, pair, Enclosure::Parens, false),
        Rule::closure_expr | Rule::quantifier_expr | Rule::quantifier_expr_no_struct =>
        // Put the body of the closure on an indented newline if it doesn't fit the line
        {
            let has_ret = pair
                .clone()
                .into_inner()
                .any(|p| matches!(p.as_rule(), Rule::ret_type));
            arena
                .concat(pair.into_inner().map(|p| {
                    match p.as_rule() {
                        Rule::expr | Rule::expr_no_struct => arena
                            .line_()
                            .append(to_doc(ctx, p, arena))
                            .nest(INDENT_SPACES),
                        Rule::attr_inner => {
                            if is_bare_trigger(p.clone()) {
                                to_doc(ctx, p, arena).append(arena.space())
                            } else {
                                arena
                                    .line_()
                                    .append(to_doc(ctx, p, arena))
                                    .append(arena.nil().flat_alt(arena.space()))
                                    .nest(INDENT_SPACES)
                            }
                        }
                        Rule::closure_param_list => {
                            if has_ret {
                                // Don't add a space, since ret_type already does it
                                to_doc(ctx, p, arena)
                            } else {
                                to_doc(ctx, p, arena).append(arena.space())
                            }
                        }
                        Rule::ret_type => to_doc(ctx, p, arena).append(arena.space()),
                        _ => to_doc(ctx, p, arena),
                    }
                }))
                .group()
        }
        Rule::condition => map_to_doc(ctx, arena, pair),
        Rule::if_expr => if_expr_to_doc(ctx, arena, pair),
        Rule::loop_clause => map_to_doc(ctx, arena, pair),
        Rule::loop_expr => loop_to_doc(ctx, arena, pair),
        Rule::for_expr => loop_to_doc(ctx, arena, pair),
        Rule::while_expr => loop_to_doc(ctx, arena, pair),
        Rule::label => unsupported(pair),
        Rule::break_expr => map_to_doc(ctx, arena, pair),
        Rule::continue_expr => map_to_doc(ctx, arena, pair),
        Rule::match_expr => map_to_doc(ctx, arena, pair),
        Rule::match_arm_list => {
            arena
                .space()
                .append(block_braces(arena, map_to_doc(ctx, arena, pair), false))
        }
        Rule::match_arm_lhs => map_to_doc(ctx, arena, pair)
            .append(arena.text(" => "))
            .group(),
        Rule::match_arm => map_to_doc(ctx, arena, pair)
            .append(arena.text(","))
            .append(arena.line()),
        Rule::match_guard =>
        // In this context, the "if" needs a space preceding it
        {
            arena.concat(pair.into_inner().map(|p| match p.as_rule() {
                Rule::if_str => arena.text(" if "),
                _ => to_doc(ctx, p, arena),
            }))
        }
        Rule::return_expr => map_to_doc(ctx, arena, pair),
        Rule::yield_expr => map_to_doc(ctx, arena, pair),
        Rule::yeet_expr => map_to_doc(ctx, arena, pair),
        Rule::let_expr_no_struct => map_to_doc(ctx, arena, pair),
        Rule::underscore_expr => map_to_doc(ctx, arena, pair).append(arena.text("_")),
        Rule::box_expr => map_to_doc(ctx, arena, pair),

        //*************************//
        //          Types          //
        //*************************//
        Rule::r#type => map_to_doc(ctx, arena, pair),
        Rule::paren_type => map_to_doc(ctx, arena, pair).parens(),
        Rule::never_type => map_to_doc(ctx, arena, pair),
        Rule::macro_type => map_to_doc(ctx, arena, pair),
        Rule::path_type => map_to_doc(ctx, arena, pair),
        Rule::tuple_type => comma_delimited(ctx, arena, pair, false).parens().group(),
        Rule::ptr_type => map_to_doc(ctx, arena, pair),
        Rule::ref_type => arena.text("&").append(map_to_doc(ctx, arena, pair)),
        Rule::array_type =>
        // In this context, the semicolon must have a space following it
        {
            arena
                .concat(pair.into_inner().map(|p| match p.as_rule() {
                    Rule::semi_str => arena.text("; "),
                    _ => to_doc(ctx, p, arena),
                }))
                .brackets()
        }
        Rule::slice_type => map_to_doc(ctx, arena, pair).brackets(),
        Rule::infer_type => map_to_doc(ctx, arena, pair),
        Rule::fn_ptr_type => map_to_doc(ctx, arena, pair),
        Rule::fn_trait_type => map_to_doc(ctx, arena, pair),
        Rule::for_type => map_to_doc(ctx, arena, pair),
        Rule::impl_trait_type => {
            // We need to inject a space after the "impl"
            arena.concat(pair.into_inner().map(|p| match p.as_rule() {
                Rule::impl_str => arena.text("impl "),
                _ => to_doc(ctx, p, arena),
            }))
        }
        Rule::dyn_trait_type => map_to_doc(ctx, arena, pair),
        Rule::type_bound_list => map_to_doc(ctx, arena, pair),
        Rule::type_bound => map_to_doc(ctx, arena, pair),

        //************************//
        //        Patterns        //
        //************************//
        Rule::pat => map_to_doc(ctx, arena, pair),
        Rule::pat_no_top_alt => map_to_doc(ctx, arena, pair),
        Rule::pat_inner => map_to_doc(ctx, arena, pair),
        Rule::literal_pat => map_to_doc(ctx, arena, pair),
        Rule::ident_pat => map_to_doc(ctx, arena, pair),
        //Rule::wildcard_pat => arena.text("_"),
        Rule::end_only_range_pat => map_to_doc(ctx, arena, pair),
        Rule::ref_pat => arena.text("&").append(map_to_doc(ctx, arena, pair)),
        Rule::record_pat => arena.concat(pair.into_inner().map(|p| match p.as_rule() {
            Rule::path => to_doc(ctx, p, arena).append(arena.space()),
            _ => to_doc(ctx, p, arena),
        })),
        Rule::record_pat_field_list => {
            spaced_braces(arena, comma_delimited(ctx, arena, pair, false)).group()
        }
        Rule::record_pat_field => map_to_doc(ctx, arena, pair),
        Rule::tuple_struct_pat_inner => comma_delimited(ctx, arena, pair, false).parens().group(),
        Rule::tuple_struct_pat => map_to_doc(ctx, arena, pair),
        Rule::tuple_pat => comma_delimited(ctx, arena, pair, false).parens().group(),
        Rule::paren_pat => map_to_doc(ctx, arena, pair).parens(),
        Rule::slice_pat => comma_delimited(ctx, arena, pair, false).brackets().group(),
        Rule::path_pat => map_to_doc(ctx, arena, pair),
        Rule::box_pat => map_to_doc(ctx, arena, pair),
        Rule::rest_pat => map_to_doc(ctx, arena, pair),
        Rule::macro_pat => unsupported(pair),
        Rule::const_block_pat => unsupported(pair),

        //************************//
        //        Verus           //
        //************************//
        Rule::publish => map_to_doc(ctx, arena, pair),
        Rule::fn_mode => map_to_doc(ctx, arena, pair).append(arena.space()),
        Rule::mode_spec_checked => map_to_doc(ctx, arena, pair),
        Rule::data_mode => map_to_doc(ctx, arena, pair),
        Rule::comma_delimited_exprs => comma_delimited(ctx, arena, pair, false).group(),
        Rule::comma_delimited_exprs_for_verus_clauses => {
            comma_delimited_full(ctx, arena, pair).nest(INDENT_SPACES)
        }
        Rule::groupable_comma_delimited_exprs_for_verus_clauses => {
            map_to_doc(ctx, arena, pair).nest(INDENT_SPACES).group()
        }
        Rule::verus_clause_non_expr => map_to_doc(ctx, arena, pair),
        Rule::requires_clause => map_to_doc(ctx, arena, pair),
        Rule::ensures_clause => map_to_doc(ctx, arena, pair),
        Rule::invariant_except_break_clause => map_to_doc(ctx, arena, pair),
        Rule::invariant_clause => map_to_doc(ctx, arena, pair),
        Rule::invariant_ensures_clause => map_to_doc(ctx, arena, pair),
        Rule::recommends_clause => map_to_doc(ctx, arena, pair),
        Rule::decreases_clause => map_to_doc(ctx, arena, pair),
        Rule::unwind_clause => map_to_doc(ctx, arena, pair),
        Rule::opens_invariants_mode => arena.space().append(map_to_doc(ctx, arena, pair)),
        Rule::opens_invariants_clause => map_to_doc(ctx, arena, pair),
        Rule::assert_requires => map_to_doc(ctx, arena, pair).append(arena.line()),
        Rule::assert_expr_prefix
        | Rule::assert_by_block_expr
        | Rule::assert_by_prover_expr
        | Rule::assert_expr => map_to_doc(ctx, arena, pair).group(),
        Rule::assume_expr => map_to_doc(ctx, arena, pair),
        Rule::assert_forall_expr => map_to_doc(ctx, arena, pair),
        Rule::prover => map_to_doc(ctx, arena, pair),
        Rule::inline_prover => map_to_doc(ctx, arena, pair).group(),
        Rule::trigger_attribute => unsupported(pair),

        Rule::WHITESPACE => arena.nil(),
        Rule::MULTI_NEWLINE => arena.hardline(),
        Rule::COMMENT => comment_to_doc(ctx, arena, pair, true),
        Rule::multiline_comment => s.append(arena.line()),
        Rule::verus_macro_body => items_to_doc(ctx, arena, pair, false),
        Rule::file | Rule::non_verus | Rule::verus_macro_use | Rule::EOI => unreachable!(),
    }
}

fn format_item(ctx: &Context, item: Pair<Rule>) -> String {
    let arena = Arena::<()>::new();
    let doc = to_doc(ctx, item, &arena).into_doc();
    debug!("{:?}", doc);
    format_doc(doc)
}

/*
 * Inline comments are difficult to handle.  Because pest reads them implicitly,
 * code like this:
 *   // Comment 1
 *   foo(x);    // Comment 2
 * gets parsed as three siblings.  Hence, when we process `foo(x)`, we don't know
 * that we shouldn't add a newline after the semicolon.  And by the time we process
 * `// Comment 2`, it's too late to retract the previous newline.  Hence, the current
 * hack is to preprocess the file to identify all inline comments (we can't do this as part
 * of the formatting pass, since when we reach `Comment 2` we can't ask it if other code
 * preceded it).  Then when we generate the formatted version, we add a marker to comments
 * we have identified as inline.  Finally, after the formatted version is converted to
 * a string, we postprocess the string to move the inline comments back to their inline position.
 *
 */

const INLINE_COMMENT_FIXUP: &str = "FORMATTER_FIXUP";
const NONINLINE_COMMENT_MARKER: &str = "FORMATTER_NOT_INLINE_MARKER";
const NONINLINE_COMMENT_DST: &str = "FORMATTER_NOT_INLINE_DST";

// Identify lines where non-whitespace precedes the start of a comment (re_inline_candidate);
// we also have to check for an earlier whitespace-prefixed comment (re_spaced_comment) that
// dominates candidates found above, like in this example:
//   let x = 10;
//   // x = 5;  // We can't do this because x is not mutable
//   let y = 5;
fn find_inline_comment_lines(s: &str) -> HashSet<usize> {
    let mut comment_lines = HashSet::new();
    let re_inline_candidate = Regex::new(r"^.*\S.*(//|/\*.*\*/)").unwrap();
    let re_spaced_comment = Regex::new(r"^\s*(///|//|/\*)").unwrap();
    for (line_num, line) in s.lines().enumerate() {
        if re_inline_candidate.captures(line).is_some()
            && re_spaced_comment.captures(line).is_none()
        {
            comment_lines.insert(line_num + 1);
        }
    }
    comment_lines
}

fn is_inline_comment(s: &str) -> bool {
    let comment_start = match (s.find("//"), s.find("/*")) {
        (Some(l), Some(r)) => std::cmp::min(l, r),
        (Some(l), None) => l,
        (None, Some(r)) => r,
        (None, None) => panic!("Failed to find a comment!: {}", s),
    };
    let prefix = &s[0..comment_start];
    let re_non_whitespace = Regex::new(r"^.*\S.*").unwrap();
    re_non_whitespace.is_match(prefix)
}

// Make sure single-line comments end up inline if they started inline or non-inline if they
// started non-inline. See `comment_to_doc` for details.
fn fix_inline_comments(s: String) -> String {
    debug!(
        "Formatted output (before comment fixes):\n>>>>>>>\n{}\n<<<<<<<<<<<\n",
        s
    );

    // Finds comments that started life as inline comments
    let re_was_inline = Regex::new(INLINE_COMMENT_FIXUP).unwrap();
    // Find a comment that got inlined
    let re_find_inline = Regex::new(r"(^.*\S.*)((//|/\*).*)").unwrap();
    // Finds comments that started life not inline
    let re_noninline = Regex::new(NONINLINE_COMMENT_MARKER).unwrap();
    // Finds the destination marker for noninline comments
    let re_noninline_dst = Regex::new(NONINLINE_COMMENT_DST).unwrap();

    let mut fixed_str: String = String::new();
    let mut prev_str: String = "".to_string();
    let mut first_iteration = true;
    let mut comment_replacement = None;
    //let mut line_num = 1;

    for line in s.lines() {
        fixed_str += &prev_str;
        //println!("Processing line {}", line_num);
        //line_num += 1;
        if re_was_inline.is_match(line) {
            if is_inline_comment(line) {
                // After we formatted the inline comment, it's still inline,
                // so just remove our marker but otherwise leave the line alone
                fixed_str += "\n";
                prev_str = line.replace(INLINE_COMMENT_FIXUP, "");
            } else {
                // The formerly inline comment is now on a line by itself, so move it back to the
                // previous line
                prev_str = format!(
                    "{:indent$}{}",
                    "",
                    line.trim_start().replace(INLINE_COMMENT_FIXUP, ""),
                    indent = INLINE_COMMENT_SPACE
                );
            }
        } else if re_noninline.is_match(line) {
            if is_inline_comment(line) {
                // Use is_inline_comment to account for comments about comments
                // This previously independent comment was absorbed into the preceding line
                // Move it to the next line in place of the destination marker we created
                let caps = re_find_inline.captures(line).unwrap();
                comment_replacement =
                    Some(caps[2].to_string().replace(NONINLINE_COMMENT_MARKER, ""));
                fixed_str += "\n";
                prev_str = caps[1].to_string();
            } else {
                // This independent comment is still independent, so leave it there,
                // but remove the marker we added to the next line
                comment_replacement = None;
                fixed_str += "\n";
                prev_str = line.replace(NONINLINE_COMMENT_MARKER, "");
            }
        } else if re_noninline_dst.is_match(line) {
            match comment_replacement {
                None => {
                    // We want to delete this line entirely, so don't add a newline to the fixed_str
                    prev_str = "".to_string();
                }
                Some(ref c) => {
                    // Replace our marker with the comment
                    fixed_str += "\n";
                    prev_str = line.replace(NONINLINE_COMMENT_DST, c);
                }
            }
        } else {
            if !first_iteration {
                fixed_str += "\n";
            }
            prev_str = line.to_string();
        }
        first_iteration = false;
    }
    fixed_str += &prev_str;
    fixed_str += "\n";
    fixed_str
}

fn strip_whitespace(s: String) -> String {
    let mut fixed_str: String = String::new();
    for line in s.lines() {
        fixed_str += line.trim_end();
        fixed_str += "\n";
    }
    fixed_str
}

#[doc(hidden)]
pub const VERUS_PREFIX: &str = "verus! {\n\n";
#[doc(hidden)]
pub const VERUS_SUFFIX: &str = "\n} // verus!\n";

fn is_multiline_comment(pair: &Pair<Rule>) -> bool {
    matches!(&pair.as_span().as_str()[..2], "/*")
}

#[derive(thiserror::Error, Debug)]
/// A failure in running verusfmt
pub enum ParseAndFormatError {
    #[error("Failed to parse")]
    ParseError { pest_err: pest::error::Error<Rule> },
}

impl From<pest::error::Error<Rule>> for ParseAndFormatError {
    fn from(pest_err: pest::error::Error<Rule>) -> Self {
        Self::ParseError { pest_err }
    }
}

impl miette::Diagnostic for ParseAndFormatError {
    fn help<'a>(&'a self) -> Option<Box<dyn std::fmt::Display + 'a>> {
        match self {
            ParseAndFormatError::ParseError { pest_err, .. } => {
                let mut help = String::new();
                match &pest_err.variant {
                    pest::error::ErrorVariant::ParsingError {
                        positives,
                        negatives,
                    } => {
                        if !positives.is_empty() {
                            help += "Expected one of: ";
                            for (i, p) in positives.iter().enumerate() {
                                if i > 0 {
                                    help += ", ";
                                }
                                help += format!("{:?}", p).as_str();
                            }
                        }
                        if !negatives.is_empty() {
                            if !help.is_empty() {
                                help += "; ";
                            }
                            help += "Negatives: ";
                            for (i, n) in negatives.iter().enumerate() {
                                if i > 0 {
                                    help += ", ";
                                }
                                help += format!("{:?}", n).as_str();
                            }
                        }
                        if help.is_empty() {
                            return None;
                        }
                    }
                    pest::error::ErrorVariant::CustomError { message } => {
                        help += message;
                    }
                }
                Some(Box::new(help))
            }
        }
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        match self {
            ParseAndFormatError::ParseError { pest_err, .. } => {
                let (start, len) = match pest_err.location {
                    pest::error::InputLocation::Pos(start) => (start, 1),
                    pest::error::InputLocation::Span((start, end)) => (start, end - start),
                };

                Some(Box::new(std::iter::once(miette::LabeledSpan::new(
                    Some("here".to_owned()),
                    start,
                    len,
                ))))
            }
        }
    }
}

fn parse_and_format(s: &str) -> miette::Result<String> {
    let ctx = Context {
        inline_comment_lines: find_inline_comment_lines(s),
    };
    let parsed_file = VerusParser::parse(Rule::file, s)
        .map_err(ParseAndFormatError::from)?
        .next()
        .expect("There will be exactly one `file` rule matched in a valid parsed file")
        .into_inner();
    let mut visitor = visitor::VerusVisitor::new();
    visitor.visit_all(parsed_file.clone());
    let reconstructed: &str = visitor.after();


    let reparsed_file = VerusParser::parse(Rule::file, reconstructed)
        .map_err(ParseAndFormatError::from)?
        .next()
        .expect("There will be exactly one `file` rule matched in a valid parsed file")
        .into_inner();


    let mut formatted_output = String::new();

    for pair in reparsed_file {
        if enabled!(Level::DEBUG) {
            debug_print(pair.clone(), 0);
        }
        let rule = pair.as_rule();
        debug!(?rule, "Processing top-level");
        match rule {
            Rule::non_verus | Rule::COMMENT => {
                formatted_output += pair.as_str();
                if matches!(pair.as_rule(), Rule::COMMENT) {
                    formatted_output += "\n";
                }
            }
            Rule::verus_macro_use => {
                let body = pair.into_inner().collect::<Vec<_>>();
                let (prefix_comments, body, suffix_comments) = {
                    assert_eq!(
                        body.iter().filter(|p| p.as_rule() != Rule::COMMENT).count(),
                        1
                    );
                    let body_index = body
                        .iter()
                        .position(|p| p.as_rule() != Rule::COMMENT)
                        .unwrap();
                    let mut body_iter = body.into_iter();
                    let prefix_comments: Vec<_> = body_iter.by_ref().take(body_index).collect();
                    let body = body_iter.by_ref().next().unwrap();
                    let suffix_comments: Vec<_> = body_iter.collect();
                    (prefix_comments, body, suffix_comments)
                };
                formatted_output += VERUS_PREFIX;
                for comment in &prefix_comments {
                    formatted_output += comment.as_str();
                    formatted_output += "\n";
                }

                formatted_output += &format_item(&ctx, body);

                if !suffix_comments.is_empty() {
                    formatted_output += "\n";
                }
                let mut first = true;
                for comment in suffix_comments {
                    if !first {
                        formatted_output += "\n";
                    } else {
                        first = false;
                    }
                    formatted_output += comment.as_str();
                }
                formatted_output += VERUS_SUFFIX;
            }
            Rule::EOI => {
                // end of input; do nothing
            }
            _ => unreachable!("Unexpected rule: {:?}", rule),
        }
    }
    let fixed_output = fix_inline_comments(formatted_output);
    let fixed_output = strip_whitespace(fixed_output);
    Ok(fixed_output)
}

/// Options to pass to [`run`]
pub struct RunOptions {
    /// The file name. If provided, improves diagnostics.
    pub file_name: Option<String>,
    /// Whether to run rustfmt on non-verus parts of code.
    pub run_rustfmt: bool,
    /// Whether to perform extra configuration for the rustfmt run. Ignored if `run_rustfmt` is false.
    pub rustfmt_config: RustFmtConfig,
}

impl Default for RunOptions {
    fn default() -> Self {
        Self {
            file_name: None,
            run_rustfmt: true,
            rustfmt_config: Default::default(),
        }
    }
}

/// Run `verusfmt`
pub fn run(s: &str, opts: RunOptions) -> miette::Result<String> {
    let unparsed_file = s;

    let file_name = opts.file_name.clone().unwrap_or("<input>".into());

    let verus_fmted = parse_and_format(unparsed_file).map_err(|e| {
        e.with_source_code(miette::NamedSource::new(
            file_name,
            unparsed_file.to_owned(),
        ))
    })?;

    let formatted_output = if !opts.run_rustfmt {
        verus_fmted
    } else {
        opts.rustfmt_config
            .run(&verus_fmted)
            .ok_or(miette::miette!("rustfmt failed"))?
    };

    Ok(formatted_output)
}
