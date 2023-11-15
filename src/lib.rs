#![allow(dead_code, unused_imports)] // TEMPORARY
#![allow(unstable_name_collisions)] // Needed due to Itertools::intersperse
use itertools::Itertools;
use pest::{iterators::Pair, iterators::Pairs, Parser};
use pest_derive::Parser;
use pretty::*;
use regex::Regex;
use std::collections::HashSet;
use std::io::Write;
use std::process::{Command, Stdio};
use std::str::from_utf8;
use tracing::{debug, enabled, error, info, trace, Level};

#[derive(Parser)]
#[grammar = "verus.pest"]
pub struct VerusParser;

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

/// Adds a space that turns into a newline plus indentation when in multi-line mode
fn soft_indent<'a>(
    arena: &'a Arena<'a, ()>,
    doc: DocBuilder<'a, Arena<'a>>,
) -> DocBuilder<'a, Arena<'a>> {
    arena.softline().append(doc).nest(INDENT_SPACES)
}

/// Adds a comma that vanishes in single-line mode
fn conditional_comma<'a>(arena: &'a Arena<'a, ()>) -> DocBuilder<'a, Arena<'a>> {
    arena.text(",").flat_alt(arena.nil()) //.group()
}

/// Comma-delimited list with an optional final comma
fn comma_delimited<'a>(
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
                } else if num_non_comments > 0 {
                    to_doc(ctx, p, arena).append(conditional_comma(arena))
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
) -> DocBuilder<'a, Arena<'a>> {
    use Enclosure::*;
    // Braces get a space when placed on a single line; the rest don't
    let opening = match enc {
        Braces => "{",
        Brackets => "[",
        Parens => "(",
    };
    // Braces get a space when placed on a single line; the rest don't
    let opening_space = match enc {
        Braces => arena.line_(),
        Brackets => arena.line_(),
        Parens => arena.line_(),
    };
    let closing = match enc {
        Braces => "}",
        Brackets => "]",
        Parens => ")",
    };
    let closing_space = match enc {
        Braces => arena.line(), //.text(" "),
        Brackets => arena.nil(),
        Parens => arena.nil(),
    };
    let pairs = pair.into_inner();
    if pairs.clone().count() == 0 {
        // Don't allow breaks in the list when the list is empty
        docs![arena, opening, closing,].group()
    } else {
        let docs = arena.concat(pairs.map(|p| to_doc(ctx, p, arena)));
        docs![arena, opening, opening_space,]
            .group()
            .append(if matches!(enc, Braces) {
                arena.line()
            } else {
                arena.nil()
            })
            .append(docs)
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
            "contains(line = <<{}>>), with {}",
            pair.as_str(),
            add_newline
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
    } else {
        s.append(arena.line())
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

/// Checks if a block may be written on a single line.  Rust says this is okay if:
/// - it is either used in expression position (not statement position) or is an unsafe block in statement position
/// - contains a single-line expression and no statements
/// - contains no comments
fn expr_only_block(r: Rule, pairs: &Pairs<Rule>) -> bool {
    assert!(matches!(r, Rule::stmt_list));
    let count = pairs.clone().fold(0, |count, p| {
        count
            + match p.as_rule() {
                Rule::attr | Rule::stmt | Rule::COMMENT => 1,
                Rule::expr => -1,
                _ => 0,
            }
    });
    return count == -1;
}

/// Checks if a block terminates in an expression
fn terminal_expr(pairs: &Pairs<Rule>) -> bool {
    let e = pairs.clone().find(|p| matches!(p.as_rule(), Rule::expr));
    !e.is_none()
}

fn debug_print(pair: Pair<Rule>, indent: usize) {
    print!("{:indent$}{:?} {{", "", pair.as_rule(), indent = indent);
    let pairs = pair.into_inner();
    if pairs.peek().is_some() {
        print!("\n");
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
        | Rule::float_number
        | Rule::lifetime_ident
        | Rule::string
        | Rule::raw_string
        | Rule::raw_string_interior
        | Rule::byte_string
        | Rule::raw_byte_string
        | Rule::r#char
        | Rule::byte => s,

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
        | Rule::question_str
        | Rule::rangle_str
        | Rule::rbrace_str
        | Rule::rbracket_str
        | Rule::rparen_str
        | Rule::semi_str
        | Rule::star_str
        | Rule::tilde_str
        | Rule::underscore_str => s,
        Rule::fn_traits => s,
        Rule::pipe_str => docs!(arena, arena.line(), s, arena.space()),
        Rule::rarrow_str => docs!(arena, arena.space(), s, arena.space()),
        //        Rule::triple_and |
        //        Rule::triple_or =>
        //            docs![arena, arena.hardline(), s, arena.space()].nest(INDENT_SPACES),
        Rule::colon_str => docs![arena, s, arena.line_(), arena.space()]
            .nest(INDENT_SPACES - 1)
            .group(),
        Rule::eq_str => docs![arena, arena.space(), s, arena.line_(), arena.space()]
            .nest(INDENT_SPACES - 1)
            .group(),
        Rule::else_str => docs![arena, arena.space(), s, arena.space()],
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
        | Rule::ghost_str
        | Rule::i128_str
        | Rule::i16_str
        | Rule::i32_str
        | Rule::i64_str
        | Rule::i8_str
        | Rule::if_str
        | Rule::impl_str
        | Rule::in_str
        | Rule::int_str
        | Rule::invariant_str
        | Rule::isize_str
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
        | Rule::pub_str
        | Rule::r_str
        | Rule::raw_str
        | Rule::ref_str
        | Rule::return_str
        | Rule::Self_str
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
        | Rule::yield_str => s.append(arena.space()),

        Rule::as_str
        | Rule::by_str_inline
        | Rule::for_str
        | Rule::has_str
        | Rule::implies_str
        | Rule::is_str => arena.space().append(s).append(arena.space()),

        Rule::by_str | Rule::via_str | Rule::when_str => arena
            .line()
            .append(s)
            .append(arena.space())
            .nest(INDENT_SPACES),

        Rule::decreases_str | Rule::ensures_str | Rule::recommends_str | Rule::requires_str => {
            arena.hardline().append(s).nest(INDENT_SPACES)
        }

        Rule::assert_str
        | Rule::assume_str
        | Rule::checked_str
        | Rule::choose_str
        | Rule::exec_str
        | Rule::exists_str
        | Rule::false_str
        | Rule::forall_str
        | Rule::proof_str
        | Rule::self_str
        | Rule::spec_str
        | Rule::true_str => s,
        //*************************//
        // Names, Paths and Macros //
        //*************************//
        Rule::name | Rule::name_ref | Rule::lifetime => s,
        Rule::path => map_to_doc(ctx, arena, pair),
        Rule::path_segment => map_to_doc(ctx, arena, pair),
        Rule::generic_arg_list => map_to_doc(ctx, arena, pair),
        Rule::generic_args => comma_delimited(ctx, arena, pair).group(),
        Rule::generic_arg => map_to_doc(ctx, arena, pair),
        Rule::type_arg => map_to_doc(ctx, arena, pair),
        Rule::assoc_type_arg => unsupported(pair),
        Rule::lifetime_arg => map_to_doc(ctx, arena, pair),
        Rule::const_arg => unsupported(pair),
        Rule::macro_call => s,
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
        Rule::macro_rules => unsupported(pair),
        Rule::macro_def => unsupported(pair),
        Rule::module => unsupported(pair),
        Rule::item_list => unsupported(pair),
        Rule::extern_crate => unsupported(pair),
        Rule::rename => map_to_doc(ctx, arena, pair),
        Rule::r#use => map_to_doc(ctx, arena, pair),
        Rule::use_tree => map_to_doc(ctx, arena, pair),
        Rule::use_tree_list => comma_delimited(ctx, arena, pair).braces().group(),
        Rule::fn_qualifier => map_to_doc(ctx, arena, pair),
        Rule::fn_terminator => map_to_doc(ctx, arena, pair),
        Rule::r#fn => {
            let pairs = pair.into_inner();
            let has_qualifier = pairs
                .clone()
                .find(|p| {
                    matches!(p.as_rule(), Rule::fn_qualifier) && p.clone().into_inner().count() > 0
                })
                .is_some();
            let mut saw_param_list = false;
            let mut saw_comment_after_param_list = false;
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
                    Rule::COMMENT => {
                        if saw_param_list {
                            saw_comment_after_param_list = true;
                        };
                        // Special case where we don't want an extra newline after the possibly inline comment
                        comment_to_doc(
                            ctx,
                            arena,
                            p,
                            !has_qualifier || !saw_comment_after_param_list,
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
        Rule::abi => unsupported(pair),
        Rule::param_list => comma_delimited(ctx, arena, pair).parens().group(),
        Rule::closure_param_list => comma_delimited(ctx, arena, pair)
            .enclose(arena.text("|"), arena.text("|"))
            .group()
            .append(arena.softline()),
        Rule::self_param => map_to_doc(ctx, arena, pair),
        Rule::param => map_to_doc(ctx, arena, pair),
        Rule::ret_type => map_to_doc(ctx, arena, pair),
        Rule::type_alias => map_to_doc(ctx, arena, pair),
        Rule::r#struct => map_to_doc(ctx, arena, pair),
        Rule::record_field_list => extra_spaced_braces(arena, comma_delimited(ctx, arena, pair)),
        Rule::condensable_record_field_list => {
            extra_spaced_braces(arena, comma_delimited(ctx, arena, pair)).group()
        }
        Rule::record_field => map_to_doc(ctx, arena, pair),
        Rule::tuple_field_list => comma_delimited(ctx, arena, pair).parens().group(),
        Rule::tuple_field => map_to_doc(ctx, arena, pair),
        Rule::field_list => map_to_doc(ctx, arena, pair),
        Rule::r#enum => map_to_doc(ctx, arena, pair),
        Rule::variant_list => arena
            .space()
            .append(comma_delimited(ctx, arena, pair).braces()),
        Rule::variant => map_to_doc(ctx, arena, pair),
        Rule::union => unsupported(pair),
        //Rule::initializer => soft_indent(arena, map_to_doc(ctx, arena, pair)),
        Rule::r#const => map_to_doc(ctx, arena, pair),
        Rule::r#static => unsupported(pair),
        Rule::r#trait => map_to_doc(ctx, arena, pair),
        Rule::trait_alias => unsupported(pair),
        Rule::assoc_items => map_to_doc_lines(ctx, arena, pair),
        Rule::assoc_item_list => {
            arena
                .space()
                .append(block_braces(arena, map_to_doc(ctx, arena, pair), true))
        }
        Rule::assoc_item => map_to_doc(ctx, arena, pair),
        Rule::r#impl => map_to_doc(ctx, arena, pair),
        Rule::extern_block => unsupported(pair),
        Rule::extern_item_list => unsupported(pair),
        Rule::extern_item => unsupported(pair),
        Rule::generic_param_list => comma_delimited(ctx, arena, pair).angles().group(),
        Rule::generic_param => map_to_doc(ctx, arena, pair),
        Rule::type_param => map_to_doc(ctx, arena, pair),
        Rule::const_param => unsupported(pair),
        Rule::lifetime_param => unsupported(pair),
        Rule::where_clause => unsupported(pair),
        Rule::where_pred => unsupported(pair),
        Rule::visibility => s.append(arena.space()),
        Rule::attr_core => arena.text(pair.as_str()),
        Rule::attr => map_to_doc(ctx, arena, pair).append(arena.hardline()),
        Rule::attr_inner => map_to_doc(ctx, arena, pair),
        Rule::meta => unsupported(pair),

        //****************************//
        // Statements and Expressions //
        //****************************//
        Rule::stmt => map_to_doc(ctx, arena, pair).append(arena.hardline()),
        // NOTE: The code for let_stmt does not explicitly attempt to replicate the (complex) rules described here:
        //       https://doc.rust-lang.org/beta/style-guide/statements.html#let-statements
        Rule::let_stmt => map_to_doc(ctx, arena, pair).group(),
        Rule::let_else => unsupported(pair),
        Rule::assignment_stmt => map_to_doc(ctx, arena, pair).group(),
        Rule::expr => map_to_doc(ctx, arena, pair),
        Rule::expr_inner => map_to_doc(ctx, arena, pair),
        Rule::expr_inner_no_struct => map_to_doc(ctx, arena, pair),
        Rule::expr_with_block => map_to_doc(ctx, arena, pair),
        Rule::expr_as => map_to_doc(ctx, arena, pair),
        Rule::expr_has => map_to_doc(ctx, arena, pair),
        Rule::expr_is => map_to_doc(ctx, arena, pair),
        Rule::expr_outer => map_to_doc(ctx, arena, pair),
        Rule::expr_outer_no_struct => map_to_doc(ctx, arena, pair),
        Rule::expr_no_struct => map_to_doc(ctx, arena, pair),
        Rule::macro_expr => unsupported(pair),
        Rule::literal => map_to_doc(ctx, arena, pair),
        Rule::path_expr => map_to_doc(ctx, arena, pair),
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
                sticky_delims(ctx, arena, pair, Enclosure::Braces)
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
            block_braces(arena, mapped, terminal_expr(&pairs))
        }
        Rule::prefix_expr => map_to_doc(ctx, arena, pair),
        Rule::assignment_ops => docs![arena, arena.space(), s, arena.line()],
        Rule::bin_expr_ops_special => arena.hardline().append(map_to_doc(ctx, arena, pair)),
        Rule::bin_expr_ops_normal => docs![arena, arena.line(), s, arena.space()]
            .nest(INDENT_SPACES)
            .group(),
        Rule::bin_expr_ops => map_to_doc(ctx, arena, pair),
        Rule::paren_expr_inner => sticky_delims(ctx, arena, pair, Enclosure::Parens),
        Rule::paren_expr => map_to_doc(ctx, arena, pair),
        Rule::array_expr_inner => sticky_delims(ctx, arena, pair, Enclosure::Brackets),
        Rule::array_expr => map_to_doc(ctx, arena, pair),
        Rule::tuple_expr_inner => sticky_delims(ctx, arena, pair, Enclosure::Parens),
        Rule::tuple_expr => map_to_doc(ctx, arena, pair),
        Rule::struct_expr => map_to_doc(ctx, arena, pair),
        Rule::record_expr_field_list => {
            extra_spaced_braces(arena, comma_delimited(ctx, arena, pair)).group()
        }
        Rule::record_expr_field => map_to_doc(ctx, arena, pair),
        Rule::arg_list => sticky_delims(ctx, arena, pair, Enclosure::Parens),
        Rule::closure_expr | Rule::quantifier_expr =>
        // Put the body of the closure on an indented newline if it doesn't fit the line
        {
            arena
                .concat(pair.into_inner().map(|p| {
                    match p.as_rule() {
                        Rule::expr | Rule::expr_no_struct => arena
                            .line_()
                            .append(to_doc(ctx, p, arena))
                            .nest(INDENT_SPACES),
                        Rule::attr_inner => arena
                            .line_()
                            .append(to_doc(ctx, p, arena))
                            .append(arena.nil().flat_alt(arena.text(" ")))
                            .nest(INDENT_SPACES),
                        _ => to_doc(ctx, p, arena),
                    }
                }))
                .group()
        }
        Rule::condition => map_to_doc(ctx, arena, pair).append(arena.space()),
        Rule::if_expr => map_to_doc(ctx, arena, pair),
        Rule::loop_expr => unsupported(pair),
        Rule::for_expr => unsupported(pair),
        Rule::while_expr => map_to_doc(ctx, arena, pair),
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
        Rule::match_guard => unsupported(pair),
        Rule::return_expr => map_to_doc(ctx, arena, pair),
        Rule::yield_expr => map_to_doc(ctx, arena, pair),
        Rule::yeet_expr => map_to_doc(ctx, arena, pair),
        Rule::let_expr => map_to_doc(ctx, arena, pair),
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
        Rule::tuple_type => comma_delimited(ctx, arena, pair).parens().group(),
        Rule::ptr_type => arena.text("*").append(map_to_doc(ctx, arena, pair)),
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
        Rule::impl_trait_type => map_to_doc(ctx, arena, pair),
        Rule::dyn_trait_type => map_to_doc(ctx, arena, pair),
        Rule::type_bound_list => unsupported(pair),
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
        Rule::record_pat => map_to_doc(ctx, arena, pair),
        Rule::record_pat_field_list => comma_delimited(ctx, arena, pair).braces().group(),
        Rule::record_pat_field => map_to_doc(ctx, arena, pair),
        Rule::tuple_struct_pat_inner => comma_delimited(ctx, arena, pair).parens().group(),
        Rule::tuple_struct_pat => map_to_doc(ctx, arena, pair),
        Rule::tuple_pat => comma_delimited(ctx, arena, pair).parens().group(),
        Rule::paren_pat => map_to_doc(ctx, arena, pair).parens(),
        Rule::slice_pat => comma_delimited(ctx, arena, pair).brackets().group(),
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
        Rule::comma_delimited_exprs => comma_delimited(ctx, arena, pair).group(),
        Rule::comma_delimited_exprs_for_verus_clauses => {
            comma_delimited_full(ctx, arena, pair).nest(INDENT_SPACES)
        }
        Rule::groupable_comma_delimited_exprs_for_verus_clauses => {
            map_to_doc(ctx, arena, pair).nest(INDENT_SPACES).group()
        }
        Rule::verus_clause_non_expr => map_to_doc(ctx, arena, pair),
        Rule::requires_clause => map_to_doc(ctx, arena, pair),
        Rule::ensures_clause => map_to_doc(ctx, arena, pair),
        Rule::invariant_clause => unsupported(pair),
        Rule::recommends_clause => map_to_doc(ctx, arena, pair),
        Rule::decreases_clause => map_to_doc(ctx, arena, pair),
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
        Rule::COMMENT => comment_to_doc(ctx, arena, pair, true),
        Rule::multiline_comment => s.append(arena.line()),
        Rule::file
        | Rule::non_verus
        | Rule::verus_macro_use
        | Rule::verus_macro_body
        | Rule::EOI => unreachable!(),
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

// Identify lines where non-whitespace precedes the start of a comment (re_inline_candidate);
// we also have to check for an earlier whitespace-prefixed comment (re_spaced_comment) that
// dominates candidates found above, like in this example:
//   let x = 10;
//   // x = 5;  // We can't do this because x is not mutable
//   let y = 5;
fn find_inline_comment_lines(s: &str) -> HashSet<usize> {
    let mut comment_lines = HashSet::new();
    let re_inline_candidate = Regex::new(r"^.*\S.*[^/](//|/\*)").unwrap();
    let re_spaced_comment = Regex::new(r"^\s*(///|//|/\*)").unwrap();
    for (line_num, line) in s.lines().enumerate() {
        if re_inline_candidate.captures(line).is_some()
            && re_spaced_comment.captures(line).is_none()
        {
            comment_lines.insert(line_num + 1);
        }
    }
    return comment_lines;
}

// Put inline comments back on their original line, rather than a line of their own
fn fix_inline_comments(s: String) -> String {
    debug!(
        "Formatted output (before comment fixes):\n>>>>>>>\n{}\n<<<<<<<<<<<\n",
        s
    );
    let mut fixed_str: String = String::new();
    let mut prev_str: String = "".to_string();
    let mut first_iteration = true;

    let re = Regex::new(INLINE_COMMENT_FIXUP).unwrap();
    let re_still_inline = Regex::new(r"^.*\S.*[^/](//|/\*)").unwrap();
    for line in s.lines() {
        fixed_str += &prev_str;
        if re.captures(line).is_some() {
            if re_still_inline.captures(line).is_some() {
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
    return fixed_str;
}

pub const VERUS_PREFIX: &str = "verus! {\n\n";
pub const VERUS_SUFFIX: &str = "\n} // verus!\n";

/// Run rustfmt
pub fn rustfmt(value: &str) -> Option<String> {
    if let Ok(mut proc) = Command::new("rustfmt")
        .arg("--emit=stdout")
        .arg("--edition=2021")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
    {
        {
            let stdin = proc.stdin.as_mut().unwrap();
            stdin.write_all(value.as_bytes()).unwrap();
        }
        if let Ok(output) = proc.wait_with_output() {
            if output.status.success() {
                return Some(from_utf8(&output.stdout).unwrap().into());
            } else {
                eprintln!("rustfmt failed! {}", from_utf8(&output.stderr).unwrap());
            }
        }
    }
    None
}

pub fn parse_and_format(s: &str) -> Result<String, pest::error::Error<Rule>> {
    let ctx = Context {
        inline_comment_lines: find_inline_comment_lines(s),
    };
    let parsed_file = VerusParser::parse(Rule::file, s)?
        .next()
        .expect("There will be exactly one `file` rule matched in a valid parsed file")
        .into_inner();

    //    info!(file = %args.file.display(), "Parsed");
    //    trace!(parsed = %parsed_file, "Parsed file");

    let mut formatted_output = String::new();

    for pair in parsed_file {
        if enabled!(Level::DEBUG) {
            debug_print(pair.clone(), 0);
        }
        let rule = pair.as_rule();
        debug!(?rule, "Processing top-level");
        match rule {
            Rule::non_verus | Rule::COMMENT => {
                formatted_output += pair.as_str();
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
                for comment in prefix_comments {
                    formatted_output += comment.as_str();
                }
                let items = body.into_inner();
                let len = items.clone().count();
                let mut prev_is_use = false;
                for (i, item) in items.enumerate() {
                    if item.as_rule() == Rule::COMMENT {
                        if prev_is_use {
                            // Add an extra line break, since we don't put line breaks
                            // between use declarations
                            formatted_output += "\n";
                        }
                        prev_is_use = false;
                        formatted_output += item.as_str();
                        if matches!(&item.as_span().as_str()[..2], "/*") {
                            formatted_output += "\n";
                        }
                    } else {
                        let is_use = matches!(
                            item.clone().into_inner().next().unwrap().as_rule(),
                            Rule::r#use
                        );
                        if prev_is_use && !is_use {
                            // Add an extra line break, since we don't put line breaks
                            // between use declarations
                            formatted_output += "\n";
                        }
                        prev_is_use = is_use;

                        formatted_output += &format_item(&ctx, item);
                        formatted_output += "\n";
                        // Add extra space between items, except for use declarations
                        if i < len - 1 && !is_use {
                            formatted_output += "\n";
                        }
                    }
                }
                for comment in suffix_comments {
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
    Ok(fixed_output)
}
