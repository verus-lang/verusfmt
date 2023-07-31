#![allow(dead_code, unused_imports)] // TEMPORARY
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use pretty::*;
use tracing::{debug, error, info, trace};

#[derive(Parser)]
#[grammar = "verus.pest"]
pub struct VerusParser;

// XXX: Should we expose these to the user as a configurable option where we pick a default? I think
// even this should be opinionated, but might be useful to expose this as an unstable option or
// something.
// rustfmt sets this to 100: https://rust-lang.github.io/rustfmt/?version=v1.6.0&search=#max_width
const NUMBER_OF_COLUMNS: usize = 100;
const INDENT_SPACES: isize = 4;

// When in doubt, we should generally try to stick to Rust style guidelines:
//   https://doc.rust-lang.org/beta/style-guide/items.html

/// Adds a space that turns into a newline plus indentation when in multi-line mode
fn soft_indent<'a>(arena:&'a Arena<'a,()>, doc: DocBuilder<'a,Arena<'a>>) -> DocBuilder<'a,Arena<'a>> {
    arena.softline().append(doc).nest(INDENT_SPACES)
}

/// Adds a comma that vanishes in single-line mode
fn conditional_comma<'a>(arena:&'a Arena<'a,()>) -> DocBuilder<'a,Arena<'a>> {
    arena.text(",").flat_alt(arena.nil()) //.group()
}

/// Comma-delimited list with an optional final comma
fn comma_delimited<'a>(arena:&'a Arena<'a,()>, pair: Pair<'a, Rule>) -> DocBuilder<'a,Arena<'a>> {
    arena.line_()
        .append(arena.intersperse(
                    pair.into_inner().map(|i| to_doc(i, arena)), 
                    docs![arena, 
                          ",", 
                          arena.line()
                    ]
                    )
        )
        .append(conditional_comma(arena))
        .nest(INDENT_SPACES)
        .append(arena.line_())
}

/// Parens around a comma-delimited list with an optional final comma,
/// where the opening paren tries to "stick" to the previous line if needed
fn sticky_paren_list<'a>(arena:&'a Arena<'a,()>, pair: Pair<'a, Rule>) -> DocBuilder<'a,Arena<'a>> {
    docs![
        arena,
        arena.text("("),
        arena.line_(),
    ].group()
    .append(map_to_doc(arena, pair)).group()
    .append(arena.text(")"))
}

fn spaced_braces<'a>(arena:&'a Arena<'a,()>, doc: DocBuilder<'a,Arena<'a>>) -> DocBuilder<'a,Arena<'a>> {
    arena.space().append(
        docs![
            arena,
            arena.nil().flat_alt(arena.space()),
            doc,
            arena.nil().flat_alt(arena.space()),
        ].braces()
    )
}

fn block_braces<'a>(arena:&'a Arena<'a,()>, doc: DocBuilder<'a,Arena<'a>>) -> DocBuilder<'a,Arena<'a>> {
    arena.space().append(
        docs![
            arena,
            arena.line().append(doc).nest(INDENT_SPACES),
            arena.line(),
        ].braces()
    )
}

/// Produce a document that simply combines the result of calling `to_doc` on each child
fn map_to_doc<'a>(arena:&'a Arena<'a,()>, pair: Pair<'a, Rule>) -> DocBuilder<'a,Arena<'a>> {
    arena.concat(pair.into_inner().map(|i| to_doc(i, arena)))
}

fn format_doc(doc: RefDoc<()>) -> String {
    let mut w = Vec::new();
    doc.render(NUMBER_OF_COLUMNS, &mut w).unwrap();
    String::from_utf8(w).unwrap()
}

/// Provide some details for parsing rules we don't (yet) support
fn unsupported(pair: Pair<Rule>) -> DocBuilder<Arena> {
    let (line, col) = pair.line_col();
    error!("Unsupported parsing object '{:?}', starting at line {}, col {}: {}", pair.as_rule(), line, col, pair.as_str());
    todo!()
}

// TODO: Be sure that comments are being handled properly.  `//` comments should start with a space

fn to_doc<'a>(pair: Pair<'a, Rule>, arena:&'a Arena<'a,()>) -> DocBuilder<'a,Arena<'a>> {
    let s = arena.text(pair.as_str().trim());
    // TODO: Apply naming policy: https://doc.rust-lang.org/beta/style-guide/advice.html#names
    debug!("Processing rule {:?}", pair.as_rule());
    match pair.as_rule() {
        //***********************//
        // General common things //
        //***********************//
        Rule::identifier |
        Rule::hex_number |
        Rule::decimal_number |
        Rule::octal_number |
        Rule::binary_number |
        Rule::int_number |
        Rule::float_number |
        Rule::lifetime_ident |
        Rule::string |
        Rule::raw_string |
        Rule::raw_string_interior |
        Rule::byte_string |
        Rule::raw_byte_string |
        Rule::r#char |
        Rule::byte
            => s,

        //***********************************************************//
        // Fixed strings we want to preserve in the formatted output //
        //***********************************************************//
        Rule::at_str |
        Rule::bang_str |
        Rule::colons_str |
        Rule::dash_str |
        Rule::dot_str |
        Rule::dot_dot_str |
        Rule::dot_dot_eq_str |
        Rule::ellipses_str |
        Rule::langle_str |
        Rule::lbracket_str |
        Rule::lparen_str |
        Rule::pipe_str |
        Rule::question_str |
        Rule::rangle_str |
        Rule::rbracket_str |
        Rule::rparen_str |
        Rule::semi_str
            => s,
        Rule::rarrow_str => docs![arena, arena.space(), s, arena.space()],
        Rule::colon_str => 
            docs![
                arena,
                s,
                arena.line_(),
                arena.space()
            ].nest(INDENT_SPACES-1).group(), 
        Rule::eq_str => 
            docs![
                arena,
                arena.space(),
                s,
                arena.line_(),
                arena.space()
            ].nest(INDENT_SPACES-1).group(), 
        Rule::as_str |
        Rule::assert_str |
        Rule::assume_str |
        Rule::async_str |
        Rule::auto_str |
        Rule::await_str |
        Rule::box_str |
        Rule::break_str |
        Rule::by_str |
        Rule::checked_str |
        Rule::choose_str |
        Rule::closed_str |
        Rule::const_str |
        Rule::continue_str |
        Rule::crate_str |
        Rule::decreases_str |
        Rule::default_str |
        Rule::do_str |
        Rule::dyn_str |
        Rule::else_str |
        Rule::ensures_str |
        Rule::enum_str |
        Rule::exec_str |
        Rule::exists_str |
        Rule::extern_str |
        Rule::f32_str |
        Rule::f64_str |
        Rule::false_str |
        Rule::fn_str |
        Rule::for_str |
        Rule::forall_str |
        Rule::ghost_str |
        Rule::i128_str |
        Rule::i16_str |
        Rule::i32_str |
        Rule::i64_str |
        Rule::i8_str |
        Rule::if_str |
        Rule::impl_str |
        Rule::implies_str |
        Rule::in_str |
        Rule::int_str |
        Rule::invariant_str |
        Rule::isize_str |
        Rule::let_str |
        Rule::loop_str |
        Rule::macro_str |
        Rule::macro_rules_str |
        Rule::match_str |
        Rule::mod_str |
        Rule::move_str |
        Rule::mut_str |
        Rule::nat_str |
        Rule::open_str |
        Rule::proof_str |
        Rule::pub_str |
        Rule::r_str |
        Rule::raw_str |
        Rule::recommends_str |
        Rule::ref_str |
        Rule::requires_str |
        Rule::return_str |
        Rule::self_str |
        Rule::Self_str |
        Rule::spec_str |
        Rule::static_str |
        Rule::struct_str |
        Rule::super_str |
        Rule::tracked_str |
        Rule::trait_str |
        Rule::trigger_str |
        Rule::true_str |
        Rule::try_str |
        Rule::type_str |
        Rule::u128_str |
        Rule::u16_str |
        Rule::u32_str |
        Rule::u64_str |
        Rule::u8_str |
        Rule::union_str |
        Rule::unsafe_str |
        Rule::use_str |
        Rule::usize_str |
        Rule::via_str |
        Rule::when_str |
        Rule::where_str |
        Rule::while_str |
        Rule::yeet_str |
        Rule::yield_str 
            => s.append(arena.space()),

        //*************************//
        // Names, Paths and Macros //
        //*************************//
        Rule::name |
        Rule::name_ref |
        Rule::lifetime
            => s,
        Rule::path => map_to_doc(arena, pair),
        Rule::path_segment => map_to_doc(arena, pair),
        Rule::generic_arg_list => unsupported(pair),
        Rule::generic_arg => map_to_doc(arena, pair),
        Rule::type_arg => unsupported(pair),
        Rule::assoc_type_arg => unsupported(pair),
        Rule::lifetime_arg => unsupported(pair),
        Rule::const_arg => unsupported(pair),
        Rule::macro_call => unsupported(pair),
        Rule::token_tree => unsupported(pair),
        Rule::macro_items => unsupported(pair),
        Rule::macro_stmts => unsupported(pair),

        //*************************//
        //          Items          //
        //*************************//
        Rule::item => map_to_doc(arena, pair),
        Rule::macro_rules => unsupported(pair),
        Rule::macro_def => unsupported(pair),
        Rule::module => unsupported(pair),
        Rule::item_list => unsupported(pair),
        Rule::extern_crate => unsupported(pair),
        Rule::rename => unsupported(pair),
        Rule::r#use => unsupported(pair),
        Rule::use_tree => unsupported(pair),
        Rule::use_tree_list => unsupported(pair),
        Rule::r#fn => map_to_doc(arena, pair),
        Rule::abi => unsupported(pair),
        Rule::param_list => { 
            if pair.as_str().starts_with('(') {
                comma_delimited(arena, pair).parens().group()
            } else { 
                comma_delimited(arena, pair).enclose(arena.text("|"), arena.text("|")).group()
            }
        }
        Rule::self_param => unsupported(pair),
        Rule::param => map_to_doc(arena, pair),
        Rule::ret_type => map_to_doc(arena, pair),
        Rule::type_alias => unsupported(pair),
        Rule::r#struct => map_to_doc(arena, pair),
        Rule::record_field_list => spaced_braces(arena, comma_delimited(arena, pair)),
        Rule::condensable_record_field_list => spaced_braces(arena, comma_delimited(arena, pair)).group(),
        Rule::record_field => map_to_doc(arena, pair),
        Rule::tuple_field_list => comma_delimited(arena, pair).parens().group(),
        Rule::tuple_field => map_to_doc(arena, pair),
        Rule::field_list => map_to_doc(arena, pair),
        Rule::r#enum => map_to_doc(arena, pair),
        Rule::variant_list => arena.space().append(comma_delimited(arena, pair).braces()),
        Rule::variant => map_to_doc(arena, pair),
        Rule::union => unsupported(pair),
        //Rule::initializer => soft_indent(arena, map_to_doc(arena, pair)),
        Rule::r#const => map_to_doc(arena, pair),
        Rule::r#static => unsupported(pair),
        Rule::r#trait => unsupported(pair),
        Rule::trait_alias => unsupported(pair),
        Rule::assoc_item_list => unsupported(pair),
        Rule::assoc_item => unsupported(pair),
        Rule::r#impl => unsupported(pair),
        Rule::extern_block => unsupported(pair),
        Rule::extern_item_list => unsupported(pair),
        Rule::extern_item => unsupported(pair),
        Rule::generic_param_list => comma_delimited(arena, pair).angles().group(),
        Rule::generic_param => map_to_doc(arena, pair),
        Rule::type_param => map_to_doc(arena, pair),
        Rule::const_param => unsupported(pair),
        Rule::lifetime_param => unsupported(pair),
        Rule::where_clause => unsupported(pair),
        Rule::where_pred => unsupported(pair),
        Rule::visibility => s.append(arena.space()),
        Rule::attr => arena.text(pair.as_str()).append(arena.hardline()),
        Rule::meta => unsupported(pair),

        //****************************//
        // Statements and Expressions //
        //****************************//
        Rule::stmt => map_to_doc(arena, pair).append(arena.line()),
        // TODO: The code for let_stmt does not explicitly attempt to replicate the (complex) rules described here:
        //       https://doc.rust-lang.org/beta/style-guide/statements.html#let-statements
        Rule::let_stmt => map_to_doc(arena, pair).group(),
        Rule::let_else => unsupported(pair),
        Rule::expr => map_to_doc(arena, pair),
        Rule::expr_inner => map_to_doc(arena, pair),
        Rule::macro_expr => unsupported(pair),
        Rule::literal => map_to_doc(arena, pair),
        Rule::path_expr => map_to_doc(arena, pair),
        Rule::stmt_list => block_braces(arena, map_to_doc(arena, pair)),
        Rule::ref_expr => unsupported(pair),
        Rule::proof_block => unsupported(pair),
        Rule::block_expr => map_to_doc(arena, pair),
        Rule::prefix_expr => unsupported(pair),
        Rule::bin_expr_ops => unsupported(pair),
        Rule::paren_expr => unsupported(pair),
        Rule::array_expr => unsupported(pair),
        Rule::tuple_expr_inner => sticky_paren_list(arena, pair),
        Rule::tuple_expr => map_to_doc(arena, pair),
        Rule::record_expr => unsupported(pair),
        Rule::record_expr_field_list => unsupported(pair),
        Rule::record_expr_field => unsupported(pair),
        Rule::arg_list => sticky_paren_list(arena, pair),
        Rule::closure_expr => unsupported(pair),
        Rule::if_expr => unsupported(pair),
        Rule::loop_expr => unsupported(pair),
        Rule::for_expr => unsupported(pair),
        Rule::while_expr => unsupported(pair),
        Rule::label => unsupported(pair),
        Rule::break_expr => unsupported(pair),
        Rule::continue_expr => unsupported(pair),
        Rule::match_expr => unsupported(pair),
        Rule::match_arm_list => unsupported(pair),
        Rule::match_arm => unsupported(pair),
        Rule::match_guard => unsupported(pair),
        Rule::return_expr => unsupported(pair),
        Rule::yield_expr => unsupported(pair),
        Rule::yeet_expr => unsupported(pair),
        Rule::let_expr => unsupported(pair),
        Rule::underscore_expr => unsupported(pair),
        Rule::box_expr => unsupported(pair),

        //*************************//
        //          Types          //
        //*************************//
        Rule::r#type => s,
        Rule::paren_type => unsupported(pair),
        Rule::never_type => unsupported(pair),
        Rule::macro_type => unsupported(pair),
        Rule::path_type => unsupported(pair),
        Rule::tuple_type => unsupported(pair),
        Rule::ptr_type => unsupported(pair),
        Rule::ref_type => unsupported(pair),
        Rule::array_type => unsupported(pair),
        Rule::slice_type => unsupported(pair),
        Rule::infer_type => unsupported(pair),
        Rule::fn_ptr_type => unsupported(pair),
        Rule::for_type => unsupported(pair),
        Rule::impl_trait_type => unsupported(pair),
        Rule::dyn_trait_type => unsupported(pair),
        Rule::type_bound_list => unsupported(pair),
        Rule::type_bound => unsupported(pair),

        //************************//
        //        Patterns        //
        //************************//
        Rule::pat => map_to_doc(arena, pair),
        Rule::pat_inner => map_to_doc(arena, pair),
        Rule::literal_pat => map_to_doc(arena, pair),
        Rule::ident_pat => map_to_doc(arena, pair),
        Rule::wildcard_pat => arena.text("_"),
        Rule::end_only_range_pat => map_to_doc(arena, pair),
        Rule::ref_pat => arena.text("&").append(map_to_doc(arena, pair)),
        Rule::record_pat => map_to_doc(arena, pair),
        Rule::record_pat_field_list => comma_delimited(arena, pair).braces().group(),   // TODO: Handle vanishing comma's interaction with rest_pat
        Rule::record_pat_field => map_to_doc(arena, pair),
        Rule::tuple_struct_pat_inner => comma_delimited(arena, pair).parens().group(),
        Rule::tuple_struct_pat => map_to_doc(arena, pair), 
        Rule::tuple_pat => comma_delimited(arena, pair).parens().group(),
        Rule::paren_pat => map_to_doc(arena, pair).parens(),
        Rule::slice_pat => comma_delimited(arena, pair).brackets().group(),
        Rule::path_pat => map_to_doc(arena, pair),
        Rule::box_pat => map_to_doc(arena, pair),
        Rule::rest_pat => map_to_doc(arena, pair),  // TODO: Should the attributes on this be on
                                                    // the same line?
        Rule::macro_pat => unsupported(pair),
        Rule::const_block_pat => unsupported(pair),

        //************************//
        //        Verus           //
        //************************//
        Rule::publish => unsupported(pair),
        Rule::fn_mode => unsupported(pair),
        Rule::mode_spec_checked => unsupported(pair),
        Rule::data_mode => unsupported(pair),
        Rule::comma_delimited_exprs => comma_delimited(arena, pair).group(),
        Rule::comma_delimited_exprs_for_verus_clauses => unsupported(pair),
        Rule::verus_clause_non_expr => unsupported(pair),
        Rule::requires_clause => unsupported(pair),
        Rule::ensures_clause => unsupported(pair),
        Rule::invariant_clause => unsupported(pair),
        Rule::recommends_clause => unsupported(pair),
        Rule::decreases_clause => unsupported(pair),
        Rule::assert_expr => unsupported(pair),
        Rule::assume_expr => unsupported(pair),
        Rule::assert_forall_expr => unsupported(pair),
        Rule::prover => unsupported(pair),
        Rule::trigger_attribute => unsupported(pair),

        Rule::WHITESPACE => arena.nil(),
        Rule::COMMENT => s,
        Rule::multiline_comment => s,
        Rule::file | Rule::non_verus | Rule::verus_macro_use | Rule::verus_macro_body | Rule::EOI => unreachable!(),

//        _ => {
//            error!("TODO: format {:?} before returning", pair.as_rule());
//            arena.text(pair.as_str().to_owned())
//        }
    }
}

fn format_item(item: Pair<Rule>) -> String {
    let arena = Arena::<()>::new();
    let doc = to_doc(item, &arena).into_doc();
    debug!("{:?}", doc);
    format_doc(doc)
}

pub const VERUS_PREFIX: &str = "verus! {\n\n";
pub const VERUS_SUFFIX: &str = "\n} // verus!\n";

pub fn parse_and_format(s: &str) -> Result<String, pest::error::Error<Rule>> {
    let parsed_file = VerusParser::parse(Rule::file, s)?
        .next()
        .expect("There will be exactly one `file` rule matched in a valid parsed file")
        .into_inner();

//    info!(file = %args.file.display(), "Parsed");
//    trace!(parsed = %parsed_file, "Parsed file");

    let mut formatted_output = String::new();

    for pair in parsed_file {
        let rule = pair.as_rule();
        debug!(?rule, "Processing top-level");
        match rule {
            Rule::non_verus | Rule::COMMENT => {
                formatted_output += pair.as_str();
            }
            Rule::verus_macro_use => {
                let body = pair.into_inner().collect::<Vec<_>>();
                assert_eq!(body.len(), 1);
                let body = body.into_iter().next().unwrap();
                formatted_output += VERUS_PREFIX;
                for item in body.into_inner() {
                    if item.as_rule() == Rule::COMMENT {
                        formatted_output += item.as_str();
                    } else {
                        formatted_output += &format_item(item);
                        formatted_output += "\n";
                    }
                }
                formatted_output += VERUS_SUFFIX;
            }
            Rule::EOI => {
                // end of input; do nothing
            }
            _ => unreachable!("Unexpected rule: {:?}", rule),
        }
    }
    Ok(formatted_output)
}


