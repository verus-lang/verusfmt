#![allow(dead_code, unused_imports)] // TEMPORARY

use std::path::PathBuf;

use anyhow::anyhow;
use clap::Parser as ClapParser;
use fs_err as fs;
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use tracing::{debug, error, info, trace};
use pretty::*;

#[derive(Parser)]
#[grammar = "verus.pest"]
pub struct VerusParser;

/// An opinionated formatter for Verus code
///
/// Formats code that is inside the `verus!{}` macro. Best utilized in conjunction with rustfmt
/// which will format everything outside the verus macro.
#[derive(ClapParser)]
#[command(version, about)]
struct Args {
    /// Run in 'check' mode. Exits with 0 only if the file is formatted correctly.
    #[arg(long = "check")]
    check: bool,
    /// Input file to be formatted
    file: PathBuf,
    /// Print debugging output (can be repeated for more detail)
    #[arg(short = 'd', long = "debug", action = clap::ArgAction::Count)]
    debug_level: u8,
}

// XXX: Should we expose this to the user as a configurable option where we pick a default? I think
// even this should be opinionated, but might be useful to expose this as an unstable option or
// something.
const NUMBER_OF_COLUMNS: usize = 120;
const INDENT_SPACES: isize = 4;

// When in doubt, we should generally try to stick to Rust style guidelines:
//   https://doc.rust-lang.org/beta/style-guide/expressions.html

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
    error!("Unsupported rule {:?} starting at line {}, col {}: {}", pair.as_rule(), line, col, pair.as_str());
    todo!()
}

// TODO: We'll want special handling for comma-delimited lists; Rust will include a terminal comma 
//       when spilling to multiple lines and otherwise omit it


fn to_doc<'a>(pair: Pair<'a, Rule>, arena:&'a Arena<'a,()>) -> DocBuilder<'a,Arena<'a>> {
    let s = arena.text(pair.as_str().trim());
    // TODO: Apply naming policy: https://doc.rust-lang.org/beta/style-guide/advice.html#names
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
        Rule::semi_str |
        Rule::bang_str |
        Rule::colons_str |
        Rule::langle_str |
        Rule::rangle_str 
            => s,
        Rule::colon_str | 
        Rule::eq_str => s.append(arena.softline()).nest(INDENT_SPACES),

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
        Rule::r#fn => unsupported(pair),
        Rule::abi => unsupported(pair),
        Rule::param_list => unsupported(pair),
        Rule::self_param => unsupported(pair),
        Rule::param => unsupported(pair),
        Rule::ret_type => unsupported(pair),
        Rule::type_alias => unsupported(pair),
        Rule::r#struct => unsupported(pair),
        Rule::record_field_list => comma_delimited(arena, pair).braces().group(),
        Rule::record_field => map_to_doc(arena, pair),
        Rule::tuple_field_list => comma_delimited(arena, pair).parens().group(),
        Rule::tuple_field => map_to_doc(arena, pair),
        Rule::field_list => map_to_doc(arena, pair),
        Rule::r#enum => map_to_doc(arena, pair),
        Rule::variant_list => arena.space().append(comma_delimited(arena, pair).braces()),
        Rule::variant => map_to_doc(arena, pair),
        Rule::union => unsupported(pair),
        Rule::initializer => soft_indent(arena, map_to_doc(arena, pair)),
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
        Rule::visibility => arena.text(pair.as_str()).append(arena.space()),
        Rule::attr => arena.text(pair.as_str()).append(arena.hardline()),
        Rule::meta => unsupported(pair),

        //****************************//
        // Statements and Expressions //
        //****************************//
        Rule::stmt => unsupported(pair),
        Rule::let_stmt => unsupported(pair),
        Rule::let_else => unsupported(pair),
        Rule::expr => { error!("TODO: pretty exprs"); s },
        Rule::expr_inner => unsupported(pair),
        Rule::macro_expr => unsupported(pair),
        Rule::literal => unsupported(pair),
        Rule::path_expr => unsupported(pair),
        Rule::stmt_list => unsupported(pair),
        Rule::ref_expr => unsupported(pair),
        Rule::proof_block => unsupported(pair),
        Rule::block_expr => unsupported(pair),
        Rule::prefix_expr => unsupported(pair),
        Rule::bin_expr_ops => unsupported(pair),
        Rule::paren_expr => unsupported(pair),
        Rule::array_expr => unsupported(pair),
        Rule::tuple_expr => unsupported(pair),
        Rule::record_expr => unsupported(pair),
        Rule::record_expr_field_list => unsupported(pair),
        Rule::record_expr_field => unsupported(pair),
        Rule::arg_list => unsupported(pair),
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
        Rule::pat => unsupported(pair),
        Rule::pat_inner => unsupported(pair),
        Rule::literal_pat => unsupported(pair),
        Rule::ident_pat => unsupported(pair),
        Rule::wildcard_pat => unsupported(pair),
        Rule::end_only_range_pat => unsupported(pair),
        Rule::ref_pat => unsupported(pair),
        Rule::record_pat => unsupported(pair),
        Rule::record_pat_field_list => unsupported(pair),
        Rule::record_pat_field => unsupported(pair),
        Rule::tuple_struct_pat => unsupported(pair),
        Rule::tuple_pat => unsupported(pair),
        Rule::paren_pat => unsupported(pair),
        Rule::slice_pat => unsupported(pair),
        Rule::path_pat => unsupported(pair),
        Rule::box_pat => unsupported(pair),
        Rule::rest_pat => unsupported(pair),
        Rule::macro_pat => unsupported(pair),
        Rule::const_block_pat => unsupported(pair),

        //************************//
        //        Verus           //
        //************************//
        Rule::publish => unsupported(pair),
        Rule::fn_mode => unsupported(pair),
        Rule::mode_spec_checked => unsupported(pair),
        Rule::data_mode => unsupported(pair),
        Rule::comma_delimited_exprs => unsupported(pair),
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

        _ => {
            error!("TODO: format {:?} before returning", pair.as_rule());
            arena.text(pair.as_str().to_owned())
        }
    }
}

fn format_item(item: Pair<Rule>) -> String {
    let arena = Arena::<()>::new();
    format_doc(to_doc(item, &arena).into_doc())
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    tracing_subscriber::fmt()
        .with_timer(tracing_subscriber::fmt::time::uptime())
        .with_level(true)
        .with_target(false)
        .with_max_level(match args.debug_level {
            0 => tracing::Level::WARN,
            1 => tracing::Level::INFO,
            2 => tracing::Level::DEBUG,
            _ => tracing::Level::TRACE,
        })
        .init();

    let unparsed_file = fs::read_to_string(&args.file)?;
    let parsed_file = VerusParser::parse(Rule::file, &unparsed_file)?
        .next()
        .expect("There will be exactly one `file` rule matched in a valid parsed file")
        .into_inner();

    info!(file = %args.file.display(), "Parsed");
    trace!(parsed = %parsed_file, "Parsed file");

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
                formatted_output += "verus! {\n\n";
                for item in body.into_inner() {
                    if item.as_rule() == Rule::COMMENT {
                        formatted_output += item.as_str();
                    } else {
                        formatted_output += &format_item(item);
                        formatted_output += "\n\n";
                    }
                }
                formatted_output += "} // verus!\n";
            }
            Rule::EOI => {
                // end of input; do nothing
            }
            _ => unreachable!("Unexpected rule: {:?}", rule),
        }
    }

    if args.check {
        if unparsed_file == formatted_output {
            info!("✨Perfectly formatted✨");
            return Ok(());
        } else {
            info!("Found some differences");
            error!("Input found not to be well formatted");
            let diff = similar::udiff::unified_diff(
                similar::Algorithm::Patience,
                &unparsed_file,
                &formatted_output,
                3,
                Some(("original", "formatted")),
            );
            println!("{diff}");
            return Err(anyhow!("invalid formatting"));
        }
    } else {
        fs::write(args.file, formatted_output)?;
        Ok(())
    }
}
