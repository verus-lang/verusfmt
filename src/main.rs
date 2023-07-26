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

fn soft_comma<'a>(arena:&'a Arena<'a,()>) -> DocBuilder<'a,Arena<'a>> {
    arena.text(",").append(arena.softline()).nest(INDENT_SPACES)
}

fn soft_comma_doc<'a>(arena:&'a Arena<'a,()>, doc: DocBuilder<'a,Arena<'a>>) -> DocBuilder<'a,Arena<'a>> {
    arena.text(",").append(arena.softline()).append(doc).nest(INDENT_SPACES)
}

/// Adds a comma that vanishes in single-line mode
fn conditional_comma<'a>(arena:&'a Arena<'a,()>) -> DocBuilder<'a,Arena<'a>> {
    arena.text(",").flat_alt(arena.nil()) //.group()
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
        Rule::eq_str => arena.text("=").append(arena.softline()).nest(INDENT_SPACES),

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
        Rule::generic_arg_list => unreachable!(),
        Rule::generic_arg => map_to_doc(arena, pair),
        Rule::type_arg => unreachable!(),
        Rule::assoc_type_arg => unreachable!(),
        Rule::lifetime_arg => unreachable!(),
        Rule::const_arg => unreachable!(),
        Rule::macro_call => unreachable!(),
        Rule::token_tree => unreachable!(),
        Rule::macro_items => unreachable!(),
        Rule::macro_stmts => unreachable!(),

        //*************************//
        //          Items          //
        //*************************//
        Rule::item => map_to_doc(arena, pair),
        Rule::macro_rules => unreachable!(),
        Rule::macro_def => unreachable!(),
        Rule::module => unreachable!(),
        Rule::item_list => unreachable!(),
        Rule::extern_crate => unreachable!(),
        Rule::rename => unreachable!(),
        Rule::r#use => unreachable!(),
        Rule::use_tree => unreachable!(),
        Rule::use_tree_list => unreachable!(),
        Rule::r#fn => unreachable!(),
        Rule::abi => unreachable!(),
        Rule::param_list => unreachable!(),
        Rule::self_param => unreachable!(),
        Rule::param => unreachable!(),
        Rule::ret_type => unreachable!(),
        Rule::type_alias => unreachable!(),
        Rule::r#struct => unreachable!(),
        Rule::record_field_list => unreachable!(),
        Rule::record_field => unreachable!(),
        Rule::tuple_field_list => unreachable!(),
        Rule::tuple_field => unreachable!(),
        Rule::field_list => unreachable!(),
        Rule::r#enum => map_to_doc(arena, pair),
        Rule::variant_list => { error!("TODO: pretty variant_list"); s },
        Rule::variant => unreachable!(),
        Rule::union => unreachable!(),
        Rule::initializer => soft_indent(arena, map_to_doc(arena, pair)),
        Rule::r#const => map_to_doc(arena, pair),
        Rule::r#static => unreachable!(),
        Rule::r#trait => unreachable!(),
        Rule::trait_alias => unreachable!(),
        Rule::assoc_item_list => unreachable!(),
        Rule::assoc_item => unreachable!(),
        Rule::r#impl => unreachable!(),
        Rule::extern_block => unreachable!(),
        Rule::extern_item_list => unreachable!(),
        Rule::extern_item => unreachable!(),
        Rule::generic_param_list => {
//            let mut generics = pair.into_inner();
//            let doc = to_doc(generics.next().unwrap(), arena);  // TODO: Handle empty list
//            doc.append(arena.concat(generics.map(|i| soft_comma_doc(arena, to_doc(i, arena))))).group().append(conditional_comma(arena)).angles()
//        },
            //arena.intersperse(pair.into_inner().map(|i| to_doc(i, arena)), soft_comma(arena)).append(conditional_comma(arena)).angles()},
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
                .angles()
                .group() 
        },
        Rule::generic_param => { map_to_doc(arena, pair) }
        Rule::type_param => unreachable!(),
        Rule::const_param => map_to_doc(arena, pair),
        Rule::lifetime_param => unreachable!(),
        Rule::where_clause => unreachable!(),
        Rule::where_pred => unreachable!(),
        Rule::visibility => arena.text(pair.as_str()).append(arena.space()),
        Rule::attr => arena.text(pair.as_str()).append(arena.hardline()),
        Rule::meta => unreachable!(),

        //****************************//
        // Statements and Expressions //
        //****************************//
        Rule::stmt => unreachable!(),
        Rule::let_stmt => unreachable!(),
        Rule::let_else => unreachable!(),
        Rule::expr => { error!("TODO: pretty exprs"); s },
        Rule::expr_inner => unreachable!(),
        Rule::macro_expr => unreachable!(),
        Rule::literal => unreachable!(),
        Rule::path_expr => unreachable!(),
        Rule::stmt_list => unreachable!(),
        Rule::ref_expr => unreachable!(),
        Rule::proof_block => unreachable!(),
        Rule::block_expr => unreachable!(),
        Rule::prefix_expr => unreachable!(),
        Rule::bin_expr_ops => unreachable!(),
        Rule::paren_expr => unreachable!(),
        Rule::array_expr => unreachable!(),
        Rule::tuple_expr => unreachable!(),
        Rule::record_expr => unreachable!(),
        Rule::record_expr_field_list => unreachable!(),
        Rule::record_expr_field => unreachable!(),
        Rule::arg_list => unreachable!(),
        Rule::closure_expr => unreachable!(),
        Rule::if_expr => unreachable!(),
        Rule::loop_expr => unreachable!(),
        Rule::for_expr => unreachable!(),
        Rule::while_expr => unreachable!(),
        Rule::label => unreachable!(),
        Rule::break_expr => unreachable!(),
        Rule::continue_expr => unreachable!(),
        Rule::match_expr => unreachable!(),
        Rule::match_arm_list => unreachable!(),
        Rule::match_arm => unreachable!(),
        Rule::match_guard => unreachable!(),
        Rule::return_expr => unreachable!(),
        Rule::yield_expr => unreachable!(),
        Rule::yeet_expr => unreachable!(),
        Rule::let_expr => unreachable!(),
        Rule::underscore_expr => unreachable!(),
        Rule::box_expr => unreachable!(),

        //*************************//
        //          Types          //
        //*************************//
        Rule::r#type => arena.text(":").append(soft_indent(arena, s)),
        Rule::paren_type => unreachable!(),
        Rule::never_type => unreachable!(),
        Rule::macro_type => unreachable!(),
        Rule::path_type => unreachable!(),
        Rule::tuple_type => unreachable!(),
        Rule::ptr_type => unreachable!(),
        Rule::ref_type => unreachable!(),
        Rule::array_type => unreachable!(),
        Rule::slice_type => unreachable!(),
        Rule::infer_type => unreachable!(),
        Rule::fn_ptr_type => unreachable!(),
        Rule::for_type => unreachable!(),
        Rule::impl_trait_type => unreachable!(),
        Rule::dyn_trait_type => unreachable!(),
        Rule::type_bound_list => unreachable!(),
        Rule::type_bound => unreachable!(),

        //************************//
        //        Patterns        //
        //************************//
        Rule::pat => unreachable!(),
        Rule::pat_inner => unreachable!(),
        Rule::literal_pat => unreachable!(),
        Rule::ident_pat => unreachable!(),
        Rule::wildcard_pat => unreachable!(),
        Rule::end_only_range_pat => unreachable!(),
        Rule::ref_pat => unreachable!(),
        Rule::record_pat => unreachable!(),
        Rule::record_pat_field_list => unreachable!(),
        Rule::record_pat_field => unreachable!(),
        Rule::tuple_struct_pat => unreachable!(),
        Rule::tuple_pat => unreachable!(),
        Rule::paren_pat => unreachable!(),
        Rule::slice_pat => unreachable!(),
        Rule::path_pat => unreachable!(),
        Rule::box_pat => unreachable!(),
        Rule::rest_pat => unreachable!(),
        Rule::macro_pat => unreachable!(),
        Rule::const_block_pat => unreachable!(),

        //************************//
        //        Verus           //
        //************************//
        Rule::publish => unreachable!(),
        Rule::fn_mode => unreachable!(),
        Rule::mode_spec_checked => unreachable!(),
        Rule::data_mode => unreachable!(),
        Rule::comma_delimited_exprs => unreachable!(),
        Rule::comma_delimited_exprs_for_verus_clauses => unreachable!(),
        Rule::verus_clause_non_expr => unreachable!(),
        Rule::requires_clause => unreachable!(),
        Rule::ensures_clause => unreachable!(),
        Rule::invariant_clause => unreachable!(),
        Rule::recommends_clause => unreachable!(),
        Rule::decreases_clause => unreachable!(),
        Rule::assert_expr => unreachable!(),
        Rule::assume_expr => unreachable!(),
        Rule::assert_forall_expr => unreachable!(),
        Rule::prover => unreachable!(),
        Rule::trigger_attribute => unreachable!(),

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
