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

fn soft_indent<'a>(arena:&'a Arena<'a,()>, doc: DocBuilder<'a,Arena<'a>>) -> DocBuilder<'a,Arena<'a>> {
    arena.softline().append(doc).nest(INDENT_SPACES)
}

fn format_doc(doc: RefDoc<()>) -> String {
    let mut w = Vec::new();
    doc.render(NUMBER_OF_COLUMNS, &mut w).unwrap();
    String::from_utf8(w).unwrap()
}

fn item_to_doc<'a>(item: Pair<'a, Rule>, arena:&'a Arena<'a,()>) -> DocBuilder<'a,Arena<'a>> {
    //let item = item.into_inner(); //.next().unwrap();  // Grab the specific case of item
    match item.as_rule() {
        //***********************//
        // General common things //
        //***********************//
        Rule::identifier => unreachable!(),
        Rule::hex_number => unreachable!(),
        Rule::decimal_number => unreachable!(),
        Rule::octal_number => unreachable!(),
        Rule::binary_number => unreachable!(),
        Rule::int_number => unreachable!(),
        Rule::float_number => unreachable!(),
        Rule::lifetime_ident => unreachable!(),
        Rule::string => unreachable!(),
        Rule::raw_string => unreachable!(),
        Rule::raw_string_interior => unreachable!(),
        Rule::byte_string => unreachable!(),
        Rule::raw_byte_string => unreachable!(),
        Rule::r#char => unreachable!(),
        Rule::byte => unreachable!(),

        //***********************************************************//
        // Fixed strings we want to preserve in the formatted output //
        //***********************************************************//
        Rule::semi_str => arena.text(";"),
        Rule::bang_str => arena.text("!"),
        Rule::colons_str => unreachable!(),
        Rule::langle_str => unreachable!(),
        Rule::rangle_str => unreachable!(),
        Rule::eq_str => arena.text("=").append(arena.softline()).nest(INDENT_SPACES),

        Rule::as_str => arena.text("as "),
        Rule::assert_str => arena.text("assert "),
        Rule::assume_str => arena.text("assume "),
        Rule::async_str => arena.text("async "),
        Rule::auto_str => arena.text("auto "),
        Rule::await_str => arena.text("await "),
        Rule::b_str => arena.text("b "),
        Rule::box_str => arena.text("box "),
        Rule::break_str => arena.text("break "),
        Rule::by_str => arena.text("by "),
        Rule::checked_str => arena.text("checked "),
        Rule::choose_str => arena.text("choose "),
        Rule::closed_str => arena.text("closed "),
        Rule::const_str => arena.text("const "),
        Rule::continue_str => arena.text("continue "),
        Rule::crate_str => arena.text("crate "),
        Rule::decreases_str => arena.text("decreases "),
        Rule::default_str => arena.text("default "),
        Rule::do_str => arena.text("do "),
        Rule::dyn_str => arena.text("dyn "),
        Rule::else_str => arena.text("else "),
        Rule::ensures_str => arena.text("ensures "),
        Rule::enum_str => arena.text("enum "),
        Rule::exec_str => arena.text("exec "),
        Rule::exists_str => arena.text("exists "),
        Rule::extern_str => arena.text("extern "),
        Rule::f32_str => arena.text("f32 "),
        Rule::f64_str => arena.text("f64 "),
        Rule::false_str => arena.text("false "),
        Rule::fn_str => arena.text("fn "),
        Rule::for_str => arena.text("for "),
        Rule::forall_str => arena.text("forall "),
        Rule::ghost_str => arena.text("ghost "),
        Rule::i128_str => arena.text("i128 "),
        Rule::i16_str => arena.text("i16 "),
        Rule::i32_str => arena.text("i32 "),
        Rule::i64_str => arena.text("i64 "),
        Rule::i8_str => arena.text("i8 "),
        Rule::if_str => arena.text("if "),
        Rule::impl_str => arena.text("impl "),
        Rule::implies_str => arena.text("implies "),
        Rule::in_str => arena.text("in "),
        Rule::int_str => arena.text("int "),
        Rule::invariant_str => arena.text("invariant "),
        Rule::isize_str => arena.text("isize "),
        Rule::let_str => arena.text("let "),
        Rule::loop_str => arena.text("loop "),
        Rule::macro_str => arena.text("macro "),
        Rule::macro_rules_str => arena.text("macro_rules "),
        Rule::match_str => arena.text("match "),
        Rule::mod_str => arena.text("mod "),
        Rule::move_str => arena.text("move "),
        Rule::mut_str => arena.text("mut "),
        Rule::nat_str => arena.text("nat "),
        Rule::open_str => arena.text("open "),
        Rule::proof_str => arena.text("proof "),
        Rule::pub_str => arena.text("pub "),
        Rule::r_str => arena.text("r "),
        Rule::raw_str => arena.text("raw "),
        Rule::recommends_str => arena.text("recommends "),
        Rule::ref_str => arena.text("ref "),
        Rule::requires_str => arena.text("requires "),
        Rule::return_str => arena.text("return "),
        Rule::self_str => arena.text("self "),
        Rule::spec_str => arena.text("spec "),
        Rule::static_str => arena.text("static "),
        Rule::struct_str => arena.text("struct "),
        Rule::super_str => arena.text("super "),
        Rule::tracked_str => arena.text("tracked "),
        Rule::trait_str => arena.text("trait "),
        Rule::trigger_str => arena.text("trigger "),
        Rule::true_str => arena.text("true "),
        Rule::try_str => arena.text("try "),
        Rule::type_str => arena.text("type "),
        Rule::u128_str => arena.text("u128 "),
        Rule::u16_str => arena.text("u16 "),
        Rule::u32_str => arena.text("u32 "),
        Rule::u64_str => arena.text("u64 "),
        Rule::u8_str => arena.text("u8 "),
        Rule::union_str => arena.text("union "),
        Rule::unsafe_str => arena.text("unsafe "),
        Rule::use_str => arena.text("use "),
        Rule::usize_str => arena.text("usize "),
        Rule::via_str => arena.text("via "),
        Rule::when_str => arena.text("when "),
        Rule::where_str => arena.text("where "),
        Rule::while_str => arena.text("while "),
        Rule::yeet_str => arena.text("yeet "),
        Rule::yield_str => arena.text("yield "),

        //*************************//
        // Names, Paths and Macros //
        //*************************//
        Rule::name => arena.text(item.as_str()),
        Rule::name_ref => unreachable!(),
        Rule::lifetime => unreachable!(),
        Rule::path => unreachable!(),
        Rule::path_segment => unreachable!(),
        Rule::generic_arg_list => unreachable!(),
        Rule::generic_arg => unreachable!(),
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
        Rule::item => arena.concat(item.into_inner().map(|i| item_to_doc(i, arena))),
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
        Rule::r#enum => unreachable!(),
        Rule::variant_list => unreachable!(),
        Rule::variant => unreachable!(),
        Rule::union => unreachable!(),
        Rule::initializer => soft_indent(arena, arena.concat(item.into_inner().map(|i| item_to_doc(i, arena)))),
        Rule::r#const => arena.concat(item.into_inner().map(|i| item_to_doc(i, arena))),
        Rule::r#static => unreachable!(),
        Rule::r#trait => unreachable!(),
        Rule::trait_alias => unreachable!(),
        Rule::assoc_item_list => unreachable!(),
        Rule::assoc_item => unreachable!(),
        Rule::r#impl => unreachable!(),
        Rule::extern_block => unreachable!(),
        Rule::extern_item_list => unreachable!(),
        Rule::extern_item => unreachable!(),
        Rule::generic_param_list => unreachable!(),
        Rule::generic_param => unreachable!(),
        Rule::type_param => unreachable!(),
        Rule::const_param => unreachable!(),
        Rule::lifetime_param => unreachable!(),
        Rule::where_clause => unreachable!(),
        Rule::where_pred => unreachable!(),
        Rule::visibility => arena.text(item.as_str()).append(arena.space()),
        Rule::attr => arena.text(item.as_str()).append(arena.hardline()),
        Rule::meta => unreachable!(),

        //****************************//
        // Statements and Expressions //
        //****************************//
        Rule::stmt => unreachable!(),
        Rule::let_stmt => unreachable!(),
        Rule::let_else => unreachable!(),
        Rule::expr => { error!("TODO: pretty exprs"); arena.text(item.as_str()) },
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
        Rule::r#type => arena.text(":").append(soft_indent(arena, arena.text(item.as_str().trim()))),
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
            error!("TODO: format {:?} before returning", item.as_rule());
            arena.text(item.as_str().to_owned())
        }
    }
}

fn format_item(item: Pair<Rule>) -> String {
    let arena = Arena::<()>::new();
    format_doc(item_to_doc(item, &arena).into_doc())
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
