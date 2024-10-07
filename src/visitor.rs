use crate::ParseAndFormatError;
use crate::Rule;
use crate::VerusParser;
use pest::{iterators::Pair, iterators::Pairs, Parser};
use pest_derive::Parser;
use std::collections::HashMap;

pub struct VerusVisitor {
    program: String,
    handlers: HashMap<String, fn(&mut VerusVisitor, Pair<Rule>)>,
    in_clone: bool,
}

impl VerusVisitor {
    pub fn new() -> Self {
        let mut handlers: HashMap<String, for<'a, 'b> fn(&'a mut VerusVisitor, Pair<'b, Rule>)> =
            HashMap::new();
        handlers.insert(
            "verus_macro_use".to_string(),
            VerusVisitor::visit_verus_macro_use,
        );
        handlers.insert("param_list".to_string(), VerusVisitor::visit_param_list);
        handlers.insert(
            "fn_block_expr".to_string(),
            VerusVisitor::visit_fn_block_expr,
        );
        handlers.insert(
            "closure_param_list".to_string(),
            VerusVisitor::visit_closure_param_list,
        );
        handlers.insert(
            "comma_delimited_exprs".to_string(),
            VerusVisitor::visit_comma_delimited_exprs,
        );
        handlers.insert("fn".to_string(), VerusVisitor::visit_fn);
        handlers.insert("arg_list".to_string(), VerusVisitor::visit_arg_list);
        handlers.insert("COMMENT".to_string(), VerusVisitor::visit_comment);
	handlers.insert("identifier".to_string(), VerusVisitor::visit_identifier);
        VerusVisitor {
            program: "".to_string(),
            handlers,
            in_clone: false,
        }
    }

    pub fn visit(&mut self, pair: Pair<Rule>) {
        println!("VISITING {:?} {:?}", pair.as_rule(), pair.as_str());
        let rule_name = format!("{:?}", pair.as_rule());
        if let Some(handler) = self.handlers.get(&rule_name) {
            handler(self, pair);
        } else {
            self.default_visit(pair);
        }
    }

    pub fn default_visit(&mut self, pair: Pair<Rule>) {
        let inner_pairs = pair.clone().into_inner();
        if inner_pairs.clone().count() == 0 {
            self.program += pair.as_str();
            self.program += " ";
        } else {
            self.visit_all(inner_pairs);
        }
    }

    pub fn visit_verus_macro_use(&mut self, pair: Pair<Rule>) {
        self.program += "verus!{\n";
        self.visit_all(pair.into_inner());
        self.program += "}\n";
    }

    pub fn visit_param_list(&mut self, pair: Pair<Rule>) {
        self.program += "(";
        let mut first = true;
        for inner_pair in pair.into_inner() {
            if !first {
                self.program += ", ";
            }
            self.program += inner_pair.as_str();
            first = false;
        }
        self.program += ")";
    }

    pub fn visit_fn(&mut self, pair: Pair<Rule>) {
        let name = pair
            .clone()
            .into_inner()
            .find(|p| p.as_rule() == Rule::name)
            .expect("Function must have a name")
            .as_str();

        if name == "is_prime" {
            self.in_clone = true;
            for fn_comp in pair.clone().into_inner() {
                let rule_name = format!("{:?}", fn_comp.as_rule());
                match rule_name.as_str() {
                    "name" => {
                        let new_name = VerusParser::parse(Rule::name, "is_prime_3")
                            .map_err(ParseAndFormatError::from)
                            .expect("")
                            .next()
                            .unwrap();
                        self.visit(new_name);
                    }
                    "param_list" => {
                        let empty_args = VerusParser::parse(Rule::param_list, "()")
                            .expect("")
                            .next()
                            .unwrap();
                        self.visit(empty_args);
                    }
                    _ => {
                        self.visit(fn_comp);
                    }
                }
            }
            self.in_clone = false;
        }
        self.visit_all(pair.into_inner());
    }

    pub fn visit_fn_block_expr(&mut self, pair: Pair<Rule>) {
        self.program += "\n {";
        self.visit_all(pair.into_inner());
        self.program += "\n } \n";
    }

    pub fn visit_closure_param_list(&mut self, pair: Pair<Rule>) {
        self.program += "|";
        let mut first = true;
        for inner_pair in pair.into_inner() {
            if !first {
                self.program += ", ";
            }
            self.program += inner_pair.as_str();
            first = false;
        }
        self.program += "|";
    }

    pub fn visit_comma_delimited_exprs(&mut self, pair: Pair<Rule>) {
        for inner_pair in pair.into_inner() {
            self.visit(inner_pair);
            self.program += ", ";
        }
    }

    pub fn visit_arg_list(&mut self, pair: Pair<Rule>) {
        self.program += "(";
        self.visit_all(pair.into_inner());
        self.program += ")";
    }

    pub fn visit_all(&mut self, pairs: Pairs<Rule>) {
        for pair in pairs {
            self.visit(pair);
        }
    }

    pub fn visit_comment(&mut self, _pair: Pair<Rule>) {
        //remove
    }

    pub fn after(&self) -> &str {
        &self.program
    }

    pub fn visit_identifier(&mut self, pair: Pair<Rule>) {
        if self.in_clone && pair.as_str() == "candidate" {
            let new_val = VerusParser::parse(Rule::int_number, "3")
                .map_err(ParseAndFormatError::from)
                .expect("")
                .next()
                .unwrap();
	    self.visit(new_val);
        } else {
            self.default_visit(pair);
        }
    }
}
