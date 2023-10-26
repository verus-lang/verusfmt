// Extracted verus code from file tests/success/encrypted_key_struct.owl:
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_variables)]

pub use vstd::{modes::*, prelude::*, seq::*, slice::*, string::*, *};
pub mod speclib;
pub use crate::speclib::{*, itree::*};
pub mod execlib;
pub use crate::execlib::{*};
pub mod owl_aead;
pub mod owl_dhke;
pub mod owl_hkdf;
pub mod owl_hmac;
pub mod owl_pke;
pub mod owl_util;

pub use extraction_lib::*;
pub use std::collections::HashMap;
pub use std::env;
pub use std::fs;
pub use std::io::{self, BufRead, Write};
pub use std::net::{SocketAddr, TcpListener, TcpStream, ToSocketAddrs};
pub use std::rc::Rc;
pub use std::str;
pub use std::thread;
pub use std::time::Duration;
pub use std::time::Instant;

verus! {
pub open const spec fn CIPHER() -> owl_aead::Mode { crate::owl_aead::Mode::Chacha20Poly1305 }
pub const fn cipher() -> (r:owl_aead::Mode) ensures r == CIPHER() { crate::owl_aead::Mode::Chacha20Poly1305 }
pub open const spec fn KEY_SIZE() -> usize { owl_aead::spec_key_size(CIPHER()) }
pub const fn key_size() -> (r:usize) ensures r == KEY_SIZE() { owl_aead::key_size(cipher()) }
pub open const spec fn TAG_SIZE() -> usize { owl_aead::spec_tag_size(CIPHER()) }
pub const fn tag_size() -> (r:usize) ensures r == TAG_SIZE() { owl_aead::tag_size(cipher()) }
pub open const spec fn NONCE_SIZE() -> usize { owl_aead::spec_nonce_size(CIPHER()) }
pub const fn nonce_size() -> (r:usize) ensures r == NONCE_SIZE() { owl_aead::nonce_size(cipher()) }
pub open const spec fn HMAC_MODE() -> owl_hmac::Mode { crate::owl_hmac::Mode::Sha512 }
pub const fn hmac_mode() -> (r:owl_hmac::Mode) ensures r == HMAC_MODE() { crate::owl_hmac::Mode::Sha512 }

#[verifier(external_type_specification)]
#[verifier(external_body)]
pub struct TcpListenerWrapper ( std::net::TcpListener );

#[verifier(external_type_specification)]
pub struct OwlErrorWrapper ( OwlError );


#[verifier(external_body)]
pub fn owl_output<A>(Tracked(t): Tracked<&mut ITreeToken<A,Endpoint>>, x: &[u8], dest_addr: &StrSlice, ret_addr: &StrSlice)
    requires old(t)@.is_output(x@, endpoint_of_addr(dest_addr.view()))
    ensures  t@ == old(t)@.give_output()
{
    let msg = msg { ret_addr: std::string::String::from(ret_addr.into_rust_str()), payload: std::vec::Vec::from(x) };
    let serialized = serialize_msg(&msg);
    let mut stream = TcpStream::connect(dest_addr.into_rust_str()).unwrap();
    stream.write_all(&serialized).unwrap();
    stream.flush().unwrap();
}

#[verifier(external_body)]
pub fn owl_input<A>(Tracked(t): Tracked<&mut ITreeToken<A,Endpoint>>, listener: &TcpListener) -> (ie:(Vec<u8>, String))
    requires old(t)@.is_input()
    ensures  t@ == old(t)@.take_input(ie.0@, endpoint_of_addr(ie.1.view()))
{
    let (mut stream, _addr) = listener.accept().unwrap();
    let mut reader = io::BufReader::new(&mut stream);
    let received: std::vec::Vec<u8> = reader.fill_buf().unwrap().to_vec();
    reader.consume(received.len());
    let msg : msg = deserialize_msg(&received);
    (msg.payload, String::from_rust_string(msg.ret_addr))
}

#[verifier(external_body)]
pub fn owl_sample<A>(Tracked(t): Tracked<&mut ITreeToken<A,Endpoint>>, n: usize) -> (res:Vec<u8>)
    requires old(t)@.is_sample(n)
    ensures  t@ == old(t)@.get_sample(res@)
{
    owl_util::gen_rand_bytes(n)
}

} // verus!




verus! {

// ------------------------------------
// ---------- SPECIFICATIONS ----------
// ------------------------------------

pub struct owlSpec_t{
pub owlSpec__x : Seq<u8>,
pub owlSpec__y : Seq<u8>
}
#[verifier(external_body)] pub closed spec fn parse_owlSpec_t(x: Seq<u8>) -> Option<owlSpec_t> {
todo!()
}
#[verifier(external_body)] pub closed spec fn serialize_owlSpec_t(x: owlSpec_t) -> Seq<u8> {
todo!()
}
pub open spec fn t(arg__x: Seq<u8>, arg__y: Seq<u8>) -> Seq<u8> {
serialize_owlSpec_t(owlSpec_t{owlSpec__x: arg__x, owlSpec__y: arg__y})
}
pub open spec fn _x(arg: Seq<u8>) -> Seq<u8> {
match parse_owlSpec_t(arg) {
Some(parsed) => parsed.owlSpec__x,
None => seq![] // TODO
}
}
pub open spec fn _y(arg: Seq<u8>) -> Seq<u8> {
match parse_owlSpec_t(arg) {
Some(parsed) => parsed.owlSpec__y,
None => seq![] // TODO
}
}

#[is_variant]
pub enum owlSpec_Result{
owlSpec_SomeResult(Seq<u8>),
owlSpec_NoResult()
}
use crate::owlSpec_Result::*;

#[verifier(external_body)] pub closed spec fn parse_owlSpec_Result(x: Seq<u8>) -> Option<owlSpec_Result> {
todo!()
}
#[verifier(external_body)] pub closed spec fn serialize_owlSpec_Result(x: owlSpec_Result) -> Seq<u8> {
todo!()
}
pub open spec fn SomeResult(x: Seq<u8>) -> Seq<u8> {
serialize_owlSpec_Result(crate::owlSpec_Result::owlSpec_SomeResult(x))
}
pub open spec fn NoResult() -> Seq<u8> {
serialize_owlSpec_Result(crate::owlSpec_Result::owlSpec_NoResult())
}



#[is_variant]
#[derive(Copy, Clone)]
pub enum Endpoint {
Loc_alice,
Loc_bob
}
#[verifier(external_body)] pub closed spec fn endpoint_of_addr(addr: Seq<char>) -> Endpoint { unimplemented!() /* axiomatized */ }

pub open spec fn alice_main_spec(cfg: cfg_alice, mut_state: state_alice) -> (res: ITree<(Seq<u8>, state_alice), Endpoint>) {
owl_spec!(mut_state,state_alice,
let c = ((sample( NONCE_SIZE()
, enc((*cfg.owl_shared_key).view(), (*cfg.owl_k_data).view()) ))) in
(output (c) to (Endpoint::Loc_bob)) in
(input (i, _)) in
let result = (let caseval = ((ret(dec((*cfg.owl_k_data).view(), i)))) in
(case (caseval)
{Some (j) => {(parse (parse_owlSpec_t(j)) as (owlSpec_t{owlSpec__x : x, owlSpec__y : y}) otherwise ((ret (NoResult(  )))) in
(ret (SomeResult(y))))},
None => {(ret (NoResult()))},})) in
(ret (result))
)
}

pub open spec fn bob_main_spec(cfg: cfg_bob, mut_state: state_bob) -> (res: ITree<((), state_bob), Endpoint>) {
owl_spec!(mut_state,state_bob,
(input (i, ev)) in
let caseval = ((ret(dec((*cfg.owl_shared_key).view(), i)))) in
(case (caseval)
{Some (k) => {let foo = ((ret (t((*cfg.owl_x).view(), (*cfg.owl_y).view())))) in
let c = ((sample(NONCE_SIZE(), enc(k, foo)))) in
(output (c) to (ev))},
None => {(ret (()))},})
)
}



// ------------------------------------
// ---------- IMPLEMENTATIONS ---------
// ------------------------------------

/* TODO this will be generated by parsley */
pub struct owl_t {
pub owl__x : Vec<u8>,
pub owl__y : Vec<u8>
}
#[verifier(external_body)] // TODO remove once parsley integrated
pub exec fn parse_owl_t(arg: &[u8]) -> (res: Option<owl_t>)
ensures res.is_Some() ==> parse_owlSpec_t(arg.view()).is_Some(),
        res.is_None() ==> parse_owlSpec_t(arg.view()).is_None(),
        res.is_Some() ==> res.get_Some_0().owl__x.view() == parse_owlSpec_t(arg.view()).get_Some_0().owlSpec__x,
        res.is_Some() ==> res.get_Some_0().owl__y.view() == parse_owlSpec_t(arg.view()).get_Some_0().owlSpec__y,
{
todo!() // call parsley exec parser
}

#[verifier(external_body)] // TODO remove once parsley integrated
pub exec fn serialize_owl_t(arg: &owl_t) -> (res: Vec<u8>)
ensures res.view() == serialize_owlSpec_t(owlSpec_t{owlSpec__x : arg.owl__x.view(), owlSpec__y : arg.owl__y.view()})
{
todo!() // call parsley exec serializer and unwrap
}



// owl_NoResult -> 1, owl_SomeResult -> 2, 
pub struct owl_Result { pub data: Rc<Vec<u8>>, pub parsing_outcome:  owl_Result_ParsingOutcome}
// #[derive(PartialEq, Eq, Debug)]
pub enum owl_Result_ParsingOutcome {
Success,
Failure,
}
#[verifier(external_body)] pub fn len_valid_owl_Result(arg: &[u8])  -> Option<usize> {
if arg.len() < 1 { return None; } else 
if *slice_index_get(arg, 0) == 1u8 && arg.len() >= 1 { return Some( 1); } else 
if *slice_index_get(arg, 0) == 2u8 && arg.len() >= 13 { return Some( 13); }
else { return None; }
}
#[verifier(external_body)] pub fn parse_into_owl_Result(arg: &mut owl_Result) {
match arg.parsing_outcome {
owl_Result_ParsingOutcome::Failure => {
match len_valid_owl_Result(&(*arg.data).as_slice()) {
Some(l) => {arg.parsing_outcome = owl_Result_ParsingOutcome::Success;}
None => {arg.data = rc_new(vec_u8_from_elem(0, 1));
arg.parsing_outcome = owl_Result_ParsingOutcome::Failure;}
}
},
_ => {}}
}
#[verifier(external_body)] pub fn construct_owl_Result_owl_NoResult() -> (res: owl_Result) 
ensures res.data.view() === NoResult()
{
let v = vec_u8_from_elem(1u8, 1);
let res = owl_Result { data: rc_new(v), parsing_outcome:  owl_Result_ParsingOutcome::Success};
res
}
#[verifier(external_body)] pub fn construct_owl_Result_owl_SomeResult(arg: &[u8]) -> (res: owl_Result) 
ensures res.data.view() === SomeResult(arg@)
{
let mut v = vec_u8_from_elem(2u8, 1);
if arg.len() < 12 {return owl_Result {data: rc_new(vec_u8_from_elem(0, 1)), parsing_outcome:  owl_Result_ParsingOutcome::Failure};}
extend_vec_u8(&mut v, slice_subrange(arg, 0, 12));

let res = owl_Result {data: rc_new(v), parsing_outcome:  owl_Result_ParsingOutcome::Success};
res
}



#[verifier(external_body)] pub const fn alice_addr() -> (a:StrSlice<'static>)
ensures endpoint_of_addr(a.view()) == Endpoint::Loc_alice
{
new_strlit("127.0.0.1:9001")
}
#[verifier(external_body)] pub const fn bob_addr() -> (a:StrSlice<'static>)
ensures endpoint_of_addr(a.view()) == Endpoint::Loc_bob
{
new_strlit("127.0.0.1:9002")
}

pub struct state_alice {}
impl state_alice {
#[verifier(external_body)] pub fn init_state_alice () -> Self {
state_alice {}}}pub struct cfg_alice {pub listener: TcpListener,
pub owl_k_data: Rc<Vec<u8>>,
pub owl_shared_key: Rc<Vec<u8>>,
pub salt: Rc<Vec<u8>>}
impl cfg_alice {
#[verifier(external_body)] pub fn init_cfg_alice (config_path : &StrSlice) -> Self {
let listener = TcpListener::bind(alice_addr().into_rust_str()).unwrap();
let owl_k_data = owl_aead::gen_rand_key(cipher());
let config_str = fs::read_to_string(config_path.into_rust_str()).expect("Config file not found");
let config = deserialize_cfg_alice_config(&config_str);
return cfg_alice {listener, owl_k_data : rc_new(owl_k_data), owl_shared_key : rc_new(config.owl_shared_key), salt : rc_new(config.salt)}} pub fn owl_alice_main(&self, Tracked(itree): Tracked<ITreeToken<(Seq<u8>, state_alice), Endpoint>>, mut_state: &mut state_alice) -> (res: Result<( owl_Result
, Tracked<ITreeToken<(Seq<u8>, state_alice), Endpoint>> ), OwlError>)
requires itree@ == alice_main_spec(*self, *old(mut_state))
ensures  res.is_Ok() ==> (res.get_Ok_0().1)@@.results_in((res.get_Ok_0().0.data.view(), *mut_state))
 {
let tracked mut itree = itree;let res_inner = {



let temp_owl__x5 = { rc_clone(&self.owl_shared_key) };
let owl__x5 = rc_clone(&temp_owl__x5);


let temp_owl__x7 = { rc_clone(&self.owl_k_data) };
let owl__x7 = rc_clone(&temp_owl__x7);



let temp_owl__x8 = { let coins = owl_sample::<(Seq<u8>, state_alice)>(Tracked(&mut itree), nonce_size()); owl_enc(&(*rc_clone(&owl__x5)).as_slice(), &(*rc_clone(&owl__x7)).as_slice(), &coins.as_slice()) };
let owl__x8 = rc_clone(&temp_owl__x8);


let temp_owl__x12 = { rc_clone(&owl__x8) };
let owl__x12 = rc_clone(&temp_owl__x12);


let temp_owl__x13 = { owl_output::<(Seq<u8>, state_alice)>(Tracked(&mut itree), &(*rc_clone(&owl__x12)).as_slice(), &bob_addr(), &alice_addr()) };
let owl__x13 = temp_owl__x13;

let (temp_owl_i15, owl__14) = owl_input::<(Seq<u8>, state_alice)>(Tracked(&mut itree), &self.listener);
let owl_i15 = Rc::new(temp_owl_i15);


let temp_owl__x35 = { rc_clone(&self.owl_k_data) };
let owl__x35 = rc_clone(&temp_owl__x35);


let temp_owl__x37 = { rc_clone(&owl_i15) };
let owl__x37 = rc_clone(&temp_owl__x37);



let temp_owl__x39 = { owl_dec(&(*rc_clone(&owl__x35)).as_slice(), &(*rc_clone(&owl__x37)).as_slice()) };
let owl__x39 = temp_owl__x39;


let temp_owl__x40 = { 
let temp_owl_caseval42 = { owl__x39 };
let owl_caseval42 = temp_owl_caseval42;


match  owl_caseval42 {Some(temp_owl_j19) => {let owl_j19 = rc_clone(&temp_owl_j19);


let temp_owl__x27 = { rc_clone(&owl_j19) };
let owl__x27 = rc_clone(&temp_owl__x27);

if let Some(parseval) = parse_owl_t(&(*rc_clone(&owl__x27)).as_slice()) {
let owl_x22 = parseval.owl__x;
let owl_y21 = parseval.owl__y;

let temp_owl__x25 = { owl_y21 };
let owl__x25 = rc_new(temp_owl__x25);


let temp_owl__x26 = { construct_owl_Result_owl_SomeResult(&(*rc_clone(&owl__x25)).as_slice()) };
let owl__x26 = temp_owl__x26;

owl__x26
} else {

let temp_owl__x20 = { construct_owl_Result_owl_NoResult() };
let owl__x20 = temp_owl__x20;

owl__x20
}}
None => {

let temp_owl__x28 = { construct_owl_Result_owl_NoResult() };
let owl__x28 = temp_owl__x28;

owl__x28}} };
let owl__x40 = temp_owl__x40;


let temp_owl__x41 = { owl__x40 };
let owl__x41 = temp_owl__x41;

(owl__x41, Tracked(itree))


};
Ok(res_inner)}

#[verifier(external_body)] pub exec fn owl_alice_main_wrapper(&self, s: &mut state_alice)->(_: owl_Result){
let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<(), Endpoint>::dummy_itree_token();
let tracked (Tracked(call_token), _) = split_bind(dummy_tok, alice_main_spec(*self, *s));
let (res,_): ( owl_Result
, Tracked<ITreeToken<(Seq<u8>, state_alice), Endpoint>> ) = self.owl_alice_main(Tracked(call_token), s, /* todo args? */).unwrap();
res
}}
pub struct state_bob {}
impl state_bob {
#[verifier(external_body)] pub fn init_state_bob () -> Self {
state_bob {}}}pub struct cfg_bob {pub listener: TcpListener,
pub owl_y: Rc<Vec<u8>>,
pub owl_x: Rc<Vec<u8>>,
pub owl_shared_key: Rc<Vec<u8>>,
pub salt: Rc<Vec<u8>>}
impl cfg_bob {
#[verifier(external_body)] pub fn init_cfg_bob (config_path : &StrSlice) -> Self {
let listener = TcpListener::bind(bob_addr().into_rust_str()).unwrap();
let owl_y = owl_aead::gen_rand_nonce(cipher());
let owl_x = owl_aead::gen_rand_nonce(cipher());
let config_str = fs::read_to_string(config_path.into_rust_str()).expect("Config file not found");
let config = deserialize_cfg_bob_config(&config_str);
return cfg_bob {listener, owl_y : rc_new(owl_y), owl_x : rc_new(owl_x), owl_shared_key : rc_new(config.owl_shared_key), salt : rc_new(config.salt)}} pub fn owl_bob_main(&self, Tracked(itree): Tracked<ITreeToken<((), state_bob), Endpoint>>, mut_state: &mut state_bob) -> (res: Result<( ()
, Tracked<ITreeToken<((), state_bob), Endpoint>> ), OwlError>)
requires itree@ == bob_main_spec(*self, *old(mut_state))
ensures  res.is_Ok() ==> (res.get_Ok_0().1)@@.results_in(((), *mut_state))
 {
let tracked mut itree = itree;let res_inner = {


let (temp_owl_i45, owl_ev44) = owl_input::<((), state_bob)>(Tracked(&mut itree), &self.listener);
let owl_i45 = Rc::new(temp_owl_i45);


let temp_owl__x75 = { rc_clone(&self.owl_shared_key) };
let owl__x75 = rc_clone(&temp_owl__x75);


let temp_owl__x77 = { rc_clone(&owl_i45) };
let owl__x77 = rc_clone(&temp_owl__x77);



let temp_owl__x78 = { owl_dec(&(*rc_clone(&owl__x75)).as_slice(), &(*rc_clone(&owl__x77)).as_slice()) };
let owl__x78 = temp_owl__x78;


let temp_owl_caseval79 = { owl__x78 };
let owl_caseval79 = temp_owl_caseval79;


match  owl_caseval79 {Some(temp_owl_k48) => {let owl_k48 = rc_clone(&temp_owl_k48);


let temp_owl__x58 = { rc_clone(&self.owl_x) };
let owl__x58 = rc_clone(&temp_owl__x58);


let temp_owl__x60 = { rc_clone(&self.owl_y) };
let owl__x60 = rc_clone(&temp_owl__x60);


let temp_owl__x62 = { owl_t {owl__x : clone_vec_u8(&*rc_clone(&owl__x58)), owl__y : clone_vec_u8(&*rc_clone(&owl__x60))} };
let owl__x62 = temp_owl__x62;


let temp_owl__x63 = { owl__x62 };
let owl__x63 = temp_owl__x63;


let temp_owl__x68 = { rc_clone(&owl_k48) };
let owl__x68 = rc_clone(&temp_owl__x68);


let temp_owl__x70 = { owl__x63 };
let owl__x70 = temp_owl__x70;



let temp_owl__x71 = { let coins = owl_sample::<((), state_bob)>(Tracked(&mut itree), nonce_size()); owl_enc(&(*rc_clone(&owl__x68)).as_slice(), &(serialize_owl_t(&owl__x70)).as_slice(), &coins.as_slice()) };
let owl__x71 = rc_clone(&temp_owl__x71);


let temp_owl__x72 = { rc_clone(&owl__x71) };
let owl__x72 = rc_clone(&temp_owl__x72);

( owl_output::<((), state_bob)>(Tracked(&mut itree), &(*rc_clone(&owl__x72)).as_slice(), &owl_ev44.as_str(), &bob_addr())
, Tracked(itree) )}
None => {

let temp_owl__x73 = { () };
let owl__x73 = temp_owl__x73;

(owl__x73, Tracked(itree))}}


};
Ok(res_inner)}

#[verifier(external_body)] pub exec fn owl_bob_main_wrapper(&self, s: &mut state_bob)->(_: ()){
let tracked dummy_tok: ITreeToken<(), Endpoint> = ITreeToken::<(), Endpoint>::dummy_itree_token();
let tracked (Tracked(call_token), _) = split_bind(dummy_tok, bob_main_spec(*self, *s));
let (res,_): ( ()
, Tracked<ITreeToken<((), state_bob), Endpoint>> ) = self.owl_bob_main(Tracked(call_token), s, /* todo args? */).unwrap();
res
}}

// ------------------------------------
// ------------ ENTRY POINT -----------
// ------------------------------------

#[verifier(external_body)] #[allow(unreachable_code)] #[allow(unused_variables)]
fn entrypoint() {
let args: std::vec::Vec<std::string::String> = env::args().collect();
if args.len() >= 4 &&  args[1] == "run" &&  args[2] == "alice"{let loc = cfg_alice::init_cfg_alice(&String::from_rust_string(args[3].clone()).as_str());
let mut mut_state = state_alice::init_state_alice();
println!("Waiting for 5 seconds to let other parties start...");
thread::sleep(Duration::new(5, 0));
println!("Running owl_alice_main ...");
let now = Instant::now();
let res = loc.owl_alice_main_wrapper(&mut mut_state);
let elapsed = now.elapsed();
println!("alice returned "/*, res*/);
println!("Elapsed: {:?}", elapsed);}else
if args.len() >= 4 &&  args[1] == "run" &&  args[2] == "bob"{let loc = cfg_bob::init_cfg_bob(&String::from_rust_string(args[3].clone()).as_str());
let mut mut_state = state_bob::init_state_bob();
println!("Waiting for 5 seconds to let other parties start...");
thread::sleep(Duration::new(5, 0));
println!("Running owl_bob_main ...");
let now = Instant::now();
let res = loc.owl_bob_main_wrapper(&mut mut_state);
let elapsed = now.elapsed();
println!("bob returned "/*, res*/);
println!("Elapsed: {:?}", elapsed);}else
if args.len() >= 3 &&  args[1] == "config"{let owl_shared_key = owl_aead::gen_rand_key(cipher());
let salt = owl_util::gen_rand_bytes(64);
let cfg_alice_config: cfg_alice_config = cfg_alice_config {owl_shared_key : owl_shared_key.clone(), salt : salt.clone()};
let cfg_alice_config_serialized = serialize_cfg_alice_config(&cfg_alice_config);
let mut cfg_alice_f = fs::File::create(format!("{}/{}.owl_config", &args[2], "cfg_alice")).expect("Can't create config file");
cfg_alice_f.write_all(cfg_alice_config_serialized.as_bytes()).expect("Can't write config file");
let cfg_bob_config: cfg_bob_config = cfg_bob_config {owl_shared_key : owl_shared_key.clone(), salt : salt.clone()};
let cfg_bob_config_serialized = serialize_cfg_bob_config(&cfg_bob_config);
let mut cfg_bob_f = fs::File::create(format!("{}/{}.owl_config", &args[2], "cfg_bob")).expect("Can't create config file");
cfg_bob_f.write_all(cfg_bob_config_serialized.as_bytes()).expect("Can't write config file");}else{println!("Incorrect usage");}
}



} // verus!

fn main() { entrypoint() }
