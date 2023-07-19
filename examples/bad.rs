// A collection of bad formatting that we expect verusfmt to improve

verus! {

#![verifier=abcd] #![verifier=efgh] pub(in self::super::crate) default const MY_CONST1 : some_type = "abcdefghijklmnopqrstuvwxyz1234567890abcdefghijklmnopqrstuvwxyz1234567890";
#![verifier=abcd] pub(in self::super::crate) default const MY_CONST2: some_type = 5;


}
