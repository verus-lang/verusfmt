//! The "standard library" for [Verus](https://github.com/verus-lang/verus).
//! Contains various utilities and datatypes for proofs,
//! as well as runtime functionality with specifications.
//! For an introduction to Verus, see [the tutorial](https://verus-lang.github.io/verus/guide/).
#![cfg_attr(not(feature = "std"), no_std)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![allow(rustdoc::invalid_rust_codeblocks)]
#![cfg_attr(verus_keep_ghost, feature(core_intrinsics))]
#![cfg_attr(verus_keep_ghost, feature(allocator_api))]
#![cfg_attr(verus_keep_ghost, feature(step_trait))]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod arithmetic {
    mod internals {
        pub mod div_internals_nonlinear {
            //! This file contains proofs related to division that require
            //! nonlinear-arithmetic reasoning to prove. These are internal
            //! functions used within the math standard library.
            //!
            //! It's based on the following file from the Dafny math standard library:
            //! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Internal/DivInternalsNonlinear.dfy`.
            //! That file has the following copyright notice:
            //! /*******************************************************************************
            //! *  Original: Copyright (c) Microsoft Corporation
            //! *  SPDX-License-Identifier: MIT
            //! *
            //! *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
            //! *  SPDX-License-Identifier: MIT
            //! *******************************************************************************/
            #[allow(unused_imports)]
            use builtin::*;
            use builtin_macros::*;

            verus! {

/// Proof that 0 divided by any given integer `d` is 0
#[verifier::nonlinear]
pub proof fn lemma_div_of0(d: int)
    requires
        d != 0 as int,
    ensures
        0 as int / d == 0 as int,
{
}

/// Proof that any given integer `d` divided by itself is 1
pub proof fn lemma_div_by_self(d: int)
    requires
        d != 0,
    ensures
        d / d == 1,
{
}

/// Proof that dividing a non-negative integer by a larger integer results in a quotient of 0
#[verifier::nonlinear]
pub proof fn lemma_small_div()
    ensures
        forall|x: int, d: int| 0 <= x < d && d > 0 ==> #[trigger] (x / d) == 0,
{
}

} // verus!
        }

        pub mod general_internals {
            //! This file contains general internal functions used within the math
            //! standard library.
            //!
            //! It's based on the following file from the Dafny math standard library:
            //! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Internal/GeneralInternals.dfy`.
            //! That file has the following copyright notice:
            //! /*******************************************************************************
            //! *  Original: Copyright (c) Microsoft Corporation
            //! *  SPDX-License-Identifier: MIT
            //! *
            //! *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
            //! *  SPDX-License-Identifier: MIT
            //! *******************************************************************************/
            //! Declares helper lemmas and predicates for non-linear arithmetic
            #[cfg(verus_keep_ghost)]
            use crate::math::{add as add1, sub as sub1};
            #[allow(unused_imports)]
            use builtin::*;
            use builtin_macros::*;

            verus! {

/// Computes the boolean `x <= y`. This is useful where we want to
/// trigger on a `<=` operator but we need a functional rather than a
/// mathematical trigger. (A trigger must be fully functional or fully
/// mathematical.)
pub open spec fn is_le(x: int, y: int) -> bool {
    x <= y
}

/// This proof, local to this module, aids in the process of proving
/// [`lemma_induction_helper`] by covering only the case of nonnegative
/// values of `x`.
proof fn lemma_induction_helper_pos(n: int, f: spec_fn(int) -> bool, x: int)
    requires
        x >= 0,
        n > 0,
        forall|i: int| 0 <= i < n ==> #[trigger] f(i),
        forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, n)),
        forall|i: int| i < n && #[trigger] f(i) ==> #[trigger] f(sub1(i, n)),
    ensures
        f(x),
    decreases x,
{
    if (x >= n) {
        assert(x - n < x);
        lemma_induction_helper_pos(n, f, x - n);
        assert(f(add1(x - n, n)));
        assert(f((x - n) + n));
    }
}

/// This proof, local to this module, aids in the process of proving
/// [`lemma_induction_helper`] by covering only the case of negative
/// values of `x`.
proof fn lemma_induction_helper_neg(n: int, f: spec_fn(int) -> bool, x: int)
    requires
        x < 0,
        n > 0,
        forall|i: int| 0 <= i < n ==> #[trigger] f(i),
        forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, n)),
        forall|i: int| i < n && #[trigger] f(i) ==> #[trigger] f(sub1(i, n)),
    ensures
        f(x),
    decreases -x,
{
    if (-x <= n) {
        lemma_induction_helper_pos(n, f, x + n);
        assert(f(sub1(x + n, n)));
        assert(f((x + n) - n));
    } else {
        lemma_induction_helper_neg(n, f, x + n);
        assert(f(sub1(x + n, n)));
        assert(f((x + n) - n));
    }
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate, proves the
/// predicate holds in certain base cases, and proves correctness of
/// inductive steps both upward and downward from the base cases. This
/// lemma invokes induction to establish that the predicate holds for
/// the given arbitrary input `x`.
///
/// `f`: The integer predicate
///
/// `n`: Upper bound on the base cases. Specifically, the caller
/// establishes `f(i)` for every value `i` satisfying `0 <= i < n`.
///
/// `x`: The desired case established by this lemma. Its postcondition
/// is thus simply `f(x)`.
///
/// To prove inductive steps upward from the base cases, the caller
/// must establish that, for any `i >= 0`, `f(i) ==> f(add1(i, n))`.
/// `add1(i, n)` is just `i + n`, but written in a functional style
/// so that it can be used where functional triggers are required.
///
/// To prove inductive steps downward from the base cases, the caller
/// must establish that, for any `i < n`, `f(i) ==> f(sub1(i, n))`.
/// `sub1(i, n)` is just `i - n`, but written in a functional style
/// so that it can be used where functional triggers are required.
pub proof fn lemma_induction_helper(n: int, f: spec_fn(int) -> bool, x: int)
    requires
        n > 0,
        forall|i: int| 0 <= i < n ==> #[trigger] f(i),
        forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, n)),
        forall|i: int| i < n && #[trigger] f(i) ==> #[trigger] f(sub1(i, n)),
    ensures
        f(x),
{
    if (x >= 0) {
        lemma_induction_helper_pos(n, f, x);
    } else {
        lemma_induction_helper_neg(n, f, x);
    }
}

} // verus!
        }

        pub mod mod_internals_nonlinear {
            //! This file contains proofs related to modulo that require
            //! nonlinear-arithmetic reasoning to prove. These are internal
            //! functions used within the math standard library.
            //!
            //! It's based on the following file from the Dafny math standard library:
            //! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Internal/ModInternalsNonlinear.dfy`.
            //! That file has the following copyright notice:
            //! /*******************************************************************************
            //! *  Original: Copyright (c) Microsoft Corporation
            //! *  SPDX-License-Identifier: MIT
            //! *
            //! *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
            //! *  SPDX-License-Identifier: MIT
            //! *******************************************************************************/
            #[allow(unused_imports)]
            use builtin::*;
            use builtin_macros::*;

            verus! {

/// Computes `x % y`. This is useful where we want to trigger on a
/// modulo operator but we need a functional rather than a
/// mathematical trigger. (A trigger must be fully functional or fully
/// mathematical.)
pub open spec fn modulus(x: int, y: int) -> int {
    x % y
}

/// Proof that 0 modulo any positive integer `m` is 0
proof fn lemma_mod_of_zero_is_zero(m: int)
    requires
        0 < m,
    ensures
        0 as int % m == 0 as int,
{
}

/// Proof of the fundamental theorem of division and modulo: That for
/// any positive divisor `d` and any integer `x`, `x` is equal to `d`
/// times `x / d` plus `x % d`.
#[verifier::nonlinear]
pub proof fn lemma_fundamental_div_mod(x: int, d: int)
    requires
        d != 0,
    ensures
        x == d * (x / d) + (x % d),
{
}

/// Proof that 0 modulo any integer is 0
proof fn lemma_0_mod_anything()
    ensures
        forall|m: int| m > 0 ==> #[trigger] modulus(0, m) == 0,
{
}

/// Proof that a natural number `x` divided by a larger natural number
/// `m` gives a remainder equal to `x`
#[verifier(nonlinear)]
pub proof fn lemma_small_mod(x: nat, m: nat)
    requires
        x < m,
        0 < m,
    ensures
        #[trigger] modulus(x as int, m as int) == x as int,
{
}

/// Proof of Euclid's division lemma, i.e., that any integer `x`
/// modulo any positive integer `m` is in the half-open range `[0, m)`.
#[verifier(nonlinear)]
pub proof fn lemma_mod_range(x: int, m: int)
    requires
        m > 0,
    ensures
        0 <= #[trigger] modulus(x, m) < m,
{
}

} // verus!
        }

        pub mod mul_internals_nonlinear {
            //! This file contains proofs related to multiplication that require
            //! nonlinear-arithmetic reasoning to prove. These are internal
            //! functions used within the math standard library.
            //!
            //! It's based on the following file from the Dafny math standard library:
            //! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Internal/MulInternalsNonlinear.dfy`.
            //! That file has the following copyright notice:
            //! /*******************************************************************************
            //! *  Original: Copyright (c) Microsoft Corporation
            //! *  SPDX-License-Identifier: MIT
            //! *
            //! *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
            //! *  SPDX-License-Identifier: MIT
            //! *******************************************************************************/
            /*
               WARNING: Think three times before adding to this file, as nonlinear
               verification is highly unstable!
            */
            // may be try to use singular?
            #[allow(unused_imports)]
            use builtin::*;
            use builtin_macros::*;

            verus! {

/// Proof that multiplying two positive integers `x` and `y` will result in a positive integer
#[verifier::nonlinear]
pub proof fn lemma_mul_strictly_positive(x: int, y: int)
    ensures
        (0 < x && 0 < y) ==> (0 < x * y),
{
}

/// Proof that `x` and `y` are both nonzero if and only if `x * y` is nonzero
#[verifier::nonlinear]
pub proof fn lemma_mul_nonzero(x: int, y: int)
    ensures
        x * y != 0 <==> x != 0 && y != 0,
{
}

/// Proof that multiplication is associative in this specific case,
/// i.e., that `x * y * z` is the same no matter which of the two
/// multiplications is done first
#[verifier::nonlinear]
pub proof fn lemma_mul_is_associative(x: int, y: int, z: int)
    ensures
        x * (y * z) == (x * y) * z,
{
}

/// Proof that multiplication distributes over addition in this
/// specific case, i.e., that `x * (y + z)` equals `x * y` plus `x * z`
#[verifier::nonlinear]
pub proof fn lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures
        x * (y + z) == x * y + x * z,
{
}

/// Proof that the if the product of two nonzero integers `x` and `y`
/// is nonnegative, then it's greater than or equal to each of `x` and
/// `y`
#[verifier::nonlinear]
pub proof fn lemma_mul_ordering(x: int, y: int)
    requires
        x != 0,
        y != 0,
        0 <= x * y,
    ensures
        x * y >= x && x * y >= y,
{
}

/// Proof that multiplying by a positive integer preserves inequality
/// in this specific case, i.e., that since `x < y` and `z > 0` we can
/// conclude that `x * z < y * z`.
#[verifier::nonlinear]
pub proof fn lemma_mul_strict_inequality(x: int, y: int, z: int)
    requires
        x < y,
        z > 0,
    ensures
        x * z < y * z,
{
}

} // verus!
        }

        pub mod div_internals {
            //! This file contains proofs related to division. These are internal
            //! functions used within the math standard library.
            //!
            //! It's based on the following file from the Dafny math standard library:
            //! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Internal/DivInternals.dfy`.
            //! That file has the following copyright notice:
            //! /*******************************************************************************
            //! *  Original: Copyright (c) Microsoft Corporation
            //! *  SPDX-License-Identifier: MIT
            //! *
            //! *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
            //! *  SPDX-License-Identifier: MIT
            //! *******************************************************************************/
            #[allow(unused_imports)]
            use builtin::*;
            use builtin_macros::*;

            verus! {

#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::general_internals::is_le;
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::mod_internals::{
    lemma_mod_induction_forall,
    lemma_mod_induction_forall2,
    mod_auto,
    lemma_mod_auto,
    lemma_mod_basics,
};
use crate::arithmetic::internals::mod_internals_nonlinear;
#[cfg(verus_keep_ghost)]
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::div_internals_nonlinear;
#[cfg(verus_keep_ghost)]
use crate::math::{add as add1, sub as sub1};

/// This function recursively computes the quotient resulting from
/// dividing two numbers `x` and `d`, in the case where `d > 0`
#[verifier(opaque)]
pub open spec fn div_pos(x: int, d: int) -> int
    recommends
        d > 0,
    decreases
            (if x < 0 {
                d - x
            } else {
                x
            }),
    when d > 0
{
    if x < 0 {
        -1 + div_pos(x + d, d)
    } else if x < d {
        0
    } else {
        1 + div_pos(x - d, d)
    }
}

/// This function recursively computes the quotient resulting from
/// dividing two numbers `x` and `d`. It's only meaningful when `d !=
/// 0`, of course.
#[verifier(opaque)]
pub open spec fn div_recursive(x: int, d: int) -> int
    recommends
        d != 0,
{
    // reveal(div_pos);
    if d > 0 {
        div_pos(x, d)
    } else {
        -1 * div_pos(x, -1 * d)
    }
}

/// Proof of basic properties of integer division when the divisor is
/// the given positive integer `n`
pub proof fn lemma_div_basics(n: int)
    requires
        n > 0,
    ensures
        (n / n) == 1 && -((-n) / n) == 1,
        forall|x: int| 0 <= x < n <==> #[trigger] (x / n) == 0,
        forall|x: int| #[trigger] ((x + n) / n) == x / n + 1,
        forall|x: int| #[trigger] ((x - n) / n) == x / n - 1,
{
    lemma_mod_auto(n);
    lemma_mod_basics(n);
    div_internals_nonlinear::lemma_small_div();
    div_internals_nonlinear::lemma_div_by_self(n);
    assert forall|x: int| 0 <= x < n <== #[trigger] (x / n) == 0 by {
        mod_internals_nonlinear::lemma_fundamental_div_mod(x, n);
    }
}

/// This function says that for any `x` and `y`, there are two
/// possibilities for the sum `x % n + y % n`: (1) It's in the range
/// `[0, n)` and `(x + y) / n == x / n + y / n`. (2) It's in the range
/// `[n, n + n)` and `(x + y) / n = x / n + y / n + 1`.
pub open spec fn div_auto_plus(n: int) -> bool {
    forall|x: int, y: int|
        #![trigger ((x + y) / n)]
        {
            let z = (x % n) + (y % n);
            ((0 <= z < n && ((x + y) / n) == x / n + y / n) || (n <= z < n + n && ((x + y) / n) == x
                / n + y / n + 1))
        }
}

/// This function says that for any `x` and `y`, there are two
/// possibilities for the difference `x % n - y % n`: (1) It's in the
/// range `[0, n)` and `(x - y) / n == x / n - y / n`. (2) It's in the
/// range `[-n, 0)` and `(x - y) / n = x / n - y / n - 1`.
pub open spec fn div_auto_minus(n: int) -> bool {
    forall|x: int, y: int|
        #![trigger ((x - y) / n)]
        {
            let z = (x % n) - (y % n);
            ((0 <= z < n && ((x - y) / n) == x / n - y / n) || (-n <= z < 0 && ((x - y) / n) == x
                / n - y / n - 1))
        }
}

/// This function states various properties of integer division when
/// the denominator is `n`, including the identity property, a fact
/// about when quotients are zero, and facts about adding and
/// subtracting integers over this common denominator
pub open spec fn div_auto(n: int) -> bool
    recommends
        n > 0,
{
    &&& mod_auto(n)
    &&& (n / n == -((-n) / n) == 1)
    &&& forall|x: int| 0 <= x < n <==> #[trigger] (x / n) == 0
    &&& div_auto_plus(n)
    &&& div_auto_minus(n)
}

/// Proof of `div_auto_plus(n)`, not exported publicly because it's
/// just used as part of [`lemma_div_auto`] to prove `div_auto(n)`
proof fn lemma_div_auto_plus(n: int)
    requires
        n > 0,
    ensures
        div_auto_plus(n),
{
    lemma_mod_auto(n);
    lemma_div_basics(n);
    assert forall|x: int, y: int|
        {
            let z = (x % n) + (y % n);
            ((0 <= z < n && #[trigger] ((x + y) / n) == x / n + y / n) || (n <= z < n + n && ((x
                + y) / n) == x / n + y / n + 1))
        } by {
        let f = |xx: int, yy: int|
            {
                let z = (xx % n) + (yy % n);
                ((0 <= z < n && ((xx + yy) / n) == xx / n + yy / n) || (n <= z < 2 * n && ((xx + yy)
                    / n) == xx / n + yy / n + 1))
            };
        assert forall|i: int, j: int|
            {
                // changing this from j + n to mod's addition speeds up the verification
                // otherwise you need higher rlimit
                // might be a good case for profilers
                &&& (j >= 0 && #[trigger] f(i, j) ==> f(i, add1(j, n)))
                &&& (i < n && f(i, j) ==> f(i - n, j))
                &&& (j < n && f(i, j) ==> f(i, j - n))
                &&& (i >= 0 && f(i, j) ==> f(i + n, j))
            } by {
            assert(((i + n) + j) / n == ((i + j) + n) / n);
            assert((i + (j + n)) / n == ((i + j) + n) / n);
            assert(((i - n) + j) / n == ((i + j) - n) / n);
            assert((i + (j - n)) / n == ((i + j) - n) / n);
        }
        assert forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> #[trigger] f(i, j) by {
            assert(((i + n) + j) / n == ((i + j) + n) / n);
            assert((i + (j + n)) / n == ((i + j) + n) / n);
            assert(((i - n) + j) / n == ((i + j) - n) / n);
            assert((i + (j - n)) / n == ((i + j) - n) / n);
        }
        lemma_mod_induction_forall2(n, f);
        assert(f(x, y));
    }
}

/// Proof of `div_auto_mius(n)`, not exported publicly because it's
/// just used as part of [`lemma_div_auto`] to prove `div_auto(n)`
proof fn lemma_div_auto_minus(n: int)
    requires
        n > 0,
    ensures
        div_auto_minus(n),
{
    lemma_mod_auto(n);
    lemma_div_basics(n);
    assert forall|x: int, y: int|
        {
            let z = (x % n) - (y % n);
            ((0 <= z < n && #[trigger] ((x - y) / n) == x / n - y / n) || (-n <= z < 0 && ((x - y)
                / n) == x / n - y / n - 1))
        } by {
        let f = |xx: int, yy: int|
            {
                let z = (xx % n) - (yy % n);
                ((0 <= z < n && ((xx - yy) / n) == xx / n - yy / n) || (-n <= z < 0 && (xx - yy) / n
                    == xx / n - yy / n - 1))
            };
        assert forall|i: int, j: int|
            {
                &&& (j >= 0 && #[trigger] f(i, j) ==> f(i, add1(j, n)))
                &&& (i < n && f(i, j) ==> f(sub1(i, n), j))
                &&& (j < n && f(i, j) ==> f(i, sub1(j, n)))
                &&& (i >= 0 && f(i, j) ==> f(add1(i, n), j))
            } by {
            assert(((i + n) - j) / n == ((i - j) + n) / n);
            assert((i - (j - n)) / n == ((i - j) + n) / n);
            assert(((i - n) - j) / n == ((i - j) - n) / n);
            assert((i - (j + n)) / n == ((i - j) - n) / n);
        }
        assert forall|i: int, j: int| 0 <= i < n && 0 <= j < n implies #[trigger] f(i, j) by {
            assert(((i + n) - j) / n == ((i - j) + n) / n);
            assert((i - (j - n)) / n == ((i - j) + n) / n);
            assert(((i - n) - j) / n == ((i - j) - n) / n);
            assert((i - (j + n)) / n == ((i - j) - n) / n);
        }
        lemma_mod_induction_forall2(n, f);
        assert(f(x, y));
    }
}

/// Proof of `div_auto(n)`, which expresses many useful properties of
/// division when the denominator is the given positive integer `n`.
pub proof fn lemma_div_auto(n: int)
    requires
        n > 0,
    ensures
        div_auto(n),
{
    lemma_mod_auto(n);
    lemma_div_basics(n);
    assert forall|x: int| 0 <= x < n <==> #[trigger] (x / n) == 0 by {
        lemma_div_basics(n);
    }
    assert((0 + n) / n == 1);
    assert((0 - n) / n == -1);
    lemma_div_auto_plus(n);
    lemma_div_auto_minus(n);
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate, proves the
/// predicate holds in certain base cases, and proves correctness of
/// inductive steps both upward and downward from the base cases. This
/// lemma invokes induction to establish that the predicate holds for
/// the given arbitrary input `x`.
///
/// `f`: The integer predicate
///
/// `n`: Upper bound on the base cases. Specifically, the caller
/// establishes `f(i)` for every value `i` satisfying `is_le(0, i) &&
/// i < n`.
///
/// `x`: The desired case established by this lemma. Its postcondition
/// thus includes `f(x)`.
///
/// To prove inductive steps upward from the base cases, the caller
/// must establish that, for any `i`, `is_le(0, i) && f(i) ==> f(i +
/// n)`. `is_le(0, i)` is just `0 <= i`, but written in a functional
/// style so that it can be used where functional triggers are
/// required.
///
/// To prove inductive steps downward from the base cases, the caller
/// must establish that, for any `i`, `is_le(i + 1, n) && f(i) ==> f(i
/// - n)`. `is_le(i + 1, n)` is just `i + 1 <= n`, but written in a
/// functional style so that it can be used where functional triggers
/// are required.
pub proof fn lemma_div_induction_auto(n: int, x: int, f: spec_fn(int) -> bool)
    requires
        n > 0,
        div_auto(n) ==> {
            &&& (forall|i: int| #[trigger] is_le(0, i) && i < n ==> f(i))
            &&& (forall|i: int| #[trigger] is_le(0, i) && f(i) ==> f(i + n))
            &&& (forall|i: int| #[trigger] is_le(i + 1, n) && f(i) ==> f(i - n))
        },
    ensures
        div_auto(n),
        f(x),
{
    lemma_div_auto(n);
    assert(forall|i: int| is_le(0, i) && i < n ==> f(i));
    assert(forall|i: int| is_le(0, i) && #[trigger] f(i) ==> #[trigger] f(add1(i, n)));
    assert(forall|i: int| is_le(i + 1, n) && #[trigger] f(i) ==> #[trigger] f(sub1(i, n)));
    assert forall|i: int| 0 <= i < n implies #[trigger] f(i) by {
        assert(f(i)) by {
            assert(forall|i: int| is_le(0, i) && i < n ==> f(i));
            assert(is_le(0, i) && i < n);
        };
    };
    lemma_mod_induction_forall(n, f);
    assert(f(x));
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate, proves the
/// predicate holds in certain base cases, and proves correctness of
/// inductive steps both upward and downward from the base cases. This
/// lemma invokes induction to establish that the predicate holds for
/// all integer values.
///
/// `f`: The integer predicate
///
/// `n`: Upper bound on the base cases. Specifically, the caller
/// establishes `f(i)` for every value `i` satisfying `is_le(0, i) &&
/// i < n`.
///
/// To prove inductive steps upward from the base cases, the caller
/// must establish that, for any `i`, `is_le(0, i) && f(i) ==> f(i +
/// n)`. `is_le(0, i)` is just `0 <= i`, but written in a functional
/// style so that it can be used where functional triggers are
/// required.
///
/// To prove inductive steps downward from the base cases, the caller
/// must establish that, for any `i`, `is_le(i + 1, n) && f(i) ==> f(i
/// - n)`. `is_le(i + 1, n)` is just `i + 1 <= n`, but written in a
/// functional style so that it can be used where functional triggers
/// are required.
pub proof fn lemma_div_induction_auto_forall(n: int, f: spec_fn(int) -> bool)
    requires
        n > 0,
        div_auto(n) ==> {
            &&& (forall|i: int| #[trigger] is_le(0, i) && i < n ==> f(i))
            &&& (forall|i: int| #[trigger] is_le(0, i) && f(i) ==> f(i + n))
            &&& (forall|i: int| #[trigger] is_le(i + 1, n) && f(i) ==> f(i - n))
        },
    ensures
        div_auto(n),
        forall|i| #[trigger] f(i),
{
    assert(div_auto(n)) by {
        lemma_div_induction_auto(n, 0, f);
    }
    assert forall|i| #[trigger] f(i) by {
        lemma_div_induction_auto(n, i, f);
    }
}

} // verus!
        }

        pub mod mod_internals {
            //! This file contains proofs related to modulo. These are internal
            //! functions used within the math standard library.
            //!
            //! It's based on the following file from the Dafny math standard library:
            //! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Internal/ModInternals.dfy`.
            //! That file has the following copyright notice:
            //! /*******************************************************************************
            //! *  Original: Copyright (c) Microsoft Corporation
            //! *  SPDX-License-Identifier: MIT
            //! *
            //! *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
            //! *  SPDX-License-Identifier: MIT
            //! *******************************************************************************/
            #[allow(unused_imports)]
            use builtin::*;
            use builtin_macros::*;

            verus! {

use crate::arithmetic::internals::general_internals::*;
use crate::arithmetic::mul::*;
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::mul_internals::lemma_mul_auto;
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::mul_internals_nonlinear;
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::mod_internals_nonlinear::{
    lemma_fundamental_div_mod,
    lemma_mod_range,
    lemma_small_mod,
};
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::div_internals_nonlinear;
#[cfg(verus_keep_ghost)]
use crate::math::{add as add1, sub as sub1};

/// This function performs the modulus operation recursively.
#[verifier(opaque)]
pub open spec fn mod_recursive(x: int, d: int) -> int
    recommends
        d > 0,
    decreases
            (if x < 0 {
                (d - x)
            } else {
                x
            }),
    when d > 0
{
    if x < 0 {
        mod_recursive(d + x, d)
    } else if x < d {
        x
    } else {
        mod_recursive(x - d, d)
    }
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate, proves the
/// predicate holds in certain base cases, and proves correctness of
/// inductive steps both upward and downward from the base cases. This
/// lemma invokes induction to establish that the predicate holds for
/// all possible inputs.
///
/// `f`: The integer predicate
///
/// `n`: Upper bound on the base cases. Specifically, the caller
/// establishes `f(i)` for every value `i` satisfying `0 <= i < n`.
///
/// To prove inductive steps upward from the base cases, the caller
/// must establish that, for any `i >= 0`, `f(i) ==> f(add1(i, n))`.
/// `add1(i, n)` is just `i + n`, but written in a functional style
/// so that it can be used where functional triggers are required.
///
/// To prove inductive steps downward from the base cases, the caller
/// must establish that, for any `i < n`, `f(i) ==> f(sub1(i, n))`.
/// `sub1(i, n)` is just `i - n`, but written in a functional style
/// so that it can be used where functional triggers are required.
pub proof fn lemma_mod_induction_forall(n: int, f: spec_fn(int) -> bool)
    requires
        n > 0,
        forall|i: int| 0 <= i < n ==> #[trigger] f(i),
        forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, n)),
        forall|i: int| i < n && #[trigger] f(i) ==> #[trigger] f(sub1(i, n)),
    ensures
        forall|i| #[trigger] f(i),
{
    assert forall|i: int| #[trigger] f(i) by {
        lemma_induction_helper(n, f, i);
    };
}

/// This utility function helps prove a mathematical property of a
/// pair of integers by induction. The caller supplies a predicate
/// over a pair of integers, proves the predicate holds in certain
/// base cases, and proves correctness of inductive steps both upward
/// and downward from the base cases. This lemma invokes induction to
/// establish that the predicate holds for all possible inputs.
///
/// `f`: The integer predicate
///
/// `n`: Upper bound on the base cases. Specifically, the caller
/// establishes `f(i, j)` for every pair of values `i, j` satisfying
/// `0 <= i < n` and `0 <= j < n`.
///
/// To prove inductive steps from the base cases, the caller must
/// establish that:
///
/// 1) For any `i >= 0`, `f(i, j) ==> f(add1(i, n), j)`. `add1(i, n)`
/// is just `i + n`, but written in a functional style so that it can
/// be used where functional triggers are required.
///
/// 2) For any `j >= 0`, `f(i, j) ==> f(i, add1(j, n))`
///
/// 3) For any `i < n`, `f(i) ==> f(sub1(i, n))`. `sub1(i, n)` is just
/// `i - n`, but written in a functional style so that it can be used
/// where functional triggers are required.
///
/// 4) For any `j < n`, `f(j) ==> f(i, sub1(j, n))`.
pub proof fn lemma_mod_induction_forall2(n: int, f: spec_fn(int, int) -> bool)
    requires
        n > 0,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> #[trigger] f(i, j),
        forall|i: int, j: int| i >= 0 && #[trigger] f(i, j) ==> #[trigger] f(add1(i, n), j),
        forall|i: int, j: int| j >= 0 && #[trigger] f(i, j) ==> #[trigger] f(i, add1(j, n)),
        forall|i: int, j: int| i < n && #[trigger] f(i, j) ==> #[trigger] f(sub1(i, n), j),
        forall|i: int, j: int| j < n && #[trigger] f(i, j) ==> #[trigger] f(i, sub1(j, n)),
    ensures
        forall|i: int, j: int| #[trigger] f(i, j),
{
    assert forall|x: int, y: int| #[trigger] f(x, y) by {
        assert forall|i: int| 0 <= i < n implies #[trigger] f(i, y) by {
            let fj = |j| f(i, j);
            lemma_mod_induction_forall(n, fj);
            assert(fj(y));
        };
        let fi = |i| f(i, y);
        lemma_mod_induction_forall(n, fi);
        assert(fi(x));
    };
}

/// Proof that when dividing, adding the denominator to the numerator
/// increases the result by 1. Specifically, for the given `n` and `x`,
/// `(x + n) / n == x / n + 1`.
pub proof fn lemma_div_add_denominator(n: int, x: int)
    requires
        n > 0,
    ensures
        (x + n) / n == x / n + 1,
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x + n, n);
    let zp = (x + n) / n - x / n - 1;
    assert(0 == n * zp + ((x + n) % n) - (x % n)) by { lemma_mul_auto() };
    if (zp > 0) {
        lemma_mul_inequality(1, zp, n);
    }
    if (zp < 0) {
        lemma_mul_inequality(zp, -1, n);
    }
}

/// Proof that when dividing, subtracting the denominator from the numerator
/// decreases the result by 1. Specifically, for the given `n` and `x`,
/// `(x - n) / n == x / n - 1`.
pub proof fn lemma_div_sub_denominator(n: int, x: int)
    requires
        n > 0,
    ensures
        (x - n) / n == x / n - 1,
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x - n, n);
    let zm = (x - n) / n - x / n + 1;
    assert(0 == n * zm + ((x - n) % n) - (x % n)) by {
        lemma_mul_auto();
    }
    if (zm > 0) {
        lemma_mul_inequality(1, zm, n);
    }
    if (zm < 0) {
        lemma_mul_inequality(zm, -1, n);
    }
}

/// Proof that when dividing, adding the denominator to the numerator
/// doesn't change the remainder. Specifically, for the given `n` and
/// `x`, `(x + n) % n == x % n`.
#[verifier::spinoff_prover]
pub proof fn lemma_mod_add_denominator(n: int, x: int)
    requires
        n > 0,
    ensures
        (x + n) % n == x % n,
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x + n, n);
    let zp = (x + n) / n - x / n - 1;
    assert(n * zp == n * ((x + n) / n - x / n) - n) by {
        assert(n * (((x + n) / n - x / n) - 1) == n * ((x + n) / n - x / n) - n) by {
            lemma_mul_is_distributive_auto();
        };
    };
    assert(0 == n * zp + ((x + n) % n) - (x % n)) by {
        lemma_mul_auto();
    }
    if (zp > 0) {
        lemma_mul_inequality(1, zp, n);
    }
    if (zp < 0) {
        lemma_mul_inequality(zp, -1, n);
    }
}

/// Proof that when dividing, subtracting the denominator from the
/// numerator doesn't change the remainder. Specifically, for the
/// given `n` and `x`, `(x - n) % n == x % n`.
pub proof fn lemma_mod_sub_denominator(n: int, x: int)
    requires
        n > 0,
    ensures
        (x - n) % n == x % n,
{
    lemma_fundamental_div_mod(x, n);
    lemma_fundamental_div_mod(x - n, n);
    let zm = (x - n) / n - x / n + 1;
    lemma_mul_is_distributive_auto();  // OBSERVE
    assert(0 == n * zm + ((x - n) % n) - (x % n)) by {
        lemma_mul_auto();
    }
    if (zm > 0) {
        lemma_mul_inequality(1, zm, n);
    }
    if (zm < 0) {
        lemma_mul_inequality(zm, -1, n);
    }
}

/// Proof that for the given `n` and `x`, `x % n == x` if and only if
/// `0 <= x < n`.
pub proof fn lemma_mod_below_denominator(n: int, x: int)
    requires
        n > 0,
    ensures
        0 <= x < n <==> x % n == x,
{
    assert forall|x: int| 0 <= x < n <==> #[trigger] (x % n) == x by {
        if (0 <= x < n) {
            lemma_small_mod(x as nat, n as nat);
        }
        lemma_mod_range(x, n);
    }
}

/// Proof of basic properties of the division given the divisor `n`:
///
/// 1) Adding the denominator to the numerator increases the quotient
/// by 1 and doesn't change the remainder.
///
/// 2) Subtracting the denominator from the numerator decreases the
/// quotient by 1 and doesn't change the remainder.
///
/// 3) The numerator is the same as the result if and only if the
/// numerator is in the half-open range `[0, n)`.
pub proof fn lemma_mod_basics(n: int)
    requires
        n > 0,
    ensures
        forall|x: int| #[trigger] ((x + n) % n) == x % n,
        forall|x: int| #[trigger] ((x - n) % n) == x % n,
        forall|x: int| #[trigger] ((x + n) / n) == x / n + 1,
        forall|x: int| #[trigger] ((x - n) / n) == x / n - 1,
        forall|x: int| 0 <= x < n <==> #[trigger] (x % n) == x,
{
    assert forall|x: int| #[trigger] ((x + n) % n) == x % n by {
        lemma_mod_add_denominator(n, x);
    };
    assert forall|x: int| #[trigger] ((x - n) % n) == x % n by {
        lemma_mod_sub_denominator(n, x);
        assert((x - n) % n == x % n);
    };
    assert forall|x: int| #[trigger] ((x + n) / n) == x / n + 1 by {
        lemma_div_add_denominator(n, x);
    };
    assert forall|x: int| #[trigger] ((x - n) / n) == x / n - 1 by {
        lemma_div_sub_denominator(n, x);
    };
    assert forall|x: int| 0 <= x < n <==> #[trigger] (x % n) == x by {
        lemma_mod_below_denominator(n, x);
    };
}

/// Proof that if `x == q * r + n` and `0 <= r < n`, then `q == x / n`
/// and `r == x % n`. Essentially, this is the converse of the
/// fundamental theorem of division and modulo.
pub proof fn lemma_quotient_and_remainder(x: int, q: int, r: int, n: int)
    requires
        n > 0,
        0 <= r < n,
        x == q * n + r,
    ensures
        q == x / n,
        r == x % n,
    decreases
            (if q > 0 {
                q
            } else {
                -q
            }),
{
    lemma_mod_basics(n);
    if q > 0 {
        mul_internals_nonlinear::lemma_mul_is_distributive_add(n, q - 1, 1);
        lemma_mul_is_commutative_auto();
        assert(q * n + r == (q - 1) * n + n + r);
        lemma_quotient_and_remainder(x - n, q - 1, r, n);
    } else if q < 0 {
        lemma_mul_is_distributive_sub(n, q + 1, 1);
        lemma_mul_is_commutative_auto();
        assert(q * n + r == (q + 1) * n - n + r);
        lemma_quotient_and_remainder(x + n, q + 1, r, n);
    } else {
        div_internals_nonlinear::lemma_small_div();
        assert(r / n == 0);
    }
}

/// This function says that for any `x` and `y`, there are two
/// possibilities for the sum `x % n + y % n`: (1) It's in the range
/// `[0, n)` and it's equal to `(x + y) % n`. (2) It's in the range
/// `[n, n + n)` and it's equal to `(x + y) % n + n`.
pub open spec fn mod_auto_plus(n: int) -> bool
    recommends
        n > 0,
{
    forall|x: int, y: int|
        {
            let z = (x % n) + (y % n);
            ((0 <= z < n && #[trigger] ((x + y) % n) == z) || (n <= z < n + n && ((x + y) % n) == z
                - n))
        }
}

/// This function says that for any `x` and `y`, there are two
/// possibilities for the difference `x % n - y % n`: (1) It's in the
/// range `[0, n)` and it's equal to `(x - y) % n`. (2) It's in the
/// range `[-n, 0)` and it's equal to `(x + y) % n - n`.
pub open spec fn mod_auto_minus(n: int) -> bool
    recommends
        n > 0,
{
    forall|x: int, y: int|
        {
            let z = (x % n) - (y % n);
            ((0 <= z < n && #[trigger] ((x - y) % n) == z) || (-n <= z < 0 && ((x - y) % n) == z
                + n))
        }
}

/// This function states various useful properties about the modulo
/// operator when the divisor is `n`.
pub open spec fn mod_auto(n: int) -> bool
    recommends
        n > 0,
{
    &&& (n % n == 0 && (-n) % n == 0)
    &&& (forall|x: int| #[trigger] ((x % n) % n) == x % n)
    &&& (forall|x: int| 0 <= x < n <==> #[trigger] (x % n) == x)
    &&& mod_auto_plus(n)
    &&& mod_auto_minus(n)
}

/// Proof of `mod_auto(n)`, which states various useful properties
/// about the modulo operator when the divisor is the positive number
/// `n`
pub proof fn lemma_mod_auto(n: int)
    requires
        n > 0,
    ensures
        mod_auto(n),
{
    lemma_mod_basics(n);
    lemma_mul_auto();
    assert forall|x: int, y: int|
        {
            let z = (x % n) + (y % n);
            ((0 <= z < n && #[trigger] ((x + y) % n) == z) || (n <= z < n + n && ((x + y) % n) == z
                - n))
        } by {
        let xq = x / n;
        let xr = x % n;
        lemma_fundamental_div_mod(x, n);
        assert(x == xq * n + xr);
        let yq = y / n;
        let yr = y % n;
        lemma_fundamental_div_mod(y, n);
        assert(y == yq * n + yr);
        if xr + yr < n {
            lemma_quotient_and_remainder(x + y, xq + yq, xr + yr, n);
        } else {
            lemma_quotient_and_remainder(x + y, xq + yq + 1, xr + yr - n, n);
        }
    }
    assert forall|x: int, y: int|
        {
            let z = (x % n) - (y % n);
            ((0 <= z < n && #[trigger] ((x - y) % n) == z) || (-n <= z < 0 && ((x - y) % n) == z
                + n))
        } by {
        let xq = x / n;
        let xr = x % n;
        lemma_fundamental_div_mod(x, n);
        assert(x == n * (x / n) + (x % n));
        let yq = y / n;
        let yr = y % n;
        lemma_fundamental_div_mod(y, n);
        assert(y == yq * n + yr);
        if xr - yr >= 0 {
            lemma_quotient_and_remainder(x - y, xq - yq, xr - yr, n);
        } else {  // xr - yr < 0
            lemma_quotient_and_remainder(x - y, xq - yq - 1, xr - yr + n, n);
        }
    }
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate, proves the
/// predicate holds in certain base cases, and proves correctness of
/// inductive steps both upward and downward from the base cases. This
/// lemma invokes induction to establish that the predicate holds for
/// the given arbitrary input `x`.
///
/// `f`: The integer predicate
///
/// `n`: Upper bound on the base cases. Specifically, the caller
/// establishes `f(i)` for every value `i` satisfying `is_le(0, i) &&
/// i < n`.
///
/// `x`: The desired case established by this lemma. Its postcondition
/// thus includes `f(x)`.
///
/// To prove inductive steps upward from the base cases, the caller
/// must establish that, for any `i`, `is_le(0, i) && f(i) ==> f(i +
/// n)`. `is_le(0, i)` is just `0 <= i`, but written in a functional
/// style so that it can be used where functional triggers are
/// required.
///
/// To prove inductive steps downward from the base cases, the caller
/// must establish that, for any `i`, `is_le(i + 1, n) && f(i) ==> f(i
/// - n)`. `is_le(i + 1, n)` is just `i + 1 <= n`, but written in a
/// functional style so that it can be used where functional triggers
/// are required.
pub proof fn lemma_mod_induction_auto(n: int, x: int, f: spec_fn(int) -> bool)
    requires
        n > 0,
        mod_auto(n) ==> {
            &&& (forall|i: int| #[trigger] is_le(0, i) && i < n ==> f(i))
            &&& (forall|i: int| #[trigger] is_le(0, i) && f(i) ==> f(i + n))
            &&& (forall|i: int| #[trigger] is_le(i + 1, n) && f(i) ==> f(i - n))
        },
    ensures
        mod_auto(n),
        f(x),
{
    lemma_mod_auto(n);
    assert(forall|i: int| is_le(0, i) && #[trigger] f(i) ==> #[trigger] f(add1(i, n)));
    assert(forall|i: int| is_le(i + 1, n) && #[trigger] f(i) ==> #[trigger] f(sub1(i, n)));
    assert forall|i: int| 0 <= i < n implies #[trigger] f(i) by {
        assert(forall|i: int| is_le(0, i) && i < n ==> f(i));
        assert(is_le(0, i) && i < n);
    };
    lemma_mod_induction_forall(n, f);
    assert(f(x));
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate, proves the
/// predicate holds in certain base cases, and proves correctness of
/// inductive steps both upward and downward from the base cases. This
/// lemma invokes induction to establish that the predicate holds for
/// all integer values.
///
/// `f`: The integer predicate
///
/// `n`: Upper bound on the base cases. Specifically, the caller
/// establishes `f(i)` for every value `i` satisfying `is_le(0, i) &&
/// i < n`.
///
/// To prove inductive steps upward from the base cases, the caller
/// must establish that, for any `i`, `is_le(0, i) && f(i) ==> f(i +
/// n)`. `is_le(0, i)` is just `0 <= i`, but written in a functional
/// style so that it can be used where functional triggers are
/// required.
///
/// To prove inductive steps downward from the base cases, the caller
/// must establish that, for any `i`, `is_le(i + 1, n) && f(i) ==> f(i
/// - n)`. `is_le(i + 1, n)` is just `i + 1 <= n`, but written in a
/// functional style so that it can be used where functional triggers
/// are required.
pub proof fn lemma_mod_induction_auto_forall(n: int, f: spec_fn(int) -> bool)
    requires
        n > 0,
        mod_auto(n) ==> {
            &&& (forall|i: int| #[trigger] is_le(0, i) && i < n ==> f(i))
            &&& (forall|i: int| #[trigger] is_le(0, i) && f(i) ==> f(i + n))
            &&& (forall|i: int| #[trigger] is_le(i + 1, n) && f(i) ==> f(i - n))
        },
    ensures
        mod_auto(n),
        forall|i| #[trigger] f(i),
{
    assert(mod_auto(n)) by {
        lemma_mod_induction_auto(n, 0, f);
    }
    assert forall|i| #[trigger] f(i) by {
        lemma_mod_induction_auto(n, i, f);
    }
}

} // verus!
        }

        pub mod mul_internals {
            //! This file contains proofs related to multiplication. These are
            //! internal functions used within the math standard library.
            //!
            //! It's based on the following file from the Dafny math standard library:
            //! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Internal/MulInternals.dfy`.
            //! That file has the following copyright notice:
            //! /*******************************************************************************
            //! *  Original: Copyright (c) Microsoft Corporation
            //! *  SPDX-License-Identifier: MIT
            //! *
            //! *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
            //! *  SPDX-License-Identifier: MIT
            //! *******************************************************************************/
            #[allow(unused_imports)]
            use builtin::*;
            use builtin_macros::*;

            #[cfg(verus_keep_ghost)]
            use crate::arithmetic::internals::general_internals::{is_le, lemma_induction_helper};
            use crate::arithmetic::internals::mul_internals_nonlinear as MulINL;
            #[cfg(verus_keep_ghost)]
            use crate::math::{add as add1, sub as sub1};

            verus! {

/// This function performs multiplication recursively. It's only valid
/// when `x` is non-negative.
#[verifier(opaque)]
pub open spec fn mul_pos(x: int, y: int) -> int
    recommends
        x >= 0,
    decreases x,
{
    if x <= 0 {
        0
    } else {
        y + mul_pos(x - 1, y)
    }
}

/// This function performs multiplication recursively.
pub open spec fn mul_recursive(x: int, y: int) -> int {
    if x >= 0 {
        mul_pos(x, y)
    } else {
        -1 * mul_pos(-1 * x, y)
    }
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate, proves the
/// predicate holds in the base case of 0, and proves correctness of
/// inductive steps both upward and downward from the base case. This
/// lemma invokes induction to establish that the predicate holds for
/// all integers.
///
/// To prove inductive steps upward from the base case, the caller
/// must establish that, for any `i >= 0`, `f(i) ==> f(add1(i, 1))`.
/// `add1(i, 1)` is just `i + 1`, but written in a functional style
/// so that it can be used where functional triggers are required.
///
/// To prove inductive steps downward from the base case, the caller
/// must establish that, for any `i <= 0`, `f(i) ==> f(sub1(i, 1))`.
/// `sub1(i, 1)` is just `i - 1`, but written in a functional style
/// so that it can be used where functional triggers are required.
pub proof fn lemma_mul_induction(f: spec_fn(int) -> bool)
    requires
        f(0),
        forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, 1)),
        forall|i: int| i <= 0 && #[trigger] f(i) ==> #[trigger] f(sub1(i, 1)),
    ensures
        forall|i: int| #[trigger] f(i),
{
    assert forall|i: int| #[trigger] f(i) by { lemma_induction_helper(1, f, i) };
}

/// Proof that multiplication is always commutative
proof fn lemma_mul_commutes()
    ensures
        forall|x: int, y: int| #[trigger] (x * y) == y * x,
{
}

/// Proof that multiplication distributes over addition by 1 and
/// over subtraction by 1
proof fn lemma_mul_successor()
    ensures
        forall|x: int, y: int| #[trigger] ((x + 1) * y) == x * y + y,
        forall|x: int, y: int| #[trigger] ((x - 1) * y) == x * y - y,
{
    assert forall|x: int, y: int| #[trigger] ((x + 1) * y) == x * y + y by {
        MulINL::lemma_mul_is_distributive_add(y, x, 1);
    }
    assert forall|x: int, y: int| #[trigger] ((x - 1) * y) == x * y - y by {
        assert((x - 1) * y == y * (x - 1));
        MulINL::lemma_mul_is_distributive_add(y, x, -1);
        assert(y * (x - 1) == y * x + y * -1);
        assert(-1 * y == -y);
        assert(x * y + (-1 * y) == x * y - y);
    }
}

/// Proof that multiplication distributes over addition and over
/// subtraction
#[verifier(spinoff_prover)]
proof fn lemma_mul_distributes()
    ensures
        forall|x: int, y: int, z: int| #[trigger] ((x + y) * z) == (x * z + y * z),
        forall|x: int, y: int, z: int| #[trigger] ((x - y) * z) == (x * z - y * z),
{
    lemma_mul_successor();
    assert forall|x: int, y: int, z: int| #[trigger] ((x + y) * z) == (x * z + y * z) by {
        let f1 = |i: int| ((x + i) * z) == (x * z + i * z);
        assert(f1(0));
        assert forall|i: int| i >= 0 && #[trigger] f1(i) implies #[trigger] f1(add1(i, 1)) by {
            assert((x + (i + 1)) * z == ((x + i) + 1) * z == (x + i) * z + z);
        };
        assert forall|i: int| i <= 0 && #[trigger] f1(i) implies #[trigger] f1(sub1(i, 1)) by {
            assert((x + (i - 1)) * z == ((x + i) - 1) * z == (x + i) * z - z);
        };
        lemma_mul_induction(f1);
        assert(f1(y));
    }
    assert forall|x: int, y: int, z: int| #[trigger] ((x - y) * z) == (x * z - y * z) by {
        let f2 = |i: int| ((x - i) * z) == (x * z - i * z);
        assert(f2(0));
        assert forall|i: int| i >= 0 && #[trigger] f2(i) implies #[trigger] f2(add1(i, 1)) by {
            assert((x - (i + 1)) * z == ((x - i) - 1) * z == (x - i) * z - z);
        };
        assert forall|i: int| i <= 0 && #[trigger] f2(i) implies #[trigger] f2(sub1(i, 1)) by {
            assert((x - (i - 1)) * z == ((x - i) + 1) * z == (x - i) * z + z);
        };
        lemma_mul_induction(f2);
        assert(f2(y));
    }
}

/// This function expresses that multiplication is commutative,
/// distributes over addition, and distributes over subtraction
pub open spec fn mul_auto() -> bool {
    &&& forall|x: int, y: int| #[trigger] (x * y) == (y * x)
    &&& forall|x: int, y: int, z: int| #[trigger] ((x + y) * z) == (x * z + y * z)
    &&& forall|x: int, y: int, z: int| #[trigger] ((x - y) * z) == (x * z - y * z)
}

/// Proof that multiplication is commutative, distributes over
/// addition, and distributes over subtraction
pub proof fn lemma_mul_auto()
    ensures
        mul_auto(),
{
    lemma_mul_commutes();
    lemma_mul_distributes();
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate `f`, proves
/// the predicate holds in the base case of 0, and proves correctness
/// of inductive steps both upward and downward from the base case.
/// This lemma invokes induction to establish that the predicate holds
/// for the given integer `x`.
///
/// To prove inductive steps upward from the base case, the caller
/// must establish that, for any `i`, `is_le(0, i)` implies `f(i) ==>
/// f(i + 1)`.
///
/// To prove inductive steps downward from the base case, the caller
/// must establish that, for any `i`, `is_le(i, 0)` implies `f(i) ==>
/// f(i - 1)`.
pub proof fn lemma_mul_induction_auto(x: int, f: spec_fn(int) -> bool)
    requires
        mul_auto() ==> {
            &&& f(0)
            &&& (forall|i| #[trigger] is_le(0, i) && f(i) ==> f(i + 1))
            &&& (forall|i| #[trigger] is_le(i, 0) && f(i) ==> f(i - 1))
        },
    ensures
        mul_auto(),
        f(x),
{
    lemma_mul_auto();
    assert(forall|i| is_le(0, i) && #[trigger] f(i) ==> f(i + 1));
    assert(forall|i| is_le(i, 0) && #[trigger] f(i) ==> f(i - 1));
    lemma_mul_induction(f);
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate `f`, proves
/// the predicate holds in the base case of 0, and proves correctness
/// of inductive steps both upward and downward from the base case.
/// This lemma invokes induction to establish that the predicate holds
/// for all integers.
///
/// To prove inductive steps upward from the base case, the caller
/// must establish that, for any `i`, `is_le(0, i)` implies `f(i) ==>
/// f(i + 1)`.
///
/// To prove inductive steps downward from the base case, the caller
/// must establish that, for any `i`, `is_le(i, 0)` implies `f(i) ==>
/// f(i - 1)`.
pub proof fn lemma_mul_induction_auto_forall(f: spec_fn(int) -> bool)
    requires
        mul_auto() ==> {
            &&& f(0)
            &&& (forall|i| #[trigger] is_le(0, i) && f(i) ==> f(i + 1))
            &&& (forall|i| #[trigger] is_le(i, 0) && f(i) ==> f(i - 1))
        },
    ensures
        mul_auto(),
        forall|i| #[trigger] f(i),
{
    assert(mul_auto()) by {
        lemma_mul_induction_auto(0, f);
    }
    assert forall|i| #[trigger] f(i) by {
        lemma_mul_induction_auto(i, f);
    }
}

} // verus!
        }
    }

    pub mod div_mod {
        //! This file contains proofs related to integer division (`/`) and
        //! remainder aka mod (`%`). These are part of the math standard library.
        //!
        //! It's based on the following file from the Dafny math standard
        //! library:
        //! `Source/DafnyStandardLibraries/src/Std/Arithmetic/DivMod.dfy`.
        //! That file has the following copyright notice:
        //! /*******************************************************************************
        //! * Original: Copyright (c) Microsoft Corporation *
        //! SPDX-License-Identifier: MIT * * Modifications and Extensions:
        //! Copyright by the contributors to the Dafny Project *
        //! SPDX-License-Identifier: MIT
        //! *******************************************************************************/
        use crate::calc_macro::*;
        #[allow(unused_imports)]
        use builtin::*;
        use builtin_macros::*;

        verus! {

#[allow(unused_imports)]
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::div_internals::{
    div_recursive,
    lemma_div_induction_auto,
    div_auto,
    div_pos,
    lemma_div_auto,
};
use crate::arithmetic::internals::div_internals_nonlinear as DivINL;
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::mod_internals::{
    lemma_div_add_denominator,
    lemma_mod_auto,
    mod_recursive,
};
use crate::arithmetic::internals::mod_internals_nonlinear as ModINL;
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::mul_internals::{
    lemma_mul_auto,
    lemma_mul_induction,
    lemma_mul_induction_auto,
};
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::general_internals::{is_le};
#[cfg(verus_keep_ghost)]
use crate::math::{add as add1, sub as sub1, div as div1};
use crate::arithmetic::mul::*;

/*****************************************************************************
* Division
*****************************************************************************/

/// Proof that, for the case of `x / d`, division using `/` is
/// equivalent to a recursive definition of division
pub proof fn lemma_div_is_div_recursive(x: int, d: int)
    requires
        0 < d,
    ensures
        div_recursive(x, d) == x / d,
{
    reveal(div_recursive);
    reveal(div_pos);
    lemma_div_induction_auto(d, x, |u: int| div_recursive(u, d) == u / d);
}

/// Proof that division using `/` is equivalent to a recursive
/// definition of division as long as the divisor is positive
pub proof fn lemma_div_is_div_recursive_auto()
    ensures
        forall|x: int, d: int| d > 0 ==> div_recursive(x, d) == #[trigger] (x / d),
{
    reveal(div_recursive);
    assert forall|x: int, d: int| d > 0 implies div_recursive(x, d) == #[trigger] (x / d) by {
        lemma_div_is_div_recursive(x, d);
    }
}

/// Proof that the quotient of an integer divided by itself is 1,
/// specifically that `d / d == 1`
pub proof fn lemma_div_by_self(d: int)
    requires
        d != 0,
    ensures
        d / d == 1,
{
    DivINL::lemma_div_by_self(d);
}

/// Proof that 0 divided by a nonzero integer is 0, specifically `0 / d == 0`
pub proof fn lemma_div_of0(d: int)
    requires
        d != 0,
    ensures
        0 as int / d == 0,
{
    DivINL::lemma_div_of0(d);
}

/// Proof establishing basic properties of division using `x`: 0
/// divided by `x` is 0; `x` divided by 1 is itself; and `x` divided
/// by itself is 1.
pub proof fn lemma_div_basics(x: int)
    ensures
        x != 0 as int ==> 0 as int / x == 0,
        x / 1 == x,
        x != 0 ==> x / x == 1,
{
    if (x != 0) {
        lemma_div_by_self(x);
        lemma_div_of0(x);
    }
}

/// Proof establishing basic properties of division: 0 divided by any
/// integer is 0; any integer divided by 1 is itself; any integer
/// divided by itself is 1.
pub proof fn lemma_div_basics_auto()
    ensures
        forall|x: int| x != 0 ==> #[trigger] (0int / x) == 0,
        forall|x: int| #[trigger] (x / 1) == x,
        forall|x: int, y: int| x >= 0 && y > 0 ==> #[trigger] (x / y) >= 0,
        forall|x: int, y: int| x >= 0 && y > 0 ==> #[trigger] (x / y) <= x,
{
    assert forall|x: int| x != 0 implies #[trigger] (0int / x) / x == 0 by {
        lemma_div_basics(x);
    };
    assert forall|x: int| x != 0 implies #[trigger] (x / 1) == x by {
        lemma_div_basics(x);
    };
    assert forall|x: int, y: int| x >= 0 && y > 0 implies 0 <= #[trigger] (x / y) <= x by {
        lemma_div_pos_is_pos(x, y);
        lemma_div_is_ordered_by_denominator(x, 1, y);
    };
}

/// Proof that if a dividend is a whole number, the divisor is a
/// natural number, and their quotient is 0, then the dividend is
/// smaller than the divisor
pub proof fn lemma_small_div_converse_auto()
    ensures
        forall|x: int, d: int| 0 <= x && 0 < d && #[trigger] (x / d) == 0 ==> x < d,
{
    assert forall|x: int, d: int| 0 <= x && 0 < d && #[trigger] (x / d) == 0 implies x < d by {
        lemma_div_induction_auto(d, x, |u: int| 0 <= u && 0 < d && u / d == 0 ==> u < d);
    }
}

/// Proof that division of a positive integer by a positive integer
/// less than or equal to it is nonzero. Specifically, given that `x
/// >= d`, we can conclude that `x / d > 0`.
pub proof fn lemma_div_non_zero(x: int, d: int)
    requires
        x >= d > 0,
    ensures
        x / d > 0,
{
    lemma_div_pos_is_pos_auto();
    if x / d == 0 {
        lemma_small_div_converse_auto();
    }
}

/// Proof that division of a positive integer by a positive integer
/// less than or equal to it is nonzero
pub proof fn lemma_div_non_zero_auto()
    ensures
        forall|x: int, d: int| x >= d > 0 ==> #[trigger] (x / d) > 0,
{
    assert forall|x: int, d: int| x >= d > 0 implies #[trigger] (x / d) > 0 by {
        lemma_div_non_zero(x, d);
    }
}

/// Proof that given two fractions with the same numerator, the order
/// of the fractions is determined by the denominators. However, if
/// the numerator is 0, the fractions are equal regardless of the
/// denominators' values. Specifically, given that `1 <= y <= z`, we
/// know `x / y >= x / z`.
pub proof fn lemma_div_is_ordered_by_denominator(x: int, y: int, z: int)
    requires
        0 <= x,
        1 <= y <= z,
    ensures
        x / y >= x / z,
    decreases x,
{
    reveal(div_recursive);
    reveal(div_pos);
    lemma_div_is_div_recursive_auto();
    assert(forall|u: int, d: int|
        #![trigger div_recursive(u, d)]
        #![trigger div1(u, d)]
        d > 0 ==> div_recursive(u, d) == div1(u, d));
    if (x < z) {
        lemma_div_is_ordered(0, x, y);
    } else {
        lemma_div_is_ordered(x - z, x - y, y);
        lemma_div_is_ordered_by_denominator(x - z, y, z);
    }
}

/// Proof that given two fractions with the same numerator, the order
/// of the fractions is determined by the denominators. However, if
/// the numerator is 0, the fractions are equal regardless of the
/// denominators' values.
pub proof fn lemma_div_is_ordered_by_denominator_auto()
    ensures
        forall|x: int, y: int, z: int|
            0 <= x && 1 <= y <= z ==> #[trigger] (x / y) >= #[trigger] (x / z),
{
    assert forall|x: int, y: int, z: int| 0 <= x && 1 <= y <= z implies #[trigger] (x / y)
        >= #[trigger] (x / z) by {
        lemma_div_is_ordered_by_denominator(x, y, z);
    }
}

/// Proof that a number gets strictly smaller when divided by a number
/// greater than one. Specifically, `x / d < x`.
pub proof fn lemma_div_is_strictly_smaller(x: int, d: int)
    requires
        0 < x,
        1 < d,
    ensures
        x / d < x,
    decreases x,
{
    lemma_div_induction_auto(d, x, |u: int| 0 < u ==> u / d < u);
}

/// Proof that a number gets strictly smaller when divided by a number
/// greater than one
pub proof fn lemma_div_is_strictly_smaller_auto()
    ensures
        forall|x: int, d: int| 0 < x && 1 < d ==> #[trigger] (x / d) < x,
{
    assert forall|x: int, d: int| 0 < x && 1 < d implies #[trigger] (x / d) < x by {
        lemma_div_is_strictly_smaller(x, d);
    }
}

/// Proof that, given `r == a % d + b % d - (a + b) % d`, `r` can also
/// be expressed as `d * ((a + b) / d) - d * (a / d) - d * (b / d)`
pub proof fn lemma_dividing_sums(a: int, b: int, d: int, r: int)
    requires
        0 < d,
        r == a % d + b % d - (a + b) % d,
    ensures
        d * ((a + b) / d) - r == d * (a / d) + d * (b / d),
{
    ModINL::lemma_fundamental_div_mod(a + b, d);
    ModINL::lemma_fundamental_div_mod(a, d);
    ModINL::lemma_fundamental_div_mod(b, d);
}

/// Proof that for any values of the following variables, `r == a % d
/// + b % d - (a + b) % d` implies `r == d * ((a + b) / d) - d * (a /
/// d) - d * (b / d)`
pub proof fn lemma_dividing_sums_auto()
    ensures
        forall|a: int, b: int, d: int, r: int|
            #![trigger (d * ((a + b) / d) - r), (d * (a / d) + d * (b / d))]
            0 < d && r == a % d + b % d - (a + b) % d ==> d * ((a + b) / d) - r == d * (a / d) + d
                * (b / d),
{
    assert forall|a: int, b: int, d: int, r: int|
        0 < d && r == a % d + b % d - (a + b) % d implies #[trigger] (d * ((a + b) / d) - r)
        == #[trigger] (d * (a / d) + d * (b / d)) by {
        lemma_dividing_sums(a, b, d, r);
    }
}

/// Proof that dividing a whole number by a natural number will result
/// in a quotient that is greater than or equal to 0. Specifically,
/// `x / d >= 0`.
pub proof fn lemma_div_pos_is_pos(x: int, d: int)
    requires
        0 <= x,
        0 < d,
    ensures
        0 <= x / d,
{
    lemma_div_auto(d);
    assert(div_auto(d));
    let f = |u: int| 0 <= u ==> u / d >= 0;
    assert forall|i: int| #[trigger] is_le(0, i) && f(i) implies f(i + d) by {
        assert(i / d >= 0);
    };
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u / d >= 0);
}

/// Proof that dividing a whole number by a natural number will result
/// in a quotient that is greater than or equal to 0
pub proof fn lemma_div_pos_is_pos_auto()
    ensures
        forall|x: int, d: int| 0 <= x && 0 < d ==> 0 <= #[trigger] (x / d),
{
    assert forall|x: int, d: int| 0 <= x && 0 < d implies 0 <= #[trigger] (x / d) by {
        lemma_div_pos_is_pos(x, d);
    }
}

/// Proof that dividing a number then adding 1 gives the same result
/// as adding the divisor and then doing the division. Specifically,
/// `1 + (x / d)` is equal to `(d + x) / d`.
pub proof fn lemma_div_plus_one(x: int, d: int)
    requires
        0 < d,
    ensures
        1 + x / d == (d + x) / d,
{
    lemma_div_auto(d);
}

/// Proof that dividing a number then adding 1 gives the same result
/// as adding the divisor and then doing the division
pub proof fn lemma_div_plus_one_auto()
    ensures
        forall|x: int, d: int|
            #![trigger (1 + x / d), ((d + x) / d)]
            0 < d ==> 1 + (x / d) == (d + x) / d,
{
    assert forall|x: int, d: int| 0 < d implies #[trigger] (1 + x / d) == #[trigger] ((d + x)
        / d) by {
        lemma_div_plus_one(x, d);
    }
}

/// Proof that dividing a number then subtracting 1 gives the same result
/// as subtracting the divisor and then doing the division. Specifically,
/// `-1 + (x / d)` is equal to `(-d + x) / d`.
pub proof fn lemma_div_minus_one(x: int, d: int)
    requires
        0 < d,
    ensures
        -1 + x / d == (-d + x) / d,
{
    lemma_div_auto(d);
}

/// Proof that dividing a number then subtracting 1 gives the same result
/// as subtracting the divisor and then doing the division
pub proof fn lemma_div_minus_one_auto()
    ensures
        forall|x: int, d: int|
            #![trigger (-1 + x / d), ((-d + x) / d)]
            0 < d ==> -1 + x / d == (-d + x) / d,
{
    assert forall|x: int, d: int| 0 < d implies #[trigger] (-1 + x / d) == #[trigger] ((-d + x)
        / d) by {
        lemma_div_minus_one(x, d);
    }
}

/// Proof that dividing any non-negative integer less than `d` by `d`
/// produces a quotient of 0
pub proof fn lemma_basic_div(d: int)
    requires
        0 < d,
    ensures
        forall|x: int| 0 <= x < d ==> #[trigger] (x / d) == 0,
{
    lemma_div_auto(d);
}

/// Proof that dividing any non-negative integer by a larger integer
/// produces a quotient of 0
pub proof fn lemma_basic_div_auto()
    ensures
        forall|x: int, d: int| 0 <= x < d ==> #[trigger] (x / d) == 0,
{
    assert forall|x: int, d: int| 0 <= x < d implies #[trigger] (x / d) == 0 by {
        lemma_basic_div(d);
    }
}

/// Proof that numerical order is preserved when dividing two seperate
/// integers by a common positive divisor. Specifically, given that
/// `z > 0` and `x <= y`, we know `x / z <= y / z`.
pub proof fn lemma_div_is_ordered(x: int, y: int, z: int)
    requires
        x <= y,
        0 < z,
    ensures
        x / z <= y / z,
{
    lemma_div_auto(z);
    let f = |xy: int| xy <= 0 ==> (xy + y) / z <= y / z;
    assert forall|i: int| #[trigger] is_le(i + 1, z) && f(i) implies f(i - z) by {
        if (i - z <= 0) {
            assert(f(i));
            assert(i <= 0 ==> (i + y) / z <= y / z);
            if (i > 0) {
                assert(z > 0);
                assert(i <= z);
                assert(((i + y) - z) / z <= y / z);
            } else {
                assert((i + y) / z <= y / z);
            }
            assert((i - z + y) / z <= y / z);
        }
    };
    lemma_div_induction_auto(z, x - y, |xy: int| xy <= 0 ==> (xy + y) / z <= y / z);
}

/// Proof that numerical order is preserved when dividing two seperate
/// integers by a common positive divisor
pub proof fn lemma_div_is_ordered_auto()
    ensures
        forall|x: int, y: int, z: int| x <= y && 0 < z ==> #[trigger] (x / z) <= #[trigger] (y / z),
{
    assert forall|x: int, y: int, z: int| x <= y && 0 < z implies #[trigger] (x / z) <= #[trigger] (
    y / z) by {
        lemma_div_is_ordered(x, y, z);
    }
}

/// Proof that dividing an integer by 2 or more results in a quotient
/// that is smaller than the original dividend. Specifically, `x / d < x`.
pub proof fn lemma_div_decreases(x: int, d: int)
    requires
        0 < x,
        1 < d,
    ensures
        x / d < x,
{
    lemma_div_induction_auto(d, x, |u: int| 0 < u ==> u / d < u);
}

/// Proof that dividing an integer by 2 or more results in a quotient
/// that is smaller than the original dividend
pub proof fn lemma_div_decreases_auto()
    ensures
        forall|x: int, d: int| 0 < x && 1 < d ==> #[trigger] (x / d) < x,
{
    assert forall|x: int, d: int| 0 < x && 1 < d implies #[trigger] (x / d) < x by {
        lemma_div_decreases(x, d);
    };
}

/// Proof that dividing an integer by 1 or more results in a quotient
/// that is less than or equal to the original dividend. Specifically,
/// `x / d <= x`.
pub proof fn lemma_div_nonincreasing(x: int, d: int)
    requires
        0 <= x,
        0 < d,
    ensures
        x / d <= x,
{
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u / d <= u);
}

/// Proof that dividing an integer by 1 or more results in a quotient
/// that is less than or equal to the original dividend
proof fn lemma_div_nonincreasing_auto()
    ensures
        forall|x: int, d: int| 0 <= x && 0 < d ==> #[trigger] (x / d) <= x,
{
    assert forall|x: int, d: int| 0 <= x && 0 < d implies #[trigger] (x / d) <= x by {
        lemma_div_nonincreasing(x, d);
    }
}

/// Proof that a natural number x divided by a larger natural number
/// gives a remainder equal to x. Specifically, because `x < m`, we
/// know `x % m == x`.
pub proof fn lemma_small_mod(x: nat, m: nat)
    requires
        x < m,
        0 < m,
    ensures
        x % m == x,
{
    ModINL::lemma_small_mod(x, m);
}

/// The remainder of a nonnegative integer `x` divided by the product of two positive integers
/// `y` and `z` is equivalent to dividing `x` by `y`, dividing the quotient by `z`, multiplying
/// the remainder by `y`, and then adding the product to the remainder of `x` divided by `y`.
/// In mathematical terms, `(x % (y * z)) == y * ((x / y) % z) + x % y`.
pub proof fn lemma_breakdown(x: int, y: int, z: int)
    requires
        0 <= x,
        0 < y,
        0 < z,
    ensures
        0 < y * z,
        (x % (y * z)) == y * ((x / y) % z) + x % y,
{
    lemma_mul_strictly_positive_auto();
    lemma_div_pos_is_pos(x, y);
    calc! {
        (<)
        (y * (x / y)) % (y * z) + (x % y) % (y * z);
        (<=)    { lemma_part_bound1(x, y, z); }
        y * (z - 1) + (x % y) % (y * z);
        (<)    { lemma_part_bound2(x, y, z); }
        y * (z - 1) + y;
        (==)    { lemma_mul_basics_auto(); }
        y * (z - 1) + y * 1;
        (==)    { lemma_mul_is_distributive_auto(); }
        y * (z - 1 + 1);
        (==) {}
        y * z;
    }
    calc! {
        (==)
        x % (y * z);
        { ModINL::lemma_fundamental_div_mod(x,y); }
        (y * (x / y) + x % y) % (y * z);
        {
            lemma_mod_properties_auto();
            assert(0 <= x % y);
            lemma_mul_nonnegative(y, x / y);
            assert((y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z);
            lemma_mod_adds(y * (x / y), x % y, y * z);
        }
        (y * (x / y)) % (y * z) + (x % y) % (y * z);
        {
            lemma_mod_properties_auto();
            lemma_mul_increases(z, y);
            lemma_mul_is_commutative_auto();
            // comparison op can't be chained in calc!
            // assert forall is also not avaialable in calc!
            assert((x % y) < y && y <= (y * z));
            lemma_small_mod((x % y) as nat, (y * z) as nat);
            assert((x % y) % (y * z) == x % y);
        }
        (y * (x / y)) % (y * z) + x % y;
        { lemma_truncate_middle(x / y, y, z); }
        y * ((x / y) % z) + x % y;
    }
}

/// Proof that, for all `x`, `y`, and `z`, `(x % (y * z)) == y * ((x / y) % z) + x % y`
pub proof fn lemma_breakdown_auto()
    ensures
        forall|y: int, z: int| #![trigger y * z] 0 < y && 0 < z ==> 0 < y * z,
        forall|x: int, y: int, z: int|
            #![trigger y * z, x % (y * z), y * ((x / y) % z) + x % y]
            0 <= x && 0 < y && 0 < z ==> x % (y * z) == y * ((x / y) % z) + x % y,
{
    assert forall|y: int, z: int| #![trigger y * z] 0 < y && 0 < z implies 0 < y * z by {
        lemma_mul_strictly_positive_auto();
    }
    assert forall|x: int, y: int, z: int|
        #![trigger y * z, x % (y * z), y * ((x / y) % z) + x % y]
        0 <= x && 0 < y && 0 < z implies x % (y * z) == y * ((x / y) % z) + x % y by {
        lemma_breakdown(x, y, z);
    }
}

/// Proof that the difference between a nonnegative integer `x` and a
/// positive integer `d` must be strictly less than the quotient of
/// `x` divided by `d` and then multiplied by `d`
pub proof fn lemma_remainder_upper(x: int, d: int)
    requires
        0 <= x,
        0 < d,
    ensures
        x - d < x / d * d,
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u - d < u / d * d);
}

/// Proof that for any nonnegative integer `x` and positive integer
/// `d`, their difference `x - d` must be strictly less than the
/// quotient of `x` divided by `d` and then multiplied by `d`
pub proof fn lemma_remainder_upper_auto()
    ensures
        forall|x: int, d: int|
            #![trigger (x - d), (x / d * d)]
            0 <= x && 0 < d ==> (x - d) < (x / d * d),
{
    assert forall|x: int, d: int| 0 <= x && 0 < d implies #[trigger] (x - d) < #[trigger] (x / d
        * d) by {
        lemma_remainder_upper(x, d);
    }
}

/// Proof that the division of a nonnegative integer `x` by a positive
/// integer `d` multiplied by `d` is less than or equal to the value
/// of `x`
pub proof fn lemma_remainder_lower(x: int, d: int)
    requires
        0 <= x,
        0 < d,
    ensures
        x >= x / d * d,
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, x, |u: int| 0 <= u ==> u >= u / d * d);
}

/// Proof that, for all nonnegative `x` and positive `d`, `(x / d) * d <= x`
pub proof fn lemma_remainder_lower_auto()
    ensures
        forall|x: int, d: int| 0 <= x && 0 < d ==> x >= #[trigger] (x / d * d),
{
    assert forall|x: int, d: int| (0 <= x && 0 < d) implies x >= #[trigger] (x / d * d) by {
        lemma_remainder_lower(x, d);
    }
}

/// Proof that the difference between a nonnegative integer `x` and
/// the division of `x` by a positive integer `d` multiplied by `d` is
/// lower bounded (inclusively) by 0 and upper bounded (exclusively)
/// by `d
pub proof fn lemma_remainder(x: int, d: int)
    requires
        0 <= x,
        0 < d,
    ensures
        0 <= x - (x / d * d) < d,
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, x, |u: int| 0 <= u - u / d * d < d);
}

/// Proof that, for any nonnegative integer `x` and positive `d`,
/// `0 <= (x - (x / d * d)) < d`
pub proof fn lemma_remainder_auto()
    ensures
        forall|x: int, d: int| 0 <= x && 0 < d ==> 0 <= #[trigger] (x - (x / d * d)) < d,
{
    assert forall|x: int, d: int| 0 <= x && 0 < d implies 0 <= #[trigger] (x - (x / d * d)) < d by {
        lemma_remainder(x, d);
    }
}

/// Proof of the fundamental theorem of division and modulo, namely
/// that `x` can be expressed as `d` times the quotient `x / d` plus
/// the remainder `x % d`.
pub proof fn lemma_fundamental_div_mod(x: int, d: int)
    requires
        d != 0,
    ensures
        x == d * (x / d) + (x % d),
{
    assert(x == d * (x / d) + (x % d)) by {
        ModINL::lemma_fundamental_div_mod(x, d);
    }
}

/// Proof of the fundamental theorem of division and modulo, namely
/// that for any `x` and nonzero `d`, `x == d * (x / d) + x % d`
pub proof fn lemma_fundamental_div_mod_auto()
    ensures
        forall|x: int, d: int| d != 0 ==> x == #[trigger] (d * (x / d) + (x % d)),
{
    assert forall|x: int, d: int| d != 0 implies x == #[trigger] (d * (x / d) + (x % d)) by {
        lemma_fundamental_div_mod(x, d);
    }
}

/// Proof that dividing `x` by `c * d` is equivalent to first dividing
/// `x` by `c` and then dividing the result by `d`
pub proof fn lemma_div_denominator(x: int, c: int, d: int)
    requires
        0 <= x,
        0 < c,
        0 < d,
    ensures
        c * d != 0,
        (x / c) / d == x / (c * d),
{
    lemma_mul_strictly_positive(c, d);
    let r = x % (c as int * d as int);
    lemma_div_pos_is_pos(r, c as int);
    if (r / c as int >= d) {
        ModINL::lemma_fundamental_div_mod(r, c as int);
        lemma_mul_inequality(d as int, r / c as int, c as int);
        lemma_mul_is_commutative(d, c);
    }
    assert(r / (c as int) < d);
    lemma_fundamental_div_mod_converse(r / c, d, 0, r / c);
    assert((r / c as int) % d as int == r / c as int);
    lemma_fundamental_div_mod(r, c);
    assert(c * (r / c) + r % c == r);
    assert(c * ((r / c as int) % d as int) + r % c as int == r);
    let k = x / (c as int * d as int);
    lemma_fundamental_div_mod(x, c * d);
    assert(x == (c * d) * (x / (c * d)) + x % (c * d));
    assert(r == x - (c * d) * (x / (c * d)));
    assert(r == x - (c * d) * k);
    calc! {
        (==)
        c * ((x / c) % d) + x % c;
        {
            lemma_mod_multiples_vanish(-k, x / c, d);
            lemma_mul_is_commutative_auto();
        }
        c * ((x / c + (-k) * d) % d) + x % c;
        { lemma_hoist_over_denominator(x, (-k) * d, c as nat); }
        c * (((x + (((-k) * d) * c)) / c) % d) + x % c;
        { lemma_mul_is_associative(-k, d, c); }
        c * (((x + ((-k) * (d * c))) / c) % d) + x % c;
        { lemma_mul_unary_negation(k, d * c); }
        c * (((x + (-(k * (d * c)))) / c) % d) + x % c;
        { lemma_mul_is_associative(k, d, c); }
        c * (((x + (-(k * d * c))) / c) % d) + x % c;
        { }
        c * (((x - k * d * c) / c) % d) + x % c;
        {
            lemma_mul_is_associative_auto();
            lemma_mul_is_commutative_auto();
        }
        c * ((r / c) % d) + x % c;
        { }
        c * (r / c) + x % c;
        {
            lemma_fundamental_div_mod(r, c);
            assert(r == c * (r / c) + r % c);
            lemma_mod_mod(x, c, d);
            assert(r % c == x % c);
        }
        r;
        { lemma_mod_properties_auto(); lemma_mod_is_mod_recursive_auto(); }
        r % (c * d);
        { }
        (x - (c * d) * k) % (c * d);
        { lemma_mul_unary_negation(c * d, k); }
        (x + (c * d) * (-k)) % (c * d);
        { lemma_mod_multiples_vanish(-k, x, c * d); }
        x % (c * d);
    }
    assert(c * (x / c) + x % c - r == c * (x / c) - c * ((x / c) % d) ==> x - r == c * (x / c) - c
        * ((x / c) % d)) by {
        lemma_fundamental_div_mod(x, c);
    };
    assert(c * (x / c) + x % c - r == c * (x / c) - c * ((x / c) % d));
    assert(x - r == c * (x / c) - c * ((x / c) % d));
    assert((x / c) / d == x / (c * d)) by {
        lemma_fundamental_div_mod(x / c, d);
        assert(d * ((x / c) / d) == x / c - ((x / c) % d));
        lemma_fundamental_div_mod(x, c * d);
        assert(x == (c * d) * (x / (c * d)) + (x % (c * d)));
        lemma_mul_is_distributive_sub(c, x / c, (x / c) % d);
        assert(c * (d * ((x / c) / d)) == c * (x / c) - c * ((x / c) % d));
        lemma_mul_is_associative(c, d, (x / c) / d);
        assert((c * d) * ((x / c) / d) == c * (x / c) - c * ((x / c) % d));
        assert((c * d) * ((x / c) / d) == x - r);
        assert((c * d) * ((x / c) / d) == (c * d) * (x / (c * d)));
        lemma_mul_equality_converse(c * d, (x / c) / d, x / (c * d));
    }
    assert(c * d != 0) by {
        assert(0 < c * d);
    }
}

/// Proof that dividing a fraction by a divisor is equivalent to
/// multiplying the fraction's denominator by the divisor
pub proof fn lemma_div_denominator_auto()
    ensures
        forall|c: int, d: int| 0 < c && 0 < d ==> #[trigger] (c * d) != 0,
        forall|x: int, c: int, d: int|
            0 <= x && 0 < c && 0 < d ==> #[trigger] ((x / c) / d) == x / (c * d),
{
    lemma_mul_nonzero_auto();
    assert forall|x: int, c: int, d: int| 0 <= x && 0 < c && 0 < d implies #[trigger] ((x / c) / d)
        == x / (c * d) by {
        lemma_div_denominator(x, c, d);
    }
}

/// Proof that multiplying an integer by a fraction is equivalent to
/// multiplying the fraction's numerator by the integer. Specifically,
/// `x * (y / z) == (x * y) / z`.
pub proof fn lemma_mul_hoist_inequality(x: int, y: int, z: int)
    requires
        0 <= x,
        0 < z,
    ensures
        x * (y / z) <= (x * y) / z,
{
    calc! {
    (==)
    (x * y) / z;
    (==)   { lemma_fundamental_div_mod(y, z); }
    (x * (z * (y / z) + y % z)) / z;
    (==)    { lemma_mul_is_distributive_auto(); }
    (x * (z * (y / z)) + x * (y % z)) / z;
    }
    assert((x * (z * (y / z)) + x * (y % z)) / z >= x * (y / z)) by {
        lemma_mod_properties_auto();
        lemma_mul_nonnegative(x, y % z);
        lemma_div_is_ordered(x * (z * (y / z)), x * (z * (y / z)) + x * (y % z), z);
        lemma_mul_is_associative_auto();
        lemma_mul_is_commutative_auto();
        lemma_div_multiples_vanish(x * (y / z), z);
    };
}

/// Proof that multiplying an integer by a fraction is equivalent to
/// multiplying the fraction's numerator by the integer
pub proof fn lemma_mul_hoist_inequality_auto()
    ensures
        forall|x: int, y: int, z: int|
            #![trigger (x * (y / z)), ((x * y) / z)]
            0 <= x && 0 < z ==> (x * (y / z)) <= ((x * y) / z),
{
    assert forall|x: int, y: int, z: int| 0 <= x && 0 < z implies #[trigger] (x * (y / z))
        <= #[trigger] ((x * y) / z) by {
        lemma_mul_hoist_inequality(x, y, z);
    }
}

/// Proof that for a positive integer `d`, if `a - a % d` is less than
/// or equal to `b` and `b` is less than `a + d - a % d`, then the
/// quotient of `a` divided by `d` is equivalent to the quotient of
/// `b` divided by `d`.
///
/// In other words, if `a` and `b` occur between the same two
/// multiples of `d`, then their quotient with `d` is equivalent.
pub proof fn lemma_indistinguishable_quotients(a: int, b: int, d: int)
    requires
        0 < d,
        0 <= a - a % d <= b < a + d - a % d,
    ensures
        a / d == b / d,
{
    lemma_div_induction_auto(
        d,
        a - b,
        |ab: int|
            {
                let u = ab + b;
                0 <= u - u % d <= b < u + d - u % d ==> u / d == b / d
            },
    );
}

/// Proof that for any `a`, `b`, and positive integer `d`, if `a - a %
/// d` is less than or equal to `b` and `b` is less than `a + d - a %
/// d`, then the quotient of `a` divided by `d` is equivalent to the
/// quotient of `b` divided by `d`.
///
/// In other words, if `a` and `b` occur between the same two
/// multiples of `d`, then their quotient with `d` is equivalent.
pub proof fn lemma_indistinguishable_quotients_auto()
    ensures
        forall|a: int, b: int, d: int|
            #![trigger (a / d), (b / d)]
            0 < d && 0 <= a - a % d <= b < a + d - a % d ==> (a / d) == (b / d),
{
    assert forall|a: int, b: int, d: int|
        0 < d && 0 <= a - a % d <= b < a + d - a % d implies #[trigger] (a / d) == #[trigger] (b
        / d) by {
        lemma_indistinguishable_quotients(a, b, d);
    }
}

/// Proof that common factors from the dividend and divisor of a
/// modulus operation can be factored out. Specifically,
/// `(b * x) % (b * c) == b * (x % c)`.
pub proof fn lemma_truncate_middle(x: int, b: int, c: int)
    requires
        0 <= x,
        0 < b,
        0 < c,
    ensures
        0 < b * c,
        (b * x) % (b * c) == b * (x % c),
{
    lemma_mul_strictly_positive_auto();
    lemma_mul_nonnegative_auto();
    calc! {
    (==)
    b * x;
    { ModINL::lemma_fundamental_div_mod(b * x, b * c); }
    (b * c) * ((b * x) / (b * c)) + (b * x) % (b * c);
    { lemma_div_denominator(b * x, b, c); }
    (b * c) * (((b * x) / b) / c) + (b * x) % (b * c);
    { lemma_mul_is_commutative_auto(); lemma_div_by_multiple(x, b); }
    (b * c) * (x / c) + (b * x) % (b * c);
    }
    assert(b * x == (b * c) * (x / c) + b * (x % c)) by {
        ModINL::lemma_fundamental_div_mod(x, c);
        lemma_mul_is_distributive_auto();
        lemma_mul_is_associative_auto();
    };
}

/// Proof that common factors from the dividend and divisor of a
/// modulus operation can be factored out
pub proof fn lemma_truncate_middle_auto()
    ensures
        forall|x: int, b: int, c: int|
            #![trigger (b * (x % c))]
            0 <= x && 0 < b && 0 < c && 0 < b * c ==> (b * x) % (b * c) == b * (x % c),
{
    assert forall|x: int, b: int, c: int| 0 <= x && 0 < b && 0 < c && 0 < b * c implies #[trigger] (
    b * (x % c)) == ((b * x) % (b * c)) by {
        lemma_truncate_middle(x, b, c);
    }
}

/// Proof that multiplying the numerator and denominator by an integer
/// does not change the quotient. Specifically,
/// `a / d == (x * a) / (x * d)`.
pub proof fn lemma_div_multiples_vanish_quotient(x: int, a: int, d: int)
    requires
        0 < x,
        0 <= a,
        0 < d,
    ensures
        0 < x * d,
        a / d == (x * a) / (x * d),
{
    lemma_mul_strictly_positive(x, d);
    calc! { (==)
        (x * a) / (x * d);
        {
            lemma_mul_nonnegative(x, a);
            lemma_div_denominator(x * a, x, d);
        }
        ((x * a) / x) / d;
        { lemma_div_multiples_vanish(a, x); }
        a / d;
    }
}

/// Proof that multiplying the numerator and denominator by an integer
/// does not change the quotient
pub proof fn lemma_div_multiples_vanish_quotient_auto()
    ensures
        forall|x: int, d: int| #![trigger x * d] 0 < x && 0 < d ==> 0 < x * d,
        forall|x: int, a: int, d: int|
            #![trigger a / d, x * a, x * d]
            0 < x && 0 <= a && 0 < d ==> a / d == (x * a) / (x * d),
{
    assert forall|x: int, d: int| #![trigger x * d] 0 < x && 0 < d implies 0 < x * d by {
        lemma_mul_strictly_positive_auto();
    }
    assert forall|x: int, a: int, d: int|
        #![trigger a / d, x * a, x * d]
        0 < x && 0 <= a && 0 < d implies a / d == (x * a) / (x * d) by {
        lemma_div_multiples_vanish_quotient(x, a, d);
    }
}

/// Proof that, since `a % d == 0` and `0 <= r < d`, we can conclude
/// `a == d * (a + r) / d`
pub proof fn lemma_round_down(a: int, r: int, d: int)
    requires
        0 < d,
        a % d == 0,
        0 <= r < d,
    ensures
        a == d * ((a + r) / d),
{
    lemma_mul_auto();
    lemma_div_induction_auto(d, a, |u: int| u % d == 0 ==> u == d * ((u + r) / d));
}

/// Proof that for all `a`, `d`, and `r`, if `a % d == 0` and `0 <= r
/// < d`, then `a == d * (a + r) / d`
pub proof fn lemma_round_down_auto()
    ensures
        forall|a: int, r: int, d: int|
            #![trigger (d * ((a + r) / d))]
            0 < d && a % d == 0 && 0 <= r < d ==> a == d * ((a + r) / d),
{
    assert forall|a: int, r: int, d: int| 0 < d && a % d == 0 && 0 <= r < d implies #[trigger] (d
        * ((a + r) / d)) == a by {
        lemma_round_down(a, r, d);
    }
}

/// Proof that, since `0 <= b < d`, we have `(d * x + b) / d == x`
pub proof fn lemma_div_multiples_vanish_fancy(x: int, b: int, d: int)
    requires
        0 < d,
        0 <= b < d,
    ensures
        (d * x + b) / d == x,
{
    let f = |u: int| (d * u + b) / d == u;
    assert(f(0)) by {
        lemma_div_auto(d);
    }
    assert forall|i: int| i >= 0 && #[trigger] f(i) implies #[trigger] f(add1(i, 1)) by {
        assert(d * (i + 1) + b == d * i + b + d) by {
            assert(d * (i + 1) == d * i + d) by {
                lemma_mul_is_distributive_add(d, i, 1);
                lemma_mul_basics(d);
            }
        }
        crate::arithmetic::internals::div_internals::lemma_div_basics(d);
    }
    assert forall|i: int| i <= 0 && #[trigger] f(i) implies #[trigger] f(sub1(i, 1)) by {
        assert(d * (i - 1) + b == d * i + b - d) by {
            assert(d * (i - 1) == d * i - d) by {
                lemma_mul_is_distributive_sub(d, i, 1);
                lemma_mul_basics(d);
            }
        }
        crate::arithmetic::internals::div_internals::lemma_div_basics(d);
    }
    lemma_mul_auto();
    lemma_mul_induction(f);
    assert(f(x));
}

/// Proof that, for any `x`, `b`, and `d` satisfying `0 <= b < d`, we
/// have `(d * x + b) / d == x`
pub proof fn lemma_div_multiples_vanish_fancy_auto()
    ensures
        forall|x: int, b: int, d: int|
            #![trigger (d * x + b) / d]
            0 < d && 0 <= b < d ==> (d * x + b) / d == x,
{
    assert forall|x: int, b: int, d: int| 0 < d && 0 <= b < d implies #[trigger] ((d * x + b) / d)
        == x by {
        lemma_div_multiples_vanish_fancy(x, b, d);
    }
}

/// Proof that multiplying an integer by a common numerator and
/// denominator results in the original integer. Specifically,
/// `(d * x) / d == x`.
pub proof fn lemma_div_multiples_vanish(x: int, d: int)
    requires
        0 < d,
    ensures
        (d * x) / d == x,
{
    lemma_div_multiples_vanish_fancy(x, 0, d);
}

/// Proof that multiplying an integer by a common numerator and
/// denominator results in the original integer
pub proof fn lemma_div_multiples_vanish_auto()
    ensures
        forall|x: int, d: int| #![trigger (d * x) / d] 0 < d ==> (d * x) / d == x,
{
    assert forall|x: int, d: int| 0 < d implies #[trigger] ((d * x) / d) == x by {
        lemma_div_multiples_vanish(x, d);
    }
}

/// Proof that multiplying a whole number by a common numerator and
/// denominator results in the original integer. Specifically,
/// `(b * d) / d == b`.
pub proof fn lemma_div_by_multiple(b: int, d: int)
    requires
        0 <= b,
        0 < d,
    ensures
        (b * d) / d == b,
{
    lemma_div_multiples_vanish(b, d);
    lemma_mul_auto();
}

/// Proof that multiplying a whole number by a common numerator and
/// denominator results in the original integer
pub proof fn lemma_div_by_multiple_auto()
    ensures
        forall|b: int, d: int| #![trigger ((b * d) / d)] 0 <= b && 0 < d ==> (b * d) / d == b,
{
    assert forall|b: int, d: int| 0 <= b && 0 < d implies #[trigger] ((b * d) / d) == b by {
        lemma_div_by_multiple(b, d);
    }
}

/// Proof that a dividend that is a positive multiple of a divisor
/// will always yield a greater quotient than a smaller dividend.
/// Specifically, `x / z < y / z` because `y == m * z` and `x < y`.
pub proof fn lemma_div_by_multiple_is_strongly_ordered(x: int, y: int, m: int, z: int)
    requires
        x < y,
        y == m * z,
        0 < z,
    ensures
        x / z < y / z,
{
    lemma_mod_multiples_basic(m, z);
    lemma_div_induction_auto(
        z,
        y - x,
        |yx: int|
            {
                let u = yx + x;
                x < u && u % z == 0 ==> x / z < u / z
            },
    );
}

/// Proof that a dividend that is a positive multiple of a divisor
/// will always yield a greater quotient than a smaller dividend
pub proof fn lemma_div_by_multiple_is_strongly_ordered_auto()
    ensures
        forall|x: int, y: int, m: int, z: int|
            #![trigger x / z, m * z, y / z]
            x < y && y == m * z && 0 < z ==> x / z < y / z,
{
    assert forall|x: int, y: int, m: int, z: int|
        x < y && y == #[trigger] (m * z) && 0 < z implies #[trigger] (x / z) < #[trigger] (y
        / z) by {
        lemma_div_by_multiple_is_strongly_ordered(x, y, m, z);
    }
}

/// Proof that if an integer is less than or equal to the product of
/// two other integers, then the quotient with one of them will be
/// less than or equal to the other of them. Specifically, because
/// `a <= b * c`, we know `a / b <= c`.
pub proof fn lemma_multiply_divide_le(a: int, b: int, c: int)
    requires
        0 < b,
        a <= b * c,
    ensures
        a / b <= c,
{
    lemma_mod_multiples_basic(c, b);
    let f = |i: int| 0 <= i && (i + a) % b == 0 ==> a / b <= (i + a) / b;
    lemma_div_induction_auto(b, b * c - a, f);
    lemma_div_multiples_vanish(c, b);
}

/// Proof that if an integer is less than or equal to the product of
/// two other integers, then the quotient with one of them will be
/// less than or equal to the other of them
proof fn lemma_multiply_divide_le_auto()
    ensures
        forall|a: int, b: int, c: int| #![trigger a / b, b * c] 0 < b && a <= b * c ==> a / b <= c,
{
    assert forall|a: int, b: int, c: int| 0 < b && a <= #[trigger] (b * c) implies #[trigger] (a
        / b) <= c by {
        lemma_multiply_divide_le(a, b, c);
    }
}

/// Proof that if an integer is less than the product of two other
/// integers, then the quotient with one of them will be less than the
/// other. Specifically, because `a < b * c`, we know `a / b < c`.
pub proof fn lemma_multiply_divide_lt(a: int, b: int, c: int)
    requires
        0 < b,
        a < b * c,
    ensures
        a / b < c,
{
    assert(((b * c - a) + a) % b == 0 ==> a / b < ((b * c - a) + a) / b) by {
        let f = |i: int| 0 < i && (i + a) % b == 0 ==> a / b < (i + a) / b;
        lemma_div_induction_auto(b, b * c - a, f);
    }
    assert(b * c == c * b) by {
        lemma_mul_is_commutative(b, c);
    }
    assert((b * c) % b == 0) by {
        lemma_mod_multiples_basic(c, b);
    }
    assert((b * c) / b == c) by {
        lemma_div_multiples_vanish(c, b);
    }
}

/// Proof that if an integer is less than the product of two other
/// integers, then the quotient with one of them will be less than the
/// other
pub proof fn lemma_multiply_divide_lt_auto()
    ensures
        forall|a: int, b: int, c: int| #![trigger a / b, b * c] 0 < b && a < b * c ==> a / b < c,
{
    assert forall|a: int, b: int, c: int| 0 < b && a < #[trigger] (b * c) implies #[trigger] (a / b)
        < c by {
        lemma_multiply_divide_lt(a, b, c);
    }
}

/// Proof that adding an integer to a fraction is equivalent to adding
/// that integer times the denominator to the numerator. Specifically,
/// `x / d + j == (x + j * d) / d`.
pub proof fn lemma_hoist_over_denominator(x: int, j: int, d: nat)
    requires
        0 < d,
    ensures
        x / d as int + j == (x + j * d) / d as int,
{
    lemma_div_auto(d as int);
    let f = |u: int| x / d as int + u == (x + u * d) / d as int;
    // OBSERVE: push precondition on its on scope
    assert(f(0) && (forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, 1))) && (
    forall|i: int| i <= 0 && #[trigger] f(i) ==> #[trigger] f(sub1(i, 1)))) by {
        lemma_mul_auto();
    }
    lemma_mul_induction(f);
    assert(f(j));
}

/// Proof that adding an integer to a fraction is equivalent to adding
/// that integer times the denominator to the numerator
pub proof fn lemma_hoist_over_denominator_auto()
    ensures
        forall|x: int, j: int, d: nat|
            #![trigger x / d as int + j]
            0 < d ==> x / d as int + j == (x + j * d) / d as int,
{
    assert forall|x: int, j: int, d: nat| 0 < d implies #[trigger] (x / d as int + j) == (x + j * d)
        / d as int by {
        lemma_hoist_over_denominator(x, j, d);
    }
}

/// Proof that, for nonnegative integer `a` and positive integers `b` and `c`,
/// the remainder of `b * (a / b)` divided by `b * c` is less than or equal to `b * (c - 1)`.
/// This accounts for the rounding down that occurs in integer division.
pub proof fn lemma_part_bound1(a: int, b: int, c: int)
    requires
        0 <= a,
        0 < b,
        0 < c,
    ensures
        0 < b * c,
        (b * (a / b) % (b * c)) <= b * (c - 1),
{
    lemma_mul_strictly_positive(b, a / b);
    lemma_mul_strictly_positive(b, c);
    lemma_mul_strictly_positive(b, c - 1);
    calc! {
        (==)
        b * (a / b) % (b * c);
        { ModINL::lemma_fundamental_div_mod(b * (a / b), b * c); }
        b * (a / b) - (b * c) * ((b * (a / b)) / (b * c));
        { lemma_mul_is_associative_auto(); }
        b * (a / b) - b * (c * ((b * (a / b)) / (b * c)));
        { lemma_mul_is_distributive_auto(); }
        b * ((a / b) - (c * ((b * (a / b)) / (b * c))));
    }
    assert(b * (a / b) % (b * c) <= b * (c - 1)) by {
        lemma_mul_is_commutative_auto();
        lemma_mul_inequality_auto();
    };
}

/// Proof that, for any nonnegative integer `a` and positive integers `b` and `c`,
/// the remainder of `b * (a / b)` divided by `b * c` is less than or equal to `b * (c - 1)`.
/// This accounts for the rounding down that occurs in integer division.
pub proof fn lemma_part_bound1_auto()
    ensures
        forall|b: int, c: int| #![trigger b * c] 0 < b && 0 < c ==> 0 < b * c,
        forall|a: int, b: int, c: int|
            #![trigger (b * (a / b) % (b * c))]
            0 <= a && 0 < b && 0 < c ==> b * (a / b) % (b * c) <= b * (c - 1),
{
    assert forall|b: int, c: int| #![trigger b * c] 0 < b && 0 < c implies 0 < b * c by {
        lemma_mul_strictly_positive_auto();
    }
    assert forall|a: int, b: int, c: int|
        #![trigger (b * (a / b) % (b * c))]
        0 <= a && 0 < b && 0 < c implies b * (a / b) % (b * c) <= b * (c - 1) by {
        lemma_part_bound1(a, b, c);
    }
}

/*******************************************************************************
* Modulus
*******************************************************************************/

/// Proof that computing the modulus using `%` is equivalent to
/// computing it with a recursive definition of modulus. Specifically,
/// `x % m` is equivalent in that way.
pub proof fn lemma_mod_is_mod_recursive(x: int, m: int)
    requires
        m > 0,
    ensures
        mod_recursive(x, m) == x % m,
    decreases
            (if x < 0 {
                -x + m
            } else {
                x
            }),
{
    reveal(mod_recursive);
    if x < 0 {
        calc! {
            (==)
            mod_recursive(x, m); {}
            mod_recursive(x + m, m);
            { lemma_mod_is_mod_recursive(x + m, m); }
            (x + m) % m;
            { lemma_add_mod_noop(x, m, m); }
            ((x % m) + (m % m)) % m;
            { lemma_mod_basics_auto(); }
            (x % m) % m;
            { lemma_mod_basics_auto(); }
            x % m;
        }
    } else if x < m {
        lemma_small_mod(x as nat, m as nat);
    } else {
        calc! {
            (==)
            mod_recursive(x, m); {}
            mod_recursive(x - m, m);
            { lemma_mod_is_mod_recursive(x - m, m); }
            (x - m) % m;
            { lemma_sub_mod_noop(x, m, m); }
            ((x % m) - (m % m)) % m;
            { lemma_mod_basics_auto(); }
            (x % m) % m;
            { lemma_mod_basics_auto(); }
            x % m;
        }
    }
}

/// Proof that computing the modulus using `%` is equivalent to
/// computing it by a recursive definition
pub proof fn lemma_mod_is_mod_recursive_auto()
    ensures
        forall|x: int, d: int| d > 0 ==> mod_recursive(x, d) == #[trigger] (x % d),
{
    reveal(mod_recursive);
    assert forall|x: int, d: int| d > 0 implies mod_recursive(x, d) == #[trigger] (x % d) by {
        lemma_mod_is_mod_recursive(x, d);
    };
}

/// Proof of basic properties of the modulus operation: any integer
/// divided by itself produces a remainder of 0; performing `(x % m) %
/// m` gives the same result as simply perfoming `x % m`.
pub proof fn lemma_mod_basics_auto()
    ensures
        forall|m: int| m > 0 ==> #[trigger] (m % m) == 0,
        forall|x: int, m: int| m > 0 ==> #[trigger] ((x % m) % m) == x % m,
{
    assert forall|m: int| m > 0 implies #[trigger] (m % m) == 0 by {
        lemma_mod_auto(m);
    };
    assert forall|x: int, m: int| m > 0 implies #[trigger] ((x % m) % m) == x % m by {
        lemma_mod_auto(m);
    };
}

/// Proof of properties of the modulus operation including those
/// described in [`lemma_mod_basics_auto`]. This lemma also states that
/// the remainder of any division will be less than the divisor's
/// value.
pub proof fn lemma_mod_properties_auto()
    ensures
        forall|m: int| m > 0 ==> #[trigger] (m % m) == 0,
        forall|x: int, m: int| m > 0 ==> #[trigger] ((x % m) % m) == x % m,
        forall|x: int, m: int| m > 0 ==> 0 <= #[trigger] (x % m) < m,
{
    lemma_mod_basics_auto();
    assert forall|x: int, m: int| m > 0 implies 0 <= #[trigger] (x % m) < m by {
        lemma_mod_auto(m);
    }
}

/// Proof that when natural number `x` is divided by natural number
/// `m`, the remainder will be less than or equal to `x`.
pub proof fn lemma_mod_decreases(x: nat, m: nat)
    requires
        0 < m,
    ensures
        x % m <= x,
{
    lemma_mod_auto(m as int);
}

/// Proof that dividing any natural number `x` by any divisor produces
/// a quotient less than or equal to `x`.
pub proof fn lemma_mod_decreases_auto()
    ensures
        forall|x: nat, m: nat| 0 < m ==> #[trigger] (x % m) <= x,
{
    assert forall|x: nat, m: nat| 0 < m implies #[trigger] (x % m) <= x by {
        lemma_mod_decreases(x, m);
    }
}

/// Proof that if `x % m` is zero and `x` is positive, then `x >= m`.
pub proof fn lemma_mod_is_zero(x: nat, m: nat)
    requires
        x > 0 && m > 0,
        x % m == 0,
    ensures
        x >= m,
{
    if (x < m) {
        lemma_small_mod(x, m);
    }
}

/// Proof that if a remainder is zero and the dividend is positive,
/// then the dividend is greater than or equal to the divisor. In
/// other words, if `x % m == 0` and `x > 0`, then `x >= m`.
pub proof fn lemma_mod_is_zero_auto()
    ensures
        forall|x: nat, m: nat| x > 0 && m > 0 && #[trigger] (x % m) == 0 ==> x >= m,
{
    assert forall|x: nat, m: nat| x > 0 && m > 0 && #[trigger] (x % m) == 0 implies x >= m by {
        lemma_mod_is_zero(x, m);
    }
}

/// Proof that multiplying by a number then dividing by that same
/// number produces a remainder of 0. Specifically, `(x * m) % m == 0`.
pub proof fn lemma_mod_multiples_basic(x: int, m: int)
    requires
        m > 0,
    ensures
        (x * m) % m == 0,
{
    lemma_mod_auto(m);
    lemma_mul_auto();
    let f = |u: int| (u * m) % m == 0;
    lemma_mul_induction(f);
    assert(f(x));
}

/// Proof that multiplying by a number then dividing by that same
/// number produces a remainder of 0
pub proof fn lemma_mod_multiples_basic_auto()
    ensures
        forall|x: int, m: int| m > 0 ==> #[trigger] ((x * m) % m) == 0,
{
    assert forall|x: int, m: int| m > 0 implies #[trigger] ((x * m) % m) == 0 by {
        lemma_mod_multiples_basic(x, m);
    }
}

/// Proof that adding the divisor to the dividend doesn't change the
/// remainder. Specifically, `(m + b) % m == b % m`.
pub proof fn lemma_mod_add_multiples_vanish(b: int, m: int)
    requires
        0 < m,
    ensures
        (m + b) % m == b % m,
{
    lemma_mod_auto(m);
}

/// Proof that adding the divisor to the dividend doesn't change the
/// remainder. In other words, for all `m` and `b`, `(m + b) % m == b % m`.
pub proof fn lemma_mod_add_multiples_vanish_auto()
    ensures
        forall|b: int, m: int| m > 0 ==> ((m + b) % m) == #[trigger] (b % m),
{
    assert forall|b: int, m: int| m > 0 implies ((m + b) % m) == #[trigger] (b % m) by {
        lemma_mod_add_multiples_vanish(b, m);
    }
}

/// Proof that subtracting the divisor from the dividend doesn't
/// change the remainder. Specifically, `(-m + b) % m == b % m`.
pub proof fn lemma_mod_sub_multiples_vanish(b: int, m: int)
    requires
        0 < m,
    ensures
        (-m + b) % m == b % m,
{
    lemma_mod_auto(m);
}

/// Proof that subtracting the divisor from the dividend doesn't
/// change the remainder. In other words, for all `m` and `b`,
/// `(-m + b) % m == b % m`.
pub proof fn lemma_mod_sub_multiples_vanish_auto()
    ensures
        forall|b: int, m: int| m > 0 ==> ((-m + b) % m) == #[trigger] (b % m),
{
    assert forall|b: int, m: int| m > 0 implies ((-m + b) % m) == #[trigger] (b % m) by {
        lemma_mod_sub_multiples_vanish(b, m);
    }
}

/// Proof that adding any multiple of the divisor to the dividend will produce the
/// same remainder. In other words, `(m * a + b) % m == b % m`.
pub proof fn lemma_mod_multiples_vanish(a: int, b: int, m: int)
    requires
        0 < m,
    ensures
        (m * a + b) % m == b % m,
    decreases
            (if a > 0 {
                a
            } else {
                -a
            }),
{
    lemma_mod_auto(m);
    lemma_mul_auto();
    let f = |u: int| (m * u + b) % m == b % m;
    lemma_mul_induction(f);
    assert(f(a));
}

/// Proof that adding any multiple of the divisor to the dividend will produce the
/// same remainder. In other words, for all `m`, `a`, and `b`,
/// `(m * a + b) % m == b % m`.
pub proof fn lemma_mod_multiples_vanish_auto()
    ensures
        forall|a: int, b: int, m: int| m > 0 ==> #[trigger] ((m * a + b) % m) == b % m,
{
    assert forall|a: int, b: int, m: int| m > 0 implies #[trigger] ((m * a + b) % m) == b % m by {
        lemma_mod_multiples_vanish(a, b, m);
    }
}

/// Proof that modulo distributes over subtraction if the subtracted value is
/// less than or equal to the modulo of the number it's being subtracted from.
/// Specifically, because `0 <= s <= x % d`, we can conclude that
/// `x % d - s % d == (x - s) % d`.
pub proof fn lemma_mod_subtraction(x: nat, s: nat, d: nat)
    requires
        0 < d,
        0 <= s <= x % d,
    ensures
        x % d - s % d == (x - s) % d as int,
{
    lemma_mod_auto(d as int);
}

/// Proof that modulo distributes over subtraction if the subtracted
/// value is less than or equal to the modulo of the number it's being
/// subtracted from. In other words, for all `s`, `x`, and `d`
/// satisfying `0 <= s <= x % d`, we can conclude that `x % d - s % d
/// == (x - s) % d`.
pub proof fn lemma_mod_subtraction_auto()
    ensures
        forall|x: nat, s: nat, d: nat|
            #![trigger ((x - s) % d as int)]
            0 < d && 0 <= s <= x % d ==> x % d - s % d == (x - s) % d as int,
{
    assert forall|x: nat, s: nat, d: nat| 0 < d && 0 <= s <= x % d implies x % d - s % d
        == #[trigger] ((x - s) % d as int) as int by {
        lemma_mod_subtraction(x, s, d);
    }
}

/// Proof that modulo distributes over addition, provided you do an
/// extra modulo after adding the remainders. Specifically,
/// `((x % m) + (y % m)) % m == (x + y) % m`.
pub proof fn lemma_add_mod_noop(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        ((x % m) + (y % m)) % m == (x + y) % m,
{
    lemma_mod_auto(m);
}

/// Proof that modulo distributes over addition, provided you do an
/// extra modulo after adding the remainders. In other words, for all
/// `x`, `y`, and `m`, `((x % m) + (y % m)) % m == (x + y) % m`.
pub proof fn lemma_add_mod_noop_auto()
    ensures
        forall|x: int, y: int, m: int|
            #![trigger (x + y) % m]
            0 < m ==> ((x % m) + (y % m)) % m == (x + y) % m,
{
    assert forall|x: int, y: int, m: int| 0 < m implies ((x % m) + (y % m)) % m == #[trigger] ((x
        + y) % m) by {
        lemma_add_mod_noop(x, y, m);
    }
}

/// Proof that describes an expanded and succinct version of modulus
/// operator in relation to addition. Specifically,
/// `(x + (y % m)) % m == (x + y) % m`.
pub proof fn lemma_add_mod_noop_right(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        (x + (y % m)) % m == (x + y) % m,
{
    lemma_mod_auto(m);
}

/// Proof that describes an expanded and succinct version of modulus
/// operator in relation to addition. That is, for all `x`, `y`, and
/// `m`, `(x + (y % m)) % m == (x + y) % m`.
pub proof fn lemma_add_mod_noop_right_auto()
    ensures
        forall|x: int, y: int, m: int|
            #![trigger (x + y) % m]
            0 < m ==> (x + (y % m)) % m == (x + y) % m,
{
    assert forall|x: int, y: int, m: int| 0 < m implies (x + (y % m)) % m == #[trigger] ((x + y)
        % m) by {
        lemma_add_mod_noop_right(x, y, m);
    }
}

/// Proof that modulo distributes over subtraction provided you do an
/// extra modulo operation after subtracting the remainders.
/// Specifically, `((x % m) - (y % m)) % m == (x - y) % m`.
pub proof fn lemma_sub_mod_noop(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        ((x % m) - (y % m)) % m == (x - y) % m,
{
    lemma_mod_auto(m);
}

/// Proof that modulo distributes over subtraction provided you do an
/// extra modulo operation after subtracting the remainders. In other
/// words, for all `x`, `y`, and `m`,
/// `((x % m) - (y % m)) % m == (x - y) % m`.
pub proof fn lemma_sub_mod_noop_auto()
    ensures
        forall|x: int, y: int, m: int|
            #![trigger (x - y) % m]
            0 < m ==> ((x % m) - (y % m)) % m == (x - y) % m,
{
    assert forall|x: int, y: int, m: int| 0 < m implies ((x % m) - (y % m)) % m == #[trigger] ((x
        - y) % m) by {
        lemma_sub_mod_noop(x, y, m);
    }
}

/// Proof that describes an expanded and succinct version of modulus
/// operator in relation to subtraction. Specifically,
/// `(x - (y % m)) % m == (x - y) % m`.
pub proof fn lemma_sub_mod_noop_right(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        (x - (y % m)) % m == (x - y) % m,
{
    lemma_mod_auto(m);
}

/// Proof that describes an expanded and succinct version of modulus
/// operator in relation to subtraction. That is, for all `x`, `y`,
/// and `m`, `(x - (y % m)) % m == (x - y) % m`.
pub proof fn lemma_sub_mod_noop_right_auto()
    ensures
        forall|x: int, y: int, m: int|
            #![trigger ((x - y) % m)]
            0 < m ==> (x - (y % m)) % m == (x - y) % m,
{
    assert forall|x: int, y: int, m: int| 0 < m implies (x - (y % m)) % m == #[trigger] ((x - y)
        % m) by {
        lemma_sub_mod_noop_right(x, y, m);
    }
}

/// Proof of two properties of the sum of two remainders with the same dividend:
/// 1) `a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d)`.
/// 2) `(a % d + b % d) < d ==> a % d + b % d == (a + b) % d`.
pub proof fn lemma_mod_adds(a: int, b: int, d: int)
    requires
        0 < d,
    ensures
        a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d),
        (a % d + b % d) < d ==> a % d + b % d == (a + b) % d,
{
    lemma_mul_auto();
    lemma_div_auto(d);
}

/// Proof of two properties of the sum of two remainders with the same dividend,
/// i.e., that for all `a`, `b`, and `d`:
/// 1) `a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d)`.
/// 2) `(a % d + b % d) < d ==> a % d + b % d == (a + b) % d`.
pub proof fn lemma_mod_adds_auto()
    ensures
        forall|a: int, b: int, d: int|
            #![trigger ((a + b) % d)]
            0 < d ==> a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d),
{
    assert forall|a: int, b: int, d: int| 0 < d implies a % d + b % d == #[trigger] ((a + b) % d)
        + d * ((a % d + b % d) / d) by {
        lemma_mod_adds(a, b, d);
    }
}

/// Proof that the remainder when dividing integer `x` by positive
/// integer `d` is equivalent to the remainder of `x * (1 - d)` by
/// `d`.
#[verifier::spinoff_prover]
pub proof fn lemma_mod_neg_neg(x: int, d: int)
    requires
        0 < d,
    ensures
        x % d == (x * (1 - d)) % d,
{
    assert((x - x * d) % d == x % d) by {
        let f = |i: int| (x - i * d) % d == x % d;
        lemma_mul_auto();
        assert(f(0) && (forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, 1))) && (
        forall|i: int| i <= 0 && #[trigger] f(i) ==> #[trigger] f(sub1(i, 1)))) by {
            lemma_mod_auto(d);
        };
        lemma_mul_induction(f);
        assert(f(x));
    }
    lemma_mul_auto();
}

/// This proof isn't exported from this module. It's just used in
/// the proof of [`lemma_fundamental_div_mod_converse`].
proof fn lemma_fundamental_div_mod_converse_helper_1(u: int, d: int, r: int)
    requires
        d != 0,
        0 <= r < d,
    ensures
        u == (u * d + r) / d,
    decreases
            if u >= 0 {
                u
            } else {
                -u
            },
{
    if u < 0 {
        lemma_fundamental_div_mod_converse_helper_1(u + 1, d, r);
        lemma_div_add_denominator(d, u * d + r);
        lemma_mul_is_distributive_add_other_way(d, u + 1, -1);
        assert(u == (u * d + r) / d);
    } else if u == 0 {
        DivINL::lemma_small_div();
        assert(u == 0 ==> u * d == 0) by (nonlinear_arith);
        assert(u == (u * d + r) / d);
    } else {
        lemma_fundamental_div_mod_converse_helper_1(u - 1, d, r);
        lemma_div_add_denominator(d, (u - 1) * d + r);
        lemma_mul_is_distributive_add_other_way(d, u - 1, 1);
        assert(u * d + r == (u - 1) * d + r + d);
        assert(u == (u * d + r) / d);
    }
}

/// This proof isn't exported from this module. It's just used in
/// the proof of [`lemma_fundamental_div_mod_converse`].
proof fn lemma_fundamental_div_mod_converse_helper_2(u: int, d: int, r: int)
    requires
        d != 0,
        0 <= r < d,
    ensures
        r == (u * d + r) % d,
    decreases
            if u >= 0 {
                u
            } else {
                -u
            },
{
    if u < 0 {
        lemma_fundamental_div_mod_converse_helper_2(u + 1, d, r);
        lemma_mod_add_multiples_vanish(u * d + r, d);
        lemma_mul_is_distributive_add_other_way(d, u + 1, -1);
        assert(u * d == (u + 1) * d + (-1) * d);
        assert(u * d + r == (u + 1) * d + r - d);
        assert(r == (u * d + r) % d);
    } else if u == 0 {
        assert(u == 0 ==> u * d == 0) by (nonlinear_arith);
        if d > 0 {
            lemma_small_mod(r as nat, d as nat);
        } else {
            lemma_small_mod(r as nat, (-d) as nat);
        }
        assert(r == (u * d + r) % d);
    } else {
        lemma_fundamental_div_mod_converse_helper_2(u - 1, d, r);
        lemma_mod_add_multiples_vanish((u - 1) * d + r, d);
        lemma_mul_is_distributive_add_other_way(d, u - 1, 1);
        assert(u * d + r == (u - 1) * d + r + d);
        assert(r == (u * d + r) % d);
    }
}

/// Proof of the converse of the fundamental property of division and modulo.
/// Specifically, if we know `0 <= r < d` and `x == q * d + r`, then we
/// know that `q` is the quotient `x / d` and `r` is the remainder `x % d`.
pub proof fn lemma_fundamental_div_mod_converse(x: int, d: int, q: int, r: int)
    requires
        d != 0,
        0 <= r < d,
        x == q * d + r,
    ensures
        q == x / d,
        r == x % d,
{
    lemma_fundamental_div_mod_converse_helper_1(q, d, r);
    assert(q == (q * d + r) / d);
    lemma_fundamental_div_mod_converse_helper_2(q, d, r);
}

/// Proof of the converse of the fundamental property of division and
/// modulo. That is, whenever `0 <= r < d` and `x == q * d + r`, we
/// know that `q` is the quotient `x / d` and `r` is the remainder `x % d`.
pub proof fn lemma_fundamental_div_mod_converse_auto()
    ensures  // forall |x: int, d: int, q: int, r: int| d != 0 && 0 <= r < d && x == #[trigger](q * d + r) ==> q == (x / d) && r == #[trigger](x % d),

        forall|x: int, d: int, q: int, r: int|
            d != 0 && 0 <= r < d && x == #[trigger] (q * d + r) ==> q == #[trigger] (x / d),
        forall|x: int, d: int, q: int, r: int|
            d != 0 && 0 <= r < d && x == #[trigger] (q * d + r) ==> r == #[trigger] (x % d),
{
    assert forall|x: int, d: int, q: int, r: int|
        d != 0 && 0 <= r < d && x == #[trigger] (q * d + r) implies q == #[trigger] (x / d) by {
        lemma_fundamental_div_mod_converse(x, d, q, r);
    };
    assert forall|x: int, d: int, q: int, r: int|
        d != 0 && 0 <= r < d && x == #[trigger] (q * d + r) implies r == #[trigger] (x % d) by {
        lemma_fundamental_div_mod_converse(x, d, q, r);
    };
}

/// Proof that the remainder, when natural number `x` is divided by
/// positive integer `m`, is less than `m`.
pub proof fn lemma_mod_pos_bound(x: int, m: int)
    requires
        0 <= x,
        0 < m,
    ensures
        0 <= x % m < m,
{
    lemma_mod_auto(m);
}

/// Proof that the remainder, when any natural number `x` is divided by
/// any positive integer `m`, is less than `m`.
pub proof fn lemma_mod_pos_bound_auto()
    ensures
        forall|x: int, m: int| 0 <= x && 0 < m ==> 0 <= #[trigger] (x % m) < m,
{
    assert forall|x: int, m: int| 0 <= x && 0 < m implies 0 <= #[trigger] (x % m) < m by {
        lemma_mod_pos_bound(x, m);
    }
}

/// Proof that when integer `x` is divided by positive integer `m`,
/// the remainder is nonegative and less than `m`.
pub proof fn lemma_mod_bound(x: int, m: int)
    requires
        0 < m,
    ensures
        0 <= x % m < m,
{
    ModINL::lemma_mod_range(x, m);
}

/// Proof that when any number is divided by a positive integer, the
/// remainder is nonnegative and less than that positive integer.
pub proof fn lemma_mod_bound_auto()
    ensures
        forall|x: int, m: int| 0 < m ==> 0 <= #[trigger] (x % m) < m,
{
    assert forall|x: int, m: int| 0 < m implies 0 <= #[trigger] (x % m) < m by {
        lemma_mod_bound(x, m);
    }
}

/// Proof that the remainder when `x * y` is divided by `m` is
/// equivalent to the remainder when `(x % m) * y` is divided by `m`
pub proof fn lemma_mul_mod_noop_left(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        (x % m) * y % m == x * y % m,
{
    lemma_mod_auto(m);
    lemma_mul_induction_auto(y, |u: int| (x % m) * u % m == x * u % m);
}

/// Proof that for any `x`, `y`, and `m`, the remainder when `x * y`
/// is divided by `m` is equivalent to the remainder when `(x % m) *
/// y` is divided by `m`
pub proof fn lemma_mul_mod_noop_left_auto()
    ensures
        forall|x: int, y: int, m: int| 0 < m ==> (x % m) * y % m == #[trigger] (x * y % m),
{
    assert forall|x: int, y: int, m: int| 0 < m implies (x % m) * y % m == #[trigger] (x * y
        % m) by {
        lemma_mul_mod_noop_left(x, y, m);
    }
}

/// Proof that the remainder when `x * y` is divided by `m` is
/// equivalent to the remainder when `x * (y % m)` is divided by `m`.
pub proof fn lemma_mul_mod_noop_right(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        x * (y % m) % m == (x * y) % m,
{
    lemma_mod_auto(m);
    lemma_mul_induction_auto(x, |u: int| u * (y % m) % m == (u * y) % m);
}

/// Proof that for all `x`, `y`, and `m`, the remainder when `x * y`
/// is divided by `m` is equivalent to the remainder when `x * (y % m)`
/// is divided by `m`.
pub proof fn lemma_mul_mod_noop_right_auto()
    ensures
        forall|x: int, y: int, m: int| 0 < m ==> x * (y % m) % m == #[trigger] ((x * y) % m),
{
    assert forall|x: int, y: int, m: int| 0 < m implies x * (y % m) % m == #[trigger] ((x * y)
        % m) by {
        lemma_mul_mod_noop_right(x, y, m);
    }
}

/// Proof of various properties about modulo equivalence with respect
/// to multiplication, specifically various expressions that `(x * y)
/// % m` is equivalent to.
pub proof fn lemma_mul_mod_noop_general(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        ((x % m) * y) % m == (x * y) % m,
        (x * (y % m)) % m == (x * y) % m,
        ((x % m) * (y % m)) % m == (x * y) % m,
{
    lemma_mod_properties_auto();
    lemma_mul_mod_noop_left(x, y, m);
    lemma_mul_mod_noop_right(x, y, m);
    lemma_mul_mod_noop_right(x % m, y, m);
}

/// Proof of various properties about modulo equivalence with respect
/// to multiplication
pub proof fn lemma_mul_mod_noop_general_auto()
    ensures
        forall|x: int, y: int, m: int|
            0 < m ==> (((x % m) * y) % m == (x * (y % m)) % m == ((x % m) * (y % m)) % m
                == #[trigger] ((x * y) % m)),
{
    assert forall|x: int, y: int, m: int| 0 < m implies (((x % m) * y) % m == (x * (y % m)) % m == (
    (x % m) * (y % m)) % m == #[trigger] ((x * y) % m)) by {
        lemma_mul_mod_noop_general(x, y, m);
    }
}

/// Proof that modulo distributes over multiplication, provided you do
/// an extra modulo operation after multiplying the remainders. Specifically,
/// `(x % m) * (y % m) % m == (x * y) % m`.
pub proof fn lemma_mul_mod_noop(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        (x % m) * (y % m) % m == (x * y) % m,
{
    lemma_mul_mod_noop_general(x, y, m);
}

/// Proof that modulo distributes over multiplication, provided you do
/// an extra modulo operation after multiplying the remainders
pub proof fn lemma_mul_mod_noop_auto()
    ensures
        forall|x: int, y: int, m: int|
            0 < m ==> ((x % m) * (y % m) % m == #[trigger] ((x * y) % m)),
{
    assert forall|x: int, y: int, m: int| 0 < m implies ((x % m) * (y % m) % m == #[trigger] ((x
        * y) % m)) by {
        lemma_mul_mod_noop(x, y, m);
    }
}

/// Proof that `x` and `y` are congruent modulo `m` if and only if `x
/// - y` is congruent to 0 modulo `m`. In other words, `x % m == y % m
/// <==> (x - y) % m == 0`.
pub proof fn lemma_mod_equivalence(x: int, y: int, m: int)
    requires
        0 < m,
    ensures
        x % m == y % m <==> (x - y) % m == 0,
{
    lemma_mod_auto(m);
}

/// Proof that for all `x`, `y`, and `m`, `x` and `y` are congruent
/// modulo `m` if and only if `x - y` is congruent to 0 modulo `m`. In
/// other words, `x % m == y % m <==> (x - y) % m == 0`.
///
/// Note: The Dafny standard library uses the triggers `x % m, y % m`
/// for this forall quantifier. But this can lead to a trigger loop,
/// so we don't do that here.
pub proof fn lemma_mod_equivalence_auto()
    ensures
        forall|x: int, y: int, m: int|
            #![trigger (x - y) % m]
            0 < m ==> (x % m == y % m <==> (x - y) % m == 0),
{
    assert forall|x: int, y: int, m: int| #![trigger (x - y) % m] 0 < m implies ((x % m) == (y % m)
        <==> (x - y) % m == 0) by {
        lemma_mod_equivalence(x, y, m);
    }
}

/// This function says that `x` is congruent to `y` modulo `m` if and
/// only if their difference `x - y` is congruent to 0 modulo `m`.
pub open spec fn is_mod_equivalent(x: int, y: int, m: int) -> bool
    recommends
        m > 0,
{
    x % m == y % m <==> (x - y) % m == 0
}

/// Proof that if `is_mod_equivalent` holds for `x`, `y`, and `m`,
/// then it holds for `x * z`, `y * z`, and `m`
pub proof fn lemma_mod_mul_equivalent(x: int, y: int, z: int, m: int)
    requires
        m > 0,
        is_mod_equivalent(x, y, m),
    ensures
        is_mod_equivalent(x * z, y * z, m),
{
    lemma_mul_mod_noop_left(x, z, m);
    lemma_mul_mod_noop_left(y, z, m);
    lemma_mod_equivalence(x, y, m);
    lemma_mod_equivalence(x * z, y * z, m);
}

/// Proof that if `is_mod_equivalent` holds for any `x`, `y`, and `m`,
/// then it holds for `x * z`, `y * z`, and `m`
pub proof fn lemma_mod_mul_equivalent_auto()
    ensures
        forall|x: int, y: int, z: int, m: int|
            m > 0 && (x % m == y % m <==> (x - y) % m == 0) ==> #[trigger] is_mod_equivalent(
                x * z,
                y * z,
                m,
            ),
{
    assert forall|x: int, y: int, z: int, m: int|
        m > 0 && is_mod_equivalent(x, y, m) implies #[trigger] is_mod_equivalent(
        x * z,
        y * z,
        m,
    ) by {
        lemma_mod_mul_equivalent(x, y, z, m);
    }
}

/// Proof that multiplying the divisor by a positive number can't
/// decrease the remainder. Specifically, because `k > 0`, we have
/// `x % d <= x % (d * k)`.
pub proof fn lemma_mod_ordering(x: int, k: int, d: int)
    requires
        1 < d,
        0 < k,
    ensures
        0 < d * k,
        x % d <= x % (d * k),
{
    lemma_mul_strictly_increases(d, k);
    calc! {
        (==)
        x % d + d * (x / d);
        { lemma_fundamental_div_mod(x, d); }
        x;
        { lemma_fundamental_div_mod(x, d * k); }
        x % (d * k) + (d * k) * (x / (d * k));
        { lemma_mul_is_associative_auto(); }
        x % (d * k) + d * (k * (x / (d * k)));
        }
    calc! {
        (==)
        x % d;
        { lemma_mod_properties_auto(); }
        (x % d) % d;
        { lemma_mod_multiples_vanish(x / d  - k * (x / (d * k)), x % d, d); }
        (x % d + d * (x / d  - k * (x / (d * k)))) % d;
        { lemma_mul_is_distributive_sub_auto(); }
        (x % d + d * (x / d) - d * (k * (x / (d * k)))) % d; {}
        (x % (d * k)) % d;
    }
    assert((x % (d * k)) % d <= x % (d * k)) by {
        lemma_mod_properties_auto();
        lemma_mod_decreases((x % (d * k)) as nat, d as nat);
    };
}

/// Proof that multiplying the divisor by a positive number can't
/// decrease the remainder. That is, for any `x`, `d > 1`, and `k > 0`,
/// `x % d <= x % (d * k)`.
pub proof fn lemma_mod_ordering_auto()
    ensures
        forall|x: int, k: int, d: int| 1 < d && 0 < k ==> (x % d <= #[trigger] (x % (d * k))),
{
    assert forall|x: int, k: int, d: int| 1 < d && 0 < k implies (x % d <= #[trigger] (x % (d
        * k))) by {
        lemma_mod_ordering(x, k, d);
    }
}

/// Proof that the remainder when `x` is divided by `a * b`, taken
/// modulo `a`, is equivalent to `x` modulo `a`. That is,
/// `(x % (a * b)) % a == x % a`.
#[verifier::spinoff_prover]
pub proof fn lemma_mod_mod(x: int, a: int, b: int)
    requires
        0 < a,
        0 < b,
    ensures
        0 < a * b,
        (x % (a * b)) % a == x % a,
{
    lemma_mul_strictly_positive_auto();
    calc! { (==)
        x;
        { lemma_fundamental_div_mod(x, a * b); }
        (a * b) * (x / (a * b)) + x % (a * b);
        { lemma_mul_is_associative_auto(); }
        a * (b * (x / (a * b))) + x % (a * b);
        { lemma_fundamental_div_mod(x % (a * b), a); }
        a * (b * (x / (a * b))) + a * (x % (a * b) / a) + (x % (a * b)) % a;
        { lemma_mul_is_distributive_auto(); }
        a * (b * (x / (a * b)) + x % (a * b) / a) + (x % (a * b)) % a;
    }
    lemma_mod_properties_auto();
    lemma_mul_is_commutative_auto();
    lemma_fundamental_div_mod_converse(
        x,
        a,
        b * (x / (a * b)) + x % (a * b) / a,
        (x % (a * b)) % a,
    );
}

/// Proof that for any integer `x` and positive integers `a` and `b`,
/// the remainder when `x` is divided by `a * b`, taken modulo `a`,
/// is equivalent to `x` modulo `a`. In other words,
/// `(x % (a * b)) % a == x % a`.
pub proof fn lemma_mod_mod_auto()
    ensures
        forall|a: int, b: int| #![trigger a * b] 0 < a && 0 < b ==> 0 < a * b,
        forall|x: int, a: int, b: int|
            #![trigger (x % (a * b)) % a, x % a]
            0 < a && 0 < b ==> (x % (a * b)) % a == x % a,
{
    assert forall|a: int, b: int| #![trigger a * b] 0 < a && 0 < b implies 0 < a * b by {
        lemma_mul_strictly_positive_auto();
    }
    assert forall|x: int, a: int, b: int| #![trigger x % (a * b)] 0 < a && 0 < b implies (x % (a
        * b)) % a == x % a by {
        lemma_mod_mod(x, a, b);
    }
}

/// Proof that `(x % y) % (y * z) < y`.
pub proof fn lemma_part_bound2(x: int, y: int, z: int)
    requires
        0 <= x,
        0 < y,
        0 < z,
    ensures
        y * z > 0,
        (x % y) % (y * z) < y,
{
    lemma_mul_strictly_positive_auto();
    lemma_mod_properties_auto();
    assert(x % y < y);
    lemma_mul_increases_auto();
    lemma_mul_is_commutative_auto();
    assert(y <= y * z);
    assert(0 <= x % y < y * z);
    lemma_mod_properties_auto();
    lemma_small_mod((x % y) as nat, (y * z) as nat);
    assert((x % y) % (y * z) == x % y);
}

/// Proof that any nonnegative integer `x` modulo `y` modulo `y * z`
/// is less than `y`
pub proof fn lemma_part_bound2_auto()
    ensures
        forall|y: int, z: int| (0 < y && 0 < z) ==> #[trigger] (y * z) > 0,
        forall|x: int, y: int, z: int|
            (0 <= x && 0 < y && 0 < z) ==> (#[trigger] (x % y) % #[trigger] (y * z) < y),
{
    assert forall|y: int, z: int| 0 < y && 0 < z implies #[trigger] (y * z) > 0 by {
        lemma_mul_strictly_positive_auto();
    };
    assert forall|x: int, y: int, z: int| 0 <= x && 0 < y && 0 < z implies #[trigger] (x % y)
        % #[trigger] (y * z) < y by {
        lemma_part_bound2(x, y, z);
    };
}

/// Proof of the validity of an expanded form of the modulus operation.
/// Specifically, `x % (y * z) == y * ((x / y) % z) + x % y`.
pub proof fn lemma_mod_breakdown(x: int, y: int, z: int)
    requires
        0 <= x,
        0 < y,
        0 < z,
    ensures
        y * z > 0,
        x % (y * z) == y * ((x / y) % z) + x % y,
{
    lemma_mul_strictly_positive_auto();
    lemma_div_pos_is_pos(x, y);
    assert(0 <= x / y);
    assert((y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z) by {
        lemma_part_bound1(x, y, z);
        lemma_part_bound2(x, y, z);
        lemma_mul_basics_auto();
        lemma_mul_is_distributive_auto();
    };
    calc! { (==)
        x % (y * z);
        { lemma_fundamental_div_mod(x, y); }
        (y * (x / y) + x%  y) % (y * z);
        {
            lemma_mod_properties_auto();
            assert(0 <= x % y);
            lemma_mul_nonnegative(y, x / y);
            assert((y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z);
            lemma_mod_adds(y * (x / y), x % y, y * z);
        }
        (y * (x / y)) % (y * z) + (x % y) % (y * z);
        {
            lemma_mod_properties_auto();
            lemma_mul_increases(z, y);
            lemma_mul_is_commutative_auto();
            assert(x % y < y && y <= y * z);
            lemma_small_mod((x % y) as nat, (y * z) as nat);
            assert((x % y) % (y * z) == x % y);
        }
        (y * (x / y)) % (y * z) + x % y;
        { lemma_truncate_middle(x / y, y, z); }
        y * ((x / y) % z) + x % y;
    }
}

/// Proof of the validity of an expanded form of the modulus operation.
/// That is, for any nonnegative `x`, positive `y`, and positive `z`, we know
/// `x % (y * z) == y * ((x / y) % z) + x % y`.
pub proof fn lemma_mod_breakdown_auto()
    ensures
        forall|y: int, z: int| #![trigger y * z] 0 < y && 0 < z ==> y * z > 0,
        forall|x: int, y: int, z: int|
            #![trigger x % (y * z)]
            0 <= x && 0 < y && 0 < z ==> x % (y * z) == y * ((x / y) % z) + x % y,
{
    assert forall|y: int, z: int| #![trigger y * z] 0 < y && 0 < z implies y * z > 0 by {
        lemma_mul_strictly_positive_auto();
    }
    assert forall|x: int, y: int, z: int| #![trigger x % (y * z)] 0 <= x && 0 < y && 0 < z implies x
        % (y * z) == y * ((x / y) % z) + x % y by {
        lemma_mod_breakdown(x, y, z);
    }
}

} // verus!
    }

    pub mod logarithm {
        //! This file contains proofs related to integer logarithms. These are
        //! part of the math standard library.
        //!
        //! It's based on the following file from the Dafny math standard
        //! library:
        //! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Logarithm.dfy`.
        //! That file has the following copyright notice:
        //! /*******************************************************************************
        //! * Original: Copyright (c) Microsoft Corporation *
        //! SPDX-License-Identifier: MIT * * Modifications and Extensions:
        //! Copyright by the contributors to the Dafny Project *
        //! SPDX-License-Identifier: MIT
        //! *******************************************************************************/
        #[allow(unused_imports)]
        use builtin::*;
        use builtin_macros::*;

        verus! {

use crate::calc_macro::*;
#[cfg(verus_keep_ghost)]
use crate::arithmetic::div_mod::{
    lemma_div_pos_is_pos_auto,
    lemma_div_decreases_auto,
    lemma_div_is_ordered_auto,
    lemma_div_multiples_vanish,
};
#[cfg(verus_keep_ghost)]
use crate::math::{div as div1};
#[cfg(verus_keep_ghost)]
use crate::arithmetic::mul::{lemma_mul_increases, lemma_mul_is_commutative};
#[cfg(verus_keep_ghost)]
use crate::arithmetic::power::{pow, lemma_pow_positive};

/// This function recursively defines the integer logarithm. It's only
/// meaningful when the base of the logarithm `base` is greater than 1,
/// and when the value whose logarithm is taken, `pow`, is non-negative.
#[verifier::opaque]
pub open spec fn log(base: int, pow: int) -> int
    recommends
        base > 1,
        pow >= 0,
    decreases pow,
{
    // In Dafny, we can invoke lemmas in functions to establish
    // termination. Here in Verus, instead, we add the second
    // conditions `pow / base >= pow` and `pow / base < 0` to show
    // termination.
    if pow < base || pow / base >= pow || pow / base < 0 {
        0
    } else {
        1 + log(base, pow / base)
    }
}

/// Proof that since `pow` is less than `base`, its logarithm in that base is 0
pub proof fn lemma_log0(base: int, pow: int)
    requires
        base > 1,
        0 <= pow < base,
    ensures
        log(base, pow) == 0,
{
    reveal(log);
}

/// Proof that since `pow` is greater than or equal to `base`, its
/// logarithm in that base is 1 more than the logarithm of `pow /
/// base`
pub proof fn lemma_log_s(base: int, pow: int)
    requires
        base > 1,
        pow >= base,
    ensures
        pow / base >= 0,
        log(base, pow) == 1 + log(base, pow / base),
{
    lemma_div_pos_is_pos_auto();
    lemma_div_decreases_auto();
    reveal(log);
}

/// Proof that whenever a value is greater than or equal to a base,
/// that value's logarithm in that base is 1 more than the logarithm
/// of that value divided by the base
pub proof fn lemma_log_s_auto()
    ensures
        forall|base: int, pow: int|
            #![trigger log(base, div1(pow, base))]
            base > 1 && pow >= base ==> div1(pow, base) >= 0 && log(base, pow) == 1 + log(
                base,
                div1(pow, base),
            ),
{
    assert forall|base: int, pow: int|
        #![trigger log(base, div1(pow, base))]
        base > 1 && pow >= base implies div1(pow, base) >= 0 && log(base, pow) == 1 + log(
        base,
        div1(pow, base),
    ) by {
        lemma_log_s(base, pow);
    }
}

/// Proof that the integer logarithm is always nonnegative. Specifically,
/// `log(base, pow) >= 0`.
pub proof fn lemma_log_nonnegative(base: int, pow: int)
    requires
        base > 1,
        0 <= pow,
    ensures
        log(base, pow) >= 0,
    decreases pow,
{
    reveal(log);
    if !(pow < base || pow / base >= pow || pow / base < 0) {
        lemma_log_nonnegative(base, pow / base);
    }
}

/// Proof that since `pow1` is less than or equal to `pow2`, the
/// integer logarithm of `pow1` in base `base` is less than or equal
/// to that of `pow2`.
pub proof fn lemma_log_is_ordered(base: int, pow1: int, pow2: int)
    requires
        base > 1,
        0 <= pow1 <= pow2,
    ensures
        log(base, pow1) <= log(base, pow2),
    decreases pow1,
{
    reveal(log);
    if pow2 < base {
        assert(log(base, pow1) == 0 == log(base, pow2));
    } else if pow1 < base {
        assert(log(base, pow1) == 0);
        lemma_log_nonnegative(base, pow2);
    } else {
        lemma_div_pos_is_pos_auto();
        lemma_div_decreases_auto();
        lemma_div_is_ordered_auto();
        lemma_log_is_ordered(base, pow1 / base, pow2 / base);
    }
}

/// Proof that the integer logarithm of `pow(base, n)` in base `base` is `n`
pub proof fn lemma_log_pow(base: int, n: nat)
    requires
        base > 1,
    ensures
        log(base, pow(base, n)) == n,
    decreases n,
{
    if n == 0 {
        reveal(pow);
        reveal(log);
    } else {
        let n_minus_1: nat = (n - 1) as nat;
        lemma_pow_positive(base, n);
        calc! {
            (==)
            log(base, pow(base, n));
            (==) { reveal(pow); }
            log(base, base * pow(base, n_minus_1));
            (==)
            {
                lemma_pow_positive(base, n_minus_1);
                lemma_mul_increases(pow(base, n_minus_1), base);
                lemma_mul_is_commutative(pow(base, n_minus_1), base);
                lemma_log_s(base, base * pow(base, n_minus_1));
            }
            1 + log(base, (base * pow(base, n_minus_1)) / base);
            (==) { lemma_div_multiples_vanish(pow(base, n_minus_1), base); }
            1 + log(base, pow(base, n_minus_1));
            (==) { lemma_log_pow(base, n_minus_1); }
            1 + (n - 1);
        }
    }
}

} // verus!
    }

    pub mod mul {
        //! This file contains proofs related to integer multiplication (`*`).
        //! These are part of the math standard library.
        //!
        //! It's based on the following file from the Dafny math standard
        //! library:
        //! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Mul.dfy`.
        //! That file has the following copyright notice:
        //! /*******************************************************************************
        //! * Original: Copyright (c) Microsoft Corporation *
        //! SPDX-License-Identifier: MIT * * Modifications and Extensions:
        //! Copyright by the contributors to the Dafny Project *
        //! SPDX-License-Identifier: MIT
        //! *******************************************************************************/
        #[allow(unused_imports)]
        use builtin::*;
        use builtin_macros::*;

        verus! {

use crate::arithmetic::internals::mul_internals_nonlinear as MulINL;
use crate::arithmetic::internals::mul_internals::*;

/// Proof that multiplication using `*` is equivalent to
/// multiplication using a recursive definition. Specifically,
/// `x * y` is equivalent in that way.
pub proof fn lemma_mul_is_mul_recursive(x: int, y: int)
    ensures
        (x * y) == mul_recursive(x, y),
{
    if (x >= 0) {
        lemma_mul_is_mul_pos(x, y);
        assert(x * y == mul_pos(x, y));
        assert((x * y) == mul_recursive(x, y));
    } else {
        lemma_mul_is_mul_pos(-x, y);
        assert(x * y == -1 * (-x * y)) by { lemma_mul_is_associative(-1, -x, y) };  // OBSERVE
        assert((x * y) == mul_recursive(x, y));
    }
}

/// Proof that multiplication using `*` is equivalent to
/// multiplication using a recursive definition
pub proof fn lemma_mul_is_mul_recursive_auto()
    ensures
        forall|x: int, y: int| x * y == mul_recursive(x, y),
{
    assert forall|x: int, y: int| x * y == mul_recursive(x, y) by { lemma_mul_is_mul_recursive(x, y)
    };
}

/// Proof that multiplying two positive integers with `*` results in
/// the same product as would be achieved by recursive addition.
/// Specifically, `x * y == mul_pos(x, y)`.
pub proof fn lemma_mul_is_mul_pos(x: int, y: int)
    requires
        x >= 0,
    ensures
        x * y == mul_pos(x, y),
{
    reveal(mul_pos);
    lemma_mul_induction_auto(x, |u: int| u >= 0 ==> u * y == mul_pos(u, y));
}

/// Proof of basic properties of multiplication by `x`, specifically
/// what happens when multiplying by 0 or 1
pub proof fn lemma_mul_basics(x: int)
    ensures
        0 * x == 0,
        x * 0 == 0,
        x * 1 == x,
        1 * x == x,
{
}

/// Proof of basic properties of multiplication, specifically what
/// happens when multiplying by 0 or 1
pub proof fn lemma_mul_basics_auto()
    ensures
        forall|x: int| #[trigger] (0 * x) == 0,
        forall|x: int| #[trigger] (x * 0) == 0,
        forall|x: int| #[trigger] (1 * x) == x,
        forall|x: int| #[trigger] (x * 1) == x,
{
}

/// Proof that `x * y` is nonzero if and only if both `x` and `y` are nonzero
pub proof fn lemma_mul_nonzero(x: int, y: int)
    ensures
        x * y != 0 <==> x != 0 && y != 0,
{
    MulINL::lemma_mul_nonzero(x, y);
}

/// Proof that a product is nonzero if and only if both factors are nonzero
pub proof fn lemma_mul_nonzero_auto()
    ensures
        forall|x: int, y: int| #[trigger] (x * y) != 0 <==> x != 0 && y != 0,
{
    assert forall|x: int, y: int| #[trigger] (x * y) != 0 <==> x != 0 && y != 0 by {
        lemma_mul_nonzero(x, y);
    }
}

/// Proof that any integer multiplied by 0 results in a product of 0
pub proof fn lemma_mul_by_zero_is_zero_auto()
    ensures
        forall|x: int| #![trigger x * 0] #![trigger 0 * x] x * 0 == 0 && 0 * x == 0,
{
    assert forall|x: int| #![trigger x * 0] #![trigger 0 * x] x * 0 == 0 && 0 * x == 0 by {
        lemma_mul_basics(x);
    }
}

/// Proof that multiplication is associative, specifically that
/// `x * (y * z) == (x * y) * z`.
pub proof fn lemma_mul_is_associative(x: int, y: int, z: int)
    ensures
        x * (y * z) == (x * y) * z,
{
    MulINL::lemma_mul_is_associative(x, y, z);
}

/// Proof that multiplication is associative
pub proof fn lemma_mul_is_associative_auto()
    ensures
        forall|x: int, y: int, z: int|
            #![trigger x * (y * z)]
            #![trigger (x * y) * z]
            (x * (y * z)) == ((x * y) * z),
{
    assert forall|x: int, y: int, z: int|
        #![trigger x * (y * z)]
        #![trigger (x * y) * z]
        (x * (y * z)) == ((x * y) * z) by {
        lemma_mul_is_associative(x, y, z);
    }
}

/// Proof that multiplication is commutative, specifically that
/// `x * y == y * x`.
pub proof fn lemma_mul_is_commutative(x: int, y: int)
    ensures
        x * y == y * x,
{
}

/// Proof that multiplication is commutative
pub proof fn lemma_mul_is_commutative_auto()
    ensures
        forall|x: int, y: int| #[trigger] (x * y) == (y * x),
{
}

/// Proof that, since the product of the two integers `x` and `y` is
/// nonnegative, that product is greater than or equal to each of `x`
/// and `y`
pub proof fn lemma_mul_ordering(x: int, y: int)
    requires
        x != 0,
        y != 0,
        0 <= x * y,
    ensures
        x * y >= x && x * y >= y,
{
    MulINL::lemma_mul_ordering(x, y);
}

/// Proof that if the product of two integers is nonnegative, then
/// that product is greater than or equal to each of the two integers
proof fn lemma_mul_ordering_auto()
    ensures
        forall|x: int, y: int|
            (0 != x && 0 != y && #[trigger] (x * y) >= 0) ==> x * y >= x && (x * y) >= y,
{
    assert forall|x: int, y: int| 0 != x && 0 != y && x * y >= 0 implies #[trigger] (x * y) >= x
        && #[trigger] (x * y) >= y by {
        lemma_mul_ordering(x, y);
    };
}

/*
    We don't port LemmaMulEquality or LemmaMulEqualityAuto from the
    Dafny standard library for arithmetic, since they're never useful.
    They say that `x == y ==> x * z == y * z`, which is trivial. It
    follows immediately from the basic SMT axiom that functions and
    operators (including multiplication) have equal values when
    applied to equal arguments.
*/

/// Proof that, since `x <= y` and `z >= 0`, `x * z <= y * z`
pub proof fn lemma_mul_inequality(x: int, y: int, z: int)
    requires
        x <= y,
        z >= 0,
    ensures
        x * z <= y * z,
{
    lemma_mul_induction_auto(z, |u: int| u >= 0 ==> x * u <= y * u);
}

/// Proof that any two integers, when each multiplied by a positive
/// number, will maintain their numerical order
pub proof fn lemma_mul_inequality_auto()
    ensures
        forall|x: int, y: int, z: int|
            x <= y && z >= 0 ==> #[trigger] (x * z) <= #[trigger] (y * z),
{
    assert forall|x: int, y: int, z: int| x <= y && z >= 0 implies #[trigger] (x * z)
        <= #[trigger] (y * z) by {
        lemma_mul_inequality(x, y, z);
    }
}

/// Proof that since `x < y` and `z > 0`, `x * z < y * z`.
pub proof fn lemma_mul_strict_inequality(x: int, y: int, z: int)
    requires
        x < y,
        z > 0,
    ensures
        x * z < y * z,
{
    MulINL::lemma_mul_strict_inequality(x, y, z);
}

/// Proof that any two distinct integers, when each multiplied by a
/// positive integer, preserves their numerical order
pub proof fn lemma_mul_strict_inequality_auto()
    ensures
        forall|x: int, y: int, z: int| x < y && z > 0 ==> #[trigger] (x * z) < #[trigger] (y * z),
{
    assert forall|x: int, y: int, z: int| x < y && z > 0 implies #[trigger] (x * z) < #[trigger] (y
        * z) by {
        if x < y && z > 0 {
            lemma_mul_strict_inequality(x, y, z);
        }
    }
}

/// Proof that since `x` is bounded above by `xbound` and `y` is
/// bounded above by `ybound`, the product of `x` and `y` is bounded
/// above by the product of the bounds
pub proof fn lemma_mul_upper_bound(x: int, xbound: int, y: int, ybound: int)
    requires
        x <= xbound,
        y <= ybound,
        0 <= x,
        0 <= y,
    ensures
        x * y <= xbound * ybound,
{
    lemma_mul_inequality(x, xbound, y);
    lemma_mul_inequality(y, ybound, xbound);
}

/// Proof that when two integers have upper bounds, their product is
/// bounded above by the product of their upper bounds
pub proof fn lemma_mul_upper_bound_auto()
    ensures
        forall|x: int, xbound: int, y: int, ybound: int|
            x <= xbound && y <= ybound && 0 <= x && 0 <= y ==> #[trigger] (x * y) <= #[trigger] (
            xbound * ybound),
{
    assert forall|x: int, xbound: int, y: int, ybound: int|
        x <= xbound && y <= ybound && 0 <= x && 0 <= y implies #[trigger] (x * y) <= #[trigger] (
    xbound * ybound) by {
        lemma_mul_upper_bound(x, xbound, y, ybound);
    }
}

/// Proof that when `x` has an exclusive upper bound `xbound` and `y`
/// has an exclusive upper bound `ybound`, that the product of `x` and
/// `y` is bounded above by the product of the predecessors of their
/// upper bounds. In other words, `x * y <= (xbound - 1) * (ybound - 1)`.
pub proof fn lemma_mul_strict_upper_bound(x: int, xbound: int, y: int, ybound: int)
    requires
        x < xbound,
        y < ybound,
        0 < x,
        0 < y,
    ensures
        x * y <= (xbound - 1) * (ybound - 1),
{
    lemma_mul_inequality(x, xbound - 1, y);
    lemma_mul_inequality(y, ybound - 1, xbound - 1);
}

/// Proof that when two integers have exclusive upper bounds, their
/// product has, as an upper bound, the product of the predecessors of
/// their upper bounds
pub proof fn lemma_mul_strict_upper_bound_auto()
    ensures
        forall|x: int, xbound: int, y: int, ybound: int|
            x < xbound && y < ybound && 0 < x && 0 < y ==> #[trigger] (x * y) <= #[trigger] ((xbound
                - 1) * (ybound - 1)),
{
    assert forall|x: int, xbound: int, y: int, ybound: int|
        x < xbound && y < ybound && 0 < x && 0 < y implies #[trigger] (x * y) <= #[trigger] ((xbound
        - 1) * (ybound - 1)) by {
        lemma_mul_strict_upper_bound(x, xbound, y, ybound);
    }
}

/// Proof that multiplying the positive integer `x` by respectively
/// `y` and `z` maintains the order of `y` and `z`. Specifically, `y
/// <= z ==> x * y <= x * z` and `y < z ==> x * y < x * z`.
pub proof fn lemma_mul_left_inequality(x: int, y: int, z: int)
    requires
        0 < x,
    ensures
        y <= z ==> x * y <= x * z,
        y < z ==> x * y < x * z,
{
    lemma_mul_induction_auto(x, |u: int| u > 0 ==> y <= z ==> u * y <= u * z);
    lemma_mul_induction_auto(x, |u: int| u > 0 ==> y < z ==> u * y < u * z);
}

/// Proof that, for all `y`, `z`, and positive `x`, multiplying `x` by
/// respectively `y` and `z` maintains the order of `y` and `z`.
/// Specifically, `y <= z ==> x * y <= x * z` and `y < z ==> x * y < x * z`.
pub proof fn lemma_mul_left_inequality_auto()
    ensures
        forall|x: int, y: int, z: int|
            x > 0 ==> (y <= z ==> #[trigger] (x * y) <= #[trigger] (x * z)) && (y < z ==> (x * y)
                < (x * z)),
{
    assert forall|x: int, y: int, z: int| (y <= z || y < z) && 0 < x implies (y <= z
        ==> #[trigger] (x * y) <= #[trigger] (x * z)) && (y < z ==> (x * y) < (x * z)) by {
        lemma_mul_left_inequality(x, y, z);
    }
}

/// Proof that if `x` and `y` have equal results when multiplied by
/// nonzero `m`, then they're equal
pub proof fn lemma_mul_equality_converse(m: int, x: int, y: int)
    requires
        m != 0,
        m * x == m * y,
    ensures
        x == y,
{
    lemma_mul_induction_auto(m, |u| x > y && 0 < u ==> x * u > y * u);
    lemma_mul_induction_auto(m, |u: int| x < y && 0 < u ==> x * u < y * u);
    lemma_mul_induction_auto(m, |u: int| x > y && 0 > u ==> x * u < y * u);
    lemma_mul_induction_auto(m, |u: int| x < y && 0 > u ==> x * u > y * u);
}

/// Proof that if any two integers are each multiplied by a common
/// nonzero integer and the products are equal, the two original
/// integers are equal
pub proof fn lemma_mul_equality_converse_auto()
    ensures
        forall|m: int, x: int, y: int|
            (m != 0 && #[trigger] (m * x) == #[trigger] (m * y)) ==> x == y,
{
    assert forall|m: int, x: int, y: int|
        m != 0 && #[trigger] (m * x) == #[trigger] (m * y) implies x == y by {
        lemma_mul_equality_converse(m, x, y);
    }
}

/// Proof that since `x * z <= y * z` and `z > 0`, that `x <= y`
pub proof fn lemma_mul_inequality_converse(x: int, y: int, z: int)
    requires
        x * z <= y * z,
        z > 0,
    ensures
        x <= y,
{
    lemma_mul_induction_auto(z, |u: int| x * u <= y * u && u > 0 ==> x <= y);
}

/// Proof that whenever two integers have a less-than-or-equal
/// relationship to each other when multiplied by a positive integer,
/// they have that relationship themselves.
pub proof fn lemma_mul_inequality_converse_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] (x * z) <= #[trigger] (y * z) && z > 0 ==> x <= y,
{
    assert forall|x: int, y: int, z: int| #[trigger]
        (x * z) <= #[trigger] (y * z) && z > 0 implies x <= y by {
        lemma_mul_inequality_converse(x, y, z);
    }
}

/// Proof that since `x * z < y * z` and `z >= 0`, we know `x < y`
pub proof fn lemma_mul_strict_inequality_converse(x: int, y: int, z: int)
    requires
        x * z < y * z,
        z >= 0,
    ensures
        x < y,
{
    lemma_mul_induction_auto(z, |u: int| x * u < y * u && u >= 0 ==> x < y);
}

/// Proof that whenever two integers have a less-than relationship to
/// each other when multiplied by a nonnegative integer, they have
/// that relationship themselves
pub proof fn lemma_mul_strict_inequality_converse_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] (x * z) < #[trigger] (y * z) && z >= 0 ==> x < y,
{
    assert forall|x: int, y: int, z: int| #[trigger]
        (x * z) < #[trigger] (y * z) && z >= 0 implies x < y by {
        lemma_mul_strict_inequality_converse(x, y, z);
    }
}

/// Proof that multiplication distributes over addition, specifically that
/// `x * (y + z) == x * y + x * z`
pub proof fn lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures
        x * (y + z) == x * y + x * z,
{
    MulINL::lemma_mul_is_distributive_add(x, y, z);
}

/// Proof that multiplication distributes over addition
pub proof fn lemma_mul_is_distributive_add_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] (x * (y + z)) == x * y + x * z,
{
    assert forall|x: int, y: int, z: int| #[trigger] (x * (y + z)) == x * y + x * z by {
        lemma_mul_is_distributive_add(x, y, z);
    }
}

/// Proof that multiplication distributes over addition, specifically that
/// `(y + z) * x == y * x + z * x`
pub proof fn lemma_mul_is_distributive_add_other_way(x: int, y: int, z: int)
    ensures
        (y + z) * x == y * x + z * x,
{
    lemma_mul_auto();
}

/// Proof that multiplication distributes over addition when the
/// addition happens in the multiplicand (i.e., in the left-hand
/// argument to `*`)
proof fn lemma_mul_is_distributive_add_other_way_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] ((y + z) * x) == y * x + z * x,
{
    assert forall|x: int, y: int, z: int| #[trigger] ((y + z) * x) == y * x + z * x by {
        lemma_mul_is_distributive_add_other_way(x, y, z);
    }
}

/// Proof that multiplication distributes over subtraction, specifically that
/// `x * (y - z) == x * y - x * z`
pub proof fn lemma_mul_is_distributive_sub(x: int, y: int, z: int)
    ensures
        x * (y - z) == x * y - x * z,
{
    lemma_mul_auto();
}

/// Proof that multiplication distributes over subtraction
pub proof fn lemma_mul_is_distributive_sub_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] (x * (y - z)) == x * y - x * z,
{
    assert forall|x: int, y: int, z: int| #[trigger] (x * (y - z)) == x * y - x * z by {
        lemma_mul_is_distributive_sub(x, y, z);
    }
}

/// Proof that multiplication distributes over subtraction when the
/// subtraction happens in the multiplicand (i.e., in the left-hand
/// argument to `*`). Specifically, `(y - z) * x == y * x - z * x`.
pub proof fn lemma_mul_is_distributive_sub_other_way(x: int, y: int, z: int)
    ensures
        (y - z) * x == y * x - z * x,
{
    lemma_mul_is_distributive_sub(x, y, z);
    lemma_mul_is_commutative(x, y - z);
    lemma_mul_is_commutative(x, y);
    lemma_mul_is_commutative(x, z);
}

/// Proof that multiplication distributes over subtraction when the
/// subtraction happens in the multiplicand (i.e., in the left-hand
/// argument to `*`)
pub proof fn lemma_mul_is_distributive_sub_other_way_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] ((y - z) * x) == y * x - z * x,
{
    assert forall|x: int, y: int, z: int| #[trigger] ((y - z) * x) == y * x - z * x by {
        lemma_mul_is_distributive_sub_other_way(x, y, z)
    }
}

/// Proof that multiplication is commutative, distributes over
/// addition, and distributes over subtraction, in the specific cases
/// where one of the arguments to the multiplication is `x` and the
/// other arguments are `y` and `z`
pub proof fn lemma_mul_is_distributive(x: int, y: int, z: int)
    ensures
        x * (y + z) == x * y + x * z,
        x * (y - z) == x * y - x * z,
        (y + z) * x == y * x + z * x,
        (y - z) * x == y * x - z * x,
        x * (y + z) == (y + z) * x,
        x * (y - z) == (y - z) * x,
        x * y == y * x,
        x * z == z * x,
{
    lemma_mul_auto();
}

/// Proof that multiplication distributes over addition and
/// subtraction, whether the addition or subtraction happens in the
/// first or the second argument to the multiplication
pub proof fn lemma_mul_is_distributive_auto()
    ensures
        forall|x: int, y: int, z: int| #[trigger] (x * (y + z)) == x * y + x * z,
        forall|x: int, y: int, z: int| #[trigger] (x * (y - z)) == x * y - x * z,
        forall|x: int, y: int, z: int| #[trigger] ((y + z) * x) == y * x + z * x,
        forall|x: int, y: int, z: int| #[trigger] ((y - z) * x) == y * x - z * x,
{
    lemma_mul_is_distributive_add_auto();
    lemma_mul_is_distributive_sub_auto();
    lemma_mul_is_commutative_auto();
}

/// Proof that if `x` and `y` are both positive, then their product is
/// also positive
pub proof fn lemma_mul_strictly_positive(x: int, y: int)
    ensures
        (0 < x && 0 < y) ==> (0 < x * y),
{
    MulINL::lemma_mul_strictly_positive(x, y);
}

/// Proof that multiplying any two positive integers will result in a
/// positive integer
pub proof fn lemma_mul_strictly_positive_auto()
    ensures
        forall|x: int, y: int| (0 < x && 0 < y) ==> (0 < #[trigger] (x * y)),
{
    assert forall|x: int, y: int| 0 < x && 0 < y implies 0 < #[trigger] (x * y) by {
        lemma_mul_strictly_positive(x, y);
    }
}

/// Proof that since `x > 1` and `y > 0`, `y < x * y`
pub proof fn lemma_mul_strictly_increases(x: int, y: int)
    requires
        1 < x,
        0 < y,
    ensures
        y < x * y,
{
    lemma_mul_induction_auto(x, |u: int| 1 < u ==> y < u * y);
}

/// Proof that multiplying any positive integer by any integer greater
/// than 1 will result in a product that is greater than the original
/// integer
pub proof fn lemma_mul_strictly_increases_auto()
    ensures
        forall|x: int, y: int| 1 < x && 0 < y ==> y < #[trigger] (x * y),
{
    assert forall|x: int, y: int| 1 < x && 0 < y implies y < #[trigger] (x * y) by {
        lemma_mul_strictly_increases(x, y);
    }
}

/// Proof that since `x` and `y` are both positive, their product is
/// greater than or equal to `y`
pub proof fn lemma_mul_increases(x: int, y: int)
    requires
        0 < x,
        0 < y,
    ensures
        y <= x * y,
{
    lemma_mul_induction_auto(x, |u: int| 0 < u ==> y <= u * y);
}

/// Proof that multiplying any two positive integers will result in a
/// product that is greater than or equal to each original integer
pub proof fn lemma_mul_increases_auto()
    ensures
        forall|x: int, y: int| (0 < x && 0 < y) ==> (y <= #[trigger] (x * y)),
{
    assert forall|x: int, y: int| (0 < x && 0 < y) implies (y <= #[trigger] (x * y)) by {
        lemma_mul_increases(x, y);
    }
}

/// Proof that since `x` and `y` are non-negative, their product is
/// non-negative
pub proof fn lemma_mul_nonnegative(x: int, y: int)
    requires
        0 <= x,
        0 <= y,
    ensures
        0 <= x * y,
{
    lemma_mul_induction_auto(x, |u: int| 0 <= u ==> 0 <= u * y);
}

/// Proof that multiplying any two non-negative integers produces a
/// non-negative integer
pub proof fn lemma_mul_nonnegative_auto()
    ensures
        forall|x: int, y: int| 0 <= x && 0 <= y ==> 0 <= #[trigger] (x * y),
{
    assert forall|x: int, y: int| 0 <= x && 0 <= y implies 0 <= #[trigger] (x * y) by {
        lemma_mul_nonnegative(x, y);
    }
}

/// Proof that negating `x` or `y` before multiplying them together
/// produces the negation of the product of `x` and `y`
pub proof fn lemma_mul_unary_negation(x: int, y: int)
    ensures
        (-x) * y == -(x * y) == x * (-y),
{
    lemma_mul_induction_auto(x, |u: int| (-u) * y == -(u * y) == u * (-y));
}

/// Proof that negating one of two integers before multiplying them
/// together produces the negation of their product
pub proof fn lemma_mul_unary_negation_auto()
    ensures
        forall|x: int, y: int|
            #![trigger (-x) * y]
            #![trigger x * (-y)]
            ((-x) * y) == (-(x * y)) == x * (-y),
{
    assert forall|x: int, y: int|
        #![trigger (-x) * y]
        #![trigger x * (-y)]
        ((-x) * y) == (-(x * y)) == x * (-y) by {
        lemma_mul_unary_negation(x, y);
    }
}

/// Proof that multiplying `-x` and `-y` produces the same product as
/// multiplying `x` and `y`
pub proof fn lemma_mul_cancels_negatives(x: int, y: int)
    ensures
        x * y == (-x) * (-y),
{
    lemma_mul_induction_auto(x, |u: int| (-u) * y == -(u * y) == u * (-y));
}

/// Proof that for any two integers `x` and `y`, multiplying `-x` and
/// `-y` produces the same product as multiplying `x` and `y`
pub proof fn lemma_mul_cancels_negatives_auto()
    ensures
        forall|x: int, y: int| #[trigger] (x * y) == (-x) * (-y),
{
    assert forall|x: int, y: int| #[trigger] (x * y) == (-x) * (-y) by {
        lemma_mul_cancels_negatives(x, y);
    }
}

/// Proof establishing many useful properties of negation
pub proof fn lemma_mul_properties()
    ensures
        forall|x: int, y: int| #[trigger] (x * y) == y * x,
        forall|x: int| #![trigger x * 1] #![trigger 1 * x] x * 1 == 1 * x == x,
        forall|x: int, y: int, z: int| x < y && z > 0 ==> #[trigger] (x * z) < #[trigger] (y * z),
        forall|x: int, y: int, z: int|
            x <= y && z >= 0 ==> #[trigger] (x * z) <= #[trigger] (y * z),
        forall|x: int, y: int, z: int| #[trigger] (x * (y + z)) == x * y + x * z,
        forall|x: int, y: int, z: int| #[trigger] (x * (y - z)) == x * y - x * z,
        forall|x: int, y: int, z: int| #[trigger] ((y + z) * x) == y * x + z * x,
        forall|x: int, y: int, z: int| #[trigger] ((y - z) * x) == y * x - z * x,
        forall|x: int, y: int, z: int|
            #![trigger x * (y * z)]
            #![trigger (x * y) * z]
            x * (y * z) == (x * y) * z,
        forall|x: int, y: int| #[trigger] (x * y) != 0 <==> x != 0 && y != 0,
        forall|x: int, y: int| 0 <= x && 0 <= y ==> 0 <= #[trigger] (x * y),
        forall|x: int, y: int|
            0 < x && 0 < y && 0 <= x * y ==> x <= #[trigger] (x * y) && y <= (x * y),
        forall|x: int, y: int| (1 < x && 0 < y) ==> (y < #[trigger] (x * y)),
        forall|x: int, y: int| (0 < x && 0 < y) ==> (y <= #[trigger] (x * y)),
        forall|x: int, y: int| (0 < x && 0 < y) ==> (0 < #[trigger] (x * y)),
{
    lemma_mul_strict_inequality_auto();
    lemma_mul_inequality_auto();
    lemma_mul_is_distributive_auto();
    lemma_mul_is_associative_auto();
    lemma_mul_ordering_auto();
    lemma_mul_nonzero_auto();
    lemma_mul_nonnegative_auto();
    lemma_mul_strictly_increases_auto();
    lemma_mul_increases_auto();
}

} // verus!
    }

    pub mod power {
        //! This file contains proofs related to exponentiation. These are
        //! part of the math standard library.
        //!
        //! It's based on the following file from the Dafny math standard library:
        //! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Power.dfy`.
        //! That file has the following copyright notice:
        //! /*******************************************************************************
        //! *  Original: Copyright (c) Microsoft Corporation
        //! *  SPDX-License-Identifier: MIT
        //! *
        //! *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
        //! *  SPDX-License-Identifier: MIT
        //! *******************************************************************************/
        use crate::calc_macro::*;
        #[allow(unused_imports)]
        use builtin::*;
        use builtin_macros::*;

        verus! {

use crate::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::general_internals::{is_le};
#[cfg(verus_keep_ghost)]
use crate::arithmetic::mul::{
    lemma_mul_inequality,
    lemma_mul_nonnegative_auto,
    lemma_mul_strictly_increases,
    lemma_mul_left_inequality,
    lemma_mul_basics_auto,
    lemma_mul_increases_auto,
    lemma_mul_strictly_increases_auto,
    lemma_mul_is_commutative_auto,
    lemma_mul_is_distributive_auto,
    lemma_mul_is_associative_auto,
    lemma_mul_nonnegative,
};
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::mul_internals::{lemma_mul_auto, lemma_mul_induction_auto};
#[cfg(verus_keep_ghost)]
use crate::math::{sub as sub1};

/// This function performs exponentiation recursively, to compute `b`
/// to the power of a natural number `e`
pub open spec fn pow(b: int, e: nat) -> int
    decreases e,
{
    if e == 0 {
        1
    } else {
        b * pow(b, (e - 1) as nat)
    }
}

/// Proof that the given integer `b` to the power of 0 is 1
pub proof fn lemma_pow0(b: int)
    ensures
        pow(b, 0) == 1,
{
    reveal(pow);
}

/// Proof that any integer to the power of 0 is 1
pub proof fn lemma_pow0_auto()
    ensures
        forall|b: int| #[trigger] pow(b, 0 as nat) == 1,
{
    reveal(pow);
}

/// Proof that the given integer `b` to the power of 1 is `b`
pub proof fn lemma_pow1(b: int)
    ensures
        pow(b, 1) == b,
{
    calc! { (==)
        pow(b, 1);
        { reveal(pow); }
        b * pow(b, 0);
        { lemma_pow0(b); }
        b * 1;
        { lemma_mul_basics_auto(); }
        b;
    }
}

/// Proof that any integer to the power of 1 is itself
pub proof fn lemma_pow1_auto()
    ensures
        forall|b: int| #[trigger] pow(b, 1) == b,
{
    reveal(pow);
    assert forall|b: int| #[trigger] pow(b, 1) == b by {
        lemma_pow1(b);
    };
}

/// Proof that 0 to the power of the given positive integer `e` is 0
pub proof fn lemma0_pow(e: nat)
    requires
        e > 0,
    ensures
        pow(0, e) == 0,
    decreases e,
{
    reveal(pow);
    lemma_mul_basics_auto();
    if e != 1 {
        lemma0_pow((e - 1) as nat);
    }
}

/// Proof that 0 to the power of any positive integer is 0
pub proof fn lemma0_pow_auto()
    ensures
        forall|e: nat| e > 0 ==> #[trigger] pow(0, e) == 0,
{
    reveal(pow);
    assert forall|e: nat| e > 0 implies #[trigger] pow(0, e) == 0 by {
        lemma0_pow(e);
    }
}

/// Proof that 1 to the power of the given natural number `e` is 1
pub proof fn lemma1_pow(e: nat)
    ensures
        pow(1, e) == 1,
    decreases e,
{
    reveal(pow);
    lemma_mul_basics_auto();
    if e != 0 {
        lemma1_pow((e - 1) as nat);
    }
}

/// Proof that 1 to the power of any natural number is 1
pub proof fn lemma1_pow_auto()
    ensures
        forall|e: nat| e > 0 ==> #[trigger] pow(1, e) == 1,
{
    reveal(pow);
    assert forall|e: nat| e > 0 implies #[trigger] pow(1, e) == 1 by {
        lemma1_pow(e);
    }
}

/// Proof that taking the given number `x` to the power of 2 produces `x * x`
pub proof fn lemma_square_is_pow2(x: int)
    ensures
        pow(x, 2) == x * x,
{
    reveal_with_fuel(pow, 3);
}

/// Proof that taking any positive integer to the power of 2 is
/// equivalent to multiplying that integer by itself
pub proof fn lemma_square_is_pow2_auto()
    ensures
        forall|x: int| x > 0 ==> #[trigger] pow(x, 2) == x * x,
{
    reveal(pow);
    assert forall|x: int| x > 0 implies #[trigger] pow(x, 2) == x * x by {
        lemma_square_is_pow2(x);
    }
}

/// Proof that taking the given positive integer `b` to the power of
/// the given natural number `n` produces a positive result
pub proof fn lemma_pow_positive(b: int, e: nat)
    requires
        b > 0,
    ensures
        0 < pow(b, e),
{
    // dafny does not need to reveal
    reveal(pow);
    lemma_mul_increases_auto();
    lemma_pow0_auto();
    lemma_mul_induction_auto(e as int, |u: int| 0 <= u ==> 0 < pow(b, u as nat));
}

/// Proof that taking any positive integer to any natural number power
/// produces a positive result
pub proof fn lemma_pow_positive_auto()
    ensures
        forall|b: int, e: nat| b > 0 ==> 0 < #[trigger] pow(b, e),
{
    reveal(pow);
    assert forall|b: int, e: nat| b > 0 implies 0 < #[trigger] pow(b, e) by {
        lemma_pow_positive(b, e);
    }
}

/// Proof that taking an integer `b` to the power of the sum of two
/// natural numbers `e1` and `e2` is equivalent to multiplying `b` to
/// the power of `e1` by `b` to the power of `e2`
pub proof fn lemma_pow_adds(b: int, e1: nat, e2: nat)
    ensures
        pow(b, e1 + e2) == pow(b, e1) * pow(b, e2),
    decreases e1,
{
    if e1 == 0 {
        calc! { (==)
        pow(b, e1) * pow(b, e2);
        { lemma_pow0(b); }
        1 * pow(b, e2);
        { lemma_mul_basics_auto(); }
        pow(b, 0 + e2);
    }
    } else {
        calc! { (==)
        pow(b, e1) * pow(b, e2);
        { reveal(pow); }
        (b * pow(b, (e1 - 1) as nat)) * pow(b, e2);
        { lemma_mul_is_associative_auto(); }
        b * (pow(b, (e1 - 1) as nat) * pow(b, e2));
        { lemma_pow_adds(b, (e1 - 1) as nat, e2); }
        b * pow(b, (e1 - 1 + e2) as nat);
        { reveal(pow); }
        pow(b, e1 + e2);
    }
    }
}

/// Proof that taking an integer to the power of the sum of two
/// natural numbers is equivalent to taking it to the power of each of
/// those numbers and multiplying the results
pub proof fn lemma_pow_adds_auto()
    ensures
        forall|x: int, y: nat, z: nat| #[trigger] pow(x, y + z) == pow(x, y) * pow(x, z),
{
    assert forall|x: int, y: nat, z: nat| #[trigger] pow(x, y + z) == pow(x, y) * pow(x, z) by {
        lemma_pow_adds(x, y, z);
    }
}

/// Proof that if `e1 >= e2`, then `b` to the power of `e1` is equal
/// to the product of `b` to the power of `e1 - e2` and `b` to the
/// power of `e2`
pub proof fn lemma_pow_sub_add_cancel(b: int, e1: nat, e2: nat)
    requires
        e1 >= e2,
    ensures
        pow(b, (e1 - e2) as nat) * pow(b, e2) == pow(b, e1),
    decreases e1,
{
    lemma_pow_adds(b, (e1 - e2) as nat, e2);
}

/// Proof that, for any `x`, `y`, and `z` such that `y >= z`, we know
/// `x` to the power of `y` is equal to the product of `x` to the
/// power of `y - z` and `x` to the power of `z`
pub proof fn lemma_pow_sub_add_cancel_auto()
    ensures
        forall|x: int, y: nat, z: nat|
            y >= z ==> #[trigger] pow(x, (y - z) as nat) * pow(x, z) == pow(x, y),
{
    assert forall|x: int, y: nat, z: nat| y >= z implies #[trigger] pow(x, (y - z) as nat) * pow(
        x,
        z,
    ) == pow(x, y) by {
        lemma_pow_sub_add_cancel(x, y, z);
    }
}

/// Proof that, as long as `e1 <= e2`, taking a positive integer `b`
/// to the power of `e2 - e1` is equivalent to dividing `b` to the
/// power of `e2` by `b` to the power of `e1`.
pub proof fn lemma_pow_subtracts(b: int, e1: nat, e2: nat)
    requires
        b > 0,
        e1 <= e2,
    ensures
        pow(b, e1) > 0,
        pow(b, (e2 - e1) as nat) == pow(b, e2) / pow(b, e1) > 0,
{
    lemma_pow_positive_auto();
    calc! {
        (==)
        pow(b, e2) / pow(b , e1);
        { lemma_pow_sub_add_cancel(b , e2, e1); }
        pow(b , (e2 - e1) as nat) * pow(b , e1) / pow(b , e1);
        { lemma_div_by_multiple(pow(b , (e2 - e1) as nat), pow(b , e1)); }
        pow(b , (e2 - e1) as nat);
    }
}

/// Proof that, for all `b`, `e1`, and `e2`, as long as `b` is
/// positive and `e1 <= e2`, taking `b` to the power of `e2 - e1` is
/// equivalent to dividing `b` to the power of `e2` by `b` to the
/// power of `e1`.
pub proof fn lemma_pow_subtracts_auto()
    ensures
        forall|b: int, e1: nat| b > 0 ==> pow(b, e1) > 0,
        forall|b: int, e1: nat, e2: nat|
            b > 0 && e1 <= e2 ==> #[trigger] pow(b, (e2 - e1) as nat) == pow(b, e2) / pow(b, e1)
                > 0,
{
    reveal(pow);
    lemma_pow_positive_auto();
    assert forall|b: int, e1: nat, e2: nat| b > 0 && e1 <= e2 implies #[trigger] pow(
        b,
        (e2 - e1) as nat,
    ) == pow(b, e2) / pow(b, e1) > 0 by {
        lemma_pow_subtracts(b, e1, e2);
    }
}

/// Proof that `a` to the power of `b * c` is equal to the result of
/// taking `a` to the power of `b`, then taking that to the power of
/// `c`
pub proof fn lemma_pow_multiplies(a: int, b: nat, c: nat)
    ensures
        0 <= b * c,
        pow(pow(a, b), c) == pow(a, b * c),
    decreases c,
{
    lemma_mul_nonnegative(b as int, c as int);
    if c == 0 {
        lemma_mul_basics_auto();
        calc! {
            (==)
            pow(a, (b * c) as nat);
            { lemma_pow0(a); }
            1;
            { lemma_pow0(pow(a, b)); }
            pow(pow(a, b), c);
        }
    } else {
        calc! { (==)
            b * c - b;
            { lemma_mul_basics_auto(); }
            b * c - b * 1;
            { lemma_mul_is_distributive_auto(); }
            b * (c - 1);
        }
        lemma_mul_nonnegative(b as int, c - 1);
        assert(0 <= b * c - b);
        calc! { (==)
            pow(a, b * c);
            { }
            pow(a, (b + b * c - b) as nat);
            { lemma_pow_adds(a, b, (b * c - b) as nat); }
            pow(a, b) * pow(a, (b * c - b) as nat);
            { }
            pow(a, b) * pow(a, (b * (c - 1)) as nat);
            { lemma_pow_multiplies(a, b, (c - 1) as nat); }
            pow(a, b) * pow(pow(a, b), (c - 1) as nat);
            { reveal(pow); }
            pow(pow(a, b), c);
        }
    }
}

/// Proof that, for any `a`, `b`, and `c`, `a` to the power of `b * c`
/// is equal to the result of taking `a` to the power of `b`, then
/// taking that to the power of `c`
pub proof fn lemma_pow_multiplies_auto()
    ensures
        forall|b: nat, c: nat| 0 <= #[trigger] (b * c),
        forall|a: int, b: nat, c: nat| #[trigger] pow(pow(a, b), c) == pow(a, b * c),
{
    assert forall|a: int, b: nat, c: nat| #[trigger] pow(pow(a, b), c) == pow(a, b * c) by {
        lemma_pow_multiplies(a, b, c);
    };
}

/// Proof that `a * b` to the power of `e` is equal to the product of
/// `a` to the power of `e` and `b` to the power of `e`
pub proof fn lemma_pow_distributes(a: int, b: int, e: nat)
    ensures
        pow(a * b, e) == pow(a, e) * pow(b, e),
    decreases e,
{
    reveal(pow);
    lemma_mul_basics_auto();
    if e >= 1 {
        calc! { (==)
            pow(a * b, e); { reveal(pow); }
            (a * b) * pow(a * b, (e - 1) as nat);
            { lemma_pow_distributes(a, b, (e - 1) as nat); }
            (a * b) * (pow(a, (e - 1) as nat) * pow(b, (e - 1) as nat));
            { lemma_mul_is_associative_auto();
            lemma_mul_is_commutative_auto();
            assert ((a * b * pow(a, (e - 1) as nat)) * pow(b, (e - 1) as nat)
                == (a * pow(a, (e - 1) as nat) * b) * pow(b, (e - 1) as nat));
            }
            (a * pow(a, (e - 1) as nat)) * (b * pow(b, (e - 1) as nat)); { reveal(pow);}
            pow(a, e) * pow(b, e);
        }
    }
}

/// Proof that, for any `x`, `y`, and `z`, `x * y` to the power of `z`
/// is equal to the product of `x` to the power of `z` and `y` to the
/// power of `z`
pub proof fn lemma_pow_distributes_auto()
    ensures
        forall|x: int, y: nat, z: nat| #[trigger] pow(x * y, z) == pow(x, z) * pow(y as int, z),
{
    // reveal pow();
    assert forall|x: int, y: nat, z: nat| #[trigger]
        pow(x * y, z) == pow(x, z) * pow(y as int, z) by {
        lemma_pow_distributes(x, y as int, z);
    }
}

/// Proof of various useful properties of [`pow`] (exponentiation)
pub proof fn lemma_pow_auto()
    ensures
        forall|x: int| pow(x, 0) == 1,
        forall|x: int| #[trigger] pow(x, 1) == x,
        forall|x: int, y: int| y == 0 ==> #[trigger] pow(x, y as nat) == 1,
        forall|x: int, y: int| y == 1 ==> #[trigger] pow(x, y as nat) == x,
        forall|x: int, y: int| 0 < x && 0 < y ==> x <= #[trigger] (x * y as nat),
        forall|x: int, y: int| 0 < x && 1 < y ==> x < #[trigger] (x * y as nat),
        forall|x: int, y: nat, z: nat| #[trigger] pow(x, y + z) == pow(x, y) * pow(x, z),
        forall|x: int, y: nat, z: nat|
            y >= z ==> #[trigger] pow(x, (y - z) as nat) * pow(x, z) == pow(x, y),
        forall|x: int, y: nat, z: nat| #[trigger] pow(x * y, z) == pow(x, z) * pow(y as int, z),
{
    reveal(pow);
    lemma_pow0_auto();
    lemma_pow1_auto();
    lemma_pow_distributes_auto();
    lemma_pow_adds_auto();
    lemma_pow_sub_add_cancel_auto();
    lemma_mul_auto();
    lemma_mul_increases_auto();
    lemma_mul_strictly_increases_auto();
}

/// Proof that a number greater than 1 raised to a power strictly
/// increases as the power strictly increases. Specifically, given
/// that `b > 1` and `e1 < e2`, we can conclude that `pow(b, e1) <
/// pow(b, e2)`.
pub proof fn lemma_pow_strictly_increases(b: nat, e1: nat, e2: nat)
    requires
        1 < b,
        e1 < e2,
    ensures
        pow(b as int, e1) < pow(b as int, e2),
{
    let f = |e: int| 0 < e ==> pow(b as int, e1) < pow(b as int, (e1 + e) as nat);
    assert forall|i: int| (#[trigger] is_le(0, i) && f(i)) implies f(i + 1) by {
        calc! {(<=)
        pow(b as int, (e1 + i) as nat);
        (<=) {
            lemma_pow_positive(b as int, (e1 + i) as nat);
            lemma_mul_left_inequality(pow(b as int, (e1 + i) as nat), 1, b as int);
        }
        pow(b as int, (e1 + i) as nat) * b;
        (<=) { lemma_pow1(b as int); }
        pow(b as int, (e1 + i) as nat) * pow(b as int, 1);
        (<=)   { lemma_pow_adds(b as int, (e1 + i) as nat, 1nat); }
        pow(b as int, (e1 + i + 1) as nat);
    }
        assert(0 < i ==> pow(b as int, e1) < pow(b as int, (e1 + i) as nat));
        if (i == 0) {
            assert(pow(b as int, e1) < pow(b as int, (e1 + 1) as nat)) by {
                reveal(pow);
                assert(pow(b as int, e1) < b * pow(b as int, e1)) by {
                    // cannot be replaced to lemma_pow_auto()
                    assert(pow(b as int, e1) > 0) by { lemma_pow_positive_auto() };
                    lemma_mul_strictly_increases(b as int, pow(b as int, e1));
                };
            };
        }
        assert(f(i + 1));
    }
    lemma_mul_induction_auto(e2 - e1, f);
}

/// Proof that any number greater than 1 raised to a power strictly
/// increases as the power strictly increases
pub proof fn lemma_pow_strictly_increases_auto()
    ensures
        forall|b: int, e1: nat, e2: nat|
            1 < b && e1 < e2 ==> #[trigger] pow(b, e1) < #[trigger] pow(b, e2),
{
    reveal(pow);
    assert forall|b: int, e1: nat, e2: nat| 1 < b && e1 < e2 implies #[trigger] pow(b, e1)
        < #[trigger] pow(b, e2) by {
        lemma_pow_strictly_increases(b as nat, e1, e2);
    }
}

/// Proof that a positive number raised to a power increases as the
/// power increases. Specifically, since `e1 <= e2`, we know `pow(b,
/// e1) <= pow(b, e2)`.
pub proof fn lemma_pow_increases(b: nat, e1: nat, e2: nat)
    requires
        b > 0,
        e1 <= e2,
    ensures
        pow(b as int, e1) <= pow(b as int, e2),
{
    if e1 != e2 {
        if b > 1 {
            lemma_pow_strictly_increases(b, e1, e2);
        } else {
            lemma1_pow(e1);
            lemma1_pow(e2);
        }
    }
}

/// Proof that a positive number raised to a power increases as the
/// power increases
pub proof fn lemma_pow_increases_auto()
    ensures
        forall|b: int, e1: nat, e2: nat|
            b > 0 && e1 <= e2 ==> #[trigger] pow(b, e1) <= #[trigger] pow(b, e2),
{
    reveal(pow);
    assert forall|b: int, e1: nat, e2: nat| b > 0 && e1 <= e2 implies #[trigger] pow(b, e1)
        <= #[trigger] pow(b, e2) by {
        lemma_pow_increases(b as nat, e1, e2);
    }
}

/// Proof that if an exponentiation result strictly increases when the
/// exponent changes, then the change is an increase. Specifically, if
/// we know `pow(b, e1) < pow(b, e2)`, then we can conclude `e1 < e2`.
pub proof fn lemma_pow_strictly_increases_converse(b: nat, e1: nat, e2: nat)
    requires
        b > 0,
        pow(b as int, e1) < pow(b as int, e2),
    ensures
        e1 < e2,
{
    if e1 >= e2 {
        lemma_pow_increases(b, e2, e1);
        assert(false);
    }
}

/// Proof that if an exponentiation result strictly increases when the
/// exponent changes, then the change is an increase. That is,
/// whenever we know `b > 0` and `pow(b, e1) < pow(b, e2)`, we can
/// conclude `e1 < e2`.
pub proof fn lemma_pow_strictly_increases_converse_auto()
    ensures
        forall|b: nat, e1: nat, e2: nat| b > 0 && pow(b as int, e1) < pow(b as int, e2) ==> e1 < e2,
{
    reveal(pow);
    assert forall|b: nat, e1: nat, e2: nat|
        b > 0 && pow(b as int, e1) < pow(b as int, e2) implies e1 < e2 by {
        lemma_pow_strictly_increases_converse(b, e1, e2);
    }
}

/// Proof that if the exponentiation of a number greater than 1
/// doesn't decrease when the exponent changes, then the change isn't
/// a decrease. Specifically, given that `b > 1` and `pow(b, e1) <=
/// pow(b, e2)`, we can conclude that `e1 <= e2`.
pub proof fn lemma_pow_increases_converse(b: nat, e1: nat, e2: nat)
    requires
        1 < b,
        pow(b as int, e1) <= pow(b as int, e2),
    ensures
        e1 <= e2,
{
    if e1 > e2 {
        lemma_pow_strictly_increases(b, e2, e1);
        assert(false);
    }
}

/// Proof that whenever the exponentiation of a number greater than 1
/// doesn't decrease when the exponent changes, then the change isn't
/// a decrease
pub proof fn lemma_pow_increases_converse_auto()
    ensures
        forall|b: nat, e1: nat, e2: nat|
            1 < b && pow(b as int, e1) <= pow(b as int, e2) ==> e1 <= e2,
{
    assert forall|b: nat, e1: nat, e2: nat|
        1 < b && pow(b as int, e1) <= pow(b as int, e2) implies e1 <= e2 by {
        lemma_pow_increases_converse(b, e1, e2);
    }
}

/// Proof that `(b^(xy))^z = (b^x)^(yz)`, given that `x * y` and `y *
/// z` are nonnegative and `b` is positive
pub proof fn lemma_pull_out_pows(b: nat, x: nat, y: nat, z: nat)
    requires
        b > 0,
    ensures
        0 <= x * y,
        0 <= y * z,
        pow(pow(b as int, x * y), z) == pow(pow(b as int, x), y * z),
{
    lemma_mul_nonnegative(x as int, y as int);
    lemma_mul_nonnegative(y as int, z as int);
    lemma_pow_positive(b as int, x);
    calc! { (==)
        pow(pow(b as int, x * y), z);
        { lemma_pow_multiplies(b as int, x, y); }
        pow(pow(pow(b as int, x), y), z);
        { lemma_pow_multiplies(pow(b as int, x), y, z); }
        pow(pow(b as int, x), y * z);
    }
}

/// Proof that for any `b`, `x`, `y`, and `z` such that `x * y >= 0`
/// and `y * z >= 0` and `b > 0`, we know `(b^(xy))^z = (b^x)^(yz)`
pub proof fn lemma_pull_out_pows_auto()
    ensures
        forall|y: nat, z: nat| 0 <= #[trigger] (z * y) && 0 <= y * z,
        forall|b: nat, x: nat, y: nat, z: nat|
            b > 0 ==> #[trigger] pow(pow(b as int, x * y), z) == pow(pow(b as int, x), y * z),
{
    // reveal(pow);
    lemma_mul_nonnegative_auto();
    assert forall|b: nat, x: nat, y: nat, z: nat| b > 0 implies #[trigger] pow(
        pow(b as int, x * y),
        z,
    ) == pow(pow(b as int, x), y * z) by {
        lemma_pull_out_pows(b, x, y, z);
    }
}

/// Proof that if `e2 <= e1` and `x < pow(b, e1)`, then dividing `x`
/// by `pow(b, e2)` produces a result less than `pow(b, e1 - e2)`
pub proof fn lemma_pow_division_inequality(x: nat, b: nat, e1: nat, e2: nat)
    requires
        b > 0,
        e2 <= e1,
        x < pow(b as int, e1),
    ensures
        pow(b as int, e2) > 0,
        // also somewhat annoying that division operator needs explicit type casting
        // because the divisor and dividend need to have the same type
        x as int / pow(b as int, e2) < pow(b as int, (e1 - e2) as nat),
{
    lemma_pow_positive_auto();
    assert(x as int / pow(b as int, e2) >= pow(b as int, (e1 - e2) as nat) ==> false) by {
        if x as int / pow(b as int, e2) >= pow(b as int, (e1 - e2) as nat) {
            lemma_mul_inequality(
                pow(b as int, (e1 - e2) as nat),
                x as int / pow(b as int, e2),
                pow(b as int, e2),
            );
            lemma_fundamental_div_mod(x as int, pow(b as int, e2));
            lemma_mul_is_commutative_auto();
            lemma_pow_adds(b as int, (e1 - e2) as nat, e2);
            lemma_mod_properties_auto();
        }
    };
}

/// Proof that for all `x`, `b`, `e1`, and `e2` such that `e2 <= e1`
/// and `x < pow(b, e1)`, we know that dividing `x` by `pow(b, e2)`
/// produces a result less than `pow(b, e1 - e2)`
pub proof fn lemma_pow_division_inequality_auto()
    ensures
        forall|b: int, e2: nat| b > 0 && e2 <= e2 ==> pow(b, e2) > 0,
        forall|x: nat, b: int, e1: nat, e2: nat|
            b > 0 && e2 <= e1 && x < pow(b, e1) ==> #[trigger] (x as int / pow(b, e2))
                < #[trigger] pow(b, (sub1(e1 as int, e2 as int)) as nat),
{
    reveal(pow);
    lemma_pow_positive_auto();
    assert forall|x: nat, b: int, e1: nat, e2: nat|
        b > 0 && e2 <= e1 && x < pow(b, e1) implies #[trigger] (x as int / pow(b, e2))
        < #[trigger] pow(b, (sub1(e1 as int, e2 as int)) as nat) by {
        lemma_pow_division_inequality(x, b as nat, e1, e2);
    };
}

/// Proof that `pow(b, e)` modulo `b` is 0
pub proof fn lemma_pow_mod(b: nat, e: nat)
    requires
        b > 0,
        e > 0,
    ensures
        pow(b as int, e) % b as int == 0,
{
    reveal(pow);
    assert(pow(b as int, e) % b as int == (b * pow(b as int, (e - 1) as nat)) % b as int);
    assert((b * pow(b as int, (e - 1) as nat)) % b as int == (pow(b as int, (e - 1) as nat) * b)
        % b as int) by {
        lemma_mul_is_commutative_auto();
    };
    assert((pow(b as int, (e - 1) as nat) * b) % b as int == 0) by {
        lemma_pow_positive_auto();
        lemma_mod_multiples_basic(pow(b as int, (e - 1) as nat), b as int);
    };
    // TODO
    // TO BE DiSCUSSED, suprisingly, the calculational proof saying the same thing does not work
    // calc! {
    // (==)
    // pow(b as int, e) % b as int; {}
    // (b * pow(b as int, (e - 1) as nat)) % b as int;
    // { lemma_mul_is_associative_auto(); }
    // (pow(b as int, (e - 1) as nat) * b) % b as int;
    // {
    //     lemma_pow_positive_auto();
    //     lemma_mod_multiples_basic(pow(b as int, (e - 1) as nat) , b as int);
    // }
    // 0;
    // }
}

/// Proof that for any `b` and `e`, we know `pow(b, e)` modulo `b` is 0
pub proof fn lemma_pow_mod_auto()
    ensures
        forall|b: nat, e: nat| b > 0 && e > 0 ==> #[trigger] pow(b as int, e) % b as int == 0,
{
    assert forall|b: nat, e: nat| b > 0 && e > 0 implies #[trigger] pow(b as int, e) % b as int
        == 0 by {
        lemma_pow_mod(b, e);
    }
}

/// Proof that exponentiation then modulo produces the same result as
/// doing the modulo first, then doing the exponentiation, then doing
/// the modulo again. Specifically, `((b % m)^e) % m == b^e % m`.
pub proof fn lemma_pow_mod_noop(b: int, e: nat, m: int)
    requires
        m > 0,
    ensures
        pow(b % m, e) % m == pow(b, e) % m,
    decreases e,
{
    reveal(pow);
    lemma_mod_properties_auto();
    if e > 0 {
        calc! { (==)
        pow(b % m, e) % m; {}
        ((b % m) * pow(b % m, (e - 1) as nat)) % m;
        { lemma_mul_mod_noop_general(b, pow(b % m, (e - 1) as nat), m); }
        ((b % m) * (pow(b % m, (e - 1) as nat) % m) % m) % m;
        { lemma_pow_mod_noop(b, (e - 1) as nat, m); }
        ((b % m) * (pow(b, (e - 1) as nat) % m) % m) % m;
        { lemma_mul_mod_noop_general(b, pow(b, (e - 1) as nat), m); }
        (b * (pow(b, (e - 1) as nat)) % m) % m; {}
        (b * (pow(b, (e - 1) as nat))) % m; {}
        pow(b, e) % m;
    }
    }
}

/// Proof that exponentiation then modulo produces the same result as
/// doing the modulo first, then doing the exponentiation, then doing
/// the modulo again
pub proof fn lemma_pow_mod_noop_auto()
    ensures
        forall|b: int, e: nat, m: int| m > 0 ==> #[trigger] pow(b % m, e) % m == pow(b, e) % m,
{
    assert forall|b: int, e: nat, m: int| m > 0 implies #[trigger] pow(b % m, e) % m == pow(b, e)
        % m by {
        lemma_pow_mod_noop(b, e, m);
    }
}

} // verus!
    }

    pub mod power2 {
        //! This file contains proofs related to powers of 2. These are part
        //! of the math standard library.
        //!
        //! It's based on the following file from the Dafny math standard library:
        //! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Power2.dfy`.
        //! That file has the following copyright notice:
        //! /*******************************************************************************
        //! *  Original: Copyright (c) Microsoft Corporation
        //! *  SPDX-License-Identifier: MIT
        //! *
        //! *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
        //! *  SPDX-License-Identifier: MIT
        //! *******************************************************************************/
        #[allow(unused_imports)]
        use builtin::*;
        use builtin_macros::*;

        verus! {

#[cfg(verus_keep_ghost)]
use crate::arithmetic::power::{pow, lemma_pow_positive, lemma_pow_auto};
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::mul_internals::lemma_mul_induction_auto;
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::general_internals::is_le;

/// This function computes 2 to the power of the given natural number
/// `e`. It's opaque so that the SMT solver doesn't waste time
/// repeatedly recursively unfolding it.
#[verifier(opaque)]
pub open spec fn pow2(e: nat) -> nat
    decreases
            e  // ensures pow2(e) > 0
            // cannot have ensurs clause in spec functions
            // a workaround is the lemma_pow2_pos below
            ,
{
    // you cannot reveal in a spec function, which cause more reveals clauses
    // for the proof
    // reveal(pow);
    pow(2, e) as nat
}

/// Proof that 2 to the power of any natural number (specifically,
/// `e`) is positive
pub proof fn lemma_pow2_pos(e: nat)
    ensures
        pow2(e) > 0,
{
    reveal(pow2);
    lemma_pow_positive(2, e);
}

/// Proof that 2 to the power of any natural number is positive
pub proof fn lemma_pow2_pos_auto()
    ensures
        forall|e: nat| #[trigger] pow2(e) > 0,
{
    assert forall|e: nat| #[trigger] pow2(e) > 0 by {
        lemma_pow2_pos(e);
    }
}

/// Proof that `pow2(e)` is equivalent to `pow(2, e)`
pub proof fn lemma_pow2(e: nat)
    ensures
        pow2(e) == pow(2, e) as int,
    decreases e,
{
    reveal(pow);
    reveal(pow2);
    if e != 0 {
        lemma_pow2((e - 1) as nat);
    }
}

/// Proof that `pow2(e)` is equivalent to `pow(2, e)` for all `e`
pub proof fn lemma_pow2_auto()
    ensures
        forall|e: nat| #[trigger] pow2(e) == pow(2, e),
{
    assert forall|e: nat| #[trigger] pow2(e) == pow(2, e) by {
        lemma_pow2(e);
    }
}

/// Proof that, for the given positive number `e`, `(2^e - 1) / 2 == 2^(e - 1) - 1`
pub proof fn lemma_pow2_mask_div2(e: nat)
    requires
        0 < e,
    ensures
        (pow2(e) - 1) / 2 == pow2((e - 1) as nat) - 1,
{
    let f = |e: int| 0 < e ==> (pow2(e as nat) - 1) / 2 == pow2((e - 1) as nat) - 1;
    assert forall|i: int| #[trigger] is_le(0, i) && f(i) implies f(i + 1) by {
        lemma_pow_auto();
        lemma_pow2_auto();
    };
    lemma_mul_induction_auto(e as int, f);
}

/// Proof that, for any positive number `e`, `(2^e - 1) / 2 == 2^(e - 1) - 1`
pub proof fn lemma_pow2_mask_div2_auto()
    ensures
        forall|e: nat| #![trigger pow2(e)] 0 < e ==> (pow2(e) - 1) / 2 == pow2((e - 1) as nat) - 1,
{
    reveal(pow2);
    assert forall|e: nat| 0 < e implies (#[trigger] (pow2(e)) - 1) / 2 == pow2((e - 1) as nat)
        - 1 by {
        lemma_pow2_mask_div2(e);
    }
}

/// Proof establishing the concrete values for all powers of 2 from 0 to 32 and also 2^64
pub proof fn lemma2_to64()
    ensures
        pow2(0) == 0x1,
        pow2(1) == 0x2,
        pow2(2) == 0x4,
        pow2(3) == 0x8,
        pow2(4) == 0x10,
        pow2(5) == 0x20,
        pow2(6) == 0x40,
        pow2(7) == 0x80,
        pow2(8) == 0x100,
        pow2(9) == 0x200,
        pow2(10) == 0x400,
        pow2(11) == 0x800,
        pow2(12) == 0x1000,
        pow2(13) == 0x2000,
        pow2(14) == 0x4000,
        pow2(15) == 0x8000,
        pow2(16) == 0x10000,
        pow2(17) == 0x20000,
        pow2(18) == 0x40000,
        pow2(19) == 0x80000,
        pow2(20) == 0x100000,
        pow2(21) == 0x200000,
        pow2(22) == 0x400000,
        pow2(23) == 0x800000,
        pow2(24) == 0x1000000,
        pow2(25) == 0x2000000,
        pow2(26) == 0x4000000,
        pow2(27) == 0x8000000,
        pow2(28) == 0x10000000,
        pow2(29) == 0x20000000,
        pow2(30) == 0x40000000,
        pow2(31) == 0x80000000,
        pow2(32) == 0x100000000,
        pow2(64) == 0x10000000000000000,
{
    reveal(pow2);
    reveal(pow);
    #[verusfmt::skip]
    assert(
        pow2(0) == 0x1 &&
        pow2(1) == 0x2 &&
        pow2(2) == 0x4 &&
        pow2(3) == 0x8 &&
        pow2(4) == 0x10 &&
        pow2(5) == 0x20 &&
        pow2(6) == 0x40 &&
        pow2(7) == 0x80 &&
        pow2(8) == 0x100 &&
        pow2(9) == 0x200 &&
        pow2(10) == 0x400 &&
        pow2(11) == 0x800 &&
        pow2(12) == 0x1000 &&
        pow2(13) == 0x2000 &&
        pow2(14) == 0x4000 &&
        pow2(15) == 0x8000 &&
        pow2(16) == 0x10000 &&
        pow2(17) == 0x20000 &&
        pow2(18) == 0x40000 &&
        pow2(19) == 0x80000 &&
        pow2(20) == 0x100000 &&
        pow2(21) == 0x200000 &&
        pow2(22) == 0x400000 &&
        pow2(23) == 0x800000 &&
        pow2(24) == 0x1000000 &&
        pow2(25) == 0x2000000 &&
        pow2(26) == 0x4000000 &&
        pow2(27) == 0x8000000 &&
        pow2(28) == 0x10000000 &&
        pow2(29) == 0x20000000 &&
        pow2(30) == 0x40000000 &&
        pow2(31) == 0x80000000 &&
        pow2(32) == 0x100000000 &&
        pow2(64) == 0x10000000000000000
    ) by(compute_only);
}

} // verus!
    }
}

pub mod array {
    #![allow(unused_imports)]
    use crate::seq::*;
    use builtin::*;
    use builtin_macros::*;

    verus! {

pub trait ArrayAdditionalSpecFns<T> {
    spec fn view(&self) -> Seq<T>;

    spec fn spec_index(&self, i: int) -> T
        recommends
            0 <= i < self.view().len(),
    ;
}

#[verifier::external]
pub trait ArrayAdditionalExecFns<T> {
    fn set(&mut self, idx: usize, t: T);
}

impl<T, const N: usize> ArrayAdditionalSpecFns<T> for [T; N] {
    spec fn view(&self) -> Seq<T>;

    #[verifier(inline)]
    open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
}

impl<T, const N: usize> ArrayAdditionalExecFns<T> for [T; N] {
    #[verifier::external_body]
    fn set(&mut self, idx: usize, t: T)
        requires
            0 <= idx < N,
        ensures
            self@ == old(self)@.update(idx as int, t),
    {
        self[idx] = t;
    }
}

#[verifier(external_body)]
pub exec fn array_index_get<T, const N: usize>(ar: &[T; N], i: usize) -> (out: &T)
    requires
        0 <= i < N,
    ensures
        *out == ar@.index(i as int),
{
    &ar[i]
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn array_len_matches_n<T, const N: usize>(ar: &[T; N])
    ensures
        (#[trigger] ar@.len()) == N,
{
}

// Referenced by Verus' internal encoding for array literals
#[doc(hidden)]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "vstd::array::array_index")]
pub open spec fn array_index<T, const N: usize>(ar: &[T; N], i: int) -> T {
    ar.view().index(i)
}

} // verus!
}

pub mod atomic {
    #![allow(unused_imports)]

    use core::sync::atomic::{
        AtomicBool, AtomicI16, AtomicI32, AtomicI64, AtomicI8, AtomicIsize, AtomicU16, AtomicU32,
        AtomicU64, AtomicU8, AtomicUsize, Ordering,
    };

    use crate::modes::*;
    use crate::pervasive::*;
    use builtin::*;
    use builtin_macros::*;

    macro_rules! make_unsigned_integer_atomic {
        ($at_ident:ident, $p_ident:ident, $p_data_ident:ident, $rust_ty: ty, $value_ty: ty, $wrap_add:ident, $wrap_sub:ident) => {
            // TODO we could support `std::intrinsics::wrapping_add`
            // and use that instead.

            verus! {

        pub open spec fn $wrap_add(a: int, b: int) -> int {
            if a + b > (<$value_ty>::MAX as int) {
                a + b - ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
            } else {
                a + b
            }
        }

        pub open spec fn $wrap_sub(a: int, b: int) -> int {
            if a - b < (<$value_ty>::MIN as int) {
                a - b + ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
            } else {
                a - b
            }
        }

        } // verus!
            atomic_types!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty);
            #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))]
            impl $at_ident {
                atomic_common_methods!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty);
                atomic_integer_methods!(
                    $at_ident, $p_ident, $rust_ty, $value_ty, $wrap_add, $wrap_sub
                );
            }
        };
    }

    macro_rules! make_signed_integer_atomic {
        ($at_ident:ident, $p_ident:ident, $p_data_ident:ident, $rust_ty: ty, $value_ty: ty, $wrap_add:ident, $wrap_sub:ident) => {
            verus! {

        pub open spec fn $wrap_add(a: int, b: int) -> int {
            if a + b > (<$value_ty>::MAX as int) {
                a + b - ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
            } else if a + b < (<$value_ty>::MIN as int) {
                a + b + ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
            } else {
                a + b
            }
        }

        pub open spec fn $wrap_sub(a: int, b: int) -> int {
            if a - b > (<$value_ty>::MAX as int) {
                a - b - ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
            } else if a - b < (<$value_ty>::MIN as int) {
                a - b + ((<$value_ty>::MAX as int) - (<$value_ty>::MIN as int) + 1)
            } else {
                a - b
            }
        }

        } // verus!
            atomic_types!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty);
            #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))]
            impl $at_ident {
                atomic_common_methods!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty);
                atomic_integer_methods!(
                    $at_ident, $p_ident, $rust_ty, $value_ty, $wrap_add, $wrap_sub
                );
            }
        };
    }

    macro_rules! make_bool_atomic {
        ($at_ident:ident, $p_ident:ident, $p_data_ident:ident, $rust_ty: ty, $value_ty: ty) => {
            atomic_types!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty);
            #[cfg_attr(verus_keep_ghost, verus::internal(verus_macro))]
            impl $at_ident {
                atomic_common_methods!($at_ident, $p_ident, $p_data_ident, $rust_ty, $value_ty);
                atomic_bool_methods!($at_ident, $p_ident, $rust_ty, $value_ty);
            }
        };
    }

    macro_rules! atomic_types {
        ($at_ident:ident, $p_ident:ident, $p_data_ident:ident, $rust_ty: ty, $value_ty: ty) => {
            verus! {

        #[verifier::external_body] /* vattr */
        pub struct $at_ident {
            ato: $rust_ty,
        }

        #[verifier::external_body] /* vattr */
        pub tracked struct $p_ident {
            no_copy: NoCopy,
        }

        pub ghost struct $p_data_ident {
            pub patomic: int,
            pub value: $value_ty,
        }

        impl $p_ident {
            #[verifier::external_body] /* vattr */
            pub spec fn view(self) -> $p_data_ident;

            pub open spec fn is_for(&self, patomic: $at_ident) -> bool {
                self.view().patomic == patomic.id()
            }

            pub open spec fn points_to(&self, v: $value_ty) -> bool {
                self.view().value == v
            }
        }

        }
        };
    }

    macro_rules! atomic_common_methods {
        ($at_ident:ident, $p_ident:ident, $p_data_ident:ident, $rust_ty: ty, $value_ty: ty) => {
            verus!{

        pub spec fn id(&self) -> int;

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        pub const fn new(i: $value_ty) -> (res: ($at_ident, Tracked<$p_ident>))
            ensures
                equal(res.1@.view(), $p_data_ident{ patomic: res.0.id(), value: i }),
        {
            let p = $at_ident { ato: <$rust_ty>::new(i) };
            (p, Tracked::assume_new())
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn load(&self, Tracked(perm): Tracked<&$p_ident>) -> (ret: $value_ty)
            requires
                equal(self.id(), perm.view().patomic),
            ensures equal(perm.view().value, ret),
            opens_invariants none
        {
            return self.ato.load(Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn store(&self, Tracked(perm): Tracked<&mut $p_ident>, v: $value_ty)
            requires
                equal(self.id(), old(perm).view().patomic),
            ensures equal(perm.view().value, v) && equal(self.id(), perm.view().patomic),
            opens_invariants none
        {
            self.ato.store(v, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn compare_exchange(&self, Tracked(perm): Tracked<&mut $p_ident>, current: $value_ty, new: $value_ty) -> (ret: Result<$value_ty, $value_ty>)
            requires
                equal(self.id(), old(perm).view().patomic),
            ensures
                equal(self.id(), perm.view().patomic)
                && match ret {
                    Result::Ok(r) =>
                           current == old(perm).view().value
                        && equal(perm.view().value, new)
                        && equal(r, old(perm).view().value),
                    Result::Err(r) =>
                           current != old(perm).view().value
                        && equal(perm.view().value, old(perm).view().value)
                        && equal(r, old(perm).view().value),
                },
            opens_invariants none
        {
            match self.ato.compare_exchange(current, new, Ordering::SeqCst, Ordering::SeqCst) {
                Ok(x) => Result::Ok(x),
                Err(x) => Result::Err(x),
            }
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn compare_exchange_weak(&self, Tracked(perm): Tracked<&mut $p_ident>, current: $value_ty, new: $value_ty) -> (ret: Result<$value_ty, $value_ty>)
            requires
                equal(self.id(), old(perm).view().patomic),
            ensures
                equal(self.id(), perm.view().patomic)
                && match ret {
                    Result::Ok(r) =>
                           current == old(perm).view().value
                        && equal(perm.view().value, new)
                        && equal(r, old(perm).view().value),
                    Result::Err(r) =>
                           equal(perm.view().value, old(perm).view().value)
                        && equal(r, old(perm).view().value),
                },
            opens_invariants none
        {
            match self.ato.compare_exchange_weak(current, new, Ordering::SeqCst, Ordering::SeqCst) {
                Ok(x) => Result::Ok(x),
                Err(x) => Result::Err(x),
            }
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn swap(&self, Tracked(perm): Tracked<&mut $p_ident>, v: $value_ty) -> (ret: $value_ty)
            requires
                equal(self.id(), old(perm).view().patomic),
            ensures
                   equal(perm.view().value, v)
                && equal(old(perm).view().value, ret)
                && equal(self.id(), perm.view().patomic),
            opens_invariants none
        {
            return self.ato.swap(v, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        pub fn into_inner(self, Tracked(perm): Tracked<$p_ident>) -> (ret: $value_ty)
            requires
                equal(self.id(), perm.view().patomic),
            ensures equal(perm.view().value, ret),
            opens_invariants none
        {
            return self.ato.into_inner();
        }

        }
        };
    }

    macro_rules! atomic_integer_methods {
        ($at_ident:ident, $p_ident:ident, $rust_ty: ty, $value_ty: ty, $wrap_add:ident, $wrap_sub:ident) => {
            verus!{

        // Note that wrapping-on-overflow is the defined behavior for fetch_add and fetch_sub
        // for Rust's atomics (in contrast to ordinary arithmetic)

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_add_wrapping(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value as int == $wrap_add(old(perm).view().value as int, n as int),
            opens_invariants none
        {
            return self.ato.fetch_add(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_sub_wrapping(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value as int == $wrap_sub(old(perm).view().value as int, n as int),
            opens_invariants none
        {
            return self.ato.fetch_sub(n, Ordering::SeqCst);
        }

        // fetch_add and fetch_sub are more natural in the common case that you
        // don't expect wrapping

        #[inline(always)]
        #[verifier::atomic] /* vattr */
        pub fn fetch_add(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires
                equal(self.id(), old(perm).view().patomic),
                (<$value_ty>::MIN as int) <= old(perm).view().value + n,
                old(perm).view().value + n <= (<$value_ty>::MAX as int),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == old(perm).view().value + n,
            opens_invariants none
        {
            self.fetch_add_wrapping(Tracked(&mut *perm), n)
        }

        #[inline(always)]
        #[verifier::atomic] /* vattr */
        pub fn fetch_sub(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires
                equal(self.id(), old(perm).view().patomic),
                (<$value_ty>::MIN as int) <= old(perm).view().value - n,
                old(perm).view().value - n <= <$value_ty>::MAX as int,
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == old(perm).view().value - n,
            opens_invariants none
        {
            self.fetch_sub_wrapping(Tracked(&mut *perm), n)
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_and(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == (old(perm).view().value & n),
            opens_invariants none
        {
            return self.ato.fetch_and(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_or(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == (old(perm).view().value | n),
            opens_invariants none
        {
            return self.ato.fetch_or(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_xor(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == (old(perm).view().value ^ n),
            opens_invariants none
        {
            return self.ato.fetch_xor(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_nand(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == !(old(perm).view().value & n),
            opens_invariants none
        {
            return self.ato.fetch_nand(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_max(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == (if old(perm).view().value > n { old(perm).view().value } else { n }),
            opens_invariants none
        {
            return self.ato.fetch_max(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_min(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret),
                perm.view().patomic == old(perm).view().patomic,
                perm.view().value == (if old(perm).view().value < n { old(perm).view().value } else { n }),
            opens_invariants none
        {
            return self.ato.fetch_min(n, Ordering::SeqCst);
        }

        }
        };
    }

    macro_rules! atomic_bool_methods {
        ($at_ident:ident, $p_ident:ident, $rust_ty: ty, $value_ty: ty) => {
            verus!{

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_and(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires
                equal(self.id(), old(perm).view().patomic),
            ensures
                   equal(old(perm).view().value, ret)
                && perm.view().patomic == old(perm).view().patomic
                && perm.view().value == (old(perm).view().value && n),
            opens_invariants none
        {
            return self.ato.fetch_and(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_or(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires
                equal(self.id(), old(perm).view().patomic),
            ensures
                  equal(old(perm).view().value, ret)
                && perm.view().patomic == old(perm).view().patomic
                && perm.view().value == (old(perm).view().value || n),
            opens_invariants none
        {
            return self.ato.fetch_or(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_xor(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires
                equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret)
                && perm.view().patomic == old(perm).view().patomic
                && perm.view().value == ((old(perm).view().value && !n) || (!old(perm).view().value && n)),
            opens_invariants none
        {
            return self.ato.fetch_xor(n, Ordering::SeqCst);
        }

        #[inline(always)]
        #[verifier::external_body] /* vattr */
        #[verifier::atomic] /* vattr */
        pub fn fetch_nand(&self, Tracked(perm): Tracked<&mut $p_ident>, n: $value_ty) -> (ret: $value_ty)
            requires
                equal(self.id(), old(perm).view().patomic),
            ensures
                equal(old(perm).view().value, ret)
                && perm.view().patomic == old(perm).view().patomic
                && perm.view().value == !(old(perm).view().value && n),
            opens_invariants none
        {
            return self.ato.fetch_nand(n, Ordering::SeqCst);
        }

        }
        };
    }

    make_bool_atomic!(
        PAtomicBool,
        PermissionBool,
        PermissionDataBool,
        AtomicBool,
        bool
    );

    make_unsigned_integer_atomic!(
        PAtomicU8,
        PermissionU8,
        PermissionDataU8,
        AtomicU8,
        u8,
        wrapping_add_u8,
        wrapping_sub_u8
    );
    make_unsigned_integer_atomic!(
        PAtomicU16,
        PermissionU16,
        PermissionDataU16,
        AtomicU16,
        u16,
        wrapping_add_u16,
        wrapping_sub_u16
    );
    make_unsigned_integer_atomic!(
        PAtomicU32,
        PermissionU32,
        PermissionDataU32,
        AtomicU32,
        u32,
        wrapping_add_u32,
        wrapping_sub_u32
    );
    make_unsigned_integer_atomic!(
        PAtomicU64,
        PermissionU64,
        PermissionDataU64,
        AtomicU64,
        u64,
        wrapping_add_u64,
        wrapping_sub_u64
    );
    make_unsigned_integer_atomic!(
        PAtomicUsize,
        PermissionUsize,
        PermissionDataUsize,
        AtomicUsize,
        usize,
        wrapping_add_usize,
        wrapping_sub_usize
    );

    make_signed_integer_atomic!(
        PAtomicI8,
        PermissionI8,
        PermissionDataI8,
        AtomicI8,
        i8,
        wrapping_add_i8,
        wrapping_sub_i8
    );
    make_signed_integer_atomic!(
        PAtomicI16,
        PermissionI16,
        PermissionDataI16,
        AtomicI16,
        i16,
        wrapping_add_i16,
        wrapping_sub_i16
    );
    make_signed_integer_atomic!(
        PAtomicI32,
        PermissionI32,
        PermissionDataI32,
        AtomicI32,
        i32,
        wrapping_add_i32,
        wrapping_sub_i32
    );
    make_signed_integer_atomic!(
        PAtomicI64,
        PermissionI64,
        PermissionDataI64,
        AtomicI64,
        i64,
        wrapping_add_i64,
        wrapping_sub_i64
    );
    make_signed_integer_atomic!(
        PAtomicIsize,
        PermissionIsize,
        PermissionDataIsize,
        AtomicIsize,
        isize,
        wrapping_add_isize,
        wrapping_sub_isize
    );

    // TODO Support AtomicPtr
}

pub mod atomic_ghost {
    //! Provides sequentially-consistent atomic memory locations with associated ghost state.
    //! See the [`atomic_with_ghost!`] documentation for more information.
    #![allow(unused_imports)]

    use crate::atomic::*;
    use crate::invariant::*;
    use crate::modes::*;
    use builtin::*;
    use builtin_macros::*;

    verus! {

pub trait AtomicInvariantPredicate<K, V, G> {
    spec fn atomic_inv(k: K, v: V, g: G) -> bool;
}

} // verus!
    macro_rules! declare_atomic_type {
        ($at_ident:ident, $patomic_ty:ident, $perm_ty:ty, $value_ty: ty, $atomic_pred_ty: ident) => {
            verus!{

        pub struct $atomic_pred_ty<Pred> { p: Pred }

        impl<K, G, Pred> InvariantPredicate<(K, int), ($perm_ty, G)> for $atomic_pred_ty<Pred>
            where Pred: AtomicInvariantPredicate<K, $value_ty, G>
        {
            open spec fn inv(k_loc: (K, int), perm_g: ($perm_ty, G)) -> bool {
                let (k, loc) = k_loc;
                let (perm, g) = perm_g;

                perm.view().patomic == loc
                  && Pred::atomic_inv(k, perm.view().value, g)
            }
        }

        #[doc = concat!(
            "Sequentially-consistent atomic memory location storing a `",
            stringify!($value_ty),
            "` and associated ghost state."
        )]
        ///
        /// See the [`atomic_with_ghost!`] documentation for usage information.

        pub struct $at_ident<K, G, Pred>
            //where Pred: AtomicInvariantPredicate<K, $value_ty, G>
        {
            #[doc(hidden)]
            pub patomic: $patomic_ty,

            #[doc(hidden)]
            pub atomic_inv: Tracked<AtomicInvariant<(K, int), ($perm_ty, G), $atomic_pred_ty<Pred>>>,
        }

        impl<K, G, Pred> $at_ident<K, G, Pred>
            where Pred: AtomicInvariantPredicate<K, $value_ty, G>
        {
            pub open spec fn well_formed(&self) -> bool {
                self.atomic_inv@.constant().1 == self.patomic.id()
            }

            pub open spec fn constant(&self) -> K {
                self.atomic_inv@.constant().0
            }

            #[inline(always)]
            pub const fn new(Ghost(k): Ghost<K>, u: $value_ty, Tracked(g): Tracked<G>) -> (t: Self)
                requires Pred::atomic_inv(k, u, g),
                ensures t.well_formed() && t.constant() == k,
            {

                let (patomic, Tracked(perm)) = $patomic_ty::new(u);

                let tracked pair = (perm, g);
                let tracked atomic_inv = AtomicInvariant::new(
                    (k, patomic.id()), pair, 0);

                $at_ident {
                    patomic,
                    atomic_inv: Tracked(atomic_inv),
                }
            }

            #[inline(always)]
            pub fn load(&self) -> $value_ty
                requires self.well_formed(),
            {
                atomic_with_ghost!(self => load(); g => { })
            }

            // TODO into_inner

            /*
            #[inline(always)]
            pub fn into_inner(self) -> ($value_ty, G) {
                requires(self.well_formed());
                ensures(|res: ($value_ty, G)| {
                    let (v, g) = res;
                    Pred::atomic_inv(self.constant(), v, g)
                });

                let { patomic, atomic_inv } = self;
                let (perm, g) = atomic_inv.into_inner();
                let v = patomic.into_inner(perm);
                (v, g)
            }
            */
        }

        }
        };
    }

    declare_atomic_type!(AtomicU64, PAtomicU64, PermissionU64, u64, AtomicPredU64);
    declare_atomic_type!(AtomicU32, PAtomicU32, PermissionU32, u32, AtomicPredU32);
    declare_atomic_type!(AtomicU16, PAtomicU16, PermissionU16, u16, AtomicPredU16);
    declare_atomic_type!(AtomicU8, PAtomicU8, PermissionU8, u8, AtomicPredU8);
    declare_atomic_type!(
        AtomicUsize,
        PAtomicUsize,
        PermissionUsize,
        usize,
        AtomicPredUsize
    );

    declare_atomic_type!(AtomicI64, PAtomicI64, PermissionI64, i64, AtomicPredI64);
    declare_atomic_type!(AtomicI32, PAtomicI32, PermissionI32, i32, AtomicPredI32);
    declare_atomic_type!(AtomicI16, PAtomicI16, PermissionI16, i16, AtomicPredI16);
    declare_atomic_type!(AtomicI8, PAtomicI8, PermissionI8, i8, AtomicPredI8);
    declare_atomic_type!(
        AtomicIsize,
        PAtomicIsize,
        PermissionIsize,
        isize,
        AtomicPredIsize
    );

    declare_atomic_type!(
        AtomicBool,
        PAtomicBool,
        PermissionBool,
        bool,
        AtomicPredBool
    );

    /// Performs a given atomic operation on a given atomic
    /// while providing access to its ghost state.
    ///
    /// `atomic_with_ghost!` supports the types
    /// [`AtomicU64`] [`AtomicU32`], [`AtomicU16`], [`AtomicU8`],
    /// [`AtomicI64`], [`AtomicI32`], [`AtomicI16`], [`AtomicI8`], and [`AtomicBool`].
    ///
    /// For each type, it supports all applicable atomic operations among
    /// `load`, `store`, `swap`, `compare_exchange`, `compare_exchange_weak`,
    /// `fetch_add`, `fetch_add_wrapping`, `fetch_sub`, `fetch_sub_wrapping`,
    /// `fetch_or`, `fetch_and`, `fetch_xor`, `fetch_nand`, `fetch_max`, and `fetch_min`.
    ///
    /// Naturally, `AtomicBool` does not support the arithmetic-specific operations.
    ///
    /// In general, the syntax is:
    ///
    ///     let result = atomic_with_ghost!(
    ///         $atomic => $operation_name($operands...);
    ///         update $prev -> $next;         // `update` line is optional
    ///         returning $ret;                // `returning` line is optional
    ///         ghost $g => {
    ///             /* Proof code with access to `tracked` variable `g: G` */
    ///         }
    ///     );
    ///
    /// Here, the `$operation_name` is one of `load`, `store`, etc. Meanwhile,
    /// `$prev`, `$next`, and `$ret` are all identifiers which
    /// will be available as spec variable inside the block to describe the
    /// atomic action which is performed.
    ///
    /// For example, suppose the user performs `fetch_add(1)`. The atomic
    /// operation might load the value 5, add 1, store the value 6,
    /// and return the original value, 5. In that case, we would have
    /// `prev == 5`, `next == 6`, and `ret == 5`.
    ///
    /// The specification for a given operation is given as a relation between
    /// `prev`, `next`, and `ret`; that is, at the beginning of the proof block,
    /// the user may assume the given specification holds:
    ///
    /// | operation                     | specification                                                                                                              |
    /// |-------------------------------|----------------------------------------------------------------------------------------------------------------------------|
    /// | `load()`                      | `next == prev && rev == prev`                                                                                              |
    /// | `store(x)`                    | `next == x && ret == ()`                                                                                                   |
    /// | `swap(x)`                     | `next == x && ret == prev`                                                                                                 |
    /// | `compare_exchange(x, y)`      | `prev == x && next == y && ret == Ok(prev)` ("success") OR<br> `prev != x && next == prev && ret == Err(prev)` ("failure") |
    /// | `compare_exchange_weak(x, y)` | `prev == x && next == y && ret == Ok(prev)` ("success") OR<br> `next == prev && ret == Err(prev)` ("failure")              |
    /// | `fetch_add(x)` (*)            | `next == prev + x && ret == prev`                                                                                          |
    /// | `fetch_add_wrapping(x)`       | `next == wrapping_add(prev, x) && ret == prev`                                                                             |
    /// | `fetch_sub(x)` (*)            | `next == prev - x && ret == prev`                                                                                          |
    /// | `fetch_sub_wrapping(x)`       | `next == wrapping_sub(prev, x) && ret == prev`                                                                             |
    /// | `fetch_or(x)`                 | <code>next == prev \| x && ret == prev</code>                                                                              |
    /// | `fetch_and(x)`                | `next == prev & x && ret == prev`                                                                                          |
    /// | `fetch_xor(x)`                | `next == prev ^ x && ret == prev`                                                                                          |
    /// | `fetch_nand(x)`               | `next == !(prev & x) && ret == prev`                                                                                       |
    /// | `fetch_max(x)`                | `next == max(prev, x) && ret == prev`                                                                                      |
    /// | `fetch_min(x)`                | `next == max(prev, x) && ret == prev`                                                                                      |
    /// | `no_op()` (**)                | `next == prev && ret == ()`                                                                                                |
    ///
    /// (*) Note that `fetch_add` and `fetch_sub` do not specify
    /// wrapping-on-overflow; instead, they require the user to
    /// prove that overflow _does not occur_, i.e., the user must show
    /// that `next` is in bounds for the integer type in question.
    /// Furthermore, for `fetch_add` and `fetch_sub`, the spec values of
    /// `prev`, `next`, and `ret` are all given with type `int`, so the
    /// user may reason about boundedness within the proof block.
    ///
    /// (As executable code, `fetch_add` is equivalent to `fetch_add_wrapping`,
    /// and likewise for `fetch_sub` and `fetch_sub_wrapping`.
    /// We have both because it's frequently the case that the user needs to verify
    /// lack-of-overflow _anyway_, and having it as an explicit precondition by default
    /// then makes verification errors easier to diagnose. Furthermore, when overflow is
    /// intended, the wrapping operations document that intent.)
    ///
    /// (**) `no_op` is entirely a ghost operation and doesn't emit any actual instruction.
    /// This allows the user to access the ghost state and the stored value (as `spec` data)
    /// without actually performing a load.
    ///
    /// ---
    ///
    /// At the beginning of the proof block, the user may assume, in addition
    /// to the specified relation between `prev`, `next`, and `ret`, that
    /// `atomic.inv(prev, g)` holds. The user is required to update `g` such that
    /// `atomic.inv(next, g)` holds at the end of the block.
    /// In other words, the ghost block has the implicit pre- and post-conditions:
    ///
    ///     let result = atomic_with_ghost!(
    ///         $atomic => $operation_name($operands...);
    ///         update $prev -> $next;
    ///         returning $ret;
    ///         ghost $g => {
    ///             assume(specified relation on (prev, next, ret));
    ///             assume(atomic.inv(prev, g));
    ///
    ///             // User code here; may update variable `g` with full
    ///             // access to variables in the outer context.
    ///
    ///             assert(atomic.inv(next, g));
    ///         }
    ///     );
    ///
    /// Note that the necessary action on ghost state might depend
    /// on the result of the operation; for example, if the user performs a
    /// compare-and-swap, then the ghost action that they then need to do
    /// will probably depend on whether the operation succeeded or not.
    ///
    /// The value returned by the `atomic_with_ghost!(...)` expression will be equal
    /// to `ret`, although the return value is an `exec` value (the actual result of
    /// the operation) while `ret` is a `spec` value.
    ///
    /// ### Example (TODO)

    #[macro_export]
    macro_rules! atomic_with_ghost {
    ($($tokens:tt)*) => {
        // The helper is used to parse things using Verus syntax
        // The helper then calls atomic_with_ghost_inner, below:
        ::builtin_macros::atomic_with_ghost_helper!(
            $crate::atomic_ghost::atomic_with_ghost_inner,
            $($tokens)*)
    }
}

    pub use atomic_with_ghost;

    #[doc(hidden)]
    #[macro_export]
    macro_rules! atomic_with_ghost_inner {
        (load, $e:expr, (), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
            $crate::atomic_ghost::atomic_with_ghost_load!($e, $prev, $next, $ret, $g, $b)
        };
        (store, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
            $crate::atomic_ghost::atomic_with_ghost_store!($e, $operand, $prev, $next, $ret, $g, $b)
        };
        (swap, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
            $crate::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
                swap, $e, $operand, $prev, $next, $ret, $g, $b
            )
        };

        (fetch_or, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
            $crate::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
                fetch_or, $e, $operand, $prev, $next, $ret, $g, $b
            )
        };
        (fetch_and, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
            $crate::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
                fetch_and, $e, $operand, $prev, $next, $ret, $g, $b
            )
        };
        (fetch_xor, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
            $crate::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
                fetch_xor, $e, $operand, $prev, $next, $ret, $g, $b
            )
        };
        (fetch_nand, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
            $crate::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
                fetch_nand, $e, $operand, $prev, $next, $ret, $g, $b
            )
        };
        (fetch_max, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
            $crate::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
                fetch_max, $e, $operand, $prev, $next, $ret, $g, $b
            )
        };
        (fetch_min, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
            $crate::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
                fetch_min, $e, $operand, $prev, $next, $ret, $g, $b
            )
        };
        (fetch_add_wrapping, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
            $crate::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
                fetch_add_wrapping,
                $e,
                $operand,
                $prev,
                $next,
                $ret,
                $g,
                $b
            )
        };
        (fetch_sub_wrapping, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
            $crate::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
                fetch_sub_wrapping,
                $e,
                $operand,
                $prev,
                $next,
                $ret,
                $g,
                $b
            )
        };

        (fetch_add, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
            $crate::atomic_ghost::atomic_with_ghost_update_fetch_add!(
                $e, $operand, $prev, $next, $ret, $g, $b
            )
        };
        (fetch_sub, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
            $crate::atomic_ghost::atomic_with_ghost_update_fetch_sub!(
                $e, $operand, $prev, $next, $ret, $g, $b
            )
        };

        (compare_exchange, $e:expr, ($operand1:expr, $operand2:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
            $crate::atomic_ghost::atomic_with_ghost_update_with_2_operand!(
                compare_exchange,
                $e,
                $operand1,
                $operand2,
                $prev,
                $next,
                $ret,
                $g,
                $b
            )
        };
        (compare_exchange_weak, $e:expr, ($operand1:expr, $operand2:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
            $crate::atomic_ghost::atomic_with_ghost_update_with_2_operand!(
                compare_exchange_weak,
                $e,
                $operand1,
                $operand2,
                $prev,
                $next,
                $ret,
                $g,
                $b
            )
        };
        (no_op, $e:expr, (), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
            $crate::atomic_ghost::atomic_with_ghost_no_op!($e, $prev, $next, $ret, $g, $b)
        };
    }

    pub use atomic_with_ghost_inner;

    #[doc(hidden)]
    #[macro_export]
    macro_rules! atomic_with_ghost_store {
        ($e:expr, $operand:expr, $prev:pat, $next:pat, $res:pat, $g:ident, $b:block) => {
            ::builtin_macros::verus_exec_expr! { {
                let atomic = &($e);
                $crate::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                    #[allow(unused_mut)]
                    let tracked (mut perm, mut $g) = pair;
                    let ghost $prev = perm.view().value;
                    atomic.patomic.store(Tracked(&mut perm), $operand);
                    let ghost $next = perm.view().value;
                    let ghost $res = ();

                    proof { $b }

                    proof { pair = (perm, $g); }
                });
            } }
        };
    }
    pub use atomic_with_ghost_store;

    #[doc(hidden)]
    #[macro_export]
    macro_rules! atomic_with_ghost_load {
        ($e:expr, $prev:pat, $next: pat, $res: pat, $g:ident, $b:block) => {
            ::builtin_macros::verus_exec_expr! { {
                let result;
                let atomic = &($e);
                $crate::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                    #[allow(unused_mut)]
                    let tracked (perm, mut $g) = pair;
                    result = atomic.patomic.load(Tracked(&perm));
                    let ghost $res = result;
                    let ghost $prev = result;
                    let ghost $next = result;

                    proof { $b }

                    proof { pair = (perm, $g); }
                });
                result
            } }
        };
    }

    pub use atomic_with_ghost_load;

    #[doc(hidden)]
    #[macro_export]
    macro_rules! atomic_with_ghost_no_op {
        ($e:expr, $prev:pat, $next: pat, $res: pat, $g:ident, $b:block) => {
            ::builtin_macros::verus_exec_expr! { {
                let atomic = &($e);
                $crate::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                    #[allow(unused_mut)]
                    let tracked (perm, mut $g) = pair;
                    let ghost $res = result;
                    let ghost $prev = result;
                    let ghost $next = result;

                    proof { $b }

                    proof { pair = (perm, $g); }
                });
            } }
        };
    }

    pub use atomic_with_ghost_no_op;

    #[doc(hidden)]
    #[macro_export]
    macro_rules! atomic_with_ghost_update_with_1_operand {
        ($name:ident, $e:expr, $operand:expr, $prev:pat, $next:pat, $res: pat, $g:ident, $b:block) => {
            ::builtin_macros::verus_exec_expr! { {
                let result;
                let atomic = &($e);
                let operand = $operand;
                $crate::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                    #[allow(unused_mut)]
                    let tracked (mut perm, mut $g) = pair;
                    let ghost $prev = perm.view().value;
                    result = atomic.patomic.$name(Tracked(&mut perm), operand);
                    let ghost $res = result;
                    let ghost $next = perm.view().value;

                    proof { $b }

                    proof { pair = (perm, $g); }
                });
                result
            } }
        };
    }

    pub use atomic_with_ghost_update_with_1_operand;

    #[doc(hidden)]
    #[macro_export]
    macro_rules! atomic_with_ghost_update_with_2_operand {
        ($name:ident, $e:expr, $operand1:expr, $operand2:expr, $prev:pat, $next:pat, $res: pat, $g:ident, $b:block) => {
            ::builtin_macros::verus_exec_expr! { {
                let result;
                let atomic = &($e);
                let operand1 = $operand1;
                let operand2 = $operand2;
                $crate::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                    #[allow(unused_mut)]
                    let tracked (mut perm, mut $g) = pair;
                    let ghost $prev = perm.view().value;
                    result = atomic.patomic.$name(Tracked(&mut perm), operand1, operand2);
                    let ghost $res = result;
                    let ghost $next = perm.view().value;

                    proof { $b }

                    proof { pair = (perm, $g); }
                });
                result
            } }
        };
    }

    pub use atomic_with_ghost_update_with_2_operand;

    #[doc(hidden)]
    #[macro_export]
    macro_rules! atomic_with_ghost_update_fetch_add {
    ($e:expr, $operand:expr, $prev:pat, $next:pat, $res: pat, $g:ident, $b:block) => {
        (::builtin_macros::verus_exec_expr!( {
            let result;
            let atomic = &($e);
            let operand = $operand;
            $crate::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                #[allow(unused_mut)]
                let tracked (mut perm, mut $g) = pair;

                proof {
                    let $prev = perm.view().value as int;
                    let $res = perm.view().value as int;
                    let $next = perm.view().value as int + (operand as int);

                    { $b }
                }

                result = atomic.patomic.fetch_add(Tracked(&mut perm), operand);

                proof { pair = (perm, $g); }
            });
            result
        } ))
    }
}

    pub use atomic_with_ghost_update_fetch_add;

    #[doc(hidden)]
    #[macro_export]
    macro_rules! atomic_with_ghost_update_fetch_sub {
        ($e:expr, $operand:expr, $prev:pat, $next:pat, $res: pat, $g:ident, $b:block) => {
            ::builtin_macros::verus_exec_expr! { {
                let result;
                let atomic = &($e);
                let operand = $operand;
                $crate::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                    #[allow(unused_mut)]
                    let tracked (mut perm, mut $g) = pair;

                    proof {
                        let $prev = perm.view().value as int;
                        let $res = perm.view().value as int;
                        let $next = perm.view().value as int - (operand as int);

                        { $b }
                    }

                    result = atomic.patomic.fetch_sub(Tracked(&mut perm), operand);

                    proof { pair = (perm, $g); }
                });
                result
            } }
        };
    }

    pub use atomic_with_ghost_update_fetch_sub;
}

pub mod bytes {
    //! Conversions to/from bytes
    #![allow(unused_imports)]

    use builtin::*;
    use builtin_macros::*;

    use crate::pervasive::*;
    use crate::seq::*;
    use crate::seq_lib::*;
    use crate::slice::*;
    use crate::view::*;

    verus! {

// Conversion between u16 and little-endian byte sequences
pub closed spec fn spec_u16_to_le_bytes(x: u16) -> Seq<u8> {
    #[verusfmt::skip]
    seq![
        (x & 0xff) as u8,
        ((x >> 8) & 0xff) as u8
    ]
}

pub closed spec fn spec_u16_from_le_bytes(s: Seq<u8>) -> u16
    recommends
        s.len() == 2,
{
    (s[0] as u16) | (s[1] as u16) << 8
}

pub proof fn lemma_auto_spec_u16_to_from_le_bytes()
    ensures
        forall|x: u16|
            {
                &&& #[trigger] spec_u16_to_le_bytes(x).len() == 2
                &&& spec_u16_from_le_bytes(spec_u16_to_le_bytes(x)) == x
            },
        forall|s: Seq<u8>|
            s.len() == 2 ==> #[trigger] spec_u16_to_le_bytes(spec_u16_from_le_bytes(s)) == s,
{
    assert forall|x: u16|
        {
            &&& #[trigger] spec_u16_to_le_bytes(x).len() == 2
            &&& spec_u16_from_le_bytes(spec_u16_to_le_bytes(x)) == x
        } by {
        let s = spec_u16_to_le_bytes(x);
        assert({
            &&& x & 0xff < 256
            &&& (x >> 8) & 0xff < 256
        }) by (bit_vector);
        #[verusfmt::skip]
        assert(x == (
        (x & 0xff) |
        ((x >> 8) & 0xff) << 8)
    ) by (bit_vector);
    };
    assert forall|s: Seq<u8>| s.len() == 2 implies #[trigger] spec_u16_to_le_bytes(
        spec_u16_from_le_bytes(s),
    ) == s by {
        let x = spec_u16_from_le_bytes(s);
        let s0 = s[0] as u16;
        let s1 = s[1] as u16;
        #[verusfmt::skip]
        assert(
        (
            (x == s0 | s1 << 8) &&
            (s0 < 256) &&
            (s1 < 256)
        ) ==>
            s0 == (x & 0xff) &&
            s1 == ((x >> 8) & 0xff)
    ) by (bit_vector);
        assert_seqs_equal!(spec_u16_to_le_bytes(spec_u16_from_le_bytes(s)) == s);
    }
}

#[verifier(external_body)]
pub exec fn u16_from_le_bytes(s: &[u8]) -> (x: u16)
    requires
        s@.len() == 2,
    ensures
        x == spec_u16_from_le_bytes(s@),
{
    use core::convert::TryInto;
    u16::from_le_bytes(s.try_into().unwrap())
}

#[cfg(feature = "alloc")]
#[verifier(external_body)]
pub exec fn u16_to_le_bytes(x: u16) -> (s: alloc::vec::Vec<u8>)
    ensures
        s@ == spec_u16_to_le_bytes(x),
        s@.len() == 2,
{
    x.to_le_bytes().to_vec()
}

// Conversion between u32 and little-endian byte sequences
pub closed spec fn spec_u32_to_le_bytes(x: u32) -> Seq<u8> {
    #[verusfmt::skip]
    seq![
        (x & 0xff) as u8,
        ((x >> 8) & 0xff) as u8,
        ((x >> 16) & 0xff) as u8,
        ((x >> 24) & 0xff) as u8,
    ]
}

pub closed spec fn spec_u32_from_le_bytes(s: Seq<u8>) -> u32
    recommends
        s.len() == 4,
{
    (s[0] as u32) | (s[1] as u32) << 8 | (s[2] as u32) << 16 | (s[3] as u32) << 24
}

#[verifier::spinoff_prover]
pub proof fn lemma_auto_spec_u32_to_from_le_bytes()
    ensures
        forall|x: u32|
            {
                &&& #[trigger] spec_u32_to_le_bytes(x).len() == 4
                &&& spec_u32_from_le_bytes(spec_u32_to_le_bytes(x)) == x
            },
        forall|s: Seq<u8>|
            s.len() == 4 ==> #[trigger] spec_u32_to_le_bytes(spec_u32_from_le_bytes(s)) == s,
{
    assert forall|x: u32|
        {
            &&& #[trigger] spec_u32_to_le_bytes(x).len() == 4
            &&& spec_u32_from_le_bytes(spec_u32_to_le_bytes(x)) == x
        } by {
        let s = spec_u32_to_le_bytes(x);
        assert({
            &&& x & 0xff < 256
            &&& (x >> 8) & 0xff < 256
            &&& (x >> 16) & 0xff < 256
            &&& (x >> 24) & 0xff < 256
        }) by (bit_vector);
        #[verusfmt::skip]
        assert(x == (
        (x & 0xff) |
        ((x >> 8) & 0xff) << 8 |
        ((x >> 16) & 0xff) << 16 |
        ((x >> 24) & 0xff) << 24)
    ) by (bit_vector);
    };
    assert forall|s: Seq<u8>| s.len() == 4 implies #[trigger] spec_u32_to_le_bytes(
        spec_u32_from_le_bytes(s),
    ) == s by {
        let x = spec_u32_from_le_bytes(s);
        let s0 = s[0] as u32;
        let s1 = s[1] as u32;
        let s2 = s[2] as u32;
        let s3 = s[3] as u32;
        #[verusfmt::skip]
        assert(
        (
            (x == s0 | s1 << 8 | s2 << 16 | s3 << 24) &&
            (s0 < 256) &&
            (s1 < 256) &&
            (s2 < 256) &&
            (s3 < 256)
        ) ==>
            s0 == (x & 0xff) &&
            s1 == ((x >> 8) & 0xff) &&
            s2 == ((x >> 16) & 0xff) &&
            s3 == ((x >> 24) & 0xff)
    ) by (bit_vector);
        assert_seqs_equal!(spec_u32_to_le_bytes(spec_u32_from_le_bytes(s)) == s);
    }
}

#[verifier(external_body)]
pub exec fn u32_from_le_bytes(s: &[u8]) -> (x: u32)
    requires
        s@.len() == 4,
    ensures
        x == spec_u32_from_le_bytes(s@),
{
    use core::convert::TryInto;
    u32::from_le_bytes(s.try_into().unwrap())
}

#[cfg(feature = "alloc")]
#[verifier(external_body)]
pub exec fn u32_to_le_bytes(x: u32) -> (s: alloc::vec::Vec<u8>)
    ensures
        s@ == spec_u32_to_le_bytes(x),
        s@.len() == 4,
{
    x.to_le_bytes().to_vec()
}

// Conversion between u64 and little-endian byte sequences
pub closed spec fn spec_u64_to_le_bytes(x: u64) -> Seq<u8> {
    #[verusfmt::skip]
    seq![
        (x & 0xff) as u8,
        ((x >> 8) & 0xff) as u8,
        ((x >> 16) & 0xff) as u8,
        ((x >> 24) & 0xff) as u8,
        ((x >> 32) & 0xff) as u8,
        ((x >> 40) & 0xff) as u8,
        ((x >> 48) & 0xff) as u8,
        ((x >> 56) & 0xff) as u8,
    ]
}

pub closed spec fn spec_u64_from_le_bytes(s: Seq<u8>) -> u64
    recommends
        s.len() == 8,
{
    #[verusfmt::skip]
    (s[0] as u64) |
    (s[1] as u64) << 8 |
    (s[2] as u64) << 16 |
    (s[3] as u64) << 24 |
    (s[4] as u64) << 32 |
    (s[5] as u64) << 40 |
    (s[6] as u64) << 48 |
    (s[7] as u64) << 56
}

pub proof fn lemma_auto_spec_u64_to_from_le_bytes()
    ensures
        forall|x: u64|
            #![trigger spec_u64_to_le_bytes(x)]
            {
                &&& spec_u64_to_le_bytes(x).len() == 8
                &&& spec_u64_from_le_bytes(spec_u64_to_le_bytes(x)) == x
            },
        forall|s: Seq<u8>|
            #![trigger spec_u64_to_le_bytes(spec_u64_from_le_bytes(s))]
            s.len() == 8 ==> spec_u64_to_le_bytes(spec_u64_from_le_bytes(s)) == s,
{
    assert forall|x: u64|
        {
            &&& #[trigger] spec_u64_to_le_bytes(x).len() == 8
            &&& spec_u64_from_le_bytes(spec_u64_to_le_bytes(x)) == x
        } by {
        let s = spec_u64_to_le_bytes(x);
        assert({
            &&& x & 0xff < 256
            &&& (x >> 8) & 0xff < 256
            &&& (x >> 16) & 0xff < 256
            &&& (x >> 24) & 0xff < 256
            &&& (x >> 32) & 0xff < 256
            &&& (x >> 40) & 0xff < 256
            &&& (x >> 48) & 0xff < 256
            &&& (x >> 56) & 0xff < 256
        }) by (bit_vector);
        #[verusfmt::skip]
        assert(x == (
        (x & 0xff) |
        ((x >> 8) & 0xff) << 8 |
        ((x >> 16) & 0xff) << 16 |
        ((x >> 24) & 0xff) << 24 |
        ((x >> 32) & 0xff) << 32 |
        ((x >> 40) & 0xff) << 40 |
        ((x >> 48) & 0xff) << 48 |
        ((x >> 56) & 0xff) << 56)
    ) by (bit_vector);
    };
    assert forall|s: Seq<u8>| s.len() == 8 implies #[trigger] spec_u64_to_le_bytes(
        spec_u64_from_le_bytes(s),
    ) == s by {
        let x = spec_u64_from_le_bytes(s);
        let s0 = s[0] as u64;
        let s1 = s[1] as u64;
        let s2 = s[2] as u64;
        let s3 = s[3] as u64;
        let s4 = s[4] as u64;
        let s5 = s[5] as u64;
        let s6 = s[6] as u64;
        let s7 = s[7] as u64;
        #[verusfmt::skip]
        assert(
        (
            (x == s0 | s1 << 8 | s2 << 16 | s3 << 24 | s4 << 32 | s5 << 40 | s6 << 48 | s7 << 56) &&
            (s0 < 256) &&
            (s1 < 256) &&
            (s2 < 256) &&
            (s3 < 256) &&
            (s4 < 256) &&
            (s5 < 256) &&
            (s6 < 256) &&
            (s7 < 256)
        ) ==>
            s0 == (x & 0xff) &&
            s1 == ((x >> 8) & 0xff) &&
            s2 == ((x >> 16) & 0xff) &&
            s3 == ((x >> 24) & 0xff) &&
            s4 == ((x >> 32) & 0xff) &&
            s5 == ((x >> 40) & 0xff) &&
            s6 == ((x >> 48) & 0xff) &&
            s7 == ((x >> 56) & 0xff)
    ) by (bit_vector);
        assert_seqs_equal!(spec_u64_to_le_bytes(spec_u64_from_le_bytes(s)) == s);
    }
}

#[verifier(external_body)]
pub exec fn u64_from_le_bytes(s: &[u8]) -> (x: u64)
    requires
        s@.len() == 8,
    ensures
        x == spec_u64_from_le_bytes(s@),
{
    use core::convert::TryInto;
    u64::from_le_bytes(s.try_into().unwrap())
}

#[cfg(feature = "alloc")]
#[verifier(external_body)]
pub exec fn u64_to_le_bytes(x: u64) -> (s: alloc::vec::Vec<u8>)
    ensures
        s@ == spec_u64_to_le_bytes(x),
        s@.len() == 8,
{
    x.to_le_bytes().to_vec()
}

// Conversion between u128 and little-endian byte sequences
pub closed spec fn spec_u128_to_le_bytes(x: u128) -> Seq<u8> {
    #[verusfmt::skip]
    seq![
        (x & 0xff) as u8,
        ((x >> 8) & 0xff) as u8,
        ((x >> 16) & 0xff) as u8,
        ((x >> 24) & 0xff) as u8,
        ((x >> 32) & 0xff) as u8,
        ((x >> 40) & 0xff) as u8,
        ((x >> 48) & 0xff) as u8,
        ((x >> 56) & 0xff) as u8,
        ((x >> 64) & 0xff) as u8,
        ((x >> 72) & 0xff) as u8,
        ((x >> 80) & 0xff) as u8,
        ((x >> 88) & 0xff) as u8,
        ((x >> 96) & 0xff) as u8,
        ((x >> 104) & 0xff) as u8,
        ((x >> 112) & 0xff) as u8,
        ((x >> 120) & 0xff) as u8,
    ]
}

pub closed spec fn spec_u128_from_le_bytes(s: Seq<u8>) -> u128
    recommends
        s.len() == 16,
{
    #[verusfmt::skip]
    (s[0] as u128) |
    (s[1] as u128) << 8 |
    (s[2] as u128) << 16 |
    (s[3] as u128) << 24 |
    (s[4] as u128) << 32 |
    (s[5] as u128) << 40 |
    (s[6] as u128) << 48 |
    (s[7] as u128) << 56 |
    (s[8] as u128) << 64 |
    (s[9] as u128) << 72 |
    (s[10] as u128) << 80 |
    (s[11] as u128) << 88 |
    (s[12] as u128) << 96 |
    (s[13] as u128) << 104 |
    (s[14] as u128) << 112 |
    (s[15] as u128) << 120
}

#[verifier::spinoff_prover]
pub proof fn lemma_auto_spec_u128_to_from_le_bytes()
    ensures
        forall|x: u128|
            {
                &&& #[trigger] spec_u128_to_le_bytes(x).len() == 16
                &&& spec_u128_from_le_bytes(spec_u128_to_le_bytes(x)) == x
            },
        forall|s: Seq<u8>|
            s.len() == 16 ==> #[trigger] spec_u128_to_le_bytes(spec_u128_from_le_bytes(s)) == s,
{
    assert forall|x: u128|
        {
            &&& #[trigger] spec_u128_to_le_bytes(x).len() == 16
            &&& spec_u128_from_le_bytes(spec_u128_to_le_bytes(x)) == x
        } by {
        let s = spec_u128_to_le_bytes(x);
        assert({
            &&& x & 0xff < 256
            &&& (x >> 8) & 0xff < 256
            &&& (x >> 16) & 0xff < 256
            &&& (x >> 24) & 0xff < 256
            &&& (x >> 32) & 0xff < 256
            &&& (x >> 40) & 0xff < 256
            &&& (x >> 48) & 0xff < 256
            &&& (x >> 56) & 0xff < 256
            &&& (x >> 64) & 0xff < 256
            &&& (x >> 72) & 0xff < 256
            &&& (x >> 80) & 0xff < 256
            &&& (x >> 88) & 0xff < 256
            &&& (x >> 96) & 0xff < 256
            &&& (x >> 104) & 0xff < 256
            &&& (x >> 112) & 0xff < 256
            &&& (x >> 120) & 0xff < 256
        }) by (bit_vector);
        #[verusfmt::skip]
        assert(x == (
        (x & 0xff) |
        ((x >> 8) & 0xff) << 8 |
        ((x >> 16) & 0xff) << 16 |
        ((x >> 24) & 0xff) << 24 |
        ((x >> 32) & 0xff) << 32 |
        ((x >> 40) & 0xff) << 40 |
        ((x >> 48) & 0xff) << 48 |
        ((x >> 56) & 0xff) << 56 |
        ((x >> 64) & 0xff) << 64 |
        ((x >> 72) & 0xff) << 72 |
        ((x >> 80) & 0xff) << 80 |
        ((x >> 88) & 0xff) << 88 |
        ((x >> 96) & 0xff) << 96 |
        ((x >> 104) & 0xff) << 104 |
        ((x >> 112) & 0xff) << 112 |
        ((x >> 120) & 0xff) << 120)
    ) by (bit_vector);
    };
    assert forall|s: Seq<u8>| s.len() == 16 implies #[trigger] spec_u128_to_le_bytes(
        spec_u128_from_le_bytes(s),
    ) == s by {
        let x = spec_u128_from_le_bytes(s);
        let s0 = s[0] as u128;
        let s1 = s[1] as u128;
        let s2 = s[2] as u128;
        let s3 = s[3] as u128;
        let s4 = s[4] as u128;
        let s5 = s[5] as u128;
        let s6 = s[6] as u128;
        let s7 = s[7] as u128;
        let s8 = s[8] as u128;
        let s9 = s[9] as u128;
        let s10 = s[10] as u128;
        let s11 = s[11] as u128;
        let s12 = s[12] as u128;
        let s13 = s[13] as u128;
        let s14 = s[14] as u128;
        let s15 = s[15] as u128;
        #[verusfmt::skip]
        assert(
        (
            (x == s0 | s1 << 8 | s2 << 16 | s3 << 24 | s4 << 32
                     | s5 << 40 | s6 << 48 | s7 << 56 | s8 << 64
                     | s9 << 72 | s10 << 80 | s11 << 88 | s12 << 96
                     | s13 << 104 | s14 << 112 | s15 << 120) &&
            (s0 < 256) &&
            (s1 < 256) &&
            (s2 < 256) &&
            (s3 < 256) &&
            (s4 < 256) &&
            (s5 < 256) &&
            (s6 < 256) &&
            (s7 < 256) &&
            (s8 < 256) &&
            (s9 < 256) &&
            (s10 < 256) &&
            (s11 < 256) &&
            (s12 < 256) &&
            (s13 < 256) &&
            (s14 < 256) &&
            (s15 < 256)
        ) ==>
            s0 == (x & 0xff) &&
            s1 == ((x >> 8) & 0xff) &&
            s2 == ((x >> 16) & 0xff) &&
            s3 == ((x >> 24) & 0xff) &&
            s4 == ((x >> 32) & 0xff) &&
            s5 == ((x >> 40) & 0xff) &&
            s6 == ((x >> 48) & 0xff) &&
            s7 == ((x >> 56) & 0xff) &&
            s8 == ((x >> 64) & 0xff) &&
            s9 == ((x >> 72) & 0xff) &&
            s10 == ((x >> 80) & 0xff) &&
            s11 == ((x >> 88) & 0xff) &&
            s12 == ((x >> 96) & 0xff) &&
            s13 == ((x >> 104) & 0xff) &&
            s14 == ((x >> 112) & 0xff) &&
            s15 == ((x >> 120) & 0xff)
    ) by (bit_vector);
        assert_seqs_equal!(spec_u128_to_le_bytes(spec_u128_from_le_bytes(s)) == s);
    }
}

#[verifier(external_body)]
pub exec fn u128_from_le_bytes(s: &[u8]) -> (x: u128)
    requires
        s@.len() == 16,
    ensures
        x == spec_u128_from_le_bytes(s@),
{
    use core::convert::TryInto;
    u128::from_le_bytes(s.try_into().unwrap())
}

#[cfg(feature = "alloc")]
#[verifier(external_body)]
pub exec fn u128_to_le_bytes(x: u128) -> (s: alloc::vec::Vec<u8>)
    ensures
        s@ == spec_u128_to_le_bytes(x),
        s@.len() == 16,
{
    x.to_le_bytes().to_vec()
}

} // verus!
}

pub mod calc_macro {
    //! The [`calc`] macro provides support for reasoning about a structured proof calculation.
    #![allow(unused_imports)]
    use crate::pervasive::*;
    use builtin::*;
    use builtin_macros::*;

    verus! {

#[doc(hidden)]
#[macro_export]
macro_rules! calc_internal {
    // Getting the last of a series of expressions
    (__internal get_last $end:expr ;) => { $end };
    (__internal get_last $init:expr ; $($tail:expr);* ;) => {
        $crate::calc_macro::calc_internal!(__internal get_last $($tail ;)*)
    };

    // Getting the first non-empty tt
    (__internal first ($tt:tt)) => { $tt };
    (__internal first () $(($rest:tt))*) => { $crate::calc_macro::calc_internal!(__internal first $(($rest))*) };
    (__internal first ($tt:tt) $(($rest:tt))*) => { $tt };

    // Translation from a relation to the relevant expression
    (__internal expr (==) ($a:expr) ($b:expr)) => { ::builtin::equal($a, $b) };
    (__internal expr (<) ($a:expr) ($b:expr)) => { ($a < $b) };
    (__internal expr (<=) ($a:expr) ($b:expr)) => { ($a <= $b) };
    (__internal expr (>) ($a:expr) ($b:expr)) => { ($a > $b) };
    (__internal expr (>=) ($a:expr) ($b:expr)) => { ($a >= $b) };
    (__internal expr (==>) ($a:expr) ($b:expr)) => { ::builtin::imply($a, $b) };
    (__internal expr (<==>) ($a:expr) ($b:expr)) => { ::builtin::imply($a, $b) && ::builtin::imply($b, $a) };
    (__internal expr ($($reln:tt)+) ($a:expr) ($b:expr)) => {
        compile_error!(concat!("INTERNAL ERROR\nUnexpected ", stringify!(($($reln)+, $a, $b)))); }; // Fallthrough

    // Any of the relation steps occuring in the middle of the chain
    (__internal mid [$($topreln:tt)+] $start:expr ; () $b:block $end:expr ; ) => {{
        ::builtin::assert_by($crate::calc_macro::calc_internal!(__internal expr ($($topreln)+) ($start) ($end)), { $b });
    }};
    (__internal mid [$($topreln:tt)+] $start:expr ; ($($reln:tt)+) $b:block $end:expr ; ) => {{
        ::builtin::assert_by($crate::calc_macro::calc_internal!(__internal expr ($($reln)+) ($start) ($end)), { $b });
    }};
    (__internal mid [$($topreln:tt)+] $start:expr ; () $b:block $mid:expr ; $(($($tailreln:tt)*) $tailb:block $taile:expr);* ;) => {{
        ::builtin::assert_by($crate::calc_macro::calc_internal!(__internal expr ($($topreln)+) ($start) ($mid)), { $b });
        $crate::calc_macro::calc_internal!(__internal mid [$($topreln)+] $mid ; $(($($tailreln)*) $tailb $taile);* ;);
    }};
    (__internal mid [$($topreln:tt)+] $start:expr ; ($($reln:tt)+) $b:block $mid:expr ; $(($($tailreln:tt)*) $tailb:block $taile:expr);* ;) => {{
        ::builtin::assert_by($crate::calc_macro::calc_internal!(__internal expr ($($reln)+) ($start) ($mid)), { $b });
        $crate::calc_macro::calc_internal!(__internal mid [$($topreln)+] $mid ; $(($($tailreln)*) $tailb $taile);* ;);
    }};

    // Main entry point to this macro; this is still an internal macro, but this is where the main
    // `calc!` macro will invoke this.
    (($($reln:tt)+) $start:expr ; $(($($($midreln:tt)+)?) $b:block ; $mid:expr);* $(;)?) => {{
        ::builtin::assert_by(
            calc_internal!(__internal expr ($($reln)+) ($start) ($crate::calc_macro::calc_internal!(__internal get_last $($mid ;)*))),
            { $crate::calc_macro::calc_internal!(__internal mid [$($reln)+] $start ; $(($($($midreln)+)?) $b $mid);* ;); }
        );
    }};

    // Fallback, if something _truly_ unexpected happens, explode and provide an error report.
    ($($tt:tt)*) => {
        compile_error!(concat!(
            "INTERNAL ERROR IN `calc!`.\n",
            "If you ever see this, please report your original `calc!` invocation to the Verus issue tracker.\n",
            "\n",
            "Internal state:",
            $("\n  `", stringify!($tt), "`",)*
        ));
    }
}

#[doc(hidden)]
#[macro_export]
// Auxiliary methods, that we do not want to invoke via the verus macro transformation (and thus
// should not go into `calc_internal`) but we don't want to clutter up the main `calc` macro either
// (mostly for documentation readability purposes).
//
// All these are internal and are not expected to be invoked directly from outside of this file.
macro_rules! calc_aux {
    // Confirming that only relations from an allow-set are allowed to be used in `calc!`.
    (confirm_allowed_relation (==)) => { }; // Allowed
    (confirm_allowed_relation (<)) => { }; // Allowed
    (confirm_allowed_relation (<=)) => { }; // Allowed
    (confirm_allowed_relation (>)) => { }; // Allowed
    (confirm_allowed_relation (>=)) => { }; // Allowed
    (confirm_allowed_relation (==>)) => { }; // Allowed
    (confirm_allowed_relation (<==>)) => { }; // Allowed
    (confirm_allowed_relation ($($t:tt)+)) => { compile_error!(concat!("Currently unsupported relation `", stringify!($($t)*), "` in calc")); }; // Fallthrough

    // Confirm that an middle relation is consistent with the main relation
    (confirm_middle_relation (==) (==)) => { }; // Equality is only consistent with itself
    (confirm_middle_relation (<=) (<=)) => { }; // Less-than-or-equal can be proven via any combination of <, ==, and <=
    (confirm_middle_relation (<=) (==)) => { }; //
    (confirm_middle_relation (<=) (<)) => { }; //
    (confirm_middle_relation (<) (<)) => { }; // Strictly-less-than is allowed to use <= and == as intermediates, as long as at least one < shows up at some point
    (confirm_middle_relation (<) (<=)) => { }; //
    (confirm_middle_relation (<) (==)) => { }; //
    (confirm_middle_relation (>=) (>=)) => { }; // Greater-than-or-equal, similar to less-than-or-equal
    (confirm_middle_relation (>=) (==)) => { }; //
    (confirm_middle_relation (>=) (>)) => { }; //
    (confirm_middle_relation (>) (>)) => { }; // Strictly-greater-than, similar to less-than-or-equal
    (confirm_middle_relation (>) (>=)) => { }; //
    (confirm_middle_relation (>) (==)) => { }; //
    (confirm_middle_relation (==>) (==>)) => { }; // Implication is consistent with itself, equality, and if-and-only-if
    (confirm_middle_relation (==>) (==)) => { }; //
    (confirm_middle_relation (==>) (<==>)) => { }; //
    (confirm_middle_relation (<==>) (<==>)) => { }; // If-and-only-if is consistent with itself, and equality
    (confirm_middle_relation (<==>) (==)) => { }; //
    (confirm_middle_relation ($($main:tt)+) ($($middle:tt)+)) => {
        compile_error!(concat!("Potentially inconsistent relation `", stringify!($($middle)*), "` with `", stringify!($($main)*), "`")); }; // Fallthrough

    (confirm_middle_relations ($($main:tt)+)) => { };
    (confirm_middle_relations ($($main:tt)+) ($($middle:tt)+) $($rest:tt)* ) => {
        $crate::calc_macro::calc_aux!(confirm_middle_relation ($($main)+) ($($middle)+));
        $crate::calc_macro::calc_aux!(confirm_middle_relations ($($main)+) $($rest)*);
    };
}

/// The `calc!` macro supports structured proofs through calculations.
///
/// In particular, one can show `a_1 R a_n` for some transitive relation `R` by performing a series
/// of steps `a_1 R a_2`, `a_2 R a_3`, ... `a_{n-1} R a_n`. The calc macro provides both convenient
/// syntax sugar to perform such a proof conveniently, without repeating oneself too often, or
/// exposing the internal steps to the outside context.
///
/// The expected usage looks like:
///
/// ```
/// calc! {
///   (R)
///   a_1; { /* proof that a_1 R a_2 */ }
///   a_2; { /* proof that a_2 R a_3 */ }
///    ...
///   a_n;
/// }
/// ```
///
/// Currently, the `calc!` macro supports common transitive relations for `R`, and this set of
/// relations may be extended in the future.
///
/// Note that `calc!` also supports stating intermediate relations, as long as they are consistent
/// with the main relation `R`. If consistency cannot be immediately shown, Verus will give a
/// helpful message about this. Intermediate relations can be specified by placing them right before
/// the proof block of that step.
///
/// A simple example of using intermediate relations looks like:
///
/// ```
/// let x: int = 2;
/// let y: int = 5;
/// calc! {
///   (<=)
///   x; (==) {}
///   5 - 3; (<) {}
///   5; {} // Notice that no intermediate relation is specified here, so `calc!` will consider the top-level relation `R`; here `<=`.
///   y;
/// }
/// ```
#[allow(unused_macros)]
#[macro_export]
macro_rules! calc {
    // The main entry point to this macro.
    (($($reln:tt)+) $start:expr ; $($(($($middlereln:tt)+))? $b:block $mid:expr);* $(;)?) => {
        $crate::calc_macro::calc_aux!(confirm_allowed_relation ($($reln)+));
        $($(
            $crate::calc_macro::calc_aux!(confirm_allowed_relation ($($middlereln)+));
        )?)*
        $crate::calc_macro::calc_aux!(confirm_middle_relations ($($reln)+) $($(($($middlereln)+))?)*);
        ::builtin_macros::verus_proof_macro_explicit_exprs!(
            $crate::calc_macro::calc_internal!(
                ($($reln)+) @@$start ; $(($($($middlereln)+)?) @@$b ; @@$mid);* ;
            )
        )
    };

    // Fallback, if we see something that is entirely unexpected, we tell the user what the usage should look like.
    ($($tt:tt)*) => {
        compile_error!(concat!(
            "Unexpected invocation of `calc!`. Expected usage looks like \n",
            "  calc! { (==)\n",
            "     a;\n",
            "     (==) { ... }\n",
            "     b + c;\n",
            "     (==) { ... }\n",
            "     d;\n",
            "  }\n",
            "\n",
            "Received:\n  calc! { ",
            $(stringify!($tt), " "),*,
            "}",
        ))
    }
}

#[doc(hidden)]
pub use calc_internal;
#[doc(hidden)]
pub use calc_aux;
pub use calc;

} // verus!
}

pub mod cell {
    use core::cell::UnsafeCell;
    use core::marker;
    use core::{mem, mem::MaybeUninit};

    #[allow(unused_imports)]
    use crate::invariant::*;
    #[allow(unused_imports)]
    use crate::modes::*;
    #[allow(unused_imports)]
    use crate::pervasive::*;
    #[allow(unused_imports)]
    use crate::prelude::*;
    #[allow(unused_imports)]
    use crate::set::*;
    #[allow(unused_imports)]
    use crate::*;

    verus! {

// TODO implement: borrow_mut; figure out Drop, see if we can avoid leaking?
/// `PCell<V>` (which stands for "permissioned call") is the primitive Verus `Cell` type.
///
/// Technically, it is a wrapper around
/// `core::cell::UnsafeCell<core::mem::MaybeUninit<V>>`, and thus has the same runtime
/// properties: there are no runtime checks (as there would be for Rust's traditional
/// [`core::cell::RefCell`](https://doc.rust-lang.org/core/cell/struct.RefCell.html)).
/// Its data may be uninitialized.
///
/// Furthermore (and unlike both
/// [`core::cell::Cell`](https://doc.rust-lang.org/core/cell/struct.Cell.html) and
/// [`core::cell::RefCell`](https://doc.rust-lang.org/core/cell/struct.RefCell.html)),
/// a `PCell<V>` may be `Sync` (depending on `V`).
/// Thanks to verification, Verus ensures that access to the cell is data-race-free.
///
/// `PCell` uses a _ghost permission token_ similar to [`ptr::PPtr`] -- see the [`ptr::PPtr`]
/// documentation for the basics.
/// For `PCell`, the associated type of the permission token is [`cell::PointsTo`].
///
/// ### Differences from `PPtr`.
///
/// The key difference is that, whereas [`ptr::PPtr`] represents a fixed address in memory,
/// a `PCell` has _no_ fixed address because a `PCell` might be moved.
/// As such, the [`pcell.id()`](PCell::id) does not correspond to a memory address; rather,
/// it is a unique identifier that is fixed for a given cell, even when it is moved.
///
/// The arbitrary ID given by [`pcell.id()`](PCell::id) is of type [`CellId`].
/// Despite the fact that it is, in some ways, "like a pointer", note that
/// `CellId` does not support any meangingful arithmetic,
/// has no concept of a "null ID",
/// and has no runtime representation.
///
/// Also note that the `PCell` might be dropped before the `PointsTo` token is dropped,
/// although in that case it will no longer be possible to use the `PointsTo` in `exec` code
/// to extract data from the cell.
///
/// ### Example (TODO)
#[verifier(external_body)]
#[verifier::accept_recursive_types(V)]
pub struct PCell<V> {
    ucell: UnsafeCell<MaybeUninit<V>>,
}

// PCell is always safe to Send/Sync. It's the PointsTo object where Send/Sync matters.
// (It doesn't matter if you move the bytes to another thread if you can't access them.)
#[verifier(external)]
unsafe impl<T> Sync for PCell<T> {

}

#[verifier(external)]
unsafe impl<T> Send for PCell<T> {

}

// PointsTo<V>, on the other hand, needs to inherit both Send and Sync from the V,
// which it does by default in the given definition.
// (Note: this depends on the current behavior that #[verifier::spec] fields are still counted for marker traits)
#[verifier(external_body)]
#[verifier::reject_recursive_types_in_ground_variants(V)]
pub tracked struct PointsTo<V> {
    phantom: marker::PhantomData<V>,
    no_copy: NoCopy,
}

pub ghost struct PointsToData<V> {
    pub pcell: CellId,
    pub value: Option<V>,
}

#[doc(hidden)]
#[macro_export]
macro_rules! pcell_opt_internal {
    [$pcell:expr => $val:expr] => {
        $crate::cell::PointsToData {
            pcell: $pcell,
            value: $val,
        }
    };
}

#[macro_export]
macro_rules! pcell_opt {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!(
            $crate::cell::pcell_opt_internal!($($tail)*)
        )
    }
}

pub use pcell_opt_internal;
pub use pcell_opt;

#[verifier(external_body)]
pub struct CellId {
    id: int,
}

impl<V> PointsTo<V> {
    pub spec fn view(self) -> PointsToData<V>;
}

impl<V> PCell<V> {
    /// A unique ID for the cell.
    pub spec fn id(&self) -> CellId;

    /// Return an empty ("uninitialized") cell.
    #[inline(always)]
    #[verifier(external_body)]
    pub const fn empty() -> (pt: (PCell<V>, Tracked<PointsTo<V>>))
        ensures
            pt.1@@ === pcell_opt![ pt.0.id() => Option::None ],
    {
        let p = PCell { ucell: UnsafeCell::new(MaybeUninit::uninit()) };
        (p, Tracked::assume_new())
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub const fn new(v: V) -> (pt: (PCell<V>, Tracked<PointsTo<V>>))
        ensures
            (pt.1@@ === PointsToData { pcell: pt.0.id(), value: Option::Some(v) }),
    {
        let p = PCell { ucell: UnsafeCell::new(MaybeUninit::new(v)) };
        (p, Tracked::assume_new())
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn put(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, v: V)
        requires
            old(perm)@ === pcell_opt![ self.id() => Option::None ],
        ensures
            perm@ === pcell_opt![ self.id() => Option::Some(v) ],
        opens_invariants none
    {
        unsafe {
            *(self.ucell.get()) = MaybeUninit::new(v);
        }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn take(&self, Tracked(perm): Tracked<&mut PointsTo<V>>) -> (v: V)
        requires
            self.id() === old(perm)@.pcell,
            old(perm)@.value.is_Some(),
        ensures
            perm@.pcell === old(perm)@.pcell,
            perm@.value === Option::None,
            v === old(perm)@.value.get_Some_0(),
        opens_invariants none
    {
        unsafe {
            let mut m = MaybeUninit::uninit();
            mem::swap(&mut m, &mut *self.ucell.get());
            m.assume_init()
        }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn replace(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V) -> (out_v: V)
        requires
            self.id() === old(perm)@.pcell,
            old(perm)@.value.is_Some(),
        ensures
            perm@.pcell === old(perm)@.pcell,
            perm@.value === Option::Some(in_v),
            out_v === old(perm)@.value.get_Some_0(),
        opens_invariants none
    {
        unsafe {
            let mut m = MaybeUninit::new(in_v);
            mem::swap(&mut m, &mut *self.ucell.get());
            m.assume_init()
        }
    }

    // The reason for the the lifetime parameter 'a is
    // that `self` actually contains the data in its interior, so it needs
    // to outlive the returned borrow.
    #[inline(always)]
    #[verifier(external_body)]
    pub fn borrow<'a>(&'a self, Tracked(perm): Tracked<&'a PointsTo<V>>) -> (v: &'a V)
        requires
            self.id() === perm@.pcell,
            perm@.value.is_Some(),
        ensures
            *v === perm@.value.get_Some_0(),
        opens_invariants none
    {
        unsafe { (*self.ucell.get()).assume_init_ref() }
    }

    //////////////////////////////////
    // Untrusted functions below here
    #[inline(always)]
    pub fn into_inner(self, Tracked(perm): Tracked<PointsTo<V>>) -> (v: V)
        requires
            self.id() === perm@.pcell,
            perm@.value.is_Some(),
        ensures
            v === perm@.value.get_Some_0(),
        opens_invariants none
    {
        let tracked mut perm = perm;
        self.take(Tracked(&mut perm))
    }
    // TODO this should replace the external_body implementation of `new` above;
    // however it requires unstable features: const_mut_refs and const_refs_to_cell
    //#[inline(always)]
    //pub const fn new(v: V) -> (pt: (PCell<V>, Tracked<PointsTo<V>>))
    //    ensures (pt.1@@ === PointsToData{ pcell: pt.0.id(), value: Option::Some(v) }),
    //{
    //    let (p, Tracked(mut t)) = Self::empty();
    //    p.put(Tracked(&mut t), v);
    //    (p, Tracked(t))
    //}

}

impl<V: Copy> PCell<V> {
    #[inline(always)]
    #[verifier(external_body)]
    pub fn write(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V)
        requires
            self.id() === old(perm)@.pcell,
            old(perm)@.value.is_Some(),
        ensures
            perm@.pcell === old(perm)@.pcell,
            perm@.value === Some(in_v),
        opens_invariants none
    {
        let _out = self.replace(Tracked(&mut *perm), in_v);
    }
}

struct InvCellPred {}

impl<T> InvariantPredicate<(Set<T>, PCell<T>), PointsTo<T>> for InvCellPred {
    closed spec fn inv(k: (Set<T>, PCell<T>), perm: PointsTo<T>) -> bool {
        let (possible_values, pcell) = k;
        {
            &&& perm@.value.is_Some()
            &&& possible_values.contains(perm@.value.get_Some_0())
            &&& pcell.id() === perm@.pcell
        }
    }
}

#[verifier::reject_recursive_types(T)]
pub struct InvCell<T> {
    possible_values: Ghost<Set<T>>,
    pcell: PCell<T>,
    perm_inv: Tracked<LocalInvariant<(Set<T>, PCell<T>), PointsTo<T>, InvCellPred>>,
}

impl<T> InvCell<T> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.perm_inv@.constant() === (self.possible_values@, self.pcell)
    }

    pub closed spec fn inv(&self, val: T) -> bool {
        &&& self.possible_values@.contains(val)
    }

    pub fn new(val: T, Ghost(f): Ghost<spec_fn(T) -> bool>) -> (cell: Self)
        requires
            f(val),
        ensures
            cell.wf() && forall|v| f(v) <==> cell.inv(v),
    {
        let (pcell, Tracked(perm)) = PCell::new(val);
        let ghost possible_values = Set::new(f);
        let tracked perm_inv = LocalInvariant::new((possible_values, pcell), perm, 0);
        InvCell { possible_values: Ghost(possible_values), pcell, perm_inv: Tracked(perm_inv) }
    }
}

impl<T> InvCell<T> {
    pub fn replace(&self, val: T) -> (old_val: T)
        requires
            self.wf() && self.inv(val),
        ensures
            self.inv(old_val),
    {
        let r;
        crate::open_local_invariant!(self.perm_inv.borrow() => perm => {
            r = self.pcell.replace(Tracked(&mut perm), val);
        });
        r
    }
}

impl<T: Copy> InvCell<T> {
    pub fn get(&self) -> (val: T)
        requires
            self.wf(),
        ensures
            self.inv(val),
    {
        let r;
        crate::open_local_invariant!(self.perm_inv.borrow() => perm => {
            r = *self.pcell.borrow(Tracked(&perm));
        });
        r
    }
}

} // verus!
}

pub mod function {
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use builtin_macros::*;

    // TODO: get rid of fun_ext*

    verus! {

/// General properties of spec functions.
///
/// For now, this just contains an axiom of function extensionality for
/// spec_fn.
/// DEPRECATED: use f1 =~= f2 or f1 =~~= f2 instead.
/// Axiom of function extensionality: two functions are equal if they are
/// equal on all inputs.
#[verifier(external_body)]
#[deprecated = "use f1 =~= f2 or f1 =~~= f2 instead"]
pub proof fn fun_ext<A, B>(f1: spec_fn(A) -> B, f2: spec_fn(A) -> B)
    requires
        forall|x: A| #![trigger f1(x)] f1(x) == f2(x),
    ensures
        f1 == f2,
{
}

} // verus!
    /// A macro to conveniently generate similar functional extensionality axioms for functions that
/// take `n` arguments.
#[doc(hidden)]
    macro_rules! gen_fun_ext_n {
        ($fun_ext:ident, $O:ident, $($x:ident : $I:ident),*) => {
            verus! {
      /// DEPRECATED: use f1 =~= f2 or f1 =~~= f2 instead.
      /// See [`fun_ext`]
      #[verifier(external_body)]
      #[deprecated = "use f1 =~= f2 or f1 =~~= f2 instead"]
      pub proof fn $fun_ext<$($I),*, $O>(f1: spec_fn($($I),*,) -> $O, f2: spec_fn($($I),*,) -> $O)
        requires forall |$($x: $I),*| #![trigger f1($($x),*)] f1($($x),*) == f2($($x),*)
        ensures f1 == f2
      {}
    }
        };
    }

    // Note: We start at 1 just for consistency; it is exactly equivalent to `fun_ext`
    gen_fun_ext_n! { fun_ext_1, B, x1: A1 }
    gen_fun_ext_n! { fun_ext_2, B, x1: A1, x2: A2 }
    gen_fun_ext_n! { fun_ext_3, B, x1: A1, x2: A2, x3: A3 }
    gen_fun_ext_n! { fun_ext_4, B, x1: A1, x2: A2, x3: A3, x4: A4 }
}

pub mod invariant {
    #[allow(unused_imports)]
    use crate::pervasive::*;
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use builtin_macros::*;

    // TODO:
    //  * utility for conveniently creating unique namespaces

    // An invariant storing objects of type V needs to be able to have some kind of configurable
    // predicate `V -> bool`. However, doing this naively with a fully configurable
    // predicate function would result in V being reject_recursive_types,
    // which is too limiting and prevents important use cases with recursive types.

    //
    // Instead, we allow the user to specify a predicate which is fixed *at the type level*
    // which we do through this trait, InvariantPredicate. However, the predicate still
    // needs to be "dynamically configurable" upon the call to the invariant constructor.
    // To support this, we add another type parameter K, a constant is fixed for a given
    // Invariant object.
    //
    // So each Invariant object has 3 type parameters:
    //  * K - A "constant" which is specified at constructor time
    //  * V - Type of the stored 'tracked' object
    //  * Pred: InvariantPredicate - provides the predicate (K, V) -> bool
    //
    // With this setup, we can now declare both K and V without reject_recursive_types.
    // To be sure, note that the following, based on our trait formalism,
    // is well-formed CIC (Coq), without any type polarity issues:
    //
    // ```
    //    Inductive InvariantPredicate K V :=
    //        | inv_pred : (K -> V -> bool) -> InvariantPredicate K V.
    //
    //    Inductive Inv (K V: Type) (x: InvariantPredicate K V) :=
    //      | inv : K -> Inv K V x.
    //
    //    Definition some_predicate (V: Type) : InvariantPredicate nat V :=
    //      inv_pred nat V (fun k v => false). (* an arbitrary predicate *)
    //
    //    (* example recursive type *)
    //    Inductive T :=
    //      | A : (Inv nat T (some_predicate T)) -> T.
    // ```
    //
    // Note that the user can always just set K to be `V -> bool` in order to make the
    // Invariant's predicate maximally configurable without having to restrict it at the
    // type level. By doing so, the user opts in to the negative usage of V in exchange
    // for the flexibility.

    verus! {

/// Trait used to specify an _invariant predicate_ for
/// [`LocalInvariant`] and [`AtomicInvariant`].
pub trait InvariantPredicate<K, V> {
    spec fn inv(k: K, v: V) -> bool;
}

} // verus!
    // LocalInvariant is NEVER `Sync`.
//
// Furthermore, for either type:
//
//  * If an Invariant<T> is Sync, then T must be Send
//      * We could put the T in an Invariant, sync the invariant to another thread,
//        and then extract the T, having effectively send it to the other thread.
//  * If Invariant<T> is Send, then T must be Send
//      * We could put the T in an Invariant, send the invariant to another thread,
//        and then take the T out.
//
// So the Sync/Send-ness of the Invariant depends on the Send-ness of T;
// however, the Sync-ness of T is unimportant (the invariant doesn't give you an extra
// ability to share a reference to a T across threads).
//
// In conclusion, we should have:
//
//    T                   AtomicInvariant<T>  LocalInvariant<T>
//
//    {}          ==>     {}                  {}
//    Send        ==>     Send+Sync           Send
//    Sync        ==>     {}                  {}
//    Sync+Send   ==>     Send+Sync           Send
/// An `AtomicInvariant` is a ghost object that provides "interior mutability"
/// for ghost objects, specifically, for `tracked` ghost objects.
/// A reference `&AtomicInvariant` may be shared between clients.
/// A client holding such a reference may _open_ the invariant
/// to obtain ghost ownership of `v1: V`, and then _close_ the invariant by returning
/// ghost ownership of a (potentially) different object `v2: V`.
///
/// An `AtomicInvariant` implements [`Sync`](https://doc.rust-lang.org/std/sync/)
/// and may be shared between threads.
/// However, this means that an `AtomicInvariant` can be only opened for
/// the duration of a single _sequentially consistent atomic_ operation.
/// Such operations are provided by our [`PAtomic`](crate::atomic) library.
/// For an invariant object without this atomicity restriction,
/// see [`LocalInvariant`], which gives up thread safety in exchange.
///
/// An `AtomicInvariant` consists of:
///
///  * A _predicate_ specified via the `InvariantPredicate` type bound, that determines
///    what values `V` may be saved inside the invariant.
///  * A _constant_ `K`, specified at construction type. The predicate function takes
///    this constant as a parameter, so the constant allows users to dynamically configure
///    the predicate function in a way that can't be done at the type level.
///  * A _namespace_. This is a bit of a technicality, and you can often just declare
///    it as an arbitrary integer with no issues. See the [`open_local_invariant!`]
///    documentation for more details.
///
/// The constant and namespace are specified at construction time ([`AtomicInvariant::new`]).
/// These values are fixed for the lifetime of the `AtomicInvariant` object.
/// To open the invariant and access the stored object `V`,
/// use the macro [`open_atomic_invariant!`].
///
/// The `AtomicInvariant` API is an instance of the ["invariant" method in Verus's general philosophy on interior mutability](https://verus-lang.github.io/verus/guide/interior_mutability.html).
///
/// **Note:** Rather than using `AtomicInvariant` directly, we generally recommend
/// using the [`atomic_ghost` APIs](crate::atomic_ghost).
#[cfg_attr(verus_keep_ghost, verifier::proof)]
    #[cfg_attr(verus_keep_ghost, verifier::external_body)] /* vattr */
    #[cfg_attr(verus_keep_ghost, verifier::accept_recursive_types(K))]
    #[cfg_attr(verus_keep_ghost, verifier::accept_recursive_types(V))]
    #[cfg_attr(verus_keep_ghost, verifier::accept_recursive_types(Pred))]
    pub struct AtomicInvariant<K, V, Pred> {
        dummy: builtin::SyncSendIfSend<V>,
        dummy1: core::marker::PhantomData<(K, Pred)>,
    }

    /// A `LocalInvariant` is a ghost object that provides "interior mutability"
    /// for ghost objects, specifically, for `tracked` ghost objects.
    /// A reference `&LocalInvariant` may be shared between clients.
    /// A client holding such a reference may _open_ the invariant
    /// to obtain ghost ownership of `v1: V`, and then _close_ the invariant by returning
    /// ghost ownership of a (potentially) different object `v2: V`.
    ///
    /// A `LocalInvariant` cannot be shared between threads
    /// (that is, it does not implement [`Sync`](https://doc.rust-lang.org/std/sync/)).
    /// However, this means that a `LocalInvariant` can be opened for an indefinite length
    /// of time, since there is no risk of a race with another thread.
    /// For an invariant object with the opposite properties, see [`AtomicInvariant`].
    ///
    /// A `LocalInvariant` consists of:
    ///
    ///  * A _predicate_ specified via the `InvariantPredicate` type bound, that determines
    ///    what values `V` may be saved inside the invariant.
    ///  * A _constant_ `K`, specified at construction type. The predicate function takes
    ///    this constant as a parameter, so the constant allows users to dynamically configure
    ///    the predicate function in a way that can't be done at the type level.
    ///  * A _namespace_. This is a bit of a technicality, and you can often just declare
    ///    it as an arbitrary integer with no issues. See the [`open_local_invariant!`]
    ///    documentation for more details.
    ///
    /// The constant and namespace are specified at construction time ([`LocalInvariant::new`]).
    /// These values are fixed for the lifetime of the `LocalInvariant` object.
    /// To open the invariant and access the stored object `V`,
    /// use the macro [`open_local_invariant!`].
    ///
    /// The `LocalInvariant` API is an instance of the ["invariant" method in Verus's general philosophy on interior mutability](https://verus-lang.github.io/verus/guide/interior_mutability.html).

    #[cfg_attr(verus_keep_ghost, verifier::proof)]
    #[cfg_attr(verus_keep_ghost, verifier::external_body)] /* vattr */
    #[cfg_attr(verus_keep_ghost, verifier::accept_recursive_types(K))]
    #[cfg_attr(verus_keep_ghost, verifier::accept_recursive_types(V))]
    #[cfg_attr(verus_keep_ghost, verifier::accept_recursive_types(Pred))]
    pub struct LocalInvariant<K, V, Pred> {
        dummy: builtin::SendIfSend<V>,
        dummy1: core::marker::PhantomData<(K, Pred)>, // TODO ignore Send/Sync here
    }

    macro_rules! declare_invariant_impl {
        ($invariant:ident) => {
            // note the path names of `inv` and `namespace` are harcoded into the VIR crate.

            verus!{

        impl<K, V, Pred: InvariantPredicate<K, V>> $invariant<K, V, Pred> {
            /// The constant specified upon the initialization of this `
            #[doc = stringify!($invariant)]
            ///`.
            pub spec fn constant(&self) -> K;

            /// Namespace the invariant was declared in.
            #[rustc_diagnostic_item = concat!("verus::vstd::invariant::", stringify!($invariant), "::namespace")]
            pub spec fn namespace(&self) -> int;

            /// Returns `true` if it is possible to store the value `v` into the `
            #[doc = stringify!($invariant)]
            ///`.
            ///
            /// This is equivalent to `Pred::inv(self.constant(), v)`.

            #[rustc_diagnostic_item = concat!("verus::vstd::invariant::", stringify!($invariant), "::inv")]
            pub open spec fn inv(&self, v: V) -> bool {
                Pred::inv(self.constant(), v)
            }

            /// Initialize a new `
            #[doc = stringify!($invariant)]
            ///` with constant `k`. initial stored (tracked) value `v`,
            /// and in the namespace `ns`.

            #[verifier::external_body]
            pub proof fn new(k: K, tracked v: V, ns: int) -> (tracked i: $invariant<K, V, Pred>)
                requires
                    Pred::inv(k, v),
                ensures
                    i.constant() == k,
                    i.namespace() == ns,
            {
                unimplemented!();
            }

            /// Destroys the `
            #[doc = stringify!($invariant)]
            ///`, returning the tracked value contained within.

            #[verifier::external_body]
            pub proof fn into_inner(#[verifier::proof] self) -> (tracked v: V)
                ensures self.inv(v),
            {
                unimplemented!();
            }
        }

        }
        };
    }

    declare_invariant_impl!(AtomicInvariant);
    declare_invariant_impl!(LocalInvariant);

    #[doc(hidden)]
    #[cfg_attr(verus_keep_ghost, verifier::proof)]
    pub struct InvariantBlockGuard;

    // NOTE: These 3 methods are removed in the conversion to VIR; they are only used
    // for encoding and borrow-checking.
    // In the VIR these are all replaced by the OpenInvariant block.
    // This means that the bodies, preconditions, and even their modes are not important.
    //
    // An example usage of the macro is like
    //
    //   i: AtomicInvariant<X>
    //
    //   open_invariant!(&i => inner => {
    //      { modify `inner` here }
    //   });
    //
    //  where `inner` will have type `X`.
    //
    //  The purpose of the `guard` object, used below, is to ensure the borrow on `i` will
    //  last the entire block.

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::vstd::invariant::open_atomic_invariant_begin"]
    #[doc(hidden)]
    #[verifier::external] /* vattr */
    pub fn open_atomic_invariant_begin<'a, K, V, Pred: InvariantPredicate<K, V>>(
        _inv: &'a AtomicInvariant<K, V, Pred>,
    ) -> (&'a InvariantBlockGuard, V) {
        unimplemented!();
    }

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::vstd::invariant::open_local_invariant_begin"]
    #[doc(hidden)]
    #[verifier::external] /* vattr */
    pub fn open_local_invariant_begin<'a, K, V, Pred: InvariantPredicate<K, V>>(
        _inv: &'a LocalInvariant<K, V, Pred>,
    ) -> (&'a InvariantBlockGuard, V) {
        unimplemented!();
    }

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::vstd::invariant::open_invariant_end"]
    #[doc(hidden)]
    #[verifier::external] /* vattr */
    pub fn open_invariant_end<V>(_guard: &InvariantBlockGuard, _v: V) {
        unimplemented!();
    }

    /// Macro used to temporarily "open" an [`AtomicInvariant`] object, obtaining the stored
    /// value within.
    ///
    /// ### Usage
    ///
    /// The form of the macro looks like,
    ///
    /// ```rust
    /// open_atomic_invariant($inv => $id => {
    ///     // Inner scope
    /// });
    /// ```
    ///
    /// This operation is very similar to [`open_local_invariant!`], so we refer to its
    /// documentation for the basics. There is only one difference, besides
    /// the fact that `$inv` should be an [`&AtomicInvariant`](AtomicInvariant)
    /// rather than a [`&LocalInvariant`](LocalInvariant).
    /// The difference is that `open_atomic_invariant!` has an additional _atomicity constraint_:
    ///
    ///  * **Atomicity constraint**: The code body of an `open_atomic_invariant!` block
    ///    cannot contain any `exec`-mode code with the exception of a _single_ atomic operation.
    ///
    /// (Of course, the code block can still contain an arbitrary amount of ghost code.)
    ///
    /// The atomicity constraint is needed because an `AtomicInvariant` must be thread-safe;
    /// that is, it can be shared across threads. In order for the ghost state to be shared
    /// safely, it must be restored after each atomic operation.
    ///
    /// The atomic operations may be found in the [`PAtomic`](crate::atomic) library.
    /// The user can also mark their own functions as "atomic operations" using
    /// `#[verifier::atomic)]`; however, this is not useful for very much other than defining
    /// wrappers around the existing atomic operations from [`PAtomic`](crate::atomic).
    /// Note that reading and writing through a [`PCell`](crate::cell::PCell)
    /// or a [`PPtr`](crate::ptr::PPtr) are _not_ atomic operations.
    ///
    /// **Note:** Rather than using `open_atomic_invariant!` directly, we generally recommend
    /// using the [`atomic_ghost` APIs](crate::atomic_ghost).
    ///
    /// ### Example
    ///
    /// TODO fill this in

    // TODO the first argument here should be macro'ed in ghost context, not exec

    #[macro_export]
    macro_rules! open_atomic_invariant {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_exec_inv_macro_exprs!($crate::invariant::open_atomic_invariant_internal!($($tail)*))
    };
}

    #[macro_export]
    macro_rules! open_atomic_invariant_in_proof {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_ghost_inv_macro_exprs!($crate::invariant::open_atomic_invariant_internal!($($tail)*))
    };
}

    #[macro_export]
    macro_rules! open_atomic_invariant_internal {
    ($eexpr:expr => $iident:ident => $bblock:block) => {
        #[cfg_attr(verus_keep_ghost, verifier::invariant_block)] /* vattr */ {
            #[cfg(verus_keep_ghost_body)]
            #[allow(unused_mut)] let (guard, mut $iident) = $crate::invariant::open_atomic_invariant_begin($eexpr);
            $bblock
            #[cfg(verus_keep_ghost_body)]
            $crate::invariant::open_invariant_end(guard, $iident);
        }
    }
}

    pub use open_atomic_invariant;
    pub use open_atomic_invariant_in_proof;
    #[doc(hidden)]
    pub use open_atomic_invariant_internal;

    /// Macro used to temporarily "open" a [`LocalInvariant`] object, obtaining the stored
    /// value within.
    ///
    /// ### Usage
    ///
    /// The form of the macro looks like,
    ///
    /// ```rust
    /// open_local_invariant($inv => $id => {
    ///     // Inner scope
    /// });
    /// ```
    ///
    /// The operation of opening an invariant is a ghost one; however, the inner code block
    /// may contain arbitrary `exec`-mode code. The invariant remains "open" for the duration
    /// of the inner code block, and it is closed again of the end of the block.
    ///
    /// The `$inv` parameter should be an expression of type `&LocalInvariant<K, V, Pred>`,
    /// the invariant object to be opened. The `$id` is an identifier which is bound within
    /// the code block as a `mut` variable of type `V`. This gives the user ownership over
    /// the `V` value, which they may manipulate freely within the code block. At the end
    /// of the code block, the variable `$id` is consumed.
    ///
    /// The obtained object `v: V`, will satisfy the `LocalInvariant`'s invariant predicate
    /// [`$inv.inv(v)`](LocalInvariant::inv). Furthermore, the user must prove that this
    /// invariant still holds at the end. In other words, the macro usage is
    /// roughly equivalent to the following:
    ///
    /// ```rust
    /// {
    ///     let $id: V = /* an arbitrary value */;
    ///     assume($inv.inv($id));
    ///     /* user code block here */
    ///     assert($inv.inv($id));
    ///     consume($id);
    /// }
    /// ```
    ///
    /// ### Avoiding Reentrancy
    ///
    /// Verus adds additional checks to ensure that an invariant is never opened
    /// more than once at the same time. For example, suppose that you attempt to nest
    /// the use of `open_invariant`, supplying the same argument `inv` to each:
    ///
    /// ```rust
    /// open_local_invariant(inv => id1 => {
    ///     open_local_invariant(inv => id2 => {
    ///     });
    /// });
    /// ```
    ///
    /// In this situation, Verus would produce an error:
    ///
    /// ```
    /// error: possible invariant collision
    ///   |
    ///   |   open_atomic_invariant!(&inv => id1 => {
    ///   |                           ^ this invariant
    ///   |       open_atomic_invariant!(&inv => id2 => {
    ///   |                               ^ might be the same as this invariant
    ///   ...
    ///   |       }
    ///   |   }
    /// ```
    ///
    /// When generating these conditions, Verus compares invariants via their
    /// [`namespace()`](LocalInvariant::namespace) values.
    /// An invariant's namespace (represented simply as an integer)
    /// is specified upon the call to [`LocalInvariant::new`].
    /// If you have the need to open multiple invariants at once, make sure to given
    /// them different namespaces.
    ///
    /// So that Verus can ensure that there are no nested invariant accesses across function
    /// boundaries, every `proof` and `exec` function has, as part of its specification,
    /// the set of invariant namespaces that it might open.
    ///
    /// UNDER CONSTRUCTION: right now the forms of these specifications are somewhat limited
    /// and we expect to expand them.
    ///
    /// The invariant set of a function can be specified by putting either
    /// `opens_invariants none` or `opens_invariants any` in the function signature.
    /// The default for an `exec`-mode function is to open any, while the default
    /// for a `proof`-mode function is to open none.
    ///
    /// ### Example
    ///
    /// TODO fill this in
    ///
    /// ### More Examples
    ///
    /// TODO fill this in

    #[macro_export]
    macro_rules! open_local_invariant {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_exec_inv_macro_exprs!(
            $crate::invariant::open_local_invariant_internal!($($tail)*))
    };
}

    #[macro_export]
    macro_rules! open_local_invariant_in_proof {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_ghost_inv_macro_exprs!($crate::invariant::open_local_invariant_internal!($($tail)*))
    };
}

    #[macro_export]
    macro_rules! open_local_invariant_internal {
    ($eexpr:expr => $iident:ident => $bblock:block) => {
        #[cfg_attr(verus_keep_ghost, verifier::invariant_block)] /* vattr */ {
            #[cfg(verus_keep_ghost_body)]
            #[allow(unused_mut)] let (guard, mut $iident) = $crate::invariant::open_local_invariant_begin($eexpr);
            $bblock
            #[cfg(verus_keep_ghost_body)]
            $crate::invariant::open_invariant_end(guard, $iident);
        }
    }
}

    pub use open_local_invariant;
    pub use open_local_invariant_in_proof;
    #[doc(hidden)]
    pub use open_local_invariant_internal;
}

pub mod layout {
    #![allow(unused_imports)]

    use crate::prelude::*;
    use builtin::*;
    use builtin_macros::*;

    verus! {

// TODO add some means for Verus to calculate the size & alignment of types
// TODO use a definition from a math library, once we have one.
pub open spec fn is_power_2(n: int) -> bool
    decreases n,
{
    if n <= 0 {
        false
    } else if n == 1 {
        true
    } else {
        n % 2 == 0 && is_power_2(n / 2)
    }
}

/// Matches the conditions here: <https://doc.rust-lang.org/stable/std/alloc/struct.Layout.html>
pub open spec fn valid_layout(size: usize, align: usize) -> bool {
    is_power_2(align as int) && size <= isize::MAX as int - (isize::MAX as int % align as int)
}

// Keep in mind that the `V: Sized` trait bound is COMPLETELY ignored in the
// VIR encoding. It is not possible to write an axiom like
// "If `V: Sized`, then `size_of::<&V>() == size_of::<usize>()`.
// If you tried, it wouldn't work the way you expect.
// The ONLY thing that checks Sized marker bounds is rustc, but it is possible
// to get around rustc's checks with broadcast_forall.
// Therefore, in spec-land, we must use the `is_sized` predicate instead.
//
// Note: for exec functions, and for proof functions that take tracked arguments,
// we CAN rely on rustc's checking. So in those cases it's okay for us to assume
// a `V: Sized` type is sized.
pub spec fn is_sized<V: ?Sized>() -> bool;

pub spec fn size_of<V>() -> nat;

pub spec fn align_of<V>() -> nat;

// Naturally, the size of any executable type is going to fit into a `usize`.
// What I'm not sure of is whether it will be possible to "reason about" arbitrarily
// big types _in ghost code_ without tripping one of rustc's checks.
//
// I think it could go like this:
//   - Have some polymorphic code that constructs a giant tuple and proves false
//   - Make sure the code doesn't get monomorphized by rustc
//   - To export the 'false' fact from the polymorphic code without monomorphizing,
//     use broadcast_forall.
//
// Therefore, we are NOT creating an axiom that `size_of` fits in usize.
// However, we still give the guarantee that if you call `core::mem::size_of`
// at runtime, then the resulting usize is correct.
#[verifier(inline)]
pub open spec fn size_of_as_usize<V>() -> usize
    recommends
        size_of::<V>() as usize as int == size_of::<V>(),
{
    size_of::<V>() as usize
}

#[verifier(inline)]
pub open spec fn align_of_as_usize<V>() -> usize
    recommends
        align_of::<V>() as usize as int == align_of::<V>(),
{
    align_of::<V>() as usize
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(size_of_as_usize)]
pub fn ex_size_of<V>() -> (u: usize)
    ensures
        is_sized::<V>(),
        u as nat == size_of::<V>(),
{
    core::mem::size_of::<V>()
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(align_of_as_usize)]
pub fn ex_align_of<V>() -> (u: usize)
    ensures
        is_sized::<V>(),
        u as nat == align_of::<V>(),
{
    core::mem::align_of::<V>()
}

// This is marked as exec, again, in order to force `V` to be a real exec type.
// Of course, it's still a no-op.
#[verifier(external_body)]
#[inline(always)]
pub exec fn layout_for_type_is_valid<V>()
    ensures
        valid_layout(size_of::<V>() as usize, align_of::<V>() as usize),
        is_sized::<V>(),
        size_of::<V>() as usize as nat == size_of::<V>(),
        align_of::<V>() as usize as nat == align_of::<V>(),
{
}

} // verus!
}

pub mod map {
    #[allow(unused_imports)]
    use crate::pervasive::*;
    use crate::set::*;
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use builtin_macros::*;
    use core::marker;

    verus! {

/// `Map<K, V>` is an abstract map type for specifications.
/// To use a "map" in compiled code, use an `exec` type like HashMap (TODO)
/// that has a `Map<K, V>` as its specification type.
///
/// An object `map: Map<K, V>` has a _domain_, a set of keys given by [`map.dom()`](Map::dom),
/// and a mapping for keys in the domain to values, given by [`map[key]`](Map::index).
/// Alternatively, a map can be thought of as a set of `(K, V)` pairs where each key
/// appears in at most entry.
///
/// In general, a map might be infinite.
/// To work specifically with finite maps, see the [`self.finite()`](Set::finite) predicate.
///
/// Maps can be constructed in a few different ways:
///  * [`Map::empty()`] constructs an empty map.
///  * [`Map::new`] and [`Map::total`] construct a map given functions that specify its domain and the mapping
///     from keys to values (a _map comprehension_).
///  * The [`map!`] macro, to construct small maps of a fixed size.
///  * By manipulating an existing map with [`Map::insert`] or [`Map::remove`].
///
/// To prove that two maps are equal, it is usually easiest to use the extensionality operator `=~=`.
#[verifier(external_body)]
#[verifier::ext_equal]
#[verifier::reject_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub tracked struct Map<K, V> {
    dummy: marker::PhantomData<(K, V)>,
}

impl<K, V> Map<K, V> {
    /// An empty map.
    pub spec fn empty() -> Map<K, V>;

    /// Gives a `Map<K, V>` whose domain contains every key, and maps each key
    /// to the value given by `fv`.
    pub open spec fn total(fv: impl Fn(K) -> V) -> Map<K, V> {
        Set::full().mk_map(fv)
    }

    /// Gives a `Map<K, V>` whose domain is given by the boolean predicate on keys `fk`,
    /// and maps each key to the value given by `fv`.
    pub open spec fn new(fk: impl Fn(K) -> bool, fv: impl Fn(K) -> V) -> Map<K, V> {
        Set::new(fk).mk_map(fv)
    }

    /// The domain of the map as a set.
    pub spec fn dom(self) -> Set<K>;

    /// Gets the value that the given key `key` maps to.
    /// For keys not in the domain, the result is meaningless and arbitrary.
    pub spec fn index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    ;

    /// `[]` operator, synonymous with `index`
    #[verifier(inline)]
    pub open spec fn spec_index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        self.index(key)
    }

    /// Inserts the given (key, value) pair into the map.
    ///
    /// If the key is already present from the map, then its existing value is overwritten
    /// by the new value.
    pub spec fn insert(self, key: K, value: V) -> Map<K, V>;

    /// Removes the given key and its associated value from the map.
    ///
    /// If the key is already absent from the map, then the map is left unchanged.
    pub spec fn remove(self, key: K) -> Map<K, V>;

    /// Returns the number of key-value pairs in the map
    pub open spec fn len(self) -> nat {
        self.dom().len()
    }

    /// DEPRECATED: use =~= or =~~= instead.
    /// Returns true if the two maps are pointwise equal, i.e.,
    /// they have the same domains and the corresponding values are equal
    /// for each key. This is equivalent to the maps being actually equal
    /// by [`axiom_map_ext_equal`].
    ///
    /// To prove that two maps are equal via extensionality, it may be easier
    /// to use the general-purpose `=~=` or `=~~=` or
    /// to use the [`assert_maps_equal!`] macro, rather than using `.ext_equal` directly.
    #[deprecated = "use =~= or =~~= instead"]
    pub open spec fn ext_equal(self, m2: Map<K, V>) -> bool {
        self =~= m2
    }

    #[verifier(external_body)]
    pub proof fn tracked_empty() -> (tracked out_v: Self)
        ensures
            out_v == Map::<K, V>::empty(),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn tracked_insert(tracked &mut self, key: K, tracked value: V)
        ensures
            *self == Map::insert(*old(self), key, value),
    {
        unimplemented!();
    }

    /// todo fill in documentation
    #[verifier(external_body)]
    pub proof fn tracked_remove(tracked &mut self, key: K) -> (tracked v: V)
        requires
            old(self).dom().contains(key),
        ensures
            *self == Map::remove(*old(self), key),
            v == old(self)[key],
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn tracked_borrow(tracked &self, key: K) -> (tracked v: &V)
        requires
            self.dom().contains(key),
        ensures
            *v === self.index(key),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn tracked_map_keys<J>(
        tracked old_map: Map<K, V>,
        key_map: Map<J, K>,
    ) -> (tracked new_map: Map<J, V>)
        requires
            forall|j|
                #![auto]
                key_map.dom().contains(j) ==> old_map.dom().contains(key_map.index(j)),
            forall|j1, j2|
                #![auto]
                !equal(j1, j2) && key_map.dom().contains(j1) && key_map.dom().contains(j2)
                    ==> !equal(key_map.index(j1), key_map.index(j2)),
        ensures
            forall|j| #[trigger] new_map.dom().contains(j) <==> key_map.dom().contains(j),
            forall|j|
                key_map.dom().contains(j) ==> new_map.dom().contains(j) && #[trigger] new_map.index(
                    j,
                ) == old_map.index(key_map.index(j)),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn tracked_remove_keys(tracked &mut self, keys: Set<K>) -> (tracked out_map: Map<
        K,
        V,
    >)
        requires
            keys.subset_of(old(self).dom()),
        ensures
            self == old(self).remove_keys(keys),
            out_map == old(self).restrict(keys),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn tracked_union_prefer_right(tracked &mut self, right: Self)
        ensures
            *self == old(self).union_prefer_right(right),
    {
        unimplemented!();
    }
}

// Trusted axioms
/* REVIEW: this is simpler than the two separate axioms below -- would this be ok?
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_index_decreases<K, V>(m: Map<K, V>, key: K)
    requires
        m.dom().contains(key),
    ensures
        #[trigger](decreases_to!(m => m[key])),
{
}
*/

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_index_decreases_finite<K, V>(m: Map<K, V>, key: K)
    requires
        m.dom().finite(),
        m.dom().contains(key),
    ensures
        #[trigger] (decreases_to!(m => m[key])),
{
}

// REVIEW: this is currently a special case that is hard-wired into the verifier
// It implements a version of https://github.com/FStarLang/FStar/pull/2954 .
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_index_decreases_infinite<K, V>(m: Map<K, V>, key: K)
    requires
        m.dom().contains(key),
    ensures
        #[trigger] is_smaller_than_recursive_function_field(m[key], m),
{
}

/// The domain of the empty map is the empty set
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_empty<K, V>()
    ensures
        #[trigger] Map::<K, V>::empty().dom() == Set::<K>::empty(),
{
}

/// The domain of a map after inserting a key-value pair is equivalent to inserting the key into
/// the original map's domain set.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_insert_domain<K, V>(m: Map<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value).dom() == m.dom().insert(key),
{
}

/// Inserting `value` at `key` in `m` results in a map that maps `key` to `value`
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_insert_same<K, V>(m: Map<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value)[key] == value,
{
}

/// Inserting `value` at `key2` does not change the value mapped to by any other keys in `m`
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_insert_different<K, V>(m: Map<K, V>, key1: K, key2: K, value: V)
    requires
        m.dom().contains(key1),
        key1 != key2,
    ensures
        m.insert(key2, value)[key1] == m[key1],
{
}

/// The domain of a map after removing a key-value pair is equivalent to removing the key from
/// the original map's domain set.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_remove_domain<K, V>(m: Map<K, V>, key: K)
    ensures
        #[trigger] m.remove(key).dom() == m.dom().remove(key),
{
}

/// Removing a key-value pair from a map does not change the value mapped to by
/// any other keys in the map.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_remove_different<K, V>(m: Map<K, V>, key1: K, key2: K)
    requires
        m.dom().contains(key1),
        key1 != key2,
    ensures
        m.remove(key2)[key1] == m[key1],
{
}

/// Two maps are equivalent if their domains are equivalent and every key in their domains map to the same value.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_ext_equal<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    ensures
        #[trigger] (m1 =~= m2) <==> {
            &&& m1.dom() =~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] == m2[k]
        },
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_ext_equal_deep<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    ensures
        #[trigger] (m1 =~~= m2) <==> {
            &&& m1.dom() =~~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] =~~= m2[k]
        },
{
}

// Macros
#[doc(hidden)]
#[macro_export]
macro_rules! map_internal {
    [$($key:expr => $value:expr),* $(,)?] => {
        $crate::map::Map::empty()
            $(.insert($key, $value))*
    }
}

/// Create a map using syntax like `map![key1 => val1, key2 => val, ...]`.
///
/// This is equivalent to `Map::empty().insert(key1, val1).insert(key2, val2)...`.
///
/// Note that this does _not_ require all keys to be distinct. In the case that two
/// or more keys are equal, the resulting map uses the value of the rightmost entry.
#[macro_export]
macro_rules! map {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::map::map_internal!($($tail)*))
    };
}

#[doc(hidden)]
#[verifier(inline)]
pub open spec fn check_argument_is_map<K, V>(m: Map<K, V>) -> Map<K, V> {
    m
}

#[doc(hidden)]
pub use map_internal;
pub use map;

/// Prove two maps `map1` and `map2` are equal by proving that their values are equal at each key.
///
/// More precisely, `assert_maps_equal!` requires that for each key `k`:
///  * `map1` contains `k` in its domain if and only if `map2` does (`map1.dom().contains(k) <==> map2.dom().contains(k)`)
///  * If they contain `k` in their domains, then their values are equal (`map1.dom().contains(k) && map2.dom().contains(k) ==> map1[k] == map2[k]`)
///
/// The property that equality follows from these facts is often called _extensionality_.
///
/// `assert_maps_equal!` can handle many trivial-looking
/// identities without any additional help:
///
/// ```rust
/// proof fn insert_remove(m: Map<int, int>, k: int, v: int)
///     requires !m.dom().contains(k)
///     ensures m.insert(k, v).remove(k) == m
/// {
///     let m2 = m.insert(k, v).remove(k);
///     assert_maps_equal!(m == m2);
///     assert(m == m2);
/// }
/// ```
///
/// For more complex cases, a proof may be required for each key:
///
/// ```rust
/// proof fn bitvector_maps() {
///     let m1 = Map::<u64, u64>::new(
///         |key: u64| key & 31 == key,
///         |key: u64| key | 5);
///
///     let m2 = Map::<u64, u64>::new(
///         |key: u64| key < 32,
///         |key: u64| 5 | key);
///
///     assert_maps_equal!(m1 == m2, key => {
///         // Show that the domains of m1 and m2 are the same by showing their predicates
///         // are equivalent.
///         assert_bit_vector((key & 31 == key) <==> (key < 32));
///
///         // Show that the values are the same by showing that these expressions
///         // are equivalent.
///         assert_bit_vector(key | 5 == 5 | key);
///     });
/// }
/// ```
#[macro_export]
macro_rules! assert_maps_equal {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::map::assert_maps_equal_internal!($($tail)*))
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! assert_maps_equal_internal {
    (::builtin::spec_eq($m1:expr, $m2:expr)) => {
        assert_maps_equal_internal!($m1, $m2)
    };
    (::builtin::spec_eq($m1:expr, $m2:expr), $k:ident $( : $t:ty )? => $bblock:block) => {
        assert_maps_equal_internal!($m1, $m2, $k $( : $t )? => $bblock)
    };
    ($m1:expr, $m2:expr $(,)?) => {
        assert_maps_equal_internal!($m1, $m2, key => { })
    };
    ($m1:expr, $m2:expr, $k:ident $( : $t:ty )? => $bblock:block) => {
        #[verifier::spec] let m1 = $crate::map::check_argument_is_map($m1);
        #[verifier::spec] let m2 = $crate::map::check_argument_is_map($m2);
        ::builtin::assert_by(::builtin::equal(m1, m2), {
            ::builtin::assert_forall_by(|$k $( : $t )?| {
                // TODO better error message here: show the individual conjunct that fails,
                // and maybe give an error message in english as well
                ::builtin::ensures([
                    ::builtin::imply(#[verifier::trigger] m1.dom().contains($k), m2.dom().contains($k))
                    && ::builtin::imply(m2.dom().contains($k), m1.dom().contains($k))
                    && ::builtin::imply(m1.dom().contains($k) && m2.dom().contains($k),
                        ::builtin::equal(m1.index($k), m2.index($k)))
                ]);
                { $bblock }
            });
            ::builtin::assert_(::builtin::ext_equal(m1, m2));
        });
    }
}

#[doc(hidden)]
pub use assert_maps_equal_internal;
pub use assert_maps_equal;

impl<K, V> Map<K, V> {
    pub proof fn tracked_map_keys_in_place(
        #[verifier::proof]
        &mut self,
        key_map: Map<K, K>,
    )
        requires
            forall|j|
                #![auto]
                key_map.dom().contains(j) ==> old(self).dom().contains(key_map.index(j)),
            forall|j1, j2|
                #![auto]
                j1 != j2 && key_map.dom().contains(j1) && key_map.dom().contains(j2)
                    ==> key_map.index(j1) != key_map.index(j2),
        ensures
            forall|j| #[trigger] self.dom().contains(j) == key_map.dom().contains(j),
            forall|j|
                key_map.dom().contains(j) ==> self.dom().contains(j) && #[trigger] self.index(j)
                    == old(self).index(key_map.index(j)),
    {
        #[verifier::proof]
        let mut tmp = Self::tracked_empty();
        crate::modes::tracked_swap(&mut tmp, self);
        #[verifier::proof]
        let mut tmp = Self::tracked_map_keys(tmp, key_map);
        crate::modes::tracked_swap(&mut tmp, self);
    }
}

} // verus!
}

pub mod map_lib {
    use crate::map::Map;
    #[allow(unused_imports)]
    use crate::pervasive::*;
    use crate::set::*;
    #[cfg(verus_keep_ghost)]
    use crate::set_lib::*;
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use builtin_macros::*;

    verus! {

impl<K, V> Map<K, V> {
    /// Is `true` if called by a "full" map, i.e., a map containing every element of type `A`.
    #[verifier(inline)]
    pub open spec fn is_full(self) -> bool {
        self.dom().is_full()
    }

    /// Is `true` if called by an "empty" map, i.e., a map containing no elements and has length 0
    #[verifier(inline)]
    pub open spec fn is_empty(self) -> (b: bool) {
        self.dom().is_empty()
    }

    /// Returns true if the key `k` is in the domain of `self`.
    #[verifier(inline)]
    pub open spec fn contains_key(self, k: K) -> bool {
        self.dom().contains(k)
    }

    /// Returns true if the value `v` is in the range of `self`.
    pub open spec fn contains_value(self, v: V) -> bool {
        exists|i: K| #[trigger] self.dom().contains(i) && self[i] == v
    }

    ///
    /// Returns the set of values in the map.
    ///
    /// ## Example
    ///
    /// ```rust
    /// assert(
    ///    map![1 => 10, 2 => 11].values() =~= set![10, 11]
    /// );
    /// ```
    pub open spec fn values(self) -> Set<V> {
        Set::<V>::new(|v: V| self.contains_value(v))
    }

    /// Returns true if the key `k` is in the domain of `self`, and it maps to the value `v`.
    pub open spec fn contains_pair(self, k: K, v: V) -> bool {
        self.dom().contains(k) && self[k] == v
    }

    /// Returns true if `m1` is _contained in_ `m2`, i.e., the domain of `m1` is a subset
    /// of the domain of `m2`, and they agree on all values in `m1`.
    ///
    /// ## Example
    ///
    /// ```rust
    /// assert(
    ///    map![1 => 10, 2 => 11].le(map![1 => 10, 2 => 11, 3 => 12])
    /// );
    /// ```
    pub open spec fn submap_of(self, m2: Self) -> bool {
        forall|k: K| #[trigger]
            self.dom().contains(k) ==> #[trigger] m2.dom().contains(k) && self[k] == m2[k]
    }

    #[verifier(inline)]
    pub open spec fn spec_le(self, m2: Self) -> bool {
        self.submap_of(m2)
    }

    /// Deprecated synonym for `submap_of`
    #[verifier(inline)]
    #[deprecated = "use m1.submap_of(m2) or m1 <= m2 instead"]
    pub open spec fn le(self, m2: Self) -> bool {
        self.submap_of(m2)
    }

    /// Gives the union of two maps, defined as:
    ///  * The domain is the union of the two input maps.
    ///  * For a given key in _both_ input maps, it maps to the same value that it maps to in the _right_ map (`m2`).
    ///  * For any other key in either input map (but not both), it maps to the same value
    ///    as it does in that map.
    ///
    /// ## Example
    ///
    /// ```rust
    /// assert(
    ///    map![1 => 10, 2 => 11].union_prefer_right(map![1 => 20, 3 => 13])
    ///    =~= map![1 => 20, 2 => 11, 3 => 13]);
    /// ```
    pub open spec fn union_prefer_right(self, m2: Self) -> Self {
        Self::new(
            |k: K| self.dom().contains(k) || m2.dom().contains(k),
            |k: K|
                if m2.dom().contains(k) {
                    m2[k]
                } else {
                    self[k]
                },
        )
    }

    /// Removes the given keys and their associated values from the map.
    ///
    /// Ignores any key in `keys` which is not in the domain of `self`.
    ///
    /// ## Example
    ///
    /// ```rust
    /// assert(
    ///    map![1 => 10, 2 => 11, 3 => 12].remove_keys(set!{2, 3, 4})
    ///    =~= map![1 => 10]);
    /// ```
    pub open spec fn remove_keys(self, keys: Set<K>) -> Self {
        Self::new(|k: K| self.dom().contains(k) && !keys.contains(k), |k: K| self[k])
    }

    /// Complement to `remove_keys`. Restricts the map to (key, value) pairs
    /// for keys that are _in_ the given set; that is, it removes any keys
    /// _not_ in the set.
    ///
    /// ## Example
    ///
    /// ```rust
    /// assert(
    ///    map![1 => 10, 2 => 11, 3 => 12].remove_keys(set!{2, 3, 4})
    ///    =~= map![2 => 11, 3 => 12]);
    /// ```
    pub open spec fn restrict(self, keys: Set<K>) -> Self {
        Self::new(|k: K| self.dom().contains(k) && keys.contains(k), |k: K| self[k])
    }

    /// Returns `true` if and only if the given key maps to the same value or does not exist in self and m2.
    pub open spec fn is_equal_on_key(self, m2: Self, key: K) -> bool {
        ||| (!self.dom().contains(key) && !m2.dom().contains(key))
        ||| (self.dom().contains(key) && m2.dom().contains(key) && self[key] == m2[key])
    }

    /// Returns `true` if the two given maps agree on all keys that their domains share
    pub open spec fn agrees(self, m2: Self) -> bool {
        forall|k| #![auto] self.dom().contains(k) && m2.dom().contains(k) ==> self[k] == m2[k]
    }

    /// Map a function `f` over all (k, v) pairs in `self`.
    pub open spec fn map_entries<W>(self, f: spec_fn(K, V) -> W) -> Map<K, W> {
        Map::new(|k: K| self.contains_key(k), |k: K| f(k, self[k]))
    }

    /// Map a function `f` over the values in `self`.
    pub open spec fn map_values<W>(self, f: spec_fn(V) -> W) -> Map<K, W> {
        Map::new(|k: K| self.contains_key(k), |k: K| f(self[k]))
    }

    /// Returns `true` if and only if a map is injective
    pub open spec fn is_injective(self) -> bool {
        forall|x: K, y: K|
            x != y && self.dom().contains(x) && self.dom().contains(y) ==> #[trigger] self[x]
                != #[trigger] self[y]
    }

    /// Swaps map keys and values. Values are not required to be unique; no
    /// promises on which key is chosen on the intersection.
    pub open spec fn invert(self) -> Map<V, K> {
        Map::<V, K>::new(
            |v: V| self.contains_value(v),
            |v: V| choose|k: K| self.contains_pair(k, v),
        )
    }

    // Proven lemmas
    /// Removing a key from a map that previously contained that key decreases
    /// the map's length by one
    pub proof fn lemma_remove_key_len(self, key: K)
        requires
            self.dom().contains(key),
            self.dom().finite(),
        ensures
            self.dom().len() == 1 + self.remove(key).dom().len(),
    {
    }

    /// The domain of a map after removing a key is equivalent to removing the key from
    /// the domain of the original map.
    pub proof fn lemma_remove_equivalency(self, key: K)
        ensures
            self.remove(key).dom() == self.dom().remove(key),
    {
    }

    /// Removing a set of n keys from a map that previously contained all n keys
    /// results in a domain of size n less than the original domain.
    pub proof fn lemma_remove_keys_len(self, keys: Set<K>)
        requires
            forall|k: K| #[trigger] keys.contains(k) ==> self.contains_key(k),
            keys.finite(),
            self.dom().finite(),
        ensures
            self.remove_keys(keys).dom().len() == self.dom().len() - keys.len(),
        decreases keys.len(),
    {
        lemma_set_properties::<K>();
        if keys.len() > 0 {
            let key = keys.choose();
            let val = self[key];
            self.remove(key).lemma_remove_keys_len(keys.remove(key));
            assert(self.remove(key).remove_keys(keys.remove(key)) =~= self.remove_keys(keys));
        } else {
            assert(self.remove_keys(keys) =~= self);
        }
    }

    /// The function `invert` results in an injective map
    pub proof fn lemma_invert_is_injective(self)
        ensures
            self.invert().is_injective(),
    {
        assert forall|x: V, y: V|
            x != y && self.invert().dom().contains(x) && self.invert().dom().contains(
                y,
            ) implies #[trigger] self.invert()[x] != #[trigger] self.invert()[y] by {
            let i = choose|i: K| #[trigger] self.dom().contains(i) && self[i] == x;
            assert(self.contains_pair(i, x));
            let j = choose|j: K| self.contains_pair(j, x) && self.invert()[x] == j;
            let k = choose|k: K| #[trigger] self.dom().contains(k) && self[k] == y;
            assert(self.contains_pair(k, y));
            let l = choose|l: K| self.contains_pair(l, y) && self.invert()[y] == l && l != j;
        }
    }
}

impl Map<int, int> {
    /// Returns `true` if a map is monotonic -- that is, if the mapping between ordered sets
    /// preserves the regular `<=` ordering on integers.
    pub open spec fn is_monotonic(self) -> bool {
        forall|x: int, y: int|
            self.dom().contains(x) && self.dom().contains(y) && x <= y ==> #[trigger] self[x]
                <= #[trigger] self[y]
    }

    /// Returns `true` if and only if a map is monotonic, only considering keys greater than
    /// or equal to start
    pub open spec fn is_monotonic_from(self, start: int) -> bool {
        forall|x: int, y: int|
            self.dom().contains(x) && self.dom().contains(y) && start <= x <= y
                ==> #[trigger] self[x] <= #[trigger] self[y]
    }
}

// Proven lemmas
/// The size of the union of two disjoint maps is equal to the sum of the sizes of the individual maps
pub proof fn lemma_disjoint_union_size<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        m1.dom().disjoint(m2.dom()),
        m1.dom().finite(),
        m2.dom().finite(),
    ensures
        m1.union_prefer_right(m2).dom().len() == m1.dom().len() + m2.dom().len(),
{
    let u = m1.union_prefer_right(m2);
    assert(u.dom() =~= m1.dom() + m2.dom());  //proves u.dom() is finite
    assert(u.remove_keys(m1.dom()).dom() =~= m2.dom());
    assert(u.remove_keys(m1.dom()).dom().len() == u.dom().len() - m1.dom().len()) by {
        u.lemma_remove_keys_len(m1.dom());
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The domain of a map constructed with `Map::new(fk, fv)` is equivalent to the set constructed with `Set::new(fk)`.
pub proof fn lemma_map_new_domain<K, V>(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V)
    ensures
        Map::<K, V>::new(fk, fv).dom() == Set::<K>::new(|k: K| fk(k)),
{
    assert(Set::new(fk) =~= Set::<K>::new(|k: K| fk(k)));
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The set of values of a map constructed with `Map::new(fk, fv)` is equivalent to
/// the set constructed with `Set::new(|v: V| (exists |k: K| fk(k) && fv(k) == v)`. In other words,
/// the set of all values fv(k) where fk(k) is true.
pub proof fn lemma_map_new_values<K, V>(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V)
    ensures
        Map::<K, V>::new(fk, fv).values() == Set::<V>::new(
            |v: V| (exists|k: K| #[trigger] fk(k) && #[trigger] fv(k) == v),
        ),
{
    let keys = Set::<K>::new(fk);
    let values = Map::<K, V>::new(fk, fv).values();
    let map = Map::<K, V>::new(fk, fv);
    assert(map.dom() =~= keys);
    assert(forall|k: K| #[trigger] fk(k) ==> keys.contains(k));
    assert(values =~= Set::<V>::new(
        |v: V| (exists|k: K| #[trigger] fk(k) && #[trigger] fv(k) == v),
    ));
}

/// Properties of maps from the Dafny prelude (which were axioms in Dafny, but proven here in Verus)
pub proof fn lemma_map_properties<K, V>()
    ensures
        forall|fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V| #[trigger]
            Map::<K, V>::new(fk, fv).dom() == Set::<K>::new(|k: K| fk(k)),  //from lemma_map_new_domain
        forall|fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V| #[trigger]
            Map::<K, V>::new(fk, fv).values() == Set::<V>::new(
                |v: V| exists|k: K| #[trigger] fk(k) && #[trigger] fv(k) == v,
            ),  //from lemma_map_new_values
{
    assert forall|fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V| #[trigger]
        Map::<K, V>::new(fk, fv).dom() == Set::<K>::new(|k: K| fk(k)) by {
        lemma_map_new_domain(fk, fv);
    }
    assert forall|fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V| #[trigger]
        Map::<K, V>::new(fk, fv).values() == Set::<V>::new(
            |v: V| exists|k: K| #[trigger] fk(k) && #[trigger] fv(k) == v,
        ) by {
        lemma_map_new_values(fk, fv);
    }
}

pub proof fn lemma_values_finite<K, V>(m: Map<K, V>)
    requires
        m.dom().finite(),
    ensures
        m.values().finite(),
    decreases m.len(),
{
    if m.len() > 0 {
        let k = m.dom().choose();
        let v = m[k];
        let m1 = m.remove(k);
        assert(m.contains_key(k));
        assert(m.contains_value(v));
        let mv = m.values();
        let m1v = m1.values();
        assert_sets_equal!(mv == m1v.insert(v), v0 => {
            if m.contains_value(v0) {
                if v0 != v {
                    let k0 = choose|k0| #![auto] m.contains_key(k0) && m[k0] == v0;
                    assert(k0 != k);
                    assert(m1.contains_key(k0));
                    assert(mv.contains(v0) ==> m1v.insert(v).contains(v0));
                    assert(mv.contains(v0) <== m1v.insert(v).contains(v0));
                }
            }
        });
        assert(m1.len() < m.len());
        lemma_values_finite(m1);
        axiom_set_insert_finite(m1.values(), v);
    } else {
        assert(m.values() =~= Set::<V>::empty());
    }
}

} // verus!
}

pub mod math {
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use builtin_macros::*;

    verus! {

/// This function computes the minimum of two given integers.
pub open spec fn min(x: int, y: int) -> int {
    if x <= y {
        x
    } else {
        y
    }
}

/// This function computes the maximum of two given integers.
pub open spec fn max(x: int, y: int) -> int {
    if x >= y {
        x
    } else {
        y
    }
}

/// This function computes the maximum of three given integers.
pub open spec fn max3(x: int, y: int, z: int) -> int {
    if x < y {
        max(y, z)
    } else {
        max(x, z)
    }
}

/// This function converts the given integer `x` to a natural number
/// by returning 0 when `x` is negative and `x` otherwise.
pub open spec fn clip(x: int) -> nat {
    if x < 0 {
        0
    } else {
        x as nat
    }
}

/// This function computes the absolute value of a given integer.
pub open spec fn abs(x: int) -> nat {
    if x < 0 {
        -x as nat
    } else {
        x as nat
    }
}

/// This function adds two integers together. It's sometimes
/// useful as a substitute for `+` in triggers that feature
/// function invocations, since mathematical operators can't be
/// mixed with function invocations in triggers.
pub open spec fn add(x: int, y: int) -> int {
    x + y
}

/// This function subtracts two integers. It's sometimes useful as
/// a substitute for `-` in triggers that feature function
/// invocations, since mathematical operators can't be mixed with
/// function invocations in triggers.
pub open spec fn sub(x: int, y: int) -> int {
    x - y
}

/// This function divides two integers. It's sometimes useful as a
/// substitute for `/` in triggers that feature function
/// invocations, since mathematical operators can't be mixed with
/// function invocations in triggers.
pub open spec fn div(x: int, y: int) -> int {
    x / y
}

} // verus!
}

pub mod modes {
    #[allow(unused_imports)]
    use crate::pervasive::*;
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use builtin_macros::*;
    //use core::marker::PhantomData;

    verus! {

#[verifier(external_body)]
pub proof fn tracked_swap<V>(tracked a: &mut V, tracked b: &mut V)
    ensures
        a == old(b),
        b == old(a),
{
    unimplemented!();
}

#[verifier(external_body)]
pub proof fn tracked_static_ref<V>(tracked v: V) -> (tracked res: &'static V)
    ensures
        res == v,
{
    unimplemented!();
}

} // verus!
    // verus
}

pub mod multiset {
    use core::marker;

    #[allow(unused_imports)]
    use crate::map::*;
    #[cfg(verus_keep_ghost)]
    use crate::math::clip;
    #[cfg(verus_keep_ghost)]
    use crate::math::min;
    #[allow(unused_imports)]
    use crate::pervasive::*;
    #[allow(unused_imports)]
    use crate::set::*;
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use builtin_macros::*;

    verus! {

/// `Multiset<V>` is an abstract multiset type for specifications.
///
/// `Multiset<V>` can be encoded as a (total) map from elements to natural numbers,
/// where the number of nonzero entries is finite.
///
/// Multisets can be constructed in a few different ways:
///  * [`Multiset::empty()`] constructs an empty multiset.
///  * [`Multiset::singleton`] constructs a multiset that contains a single element with multiplicity 1.
///  * [`Multiset::new`] constructs a multiset from a map of elements to multiplicities.
///  * By manipulating existings multisets with [`Multiset::add`], [`Multiset::insert`],
///    [`Multiset::sub`], [`Multiset::remove`], [`Multiset::update`], or [`Multiset::filter`].
///  * TODO: `multiset!` constructor macro, multiset from set, from map, etc.
///
/// To prove that two multisets are equal, it is usually easiest to use the
/// extensionality operator `=~=`.
// We could in principle implement the Multiset via an inductive datatype
// and so we can mark its type argument as accept_recursive_types.
// Note: Multiset is finite (in contrast to Set, Map, which are infinite) because it
// isn't entirely obvious how to represent an infinite multiset in the case where
// a single value (v: V) has an infinite multiplicity. It seems to require either:
//   (1) representing multiplicity by an ordinal or cardinal or something
//   (2) limiting each multiplicity to be finite
// (1) would be complicated and it's not clear what the use would be; (2) has some
// weird properties (e.g., you can't in general define a multiset `map` function
// since it might map an infinite number of elements to the same one).
#[verifier(external_body)]
#[verifier::ext_equal]
#[verifier::accept_recursive_types(V)]
pub struct Multiset<V> {
    dummy: marker::PhantomData<V>,
}

impl<V> Multiset<V> {
    /// Returns the _count_, or _multiplicity_ of a single value within the multiset.
    pub spec fn count(self, value: V) -> nat;

    /// The total size of the multiset, i.e., the sum of all multiplicities over all values.
    pub spec fn len(self) -> nat;

    /// An empty multiset.
    pub spec fn empty() -> Self;

    /// Creates a multiset whose elements are given by the domain of the map `m` and whose
    /// multiplicities are given by the corresponding values of `m[element]`. The map `m`
    /// must be finite, or else this multiset is arbitrary.
    pub open spec fn from_map(m: Map<V, nat>) -> Self;

    #[deprecated = "use from_map instead"]
    pub open spec fn new(m: Map<V, nat>) -> Self {
        Self::from_map(m)
    }

    pub open spec fn from_set(m: Set<V>) -> Self {
        Self::from_map(Map::new(|k| m.contains(k), |v| 1))
    }

    /// A singleton multiset, i.e., a multiset with a single element of multiplicity 1.
    pub spec fn singleton(v: V) -> Self;

    /// Takes the union of two multisets. For a given element, its multiplicity in
    /// the resulting multiset is the sum of its multiplicities in the operands.
    pub spec fn add(self, m2: Self) -> Self;

    /// Takes the difference of two multisets.
    /// The multiplicities of `m2` are subtracted from those of `self`; if any element
    /// occurs more in `m2` then the resulting multiplicity bottoms out at 0.
    /// (See [`axiom_multiset_sub`] for the precise definition.)
    ///
    /// Note in particular that `self == self.sub(m).add(m)` only holds if
    /// `m` is included in `self`.
    pub spec fn sub(self, m2: Self) -> Self;

    /// Inserts one instance the value `v` into the multiset.
    ///
    /// This always increases the total size of the multiset by 1.
    pub open spec fn insert(self, v: V) -> Self {
        self.add(Self::singleton(v))
    }

    /// Removes one instance of the value `v` from the multiset.
    ///
    /// If `v` was absent from the multiset, then the multiset is unchanged.
    pub open spec fn remove(self, v: V) -> Self {
        self.sub(Self::singleton(v))
    }

    /// Updates the multiplicity of the value `v` in the multiset to `mult`.
    pub open spec fn update(self, v: V, mult: nat) -> Self {
        let map = Map::new(
            |key: V| (self.contains(key) || key == v),
            |key: V|
                if key == v {
                    mult
                } else {
                    self.count(key)
                },
        );
        Self::from_map(map)
    }

    /// Returns `true` is the left argument is contained in the right argument,
    /// that is, if for each value `v`, the number of occurences in the left
    /// is at most the number of occurences in the right.
    pub open spec fn subset_of(self, m2: Self) -> bool {
        forall|v: V| self.count(v) <= m2.count(v)
    }

    #[verifier(inline)]
    #[deprecated = "use m1.subset_of(m2) or m1 <= m2 instead"]
    pub open spec fn le(self, m2: Self) -> bool {
        self.subset_of(m2)
    }

    #[verifier(inline)]
    pub open spec fn spec_le(self, m2: Self) -> bool {
        self.subset_of(m2)
    }

    /// DEPRECATED: use =~= or =~~= instead.
    /// Returns true if the two multisets are pointwise equal, i.e.,
    /// for every value `v: V`, the counts are the same in each multiset.
    /// This is equivalent to the multisets actually being equal
    /// by [`axiom_multiset_ext_equal`].
    ///
    /// To prove that two maps are equal via extensionality, it may be easier
    /// to use the general-purpose `=~=` or `=~~=` or
    /// to use the [`assert_multisets_equal!`] macro, rather than using `ext_equal` directly.
    #[deprecated = "use =~= or =~~= instead"]
    pub open spec fn ext_equal(self, m2: Self) -> bool {
        self =~= m2
    }

    // TODO define this in terms of a more general constructor?
    pub spec fn filter(self, f: impl Fn(V) -> bool) -> Self;

    /// Chooses an arbitrary value of the multiset.
    ///
    /// This is often useful for proofs by induction.
    ///
    /// (Note that, although the result is arbitrary, it is still a _deterministic_ function
    /// like any other `spec` function.)
    pub open spec fn choose(self) -> V {
        choose|v: V| self.count(v) > 0
    }

    /// Predicate indicating if the multiset contains the given value.
    pub open spec fn contains(self, v: V) -> bool {
        self.count(v) > 0
    }

    /// Returns a multiset containing the lower count of a given element
    /// between the two sets. In other words, returns a multiset with only
    /// the elements that "overlap".
    pub open spec fn intersection_with(self, other: Self) -> Self {
        let m = Map::<V, nat>::new(
            |v: V| self.contains(v),
            |v: V| min(self.count(v) as int, other.count(v) as int) as nat,
        );
        Self::from_map(m)
    }

    /// Returns a multiset containing the difference between the count of a
    /// given element of the two sets.
    pub open spec fn difference_with(self, other: Self) -> Self {
        let m = Map::<V, nat>::new(
            |v: V| self.contains(v),
            |v: V| clip(self.count(v) - other.count(v)),
        );
        Self::from_map(m)
    }

    /// Returns true if there exist no elements that have a count greater
    /// than 0 in both multisets. In other words, returns true if the two
    /// multisets have no elements in common.
    pub open spec fn is_disjoint_from(self, other: Self) -> bool {
        forall|x: V| self.count(x) == 0 || other.count(x) == 0
    }

    /// Returns the set of all elements that have a count greater than 0
    pub open spec fn dom(self) -> Set<V> {
        Set::new(|v: V| self.count(v) > 0)
    }
}

// Specification of `empty`
/// The empty multiset maps every element to multiplicity 0
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_empty<V>(v: V)
    ensures
        Multiset::empty().count(v) == 0,
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// A multiset is equivalent to the empty multiset if and only if it has length 0.
/// If the multiset has length greater than 0, then there exists some element in the
/// multiset that has a count greater than 0.
pub proof fn lemma_multiset_empty_len<V>(m: Multiset<V>)
    ensures
        (m.len() == 0 <==> m =~= Multiset::empty()) && (m.len() > 0 ==> exists|v: V|
            0 < m.count(v)),
{
}

// Specifications of `from_map`
/// A call to Multiset::new with input map `m` will return a multiset that maps
/// value `v` to multiplicity `m[v]` if `v` is in the domain of `m`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_contained<V>(m: Map<V, nat>, v: V)
    requires
        m.dom().finite(),
        m.dom().contains(v),
    ensures
        #[trigger] Multiset::from_map(m).count(v) == m[v],
{
}

/// A call to Multiset::new with input map `m` will return a multiset that maps
/// value `v` to multiplicity 0 if `v` is not in the domain of `m`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_new_not_contained<V>(m: Map<V, nat>, v: V)
    requires
        m.dom().finite(),
        !m.dom().contains(v),
    ensures
        Multiset::from_map(m).count(v) == 0,
{
}

// Specification of `singleton`
/// A call to Multiset::singleton with input value `v` will return a multiset that maps
/// value `v` to multiplicity 1.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_singleton<V>(v: V)
    ensures
        (#[trigger] Multiset::singleton(v)).count(v) == 1,
{
}

/// A call to Multiset::singleton with input value `v` will return a multiset that maps
/// any value other than `v` to 0
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_singleton_different<V>(v: V, w: V)
    ensures
        v != w ==> Multiset::singleton(v).count(w) == 0,
{
}

// Specification of `add`
/// The count of value `v` in the multiset `m1.add(m2)` is equal to the sum of the
/// counts of `v` in `m1` and `m2` individually.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_add<V>(m1: Multiset<V>, m2: Multiset<V>, v: V)
    ensures
        m1.add(m2).count(v) == m1.count(v) + m2.count(v),
{
}

// Specification of `sub`
/// The count of value `v` in the multiset `m1.sub(m2)` is equal to the difference between the
/// count of `v` in `m1` and `m2` individually. However, the difference is cut off at 0 and
/// cannot be negative.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_sub<V>(m1: Multiset<V>, m2: Multiset<V>, v: V)
    ensures
        m1.sub(m2).count(v) == if m1.count(v) >= m2.count(v) {
            m1.count(v) - m2.count(v)
        } else {
            0
        },
{
}

// Extensional equality
/// Two multisets are equivalent if and only if they have the same count for every value.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_ext_equal<V>(m1: Multiset<V>, m2: Multiset<V>)
    ensures
        #[trigger] (m1 =~= m2) <==> (forall|v: V| m1.count(v) == m2.count(v)),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_ext_equal_deep<V>(m1: Multiset<V>, m2: Multiset<V>)
    ensures
        #[trigger] (m1 =~~= m2) <==> m1 =~= m2,
{
}

// Specification of `len`
/// The length of the empty multiset is 0.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_len_empty<V>()
    ensures
        (#[trigger] Multiset::<V>::empty().len()) == 0,
{
}

/// The length of a singleton multiset is 1.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_len_singleton<V>(v: V)
    ensures
        (#[trigger] Multiset::<V>::singleton(v).len()) == 1,
{
}

/// The length of the addition of two multisets is equal to the sum of the lengths of each individual multiset.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_len_add<V>(m1: Multiset<V>, m2: Multiset<V>)
    ensures
        (#[trigger] m1.add(m2).len()) == m1.len() + m2.len(),
{
}

// TODO could probably prove this theorem.
/// The length of the subtraction of two multisets is equal to the difference between the lengths of each individual multiset.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_len_sub<V>(m1: Multiset<V>, m2: Multiset<V>)
    requires
        m2.subset_of(m1),
    ensures
        (#[trigger] m1.sub(m2).len()) == m1.len() - m2.len(),
{
}

/// The count for any given value `v` in a multiset `m` must be less than or equal to the length of `m`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_count_le_len<V>(m: Multiset<V>, v: V)
    ensures
        #[trigger] m.count(v) <= #[trigger] m.len(),
{
}

// Specification of `filter`
/// For a given value `v` and boolean predicate `f`, if `f(v)` is true, then the count of `v` in
/// `m.filter(f)` is the same as the count of `v` in `m`. Otherwise, the count of `v` in `m.filter(f)` is 0.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_filter_count<V>(m: Multiset<V>, f: spec_fn(V) -> bool, v: V)
    ensures
        (#[trigger] m.filter(f).count(v)) == if f(v) {
            m.count(v)
        } else {
            0
        },
{
}

// Specification of `choose`
/// In a nonempty multiset `m`, the `choose` function will return a value that maps to a multiplicity
/// greater than 0 in `m`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_choose_count<V>(m: Multiset<V>)
    requires
        #[trigger] m.len() != 0,
    ensures
        #[trigger] m.count(m.choose()) > 0,
{
}

// Axiom about finiteness
/// The domain of a multiset (the set of all values that map to a multiplicity greater than 0) is always finite.
// NB this axiom's soundness depends on the inability to learn anything about the entirety of
// Multiset::from_map.dom().
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_always_finite<V>(m: Multiset<V>)
    ensures
        #[trigger] m.dom().finite(),
{
}

// Lemmas about `update`
/// The multiset resulting from updating a value `v` in a multiset `m` to multiplicity `mult` will
/// have a count of `mult` for `v`.
pub proof fn lemma_update_same<V>(m: Multiset<V>, v: V, mult: nat)
    ensures
        m.update(v, mult).count(v) == mult,
{
    let map = Map::new(
        |key: V| (m.contains(key) || key == v),
        |key: V|
            if key == v {
                mult
            } else {
                m.count(key)
            },
    );
    assert(map.dom() =~= m.dom().insert(v));
}

/// The multiset resulting from updating a value `v1` in a multiset `m` to multiplicity `mult` will
/// not change the multiplicities of any other values in `m`.
pub proof fn lemma_update_different<V>(m: Multiset<V>, v1: V, mult: nat, v2: V)
    requires
        v1 != v2,
    ensures
        m.update(v1, mult).count(v2) == m.count(v2),
{
    let map = Map::new(
        |key: V| (m.contains(key) || key == v1),
        |key: V|
            if key == v1 {
                mult
            } else {
                m.count(key)
            },
    );
    assert(map.dom() =~= m.dom().insert(v1));
}

// Lemmas about `insert`
// This verified lemma used to be an axiom in the Dafny prelude
/// If you insert element x into multiset m, then element y maps
/// to a count greater than 0 if and only if x==y or y already
/// mapped to a count greater than 0 before the insertion of x.
pub proof fn lemma_insert_containment<V>(m: Multiset<V>, x: V, y: V)
    ensures
        0 < m.insert(x).count(y) <==> x == y || 0 < m.count(y),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Inserting an element `x` into multiset `m` will increase the count of `x` in `m` by 1.
pub proof fn lemma_insert_increases_count_by_1<V>(m: Multiset<V>, x: V)
    ensures
        m.insert(x).count(x) == m.count(x) + 1,
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If multiset `m` maps element `y` to a multiplicity greater than 0, then inserting any element `x`
/// into `m` will not cause `y` to map to a multiplicity of 0. This is a way of saying that inserting `x`
/// will not cause any counts to decrease, because it accounts both for when x == y and when x != y.
pub proof fn lemma_insert_non_decreasing<V>(m: Multiset<V>, x: V, y: V)
    ensures
        0 < m.count(y) ==> 0 < m.insert(x).count(y),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Inserting an element `x` into a multiset `m` will not change the count of any other element `y` in `m`.
pub proof fn lemma_insert_other_elements_unchanged<V>(m: Multiset<V>, x: V, y: V)
    ensures
        x != y ==> m.count(y) == m.insert(x).count(y),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Inserting an element `x` into a multiset `m` will increase the length of `m` by 1.
pub proof fn lemma_insert_len<V>(m: Multiset<V>, x: V)
    ensures
        m.insert(x).len() == m.len() + 1,
{
}

// Lemmas about `intersection_with`
// This verified lemma used to be an axiom in the Dafny prelude
/// The multiplicity of an element `x` in the intersection of multisets `a` and `b` will be the minimum
/// count of `x` in either `a` or `b`.
pub proof fn lemma_intersection_count<V>(a: Multiset<V>, b: Multiset<V>, x: V)
    ensures
        a.intersection_with(b).count(x) == min(a.count(x) as int, b.count(x) as int),
{
    let m = Map::<V, nat>::new(
        |v: V| a.contains(v),
        |v: V| min(a.count(v) as int, b.count(v) as int) as nat,
    );
    assert(m.dom() =~= a.dom());
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the intersection of multisets `a` and `b` and then taking the resulting multiset's intersection
/// with `b` again is the same as just taking the intersection of `a` and `b` once.
pub proof fn lemma_left_pseudo_idempotence<V>(a: Multiset<V>, b: Multiset<V>)
    ensures
        a.intersection_with(b).intersection_with(b) =~= a.intersection_with(b),
{
    assert forall|x: V| #[trigger]
        a.intersection_with(b).count(x) == min(a.count(x) as int, b.count(x) as int) by {
        lemma_intersection_count(a, b, x);
    }
    assert forall|x: V| #[trigger]
        a.intersection_with(b).intersection_with(b).count(x) == min(
            a.count(x) as int,
            b.count(x) as int,
        ) by {
        lemma_intersection_count(a.intersection_with(b), b, x);
        assert(min(min(a.count(x) as int, b.count(x) as int) as int, b.count(x) as int) == min(
            a.count(x) as int,
            b.count(x) as int,
        ));
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the intersection of multiset `a` with the result of taking the intersection of `a` and `b`
/// is the same as just taking the intersection of `a` and `b` once.
pub proof fn lemma_right_pseudo_idempotence<V>(a: Multiset<V>, b: Multiset<V>)
    ensures
        a.intersection_with(a.intersection_with(b)) =~= a.intersection_with(b),
{
    assert forall|x: V| #[trigger]
        a.intersection_with(b).count(x) == min(a.count(x) as int, b.count(x) as int) by {
        lemma_intersection_count(a, b, x);
    }
    assert forall|x: V| #[trigger]
        a.intersection_with(a.intersection_with(b)).count(x) == min(
            a.count(x) as int,
            b.count(x) as int,
        ) by {
        lemma_intersection_count(a, a.intersection_with(b), x);
        assert(min(a.count(x) as int, min(a.count(x) as int, b.count(x) as int) as int) == min(
            a.count(x) as int,
            b.count(x) as int,
        ));
    }
}

// Lemmas about `difference_with`
// This verified lemma used to be an axiom in the Dafny prelude
/// The multiplicity of an element `x` in the difference of multisets `a` and `b` will be
/// equal to the difference of the counts of `x` in `a` and `b`, or 0 if this difference is negative.
pub proof fn lemma_difference_count<V>(a: Multiset<V>, b: Multiset<V>, x: V)
    ensures
        a.difference_with(b).count(x) == clip(a.count(x) - b.count(x)),
{
    let m = Map::<V, nat>::new(|v: V| a.contains(v), |v: V| clip(a.count(v) - b.count(v)));
    assert(m.dom() =~= a.dom());
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If the multiplicity of element `x` is less in multiset `a` than in multiset `b`, then the multiplicity
/// of `x` in the difference of `a` and `b` will be 0.
pub proof fn lemma_difference_bottoms_out<V>(a: Multiset<V>, b: Multiset<V>, x: V)
    ensures
        a.count(x) <= b.count(x) ==> a.difference_with(b).count(x) == 0,
{
    lemma_difference_count(a, b, x);
}

#[macro_export]
macro_rules! assert_multisets_equal {
    (::builtin::spec_eq($m1:expr, $m2:expr)) => {
        assert_multisets_equal_internal!($m1, $m2)
    };
    (::builtin::spec_eq($m1:expr, $m2:expr), $k:ident $( : $t:ty )? => $bblock:block) => {
        assert_multisets_equal_internal!($m1, $m2, $k $( : $t )? => $bblock)
    };
    ($m1:expr, $m2:expr $(,)?) => {
        assert_multisets_equal!($m1, $m2, key => { })
    };
    ($m1:expr, $m2:expr, $k:ident $( : $t:ty )? => $bblock:block) => {
        #[verifier::spec] let m1 = $m1;
        #[verifier::spec] let m2 = $m2;
        ::builtin::assert_by(::builtin::equal(m1, m2), {
            ::builtin::assert_forall_by(|$k $( : $t )?| {
                ::builtin::ensures([
                    ::builtin::equal(m1.count($k), m2.count($k))
                ]);
                { $bblock }
            });
            ::builtin::assert_(::builtin::ext_equal(m1, m2));
        });
    }
}

/// Properties of multisets from the Dafny prelude (which were axioms in Dafny, but proven here in Verus)
pub proof fn lemma_multiset_properties<V>()
    ensures
        forall|m: Multiset<V>, v: V, mult: nat| #[trigger] m.update(v, mult).count(v) == mult,  //from lemma_update_same
        forall|m: Multiset<V>, v1: V, mult: nat, v2: V|
            v1 != v2 ==> #[trigger] m.update(v1, mult).count(v2) == m.count(v2),  //from lemma_update_different
        forall|m: Multiset<V>|
            (#[trigger] m.len() == 0 <==> m =~= Multiset::empty()) && (#[trigger] m.len() > 0
                ==> exists|v: V| 0 < m.count(v)),  //from lemma_multiset_empty_len
        forall|m: Multiset<V>, x: V, y: V|
            0 < #[trigger] m.insert(x).count(y) <==> x == y || 0 < m.count(y),  //from lemma_insert_containment
        forall|m: Multiset<V>, x: V| #[trigger] m.insert(x).count(x) == m.count(x) + 1,  //from lemma_insert_increases_count_by_1
        forall|m: Multiset<V>, x: V, y: V| 0 < m.count(y) ==> 0 < #[trigger] m.insert(x).count(y),  //from lemma_insert_non_decreasing
        forall|m: Multiset<V>, x: V, y: V|
            x != y ==> #[trigger] m.count(y) == #[trigger] m.insert(x).count(y),  //from lemma_insert_other_elements_unchanged
        forall|m: Multiset<V>, x: V| #[trigger] m.insert(x).len() == m.len() + 1,  //from lemma_insert_len
        forall|a: Multiset<V>, b: Multiset<V>, x: V| #[trigger]
            a.intersection_with(b).count(x) == min(a.count(x) as int, b.count(x) as int),  //from lemma_intersection_count
        forall|a: Multiset<V>, b: Multiset<V>| #[trigger]
            a.intersection_with(b).intersection_with(b) == a.intersection_with(b),  //from lemma_left_pseudo_idempotence
        forall|a: Multiset<V>, b: Multiset<V>| #[trigger]
            a.intersection_with(a.intersection_with(b)) == a.intersection_with(b),  //from lemma_right_pseudo_idempotence
        forall|a: Multiset<V>, b: Multiset<V>, x: V| #[trigger]
            a.difference_with(b).count(x) == clip(a.count(x) - b.count(x)),  //from lemma_difference_count
        forall|a: Multiset<V>, b: Multiset<V>, x: V| #[trigger]
            a.count(x) <= #[trigger] b.count(x) ==> (#[trigger] a.difference_with(b)).count(x)
                == 0,  //from lemma_difference_bottoms_out
{
    assert forall|m: Multiset<V>, v: V, mult: nat| #[trigger]
        m.update(v, mult).count(v) == mult by {
        lemma_update_same(m, v, mult);
    }
    assert forall|m: Multiset<V>, v1: V, mult: nat, v2: V| v1 != v2 implies #[trigger] m.update(
        v1,
        mult,
    ).count(v2) == m.count(v2) by {
        lemma_update_different(m, v1, mult, v2);
    }
    assert forall|a: Multiset<V>, b: Multiset<V>, x: V| #[trigger]
        a.intersection_with(b).count(x) == min(a.count(x) as int, b.count(x) as int) by {
        lemma_intersection_count(a, b, x);
    }
    assert forall|a: Multiset<V>, b: Multiset<V>| #[trigger]
        a.intersection_with(b).intersection_with(b) == a.intersection_with(b) by {
        lemma_left_pseudo_idempotence(a, b);
    }
    assert forall|a: Multiset<V>, b: Multiset<V>| #[trigger]
        a.intersection_with(a.intersection_with(b)) == a.intersection_with(b) by {
        lemma_right_pseudo_idempotence(a, b);
    }
    assert forall|a: Multiset<V>, b: Multiset<V>, x: V| #[trigger]
        a.difference_with(b).count(x) == clip(a.count(x) - b.count(x)) by {
        lemma_difference_count(a, b, x);
    }
}

pub use assert_multisets_equal;

} // verus!
}

pub mod option {
    #![deprecated(note = "Use std::option instead")]

    #[allow(unused_imports)]
    use crate::pervasive::*;
    #[allow(unused_imports)]
    use builtin::*;
    use builtin_macros::*;

    verus! {

#[is_variant]
#[verifier::ext_equal]
#[verifier::accept_recursive_types(A)]
pub enum Option<A> {
    None,
    Some(A),
}

pub use crate::option::Option::None;
pub use crate::option::Option::Some;

// TODO this currently doesn't work without `external`,
// because of some temporary Verus trait limitations,
// but we need to implement Copy.
#[verifier(external)]
impl<A: Clone> Clone for Option<A> {
    fn clone(&self) -> Self {
        match self {
            Option::None => Option::None,
            Option::Some(a) => Option::Some(a.clone()),
        }
    }
}

impl<A: Copy> Copy for Option<A> {

}

impl<A> Option<A> {
    pub open spec fn or(self, optb: Option<A>) -> Option<A> {
        match self {
            Option::None => optb,
            Option::Some(s) => self,
        }
    }

    #[inline(always)]
    pub const fn is_some(&self) -> (res: bool)
        ensures
            res <==> self.is_Some(),
    {
        match self {
            Option::Some(_) => true,
            Option::None => false,
        }
    }

    #[inline(always)]
    pub const fn is_none(&self) -> (res: bool)
        ensures
            res <==> self.is_None(),
    {
        match self {
            Option::Some(_) => false,
            Option::None => true,
        }
    }

    pub fn as_ref(&self) -> (a: Option<&A>)
        ensures
            a.is_Some() <==> self.is_Some(),
            a.is_Some() ==> self.get_Some_0() == a.get_Some_0(),
    {
        match self {
            Option::Some(x) => Option::Some(x),
            Option::None => Option::None,
        }
    }

    // A more-readable synonym for get_Some_0().
    #[verifier(inline)]
    pub open spec fn spec_unwrap(self) -> A
        recommends
            self.is_Some(),
    {
        self.get_Some_0()
    }

    #[verifier(when_used_as_spec(spec_unwrap))]
    pub fn unwrap(self) -> (a: A)
        requires
            self.is_Some(),
        ensures
            a == self.get_Some_0(),
    {
        match self {
            Option::Some(a) => a,
            Option::None => unreached(),
        }
    }

    pub proof fn tracked_unwrap(tracked self) -> (tracked a: A)
        requires
            self.is_Some(),
        ensures
            a == self.get_Some_0(),
    {
        match self {
            Option::Some(a) => a,
            Option::None => proof_from_false(),
        }
    }
}

} // verus!
    /// A poor-person's `?` operator, until Verus switches to the "real" Rust `Option`.
#[macro_export]
    #[allow(unused_macros)]
    macro_rules! try_option {
        ($x:expr) => {{
            let x = $x;
            match x {
                $crate::option::Option::None => {
                    return $crate::option::Option::None;
                }
                $crate::option::Option::Some(x) => x,
            }
        }};
    }
}

pub mod pervasive {
    #![allow(internal_features)]

    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use builtin_macros::*;

    #[cfg(not(feature = "std"))]
    macro_rules! println {
        ($($arg:tt)*) => {};
    }
    verus! {

// TODO: remove this
pub proof fn assume(b: bool)
    ensures
        b,
{
    admit();
}

// TODO: remove this
#[verifier(custom_req_err("assertion failure"))]
pub proof fn assert(b: bool)
    requires
        b,
    ensures
        b,
{
}

pub proof fn affirm(b: bool)
    requires
        b,
{
}

// TODO: when default trait methods are supported, most of these should be given defaults
pub trait ForLoopGhostIterator {
    type ExecIter;

    type Item;

    type Decrease;

    // Connect the ExecIter to the GhostIter
    // Always enabled
    // Always true before and after each loop iteration
    spec fn exec_invariant(&self, exec_iter: &Self::ExecIter) -> bool;

    // Additional optional invariants about the GhostIter
    // May be disabled with #[verifier::no_auto_loop_invariant]
    // If enabled, always true before and after each loop iteration
    // (When the analysis can infer a spec initial value, the analysis places the value in init)
    spec fn ghost_invariant(&self, init: Option<&Self>) -> bool;

    // True upon loop exit
    spec fn ghost_ensures(&self) -> bool;

    // Value used by default for decreases clause when no explicit decreases clause is provided
    // (the user can override this with an explicit decreases clause).
    // (If there's no appropriate decrease, this can return None,
    // and the user will have to provide an explicit decreases clause.)
    spec fn ghost_decrease(&self) -> Option<Self::Decrease>;

    // If there will be Some next value, and we can make a useful guess as to what the next value
    // will be, return Some of it.
    // Otherwise, return None.
    // TODO: in the long term, we could have VIR insert an assertion (or warning)
    // that ghost_peek_next returns non-null if it is used in the invariants.
    // (this will take a little bit of engineering since the syntax macro blindly inserts
    // let bindings using ghost_peek_next, even if they aren't needed, and we only learn
    // what is actually needed later in VIR.)
    spec fn ghost_peek_next(&self) -> Option<Self::Item>;

    // At the end of the for loop, advance to the next position.
    // Future TODO: this may be better as a proof function
    spec fn ghost_advance(&self, exec_iter: &Self::ExecIter) -> Self where Self: Sized;
}

pub trait ForLoopGhostIteratorNew {
    type GhostIter;

    // Create a new ghost iterator from an exec iterator
    // Future TODO: this may be better as a proof function
    spec fn ghost_iter(&self) -> Self::GhostIter;
}

#[cfg(verus_keep_ghost)]
pub trait FnWithRequiresEnsures<Args, Output>: Sized {
    spec fn requires(self, args: Args) -> bool;

    spec fn ensures(self, args: Args, output: Output) -> bool;
}

#[cfg(verus_keep_ghost)]
impl<Args: core::marker::Tuple, Output, F: FnOnce<Args, Output = Output>> FnWithRequiresEnsures<
    Args,
    Output,
> for F {
    #[verifier::inline]
    open spec fn requires(self, args: Args) -> bool {
        call_requires(self, args)
    }

    #[verifier::inline]
    open spec fn ensures(self, args: Args, output: Output) -> bool {
        call_ensures(self, args, output)
    }
}

// Non-statically-determined function calls are translated *internally* (at the VIR level)
// to this function call. This should not actually be called directly by the user.
// That is, Verus treats `f(x, y)` as `exec_nonstatic_call(f, (x, y))`.
// (Note that this function wouldn't even satisfy the borrow-checker if you tried to
// use it with a `&F` or `&mut F`, but this doesn't matter since it's only used at VIR.)
#[cfg(verus_keep_ghost)]
#[verifier(custom_req_err("Call to non-static function fails to satisfy `callee.requires(args)`"))]
#[doc(hidden)]
#[verifier(external_body)]
#[rustc_diagnostic_item = "verus::vstd::vstd::exec_nonstatic_call"]
fn exec_nonstatic_call<Args: core::marker::Tuple, Output, F>(f: F, args: Args) -> (output:
    Output) where F: FnOnce<Args, Output = Output>
    requires
        call_requires(f, args),
    ensures
        call_ensures(f, args, output),
{
    unimplemented!();
}

/// A tool to check one's reasoning while writing complex spec functions.
/// Not intended to be used as a mechanism for instantiating quantifiers, `spec_affirm` should
/// be removed from spec functions once they are complete.
///
/// ## Example
///
/// ```rust
/// #[spec(checked)] fn some_predicate(a: nat) -> bool {
///     recommends(a < 100);
///     if (a >= 50) {
///         let _ = spec_affirm(50 <= a && a < 100);
///         a >= 75
///     } else {
///         let _ = spec_affirm(a < 50);
///         // let _ = spec_affirm(a < 40); would raise a recommends note here
///         a < 25
///     }
/// }
/// ```
pub closed spec fn spec_affirm(b: bool) -> bool
    recommends
        b,
{
    b
}

/// In spec, all types are inhabited
#[verifier(external_body)]  /* vattr */
#[allow(dead_code)]
pub closed spec fn arbitrary<A>() -> A {
    unimplemented!()
}

#[verifier(external_body)]  /* vattr */
#[allow(dead_code)]
pub proof fn proof_from_false<A>() -> (tracked a: A) {
    requires(false);
    unimplemented!()
}

#[verifier(external_body)]  /* vattr */
#[allow(dead_code)]
pub fn unreached<A>() -> A
    requires
        false,
{
    panic!("unreached_external")
}

#[verifier(external_body)]  /* vattr */
pub fn print_u64(i: u64) {
    println!("{}", i);
}

#[verifier(external_body)]
#[deprecated(note="please use `std::mem::swap` instead")]
pub fn swap<A>(x: &mut A, y: &mut A)
    ensures
        *x == *old(y),
        *y == *old(x),
{
    core::mem::swap(x, y)
}

#[verifier::external_body]
pub fn runtime_assert(b: bool)
    requires
        b,
{
    runtime_assert_internal(b);
}

} // verus!
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    fn runtime_assert_internal(b: bool) {
        assert!(b);
    }

    /// Allows you to prove a boolean predicate by assuming its negation and proving
    /// a contradiction.
    ///
    /// `assert_by_contradiction!(b, { /* proof */ });`
    /// Equivalent to writing `if !b { /* proof */; assert(false); }`
    /// but is more concise and documents intent.
    ///
    /// ```rust
    /// assert_by_contradiction!(b, {
    ///     // assume !b here
    ///     // prove `false`
    /// });
    /// ```

    #[macro_export]
    macro_rules! assert_by_contradiction {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!($crate::assert_by_contradiction_internal!($($a)*))
    }
}

    #[doc(hidden)]
    #[macro_export]
    macro_rules! assert_by_contradiction_internal {
        ($predicate:expr, $bblock:block) => {
            ::builtin::assert_by($predicate, {
                if !$predicate {
                    $bblock::builtin::assert_(false);
                }
            });
        };
    }

    /// Macro to help set up boilerplate for specifying invariants when using
    /// invariant-based datatypes.
    ///
    /// This currently supports the `AtomicInvariant` and `LocalInvariant`
    /// types, as well as all the `atomic_ghost` types (e.g., `AtomicU64`, `AtomicBool`, and so on).
    /// It is important to first understand how these types work.
    /// In particular, `LocalInvariant` (for example) takes three type parameters,
    /// `K`, `V`, and `Pred: InvariantPredicate`.
    /// The `InvariantPredicate` trait lets the user specify an invariant at the static type
    /// level, while `K` allows the user to configure the invariant upon construction.
    /// `AtomicInvariant` uses the same system, and the `atomic_ghost` types are similar
    /// but use a different trait (`AtomicInvariantPredicate`).
    ///
    /// However, setting all this up in a typical application tends to involve a bit
    /// of boilerplate. That's where this macro comes in.
    ///
    /// # Usage
    ///
    /// The `struct_with_invariants!` macro is used at the item level, and it should contains
    /// a single struct declaration followed by a single declaration of a `spec` function
    /// returning `bool`. However, this spec function should not contain a boolean predicate
    /// as usual, but instead a series of _invariant declarations_.
    /// Each invariant declaration applies to a single field of the struct.
    ///
    /// ```rust
    /// struct_with_invariants!{
    ///     (pub)? struct $struct_name (<...>)? (where ...)? {
    ///         ( (pub)? $field_name: $type, )*
    ///     }
    ///
    ///     (pub)? (open|closed)? spec fn(&self (, ...)?) $fn_name {
    ///         ( InvariantDecl | BoolPredicateDecl )*
    ///     }
    /// }
    /// ```
    ///
    /// A field of the struct, if it uses a supported type, may leave the type _incomplete_ by
    /// omitting some of its type parameters.
    /// The following are valid incomplete types:
    ///
    ///  * `LocalInvariant<_, V, _>`
    ///  * `AtomicInvariant<_, V, _>`
    ///  * `AtomicBool<_, G, _>`
    ///  * `AtomicU64<_, G, _>`
    ///    * ... and so on for the other `atomic_ghost` types.
    ///
    /// There must be exactly one invariant declaration for each incomplete type used in the
    /// struct declaration. The macro uses invariant declarations to fill in the type parameters.
    ///
    /// The user can also provide boolean predicate declarations, which are copied verbatim
    /// into the `$fn_name` definition. This is a convenience, since it is common to want
    /// to add extra conditions, and it is fairly straightforward.
    /// The complex part of the macro expansion in the invariant declarations.
    ///
    /// ```rust
    /// BoolPredicateDecl  :=  predicate { $bool_expr }
    ///
    /// InvariantDecl  :=
    ///     invariant on $field_name
    ///         ( with ($dependencies) )?
    ///         ( forall | ($ident: $type, )* | )?
    ///         ( where ($where_expr) )?
    ///         ( specifically ($specifically_expr) )?
    ///         is ($params) {
    ///             $bool_expr
    ///         }
    /// ```
    ///
    /// In the `InvariantDecl`, the user always needs to provide the following data:
    ///
    ///  * The `$field_name` is the field that this invariant applies to
    ///     (which must have an incomplete type as described above)
    ///  * The `$params` are the values constrained by the invariant.
    ///      * For a `LocalInvariant<V>` or `AtomicInvariant<V>`, this should be a single
    ///        parameter of type `V`.
    ///      * For an `atomic_ghost` type, this should consist of two parameters,
    ///        first the primitive type stored by the atomic, and secondly one of the ghost type, `G`.
    ///        (For example, the type `AtomicBool<_, G, _>` should have two parameters
    ///        here, `b: bool, g: G`.)
    ///  * Finally, the `$bool_expr` is the invariant predicate, which may reference any of
    ///     the fields declared in `$dependencies`, or any of the params.
    ///
    /// The other input clauses handle additional complexities that often comes up.
    /// For example, it is often necessary for the invariant to refer to the values of other fields
    /// in the struct.
    ///
    ///  * The `with` input gives the list of field names (other fields
    ///     from the struct definition) that may be referenced from
    ///     the body of this invariant.
    ///     The graph of dependencies across all fields must be acyclic.
    ///
    /// Finally, when the field is a _container_ type, e.g., `vec: Vec<AtomicU64<_, G, _>>` or
    /// `opt: Option<AtomicU64<_, G, _>>`, there are some additional complexities.
    /// We might need the invariant to be conditional (e.g., for an optional, the invariant would only
    /// exist if `opt.is_Some()`).
    /// We might need to quantify over a variable (e.g., in a vector, we want to specify an invariant
    /// for each element, element `i` where `0 <= i < vec.len()`).
    /// Finally, we need to indicate the value actually getting the invariant (e.g., `self.vec[i]`).
    ///
    /// * The `forall` lets you specify additional bound variables. Everything after the `forall`---the
    ///   `where`, the `specifically`, and finally the `$bool_expr$`---can all reference these bound variables.
    /// * The `where` lets you specify an additional hypothesis that the invariant is dependent on.
    /// * The `specifically` lets you indicate the value getting the invariant.
    ///
    /// This all roughly means, "forall instantiations of the quantified variables, if the condition `$where_expr` holds,
    /// then the value given by `$specifically_expr` has the invariant given by `$bool_expr`.
    /// See the detailed information on the macro-expansion below for more details.
    ///
    /// Given all the information from the `InvariantDecl`, the macro fills in the `_` placeholders as follows:
    ///
    ///  * The macro fills in the `K` type as the types of the fields marked as dependencies and
    ///    the quantified variables in the forall (packing all these types into a tuple if necessary).
    ///  * The macro fills in the `Pred` type by creating a new type and implementing the appropriate
    ///    trait with the user-provided predicate.
    ///
    /// # Example (TODO)
    ///
    /// # Example using a container type (TODO)
    ///
    /// # Macro Expansion (TODO)
    pub use builtin_macros::struct_with_invariants;

    verus! {

use crate::view::View;

#[cfg(feature = "alloc")]
#[verifier::external]
pub trait VecAdditionalExecFns<T> {
    fn set(&mut self, i: usize, value: T);

    fn set_and_swap(&mut self, i: usize, value: &mut T);
}

#[cfg(feature = "alloc")]
impl<T> VecAdditionalExecFns<T> for alloc::vec::Vec<T> {
    /// Replacement for `self[i] = value;` (which Verus does not support for technical reasons)
    #[verifier::external_body]
    fn set(&mut self, i: usize, value: T)
        requires
            i < old(self).len(),
        ensures
            self@ == old(self)@.update(i as int, value),
    {
        self[i] = value;
    }

    /// Replacement for `swap(&mut self[i], &mut value)` (which Verus does not support for technical reasons)
    #[verifier::external_body]
    fn set_and_swap(&mut self, i: usize, value: &mut T)
        requires
            i < old(self).len(),
        ensures
            self@ == old(self)@.update(i as int, *old(value)),
            *value == old(self)@.index(i as int),
    {
        core::mem::swap(&mut self[i], value);
    }
}

} // verus!
}

#[cfg(feature = "alloc")]
pub mod ptr {
    #![allow(unused_imports)]

    use alloc::alloc::Layout;
    use core::{marker, mem, mem::MaybeUninit};

    use crate::layout::*;
    use crate::modes::*;
    use crate::pervasive::*;
    use crate::prelude::*;
    use crate::*;
    use builtin::*;
    use builtin_macros::*;

    #[cfg(verus_keep_ghost)]
    use crate::set_lib::set_int_range;

    verus! {

/// `PPtr<V>` (which stands for "permissioned pointer")
/// is a wrapper around a raw pointer to `V` on the heap.
///
/// Technically, it is a wrapper around `*mut mem::MaybeUninit<V>`, that is, the object
/// it points to may be uninitialized.
///
/// In order to access (read or write) the value behind the pointer, the user needs
/// a special _ghost permission token_, [`PointsTo<V>`](PointsTo). This object is `tracked`,
/// which means that it is "only a proof construct" that does not appear in code,
/// but its uses _are_ checked by the borrow-checker. This ensures memory safety,
/// data-race-freedom, prohibits use-after-free, etc.
///
/// ### PointsTo objects.
///
/// The [`PointsTo`] object represents both the ability to access the data behind the
/// pointer _and_ the ability to free it (return it to the memory allocator).
///
/// In particular:
///  * When the user owns a `PointsTo<V>` object associated to a given pointer,
///    they can either read or write its contents, or deallocate ("free") it.
///  * When the user has a shared borrow, `&PointsTo<V>`, they can read
///    the contents (i.e., obtained a shared borrow `&V`).
///
/// The `perm: PointsTo<V>` object tracks two pieces of data:
///  * `perm.pptr` is the pointer that the permission is associated to,
///     given by [`ptr.id()`](PPtr::id).
///  * `perm.value` tracks the data that is behind the pointer. Thereby:
///      * When the user uses the permission to _read_ a value, they always
///        read the value as given by the `perm.value`.
///      * When the user uses the permission to _write_ a value, the `perm.value`
///        data is updated.
///
/// For those familiar with separation logic, the `PointsTo` object plays a role
/// similar to that of the "points-to" operator, _ptr_ ↦ _value_.
///
/// ### Differences from `PCell`.
///
/// `PPtr` is similar to [`cell::PCell`], but has a few key differences:
///  * In `PCell<T>`, the type `T` is placed internally to the `PCell`, whereas with `PPtr`,
///    the type `T` is placed at some location on the heap.
///  * Since `PPtr` is just a pointer (represented by an integer), it can be `Copy`.
///  * The `ptr::PointsTo` token represents not just the permission to read/write
///    the contents, but also to deallocate.
///
/// ### Example (TODO)
// Notes about pointer provenance:
//
// "Pointer provenance" is this complicated subject which is a necessary
// evil if you want to understand the abstract machine semantics of a language
// with pointers and what is or is not UB with int-to-pointer casts.
//
// See this series of blog posts for some introduction:
// https://www.ralfj.de/blog/2022/04/11/provenance-exposed.html
//
// Here in Verus, where code is forced to be verified, we want to tell
// a much simpler story, which is the following:
//
//   ***** VERUS POINTER MODEL *****
//    "Provenance" comes from the `tracked ghost` PointsTo object.
//   *******************************
//
// Pretty simple, right?
//
// Of course, this trusted pointer library still needs to actually run and
// be sound in the Rust backend.
// Rust's abstract pointer model is unchanged, and it doesn't know anything
// about Verus's special ghost `PointsTo` object, which gets erased, anyway.
//
// Maybe someday the ghost PointsTo model will become a real
// memory model. That isn't true today.
// So we still need to know something about actual, real memory models that
// are used right now in order to implement this API soundly.
//
// Our goal is to allow the *user of Verus* to think in terms of the
// VERUS POINTER MODEL where provenance is tracked via the `PointsTo` object.
// The rest of this is just details for the trusted implementation of PPtr
// that will be sound in the Rust backend.
//
// In the "PNVI-ae-udi" model:
//  * A ptr->int cast "exposes" a pointer (adding it some global list in the
//    abstract machine)
//  * An int->ptr cast acquires the provenance of that pointer only if it
//    was previously exposed.
//
// The "tower of weakenings", however,
// (see https://gankra.github.io/blah/tower-of-weakenings/)
// proposes a stricter model called "Strict Provenance".
// This basically forbids exposing and requires provenance to always be tracked.
//
// If possible, it would be nice to stick to this stricter model, but it isn't necessary.
//
// Unfortunately, it's not possible. The Strict Provenance requires "provenance" to be
// tracked through non-ghost pointers. We can't use our ghost objects to track provenance
// in general while staying consistent with Strict Provenance.
//
// We have two options:
//
//  1. Just forbid int->ptr conversions
//  2. Always "expose" every PPtr when it's created, in order to definitely be safe
//     under PNVI-ae-udi.
//
// However, int->ptr conversions ought to be allowed in the VERUS POINTER MODEL,
// so I'm going with (2) here.
//
// TODO reconsider: Is this plan actually good? Exposing all pointers has the potential
// to ruin optimizations. If the plan is bad, and we want to avoid the cost of
// "expose-everywhere", we may need to actually track provenance as part
// of the specification of PPtr.
//
// Perhaps what we could do is specify a low-level pointer library with
// strict provenance rules + exposed pointers,
// and then verify user libraries on top of that?
// TODO implement: borrow_mut; figure out Drop, see if we can avoid leaking?
// TODO just replace this with `*mut V`
#[repr(C)]
#[verifier(external_body)]
#[verifier::accept_recursive_types(V)]
pub struct PPtr<V> {
    pub uptr: *mut V,
}

// PPtr is always safe to Send/Sync. It's the PointsTo object where Send/Sync matters.
// It doesn't matter if you send the pointer to another thread if you can't access it.
#[verifier(external)]
unsafe impl<T> Sync for PPtr<T> {

}

#[verifier(external)]
unsafe impl<T> Send for PPtr<T> {

}

// TODO some of functionality could have V: ?Sized
/// A `tracked` ghost object that gives the user permission to dereference a pointer
/// for reading or writing, or to free the memory at that pointer.
///
/// The meaning of a `PointsTo` object is given by the data in its
/// `View` object, [`PointsToData`].
///
/// See the [`PPtr`] documentation for more details.
#[verifier(external_body)]
#[verifier::reject_recursive_types_in_ground_variants(V)]
pub tracked struct PointsTo<V> {
    phantom: marker::PhantomData<V>,
    no_copy: NoCopy,
}

/// Represents the meaning of a [`PointsTo`] object.
pub ghost struct PointsToData<V> {
    /// Indicates that this token is for a pointer `ptr: PPtr<V>`
    /// such that [`ptr.id()`](PPtr::id) equal to this value.
    pub pptr: int,
    /// Indicates that this token gives the ability to read a value `V` from memory.
    /// When `None`, it indicates that the memory is uninitialized.
    pub value: Option<V>,
}

// TODO add similiar height axioms for other ghost objects
#[verifier(broadcast_forall)]
#[verifier(external_body)]
pub proof fn points_to_height_axiom<V>(points_to: PointsTo<V>)
    ensures
        #[trigger] is_smaller_than(points_to@, points_to),
{
    unimplemented!()
}

/// Points to uninitialized memory.
#[verifier(external_body)]
pub tracked struct PointsToRaw {
    no_copy: NoCopy,
}

#[verifier(external_body)]
pub tracked struct Dealloc<
    #[verifier(strictly_positive)]
    V,
> {
    phantom: marker::PhantomData<V>,
    no_copy: NoCopy,
}

pub ghost struct DeallocData {
    pub pptr: int,
}

#[verifier(external_body)]
pub tracked struct DeallocRaw {
    no_copy: NoCopy,
}

pub ghost struct DeallocRawData {
    pub pptr: int,
    pub size: nat,
    pub align: nat,
}

impl<V> PointsTo<V> {
    pub spec fn view(self) -> PointsToData<V>;

    /// Any dereferenceable pointer must be non-null.
    /// (Note that null pointers _do_ exist and are representable by `PPtr`;
    /// however, it is not possible to obtain a `PointsTo` token for
    /// any such a pointer.)
    #[verifier(external_body)]
    pub proof fn is_nonnull(tracked &self)
        ensures
            self@.pptr != 0,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn leak_contents(tracked &mut self)
        ensures
            self@.pptr == old(self)@.pptr && self@.value.is_None(),
    {
        unimplemented!();
    }
}

impl<V> PointsTo<V> {
    #[verifier(external_body)]
    pub proof fn into_raw(tracked self) -> (tracked points_to_raw: PointsToRaw)
        requires
            self@.value.is_None(),
        ensures
            points_to_raw.is_range(self@.pptr, size_of::<V>() as int),
            is_sized::<V>(),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn borrow_raw(tracked &self) -> (tracked points_to_raw: &PointsToRaw)
        requires
            self@.value.is_None(),
        ensures
            points_to_raw.is_range(self@.pptr, size_of::<V>() as int),
            is_sized::<V>(),
    {
        unimplemented!();
    }
}

impl PointsToRaw {
    pub spec fn view(self) -> Map<int, u8>;

    pub open spec fn contains_range(self, start: int, len: int) -> bool {
        set_int_range(start, start + len).subset_of(self@.dom())
    }

    pub open spec fn is_range(self, start: int, len: int) -> bool {
        set_int_range(start, start + len) =~= self@.dom()
    }

    #[verifier(inline)]
    pub open spec fn spec_index(self, i: int) -> u8 {
        self@[i]
    }

    #[verifier(external_body)]
    pub proof fn is_nonnull(tracked &self)
        ensures
            !self@.dom().contains(0),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn is_in_bounds(tracked &self)
        ensures
            forall|i: int| self@.dom().contains(i) ==> 0 < i <= usize::MAX,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn empty() -> (tracked points_to_raw: Self)
        ensures
            points_to_raw@ == Map::<int, u8>::empty(),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn into_typed<V>(tracked self, start: int) -> (tracked points_to: PointsTo<V>)
        requires
            is_sized::<V>(),
            start % align_of::<V>() as int == 0,
            self.is_range(start, size_of::<V>() as int),
        ensures
            points_to@.pptr === start,
            points_to@.value === None,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn borrow_typed<V>(tracked &self, start: int) -> (tracked points_to: &PointsTo<V>)
        requires
            is_sized::<V>(),
            start % align_of::<V>() as int == 0,
            self.contains_range(start, size_of::<V>() as int),
        ensures
            points_to@.pptr === start,
            points_to@.value === None,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn join(tracked self, tracked other: Self) -> (tracked joined: Self)
        ensures
            self@.dom().disjoint(other@.dom()),
            joined@ == self@.union_prefer_right(other@),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn borrow_join<'a>(tracked &'a self, tracked other: &'a Self) -> (tracked joined:
        &'a Self)
        ensures
            (forall|i|
                #![trigger self@.dom().contains(i), other@.dom().contains(i)]
                self@.dom().contains(i) && other@.dom().contains(i) ==> self@[i] == other@[i]),
            joined@ == self@.union_prefer_right(other@),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn split(tracked self, range: Set<int>) -> (tracked res: (Self, Self))
        requires
            range.subset_of(self@.dom()),
        ensures
            res.0@ == self@.restrict(range),
            res.1@ == self@.remove_keys(range),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn borrow_subset(tracked &self, range: Set<int>) -> (tracked res: &Self)
        requires
            range.subset_of(self@.dom()),
        ensures
            res@ == self@.restrict(range),
    {
        unimplemented!();
    }
}

impl<V> Dealloc<V> {
    pub spec fn view(self) -> DeallocData;
}

impl<V> Dealloc<V> {
    #[verifier(external_body)]
    pub proof fn is_nonnull(tracked &self)
        ensures
            self@.pptr != 0,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn into_raw(tracked self) -> (tracked dealloc_raw: DeallocRaw)
        ensures
            dealloc_raw@.pptr === self@.pptr,
            dealloc_raw@.size === size_of::<V>(),
            dealloc_raw@.align === align_of::<V>(),
            is_sized::<V>(),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn borrow_raw(tracked &self) -> (tracked dealloc_raw: &DeallocRaw)
        ensures
            dealloc_raw@.pptr === self@.pptr,
            dealloc_raw@.size === size_of::<V>(),
            dealloc_raw@.align === align_of::<V>(),
            is_sized::<V>(),
    {
        unimplemented!();
    }
}

impl DeallocRaw {
    pub spec fn view(self) -> DeallocRawData;

    #[verifier(external_body)]
    pub proof fn is_nonnull(tracked &self)
        ensures
            self@.pptr != 0,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn into_typed<V>(tracked self) -> (tracked dealloc: Dealloc<V>)
        requires
            is_sized::<V>(),
            self@.size === size_of::<V>(),
            self@.align === align_of::<V>(),
        ensures
            dealloc@.pptr === self@.pptr,
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn borrow_typed<V>(tracked &self) -> (tracked dealloc: &Dealloc<V>)
        requires
            is_sized::<V>(),
            self@.size === size_of::<V>(),
            self@.align === align_of::<V>(),
        ensures
            dealloc@.pptr === self@.pptr,
    {
        unimplemented!();
    }
}

impl<A> Clone for PPtr<A> {
    #[verifier(external_body)]
    fn clone(&self) -> (s: Self)
        ensures
            s == *self,
    {
        PPtr { uptr: self.uptr }
    }
}

impl<A> Copy for PPtr<A> {

}

impl<V> PPtr<V> {
    /// Cast a pointer to an integer.
    #[inline(always)]
    #[verifier(external_body)]
    pub fn to_usize(&self) -> (u: usize)
        ensures
            u as int == self.id(),
    {
        self.uptr as usize
    }

    /// integer address of the pointer
    pub spec fn id(&self) -> int;

    /// Cast an integer to a pointer.
    ///
    /// Note that this does _not_ require or ensure that the pointer is valid.
    /// Of course, if the user creates an invalid pointer, they would still not be able to
    /// create a valid [`PointsTo`] token for it, and thus they would never
    /// be able to access the data behind the pointer.
    ///
    /// This is analogous to normal Rust, where casting to a pointer is always possible,
    /// but dereferencing a pointer is an `unsafe` operation.
    /// In Verus, casting to a pointer is likewise always possible,
    /// while dereferencing it is only allowed when the right preconditions are met.
    #[inline(always)]
    #[verifier(external_body)]
    pub fn from_usize(u: usize) -> (p: Self)
        ensures
            p.id() == u as int,
    {
        let uptr = u as *mut V;
        PPtr { uptr }
    }

    /// Allocates heap memory for type `V`, leaving it uninitialized.
    #[inline(always)]
    #[verifier(external_body)]
    pub fn empty() -> (pt: (PPtr<V>, Tracked<PointsTo<V>>, Tracked<Dealloc<V>>))
        ensures
            pt.1@@ === (PointsToData { pptr: pt.0.id(), value: None }),
            pt.2@@ === (DeallocData { pptr: pt.0.id() }),
        opens_invariants none
    {
        let layout = Layout::new::<V>();
        let size = layout.size();
        let align = layout.align();
        let (p, _, _) = PPtr::<V>::alloc(size, align);
        (p, Tracked::assume_new(), Tracked::assume_new())
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn alloc(size: usize, align: usize) -> (pt: (
        PPtr<V>,
        Tracked<PointsToRaw>,
        Tracked<DeallocRaw>,
    ))
        requires
            valid_layout(size, align),
        ensures
            pt.1@.is_range(pt.0.id(), size as int),
            pt.2@@ === (DeallocRawData { pptr: pt.0.id(), size: size as nat, align: align as nat }),
            pt.0.id() % align as int == 0,
        opens_invariants none
    {
        // Add padding (this is to prevent the user from being able to "combine" allocations)
        // Constructing the layout object might fail if the allocation becomes too big.
        // The 'add' can't overflow, since we already know (size, align) is a valid layout.
        let layout = Layout::from_size_align(size + align, align).unwrap();
        let p = PPtr { uptr: unsafe { ::alloc::alloc::alloc(layout) as *mut V } };
        // See explanation about exposing pointers, above
        let _exposed_addr = p.uptr as usize;
        (p, Tracked::assume_new(), Tracked::assume_new())
    }

    /// Moves `v` into the location pointed to by the pointer `self`.
    /// Requires the memory to be uninitialized, and leaves it initialized.
    ///
    /// In the ghost perspective, this updates `perm.value`
    /// from `None` to `Some(v)`.
    #[inline(always)]
    #[verifier(external_body)]
    pub fn put(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, v: V)
        requires
            self.id() === old(perm)@.pptr,
            old(perm)@.value === None,
        ensures
            perm@.pptr === old(perm)@.pptr,
            perm@.value === Some(v),
        opens_invariants none
    {
        // See explanation about exposing pointers, above
        let ptr = self.uptr as usize as *mut V;
        unsafe {
            // We use `write` here because it does not attempt to "drop" the memory at `*ptr`.
            core::ptr::write(ptr, v);
        }
    }

    /// Moves `v` out of the location pointed to by the pointer `self`
    /// and returns it.
    /// Requires the memory to be initialized, and leaves it uninitialized.
    ///
    /// In the ghost perspective, this updates `perm.value`
    /// from `Some(v)` to `None`,
    /// while returning the `v` as an `exec` value.
    #[inline(always)]
    #[verifier(external_body)]
    pub fn take(&self, Tracked(perm): Tracked<&mut PointsTo<V>>) -> (v: V)
        requires
            self.id() === old(perm)@.pptr,
            old(perm)@.value.is_Some(),
        ensures
            perm@.pptr === old(perm)@.pptr,
            perm@.value === None,
            v === old(perm)@.value.get_Some_0(),
        opens_invariants none
    {
        // See explanation about exposing pointers, above
        let ptr = self.uptr as usize as *mut V;
        unsafe { core::ptr::read(ptr) }
    }

    /// Swaps the `in_v: V` passed in as an argument with the value in memory.
    /// Requires the memory to be initialized, and leaves it initialized with the new value.
    #[inline(always)]
    #[verifier(external_body)]
    pub fn replace(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V) -> (out_v: V)
        requires
            self.id() === old(perm)@.pptr,
            old(perm)@.value.is_Some(),
        ensures
            perm@.pptr === old(perm)@.pptr,
            perm@.value === Some(in_v),
            out_v === old(perm)@.value.get_Some_0(),
        opens_invariants none
    {
        // See explanation about exposing pointers, above
        let ptr = self.uptr as usize as *mut V;
        unsafe {
            let mut m = in_v;
            mem::swap(&mut m, &mut *ptr);
            m
        }
    }

    /// Given a shared borrow of the `PointsTo<V>`, obtain a shared borrow of `V`.
    // Note that `self` is just a pointer, so it doesn't need to outlive
    // the returned borrow.
    #[inline(always)]
    #[verifier(external_body)]
    pub fn borrow<'a>(&self, Tracked(perm): Tracked<&'a PointsTo<V>>) -> (v: &'a V)
        requires
            self.id() === perm@.pptr,
            perm@.value.is_Some(),
        ensures
            *v === perm@.value.get_Some_0(),
        opens_invariants none
    {
        // See explanation about exposing pointers, above
        let ptr = self.uptr as usize as *mut V;
        unsafe { &*ptr }
    }

    /// Free the memory pointed to be `perm`.
    /// Requires the memory to be uninitialized.
    ///
    /// This consumes `perm`, since it will no longer be safe to access
    /// that memory location.
    #[inline(always)]
    #[verifier(external_body)]
    pub fn dispose(
        &self,
        Tracked(perm): Tracked<PointsTo<V>>,
        Tracked(dealloc): Tracked<Dealloc<V>>,
    )
        requires
            self.id() === perm@.pptr,
            perm@.value === None,
            perm@.pptr == dealloc@.pptr,
        opens_invariants none
    {
        unsafe {
            let layout = alloc::alloc::Layout::for_value(&*self.uptr);
            let size = layout.size();
            let align = layout.align();
            // Add the padding to match what we did in 'alloc'
            let layout = Layout::from_size_align_unchecked(size + align, align);
            ::alloc::alloc::dealloc(self.uptr as *mut u8, layout);
        }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn dealloc(
        &self,
        size: usize,
        align: usize,
        Tracked(perm): Tracked<PointsToRaw>,
        Tracked(dealloc): Tracked<DeallocRaw>,
    )
        requires
            perm.is_range(self.id(), size as int),
            dealloc@.pptr === self.id(),
            dealloc@.size === size as nat,
            dealloc@.align === align as nat,
        opens_invariants none
    {
        unsafe {
            // Since we have the Dealloc object, we know this is a valid layout
            // and that it's safe to call 'deallocate'
            // Remember to add the padding, like in `alloc`
            let layout = Layout::from_size_align_unchecked(size + align, align);
            ::alloc::alloc::dealloc(self.uptr as *mut u8, layout);
        }
    }

    //////////////////////////////////
    // Verified library functions below here
    /// Free the memory pointed to be `perm` and return the
    /// value that was previously there.
    /// Requires the memory to be initialized.
    /// This consumes the [`PointsTo`] token, since the user is giving up
    /// access to the memory by freeing it.
    #[inline(always)]
    pub fn into_inner(
        self,
        Tracked(perm): Tracked<PointsTo<V>>,
        Tracked(dealloc): Tracked<Dealloc<V>>,
    ) -> (v: V)
        requires
            self.id() === perm@.pptr,
            perm@.pptr == dealloc@.pptr,
            perm@.value.is_Some(),
        ensures
            v === perm@.value.get_Some_0(),
        opens_invariants none
    {
        let tracked mut perm = perm;
        let v = self.take(Tracked(&mut perm));
        self.dispose(Tracked(perm), Tracked(dealloc));
        v
    }

    /// Allocates heap memory for type `V`, leaving it initialized
    /// with the given value `v`.
    #[inline(always)]
    pub fn new(v: V) -> (pt: (PPtr<V>, Tracked<PointsTo<V>>, Tracked<Dealloc<V>>))
        ensures
            (pt.1@@ === PointsToData { pptr: pt.0.id(), value: Some(v) }),
            (pt.2@@ === DeallocData { pptr: pt.0.id() }),
    {
        let (p, Tracked(mut t), Tracked(d)) = Self::empty();
        p.put(Tracked(&mut t), v);
        (p, Tracked(t), Tracked(d))
    }
}

impl<V: Copy> PPtr<V> {
    #[inline(always)]
    pub fn write(&self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V)
        requires
            self.id() === old(perm)@.pptr,
        ensures
            perm@.pptr === old(perm)@.pptr,
            perm@.value === Some(in_v),
        opens_invariants none
    {
        proof {
            perm.leak_contents();
        }
        self.put(Tracked(&mut *perm), in_v);
    }

    #[inline(always)]
    pub fn read(&self, Tracked(perm): Tracked<&PointsTo<V>>) -> (out_v: V)
        requires
            self.id() === perm@.pptr,
            perm@.value.is_Some(),
        ensures
            perm@.value === Some(out_v),
        opens_invariants none
    {
        *self.borrow(Tracked(&*perm))
    }
}

// Manipulating the contents in a PointsToRaw
impl PPtr<u8> {
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))]
    #[verifier::external_body]
    fn copy_nonoverlapping(
        &self,
        dst: PPtr<u8>,
        count: usize,
        perm_src: &PointsToRaw,
        perm_dst: &mut PointsToRaw,
    )
        requires
            perm_src.contains_range(self.id(), count as int),
            old(perm_dst).contains_range(dst.id(), count as int),
        ensures
            perm_dst@ == old(perm_dst)@.union_prefer_right(
                perm_src@.restrict(set_int_range(self.id(), self.id() + count)),
            ),
    {
        unsafe { core::ptr::copy_nonoverlapping(self.uptr, dst.uptr, count) }
    }

    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))]
    #[verifier::external_body]
    fn write_bytes(&self, val: u8, count: usize, perm: &mut PointsToRaw)
        requires
            old(perm).contains_range(self.id(), count as int),
        ensures
            perm@ == old(perm)@.union_prefer_right(
                Map::new(
                    |addr| set_int_range(self.id(), self.id() + count).contains(addr),
                    |addr| val,
                ),
            ),
    {
        unsafe {
            core::ptr::write_bytes::<u8>(self.uptr, val, count);
        }
    }
}

} // verus!
}

pub mod result {
    #![deprecated(note = "Use std::result instead")]

    #[allow(unused_imports)]
    use crate::pervasive::*;
    #[allow(unused_imports)]
    use builtin::*;
    use builtin_macros::*;

    verus! {

#[is_variant]
pub enum Result<T, E> {
    Ok(T),
    Err(E),
}

pub use crate::result::Result::Ok;
pub use crate::result::Result::Err;

impl<T, E> Result<T, E> {
    #[inline(always)]
    pub const fn is_ok(&self) -> (res: bool)
        ensures
            res <==> self.is_Ok(),
    {
        match self {
            Result::Ok(_) => true,
            Result::Err(_) => false,
        }
    }

    #[inline(always)]
    pub const fn is_err(&self) -> (res: bool)
        ensures
            res <==> self.is_Err(),
    {
        match self {
            Result::Ok(_) => false,
            Result::Err(_) => true,
        }
    }

    pub fn as_ref(&self) -> (r: Result<&T, &E>)
        ensures
            r.is_Ok() <==> self.is_Ok(),
            r.is_Ok() ==> self.get_Ok_0() == r.get_Ok_0(),
            r.is_Err() <==> self.is_Err(),
            r.is_Err() ==> self.get_Err_0() == r.get_Err_0(),
    {
        match self {
            Result::Ok(t) => Result::Ok(t),
            Result::Err(e) => Result::Err(e),
        }
    }

    // A more-readable synonym for get_Ok_0().
    #[verifier(inline)]
    pub open spec fn spec_unwrap(self) -> T
        recommends
            self.is_Ok(),
    {
        self.get_Ok_0()
    }

    #[verifier(when_used_as_spec(spec_unwrap))]
    pub fn unwrap(self) -> (t: T)
        requires
            self.is_Ok(),
        ensures
            t == self.get_Ok_0(),
    {
        match self {
            Result::Ok(t) => t,
            Result::Err(_) => unreached(),
        }
    }

    // A more-readable synonym for get_Err_0().
    #[verifier(inline)]
    pub open spec fn spec_unwrap_err(self) -> E
        recommends
            self.is_Err(),
    {
        self.get_Err_0()
    }

    #[verifier(when_used_as_spec(spec_unwrap_err))]
    pub fn unwrap_err(self) -> (e: E)
        requires
            self.is_Err(),
        ensures
            e == self.get_Err_0(),
    {
        match self {
            Result::Ok(_) => unreached(),
            Result::Err(e) => e,
        }
    }
}

} // verus!
}

pub mod seq {
    use core::marker;

    #[allow(unused_imports)]
    use crate::pervasive::*;
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use builtin_macros::*;

    verus! {

/// `Seq<A>` is a sequence type for specifications.
/// To use a "sequence" in compiled code, use an `exec` type like [`vec::Vec`](crate::vec::Vec)
/// that has `Seq<A>` as its specification type.
///
/// An object `seq: Seq<A>` has a length, given by [`seq.len()`](Seq::len),
/// and a value at each `i` for `0 <= i < seq.len()`, given by [`seq[i]`](Seq::index).
///
/// Sequences can be constructed in a few different ways:
///  * [`Seq::empty`] construct an empty sequence (`len() == 0`)
///  * [`Seq::new`] construct a sequence of a given length, initialized according
///     to a given function mapping indices `i` to values `A`.
///  * The [`seq!`] macro, to construct small sequences of a fixed size (analagous to the
///     [`std::vec!`] macro).
///  * By manipulating an existing sequence with [`Seq::push`], [`Seq::update`],
///    or [`Seq::add`].
///
/// To prove that two sequences are equal, it is usually easiest to use the
/// extensional equality operator `=~=`.
#[verifier::external_body]
#[verifier::ext_equal]
#[verifier::accept_recursive_types(A)]
pub struct Seq<A> {
    dummy: marker::PhantomData<A>,
}

impl<A> Seq<A> {
    /// An empty sequence (i.e., a sequence of length 0).
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::empty"]
    pub spec fn empty() -> Seq<A>;

    /// Construct a sequence `s` of length `len` where entry `s[i]` is given by `f(i)`.
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::new"]
    pub spec fn new(len: nat, f: impl Fn(int) -> A) -> Seq<A>;

    /// The length of a sequence.
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::len"]
    pub spec fn len(self) -> nat;

    /// Gets the value at the given index `i`.
    ///
    /// If `i` is not in the range `[0, self.len())`, then the resulting value
    /// is meaningless and arbitrary.
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::index"]
    pub spec fn index(self, i: int) -> A
        recommends
            0 <= i < self.len(),
    ;

    /// `[]` operator, synonymous with `index`
    #[verifier(inline)]
    pub open spec fn spec_index(self, i: int) -> A
        recommends
            0 <= i < self.len(),
    {
        self.index(i)
    }

    /// Appends the value `a` to the end of the sequence.
    /// This always increases the length of the sequence by 1.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn push_test() {
    ///     assert(seq![10, 11, 12].push(13) =~= seq![10, 11, 12, 13]);
    /// }
    /// ```
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::push"]
    pub spec fn push(self, a: A) -> Seq<A>;

    /// Updates the sequence at the given index, replacing the element with the given
    /// value, and leaves all other entries unchanged.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn update_test() {
    ///     let s = seq![10, 11, 12, 13, 14];
    ///     let t = s.update(2, -5);
    ///     assert(t =~= seq![10, 11, -5, 13, 14]);
    /// }
    /// ```
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::update"]
    pub spec fn update(self, i: int, a: A) -> Seq<A>
        recommends
            0 <= i < self.len(),
    ;

    /// DEPRECATED: use =~= or =~~= instead.
    /// Returns `true` if the two sequences are pointwise equal, i.e.,
    /// they have the same length and the corresponding values are equal
    /// at each index. This is equivalent to the sequences being actually equal
    /// by [`axiom_seq_ext_equal`].
    ///
    /// To prove that two sequences are equal via extensionality, it may be easier
    /// to use the general-purpose `=~=` or `=~~=` or
    /// to use the [`assert_seqs_equal!`](crate::seq_lib::assert_seqs_equal) macro,
    /// rather than using `.ext_equal` directly.
    #[deprecated = "use =~= or =~~= instead"]
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::ext_equal"]
    pub open spec fn ext_equal(self, s2: Seq<A>) -> bool {
        self =~= s2
    }

    /// Returns a sequence for the given subrange.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn subrange_test() {
    ///     let s = seq![10, 11, 12, 13, 14];
    ///     //                  ^-------^
    ///     //          0   1   2   3   4   5
    ///     let sub = s.subrange(2, 4);
    ///     assert(sub =~= seq![12, 13]);
    /// }
    /// ```
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::subrange"]
    pub spec fn subrange(self, start_inclusive: int, end_exclusive: int) -> Seq<A>
        recommends
            0 <= start_inclusive <= end_exclusive <= self.len(),
    ;

    /// Returns a sequence containing only the first n elements of the original sequence
    #[verifier(inline)]
    pub open spec fn take(self, n: int) -> Seq<A> {
        self.subrange(0, n)
    }

    /// Returns a sequence without the first n elements of the original sequence
    #[verifier(inline)]
    pub open spec fn skip(self, n: int) -> Seq<A> {
        self.subrange(n, self.len() as int)
    }

    /// Concatenates the sequences.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn add_test() {
    ///     assert(seq![10int, 11].add(seq![12, 13, 14])
    ///             =~= seq![10, 11, 12, 13, 14]);
    /// }
    /// ```
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::add"]
    pub spec fn add(self, rhs: Seq<A>) -> Seq<A>;

    /// `+` operator, synonymous with `add`
    #[verifier(inline)]
    pub open spec fn spec_add(self, rhs: Seq<A>) -> Seq<A> {
        self.add(rhs)
    }

    /// Returns the last element of the sequence.
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::last"]
    pub open spec fn last(self) -> A
        recommends
            0 < self.len(),
    {
        self[self.len() as int - 1]
    }

    /// Returns the first element of the sequence.
    #[rustc_diagnostic_item = "vstd::seq::Seq::first"]
    pub open spec fn first(self) -> A
        recommends
            0 < self.len(),
    {
        self[0]
    }
}

// Trusted axioms
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_index_decreases<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] (decreases_to!(s => s[i])),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_empty<A>()
    ensures
        #[trigger] Seq::<A>::empty().len() == 0,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_new_len<A>(len: nat, f: spec_fn(int) -> A)
    ensures
        #[trigger] Seq::new(len, f).len() == len,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_new_index<A>(len: nat, f: spec_fn(int) -> A, i: int)
    requires
        0 <= i < len,
    ensures
        Seq::new(len, f)[i] == f(i),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_push_len<A>(s: Seq<A>, a: A)
    ensures
        #[trigger] s.push(a).len() == s.len() + 1,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_push_index_same<A>(s: Seq<A>, a: A, i: int)
    requires
        i == s.len(),
    ensures
        #[trigger] s.push(a)[i] == a,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_push_index_different<A>(s: Seq<A>, a: A, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.push(a)[i] == s[i],
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_update_len<A>(s: Seq<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.update(i, a).len() == s.len(),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_update_same<A>(s: Seq<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.update(i, a)[i] == a,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_update_different<A>(s: Seq<A>, i1: int, i2: int, a: A)
    requires
        0 <= i1 < s.len(),
        0 <= i2 < s.len(),
        i1 != i2,
    ensures
        s.update(i2, a)[i1] == s[i1],
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_ext_equal<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] (s1 =~= s2) <==> {
            &&& s1.len() == s2.len()
            &&& forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]
        },
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_ext_equal_deep<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] (s1 =~~= s2) <==> {
            &&& s1.len() == s2.len()
            &&& forall|i: int| 0 <= i < s1.len() ==> s1[i] =~~= s2[i]
        },
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_subrange_len<A>(s: Seq<A>, j: int, k: int)
    requires
        0 <= j <= k <= s.len(),
    ensures
        #[trigger] s.subrange(j, k).len() == k - j,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_subrange_index<A>(s: Seq<A>, j: int, k: int, i: int)
    requires
        0 <= j <= k <= s.len(),
        0 <= i < k - j,
    ensures
        s.subrange(j, k)[i] == s[i + j],
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_add_len<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] s1.add(s2).len() == s1.len() + s2.len(),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_add_index1<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        0 <= i < s1.len(),
    ensures
        s1.add(s2)[i] == s1[i],
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_seq_add_index2<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        s1.len() <= i < s1.len() + s2.len(),
    ensures
        s1.add(s2)[i] == s2[i - s1.len()],
{
}

// ------------- Macros ---------------- //
#[doc(hidden)]
#[macro_export]
macro_rules! seq_internal {
    [$($elem:expr),* $(,)?] => {
        $crate::seq::Seq::empty()
            $(.push($elem))*
    }
}

/// Creates a [`Seq`] containing the given elements.
///
/// ## Example
///
/// ```rust
/// let s = seq![11, 12, 13];
///
/// assert(s.len() == 3);
/// assert(s[0] == 11);
/// assert(s[1] == 12);
/// assert(s[2] == 13);
/// ```
#[macro_export]
macro_rules! seq {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::seq::seq_internal!($($tail)*))
    };
}

#[doc(hidden)]
pub use seq_internal;
pub use seq;

} // verus!
}

pub mod seq_lib {
    #[allow(unused_imports)]
    use crate::multiset::Multiset;
    #[allow(unused_imports)]
    use crate::pervasive::*;
    #[allow(unused_imports)]
    use crate::relations::*;
    #[allow(unused_imports)]
    use crate::seq::*;
    #[allow(unused_imports)]
    use crate::set::Set;
    #[cfg(verus_keep_ghost)]
    use crate::set_lib::lemma_set_properties;
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use builtin_macros::*;

    verus! {

impl<A> Seq<A> {
    /// Applies the function `f` to each element of the sequence, and returns
    /// the resulting sequence.
    /// The `int` parameter of `f` is the index of the element being mapped.
    // TODO(verus): rename to map_entries, for consistency with Map::map
    pub open spec fn map<B>(self, f: spec_fn(int, A) -> B) -> Seq<B> {
        Seq::new(self.len(), |i: int| f(i, self[i]))
    }

    /// Applies the function `f` to each element of the sequence, and returns
    /// the resulting sequence.
    /// The `int` parameter of `f` is the index of the element being mapped.
    // TODO(verus): rename to map, because this is what everybody wants.
    pub open spec fn map_values<B>(self, f: spec_fn(A) -> B) -> Seq<B> {
        Seq::new(self.len(), |i: int| f(self[i]))
    }

    /// Is true if the calling sequence is a prefix of the given sequence 'other'.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn prefix_test() {
    ///     let pre: Seq<int> = seq![1, 2, 3];
    ///     let whole: Seq<int> = seq![1, 2, 3, 4, 5];
    ///     assert(pre.is_prefix_of(whole));
    /// }
    /// ```
    pub open spec fn is_prefix_of(self, other: Self) -> bool {
        self.len() <= other.len() && self =~= other.subrange(0, self.len() as int)
    }

    /// Is true if the calling sequence is a suffix of the given sequence 'other'.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn suffix_test() {
    ///     let end: Seq<int> = seq![3, 4, 5];
    ///     let whole: Seq<int> = seq![1, 2, 3, 4, 5];
    ///     assert(end.is_suffix_of(whole));
    /// }
    /// ```
    pub open spec fn is_suffix_of(self, other: Self) -> bool {
        self.len() <= other.len() && self =~= other.subrange(
            (other.len() - self.len()) as int,
            other.len() as int,
        )
    }

    /// Sorts the sequence according to the given leq function
    ///
    /// ## Example
    ///
    /// ```rust
    /// {{#include ../../../rust_verify/example/multiset.rs:sorted_by_leq}}
    /// ```
    pub closed spec fn sort_by(self, leq: spec_fn(A, A) -> bool) -> Seq<A>
        recommends
            total_ordering(leq),
        decreases self.len(),
    {
        if self.len() <= 1 {
            self
        } else {
            let split_index = self.len() / 2;
            let left = self.subrange(0, split_index as int);
            let right = self.subrange(split_index as int, self.len() as int);
            let left_sorted = left.sort_by(leq);
            let right_sorted = right.sort_by(leq);
            merge_sorted_with(left_sorted, right_sorted, leq)
        }
    }

    pub proof fn lemma_sort_by_ensures(self, leq: spec_fn(A, A) -> bool)
        requires
            total_ordering(leq),
        ensures
            self.to_multiset() =~= self.sort_by(leq).to_multiset(),
            sorted_by(self.sort_by(leq), leq),
            forall|x: A| !self.contains(x) ==> !(#[trigger] self.sort_by(leq).contains(x)),
        decreases self.len(),
    {
        if self.len() <= 1 {
        } else {
            let split_index = self.len() / 2;
            let left = self.subrange(0, split_index as int);
            let right = self.subrange(split_index as int, self.len() as int);
            assert(self =~= left + right);
            let left_sorted = left.sort_by(leq);
            left.lemma_sort_by_ensures(leq);
            let right_sorted = right.sort_by(leq);
            right.lemma_sort_by_ensures(leq);
            lemma_merge_sorted_with_ensures(left_sorted, right_sorted, leq);
            lemma_multiset_commutative(left, right);
            lemma_multiset_commutative(left_sorted, right_sorted);
            assert forall|x: A| !self.contains(x) implies !(#[trigger] self.sort_by(leq).contains(
                x,
            )) by {
                self.to_multiset_ensures();
                self.sort_by(leq).to_multiset_ensures();
                assert(!self.contains(x) ==> self.to_multiset().count(x) == 0);
            }
        }
    }

    /// Returns the sequence containing only the elements of the original sequence
    /// such that pred(element) is true.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn filter_test() {
    ///    let seq: Seq<int> = seq![1, 2, 3, 4, 5];
    ///    let even: Seq<int> = seq.filter(|x| x % 2 == 0);
    ///    reveal_with_fuel(Seq::<int>::filter, 6); //Needed for Verus to unfold the recursive definition of filter
    ///    assert(even =~= seq![2, 4]);
    /// }
    /// ```
    #[verifier::opaque]
    pub open spec fn filter(self, pred: spec_fn(A) -> bool) -> Self
        decreases self.len(),
    {
        if self.len() == 0 {
            self
        } else {
            let subseq = self.drop_last().filter(pred);
            if pred(self.last()) {
                subseq.push(self.last())
            } else {
                subseq
            }
        }
    }

    pub proof fn filter_lemma(self, pred: spec_fn(A) -> bool)
        ensures
    // we don't keep anything bad
    // TODO(andrea): recommends didn't catch this error, where i isn't known to be in
    // self.filter(pred).len()
    //forall |i: int| 0 <= i < self.len() ==> pred(#[trigger] self.filter(pred)[i]),

            forall|i: int|
                0 <= i < self.filter(pred).len() ==> pred(#[trigger] self.filter(pred)[i]),
            // we keep everything we should
            forall|i: int|
                0 <= i < self.len() && pred(self[i]) ==> #[trigger] self.filter(pred).contains(
                    self[i],
                ),
            // the filtered list can't grow
            self.filter(pred).len() <= self.len(),
        decreases self.len(),
    {
        reveal(Seq::filter);
        let out = self.filter(pred);
        if 0 < self.len() {
            self.drop_last().filter_lemma(pred);
            assert forall|i: int| 0 <= i < out.len() implies pred(out[i]) by {
                if i < out.len() - 1 {
                    assert(self.drop_last().filter(pred)[i] == out.drop_last()[i]);  // trigger drop_last
                    assert(pred(out[i]));  // TODO(andrea): why is this line required? It's the conclusion of the assert-forall.
                }
            }
            assert forall|i: int|
                0 <= i < self.len() && pred(self[i]) implies #[trigger] out.contains(self[i]) by {
                if i == self.len() - 1 {
                    assert(self[i] == out[out.len() - 1]);  // witness to contains
                } else {
                    let subseq = self.drop_last().filter(pred);
                    assert(subseq.contains(self.drop_last()[i]));  // trigger recursive invocation
                    let j = choose|j| 0 <= j < subseq.len() && subseq[j] == self[i];
                    assert(out[j] == self[i]);  // TODO(andrea): same, seems needless
                }
            }
        }
    }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn filter_lemma_broadcast(self, pred: spec_fn(A) -> bool)
        ensures
            forall|i: int|
                0 <= i < self.filter(pred).len() ==> pred(#[trigger] self.filter(pred)[i])
                    && self.contains(self.filter(pred)[i]),
            forall|i: int|
                0 <= i < self.len() && pred(self[i]) ==> #[trigger] self.filter(pred).contains(
                    self[i],
                ),
            #[trigger] self.filter(pred).len() <= self.len(),
    ;

    proof fn filter_distributes_over_add(a: Self, b: Self, pred: spec_fn(A) -> bool)
        ensures
            (a + b).filter(pred) == a.filter(pred) + b.filter(pred),
        decreases b.len(),
    {
        reveal(Seq::filter);
        if 0 < b.len() {
            Self::drop_last_distributes_over_add(a, b);
            Self::filter_distributes_over_add(a, b.drop_last(), pred);
            if pred(b.last()) {
                Self::push_distributes_over_add(
                    a.filter(pred),
                    b.drop_last().filter(pred),
                    b.last(),
                );
            }
        } else {
            Self::add_empty_right(a, b);
            Self::add_empty_right(a.filter(pred), b.filter(pred));
        }
    }

    #[verifier(broadcast_forall)]
    pub proof fn add_empty_left(a: Self, b: Self)
        requires
            a.len() == 0,
        ensures
            a + b == b,
    {
        assert(a + b =~= b);
    }

    #[verifier(broadcast_forall)]
    pub proof fn add_empty_right(a: Self, b: Self)
        requires
            b.len() == 0,
        ensures
            a + b == a,
    {
        assert(a + b =~= a);
    }

    #[verifier(broadcast_forall)]
    pub proof fn push_distributes_over_add(a: Self, b: Self, elt: A)
        ensures
            (a + b).push(elt) == a + b.push(elt),
    {
        assert((a + b).push(elt) =~= a + b.push(elt));
    }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn filter_distributes_over_add_broacast(a: Self, b: Self, pred: spec_fn(A) -> bool)
        ensures
            #[trigger] (a + b).filter(pred) == a.filter(pred) + b.filter(pred),
    {
        // TODO(chris): We have perfectly good proofs sitting around for these broadcasts; they don't
        // need to be axioms!
        //        assert forall |a:Self, b:Self, pred:spec_fn(A)->bool| (a+b).filter(pred) == a.filter(pred) + b.filter(pred) by {
        //            Self::filter_distributes_over_add(a, b, pred);
        //        }
    }

    /// Returns the maximum value in a non-empty sequence, given sorting function leq
    pub open spec fn max_via(self, leq: spec_fn(A, A) -> bool) -> A
        recommends
            self.len() > 0,
        decreases self.len(),
    {
        if self.len() > 1 {
            if leq(self[0], self.subrange(1, self.len() as int).max_via(leq)) {
                self.subrange(1, self.len() as int).max_via(leq)
            } else {
                self[0]
            }
        } else {
            self[0]
        }
    }

    /// Returns the minimum value in a non-empty sequence, given sorting function leq
    pub open spec fn min_via(self, leq: spec_fn(A, A) -> bool) -> A
        recommends
            self.len() > 0,
        decreases self.len(),
    {
        if self.len() > 1 {
            let subseq = self.subrange(1, self.len() as int);
            let elt = subseq.min_via(leq);
            if leq(elt, self[0]) {
                elt
            } else {
                self[0]
            }
        } else {
            self[0]
        }
    }

    // TODO is_sorted -- extract from summer_school e22
    pub open spec fn contains(self, needle: A) -> bool {
        exists|i: int| 0 <= i < self.len() && self[i] == needle
    }

    /// Returns an index where `needle` appears in the sequence.
    /// Returns an arbitrary value if the sequence does not contain the `needle`.
    pub open spec fn index_of(self, needle: A) -> int {
        choose|i: int| 0 <= i < self.len() && self[i] == needle
    }

    /// For an element that occurs at least once in a sequence, if its first occurence
    /// is at index i, Some(i) is returned. Otherwise, None is returned
    pub closed spec fn index_of_first(self, needle: A) -> (result: Option<int>) {
        if self.contains(needle) {
            Some(self.first_index_helper(needle))
        } else {
            None
        }
    }

    // Recursive helper function for index_of_first
    spec fn first_index_helper(self, needle: A) -> int
        recommends
            self.contains(needle),
        decreases self.len(),
    {
        if self.len() <= 0 {
            -1  //arbitrary, will never get to this case

        } else if self[0] == needle {
            0
        } else {
            1 + self.subrange(1, self.len() as int).first_index_helper(needle)
        }
    }

    pub proof fn index_of_first_ensures(self, needle: A)
        ensures
            match self.index_of_first(needle) {
                Some(index) => {
                    &&& self.contains(needle)
                    &&& 0 <= index < self.len()
                    &&& self[index] == needle
                    &&& forall|j: int| 0 <= j < index < self.len() ==> self[j] != needle
                },
                None => { !self.contains(needle) },
            },
        decreases self.len(),
    {
        if self.contains(needle) {
            let index = self.index_of_first(needle).unwrap();
            if self.len() <= 0 {
            } else if self[0] == needle {
            } else {
                assert(Seq::empty().push(self.first()).add(self.drop_first()) =~= self);
                self.drop_first().index_of_first_ensures(needle);
            }
        }
    }

    /// For an element that occurs at least once in a sequence, if its last occurence
    /// is at index i, Some(i) is returned. Otherwise, None is returned
    pub closed spec fn index_of_last(self, needle: A) -> Option<int> {
        if self.contains(needle) {
            Some(self.last_index_helper(needle))
        } else {
            None
        }
    }

    // Recursive helper function for last_index_of
    spec fn last_index_helper(self, needle: A) -> int
        recommends
            self.contains(needle),
        decreases self.len(),
    {
        if self.len() <= 0 {
            -1  //arbitrary, will never get to this case

        } else if self.last() == needle {
            self.len() - 1
        } else {
            self.drop_last().last_index_helper(needle)
        }
    }

    pub proof fn index_of_last_ensures(self, needle: A)
        ensures
            match self.index_of_last(needle) {
                Some(index) => {
                    &&& self.contains(needle)
                    &&& 0 <= index < self.len()
                    &&& self[index] == needle
                    &&& forall|j: int| 0 <= index < j < self.len() ==> self[j] != needle
                },
                None => { !self.contains(needle) },
            },
        decreases self.len(),
    {
        if self.contains(needle) {
            let index = self.index_of_last(needle).unwrap();
            if self.len() <= 0 {
            } else if self.last() == needle {
            } else {
                assert(self.drop_last().push(self.last()) =~= self);
                self.drop_last().index_of_last_ensures(needle);
            }
        }
    }

    /// Drops the last element of a sequence and returns a sequence whose length is
    /// thereby 1 smaller.
    ///
    /// If the input sequence is empty, the result is meaningless and arbitrary.
    pub open spec fn drop_last(self) -> Seq<A>
        recommends
            self.len() >= 1,
    {
        self.subrange(0, self.len() as int - 1)
    }

    /// Dropping the last element of a concatenation of `a` and `b` is equivalent
    /// to skipping the last element of `b` and then concatenating `a` and `b`
    pub proof fn drop_last_distributes_over_add(a: Self, b: Self)
        requires
            0 < b.len(),
        ensures
            (a + b).drop_last() == a + b.drop_last(),
    {
        assert_seqs_equal!((a+b).drop_last(), a+b.drop_last());
    }

    pub open spec fn drop_first(self) -> Seq<A>
        recommends
            self.len() >= 1,
    {
        self.subrange(1, self.len() as int)
    }

    /// returns `true` if the sequence has no duplicate elements
    pub open spec fn no_duplicates(self) -> bool {
        forall|i, j| (0 <= i < self.len() && 0 <= j < self.len() && i != j) ==> self[i] != self[j]
    }

    /// Returns `true` if two sequences are disjoint
    pub open spec fn disjoint(self, other: Self) -> bool {
        forall|i: int, j: int| 0 <= i < self.len() && 0 <= j < other.len() ==> self[i] != other[j]
    }

    /// Converts a sequence into a set
    pub open spec fn to_set(self) -> Set<A> {
        Set::new(|a: A| self.contains(a))
    }

    /// Converts a sequence into a multiset
    pub closed spec fn to_multiset(self) -> Multiset<A>
        decreases self.len(),
    {
        if self.len() == 0 {
            Multiset::<A>::empty()
        } else {
            Multiset::<A>::empty().insert(self.first()).add(self.drop_first().to_multiset())
        }
    }

    /// Proof of function to_multiset() correctness
    pub proof fn to_multiset_ensures(self)
        ensures
            forall|a: A| #[trigger] (self.push(a).to_multiset()) =~= self.to_multiset().insert(a),
            self.len() == self.to_multiset().len(),
            forall|a: A| self.contains(a) <==> #[trigger] self.to_multiset().count(a) > 0,
    {
        assert forall|a: A| #[trigger]
            (self.push(a).to_multiset()) =~= self.to_multiset().insert(a) by {
            to_multiset_build(self, a);
        }
        to_multiset_len(self);
        assert forall|a: A| self.contains(a) <==> #[trigger] self.to_multiset().count(a) > 0 by {
            to_multiset_contains(self, a);
        }
    }

    /// Insert item a at index i, shifting remaining elements (if any) to the right
    pub open spec fn insert(self, i: int, a: A) -> Seq<A>
        recommends
            0 <= i <= self.len(),
    {
        self.subrange(0, i).push(a) + self.subrange(i, self.len() as int)
    }

    /// Proof of correctness and expected properties of insert function
    pub proof fn insert_ensures(self, pos: int, elt: A)
        requires
            0 <= pos <= self.len(),
        ensures
            self.insert(pos, elt).len() == self.len() + 1,
            forall|i: int| 0 <= i < pos ==> #[trigger] self.insert(pos, elt)[i] == self[i],
            forall|i: int| pos <= i < self.len() ==> self.insert(pos, elt)[i + 1] == self[i],
            self.insert(pos, elt)[pos] == elt,
    {
    }

    /// Remove item at index i, shifting remaining elements to the left
    pub open spec fn remove(self, i: int) -> Seq<A>
        recommends
            0 <= i < self.len(),
    {
        self.subrange(0, i) + self.subrange(i + 1, self.len() as int)
    }

    /// Proof of function remove() correctness
    pub proof fn remove_ensures(self, i: int)
        requires
            0 <= i < self.len(),
        ensures
            self.remove(i).len() == self.len() - 1,
            forall|index: int| 0 <= index < i ==> #[trigger] self.remove(i)[index] == self[index],
            forall|index: int|
                i <= index < self.len() - 1 ==> #[trigger] self.remove(i)[index] == self[index + 1],
    {
    }

    /// If a given element occurs at least once in a sequence, the sequence without
    /// its first occurrence is returned. Otherwise the same sequence is returned.
    pub open spec fn remove_value(self, val: A) -> Seq<A> {
        let index = self.index_of_first(val);
        match index {
            Some(i) => self.remove(i),
            None => self,
        }
    }

    /// Returns the sequence that is in reverse order to a given sequence.
    pub open spec fn reverse(self) -> Seq<A>
        decreases self.len(),
    {
        if self.len() == 0 {
            Seq::empty()
        } else {
            Seq::new(self.len(), |i: int| self[self.len() - 1 - i])
        }
    }

    /// Zips two sequences of equal length into one sequence that consists of pairs.
    /// If the two sequences are different lengths, returns an empty sequence
    pub open spec fn zip_with<B>(self, other: Seq<B>) -> Seq<(A, B)>
        recommends
            self.len() == other.len(),
        decreases self.len(),
    {
        if self.len() != other.len() {
            Seq::empty()
        } else if self.len() == 0 {
            Seq::empty()
        } else {
            Seq::new(self.len(), |i: int| (self[i], other[i]))
        }
    }

    /// Folds the sequence to the left, applying `f` to perform the fold.
    ///
    /// Equivalent to `Iterator::fold` in Rust.
    ///
    /// Given a sequence `s = [x0, x1, x2, ..., xn]`, applying this function `s.fold_left(b, f)`
    /// returns `f(...f(f(b, x0), x1), ..., xn)`.
    pub open spec fn fold_left<B>(self, b: B, f: spec_fn(B, A) -> B) -> (res: B)
        decreases self.len(),
    {
        if self.len() == 0 {
            b
        } else {
            f(self.drop_last().fold_left(b, f), self.last())
        }
    }

    /// Equivalent to [`Self::fold_left`] but defined by breaking off the leftmost element when
    /// recursing, rather than the rightmost. See [`Self::lemma_fold_left_alt`] that proves
    /// equivalence.
    pub open spec fn fold_left_alt<B>(self, b: B, f: spec_fn(B, A) -> B) -> (res: B)
        decreases self.len(),
    {
        if self.len() == 0 {
            b
        } else {
            self.subrange(1, self.len() as int).fold_left_alt(f(b, self[0]), f)
        }
    }

    /// An auxiliary lemma for proving [`Self::lemma_fold_left_alt`].
    proof fn aux_lemma_fold_left_alt<B>(self, b: B, f: spec_fn(B, A) -> B, k: int)
        requires
            0 < k <= self.len(),
        ensures
            self.subrange(k, self.len() as int).fold_left_alt(
                self.subrange(0, k).fold_left_alt(b, f),
                f,
            ) == self.fold_left_alt(b, f),
        decreases k,
    {
        reveal_with_fuel(Seq::fold_left_alt, 2);
        if k == 1 {
            // trivial base case
        } else {
            self.subrange(1, self.len() as int).aux_lemma_fold_left_alt(f(b, self[0]), f, k - 1);
            assert_seqs_equal!(
                self.subrange(1, self.len() as int)
                    .subrange(k - 1, self.subrange(1, self.len() as int).len() as int) ==
                self.subrange(k, self.len() as int)
            );
            assert_seqs_equal!(
                self.subrange(1, self.len() as int).subrange(0, k - 1) ==
                self.subrange(1, k)
            );
            assert_seqs_equal!(
                self.subrange(0, k).subrange(1, self.subrange(0, k).len() as int) ==
                self.subrange(1, k)
            );
        }
    }

    /// [`Self::fold_left`] and [`Self::fold_left_alt`] are equivalent.
    pub proof fn lemma_fold_left_alt<B>(self, b: B, f: spec_fn(B, A) -> B)
        ensures
            self.fold_left(b, f) == self.fold_left_alt(b, f),
        decreases self.len(),
    {
        reveal_with_fuel(Seq::fold_left, 2);
        reveal_with_fuel(Seq::fold_left_alt, 2);
        if self.len() <= 1 {
            // trivial base cases
        } else {
            self.aux_lemma_fold_left_alt(b, f, self.len() - 1);
            self.subrange(self.len() - 1, self.len() as int).lemma_fold_left_alt(
                self.drop_last().fold_left_alt(b, f),
                f,
            );
            self.subrange(0, self.len() - 1).lemma_fold_left_alt(b, f);
        }
    }

    /// Folds the sequence to the right, applying `f` to perform the fold.
    ///
    /// Equivalent to `DoubleEndedIterator::rfold` in Rust.
    ///
    /// Given a sequence `s = [x0, x1, x2, ..., xn]`, applying this function `s.fold_right(b, f)`
    /// returns `f(x0, f(x1, f(x2, ..., f(xn, b)...)))`.
    pub open spec fn fold_right<B>(self, f: spec_fn(A, B) -> B, b: B) -> (res: B)
        decreases self.len(),
    {
        if self.len() == 0 {
            b
        } else {
            self.drop_last().fold_right(f, f(self.last(), b))
        }
    }

    /// Equivalent to [`Self::fold_right`] but defined by breaking off the leftmost element when
    /// recursing, rather than the rightmost. See [`Self::lemma_fold_right_alt`] that proves
    /// equivalence.
    pub open spec fn fold_right_alt<B>(self, f: spec_fn(A, B) -> B, b: B) -> (res: B)
        decreases self.len(),
    {
        if self.len() == 0 {
            b
        } else {
            f(self[0], self.subrange(1, self.len() as int).fold_right_alt(f, b))
        }
    }

    /// An auxiliary lemma for proving [`Self::lemma_fold_right_alt`].
    proof fn aux_lemma_fold_right_alt<B>(self, f: spec_fn(A, B) -> B, b: B, k: int)
        requires
            0 <= k < self.len(),
        ensures
            self.subrange(0, k).fold_right(f, self.subrange(k, self.len() as int).fold_right(f, b))
                == self.fold_right(f, b),
        decreases self.len(),
    {
        reveal_with_fuel(Seq::fold_right, 2);
        if k == self.len() - 1 {
            // trivial base case
        } else {
            self.subrange(0, self.len() - 1).aux_lemma_fold_right_alt(f, f(self.last(), b), k);
            assert_seqs_equal!(
                self.subrange(0, self.len() - 1).subrange(0, k) ==
                self.subrange(0, k)
            );
            assert_seqs_equal!(
                self.subrange(0, self.len() - 1).subrange(k, self.subrange(0, self.len() - 1).len() as int) ==
                self.subrange(k, self.len() - 1)
            );
            assert_seqs_equal!(
                self.subrange(k, self.len() as int).drop_last() ==
                self.subrange(k, self.len() - 1)
            );
        }
    }

    /// [`Self::fold_right`] and [`Self::fold_right_alt`] are equivalent.
    pub proof fn lemma_fold_right_alt<B>(self, f: spec_fn(A, B) -> B, b: B)
        ensures
            self.fold_right(f, b) == self.fold_right_alt(f, b),
        decreases self.len(),
    {
        reveal_with_fuel(Seq::fold_right, 2);
        reveal_with_fuel(Seq::fold_right_alt, 2);
        if self.len() <= 1 {
            // trivial base cases
        } else {
            self.subrange(1, self.len() as int).lemma_fold_right_alt(f, b);
            self.aux_lemma_fold_right_alt(f, b, 1);
        }
    }

    // Proven lemmas
    /// Given a sequence with no duplicates, each element occurs only
    /// once in its conversion to a multiset
    pub proof fn lemma_multiset_has_no_duplicates(self)
        requires
            self.no_duplicates(),
        ensures
            forall|x: A| self.to_multiset().contains(x) ==> self.to_multiset().count(x) == 1,
        decreases self.len(),
    {
        if self.len() == 0 {
            assert(forall|x: A|
                self.to_multiset().contains(x) ==> self.to_multiset().count(x) == 1);
        } else {
            lemma_seq_properties::<A>();
            assert(self.drop_last().push(self.last()) =~= self);
            self.drop_last().lemma_multiset_has_no_duplicates();
        }
    }

    /// The concatenation of two subsequences derived from a non-empty sequence,
    /// the first obtained from skipping the last element, the second consisting only
    /// of the last element, is the original sequence.
    pub proof fn lemma_add_last_back(self)
        requires
            0 < self.len(),
        ensures
            #[trigger] self.drop_last().push(self.last()) =~= self,
    {
    }

    /// If a predicate is true at every index of a sequence,
    /// it is true for every member of the sequence as a collection.
    /// Useful for converting quantifiers between the two forms
    /// to satisfy a precondition in the latter form.
    pub proof fn lemma_indexing_implies_membership(self, f: spec_fn(A) -> bool)
        requires
            forall|i: int| 0 <= i < self.len() ==> #[trigger] f(#[trigger] self[i]),
        ensures
            forall|x: A| #[trigger] self.contains(x) ==> #[trigger] f(x),
    {
        assert(forall|i: int| 0 <= i < self.len() ==> #[trigger] self.contains(self[i]));
    }

    /// If a predicate is true for every member of a sequence as a collection,
    /// it is true at every index of the sequence.
    /// Useful for converting quantifiers between the two forms
    /// to satisfy a precondition in the latter form.
    pub proof fn lemma_membership_implies_indexing(self, f: spec_fn(A) -> bool)
        requires
            forall|x: A| #[trigger] self.contains(x) ==> #[trigger] f(x),
        ensures
            forall|i: int| 0 <= i < self.len() ==> #[trigger] f(self[i]),
    {
        assert forall|i: int| 0 <= i < self.len() implies #[trigger] f(self[i]) by {
            assert(self.contains(self[i]));
        }
    }

    /// A sequence that is sliced at the pos-th element, concatenated
    /// with that same sequence sliced from the pos-th element, is equal to the
    /// original unsliced sequence.
    pub proof fn lemma_split_at(self, pos: int)
        requires
            0 <= pos <= self.len(),
        ensures
            self.subrange(0, pos) + self.subrange(pos, self.len() as int) =~= self,
    {
    }

    /// Any element in a slice is included in the original sequence.
    pub proof fn lemma_element_from_slice(self, new: Seq<A>, a: int, b: int, pos: int)
        requires
            0 <= a <= b <= self.len(),
            new == self.subrange(a, b),
            a <= pos < b,
        ensures
            pos - a < new.len(),
            new[pos - a] == self[pos],
    {
    }

    /// A slice (from s2..e2) of a slice (from s1..e1) of a sequence is equal to just a
    /// slice (s1+s2..s1+e2) of the original sequence.
    pub proof fn lemma_slice_of_slice(self, s1: int, e1: int, s2: int, e2: int)
        requires
            0 <= s1 <= e1 <= self.len(),
            0 <= s2 <= e2 <= e1 - s1,
        ensures
            self.subrange(s1, e1).subrange(s2, e2) =~= self.subrange(s1 + s2, s1 + e2),
    {
    }

    /// A sequence of unique items, when converted to a set, produces a set with matching length
    pub proof fn unique_seq_to_set(self)
        requires
            self.no_duplicates(),
        ensures
            self.len() == self.to_set().len(),
        decreases self.len(),
    {
        seq_to_set_equal_rec::<A>(self);
        if self.len() == 0 {
        } else {
            let rest = self.drop_last();
            rest.unique_seq_to_set();
            seq_to_set_equal_rec::<A>(rest);
            seq_to_set_rec_is_finite::<A>(rest);
            assert(!seq_to_set_rec(rest).contains(self.last()));
            assert(seq_to_set_rec(rest).insert(self.last()).len() == seq_to_set_rec(rest).len()
                + 1);
        }
    }

    /// The cardinality of a set of elements is always less than or
    /// equal to that of the full sequence of elements.
    pub proof fn lemma_cardinality_of_set(self)
        ensures
            self.to_set().len() <= self.len(),
        decreases self.len(),
    {
        lemma_seq_properties::<A>();
        lemma_set_properties::<A>();
        if self.len() == 0 {
        } else {
            assert(self.drop_last().to_set().insert(self.last()) =~= self.to_set());
            self.drop_last().lemma_cardinality_of_set();
        }
    }

    /// A sequence is of length 0 if and only if its conversion to
    /// a set results in the empty set.
    pub proof fn lemma_cardinality_of_empty_set_is_0(self)
        ensures
            self.to_set().len() == 0 <==> self.len() == 0,
    {
        assert(self.len() == 0 ==> self.to_set().len() == 0) by { self.lemma_cardinality_of_set() }
        assert(!(self.len() == 0) ==> !(self.to_set().len() == 0)) by {
            if self.len() > 0 {
                assert(self.to_set().contains(self[0]));
                assert(self.to_set().remove(self[0]).len() <= self.to_set().len());
            }
        }
    }

    /// A sequence with cardinality equal to its set has no duplicates.
    /// Inverse property of that shown in lemma unique_seq_to_set
    pub proof fn lemma_no_dup_set_cardinality(self)
        requires
            self.to_set().len() == self.len(),
        ensures
            self.no_duplicates(),
        decreases self.len(),
    {
        lemma_seq_properties::<A>();
        if self.len() == 0 {
        } else {
            assert(self =~= Seq::empty().push(self.first()).add(self.drop_first()));
            if self.drop_first().contains(self.first()) {
                // If there is a duplicate, then we show that |s.to_set()| == |s| cannot hold.
                assert(self.to_set() =~= self.drop_first().to_set());
                assert(self.to_set().len() <= self.drop_first().len()) by {
                    self.drop_first().lemma_cardinality_of_set()
                }
            } else {
                assert(self.to_set().len() == 1 + self.drop_first().to_set().len()) by {
                    assert(self.drop_first().to_set().insert(self.first()) =~= self.to_set());
                }
                self.drop_first().lemma_no_dup_set_cardinality();
            }
        }
    }
}

impl<A, B> Seq<(A, B)> {
    /// Unzips a sequence that contains pairs into two separate sequences.
    pub closed spec fn unzip(self) -> (Seq<A>, Seq<B>) {
        (Seq::new(self.len(), |i: int| self[i].0), Seq::new(self.len(), |i: int| self[i].1))
    }

    /// Proof of correctness and expected properties of unzip function
    pub proof fn unzip_ensures(self)
        ensures
            self.unzip().0.len() == self.unzip().1.len(),
            self.unzip().0.len() == self.len(),
            self.unzip().1.len() == self.len(),
            forall|i: int|
                0 <= i < self.len() ==> (#[trigger] self.unzip().0[i], #[trigger] self.unzip().1[i])
                    == self[i],
        decreases self.len(),
    {
        if self.len() > 0 {
            self.drop_last().unzip_ensures();
        }
    }

    /// Unzipping a sequence of sequences and then zipping the resulting two sequences
    /// back together results in the original sequence of sequences.
    pub proof fn lemma_zip_of_unzip(self)
        ensures
            self.unzip().0.zip_with(self.unzip().1) =~= self,
    {
    }
}

impl<A> Seq<Seq<A>> {
    /// Flattens a sequence of sequences into a single sequence by concatenating
    /// subsequences, starting from the first element.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn flatten_test() {
    ///    let seq: Seq<Seq<int>> = seq![seq![1, 2, 3], seq![4, 5, 6], seq![7, 8, 9]];
    ///    let flat: Seq<int> = seq.flatten();
    ///    reveal_with_fuel(Seq::<Seq<int>>::flatten, 5); //Needed for Verus to unfold the recursive definition of flatten
    ///    assert(flat =~= seq![1, 2, 3, 4, 5, 6, 7, 8, 9]);
    /// }
    /// ```
    pub open spec fn flatten(self) -> Seq<A>
        decreases self.len(),
    {
        if self.len() == 0 {
            Seq::empty()
        } else {
            self.first().add(self.drop_first().flatten())
        }
    }

    /// Flattens a sequence of sequences into a single sequence by concatenating
    /// subsequences in reverse order, i.e. starting from the last element.
    /// This is equivalent to a call to `flatten`, but with concatenation operation
    /// applied along the oppositive associativity for the sake of proof reasoning in that direction.
    pub open spec fn flatten_alt(self) -> Seq<A>
        decreases self.len(),
    {
        if self.len() == 0 {
            Seq::empty()
        } else {
            self.drop_last().flatten_alt().add(self.last())
        }
    }

    /// Flattening a sequence of a sequence x, where x has length 1,
    /// results in a sequence equivalent to the single element of x
    pub proof fn lemma_flatten_one_element(self)
        ensures
            self.len() == 1 ==> self.flatten() == self.first(),
    {
        reveal(Seq::add_empty_right);
        if self.len() == 1 {
            assert(self.flatten() =~= self.first().add(self.drop_first().flatten()));
        }
    }

    /// The length of a flattened sequence of sequences x is greater than or
    /// equal to any of the lengths of the elements of x.
    pub proof fn lemma_flatten_length_ge_single_element_length(self, i: int)
        requires
            0 <= i < self.len(),
        ensures
            self.flatten_alt().len() >= self[i].len(),
        decreases self.len(),
    {
        if self.len() == 1 {
            self.lemma_flatten_one_element();
            self.lemma_flatten_and_flatten_alt_are_equivalent();
        } else if i < self.len() - 1 {
            self.drop_last().lemma_flatten_length_ge_single_element_length(i);
        } else {
            assert(self.flatten_alt() == self.drop_last().flatten_alt().add(self.last()));
        }
    }

    /// The length of a flattened sequence of sequences x is less than or equal
    /// to the length of x multiplied by a number greater than or equal to the
    /// length of the longest sequence in x.
    pub proof fn lemma_flatten_length_le_mul(self, j: int)
        requires
            forall|i: int| 0 <= i < self.len() ==> (#[trigger] self[i]).len() <= j,
        ensures
            self.flatten_alt().len() <= self.len() * j,
        decreases self.len(),
    {
        lemma_seq_properties::<A>();
        lemma_seq_properties::<Seq<A>>();
        if self.len() == 0 {
        } else {
            self.drop_last().lemma_flatten_length_le_mul(j);
            assert((self.len() - 1) * j == (self.len() * j) - (1 * j)) by (nonlinear_arith);  //TODO: use math library after imported
        }
    }

    /// Flattening sequences of sequences in order (starting from the beginning)
    /// and in reverse order (starting from the end) results in the same sequence.
    pub proof fn lemma_flatten_and_flatten_alt_are_equivalent(self)
        ensures
            self.flatten() == self.flatten_alt(),
        decreases self.len(),
    {
        reveal(Seq::add_empty_right);
        reveal(Seq::push_distributes_over_add);
        if self.len() != 0 {
            self.drop_last().lemma_flatten_and_flatten_alt_are_equivalent();
            seq![self.last()].lemma_flatten_one_element();
            lemma_flatten_concat(self.drop_last(), seq![self.last()]);
            assert(self =~= self.drop_last().push(self.last()));
        }
    }
}

/********************************* Extrema in Sequences *********************************/

impl Seq<int> {
    /// Returns the maximum integer value in a non-empty sequence of integers.
    pub open spec fn max(self) -> int
        recommends
            0 < self.len(),
        decreases self.len(),
    {
        if self.len() == 1 {
            self[0]
        } else if self.len() == 0 {
            0
        } else {
            let later_max = self.drop_first().max();
            if self[0] >= later_max {
                self[0]
            } else {
                later_max
            }
        }
    }

    /// Proof of correctness and expected properties for max function
    pub proof fn max_ensures(self)
        ensures
            forall|x: int| self.contains(x) ==> x <= self.max(),
            forall|i: int| 0 <= i < self.len() ==> self[i] <= self.max(),
            self.len() == 0 || self.contains(self.max()),
        decreases self.len(),
    {
        if self.len() <= 1 {
        } else {
            let elt = self.drop_first().max();
            assert(self.drop_first().contains(elt)) by { self.drop_first().max_ensures() }
            assert forall|i: int| 0 <= i < self.len() implies self[i] <= self.max() by {
                assert(i == 0 || self[i] == self.drop_first()[i - 1]);
                assert(forall|j: int|
                    0 <= j < self.drop_first().len() ==> self.drop_first()[j]
                        <= self.drop_first().max()) by { self.drop_first().max_ensures() }
            }
        }
    }

    /// Returns the minimum integer value in a non-empty sequence of integers.
    pub open spec fn min(self) -> int
        recommends
            0 < self.len(),
        decreases self.len(),
    {
        if self.len() == 1 {
            self[0]
        } else if self.len() == 0 {
            0
        } else {
            let later_min = self.drop_first().min();
            if self[0] <= later_min {
                self[0]
            } else {
                later_min
            }
        }
    }

    /// Proof of correctness and expected properties for min function
    pub proof fn min_ensures(self)
        ensures
            forall|x: int| self.contains(x) ==> self.min() <= x,
            forall|i: int| 0 <= i < self.len() ==> self.min() <= self[i],
            self.len() == 0 || self.contains(self.min()),
        decreases self.len(),
    {
        if self.len() <= 1 {
        } else {
            let elt = self.drop_first().min();
            assert(self.subrange(1, self.len() as int).contains(elt)) by {
                self.drop_first().min_ensures()
            }
            assert forall|i: int| 0 <= i < self.len() implies self.min() <= self[i] by {
                assert(i == 0 || self[i] == self.drop_first()[i - 1]);
                assert(forall|j: int|
                    0 <= j < self.drop_first().len() ==> self.drop_first().min()
                        <= self.drop_first()[j]) by { self.drop_first().min_ensures() }
            }
        }
    }

    pub closed spec fn sort(self) -> Self {
        self.sort_by(|x: int, y: int| x <= y)
    }

    pub proof fn lemma_sort_ensures(self)
        ensures
            self.to_multiset() =~= self.sort().to_multiset(),
            sorted_by(self.sort(), |x: int, y: int| x <= y),
    {
        self.lemma_sort_by_ensures(|x: int, y: int| x <= y);
    }

    /// The maximum element in a non-empty sequence is greater than or equal to
    /// the maxima of its non-empty subsequences.
    pub proof fn lemma_subrange_max(self, from: int, to: int)
        requires
            0 <= from < to <= self.len(),
        ensures
            self.subrange(from, to).max() <= self.max(),
    {
        self.max_ensures();
        self.subrange(from, to).max_ensures();
    }

    /// The minimum element in a non-empty sequence is less than or equal to
    /// the minima of its non-empty subsequences.
    pub proof fn lemma_subrange_min(self, from: int, to: int)
        requires
            0 <= from < to <= self.len(),
        ensures
            self.subrange(from, to).min() >= self.min(),
    {
        self.min_ensures();
        self.subrange(from, to).min_ensures();
    }
}

// Helper function to aid with merge sort
spec fn merge_sorted_with<A>(left: Seq<A>, right: Seq<A>, leq: spec_fn(A, A) -> bool) -> Seq<A>
    recommends
        sorted_by(left, leq),
        sorted_by(right, leq),
        total_ordering(leq),
    decreases left.len(), right.len(),
{
    if left.len() == 0 {
        right
    } else if right.len() == 0 {
        left
    } else if leq(left.first(), right.first()) {
        Seq::<A>::empty().push(left.first()) + merge_sorted_with(left.drop_first(), right, leq)
    } else {
        Seq::<A>::empty().push(right.first()) + merge_sorted_with(left, right.drop_first(), leq)
    }
}

proof fn lemma_merge_sorted_with_ensures<A>(left: Seq<A>, right: Seq<A>, leq: spec_fn(A, A) -> bool)
    requires
        sorted_by(left, leq),
        sorted_by(right, leq),
        total_ordering(leq),
    ensures
        (left + right).to_multiset() =~= merge_sorted_with(left, right, leq).to_multiset(),
        sorted_by(merge_sorted_with(left, right, leq), leq),
    decreases left.len(), right.len(),
{
    lemma_seq_properties::<A>();
    if left.len() == 0 {
        assert(left + right =~= right);
    } else if right.len() == 0 {
        assert(left + right =~= left);
    } else if leq(left.first(), right.first()) {
        let result = Seq::<A>::empty().push(left.first()) + merge_sorted_with(
            left.drop_first(),
            right,
            leq,
        );
        lemma_merge_sorted_with_ensures(left.drop_first(), right, leq);
        let rest = merge_sorted_with(left.drop_first(), right, leq);
        assert(rest.len() == 0 || rest.first() == left.drop_first().first() || rest.first()
            == right.first()) by {
            if left.drop_first().len() == 0 {
            } else if leq(left.drop_first().first(), right.first()) {
                assert(rest =~= Seq::<A>::empty().push(left.drop_first().first())
                    + merge_sorted_with(left.drop_first().drop_first(), right, leq));
            } else {
                assert(rest =~= Seq::<A>::empty().push(right.first()) + merge_sorted_with(
                    left.drop_first(),
                    right.drop_first(),
                    leq,
                ));
            }
        }
        lemma_new_first_element_still_sorted_by(left.first(), rest, leq);
        assert((left.drop_first() + right) =~= (left + right).drop_first());
    } else {
        let result = Seq::<A>::empty().push(right.first()) + merge_sorted_with(
            left,
            right.drop_first(),
            leq,
        );
        lemma_merge_sorted_with_ensures(left, right.drop_first(), leq);
        let rest = merge_sorted_with(left, right.drop_first(), leq);
        assert(rest.len() == 0 || rest.first() == left.first() || rest.first()
            == right.drop_first().first()) by {
            assert(left.len() > 0);
            if right.drop_first().len() == 0 {  /*assert(rest =~= left);*/
            } else if leq(left.first(), right.drop_first().first()) {  //right might be length 1
                assert(rest =~= Seq::<A>::empty().push(left.first()) + merge_sorted_with(
                    left.drop_first(),
                    right.drop_first(),
                    leq,
                ));
            } else {
                assert(rest =~= Seq::<A>::empty().push(right.drop_first().first())
                    + merge_sorted_with(left, right.drop_first().drop_first(), leq));
            }
        }
        lemma_new_first_element_still_sorted_by(
            right.first(),
            merge_sorted_with(left, right.drop_first(), leq),
            leq,
        );
        lemma_seq_union_to_multiset_commutative(left, right);
        assert((right.drop_first() + left) =~= (right + left).drop_first());
        lemma_seq_union_to_multiset_commutative(right.drop_first(), left);
    }
}

/// The maximum of the concatenation of two non-empty sequences is greater than or
/// equal to the maxima of its two non-empty subsequences.
pub proof fn lemma_max_of_concat(x: Seq<int>, y: Seq<int>)
    requires
        0 < x.len() && 0 < y.len(),
    ensures
        x.max() <= (x + y).max(),
        y.max() <= (x + y).max(),
        forall|elt: int| (x + y).contains(elt) ==> elt <= (x + y).max(),
    decreases x.len(),
{
    lemma_seq_properties::<int>();
    x.max_ensures();
    y.max_ensures();
    (x + y).max_ensures();
    assert(x.drop_first().len() == x.len() - 1);
    if x.len() == 1 {
        assert(y.max() <= (x + y).max()) by {
            assert((x + y).contains(y.max()));
        }
    } else {
        assert(x.max() <= (x + y).max()) by {
            assert(x.contains(x.max()));
            assert((x + y).contains(x.max()));
        }
        assert(x.drop_first() + y =~= (x + y).drop_first());
        lemma_max_of_concat(x.drop_first(), y);
    }
}

/// The minimum of the concatenation of two non-empty sequences is less than or
/// equal to the minimum of its two non-empty subsequences.
pub proof fn lemma_min_of_concat(x: Seq<int>, y: Seq<int>)
    requires
        0 < x.len() && 0 < y.len(),
    ensures
        (x + y).min() <= x.min(),
        (x + y).min() <= y.min(),
        forall|elt: int| (x + y).contains(elt) ==> (x + y).min() <= elt,
    decreases x.len(),
{
    x.min_ensures();
    y.min_ensures();
    (x + y).min_ensures();
    lemma_seq_properties::<int>();
    if x.len() == 1 {
        assert((x + y).min() <= y.min()) by {
            assert((x + y).contains(y.min()));
        }
    } else {
        assert((x + y).min() <= x.min()) by {
            assert((x + y).contains(x.min()));
        }
        assert((x + y).min() <= y.min()) by {
            assert((x + y).contains(y.min()));
        }
        assert(x.drop_first() + y =~= (x + y).drop_first());
        lemma_max_of_concat(x.drop_first(), y)
    }
}

/************************* Sequence to Multiset Conversion **************************/

/// push(a) o to_multiset = to_multiset o insert(a)
proof fn to_multiset_build<A>(s: Seq<A>, a: A)
    ensures
        s.push(a).to_multiset() =~= s.to_multiset().insert(a),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.to_multiset() =~= Multiset::<A>::empty());
        assert(s.push(a).drop_first() =~= Seq::<A>::empty());
        assert(s.push(a).to_multiset() =~= Multiset::<A>::empty().insert(a).add(
            Seq::<A>::empty().to_multiset(),
        ));
    } else {
        to_multiset_build(s.drop_first(), a);
        assert(s.drop_first().push(a).to_multiset() =~= s.drop_first().to_multiset().insert(a));
        assert(s.push(a).drop_first() =~= s.drop_first().push(a));
    }
}

/// to_multiset() preserves length
proof fn to_multiset_len<A>(s: Seq<A>)
    ensures
        s.len() == s.to_multiset().len(),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.to_multiset() =~= Multiset::<A>::empty());
        assert(s.len() == 0);
    } else {
        to_multiset_len(s.drop_first());
        assert(s.len() == s.drop_first().len() + 1);
        assert(s.to_multiset().len() == s.drop_first().to_multiset().len() + 1);
    }
}

/// to_multiset() contains only the elements of the sequence
proof fn to_multiset_contains<A>(s: Seq<A>, a: A)
    ensures
        s.contains(a) <==> s.to_multiset().count(a) > 0,
    decreases s.len(),
{
    if s.len() != 0 {
        // ==>
        if s.contains(a) {
            if s.first() == a {
                to_multiset_build(s, a);
                assert(s.to_multiset() =~= Multiset::<A>::empty().insert(s.first()).add(
                    s.drop_first().to_multiset(),
                ));
                assert(Multiset::<A>::empty().insert(s.first()).contains(s.first()));
            } else {
                to_multiset_contains(s.drop_first(), a);
                assert(s.skip(1) =~= s.drop_first());
                lemma_seq_skip_contains(s, 1, a);
                assert(s.to_multiset().count(a) == s.drop_first().to_multiset().count(a));
                assert(s.contains(a) <==> s.to_multiset().count(a) > 0);
            }
        }
        // <==

        if s.to_multiset().count(a) > 0 {
            to_multiset_contains(s.drop_first(), a);
            assert(s.contains(a) <==> s.to_multiset().count(a) > 0);
        } else {
            assert(s.contains(a) <==> s.to_multiset().count(a) > 0);
        }
    }
}

/// The last element of two concatenated sequences, the second one being non-empty, will be the
/// last element of the latter sequence.
pub proof fn lemma_append_last<A>(s1: Seq<A>, s2: Seq<A>)
    requires
        0 < s2.len(),
    ensures
        (s1 + s2).last() == s2.last(),
{
}

/// The concatenation of sequences is associative
pub proof fn lemma_concat_associative<A>(s1: Seq<A>, s2: Seq<A>, s3: Seq<A>)
    ensures
        s1.add(s2.add(s3)) =~= s1.add(s2).add(s3),
{
}

/// Recursive definition of seq to set conversion
spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len(),
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}

// Helper function showing that the recursive definition of set_to_seq produces a finite set
proof fn seq_to_set_rec_is_finite<A>(seq: Seq<A>)
    ensures
        seq_to_set_rec(seq).finite(),
    decreases seq.len(),
{
    if seq.len() > 0 {
        let sub_seq = seq.drop_last();
        assert(seq_to_set_rec(sub_seq).finite()) by {
            seq_to_set_rec_is_finite(sub_seq);
        }
    }
}

// Helper function showing that the resulting set contains all elements of the sequence
proof fn seq_to_set_rec_contains<A>(seq: Seq<A>)
    ensures
        forall|a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a),
    decreases seq.len(),
{
    if seq.len() > 0 {
        assert(forall|a| #[trigger]
            seq.drop_last().contains(a) <==> seq_to_set_rec(seq.drop_last()).contains(a)) by {
            seq_to_set_rec_contains(seq.drop_last());
        }
        assert(seq =~= seq.drop_last().push(seq.last()));
        assert forall|a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a) by {
            if !seq.drop_last().contains(a) {
                if a == seq.last() {
                    assert(seq.contains(a));
                    assert(seq_to_set_rec(seq).contains(a));
                } else {
                    assert(!seq_to_set_rec(seq).contains(a));
                }
            }
        }
    }
}

// Helper function showing that the recursive definition matches the set comprehension one
proof fn seq_to_set_equal_rec<A>(seq: Seq<A>)
    ensures
        seq.to_set() == seq_to_set_rec(seq),
{
    assert(forall|n| #[trigger] seq.contains(n) <==> seq_to_set_rec(seq).contains(n)) by {
        seq_to_set_rec_contains(seq);
    }
    assert(forall|n| #[trigger] seq.contains(n) <==> seq.to_set().contains(n));
    assert(seq.to_set() =~= seq_to_set_rec(seq));
}

/// The set obtained from a sequence is finite
pub proof fn seq_to_set_is_finite<A>(seq: Seq<A>)
    ensures
        seq.to_set().finite(),
{
    assert(seq.to_set().finite()) by {
        seq_to_set_equal_rec(seq);
        seq_to_set_rec_is_finite(seq);
    }
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn seq_to_set_is_finite_broadcast<A>(seq: Seq<A>)
    ensures
        #[trigger] seq.to_set().finite(),
{
    // TODO: merge this with seq_to_set_is_finite when broadcast_forall is better supported
}

/// If sequences a and b don't have duplicates, and there are no
/// elements in common between them, then the concatenated sequence
/// a + b will not contain duplicates either.
pub proof fn lemma_no_dup_in_concat<A>(a: Seq<A>, b: Seq<A>)
    requires
        a.no_duplicates(),
        b.no_duplicates(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a[i] != b[j],
    ensures
        #[trigger] (a + b).no_duplicates(),
{
}

/// Flattening sequences of sequences is distributive over concatenation. That is, concatenating
/// the flattening of two sequences of sequences is the same as flattening the
/// concatenation of two sequences of sequences.
pub proof fn lemma_flatten_concat<A>(x: Seq<Seq<A>>, y: Seq<Seq<A>>)
    ensures
        (x + y).flatten() =~= x.flatten() + y.flatten(),
    decreases x.len(),
{
    if x.len() == 0 {
        assert(x + y =~= y);
    } else {
        assert((x + y).drop_first() =~= x.drop_first() + y);
        assert(x.first() + (x.drop_first() + y).flatten() =~= x.first() + x.drop_first().flatten()
            + y.flatten()) by {
            lemma_flatten_concat(x.drop_first(), y);
        }
    }
}

/// Flattening sequences of sequences in reverse order is distributive over concatentation.
/// That is, concatenating the flattening of two sequences of sequences in reverse
/// order is the same as flattening the concatenation of two sequences of sequences
/// in reverse order.
pub proof fn lemma_flatten_alt_concat<A>(x: Seq<Seq<A>>, y: Seq<Seq<A>>)
    ensures
        (x + y).flatten_alt() =~= x.flatten_alt() + y.flatten_alt(),
    decreases y.len(),
{
    if y.len() == 0 {
        assert(x + y =~= x);
    } else {
        assert((x + y).drop_last() =~= x + y.drop_last());
        assert((x + y.drop_last()).flatten_alt() + y.last() =~= x.flatten_alt()
            + y.drop_last().flatten_alt() + y.last()) by {
            lemma_flatten_alt_concat(x, y.drop_last());
        }
    }
}

/// The multiset of a concatenated sequence `a + b` is equivalent to the multiset of the
/// concatenated sequence `b + a`.
pub proof fn lemma_seq_union_to_multiset_commutative<A>(a: Seq<A>, b: Seq<A>)
    ensures
        (a + b).to_multiset() =~= (b + a).to_multiset(),
{
    lemma_multiset_commutative(a, b);
    lemma_multiset_commutative(b, a);
}

/// The multiset of a concatenated sequence `a + b` is equivalent to the multiset of just
/// sequence `a` added to the multiset of just sequence `b`.
pub proof fn lemma_multiset_commutative<A>(a: Seq<A>, b: Seq<A>)
    ensures
        (a + b).to_multiset() =~= a.to_multiset().add(b.to_multiset()),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        lemma_multiset_commutative(a.drop_first(), b);
        assert(a.drop_first() + b =~= (a + b).drop_first());
    }
}

/// Any two sequences that are sorted by a total order and that have the same elements are equal.
pub proof fn lemma_sorted_unique<A>(x: Seq<A>, y: Seq<A>, leq: spec_fn(A, A) -> bool)
    requires
        sorted_by(x, leq),
        sorted_by(y, leq),
        total_ordering(leq),
        x.to_multiset() == y.to_multiset(),
    ensures
        x =~= y,
    decreases x.len(), y.len(),
{
    x.to_multiset_ensures();
    y.to_multiset_ensures();
    if x.len() == 0 || y.len() == 0 {
    } else {
        assert(x.to_multiset().contains(x[0]));
        assert(x.to_multiset().contains(y[0]));
        let i = choose|i: int| #![trigger x.spec_index(i) ] 0 <= i < x.len() && x[i] == y[0];
        assert(leq(x[i], x[0]));
        assert(leq(x[0], x[i]));
        assert(x.drop_first().to_multiset() =~= x.to_multiset().remove(x[0]));
        assert(y.drop_first().to_multiset() =~= y.to_multiset().remove(y[0]));
        lemma_sorted_unique(x.drop_first(), y.drop_first(), leq);
        assert(x.drop_first() =~= y.drop_first());
        assert(x.first() == y.first());
        assert(x =~= Seq::<A>::empty().push(x.first()).add(x.drop_first()));
        assert(x =~= y);
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
pub proof fn lemma_seq_contains<A>(s: Seq<A>, x: A)
    ensures
        s.contains(x) <==> exists|i: int| 0 <= i < s.len() && s[i] == x,
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The empty sequence contains nothing
pub proof fn lemma_seq_empty_contains_nothing<A>(x: A)
    ensures
        !Seq::<A>::empty().contains(x),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
// Note: Dafny only does one way implication, but theoretically it could go both ways
/// A sequence with length 0 is equivalent to the empty sequence
pub proof fn lemma_seq_empty_equality<A>(s: Seq<A>)
    ensures
        s.len() == 0 ==> s =~= Seq::<A>::empty(),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The concatenation of two sequences contains only the elements
/// of the two sequences
pub proof fn lemma_seq_concat_contains_all_elements<A>(x: Seq<A>, y: Seq<A>, elt: A)
    ensures
        (x + y).contains(elt) <==> x.contains(elt) || y.contains(elt),
    decreases x.len(),
{
    if x.len() == 0 && y.len() > 0 {
        assert((x + y) =~= y);
    } else {
        assert forall|elt: A| #[trigger] x.contains(elt) implies #[trigger] (x + y).contains(
            elt,
        ) by {
            let index = choose|i: int| 0 <= i < x.len() && x[i] == elt;
            assert((x + y)[index] == elt);
        }
        assert forall|elt: A| #[trigger] y.contains(elt) implies #[trigger] (x + y).contains(
            elt,
        ) by {
            let index = choose|i: int| 0 <= i < y.len() && y[i] == elt;
            assert((x + y)[index + x.len()] == elt);
        }
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// After pushing an element onto a sequence, the sequence contains that element
pub proof fn lemma_seq_contains_after_push<A>(s: Seq<A>, v: A, x: A)
    ensures
        (s.push(v).contains(x) <==> v == x || s.contains(x)) && s.push(v).contains(v),
{
    assert forall|elt: A| #[trigger] s.contains(elt) implies #[trigger] s.push(v).contains(elt) by {
        let index = choose|i: int| 0 <= i < s.len() && s[i] == elt;
        assert(s.push(v)[index] == elt);
    }
    assert(s.push(v)[s.len() as int] == v);
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The subrange of a sequence contains only the elements within the indices `start` and `stop`
/// of the original sequence.
pub proof fn lemma_seq_subrange_elements<A>(s: Seq<A>, start: int, stop: int, x: A)
    requires
        0 <= start <= stop <= s.len(),
    ensures
        s.subrange(start, stop).contains(x) <==> (exists|i: int|
            0 <= start <= i < stop <= s.len() && s[i] == x),
{
    assert((exists|i: int| 0 <= start <= i < stop <= s.len() && s[i] == x) ==> s.subrange(
        start,
        stop,
    ).contains(x)) by {
        if exists|i: int| 0 <= start <= i < stop <= s.len() && s[i] == x {
            let index = choose|i: int| 0 <= start <= i < stop <= s.len() && s[i] == x;
            assert(s.subrange(start, stop)[index - start] == s[index]);
        }
    }
}

/************************** Lemmas about Take/Skip ***************************/

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the first `n` elements of a sequence results in a sequence of length `n`,
/// as long as `n` is within the bounds of the original sequence.
pub proof fn lemma_seq_take_len<A>(s: Seq<A>, n: int)
    ensures
        0 <= n <= s.len() ==> s.take(n).len() == n,
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The resulting sequence after taking the first `n` elements from sequence `s` contains
/// element `x` if and only if `x` is contained in the first `n` elements of `s`.
pub proof fn lemma_seq_take_contains<A>(s: Seq<A>, n: int, x: A)
    requires
        0 <= n <= s.len(),
    ensures
        s.take(n).contains(x) <==> (exists|i: int| 0 <= i < n <= s.len() && s[i] == x),
{
    assert((exists|i: int| 0 <= i < n <= s.len() && #[trigger] s[i] == x) ==> s.take(n).contains(x))
        by {
        if exists|i: int| 0 <= i < n <= s.len() && #[trigger] s[i] == x {
            let index = choose|i: int| 0 <= i < n <= s.len() && #[trigger] s[i] == x;
            assert(s.take(n)[index] == s[index]);
        }
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `j` is a valid index less than `n`, then the `j`th element of the sequence `s`
/// is the same as `j`th element of the sequence after taking the first `n` elements of `s`.
pub proof fn lemma_seq_take_index<A>(s: Seq<A>, n: int, j: int)
    ensures
        0 <= j < n <= s.len() ==> s.take(n)[j] == s[j],
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Skipping the first `n` elements of a sequence gives a sequence of length `n` less than
/// the original sequence's length.
pub proof fn lemma_seq_skip_len<A>(s: Seq<A>, n: int)
    ensures
        0 <= n <= s.len() ==> s.skip(n).len() == s.len() - n,
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The resulting sequence after skipping the first `n` elements from sequence `s` contains
/// element `x` if and only if `x` is contained in `s` before index `n`.
pub proof fn lemma_seq_skip_contains<A>(s: Seq<A>, n: int, x: A)
    requires
        0 <= n <= s.len(),
    ensures
        s.skip(n).contains(x) <==> (exists|i: int| 0 <= n <= i < s.len() && s[i] == x),
{
    assert((exists|i: int| 0 <= n <= i < s.len() && #[trigger] s[i] == x) ==> s.skip(n).contains(x))
        by {
        let index = choose|i: int| 0 <= n <= i < s.len() && #[trigger] s[i] == x;
        lemma_seq_skip_index(s, n, index - n);
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `j` is a valid index less than `s.len() - n`, then the `j`th element of the sequence
/// `s.skip(n)` is the same as the `j+n`th element of the sequence `s`.
pub proof fn lemma_seq_skip_index<A>(s: Seq<A>, n: int, j: int)
    ensures
        0 <= n && 0 <= j < (s.len() - n) ==> s.skip(n)[j] == s[j + n],
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `k` is a valid index between `n` (inclusive) and the length of sequence `s` (exclusive),
/// then the `k-n`th element of the sequence `s.skip(n)` is the same as the `k`th element of the
/// original sequence `s`.
pub proof fn lemma_seq_skip_index2<A>(s: Seq<A>, n: int, k: int)
    ensures
        0 <= n <= k < s.len() ==> (s.skip(n))[k - n] == s[k],
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `n` is the length of sequence `a`, then taking the first `n` elements of the concatenation
/// `a + b` is equivalent to the sequence `a` and skipping the first `n` elements of the concatenation
/// `a + b` is equivalent to the sequence `b`.
pub proof fn lemma_seq_append_take_skip<A>(a: Seq<A>, b: Seq<A>, n: int)
    ensures
        n == a.len() ==> ((a + b).take(n) =~= a && (a + b).skip(n) =~= b),
{
}

/************* Lemmas about the Commutability of Take and Skip with Update ************/

// This verified lemma used to be an axiom in the Dafny prelude
/// If `i` is in the first `n` indices of sequence `s`, updating sequence `s` at index `i` with
/// value `v` and then taking the first `n` elements is equivalent to first taking the first `n`
/// elements of `s` and then updating index `i` to value `v`.
pub proof fn lemma_seq_take_update_commut1<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= i < n <= s.len() ==> #[trigger] s.update(i, v).take(n) =~= s.take(n).update(i, v),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `i` is a valid index after the first `n` indices of sequence `s`, updating sequence `s` at
/// index `i` with value `v` and then taking the first `n` elements is equivalent to just taking the first `n`
/// elements of `s` without the update.
pub proof fn lemma_seq_take_update_commut2<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= n <= i < s.len() ==> #[trigger] s.update(i, v).take(n) =~= s.take(n),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `i` is a valid index after the first `n` indices of sequence `s`, updating sequence `s` at
/// index `i` with value `v` and then skipping the first `n` elements is equivalent to skipping the first `n`
/// elements of `s` and then updating index `i-n` to value `v`.
pub proof fn lemma_seq_skip_update_commut1<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= n <= i < s.len() ==> #[trigger] s.update(i, v).skip(n) =~= s.skip(n).update(i - n, v),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `i` is a valid index in the first `n` indices of sequence `s`, updating sequence `s` at
/// index `i` with value `v` and then skipping the first `n` elements is equivalent to just skipping
/// the first `n` elements without the update.
pub proof fn lemma_seq_skip_update_commut2<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= i < n <= s.len() ==> s.update(i, v).skip(n) =~= s.skip(n),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Pushing element `v` onto the end of sequence `s` and then skipping the first `n` elements is
/// equivalent to skipping the first `n` elements of `s` and then pushing `v` onto the end.
pub proof fn lemma_seq_skip_build_commut<A>(s: Seq<A>, v: A, n: int)
    ensures
        0 <= n <= s.len() ==> s.push(v).skip(n) =~= s.skip(n).push(v),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// `s.skip(0)` is equivalent to `s`.
pub proof fn lemma_seq_skip_nothing<A>(s: Seq<A>, n: int)
    ensures
        n == 0 ==> s.skip(n) =~= s,
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// `s.take(0)` is equivalent to the empty sequence.
pub proof fn lemma_seq_take_nothing<A>(s: Seq<A>, n: int)
    ensures
        n == 0 ==> s.take(n) =~= Seq::<A>::empty(),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `m + n` is less than or equal to the length of sequence `s`, then skipping the first `m` elements
/// and then skipping the first `n` elements of the resulting sequence is equivalent to just skipping
/// the first `m + n` elements.
pub proof fn lemma_seq_skip_of_skip<A>(s: Seq<A>, m: int, n: int)
    ensures
        (0 <= m && 0 <= n && m + n <= s.len()) ==> s.skip(m).skip(n) =~= s.skip(m + n),
{
}

/// Properties of sequences from the Dafny prelude (which were axioms in Dafny, but proven here in Verus)
pub proof fn lemma_seq_properties<A>()
    ensures
        forall|s: Seq<A>, x: A|
            s.contains(x) <==> exists|i: int| 0 <= i < s.len() && #[trigger] s[i] == x,  //from lemma_seq_contains(s, x),
        forall|x: A| !(#[trigger] Seq::<A>::empty().contains(x)),  //from lemma_seq_empty_contains_nothing(x),
        forall|s: Seq<A>| #[trigger] s.len() == 0 ==> s =~= Seq::<A>::empty(),  //from lemma_seq_empty_equality(s),
        forall|x: Seq<A>, y: Seq<A>, elt: A| #[trigger]
            (x + y).contains(elt) <==> x.contains(elt) || y.contains(elt),  //from lemma_seq_concat_contains_all_elements(x, y, elt),
        forall|s: Seq<A>, v: A, x: A|
            (#[trigger] s.push(v).contains(x) <==> v == x || s.contains(x)) && #[trigger] s.push(
                v,
            ).contains(v),  //from lemma_seq_contains_after_push(s, v, x)
        forall|s: Seq<A>, start: int, stop: int, x: A|
            (0 <= start <= stop <= s.len() && #[trigger] s.subrange(start, stop).contains(x)) <==> (
            exists|i: int| 0 <= start <= i < stop <= s.len() && #[trigger] s[i] == x),  //from lemma_seq_subrange_elements(s, start, stop, x),
        forall|s: Seq<A>, n: int| 0 <= n <= s.len() ==> #[trigger] s.take(n).len() == n,  //from lemma_seq_take_len(s, n)
        forall|s: Seq<A>, n: int, x: A|
            (#[trigger] s.take(n).contains(x) && 0 <= n <= s.len()) <==> (exists|i: int|
                0 <= i < n <= s.len() && #[trigger] s[i] == x),  //from lemma_seq_take_contains(s, n, x),
        forall|s: Seq<A>, n: int, j: int| 0 <= j < n <= s.len() ==> #[trigger] s.take(n)[j] == s[j],  //from lemma_seq_take_index(s, n, j),
        forall|s: Seq<A>, n: int| 0 <= n <= s.len() ==> #[trigger] s.skip(n).len() == s.len() - n,  //from lemma_seq_skip_len(s, n),
        forall|s: Seq<A>, n: int, x: A|
            (#[trigger] s.skip(n).contains(x) && 0 <= n <= s.len()) <==> (exists|i: int|
                0 <= n <= i < s.len() && #[trigger] s[i] == x),  //from lemma_seq_skip_contains(s, n, x),
        forall|s: Seq<A>, n: int, j: int|
            0 <= n && 0 <= j < (s.len() - n) ==> #[trigger] s.skip(n)[j] == s[j + n],  //from lemma_seq_skip_index(s, n, j),
        forall|a: Seq<A>, b: Seq<A>, n: int|
            #![trigger (a+b).take(n)]
            #![trigger (a+b).skip(n)]
            n == a.len() ==> ((a + b).take(n) =~= a && (a + b).skip(n) =~= b),  //from lemma_seq_append_take_skip(a, b, n),
        forall|s: Seq<A>, i: int, v: A, n: int|
            0 <= i < n <= s.len() ==> #[trigger] s.update(i, v).take(n) == s.take(n).update(i, v),  //from lemma_seq_take_update_commut1(s, i, v, n),
        forall|s: Seq<A>, i: int, v: A, n: int|
            0 <= n <= i < s.len() ==> #[trigger] s.update(i, v).take(n) == s.take(n),  //from lemma_seq_take_update_commut2(s, i, v, n),
        forall|s: Seq<A>, i: int, v: A, n: int|
            0 <= n <= i < s.len() ==> #[trigger] s.update(i, v).skip(n) == s.skip(n).update(
                i - n,
                v,
            ),  //from lemma_seq_skip_update_commut1(s, i, v, n),
        forall|s: Seq<A>, i: int, v: A, n: int|
            0 <= i < n <= s.len() ==> #[trigger] s.update(i, v).skip(n) == s.skip(n),  //from lemma_seq_skip_update_commut2(s, i, v, n),
        forall|s: Seq<A>, v: A, n: int|
            0 <= n <= s.len() ==> #[trigger] s.push(v).skip(n) == s.skip(n).push(v),  //from lemma_seq_skip_build_commut(s, v, n),
        forall|s: Seq<A>, n: int| n == 0 ==> #[trigger] s.skip(n) == s,  //from lemma_seq_skip_nothing(s, n),
        forall|s: Seq<A>, n: int| n == 0 ==> #[trigger] s.take(n) == Seq::<A>::empty(),  //from lemma_seq_take_nothing(s, n),
        forall|s: Seq<A>, m: int, n: int|
            (0 <= m && 0 <= n && m + n <= s.len()) ==> s.skip(m).skip(n) == s.skip(m + n),  //from lemma_seq_skip_of_skip(s, m, n),
        forall|s: Seq<A>, a: A| #[trigger] (s.push(a).to_multiset()) =~= s.to_multiset().insert(a),  //from o_multiset_properties
        forall|s: Seq<A>| s.len() == #[trigger] s.to_multiset().len(),  //from to_multiset_ensures
        forall|s: Seq<A>, a: A|
            s.contains(a) <==> #[trigger] s.to_multiset().count(a)
                > 0,  //from to_multiset_ensures
{
    assert forall|x: Seq<A>, y: Seq<A>, elt: A| #[trigger] (x + y).contains(elt) implies x.contains(
        elt,
    ) || y.contains(elt) by {
        lemma_seq_concat_contains_all_elements(x, y, elt);
    }
    assert forall|x: Seq<A>, y: Seq<A>, elt: A|
        x.contains(elt) || y.contains(elt) implies #[trigger] (x + y).contains(elt) by {
        lemma_seq_concat_contains_all_elements(x, y, elt);
    }
    assert forall|s: Seq<A>, v: A, x: A| #[trigger] s.push(v).contains(x) implies v == x
        || s.contains(x) by {
        lemma_seq_contains_after_push(s, v, x);
    }
    assert forall|s: Seq<A>, v: A, x: A| v == x || s.contains(x) implies #[trigger] s.push(
        v,
    ).contains(x) by {
        lemma_seq_contains_after_push(s, v, x);
    }
    assert forall|s: Seq<A>, start: int, stop: int, x: A|
        0 <= start <= stop <= s.len() && #[trigger] s.subrange(start, stop).contains(
            x,
        ) implies exists|i: int| 0 <= start <= i < stop <= s.len() && #[trigger] s[i] == x by {
        lemma_seq_subrange_elements(s, start, stop, x);
    }
    assert forall|s: Seq<A>, start: int, stop: int, x: A|
        exists|i: int|
            0 <= start <= i < stop <= s.len() && #[trigger] s[i] == x implies #[trigger] s.subrange(
        start,
        stop,
    ).contains(x) by {
        lemma_seq_subrange_elements(s, start, stop, x);
    }
    assert forall|s: Seq<A>, n: int, x: A| #[trigger]
        s.take(n).contains(x) && 0 <= n <= s.len() implies (exists|i: int|
        0 <= i < n <= s.len() && #[trigger] s[i] == x) by {
        lemma_seq_take_contains(s, n, x);
    }
    assert forall|s: Seq<A>, n: int, x: A|
        (exists|i: int| 0 <= i < n <= s.len() && #[trigger] s[i] == x) implies #[trigger] s.take(
        n,
    ).contains(x) by {
        lemma_seq_take_contains(s, n, x);
    }
    assert forall|s: Seq<A>, n: int, j: int| 0 <= j < n <= s.len() implies #[trigger] s.take(n)[j]
        == s[j] by {
        lemma_seq_take_len(s, n);
        assert(0 <= n <= s.len() ==> s.take(n).len() == n);
        assert(0 <= n <= s.len());
        assert(s.take(n).len() == n);
        lemma_seq_take_index(s, n, j);
    }
    assert forall|s: Seq<A>, n: int, x: A| #[trigger]
        s.skip(n).contains(x) && 0 <= n <= s.len() implies (exists|i: int|
        0 <= n <= i < s.len() && #[trigger] s[i] == x) by {
        lemma_seq_skip_contains(s, n, x);
    }
    assert forall|s: Seq<A>, n: int, x: A|
        (exists|i: int| 0 <= n <= i < s.len() && #[trigger] s[i] == x) implies #[trigger] s.skip(
        n,
    ).contains(x) && 0 <= n <= s.len() by {
        lemma_seq_skip_contains(s, n, x);
    }
    assert forall|s: Seq<A>, i: int, v: A, n: int|
        0 <= i < n <= s.len() implies #[trigger] s.update(i, v).take(n) == s.take(n).update(
        i,
        v,
    ) by {
        lemma_seq_take_update_commut1(s, i, v, n);
    }
    assert forall|s: Seq<A>, i: int, v: A, n: int|
        0 <= n <= i < s.len() implies #[trigger] s.update(i, v).take(n) == s.take(n) by {
        lemma_seq_take_update_commut2(s, i, v, n);
    }
    assert forall|s: Seq<A>, i: int, v: A, n: int|
        0 <= n <= i < s.len() implies #[trigger] s.update(i, v).skip(n) == s.skip(n).update(
        i - n,
        v,
    ) by {
        lemma_seq_skip_update_commut1(s, i, v, n);
    }
    assert forall|s: Seq<A>, i: int, v: A, n: int|
        0 <= i < n <= s.len() implies #[trigger] s.update(i, v).skip(n) == s.skip(n) by {
        lemma_seq_skip_update_commut2(s, i, v, n);
    }
    assert forall|s: Seq<A>, v: A, n: int| 0 <= n <= s.len() implies #[trigger] s.push(v).skip(n)
        == s.skip(n).push(v) by {
        lemma_seq_skip_build_commut(s, v, n);
    }
    assert forall|s: Seq<A>, n: int| n == 0 implies #[trigger] s.skip(n) == s by {
        lemma_seq_skip_nothing(s, n);
    }
    assert forall|s: Seq<A>, n: int| n == 0 implies #[trigger] s.take(n) == Seq::<A>::empty() by {
        lemma_seq_take_nothing(s, n);
    }
    assert forall|s: Seq<A>, m: int, n: int| (0 <= m && 0 <= n && m + n <= s.len()) implies s.skip(
        m,
    ).skip(n) == s.skip(m + n) by {
        lemma_seq_skip_of_skip(s, m, n);
    }
    assert forall|s: Seq<A>, a: A| #[trigger]
        (s.push(a).to_multiset()) =~= s.to_multiset().insert(a) by {
        s.to_multiset_ensures();
    }
    assert forall|s: Seq<A>| s.len() == #[trigger] s.to_multiset().len() by {
        s.to_multiset_ensures();
    }
    assert forall|s: Seq<A>, a: A| s.contains(a) implies #[trigger] s.to_multiset().count(a)
        > 0 by {
        s.to_multiset_ensures();
    }
    assert forall|s: Seq<A>, a: A| #[trigger] s.to_multiset().count(a) > 0 implies s.contains(
        a,
    ) by {
        s.to_multiset_ensures();
    }
}

#[doc(hidden)]
#[verifier(inline)]
pub open spec fn check_argument_is_seq<A>(s: Seq<A>) -> Seq<A> {
    s
}

/// Prove two sequences `s1` and `s2` are equal by proving that their elements are equal at each index.
///
/// More precisely, `assert_seqs_equal!` requires:
///  * `s1` and `s2` have the same length (`s1.len() == s2.len()`), and
///  * for all `i` in the range `0 <= i < s1.len()`, we have `s1[i] == s2[i]`.
///
/// The property that equality follows from these facts is often called _extensionality_.
///
/// `assert_seqs_equal!` can handle many trivial-looking
/// identities without any additional help:
///
/// ```rust
/// proof fn subrange_concat(s: Seq<u64>, i: int) {
///     requires([
///         0 <= i && i <= s.len(),
///     ]);
///
///     let t1 = s.subrange(0, i);
///     let t2 = s.subrange(i, s.len());
///     let t = t1.add(t2);
///
///     assert_seqs_equal!(s == t);
///
///     assert(s == t);
/// }
/// ```
///
/// In more complex cases, a proof may be required for the equality of each element pair.
/// For example,
///
/// ```rust
/// proof fn bitvector_seqs() {
///     let s = Seq::<u64>::new(5, |i| i as u64);
///     let t = Seq::<u64>::new(5, |i| i as u64 | 0);
///
///     assert_seqs_equal!(s == t, i => {
///         // Need to show that s[i] == t[i]
///         // Prove that the elements are equal by appealing to a bitvector solver:
///         let j = i as u64;
///         assert_bit_vector(j | 0 == j);
///         assert(s[i] == t[i]);
///     });
/// }
/// ```
#[macro_export]
macro_rules! assert_seqs_equal {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::seq_lib::assert_seqs_equal_internal!($($tail)*))
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! assert_seqs_equal_internal {
    (::builtin::spec_eq($s1:expr, $s2:expr)) => {
        assert_seqs_equal_internal!($s1, $s2)
    };
    (::builtin::spec_eq($s1:expr, $s2:expr), $idx:ident => $bblock:block) => {
        assert_seqs_equal_internal!($s1, $s2, $idx => $bblock)
    };
    ($s1:expr, $s2:expr $(,)?) => {
        assert_seqs_equal_internal!($s1, $s2, idx => { })
    };
    ($s1:expr, $s2:expr, $idx:ident => $bblock:block) => {
        #[verifier::spec] let s1 = $crate::seq_lib::check_argument_is_seq($s1);
        #[verifier::spec] let s2 = $crate::seq_lib::check_argument_is_seq($s2);
        ::builtin::assert_by(::builtin::equal(s1, s2), {
            ::builtin::assert_(s1.len() == s2.len());
            ::builtin::assert_forall_by(|$idx : ::builtin::int| {
                ::builtin::requires(::builtin_macros::verus_proof_expr!(0 <= $idx && $idx < s1.len()));
                ::builtin::ensures(::builtin::equal(s1.index($idx), s2.index($idx)));
                { $bblock }
            });
            ::builtin::assert_(::builtin::ext_equal(s1, s2));
        });
    }
}

#[doc(hidden)]
pub use assert_seqs_equal_internal;
pub use assert_seqs_equal;

} // verus!
}

pub mod set {
    use core::marker;

    #[allow(unused_imports)]
    use crate::map::*;
    #[allow(unused_imports)]
    use crate::pervasive::*;
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use builtin_macros::*;

    verus! {

/// `Set<A>` is a set type for specifications.
///
/// An object `set: Set<A>` is a subset of the set of all values `a: A`.
/// Equivalently, it can be thought of as a boolean predicate on `A`.
///
/// In general, a set might be infinite.
/// To work specifically with finite sets, see the [`self.finite()`](Set::finite) predicate.
///
/// Sets can be constructed in a few different ways:
///  * [`Set::empty`] gives an empty set
///  * [`Set::full`] gives the set of all elements in `A`
///  * [`Set::new`] constructs a set from a boolean predicate
///  * The [`set!`] macro, to construct small sets of a fixed size
///  * By manipulating an existing sequence with [`Set::union`], [`Set::intersect`],
///    [`Set::difference`], [`Set::complement`], [`Set::filter`], [`Set::insert`],
///    or [`Set::remove`].
///
/// To prove that two sequences are equal, it is usually easiest to use the extensionality
/// operator `=~=`.
#[verifier(external_body)]
#[verifier::ext_equal]
#[verifier::reject_recursive_types(A)]
pub struct Set<A> {
    dummy: marker::PhantomData<A>,
}

impl<A> Set<A> {
    /// The "empty" set.
    pub spec fn empty() -> Set<A>;

    /// Set whose membership is determined by the given boolean predicate.
    pub spec fn new<F: Fn(A) -> bool>(f: F) -> Set<A>;

    /// The "full" set, i.e., set containing every element of type `A`.
    pub open spec fn full() -> Set<A> {
        Set::empty().complement()
    }

    /// Predicate indicating if the set contains the given element.
    pub spec fn contains(self, a: A) -> bool;

    /// DEPRECATED: use =~= or =~~= instead.
    /// Returns `true` if for every value `a: A`, it is either in both input sets or neither.
    /// This is equivalent to the sets being actually equal
    /// by [`axiom_set_ext_equal`].
    ///
    /// To prove that two sets are equal via extensionality, it may be easier
    /// to use the general-purpose `=~=` or `=~~=` or
    /// to use the [`assert_sets_equal!`](crate::set_lib::assert_sets_equal) macro,
    /// rather than using `.ext_equal` directly.
    #[deprecated = "use =~= or =~~= instead"]
    pub open spec fn ext_equal(self, s2: Set<A>) -> bool {
        self =~= s2
    }

    /// Returns `true` if the first argument is a subset of the second.
    pub open spec fn subset_of(self, s2: Set<A>) -> bool {
        forall|a: A| self.contains(a) ==> s2.contains(a)
    }

    #[verifier(inline)]
    pub open spec fn spec_le(self, s2: Set<A>) -> bool {
        self.subset_of(s2)
    }

    /// Returns a new set with the given element inserted.
    /// If that element is already in the set, then an identical set is returned.
    pub spec fn insert(self, a: A) -> Set<A>;

    /// Returns a new set with the given element removed.
    /// If that element is already absent from the set, then an identical set is returned.
    pub spec fn remove(self, a: A) -> Set<A>;

    /// Union of two sets.
    pub spec fn union(self, s2: Set<A>) -> Set<A>;

    /// `+` operator, synonymous with `union`
    #[verifier(inline)]
    pub open spec fn spec_add(self, s2: Set<A>) -> Set<A> {
        self.union(s2)
    }

    /// Intersection of two sets.
    pub spec fn intersect(self, s2: Set<A>) -> Set<A>;

    /// `*` operator, synonymous with `intersect`
    #[verifier(inline)]
    pub open spec fn spec_mul(self, s2: Set<A>) -> Set<A> {
        self.intersect(s2)
    }

    /// Set difference, i.e., the set of all elements in the first one but not in the second.
    pub spec fn difference(self, s2: Set<A>) -> Set<A>;

    /// Set complement (within the space of all possible elements in `A`).
    /// `-` operator, synonymous with `difference`
    #[verifier(inline)]
    pub open spec fn spec_sub(self, s2: Set<A>) -> Set<A> {
        self.difference(s2)
    }

    pub spec fn complement(self) -> Set<A>;

    /// Set of all elements in the given set which satisfy the predicate `f`.
    pub open spec fn filter<F: Fn(A) -> bool>(self, f: F) -> Set<A> {
        self.intersect(Self::new(f))
    }

    /// Returns `true` if the set is finite.
    pub spec fn finite(self) -> bool;

    /// Cardinality of the set. (Only meaningful if a set is finite.)
    pub spec fn len(self) -> nat;

    /// Chooses an arbitrary element of the set.
    ///
    /// This is often useful for proofs by induction.
    ///
    /// (Note that, although the result is arbitrary, it is still a _deterministic_ function
    /// like any other `spec` function.)
    pub open spec fn choose(self) -> A {
        choose|a: A| self.contains(a)
    }

    /// Creates a [`Map`] whose domain is the given set.
    /// The values of the map are given by `f`, a function of the keys.
    pub spec fn mk_map<V, F: Fn(A) -> V>(self, f: F) -> Map<A, V>;

    /// Returns `true` if the sets are disjoint, i.e., if their interesection is
    /// the empty set.
    pub open spec fn disjoint(self, s2: Self) -> bool {
        forall|a: A| self.contains(a) ==> !s2.contains(a)
    }
}

// Trusted axioms
/// The empty set contains no elements
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_empty<A>(a: A)
    ensures
        !(#[trigger] Set::empty().contains(a)),
{
}

/// A call to `Set::new` with the predicate `f` contains `a` if and only if `f(a)` is true.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_new<A>(f: spec_fn(A) -> bool, a: A)
    ensures
        Set::new(f).contains(a) == f(a),
{
}

/// The result of inserting element `a` into set `s` must contains `a`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_same<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.insert(a).contains(a),
{
}

/// If `a1` does not equal `a2`, then the result of inserting element `a2` into set `s`
/// must contain `a1` if and only if the set contained `a1` before the insertion of `a2`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        s.insert(a2).contains(a1) == s.contains(a1),
{
}

/// The result of removing element `a` from set `s` must not contain `a`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_same<A>(s: Set<A>, a: A)
    ensures
        !(#[trigger] s.remove(a).contains(a)),
{
}

/// Removing an element `a` from a set `s` and then inserting `a` back into the set`
/// is equivalent to the original set `s`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_insert<A>(s: Set<A>, a: A)
    requires
        s.contains(a),
    ensures
        (#[trigger] s.remove(a)).insert(a) == s,
{
}

/// If `a1` does not equal `a2`, then the result of removing element `a2` from set `s`
/// must contain `a1` if and only if the set contained `a1` before the removal of `a2`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        s.remove(a2).contains(a1) == s.contains(a1),
{
}

/// The union of sets `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and/or `s2` contains `a`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_union<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        s1.union(s2).contains(a) == (s1.contains(a) || s2.contains(a)),
{
}

/// The intersection of sets `s1` and `s2` contains element `a` if and only if
/// both `s1` and `s2` contain `a`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_intersect<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
}

/// The set difference between `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and `s2` does not contain `a`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_difference<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
}

/// The complement of set `s` contains element `a` if and only if `s` does not contain `a`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_complement<A>(s: Set<A>, a: A)
    ensures
        s.complement().contains(a) == !s.contains(a),
{
}

/// Sets `s1` and `s2` are equal if and only if they contain all of the same elements.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_ext_equal<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger] (s1 =~= s2) <==> (forall|a: A| s1.contains(a) == s2.contains(a)),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_ext_equal_deep<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger] (s1 =~~= s2) <==> s1 =~= s2,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_mk_map_domain<K, V>(s: Set<K>, f: spec_fn(K) -> V)
    ensures
        #[trigger] s.mk_map(f).dom() == s,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_mk_map_index<K, V>(s: Set<K>, f: spec_fn(K) -> V, key: K)
    requires
        s.contains(key),
    ensures
        s.mk_map(f)[key] == f(key),
{
}

// Trusted axioms about finite
/// The empty set is finite.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_empty_finite<A>()
    ensures
        #[trigger] Set::<A>::empty().finite(),
{
}

/// The result of inserting an element `a` into a finite set `s` is also finite.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_finite<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).finite(),
{
}

/// The result of removing an element `a` from a finite set `s` is also finite.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_finite<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.remove(a).finite(),
{
}

/// The union of two finite sets is finite.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_union_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        #[trigger] s1.union(s2).finite(),
{
}

/// The intersection of two finite sets is finite.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_intersect_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite() || s2.finite(),
    ensures
        #[trigger] s1.intersect(s2).finite(),
{
}

/// The set difference between two finite sets is finite.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_difference_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        #[trigger] s1.difference(s2).finite(),
{
}

/// An infinite set `s` contains the element `s.choose()`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_choose_finite<A>(s: Set<A>)
    requires
        !s.finite(),
    ensures
        #[trigger] s.contains(s.choose()),
{
}

// Trusted axioms about len
// Note: we could add more axioms about len, but they would be incomplete.
// The following, with axiom_set_ext_equal, are enough to build libraries about len.
/// The empty set has length 0.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_empty_len<A>()
    ensures
        #[trigger] Set::<A>::empty().len() == 0,
{
}

/// The result of inserting an element `a` into a finite set `s` has length
/// `s.len() + 1` if `a` is not already in `s` and length `s.len()` otherwise.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).len() == s.len() + (if s.contains(a) {
            0int
        } else {
            1
        }),
{
}

/// The result of removing an element `a` from a finite set `s` has length
/// `s.len() - 1` if `a` is in `s` and length `s.len()` otherwise.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        s.len() == #[trigger] s.remove(a).len() + (if s.contains(a) {
            1int
        } else {
            0
        }),
{
}

/// If a finite set `s` contains any element, it has length greater than 0.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_contains_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
        #[trigger] s.contains(a),
    ensures
        #[trigger] s.len() != 0,
{
}

/// A finite set `s` contains the element `s.choose()` if it has length greater than 0.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_choose_len<A>(s: Set<A>)
    requires
        s.finite(),
        #[trigger] s.len() != 0,
    ensures
        #[trigger] s.contains(s.choose()),
{
}

// Macros
#[doc(hidden)]
#[macro_export]
macro_rules! set_internal {
    [$($elem:expr),* $(,)?] => {
        $crate::set::Set::empty()
            $(.insert($elem))*
    };
}

#[macro_export]
macro_rules! set {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::set::set_internal!($($tail)*))
    };
}

pub use set_internal;
pub use set;

} // verus!
}

pub mod set_lib {
    #[allow(unused_imports)]
    use crate::multiset::Multiset;
    #[allow(unused_imports)]
    use crate::pervasive::*;
    use crate::prelude::Seq;
    #[allow(unused_imports)]
    use crate::relations::*;
    #[allow(unused_imports)]
    use crate::set::*;
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use builtin_macros::*;

    verus! {

impl<A> Set<A> {
    /// Is `true` if called by a "full" set, i.e., a set containing every element of type `A`.
    pub open spec fn is_full(self) -> bool {
        self == Set::<A>::full()
    }

    /// Is `true` if called by an "empty" set, i.e., a set containing no elements and has length 0
    pub open spec fn is_empty(self) -> (b: bool) {
        self.len() == 0
    }

    /// Returns the set contains an element `f(x)` for every element `x` in `self`.
    pub open spec fn map<B>(self, f: spec_fn(A) -> B) -> Set<B> {
        Set::new(|a: B| exists|x: A| self.contains(x) && a == f(x))
    }

    /// Folds the set, applying `f` to perform the fold. The next element for the fold is chosen by
    /// the choose operator.
    ///
    /// Given a set `s = {x0, x1, x2, ..., xn}`, applying this function `s.fold(init, f)`
    /// returns `f(...f(f(init, x0), x1), ..., xn)`.
    pub open spec fn fold<E>(self, init: E, f: spec_fn(E, A) -> E) -> E
        decreases self.len(),
    {
        if self.finite() {
            if self.len() == 0 {
                init
            } else {
                let a = self.choose();
                self.remove(a).fold(f(init, a), f)
            }
        } else {
            arbitrary()
        }
    }

    /// Converts a set into a sequence with an arbitrary ordering.
    pub open spec fn to_seq(self) -> Seq<A>
        recommends
            self.finite(),
        decreases self.len(),
        when self.finite()
        via Self::decreases_proof
    {
        if self.len() == 0 {
            Seq::<A>::empty()
        } else {
            let x = self.choose();
            Seq::<A>::empty().push(x) + self.remove(x).to_seq()
        }
    }

    // Helper function to prove termination of function to_seq
    #[via_fn]
    proof fn decreases_proof(self) {
        lemma_set_properties::<A>();
        if self.len() > 0 {
            let x = self.choose();
            assert(self.contains(x));
            assert(self.remove(x).len() < self.len());
        }
    }

    /// Converts a set into a sequence sorted by the given ordering function `leq`
    pub open spec fn to_sorted_seq(self, leq: spec_fn(A, A) -> bool) -> Seq<A> {
        self.to_seq().sort_by(leq)
    }

    /// A singleton set has at least one element and any two elements are equal.
    pub open spec fn is_singleton(self) -> bool {
        &&& self.len() > 0
        &&& (forall|x: A, y: A| self.contains(x) && self.contains(y) ==> x == y)
    }

    /// Any totally-ordered set contains a unique minimal (equivalently, least) element.
    /// Returns an arbitrary value if r is not a total ordering
    pub closed spec fn find_unique_minimal(self, r: spec_fn(A, A) -> bool) -> A
        recommends
            total_ordering(r),
            self.len() > 0,
            self.finite(),
        decreases self.len(),
        when self.finite()
        via Self::prove_decrease_min_unique
    {
        if self.len() <= 1 {
            self.choose()
        } else {
            let x = choose|x: A| self.contains(x);
            let min = self.remove(x).find_unique_minimal(r);
            if r(min, x) {
                min
            } else {
                x
            }
        }
    }

    #[via_fn]
    proof fn prove_decrease_min_unique(self, r: spec_fn(A, A) -> bool) {
        lemma_set_properties::<A>();
        if self.len() > 0 {
            let x = self.choose();
            assert(self.contains(x));
            assert(self.remove(x).len() < self.len());
        }
    }

    /// Proof of correctness and expected behavior for `Set::find_unique_minimal`.
    pub proof fn find_unique_minimal_ensures(self, r: spec_fn(A, A) -> bool)
        requires
            self.finite(),
            self.len() > 0,
            total_ordering(r),
        ensures
            is_minimal(r, self.find_unique_minimal(r), self) && (forall|min: A|
                is_minimal(r, min, self) ==> self.find_unique_minimal(r) == min),
        decreases self.len(),
    {
        lemma_set_properties::<A>();
        if self.len() == 1 {
            let x = choose|x: A| self.contains(x);
            assert(self.remove(x).insert(x) =~= self);
            assert(is_minimal(r, self.find_unique_minimal(r), self));
        } else {
            let x = choose|x: A| self.contains(x);
            self.remove(x).find_unique_minimal_ensures(r);
            assert(is_minimal(r, self.remove(x).find_unique_minimal(r), self.remove(x)));
            let y = self.remove(x).find_unique_minimal(r);
            let min_updated = self.find_unique_minimal(r);
            assert(!r(y, x) ==> min_updated == x);
            assert(forall|elt: A|
                self.remove(x).contains(elt) && #[trigger] r(elt, y) ==> #[trigger] r(y, elt));
            assert forall|elt: A|
                self.contains(elt) && #[trigger] r(elt, min_updated) implies #[trigger] r(
                min_updated,
                elt,
            ) by {
                assert(r(min_updated, x) || r(min_updated, y));
                if min_updated == y {  // Case where the new min is the old min
                    assert(is_minimal(r, self.find_unique_minimal(r), self));
                } else {  //Case where the new min is the newest element
                    assert(self.remove(x).contains(elt) || elt == x);
                    assert(min_updated == x);
                    assert(r(x, y) || r(y, x));
                    assert(!r(x, y) || !r(y, x));
                    assert(!(min_updated == y) ==> !r(y, x));
                    assert(r(x, y));
                    if (self.remove(x).contains(elt)) {
                        assert(r(elt, y) && r(y, elt) ==> elt == y);
                    } else {
                    }
                }
            }
            assert forall|min_poss: A|
                is_minimal(r, min_poss, self) implies self.find_unique_minimal(r) == min_poss by {
                assert(is_minimal(r, min_poss, self.remove(x)) || x == min_poss);
                assert(r(min_poss, self.find_unique_minimal(r)));
            }
        }
    }

    /// Any totally-ordered set contains a unique maximal (equivalently, greatest) element.
    /// Returns an arbitrary value if r is not a total ordering
    pub closed spec fn find_unique_maximal(self, r: spec_fn(A, A) -> bool) -> A
        recommends
            total_ordering(r),
            self.len() > 0,
        decreases self.len(),
        when self.finite()
        via Self::prove_decrease_max_unique
    {
        if self.len() <= 1 {
            self.choose()
        } else {
            let x = choose|x: A| self.contains(x);
            let max = self.remove(x).find_unique_maximal(r);
            if r(x, max) {
                max
            } else {
                x
            }
        }
    }

    #[via_fn]
    proof fn prove_decrease_max_unique(self, r: spec_fn(A, A) -> bool) {
        lemma_set_properties::<A>();
    }

    /// Proof of correctness and expected behavior for `Set::find_unique_maximal`.
    pub proof fn find_unique_maximal_ensures(self, r: spec_fn(A, A) -> bool)
        requires
            self.finite(),
            self.len() > 0,
            total_ordering(r),
        ensures
            is_maximal(r, self.find_unique_maximal(r), self) && (forall|max: A|
                is_maximal(r, max, self) ==> self.find_unique_maximal(r) == max),
        decreases self.len(),
    {
        lemma_set_properties::<A>();
        if self.len() == 1 {
            let x = choose|x: A| self.contains(x);
            assert(self.remove(x) =~= Set::<A>::empty());
            assert(self.contains(self.find_unique_maximal(r)));
        } else {
            let x = choose|x: A| self.contains(x);
            self.remove(x).find_unique_maximal_ensures(r);
            assert(is_maximal(r, self.remove(x).find_unique_maximal(r), self.remove(x)));
            assert(self.remove(x).insert(x) =~= self);
            let y = self.remove(x).find_unique_maximal(r);
            let max_updated = self.find_unique_maximal(r);
            assert(max_updated == x || max_updated == y);
            assert(!r(x, y) ==> max_updated == x);
            assert forall|elt: A|
                self.contains(elt) && #[trigger] r(max_updated, elt) implies #[trigger] r(
                elt,
                max_updated,
            ) by {
                assert(r(x, max_updated) || r(y, max_updated));
                if max_updated == y {  // Case where the new max is the old max
                    assert(r(elt, max_updated));
                    assert(r(x, max_updated));
                    assert(is_maximal(r, self.find_unique_maximal(r), self));
                } else {  //Case where the new max is the newest element
                    assert(self.remove(x).contains(elt) || elt == x);
                    assert(max_updated == x);
                    assert(r(x, y) || r(y, x));
                    assert(!r(x, y) || !r(y, x));
                    assert(!(max_updated == y) ==> !r(x, y));
                    assert(r(y, x));
                    if (self.remove(x).contains(elt)) {
                        assert(r(y, elt) ==> r(elt, y));
                        assert(r(y, elt) && r(elt, y) ==> elt == y);
                        assert(r(elt, x));
                        assert(r(elt, max_updated))
                    } else {
                    }
                }
            }
            assert forall|max_poss: A|
                is_maximal(r, max_poss, self) implies self.find_unique_maximal(r) == max_poss by {
                assert(is_maximal(r, max_poss, self.remove(x)) || x == max_poss);
                assert(r(max_poss, self.find_unique_maximal(r)));
                assert(r(self.find_unique_maximal(r), max_poss));
            }
        }
    }

    /// Converts a set into a multiset where each element from the set has
    /// multiplicity 1 and any other element has multiplicity 0.
    pub open spec fn to_multiset(self) -> Multiset<A>
        decreases self.len(),
        when self.finite()
    {
        if self.len() == 0 {
            Multiset::<A>::empty()
        } else {
            Multiset::<A>::empty().insert(self.choose()).add(
                self.remove(self.choose()).to_multiset(),
            )
        }
    }

    /// A finite set with length 0 is equivalent to the empty set.
    pub proof fn lemma_len0_is_empty(self)
        requires
            self.finite(),
            self.len() == 0,
        ensures
            self == Set::<A>::empty(),
    {
        if exists|a: A| self.contains(a) {
            // derive contradiction:
            assert(self.remove(self.choose()).len() + 1 == 0);
        }
        assert(self =~= Set::empty());
    }

    /// A singleton set has length 1.
    pub proof fn lemma_singleton_size(self)
        requires
            self.is_singleton(),
        ensures
            self.len() == 1,
    {
        lemma_set_properties::<A>();
        assert(self.remove(self.choose()) =~= Set::empty());
    }

    /// A set has exactly one element, if and only if, it has at least one element and any two elements are equal.
    pub proof fn lemma_is_singleton(s: Set<A>)
        requires
            s.finite(),
        ensures
            s.is_singleton() == (s.len() == 1),
    {
        if s.is_singleton() {
            s.lemma_singleton_size();
        }
        if s.len() == 1 {
            assert forall|x: A, y: A| s.contains(x) && s.contains(y) implies x == y by {
                let x = choose|x: A| s.contains(x);
                lemma_set_properties::<A>();
                assert(s.remove(x).len() == 0);
                assert(s.insert(x) =~= s);
            }
        }
    }

    /// The result of filtering a finite set is finite and has size less than or equal to the original set.
    pub proof fn lemma_len_filter(self, f: spec_fn(A) -> bool)
        requires
            self.finite(),
        ensures
            self.filter(f).finite(),
            self.filter(f).len() <= self.len(),
        decreases self.len(),
    {
        lemma_len_intersect::<A>(self, Set::new(f));
    }

    /// In a pre-ordered set, a greatest element is necessarily maximal.
    pub proof fn lemma_greatest_implies_maximal(self, r: spec_fn(A, A) -> bool, max: A)
        requires
            pre_ordering(r),
        ensures
            is_greatest(r, max, self) ==> is_maximal(r, max, self),
    {
    }

    /// In a pre-ordered set, a least element is necessarily minimal.
    pub proof fn lemma_least_implies_minimal(self, r: spec_fn(A, A) -> bool, min: A)
        requires
            pre_ordering(r),
        ensures
            is_least(r, min, self) ==> is_minimal(r, min, self),
    {
    }

    /// In a totally-ordered set, an element is maximal if and only if it is a greatest element.
    pub proof fn lemma_maximal_equivalent_greatest(self, r: spec_fn(A, A) -> bool, max: A)
        requires
            total_ordering(r),
        ensures
            is_greatest(r, max, self) <==> is_maximal(r, max, self),
    {
        assert(is_maximal(r, max, self) ==> forall|x: A|
            !self.contains(x) || !r(max, x) || r(x, max));
    }

    /// In a totally-ordered set, an element is maximal if and only if it is a greatest element.
    pub proof fn lemma_minimal_equivalent_least(self, r: spec_fn(A, A) -> bool, min: A)
        requires
            total_ordering(r),
        ensures
            is_least(r, min, self) <==> is_minimal(r, min, self),
    {
        assert(is_minimal(r, min, self) ==> forall|x: A|
            !self.contains(x) || !r(x, min) || r(min, x));
    }

    /// In a partially-ordered set, there exists at most one least element.
    pub proof fn lemma_least_is_unique(self, r: spec_fn(A, A) -> bool)
        requires
            partial_ordering(r),
        ensures
            forall|min: A, min_prime: A|
                is_least(r, min, self) && is_least(r, min_prime, self) ==> min == min_prime,
    {
        assert forall|min: A, min_prime: A|
            is_least(r, min, self) && is_least(r, min_prime, self) implies min == min_prime by {
            assert(r(min, min_prime));
            assert(r(min_prime, min));
        }
    }

    /// In a partially-ordered set, there exists at most one greatest element.
    pub proof fn lemma_greatest_is_unique(self, r: spec_fn(A, A) -> bool)
        requires
            partial_ordering(r),
        ensures
            forall|max: A, max_prime: A|
                is_greatest(r, max, self) && is_greatest(r, max_prime, self) ==> max == max_prime,
    {
        assert forall|max: A, max_prime: A|
            is_greatest(r, max, self) && is_greatest(r, max_prime, self) implies max
            == max_prime by {
            assert(r(max_prime, max));
            assert(r(max, max_prime));
        }
    }

    /// In a totally-ordered set, there exists at most one minimal element.
    pub proof fn lemma_minimal_is_unique(self, r: spec_fn(A, A) -> bool)
        requires
            total_ordering(r),
        ensures
            forall|min: A, min_prime: A|
                is_minimal(r, min, self) && is_minimal(r, min_prime, self) ==> min == min_prime,
    {
        assert forall|min: A, min_prime: A|
            is_minimal(r, min, self) && is_minimal(r, min_prime, self) implies min == min_prime by {
            self.lemma_minimal_equivalent_least(r, min);
            self.lemma_minimal_equivalent_least(r, min_prime);
            self.lemma_least_is_unique(r);
        }
    }

    /// In a totally-ordered set, there exists at most one maximal element.
    pub proof fn lemma_maximal_is_unique(self, r: spec_fn(A, A) -> bool)
        requires
            self.finite(),
            total_ordering(r),
        ensures
            forall|max: A, max_prime: A|
                is_maximal(r, max, self) && is_maximal(r, max_prime, self) ==> max == max_prime,
    {
        assert forall|max: A, max_prime: A|
            is_maximal(r, max, self) && is_maximal(r, max_prime, self) implies max == max_prime by {
            self.lemma_maximal_equivalent_greatest(r, max);
            self.lemma_maximal_equivalent_greatest(r, max_prime);
            self.lemma_greatest_is_unique(r);
        }
    }
}

/// The size of a union of two sets is less than or equal to the size of
/// both individual sets combined.
pub proof fn lemma_len_union<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        s1.union(s2).len() <= s1.len() + s2.len(),
    decreases s1.len(),
{
    if s1.is_empty() {
        assert(s1.union(s2) =~= s2);
    } else {
        let a = s1.choose();
        if s2.contains(a) {
            assert(s1.union(s2) =~= s1.remove(a).union(s2));
        } else {
            assert(s1.union(s2).remove(a) =~= s1.remove(a).union(s2));
        }
        lemma_len_union::<A>(s1.remove(a), s2);
    }
}

/// The size of a union of two sets is greater than or equal to the size of
/// both individual sets.
pub proof fn lemma_len_union_ind<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        s1.union(s2).len() >= s1.len(),
        s1.union(s2).len() >= s2.len(),
    decreases s2.len(),
{
    lemma_set_properties::<A>();
    if s2.len() == 0 {
    } else {
        let y = choose|y: A| s2.contains(y);
        if s1.contains(y) {
            assert(s1.remove(y).union(s2.remove(y)) =~= s1.union(s2).remove(y));
            lemma_len_union_ind(s1.remove(y), s2.remove(y))
        } else {
            assert(s1.union(s2.remove(y)) =~= s1.union(s2).remove(y));
            lemma_len_union_ind(s1, s2.remove(y))
        }
    }
}

/// The size of the intersection of finite set `s1` and set `s2` is less than or equal to the size of `s1`.
pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases s1.len(),
{
    if s1.is_empty() {
        assert(s1.intersect(s2) =~= s1);
    } else {
        let a = s1.choose();
        assert(s1.intersect(s2).remove(a) =~= s1.remove(a).intersect(s2));
        lemma_len_intersect::<A>(s1.remove(a), s2);
    }
}

/// If `s1` is a subset of finite set `s2`, then the size of `s1` is less than or equal to
/// the size of `s2` and `s1` must be finite.
pub proof fn lemma_len_subset<A>(s1: Set<A>, s2: Set<A>)
    requires
        s2.finite(),
        s1.subset_of(s2),
    ensures
        s1.len() <= s2.len(),
        s1.finite(),
{
    lemma_len_intersect::<A>(s2, s1);
    assert(s2.intersect(s1) =~= s1);
}

/// The size of the difference of finite set `s1` and set `s2` is less than or equal to the size of `s1`.
pub proof fn lemma_len_difference<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.difference(s2).len() <= s1.len(),
    decreases s1.len(),
{
    if s1.is_empty() {
        assert(s1.difference(s2) =~= s1);
    } else {
        let a = s1.choose();
        assert(s1.difference(s2).remove(a) =~= s1.remove(a).difference(s2));
        lemma_len_difference::<A>(s1.remove(a), s2);
    }
}

/// Creates a finite set of integers in the range [lo, hi).
pub open spec fn set_int_range(lo: int, hi: int) -> Set<int> {
    Set::new(|i: int| lo <= i && i < hi)
}

/// If a set solely contains integers in the range [a, b), then its size is
/// bounded by b - a.
pub proof fn lemma_int_range(lo: int, hi: int)
    requires
        lo <= hi,
    ensures
        set_int_range(lo, hi).finite(),
        set_int_range(lo, hi).len() == hi - lo,
    decreases hi - lo,
{
    if lo == hi {
        assert(set_int_range(lo, hi) =~= Set::empty());
    } else {
        lemma_int_range(lo, hi - 1);
        assert(set_int_range(lo, hi - 1).insert(hi - 1) =~= set_int_range(lo, hi));
    }
}

/// If x is a subset of y and the size of x is equal to the size of y, x is equal to y.
pub proof fn lemma_subset_equality<A>(x: Set<A>, y: Set<A>)
    requires
        x.subset_of(y),
        x.finite(),
        y.finite(),
        x.len() == y.len(),
    ensures
        x =~= y,
    decreases x.len(),
{
    lemma_set_properties::<A>();
    if x =~= Set::<A>::empty() {
    } else {
        let e = x.choose();
        lemma_subset_equality(x.remove(e), y.remove(e));
    }
}

/// If an injective function is applied to each element of a set to construct
/// another set, the two sets have the same size.
// the dafny original lemma reasons with partial function f
pub proof fn lemma_map_size<A, B>(x: Set<A>, y: Set<B>, f: spec_fn(A) -> B)
    requires
        injective(f),
        forall|a: A| x.contains(a) ==> y.contains(#[trigger] f(a)),
        forall|b: B| (#[trigger] y.contains(b)) ==> exists|a: A| x.contains(a) && f(a) == b,
        x.finite(),
        y.finite(),
    ensures
        x.len() == y.len(),
    decreases x.len(),
{
    lemma_set_properties::<A>();
    lemma_set_properties::<B>();
    if x.len() != 0 {
        let a = x.choose();
        lemma_map_size(x.remove(a), y.remove(f(a)), f);
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the union of sets `a` and `b` and then taking the union of the result with `b`
/// is the same as taking the union of `a` and `b` once.
pub proof fn lemma_set_union_again1<A>(a: Set<A>, b: Set<A>)
    ensures
        a.union(b).union(b) =~= a.union(b),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the union of sets `a` and `b` and then taking the union of the result with `a`
/// is the same as taking the union of `a` and `b` once.
pub proof fn lemma_set_union_again2<A>(a: Set<A>, b: Set<A>)
    ensures
        a.union(b).union(a) =~= a.union(b),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the intersection of sets `a` and `b` and then taking the intersection of the result with `b`
/// is the same as taking the intersection of `a` and `b` once.
pub proof fn lemma_set_intersect_again1<A>(a: Set<A>, b: Set<A>)
    ensures
        (a.intersect(b)).intersect(b) =~= a.intersect(b),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the intersection of sets `a` and `b` and then taking the intersection of the result with `a`
/// is the same as taking the intersection of `a` and `b` once.
pub proof fn lemma_set_intersect_again2<A>(a: Set<A>, b: Set<A>)
    ensures
        (a.intersect(b)).intersect(a) =~= a.intersect(b),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If set `s2` contains element `a`, then the set difference of `s1` and `s2` does not contain `a`.
pub proof fn lemma_set_difference2<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        s2.contains(a) ==> !s1.difference(s2).contains(a),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If sets `a` and `b` are disjoint, meaning they have no elements in common, then the set difference
/// of `a + b` and `b` is equal to `a` and the set difference of `a + b` and `a` is equal to `b`.
pub proof fn lemma_set_disjoint<A>(a: Set<A>, b: Set<A>)
    ensures
        a.disjoint(b) ==> ((a + b).difference(a) =~= b && (a + b).difference(b) =~= a),
{
}

// Dafny encodes the second clause with a single directional, although
// it should be fine with both directions?
// This verified lemma used to be an axiom in the Dafny prelude
/// Set `s` has length 0 if and only if it is equal to the empty set. If `s` has length greater than 0,
/// Then there must exist an element `x` such that `s` contains `x`.
pub proof fn lemma_set_empty_equivalency_len<A>(s: Set<A>)
    requires
        s.finite(),
    ensures
        (s.len() == 0 <==> s == Set::<A>::empty()) && (s.len() != 0 ==> exists|x: A| s.contains(x)),
{
    assert(s.len() == 0 ==> s =~= Set::empty()) by {
        if s.len() == 0 {
            assert(forall|a: A| !(Set::empty().contains(a)));
            assert(Set::<A>::empty().len() == 0);
            assert(Set::<A>::empty().len() == s.len());
            assert((exists|a: A| s.contains(a)) || (forall|a: A| !s.contains(a)));
            if exists|a: A| s.contains(a) {
                let a = s.choose();
                assert(s.remove(a).len() == s.len() - 1) by {
                    axiom_set_remove_len(s, a);
                }
            }
        }
    }
    assert(s.len() == 0 <== s =~= Set::empty());
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If sets `a` and `b` are disjoint, meaning they share no elements in common, then the length
/// of the union `a + b` is equal to the sum of the lengths of `a` and `b`.
pub proof fn lemma_set_disjoint_lens<A>(a: Set<A>, b: Set<A>)
    requires
        a.finite(),
        b.finite(),
    ensures
        a.disjoint(b) ==> (a + b).len() == a.len() + b.len(),
    decreases a.len(),
{
    if a.len() == 0 {
        lemma_set_empty_equivalency_len(a);
        assert(a + b =~= b);
    } else {
        if a.disjoint(b) {
            let x = a.choose();
            assert(a.remove(x) + b =~= (a + b).remove(x));
            lemma_set_disjoint_lens(a.remove(x), b);
        }
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The length of the union between two sets added to the length of the intersection between the
/// two sets is equal to the sum of the lengths of the two sets.
pub proof fn lemma_set_intersect_union_lens<A>(a: Set<A>, b: Set<A>)
    requires
        a.finite(),
        b.finite(),
    ensures
        (a + b).len() + a.intersect(b).len() == a.len() + b.len(),
    decreases a.len(),
{
    if a.len() == 0 {
        lemma_set_empty_equivalency_len(a);
        assert(a + b =~= b);
        assert(a.intersect(b) =~= Set::empty());
        assert(a.intersect(b).len() == 0);
    } else {
        let x = a.choose();
        lemma_set_intersect_union_lens(a.remove(x), b);
        if (b.contains(x)) {
            assert(a.remove(x) + b =~= (a + b));
            assert(a.intersect(b).remove(x) =~= a.remove(x).intersect(b));
        } else {
            assert(a.remove(x) + b =~= (a + b).remove(x));
            assert(a.remove(x).intersect(b) =~= a.intersect(b));
        }
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The length of the set difference `A \ B` added to the length of the set difference `B \ A` added to
/// the length of the intersection `A ∩ B` is equal to the length of the union `A + B`.
///
/// The length of the set difference `A \ B` is equal to the length of `A` minus the length of the
/// intersection `A ∩ B`.
pub proof fn lemma_set_difference_len<A>(a: Set<A>, b: Set<A>)
    requires
        a.finite(),
        b.finite(),
    ensures
        (a.difference(b).len() + b.difference(a).len() + a.intersect(b).len() == (a + b).len()) && (
        a.difference(b).len() == a.len() - a.intersect(b).len()),
    decreases a.len(),
{
    if a.len() == 0 {
        lemma_set_empty_equivalency_len(a);
        assert(a.difference(b) =~= Set::empty());
        assert(b.difference(a) =~= b);
        assert(a.intersect(b) =~= Set::empty());
        assert(a + b =~= b);
    } else {
        let x = a.choose();
        lemma_set_difference_len(a.remove(x), b);
        if b.contains(x) {
            assert(a.intersect(b).remove(x) =~= a.remove(x).intersect(b));
            assert(a.remove(x).difference(b) =~= a.difference(b));
            assert(b.difference(a.remove(x)).remove(x) =~= b.difference(a));
            assert(a.remove(x) + b =~= a + b);
        } else {
            assert(a.remove(x) + b =~= (a + b).remove(x));
            assert(a.remove(x).difference(b) =~= a.difference(b).remove(x));
            assert(b.difference(a.remove(x)) =~= b.difference(a));
            assert(a.remove(x).intersect(b) =~= a.intersect(b));
        }
    }
}

/// Properties of sets from the Dafny prelude (which were axioms in Dafny, but proven here in Verus)
pub proof fn lemma_set_properties<A>()
    ensures
        forall|a: Set<A>, b: Set<A>| #[trigger] a.union(b).union(b) == a.union(b),  //from lemma_set_union_again1
        forall|a: Set<A>, b: Set<A>| #[trigger] a.union(b).union(a) == a.union(b),  //from lemma_set_union_again2
        forall|a: Set<A>, b: Set<A>| #[trigger] (a.intersect(b)).intersect(b) == a.intersect(b),  //from lemma_set_intersect_again1
        forall|a: Set<A>, b: Set<A>| #[trigger] (a.intersect(b)).intersect(a) == a.intersect(b),  //from lemma_set_intersect_again2
        forall|s1: Set<A>, s2: Set<A>, a: A| s2.contains(a) ==> !s1.difference(s2).contains(a),  //from lemma_set_difference2
        forall|a: Set<A>, b: Set<A>|
            a.disjoint(b) ==> ((#[trigger] (a + b)).difference(a) == b && (a + b).difference(b)
                == a),  //from lemma_set_disjoint
        forall|s: Set<A>| #[trigger] s.len() != 0 && s.finite() ==> exists|a: A| s.contains(a),
        forall|a: Set<A>, b: Set<A>|
            (a.finite() && b.finite() && a.disjoint(b)) ==> #[trigger] (a + b).len() == a.len()
                + b.len(),  //from lemma_set_disjoint_lens
        forall|a: Set<A>, b: Set<A>|
            (a.finite() && b.finite()) ==> #[trigger] (a + b).len() + #[trigger] a.intersect(
                b,
            ).len() == a.len() + b.len(),  //from lemma_set_intersect_union_lens
        forall|a: Set<A>, b: Set<A>|
            (a.finite() && b.finite()) ==> ((#[trigger] a.difference(b).len() + b.difference(
                a,
            ).len() + a.intersect(b).len() == (a + b).len()) && (a.difference(b).len() == a.len()
                - a.intersect(b).len())),  //from lemma_set_difference_len
{
    assert forall|a: Set<A>, b: Set<A>| #[trigger] a.union(b).union(b) == a.union(b) by {
        lemma_set_union_again1(a, b);
    }
    assert forall|a: Set<A>, b: Set<A>| #[trigger] a.union(b).union(a) == a.union(b) by {
        lemma_set_union_again2(a, b);
    }
    assert forall|a: Set<A>, b: Set<A>| #[trigger]
        (a.intersect(b)).intersect(b) == a.intersect(b) by {
        lemma_set_intersect_again1(a, b);
    }
    assert forall|a: Set<A>, b: Set<A>| #[trigger]
        (a.intersect(b)).intersect(a) == a.intersect(b) by {
        lemma_set_intersect_again2(a, b);
    }
    assert forall|a: Set<A>, b: Set<A>| a.disjoint(b) implies ((#[trigger] (a + b)).difference(a)
        == b && (a + b).difference(b) == a) by {
        lemma_set_disjoint(a, b);
    }
    assert forall|s: Set<A>| #[trigger] s.len() != 0 && s.finite() implies exists|a: A|
        s.contains(a) by {
        assert(s.contains(s.choose()));
    }
    assert forall|a: Set<A>, b: Set<A>|
        a.disjoint(b) && b.finite() && a.finite() implies #[trigger] (a + b).len() == a.len()
        + b.len() by {
        lemma_set_disjoint_lens(a, b);
    }
    assert forall|a: Set<A>, b: Set<A>| a.finite() && b.finite() implies #[trigger] (a + b).len()
        + #[trigger] a.intersect(b).len() == a.len() + b.len() by {
        lemma_set_intersect_union_lens(a, b);
    }
    assert forall|a: Set<A>, b: Set<A>|
        (a.finite() && b.finite()) ==> #[trigger] a.difference(b).len() + b.difference(a).len()
            + a.intersect(b).len() == (a + b).len() by {
        if a.finite() && b.finite() {
            lemma_set_difference_len(a, b);
        }
    }
    assert forall|a: Set<A>, b: Set<A>|
        (a.finite() && b.finite()) ==> #[trigger] a.difference(b).len() == a.len() - a.intersect(
            b,
        ).len() by {
        if a.finite() && b.finite() {
            lemma_set_difference_len(a, b);
        }
    }
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_is_empty<A>(s: Set<A>)
    requires
        s.finite(),
        !(#[trigger] s.is_empty()),
    ensures
        exists|a: A| s.contains(a),
{
}

#[doc(hidden)]
#[verifier(inline)]
pub open spec fn check_argument_is_set<A>(s: Set<A>) -> Set<A> {
    s
}

/// Prove two sets equal by extensionality. Usage is:
///
/// ```rust
/// assert_sets_equal!(set1 == set2);
/// ```
///
/// or,
///
/// ```rust
/// assert_sets_equal!(set1 == set2, elem => {
///     // prove that set1.contains(elem) iff set2.contains(elem)
/// });
/// ```
#[macro_export]
macro_rules! assert_sets_equal {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::set_lib::assert_sets_equal_internal!($($tail)*))
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! assert_sets_equal_internal {
    (::builtin::spec_eq($s1:expr, $s2:expr)) => {
        assert_sets_equal_internal!($s1, $s2)
    };
    (::builtin::spec_eq($s1:expr, $s2:expr), $elem:ident $( : $t:ty )? => $bblock:block) => {
        assert_sets_equal_internal!($s1, $s2, $elem $( : $t )? => $bblock)
    };
    ($s1:expr, $s2:expr $(,)?) => {
        assert_sets_equal_internal!($s1, $s2, elem => { })
    };
    ($s1:expr, $s2:expr, $elem:ident $( : $t:ty )? => $bblock:block) => {
        #[verifier::spec] let s1 = $crate::set_lib::check_argument_is_set($s1);
        #[verifier::spec] let s2 = $crate::set_lib::check_argument_is_set($s2);
        ::builtin::assert_by(::builtin::equal(s1, s2), {
            ::builtin::assert_forall_by(|$elem $( : $t )?| {
                ::builtin::ensures(
                    ::builtin::imply(s1.contains($elem), s2.contains($elem))
                    &&
                    ::builtin::imply(s2.contains($elem), s1.contains($elem))
                );
                { $bblock }
            });
            ::builtin::assert_(::builtin::ext_equal(s1, s2));
        });
    }
}

pub use assert_sets_equal_internal;
pub use assert_sets_equal;

} // verus!
}

pub mod slice {
    #![allow(unused_imports)]
    use crate::seq::*;
    use crate::view::*;
    use builtin::*;
    use builtin_macros::*;

    #[cfg(verus_keep_ghost)]
    #[cfg(feature = "alloc")]
    pub use super::std_specs::vec::VecAdditionalSpecFns;

    verus! {

pub trait SliceAdditionalSpecFns<T> {
    spec fn view(&self) -> Seq<T>;

    spec fn spec_index(&self, i: int) -> T
        recommends
            0 <= i < self.view().len(),
    ;
}

impl<T> SliceAdditionalSpecFns<T> for [T] {
    spec fn view(&self) -> Seq<T>;

    #[verifier(inline)]
    open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
}

#[verifier(external_body)]
pub exec fn slice_index_get<T>(slice: &[T], i: usize) -> (out: &T)
    requires
        0 <= i < slice.view().len(),
    ensures
        *out == slice@.index(i as int),
{
    &slice[i]
}

#[cfg(feature = "alloc")]
#[verifier(external_body)]
pub exec fn slice_to_vec<T: Copy>(slice: &[T]) -> (out: alloc::vec::Vec<T>)
    ensures
        out@ == slice@,
{
    slice.to_vec()
}

#[verifier(external_body)]
pub exec fn slice_subrange<T, 'a>(slice: &'a [T], i: usize, j: usize) -> (out: &'a [T])
    requires
        0 <= i <= j <= slice@.len(),
    ensures
        out@ == slice@.subrange(i as int, j as int),
{
    &slice[i..j]
}

#[verifier(external_fn_specification)]
pub exec fn slice_len<T>(slice: &[T]) -> (length: usize)
    ensures
        length >= 0,
        length == slice@.len(),
{
    slice.len()
}

} // verus!
}

pub mod state_machine_internal {
    //! Helper utilities used by the `state_machine_macros` codegen.
    #![allow(unused_imports)]
    #![doc(hidden)]

    use crate::map::*;
    use crate::pervasive::*;
    use crate::prelude::*;
    use crate::seq::*;
    use builtin::*;
    use builtin_macros::*;

    #[cfg_attr(verus_keep_ghost, verifier::external_body)] /* vattr */
    #[cfg_attr(verus_keep_ghost, verifier::accept_recursive_types(T))]
    pub struct SyncSendIfSyncSend<T> {
        _sync_send: builtin::SyncSendIfSyncSend<T>,
    }

    #[cfg_attr(verus_keep_ghost, verifier::external_body)] /* vattr */
    pub struct NoCopy {
        _no_copy: builtin::NoCopy,
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove assertion safety condition")] /* vattr */
    pub fn assert_safety(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove safety condition that the pattern matches")] /* vattr */
    pub fn assert_let_pattern(b: bool) {
        requires(b);
        ensures(b);
    }

    // SpecialOps

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: to add a value Some(_), field must be None before the update")] /* vattr */
    pub fn assert_add_option(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: to add a singleton set, the value must not be in the set before the update")] /* vattr */
    pub fn assert_add_set(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: to add a value `true`, field must be `false` before the update")] /* vattr */
    pub fn assert_add_bool(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: the given key must be absent from the map before the update")] /* vattr */
    pub fn assert_add_map(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: if the key is already in the map, its existing value must agree with the provided value")] /* vattr */
    pub fn assert_add_persistent_map(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: if the previous value is Some(_), then this existing value must agree with the newly provided value")] /* vattr */
    pub fn assert_add_persistent_option(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: the given value to be withdrawn must be stored before the withdraw")] /* vattr */
    pub fn assert_withdraw_option(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: to deposit a value into Some(_), the field must be None before the deposit")] /* vattr */
    pub fn assert_deposit_option(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err(
        "unable to prove inherent safety condition: the value being guarded must be stored"
    )] /* vattr */
    pub fn assert_guard_option(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: the value to be withdrawn must be stored at the given key before the withdraw")] /* vattr */
    pub fn assert_withdraw_map(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: the given key must be absent from the map before the deposit")] /* vattr */
    pub fn assert_deposit_map(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: the value being guarded must be stored at the given key")] /* vattr */
    pub fn assert_guard_map(b: bool) {
        requires(b);
        ensures(b);
    }

    // SpecialOps (with general element)

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: the optional values being composed cannot both be Some(_)")] /* vattr */
    pub fn assert_general_add_option(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err(
        "unable to prove inherent safety condition: the sets being composed must be disjoint"
    )] /* vattr */
    pub fn assert_general_add_set(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: the boolean values being composed cannot both be `true`")] /* vattr */
    pub fn assert_general_add_bool(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: the key domains of the maps being composed must be disjoint")] /* vattr */
    pub fn assert_general_add_map(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: the maps being composed must agree on their values for any key in both domains")] /* vattr */
    pub fn assert_general_add_persistent_map(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: if the previous value and the newly added values are both Some(_), then their values must agree")] /* vattr */
    pub fn assert_general_add_persistent_option(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: the optional value to be withdrawn must be stored before the withdraw")] /* vattr */
    pub fn assert_general_withdraw_option(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: the optional values being composed cannot both be Some(_)")] /* vattr */
    pub fn assert_general_deposit_option(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err(
        "unable to prove inherent safety condition: the value being guarded must be stored"
    )] /* vattr */
    pub fn assert_general_guard_option(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: the map being withdrawn must be a submap of the stored map")] /* vattr */
    pub fn assert_general_withdraw_map(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: the key domains of the maps being composed must be disjoint")] /* vattr */
    pub fn assert_general_deposit_map(b: bool) {
        requires(b);
        ensures(b);
    }

    #[cfg(verus_keep_ghost)]
    #[verifier::proof]
    #[verifier::custom_req_err("unable to prove inherent safety condition: the map being guarded must be a submap of the stored map")] /* vattr */
    pub fn assert_general_guard_map(b: bool) {
        requires(b);
        ensures(b);
    }

    // used by the `update field[idx] = ...;` syntax
    //
    // note: the built-in rust trait IndexMut doesn't work here
    // (because these functions need to be 'spec' code, and IndexMut uses a &mut to do its job)
    // perhaps we'll make our own trait for this purpose some day, but regardless, this suffices
    // for our purposes

    verus! {

#[doc(hidden)]
pub open spec fn nat_max(a: nat, b: nat) -> nat {
    if a > b {
        a
    } else {
        b
    }
}

#[doc(hidden)]
impl<A> Seq<A> {
    #[verifier::inline]
    pub open spec fn update_at_index(self, i: int, a: A) -> Self
        recommends
            0 <= i < self.len(),
    {
        self.update(i, a)
    }
}

#[doc(hidden)]
impl<K, V> Map<K, V> {
    // note that despite the name, this is allowed to insert
    #[verifier::inline]
    pub open spec fn update_at_index(self, k: K, v: V) -> Self {
        self.insert(k, v)
    }
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn opt_is_none<V>(a: Option<V>) -> bool {
    a.is_None()
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn opt_ge<V>(a: Option<V>, b: Option<V>) -> bool {
    b.is_Some() ==> a === b
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn opt_add<V>(a: Option<V>, b: Option<V>) -> Option<V> {
    if b.is_Some() {
        b
    } else {
        a
    }
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn opt_agree<V>(a: Option<V>, b: Option<V>) -> bool {
    a.is_Some() && b.is_Some() ==> a.get_Some_0() === b.get_Some_0()
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn opt_sub<V>(a: Option<V>, b: Option<V>) -> Option<V> {
    if b.is_Some() {
        Option::None
    } else {
        a
    }
}

} // verus!
}

pub mod string {
    #![feature(rustc_attrs)]
    #![allow(unused_imports)]

    #[cfg(feature = "alloc")]
    use alloc::string::{self, ToString};

    use super::seq::Seq;
    use crate::prelude::*;
    use crate::view::*;
    use builtin::*;
    use builtin_macros::verus;

    verus! {

#[cfg(feature = "alloc")]
#[cfg_attr(verus_keep_ghost, verifier::external_body)]
pub struct String {
    inner: string::String,
}

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::string::StrSlice")]
#[cfg_attr(verus_keep_ghost, verifier::external_body)]
pub struct StrSlice<'a> {
    inner: &'a str,
}

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::string::new_strlit")]
#[cfg_attr(verus_keep_ghost, verifier::external_body)]
pub const fn new_strlit<'a>(s: &'a str) -> StrSlice<'a> {
    StrSlice { inner: s }
}

impl<'a> StrSlice<'a> {
    pub spec fn view(&self) -> Seq<char>;

    pub spec fn is_ascii(&self) -> bool;

    /// The len() function in rust returns the byte length.
    /// It is more useful to talk about the length of characters and therefore this function was added.
    /// Please note that this function counts the unicode variation selectors as characters.
    /// Warning: O(n)
    #[verifier(external_body)]
    pub fn unicode_len(&self) -> (l: usize)
        ensures
            l as nat == self@.len(),
    {
        self.inner.chars().count()
    }

    /// Warning: O(n) not O(1) due to unicode decoding needed
    #[verifier(external_body)]
    pub fn get_char(&self, i: usize) -> (c: char)
        requires
            i < self@.len(),
        ensures
            self@.index(i as int) == c,
            self.is_ascii() ==> forall|i: int| i < self@.len() ==> (self@.index(i) as nat) < 256,
    {
        self.inner.chars().nth(i).unwrap()
    }

    #[verifier(external_body)]
    pub fn substring_ascii(&self, from: usize, to: usize) -> (ret: StrSlice<'a>)
        requires
            self.is_ascii(),
            from < self@.len(),
            to <= self@.len(),
        ensures
            ret@ == self@.subrange(from as int, to as int),
            ret.is_ascii() == self.is_ascii(),
    {
        StrSlice { inner: &self.inner[from..to] }
    }

    #[verifier(external_body)]
    pub fn substring_char(&self, from: usize, to: usize) -> (ret: StrSlice<'a>)
        requires
            from < self@.len(),
            to <= self@.len(),
        ensures
            ret@ == self@.subrange(from as int, to as int),
            ret.is_ascii() == self.is_ascii(),
    {
        let mut char_pos = 0;
        let mut byte_start = None;
        let mut byte_end = None;
        let mut byte_pos = 0;
        let mut it = self.inner.chars();
        loop {
            if char_pos == from {
                byte_start = Some(byte_pos);
            }
            if char_pos == to {
                byte_end = Some(byte_pos);
                break ;
            }
            if let Some(c) = it.next() {
                char_pos += 1;
                byte_pos += c.len_utf8();
            } else {
                break ;
            }
        }
        let byte_start = byte_start.unwrap();
        let byte_end = byte_end.unwrap();
        StrSlice { inner: &self.inner[byte_start..byte_end] }
    }

    #[cfg(feature = "alloc")]
    pub fn to_string(self) -> (ret: String)
        ensures
            self@ == ret@,
            self.is_ascii() == ret.is_ascii(),
    {
        String::from_str(self)
    }

    #[verifier(external_body)]
    pub fn get_ascii(&self, i: usize) -> (b: u8)
        requires
            self.is_ascii(),
        ensures
            self.view().index(i as int) as u8 == b,
    {
        self.inner.as_bytes()[i]
    }

    // TODO:This should be the as_bytes function after
    // slice support is added
    // pub fn as_bytes<'a>(&'a [u8]) -> (ret: &'a [u8])
    #[cfg(feature = "alloc")]
    #[verifier(external_body)]
    pub fn as_bytes(&self) -> (ret: alloc::vec::Vec<u8>)
        requires
            self.is_ascii(),
        ensures
            ret.view() == Seq::new(self.view().len(), |i| self.view().index(i) as u8),
    {
        let mut v = alloc::vec::Vec::new();
        for c in self.inner.as_bytes().iter() {
            v.push(*c);
        }
        v
    }

    #[verifier(external)]
    pub fn from_rust_str(inner: &'a str) -> StrSlice<'a> {
        StrSlice { inner }
    }

    #[verifier(external)]
    pub fn into_rust_str(&'a self) -> &'a str {
        self.inner
    }
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_str_literal_is_ascii<'a>(s: StrSlice<'a>)
    ensures
        #[trigger] s.is_ascii() == builtin::strslice_is_ascii(s),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_str_literal_len<'a>(s: StrSlice<'a>)
    ensures
        #[trigger] s@.len() == builtin::strslice_len(s),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_str_literal_get_char<'a>(s: StrSlice<'a>, i: int)
    ensures
        #[trigger] s@.index(i) == builtin::strslice_get_char(s, i),
{
}

#[cfg(feature = "alloc")]
impl String {
    pub spec fn view(&self) -> Seq<char>;

    pub spec fn is_ascii(&self) -> bool;

    #[verifier(external_body)]
    pub fn from_str<'a>(s: StrSlice<'a>) -> (ret: String)
        ensures
            s@ == ret@,
            s.is_ascii() == ret.is_ascii(),
    {
        String { inner: s.inner.to_string() }
    }

    #[verifier(external_body)]
    pub fn as_str<'a>(&'a self) -> (ret: StrSlice<'a>)
        ensures
            self@ == ret@,
            self.is_ascii() == ret.is_ascii(),
    {
        let inner = self.inner.as_str();
        StrSlice { inner }
    }

    #[verifier(external_body)]
    pub fn append<'a, 'b>(&'a mut self, other: StrSlice<'b>)
        ensures
            self@ == old(self)@ + other@,
            self.is_ascii() == old(self).is_ascii() && other.is_ascii(),
    {
        self.inner += other.inner;
    }

    #[verifier(external_body)]
    pub fn concat<'b>(self, other: StrSlice<'b>) -> (ret: String)
        ensures
            ret@ == self@ + other@,
            ret.is_ascii() == self.is_ascii() && other.is_ascii(),
    {
        String { inner: self.inner + other.inner }
    }

    #[verifier(external_body)]
    pub fn eq(&self, other: &Self) -> (b: bool)
        ensures
            b == (self.view() == other.view()),
    {
        self.inner == other.inner
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (result: String)
        ensures
            result == self,
    {
        String { inner: self.inner.clone() }
    }

    #[verifier(external)]
    pub fn from_rust_string(inner: alloc::string::String) -> String {
        String { inner }
    }

    #[verifier(external)]
    pub fn into_rust_string(self) -> alloc::string::String {
        self.inner
    }

    #[verifier(external)]
    pub fn as_rust_string_ref(&self) -> &alloc::string::String {
        &self.inner
    }
}

} // verus!
}

#[cfg(feature = "std")]
pub mod thread {
    #![allow(unused_imports)]

    use crate::pervasive::*;
    use builtin::*;
    use builtin_macros::*;
    use core::marker;

    verus! {

/// Object returned by [`spawn()`](spawn) to allow thread joining.
/// (Wrapper around [`std::thread::JoinHandle`](https://doc.rust-lang.org/std/thread/struct.JoinHandle.html).)
///
/// See the documentation of [`spawn()`](spawn) for more details.
#[verifier(external_body)]
#[verifier::reject_recursive_types(Ret)]
pub struct JoinHandle<Ret> {
    handle: std::thread::JoinHandle<Ret>,
}

impl<Ret> JoinHandle<Ret> {
    /// Predicate restricting the possible return values. This is determined by the
    /// postcondition of the closure provided when calling `spawn()`.
    pub spec fn predicate(&self, ret: Ret) -> bool;

    /// Wait for a thread to complete.
    #[verifier(external_body)]
    pub fn join(self) -> (r_result: Result<Ret, ()>)
        ensures
            match r_result {
                Result::Ok(r) => self.predicate(r),
                Result::Err(_) => true,
            },
    {
        let res = std::panic::catch_unwind(
            std::panic::AssertUnwindSafe(
                ||
                    {
                        match self.handle.join() {
                            Ok(v) => Ok(v),
                            Err(_) => Err(()),
                        }
                    },
            ),
        );
        match res {
            Ok(res) => res,
            Err(_) => {
                println!("panic on join");
                std::process::abort();
            },
        }
    }
}

/// Spawns a thread. (Wrapper around [`std::thread::spawn`](https://doc.rust-lang.org/std/thread/fn.spawn.html).)
///
/// This takes as input a `FnOnce` closure with no arguments.
/// The `spawn` returns a [`JoinHandle`], on which the client can call
/// [`join()`](JoinHandle::join) to wait
/// for the thread to complete. The return value of the closure is returned via `join()`.
///
/// The closure must be callable (i.e., its precondition must be satisfied)
/// but it may have an arbitrary postcondition. The postcondition is passed through
/// the `JoinHandle` via [`JoinHandle::predicate()`](JoinHandle::predicate).
///
/// ### Example
///
/// ```rust,ignore
/// struct MyInteger {
///     u: u64,
/// }
///
/// fn main() {
///     // Construct an object to pass into the thread.
///     let my_int = MyInteger { u: 5 };
///
///     // Spawn a new thread.
///     let join_handle = spawn(move || {
///         ensures(|return_value: MyInteger|
///             return_value.u == 20);
///
///         // Move the `my_int` object into the closure.
///         let mut my_int_on_another_thread = my_int;
///
///         // Update its value.
///         my_int_on_another_thread.u = 20;
///
///         // Return it.
///         my_int_on_another_thread
///     });
///
///     // Wait for the thread to finish its work.
///     let result_my_int = join_handle.join();
///
///     match result_my_int {
///         Result::Ok(my_int) => {
///             // Obtain the `MyInteger` object that was passed
///             // back from the spawned thread.
///             // Assert that it has the right value.
///             assert(my_int.u == 20);
///         }
///         Result::Err(_) => { }
///     }
/// }
/// ```
#[verifier(external_body)]
pub fn spawn<F, Ret>(f: F) -> (handle: JoinHandle<Ret>) where
    F: FnOnce() -> Ret,
    F: Send + 'static,
    Ret: Send + 'static,

    requires
        f.requires(()),
    ensures
        forall|ret: Ret| #[trigger] handle.predicate(ret) ==> f.ensures((), ret),
{
    let res = std::panic::catch_unwind(
        std::panic::AssertUnwindSafe(
            ||
                {
                    let handle = std::thread::spawn(move || f());
                    JoinHandle { handle }
                },
        ),
    );
    match res {
        Ok(res) => res,
        Err(_) => {
            println!("panic on spawn");
            std::process::abort();
        },
    }
}

/// Wrapper around Rust's
/// [`ThreadId`](https://doc.rust-lang.org/std/thread/struct.ThreadId.html)
/// object. This is an opaque type.
// Note: Rust defines ThreadId as an opaque type. Rust guarantees that ThreadIds
// will never be reused. There's also an `as_u64()` method, but it's unstable,
// and right now it's not clear if it's going to have the same guarantee.
// Regardless, it seems best to stick with Rust's opaque type here.
#[verifier(external_body)]
pub struct ThreadId {
    thread_id: std::thread::ThreadId,
}

/// Proof object that guarantees the owning thread has the given ThreadId.
#[cfg(verus_keep_ghost)]
#[verifier(external_body)]
pub tracked struct IsThread {}

#[cfg(verus_keep_ghost)]
impl !Sync for IsThread {

}

#[cfg(verus_keep_ghost)]
impl !Send for IsThread {

}

// TODO: remove this when !Sync, !Send are supported by stable Rust
#[cfg(not(verus_keep_ghost))]
#[verifier(external_body)]
pub tracked struct IsThread {
    _no_send_sync: core::marker::PhantomData<*const ()>,
}

impl IsThread {
    pub spec fn view(&self) -> ThreadId;

    /// Guarantees that any two `IsThread` objects on the same thread
    /// will have the same ID.
    #[verifier(external_body)]
    pub proof fn agrees(tracked self, tracked other: IsThread)
        ensures
            self@ == other@,
    {
        unimplemented!();
    }
}

#[verifier(external)]
impl Clone for IsThread {
    #[cfg(verus_keep_ghost)]
    fn clone(&self) -> Self {
        IsThread {  }
    }

    #[cfg(not(verus_keep_ghost))]
    fn clone(&self) -> Self {
        IsThread { _no_send_sync: Default::default() }
    }
}

impl Copy for IsThread {

}

/// Gets the current thread ID using Rust's [`Thread::id()`](https://doc.rust-lang.org/std/thread/struct.Thread.html#method.id)
/// under the hood. Also returns a ghost object representing proof of being on this thread.
#[verifier(external_body)]
pub fn thread_id() -> (res: (ThreadId, Tracked<IsThread>))
    ensures
        res.1@@ == res.0,
{
    let id: std::thread::ThreadId = std::thread::current().id();
    let id = ThreadId { thread_id: id };
    (id, Tracked::assume_new())
}

/// Returns _just_ the ghost object, without physically obtaining the thread ID.
#[verifier(external_body)]
pub proof fn ghost_thread_id() -> (tracked res: IsThread) {
    unimplemented!();
}

/// Tracked object that makes any tracked object `Send` or `Sync`.
/// Requires the client to prove that they are the correct thread in order to
/// access the underlying object.
#[verifier(external_body)]
#[verifier::accept_recursive_types(V)]
tracked struct ThreadShareable<V> {
    phantom: marker::PhantomData<V>,
}

#[verifier(external)]
unsafe impl<V> Sync for ThreadShareable<V> {

}

#[verifier(external)]
unsafe impl<V> Send for ThreadShareable<V> {

}

impl<V> ThreadShareable<V> {
    pub spec fn view(&self) -> V;

    pub spec fn id(&self) -> ThreadId;

    /// Recover the inner value provide we are on the same thread.
    #[verifier(external_body)]
    pub proof fn into(tracked self, tracked is_thread: IsThread) -> (tracked res: V)
        requires
            self.id() == is_thread@,
        ensures
            res == self@,
    {
        unimplemented!();
    }

    /// Borrow the inner value provide we are on the same thread.
    #[verifier(external_body)]
    pub proof fn borrow(tracked &self, tracked is_thread: IsThread) -> (tracked res: &V)
        requires
            self.id() == is_thread@,
        ensures
            *res == self@,
    {
        unimplemented!();
    }
}

impl<V: Send> ThreadShareable<V> {
    /// Recover the inner value.
    /// Unlike `into`, this has no thread requirement, but it does
    /// require the inner type to be `Send`.
    #[verifier(external_body)]
    pub proof fn send_into(tracked self) -> (tracked res: V)
        ensures
            res == self@,
    {
        unimplemented!();
    }
}

impl<V: Sync> ThreadShareable<V> {
    /// Borrow the inner value.
    /// Unlike `borrow`, this has no thread requirement, but it does
    /// require the inner type to be `Sync`.
    #[verifier(external_body)]
    pub proof fn sync_borrow(tracked &self) -> (tracked res: &V)
        ensures
            *res == self@,
    {
        unimplemented!();
    }
}

} // verus!
}

#[cfg(feature = "alloc")]
pub mod vec {
    #![deprecated(note = "Use std::vec instead")]

    #[allow(unused_imports)]
    use crate::pervasive::*;
    use crate::seq::*;
    #[allow(unused_imports)]
    use crate::slice::*;
    use crate::view::*;
    use alloc::vec;
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use builtin_macros::*;

    verus! {

#[verifier(external_body)]
#[verifier::accept_recursive_types(A)]
pub struct Vec<A> {
    pub vec: vec::Vec<A>,
}

/* TODO: We may want to move to this, but it will break some existing code:

impl<A: View> View for Vec<A> {
    type V = Seq<A::V>;
    spec fn view(&self) -> Seq<A::V>;
}
*/

impl<A> View for Vec<A> {
    type V = Seq<A>;

    spec fn view(&self) -> Seq<A>;
}

impl<A> Vec<A> {
    #[verifier(external_body)]
    pub fn new() -> (v: Self)
        ensures
            v@ == Seq::<A>::empty(),
    {
        Vec { vec: vec::Vec::new() }
    }

    /// Constructs a new, empty `Vec<A>` with at least the specified capacity. Equivalent to
    /// [`Self::new`], but useful to improve performance when the size is known in advance.
    #[verifier(external_body)]
    pub fn with_capacity(capacity: usize) -> (v: Self)
        ensures
            v@ == Seq::<A>::empty(),
    {
        Vec { vec: vec::Vec::with_capacity(capacity) }
    }

    /// Reserves capacity for at least additional more elements to be inserted in the given `Vec<A>`.
    /// The collection may reserve more space to speculatively avoid frequent reallocations. After
    /// calling reserve, capacity will be greater than or equal to `self.len() + additional`. Does
    /// nothing if capacity is already sufficient.
    #[verifier(external_body)]
    pub fn reserve(&mut self, additional: usize)
        ensures
            self@ == old(self)@,
    {
        self.vec.reserve(additional);
    }

    pub fn empty() -> (v: Self)
        ensures
            v@ == Seq::<A>::empty(),
    {
        Vec::new()
    }

    #[verifier(external_body)]
    pub fn push(&mut self, value: A)
        ensures
            self@ == old(self)@.push(value),
    {
        self.vec.push(value);
    }

    #[verifier(external_body)]
    pub fn pop(&mut self) -> (value: A)
        requires
            old(self).len() > 0,
        ensures
            value == old(self)[old(self).len() - 1],
            self@ == old(self)@.subrange(0, old(self).len() - 1),
    {
        unsafe {
            self.vec.pop().unwrap_unchecked()  // Safe to unwrap given the precondition above

        }
    }

    #[verifier(inline)]
    pub open spec fn spec_index(self, i: int) -> A {
        self@[i]
    }

    #[verifier(external_body)]
    pub fn index(&self, i: usize) -> (r: &A)
        requires
            i < self.len(),
        ensures
            *r == self[i as int],
    {
        &self.vec[i]
    }

    #[verifier(external_body)]
    pub fn set(&mut self, i: usize, a: A)
        requires
            i < old(self).len(),
        ensures
            self@ == old(self)@.update(i as int, a),
    {
        self.vec[i] = a;
    }

    #[verifier(external_body)]
    pub fn swap(&mut self, i: usize, a: &mut A)
        requires
            i < old(self).len(),
        ensures
            self@ == old(self)@.update(i as int, *old(a)),
            *a == old(self)@.index(i as int),
    {
        core::mem::swap(&mut self.vec[i], a);
    }

    #[verifier(external_body)]
    pub fn insert(&mut self, i: usize, a: A)
        requires
            i <= old(self).len(),
        ensures
            self@ == old(self)@.insert(i as int, a),
    {
        self.vec.insert(i, a);
    }

    #[verifier(external_body)]
    pub fn remove(&mut self, i: usize) -> (r: A)
        requires
            i < old(self).len(),
        ensures
            r == old(self)[i as int],
            self@ == old(self)@.remove(i as int),
    {
        self.vec.remove(i)
    }

    pub spec fn spec_len(&self) -> usize;

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (l: usize)
        ensures
            l == self.len(),
    {
        self.vec.len()
    }

    #[verifier(external_body)]
    pub fn as_slice(&self) -> (slice: &[A])
        ensures
            slice@ == self@,
    {
        self.vec.as_slice()
    }

    #[verifier(external_body)]
    pub fn clear(&mut self)
        ensures
            self.view() == Seq::<A>::empty(),
    {
        self.vec.clear();
    }

    #[verifier(external_body)]
    pub fn append(&mut self, other: &mut Vec<A>)
        ensures
            self@ == old(self)@ + old(other)@,
            other@ == Seq::<A>::empty(),
    {
        self.vec.append(&mut other.vec);
    }
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_spec_len<A>(v: Vec<A>)
    ensures
        #[trigger] v.spec_len() == v.view().len(),
{
}

} // verus!
}

pub mod view {
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use builtin_macros::*;

    verus! {

/// Types used in executable code can implement View to provide a mathematical abstraction
/// of the type.
/// For example, Vec implements a view method that returns a Seq.
/// For base types like bool and u8, the view V of the type is the type itself.
/// Types only used in ghost code, such as int, nat, and Seq, do not need to implement View.
pub trait View {
    type V;

    spec fn view(&self) -> Self::V;
}

impl<A: View> View for &A {
    type V = A::V;

    #[verifier::inline]
    open spec fn view(&self) -> A::V {
        (**self).view()
    }
}

#[cfg(feature = "alloc")]
impl<A: View> View for alloc::boxed::Box<A> {
    type V = A::V;

    #[verifier::inline]
    open spec fn view(&self) -> A::V {
        (**self).view()
    }
}

#[cfg(feature = "alloc")]
impl<A: View> View for alloc::rc::Rc<A> {
    type V = A::V;

    #[verifier::inline]
    open spec fn view(&self) -> A::V {
        (**self).view()
    }
}

#[cfg(feature = "alloc")]
impl<A: View> View for alloc::sync::Arc<A> {
    type V = A::V;

    #[verifier::inline]
    open spec fn view(&self) -> A::V {
        (**self).view()
    }
}

macro_rules! declare_identity_view {
    ($t:ty) => {
        #[cfg_attr(verus_keep_ghost, verifier::verify)]
        impl View for $t {
            type V = $t;

            #[cfg(verus_keep_ghost)]
            #[verus::internal(spec)]
            #[verus::internal(open)]
            #[verifier::inline]
            fn view(&self) -> $t {
                *self
            }
        }
    }
}

declare_identity_view!(());

declare_identity_view!(bool);

declare_identity_view!(u8);

declare_identity_view!(u16);

declare_identity_view!(u32);

declare_identity_view!(u64);

declare_identity_view!(u128);

declare_identity_view!(usize);

declare_identity_view!(i8);

declare_identity_view!(i16);

declare_identity_view!(i32);

declare_identity_view!(i64);

declare_identity_view!(i128);

declare_identity_view!(isize);

macro_rules! declare_tuple_view {
    ([$($n:tt)*], [$($a:ident)*]) => {
        #[cfg_attr(verus_keep_ghost, verifier::verify)]
        impl<$($a: View, )*> View for ($($a, )*) {
            type V = ($($a::V, )*);
            #[cfg(verus_keep_ghost)]
            #[verus::internal(spec)]
            #[verus::internal(open)]
            fn view(&self) -> ($($a::V, )*) {
                ($(self.$n.view(), )*)
            }
        }
    }
}

// REVIEW: we can declare more, but let's check the vstd size and overhead first
declare_tuple_view!([0], [A0]);

declare_tuple_view!([0 1], [A0 A1]);

declare_tuple_view!([0 1 2], [A0 A1 A2]);

declare_tuple_view!([0 1 2 3], [A0 A1 A2 A3]);

} // verus!
}

pub mod relations {
    //! Provides specifications for spec closures as relations.
    #[allow(unused_imports)]
    use crate::pervasive::*;
    #[allow(unused_imports)]
    use crate::seq::*;
    #[allow(unused_imports)]
    use crate::set::Set;
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use builtin_macros::*;

    verus! {

pub open spec fn injective<X, Y>(r: spec_fn(X) -> Y) -> bool {
    forall|x1: X, x2: X| #[trigger] r(x1) == #[trigger] r(x2) ==> x1 == x2
}

pub open spec fn commutative<T, U>(r: spec_fn(T, T) -> U) -> bool {
    forall|x: T, y: T| #[trigger] r(x, y) == #[trigger] r(y, x)
}

pub open spec fn associative<T>(r: spec_fn(T, T) -> T) -> bool {
    forall|x: T, y: T, z: T| #[trigger] r(x, r(y, z)) == #[trigger] r(r(x, y), z)
}

pub open spec fn reflexive<T>(r: spec_fn(T, T) -> bool) -> bool {
    forall|x: T| #[trigger] r(x, x)
}

pub open spec fn irreflexive<T>(r: spec_fn(T, T) -> bool) -> bool {
    forall|x: T| #[trigger] r(x, x) == false
}

pub open spec fn antisymmetric<T>(r: spec_fn(T, T) -> bool) -> bool {
    forall|x: T, y: T| #[trigger] r(x, y) && #[trigger] r(y, x) ==> x == y
}

pub open spec fn asymmetric<T>(r: spec_fn(T, T) -> bool) -> bool {
    forall|x: T, y: T| #[trigger] r(x, y) ==> #[trigger] r(y, x) == false
}

pub open spec fn symmetric<T>(r: spec_fn(T, T) -> bool) -> bool {
    forall|x: T, y: T| #[trigger] r(x, y) <==> #[trigger] r(y, x)
}

pub open spec fn connected<T>(r: spec_fn(T, T) -> bool) -> bool {
    forall|x: T, y: T| x != y ==> #[trigger] r(x, y) || #[trigger] r(y, x)
}

pub open spec fn strongly_connected<T>(r: spec_fn(T, T) -> bool) -> bool {
    forall|x: T, y: T| #[trigger] r(x, y) || #[trigger] r(y, x)
}

pub open spec fn transitive<T>(r: spec_fn(T, T) -> bool) -> bool {
    forall|x: T, y: T, z: T| #[trigger] r(x, y) && #[trigger] r(y, z) ==> r(x, z)
}

pub open spec fn total_ordering<T>(r: spec_fn(T, T) -> bool) -> bool {
    &&& reflexive(r)
    &&& antisymmetric(r)
    &&& transitive(r)
    &&& strongly_connected(r)
}

pub open spec fn strict_total_ordering<T>(r: spec_fn(T, T) -> bool) -> bool {
    &&& irreflexive(r)
    &&& antisymmetric(r)
    &&& transitive(r)
    &&& connected(r)
}

pub open spec fn pre_ordering<T>(r: spec_fn(T, T) -> bool) -> bool {
    &&& reflexive(r)
    &&& transitive(r)
}

pub open spec fn partial_ordering<T>(r: spec_fn(T, T) -> bool) -> bool {
    &&& reflexive(r)
    &&& transitive(r)
    &&& antisymmetric(r)
}

pub open spec fn equivalence_relation<T>(r: spec_fn(T, T) -> bool) -> bool {
    &&& reflexive(r)
    &&& symmetric(r)
    &&& transitive(r)
}

/// This function returns true if the input sequence a is sorted, using the input function
/// less_than to sort the elements
pub open spec fn sorted_by<T>(a: Seq<T>, less_than: spec_fn(T, T) -> bool) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> #[trigger] less_than(a[i], a[j])
}

/// An element in an ordered set is called a least element (or a minimum), if it is less than
/// every other element of the set.
///
/// change f to leq bc it is a relation. also these are an ordering relation
pub open spec fn is_least<T>(leq: spec_fn(T, T) -> bool, min: T, s: Set<T>) -> bool {
    s.contains(min) && forall|x: T| s.contains(x) ==> #[trigger] leq(min, x)
}

/// An element in an ordered set is called a minimal element, if no other element is less than it.
pub open spec fn is_minimal<T>(leq: spec_fn(T, T) -> bool, min: T, s: Set<T>) -> bool {
    s.contains(min) && forall|x: T|
        s.contains(x) && #[trigger] leq(x, min) ==> #[trigger] leq(min, x)
}

/// An element in an ordered set is called a greatest element (or a maximum), if it is greater than
///every other element of the set.
pub open spec fn is_greatest<T>(leq: spec_fn(T, T) -> bool, max: T, s: Set<T>) -> bool {
    s.contains(max) && forall|x: T| s.contains(x) ==> #[trigger] leq(x, max)
}

/// An element in an ordered set is called a maximal element, if no other element is greater than it.
pub open spec fn is_maximal<T>(leq: spec_fn(T, T) -> bool, max: T, s: Set<T>) -> bool {
    s.contains(max) && forall|x: T|
        s.contains(x) && #[trigger] leq(max, x) ==> #[trigger] leq(x, max)
}

pub proof fn lemma_new_first_element_still_sorted_by<T>(
    x: T,
    s: Seq<T>,
    less_than: spec_fn(T, T) -> bool,
)
    requires
        sorted_by(s, less_than),
        s.len() == 0 || less_than(x, s[0]),
        total_ordering(less_than),
    ensures
        sorted_by(seq![x].add(s), less_than),
{
    if s.len() > 1 {
        assert forall|index: int| 0 < index < s.len() implies #[trigger] less_than(x, s[index]) by {
            assert(less_than(s[0], s[index]));
        };
    }
}

} // verus!
}

#[cfg(verus_keep_ghost)]
pub mod std_specs {
    pub mod atomic {
        #![allow(unused_imports)]
        use crate::prelude::*;
        use builtin::*;
        use builtin_macros::*;

        use core::sync::atomic::*;

        // Supports the core::sync::atomic functions
        // This provides NO support for reasoning about the values inside the atomics.
        // If you need to do that, see `vstd::atomic` or `vstd::atomic_ghost` instead.

        #[verifier::external_type_specification]
        pub struct ExOrdering(Ordering);

        macro_rules! atomic_specs_common {
            ($at:ty, $ty:ty) => {
                #[verifier::external_type_specification]
                #[verifier::external_body]
                pub struct ExAtomic($at);

                #[verifier::external_fn_specification]
                pub fn ex_new(v: $ty) -> $at {
                    <$at>::new(v)
                }

                #[verifier::external_fn_specification]
                pub fn ex_compare_exchange(
                    atomic: &$at,
                    current: $ty,
                    new: $ty,
                    success: Ordering,
                    failure: Ordering,
                ) -> Result<$ty, $ty> {
                    atomic.compare_exchange(current, new, success, failure)
                }

                #[verifier::external_fn_specification]
                pub fn ex_compare_exchange_weak(
                    atomic: &$at,
                    current: $ty,
                    new: $ty,
                    success: Ordering,
                    failure: Ordering,
                ) -> Result<$ty, $ty> {
                    atomic.compare_exchange_weak(current, new, success, failure)
                }

                #[verifier::external_fn_specification]
                pub fn ex_fetch_and(atomic: &$at, val: $ty, order: Ordering) -> $ty {
                    atomic.fetch_and(val, order)
                }

                #[verifier::external_fn_specification]
                pub fn ex_fetch_nand(atomic: &$at, val: $ty, order: Ordering) -> $ty {
                    atomic.fetch_nand(val, order)
                }

                #[verifier::external_fn_specification]
                pub fn ex_fetch_or(atomic: &$at, val: $ty, order: Ordering) -> $ty {
                    atomic.fetch_or(val, order)
                }

                #[verifier::external_fn_specification]
                pub fn ex_fetch_xor(atomic: &$at, val: $ty, order: Ordering) -> $ty {
                    atomic.fetch_xor(val, order)
                }

                #[verifier::external_fn_specification]
                pub fn ex_load(atomic: &$at, order: Ordering) -> $ty {
                    atomic.load(order)
                }

                #[verifier::external_fn_specification]
                pub fn ex_store(atomic: &$at, val: $ty, order: Ordering) {
                    atomic.store(val, order)
                }

                #[verifier::external_fn_specification]
                pub fn ex_swap(atomic: &$at, val: $ty, order: Ordering) -> $ty {
                    atomic.swap(val, order)
                }
            };
        }

        macro_rules! atomic_specs_int_specific {
            ($at:ty, $ty:ty) => {
                #[verifier::external_fn_specification]
                pub fn ex_fetch_add(atomic: &$at, val: $ty, order: Ordering) -> $ty {
                    atomic.fetch_add(val, order)
                }

                #[verifier::external_fn_specification]
                pub fn ex_fetch_sub(atomic: &$at, val: $ty, order: Ordering) -> $ty {
                    atomic.fetch_sub(val, order)
                }

                #[verifier::external_fn_specification]
                pub fn ex_fetch_min(atomic: &$at, val: $ty, order: Ordering) -> $ty {
                    atomic.fetch_min(val, order)
                }

                #[verifier::external_fn_specification]
                pub fn ex_fetch_max(atomic: &$at, val: $ty, order: Ordering) -> $ty {
                    atomic.fetch_max(val, order)
                }
            };
        }

        macro_rules! atomic_specs_int {
            ($modname:ident, $at:ty, $ty:ty) => {
                mod $modname {
                    use super::*;
                    atomic_specs_common!($at, $ty);
                    atomic_specs_int_specific!($at, $ty);
                }
            };
        }

        macro_rules! atomic_specs_bool {
            ($modname:ident, $at:ty, $ty:ty) => {
                mod $modname {
                    use super::*;
                    atomic_specs_common!($at, $ty);
                }
            };
        }

        atomic_specs_int!(atomic_specs_u8, AtomicU8, u8);
        atomic_specs_int!(atomic_specs_u16, AtomicU16, u16);
        atomic_specs_int!(atomic_specs_u32, AtomicU32, u32);
        atomic_specs_int!(atomic_specs_u64, AtomicU64, u64);
        atomic_specs_int!(atomic_specs_usize, AtomicUsize, usize);

        atomic_specs_int!(atomic_specs_i8, AtomicI8, i8);
        atomic_specs_int!(atomic_specs_i16, AtomicI16, i16);
        atomic_specs_int!(atomic_specs_i32, AtomicI32, i32);
        atomic_specs_int!(atomic_specs_i64, AtomicI64, i64);
        atomic_specs_int!(atomic_specs_isize, AtomicIsize, isize);

        atomic_specs_bool!(atomic_specs_bool, AtomicBool, bool);
    }

    pub mod bits {
        use crate::prelude::*;

        verus! {

// TODO mark the lemmas as not external_body when it's supported
// along with broadcast_forall
///////////////////////////
/////////////////////////// For u8
/// Equivalent to `i.trailing_zeros()`.
/// See [`axiom_u8_trailing_zeros`] for useful properties.
pub closed spec fn u8_trailing_zeros(i: u8) -> u32
    decreases i,
{
    if i == 0 {
        8
    } else if (i & 1) != 0 {
        0
    } else {
        (1 + u8_trailing_zeros(i / 2)) as u32
    }
}

/// Equivalent to `i.leading_zeros()`.
/// See [`axiom_u8_leading_zeros`] for useful properties.
pub closed spec fn u8_leading_zeros(i: u8) -> u32
    decreases i,
{
    if i == 0 {
        8
    } else {
        (u8_leading_zeros(i / 2) - 1) as u32
    }
}

/// Equivalent to `i.trailing_ones()`.
/// See [`axiom_u8_trailing_ones`] for useful properties.
pub open spec fn u8_trailing_ones(i: u8) -> u32 {
    u8_trailing_zeros(!i)
}

/// Equivalent to `i.leading_ones()`.
/// See [`axiom_u8_leading_ones`] for useful properties.
pub open spec fn u8_leading_ones(i: u8) -> u32 {
    u8_leading_zeros(!i)
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u8_trailing_zeros)]
pub fn ex_u8_trailing_zeros(i: u8) -> (r: u32)
    ensures
        r == u8_trailing_zeros(i),
{
    i.trailing_zeros()
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u8_trailing_ones)]
pub fn ex_u8_trailing_ones(i: u8) -> (r: u32)
    ensures
        r == u8_trailing_ones(i),
{
    i.trailing_ones()
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u8_leading_zeros)]
pub fn ex_u8_leading_zeros(i: u8) -> (r: u32)
    ensures
        r == u8_leading_zeros(i),
{
    i.leading_zeros()
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u8_leading_ones)]
pub fn ex_u8_leading_ones(i: u8) -> (r: u32)
    ensures
        r == u8_leading_ones(i),
{
    i.leading_ones()
}

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn axiom_u8_trailing_zeros(i: u8)
    ensures
        0 <= #[trigger] u8_trailing_zeros(i) <= 8,
        i == 0 <==> u8_trailing_zeros(i) == 8,
        // i^th bit is 1
        0 <= u8_trailing_zeros(i) < 8 ==> (i >> u8_trailing_zeros(i) as u8) & 1u8 == 1u8,
        // trailing bits are 0
        i << sub(8, u8_trailing_zeros(i) as u8) == 0,
        forall|j: u8| 0 <= j < u8_trailing_zeros(i) ==> #[trigger] (i >> j) & 1u8 == 0u8,
    decreases i,
{
    assert(i >> 0 == i) by (bit_vector);
    assert(i << 0 == i) by (bit_vector);
    assert(i & 0 == 0) by (bit_vector);
    assert(i / 2 == (i >> 1u8)) by (bit_vector);
    assert((i & 1) == 0 ==> i != 1) by (bit_vector);
    let x = u8_trailing_zeros(i / 2) as u8;
    assert(x < 8 ==> (i >> 1) >> x == (i >> add(x, 1))) by (bit_vector);
    assert(i << 8 == 0) by (bit_vector);
    assert(i & 1 != 0 ==> i & 1 == 1) by (bit_vector);
    assert((i & 1) == 0 ==> (i >> 1) << sub(8, x) == 0 ==> i << sub(8, add(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u8_trailing_zeros(i / 2);
    }
    assert forall|j: u8| 0 <= j < u8_trailing_zeros(i) implies #[trigger] (i >> j) & 1u8 == 0u8 by {
        let y = u8_trailing_zeros(i) as u8;
        assert(y <= 8 ==> i << sub(8, y) == 0 && 0 <= j < y ==> (i >> j) & 1u8 == 0u8)
            by (bit_vector);
    }
}

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn axiom_u8_trailing_ones(i: u8)
    ensures
        0 <= #[trigger] u8_trailing_ones(i) <= 8,
        i == 0xffu8 <==> u8_trailing_ones(i) == 8,
        // i^th bit is 0
        0 <= u8_trailing_ones(i) < 8 ==> (i >> u8_trailing_ones(i) as u8) & 1u8 == 0u8,
        // trailing bits are 1
        (!i) << sub(8, u8_trailing_ones(i) as u8) == 0,
        forall|j: u8| 0 <= j < u8_trailing_ones(i) ==> #[trigger] (i >> j) & 1u8 == 1u8,
{
    axiom_u8_trailing_zeros(!i);
    assert(!0xffu8 == 0) by (bit_vector);
    assert(!i == 0 ==> i == 0xffu8) by (bit_vector);
    let x = u8_trailing_ones(i) as u8;
    assert(((!i) >> x) & 1u8 == 1u8 ==> (i >> x) & 1u8 == 0u8) by (bit_vector);
    assert forall|j: u8| 0 <= j < u8_trailing_ones(i) implies #[trigger] (i >> j) & 1u8 == 1u8 by {
        let y = u8_trailing_ones(i) as u8;
        assert(y <= 8 ==> (!i) << sub(8, y) == 0 && 0 <= j < y ==> (i >> j) & 1u8 == 1u8)
            by (bit_vector);
    }
}

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn axiom_u8_leading_zeros(i: u8)
    ensures
        0 <= #[trigger] u8_leading_zeros(i) <= 8,
        i == 0 <==> u8_leading_zeros(i) == 8,
        // i^th bit from the left is 1
        0 <= u8_leading_zeros(i) < 8 ==> (i >> sub(7u8, u8_leading_zeros(i) as u8)) & 1u8 != 0u8,
        // leading bits are 0
        i >> sub(8, u8_leading_zeros(i) as u8) == 0,
        forall|j: u8| 8 - u8_leading_zeros(i) <= j < 8 ==> #[trigger] (i >> j) & 1u8 == 0u8,
    decreases i,
{
    assert(i / 2 == (i >> 1u8)) by (bit_vector);
    assert(((i >> 1) >> sub(7u8, 0)) & 1u8 == 0u8) by (bit_vector);
    let x = u8_leading_zeros(i / 2) as u8;
    assert(i >> 0 == i) by (bit_vector);
    assert(1u8 & 1u8 == 1u8) by (bit_vector);
    assert(0 < x < 8 ==> ((i >> 1) >> sub(7u8, x)) == (i >> sub(7u8, sub(x, 1)))) by (bit_vector);
    assert(0 < x <= 8 ==> (i >> 1) >> sub(8, x) == 0 ==> i >> sub(8, sub(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u8_leading_zeros(i / 2);
    }
    assert forall|j: u8| 8 - u8_leading_zeros(i) <= j < 8 implies #[trigger] (i >> j) & 1u8
        == 0u8 by {
        let y = u8_leading_zeros(i) as u8;
        assert(y <= 8 ==> i >> sub(8, y) == 0 ==> sub(8, y) <= j < 8 ==> (i >> j) & 1u8 == 0u8)
            by (bit_vector);
    }
}

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn axiom_u8_leading_ones(i: u8)
    ensures
        0 <= #[trigger] u8_leading_ones(i) <= 8,
        i == 0xffu8 <==> u8_leading_ones(i) == 8,
        // i^th bit from the left is 0
        0 <= u8_leading_ones(i) < 8 ==> (i >> sub(7u8, u8_leading_ones(i) as u8)) & 1u8 == 0u8,
        (!i) >> sub(8, u8_leading_ones(i) as u8) == 0,
        forall|j: u8| 8 - u8_leading_ones(i) <= j < 8 ==> #[trigger] (i >> j) & 1u8 == 1u8,
{
    axiom_u8_leading_zeros(!i);
    assert(!0xffu8 == 0) by (bit_vector);
    assert(!i == 0 ==> i == 0xffu8) by (bit_vector);
    let x = u8_leading_ones(i) as u8;
    assert(((!i) >> sub(7u8, x)) & 1u8 != 0u8 ==> (i >> sub(7u8, x)) & 1u8 == 0u8) by (bit_vector);
    assert forall|j: u8| 8 - u8_leading_ones(i) <= j < 8 implies #[trigger] (i >> j) & 1u8
        == 1u8 by {
        let y = u8_leading_ones(i) as u8;
        assert(y <= 8 ==> (!i) >> sub(8, y) == 0 ==> sub(8, y) <= j < 8 ==> (i >> j) & 1u8 == 1u8)
            by (bit_vector);
    }
}

///////////////////////////
/////////////////////////// For u16
/// Equivalent to `i.trailing_zeros()`.
/// See [`axiom_u16_trailing_zeros`] for useful properties.
pub closed spec fn u16_trailing_zeros(i: u16) -> u32
    decreases i,
{
    if i == 0 {
        16
    } else if (i & 1) != 0 {
        0
    } else {
        (1 + u16_trailing_zeros(i / 2)) as u32
    }
}

/// Equivalent to `i.leading_zeros()`.
/// See [`axiom_u16_leading_zeros`] for useful properties.
pub closed spec fn u16_leading_zeros(i: u16) -> u32
    decreases i,
{
    if i == 0 {
        16
    } else {
        (u16_leading_zeros(i / 2) - 1) as u32
    }
}

/// Equivalent to `i.trailing_ones()`.
/// See [`axiom_u16_trailing_ones`] for useful properties.
pub open spec fn u16_trailing_ones(i: u16) -> u32 {
    u16_trailing_zeros(!i)
}

/// Equivalent to `i.leading_ones()`.
/// See [`axiom_u16_leading_ones`] for useful properties.
pub open spec fn u16_leading_ones(i: u16) -> u32 {
    u16_leading_zeros(!i)
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u16_trailing_zeros)]
pub fn ex_u16_trailing_zeros(i: u16) -> (r: u32)
    ensures
        r == u16_trailing_zeros(i),
{
    i.trailing_zeros()
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u16_trailing_ones)]
pub fn ex_u16_trailing_ones(i: u16) -> (r: u32)
    ensures
        r == u16_trailing_ones(i),
{
    i.trailing_ones()
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u16_leading_zeros)]
pub fn ex_u16_leading_zeros(i: u16) -> (r: u32)
    ensures
        r == u16_leading_zeros(i),
{
    i.leading_zeros()
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u16_leading_ones)]
pub fn ex_u16_leading_ones(i: u16) -> (r: u32)
    ensures
        r == u16_leading_ones(i),
{
    i.leading_ones()
}

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn axiom_u16_trailing_zeros(i: u16)
    ensures
        0 <= #[trigger] u16_trailing_zeros(i) <= 16,
        i == 0 <==> u16_trailing_zeros(i) == 16,
        // i^th bit is 1
        0 <= u16_trailing_zeros(i) < 16 ==> (i >> u16_trailing_zeros(i) as u16) & 1u16 == 1u16,
        // trailing bits are 0
        i << sub(16, u16_trailing_zeros(i) as u16) == 0,
        forall|j: u16| 0 <= j < u16_trailing_zeros(i) ==> #[trigger] (i >> j) & 1u16 == 0u16,
    decreases i,
{
    assert(i >> 0 == i) by (bit_vector);
    assert(i << 0 == i) by (bit_vector);
    assert(i & 0 == 0) by (bit_vector);
    assert(i / 2 == (i >> 1u16)) by (bit_vector);
    assert((i & 1) == 0 ==> i != 1) by (bit_vector);
    let x = u16_trailing_zeros(i / 2) as u16;
    assert(x < 16 ==> (i >> 1) >> x == (i >> add(x, 1))) by (bit_vector);
    assert(i << 16 == 0) by (bit_vector);
    assert(i & 1 != 0 ==> i & 1 == 1) by (bit_vector);
    assert((i & 1) == 0 ==> (i >> 1) << sub(16, x) == 0 ==> i << sub(16, add(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u16_trailing_zeros(i / 2);
    }
    assert forall|j: u16| 0 <= j < u16_trailing_zeros(i) implies #[trigger] (i >> j) & 1u16
        == 0u16 by {
        let y = u16_trailing_zeros(i) as u16;
        assert(y <= 16 ==> i << sub(16, y) == 0 && 0 <= j < y ==> (i >> j) & 1u16 == 0u16)
            by (bit_vector);
    }
}

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn axiom_u16_trailing_ones(i: u16)
    ensures
        0 <= #[trigger] u16_trailing_ones(i) <= 16,
        i == 0xffffu16 <==> u16_trailing_ones(i) == 16,
        // i^th bit is 0
        0 <= u16_trailing_ones(i) < 16 ==> (i >> u16_trailing_ones(i) as u16) & 1u16 == 0u16,
        // trailing bits are 1
        (!i) << sub(16, u16_trailing_ones(i) as u16) == 0,
        forall|j: u16| 0 <= j < u16_trailing_ones(i) ==> #[trigger] (i >> j) & 1u16 == 1u16,
{
    axiom_u16_trailing_zeros(!i);
    assert(!0xffffu16 == 0) by (bit_vector);
    assert(!i == 0 ==> i == 0xffffu16) by (bit_vector);
    let x = u16_trailing_ones(i) as u16;
    assert(((!i) >> x) & 1u16 == 1u16 ==> (i >> x) & 1u16 == 0u16) by (bit_vector);
    assert forall|j: u16| 0 <= j < u16_trailing_ones(i) implies #[trigger] (i >> j) & 1u16
        == 1u16 by {
        let y = u16_trailing_ones(i) as u16;
        assert(y <= 16 ==> (!i) << sub(16, y) == 0 && 0 <= j < y ==> (i >> j) & 1u16 == 1u16)
            by (bit_vector);
    }
}

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn axiom_u16_leading_zeros(i: u16)
    ensures
        0 <= #[trigger] u16_leading_zeros(i) <= 16,
        i == 0 <==> u16_leading_zeros(i) == 16,
        // i^th bit from the left is 1
        0 <= u16_leading_zeros(i) < 16 ==> (i >> sub(15u16, u16_leading_zeros(i) as u16)) & 1u16
            != 0u16,
        // leading bits are 0
        i >> sub(16, u16_leading_zeros(i) as u16) == 0,
        forall|j: u16| 16 - u16_leading_zeros(i) <= j < 16 ==> #[trigger] (i >> j) & 1u16 == 0u16,
    decreases i,
{
    assert(i / 2 == (i >> 1u16)) by (bit_vector);
    assert(((i >> 1) >> sub(15u16, 0)) & 1u16 == 0u16) by (bit_vector);
    let x = u16_leading_zeros(i / 2) as u16;
    assert(i >> 0 == i) by (bit_vector);
    assert(1u16 & 1u16 == 1u16) by (bit_vector);
    assert(0 < x < 16 ==> ((i >> 1) >> sub(15u16, x)) == (i >> sub(15u16, sub(x, 1))))
        by (bit_vector);
    assert(0 < x <= 16 ==> (i >> 1) >> sub(16, x) == 0 ==> i >> sub(16, sub(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u16_leading_zeros(i / 2);
    }
    assert forall|j: u16| 16 - u16_leading_zeros(i) <= j < 16 implies #[trigger] (i >> j) & 1u16
        == 0u16 by {
        let y = u16_leading_zeros(i) as u16;
        assert(y <= 16 ==> i >> sub(16, y) == 0 ==> sub(16, y) <= j < 16 ==> (i >> j) & 1u16
            == 0u16) by (bit_vector);
    }
}

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn axiom_u16_leading_ones(i: u16)
    ensures
        0 <= #[trigger] u16_leading_ones(i) <= 16,
        i == 0xffffu16 <==> u16_leading_ones(i) == 16,
        // i^th bit from the left is 0
        0 <= u16_leading_ones(i) < 16 ==> (i >> sub(15u16, u16_leading_ones(i) as u16)) & 1u16
            == 0u16,
        (!i) >> sub(16, u16_leading_ones(i) as u16) == 0,
        forall|j: u16| 16 - u16_leading_ones(i) <= j < 16 ==> #[trigger] (i >> j) & 1u16 == 1u16,
{
    axiom_u16_leading_zeros(!i);
    assert(!0xffffu16 == 0) by (bit_vector);
    assert(!i == 0 ==> i == 0xffffu16) by (bit_vector);
    let x = u16_leading_ones(i) as u16;
    assert(((!i) >> sub(15u16, x)) & 1u16 != 0u16 ==> (i >> sub(15u16, x)) & 1u16 == 0u16)
        by (bit_vector);
    assert forall|j: u16| 16 - u16_leading_ones(i) <= j < 16 implies #[trigger] (i >> j) & 1u16
        == 1u16 by {
        let y = u16_leading_ones(i) as u16;
        assert(y <= 16 ==> (!i) >> sub(16, y) == 0 ==> sub(16, y) <= j < 16 ==> (i >> j) & 1u16
            == 1u16) by (bit_vector);
    }
}

///////////////////////////
/////////////////////////// For u32
/// Equivalent to `i.trailing_zeros()`.
/// See [`axiom_u32_trailing_zeros`] for useful properties.
pub closed spec fn u32_trailing_zeros(i: u32) -> u32
    decreases i,
{
    if i == 0 {
        32
    } else if (i & 1) != 0 {
        0
    } else {
        (1 + u32_trailing_zeros(i / 2)) as u32
    }
}

/// Equivalent to `i.leading_zeros()`.
/// See [`axiom_u32_leading_zeros`] for useful properties.
pub closed spec fn u32_leading_zeros(i: u32) -> u32
    decreases i,
{
    if i == 0 {
        32
    } else {
        (u32_leading_zeros(i / 2) - 1) as u32
    }
}

/// Equivalent to `i.trailing_ones()`.
/// See [`axiom_u32_trailing_ones`] for useful properties.
pub open spec fn u32_trailing_ones(i: u32) -> u32 {
    u32_trailing_zeros(!i)
}

/// Equivalent to `i.leading_ones()`.
/// See [`axiom_u32_leading_ones`] for useful properties.
pub open spec fn u32_leading_ones(i: u32) -> u32 {
    u32_leading_zeros(!i)
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u32_trailing_zeros)]
pub fn ex_u32_trailing_zeros(i: u32) -> (r: u32)
    ensures
        r == u32_trailing_zeros(i),
{
    i.trailing_zeros()
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u32_trailing_ones)]
pub fn ex_u32_trailing_ones(i: u32) -> (r: u32)
    ensures
        r == u32_trailing_ones(i),
{
    i.trailing_ones()
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u32_leading_zeros)]
pub fn ex_u32_leading_zeros(i: u32) -> (r: u32)
    ensures
        r == u32_leading_zeros(i),
{
    i.leading_zeros()
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u32_leading_ones)]
pub fn ex_u32_leading_ones(i: u32) -> (r: u32)
    ensures
        r == u32_leading_ones(i),
{
    i.leading_ones()
}

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn axiom_u32_trailing_zeros(i: u32)
    ensures
        0 <= #[trigger] u32_trailing_zeros(i) <= 32,
        i == 0 <==> u32_trailing_zeros(i) == 32,
        // i^th bit is 1
        0 <= u32_trailing_zeros(i) < 32 ==> (i >> u32_trailing_zeros(i) as u32) & 1u32 == 1u32,
        // trailing bits are 0
        i << sub(32, u32_trailing_zeros(i) as u32) == 0,
        forall|j: u32| 0 <= j < u32_trailing_zeros(i) ==> #[trigger] (i >> j) & 1u32 == 0u32,
    decreases i,
{
    assert(i >> 0 == i) by (bit_vector);
    assert(i << 0 == i) by (bit_vector);
    assert(i & 0 == 0) by (bit_vector);
    assert(i / 2 == (i >> 1u32)) by (bit_vector);
    assert((i & 1) == 0 ==> i != 1) by (bit_vector);
    let x = u32_trailing_zeros(i / 2) as u32;
    assert(x < 32 ==> (i >> 1) >> x == (i >> add(x, 1))) by (bit_vector);
    assert(i << 32 == 0) by (bit_vector);
    assert(i & 1 != 0 ==> i & 1 == 1) by (bit_vector);
    assert((i & 1) == 0 ==> (i >> 1) << sub(32, x) == 0 ==> i << sub(32, add(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u32_trailing_zeros(i / 2);
    }
    assert forall|j: u32| 0 <= j < u32_trailing_zeros(i) implies #[trigger] (i >> j) & 1u32
        == 0u32 by {
        let y = u32_trailing_zeros(i) as u32;
        assert(y <= 32 ==> i << sub(32, y) == 0 && 0 <= j < y ==> (i >> j) & 1u32 == 0u32)
            by (bit_vector);
    }
}

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn axiom_u32_trailing_ones(i: u32)
    ensures
        0 <= #[trigger] u32_trailing_ones(i) <= 32,
        i == 0xffff_ffffu32 <==> u32_trailing_ones(i) == 32,
        // i^th bit is 0
        0 <= u32_trailing_ones(i) < 32 ==> (i >> u32_trailing_ones(i) as u32) & 1u32 == 0u32,
        // trailing bits are 1
        (!i) << sub(32, u32_trailing_ones(i) as u32) == 0,
        forall|j: u32| 0 <= j < u32_trailing_ones(i) ==> #[trigger] (i >> j) & 1u32 == 1u32,
{
    axiom_u32_trailing_zeros(!i);
    assert(!0xffff_ffffu32 == 0) by (bit_vector);
    assert(!i == 0 ==> i == 0xffff_ffffu32) by (bit_vector);
    let x = u32_trailing_ones(i) as u32;
    assert(((!i) >> x) & 1u32 == 1u32 ==> (i >> x) & 1u32 == 0u32) by (bit_vector);
    assert forall|j: u32| 0 <= j < u32_trailing_ones(i) implies #[trigger] (i >> j) & 1u32
        == 1u32 by {
        let y = u32_trailing_ones(i) as u32;
        assert(y <= 32 ==> (!i) << sub(32, y) == 0 && 0 <= j < y ==> (i >> j) & 1u32 == 1u32)
            by (bit_vector);
    }
}

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn axiom_u32_leading_zeros(i: u32)
    ensures
        0 <= #[trigger] u32_leading_zeros(i) <= 32,
        i == 0 <==> u32_leading_zeros(i) == 32,
        // i^th bit from the left is 1
        0 <= u32_leading_zeros(i) < 32 ==> (i >> sub(31u32, u32_leading_zeros(i) as u32)) & 1u32
            != 0u32,
        // leading bits are 0
        i >> sub(32, u32_leading_zeros(i) as u32) == 0,
        forall|j: u32| 32 - u32_leading_zeros(i) <= j < 32 ==> #[trigger] (i >> j) & 1u32 == 0u32,
    decreases i,
{
    assert(i / 2 == (i >> 1u32)) by (bit_vector);
    assert(((i >> 1) >> sub(31u32, 0)) & 1u32 == 0u32) by (bit_vector);
    let x = u32_leading_zeros(i / 2) as u32;
    assert(i >> 0 == i) by (bit_vector);
    assert(1u32 & 1u32 == 1u32) by (bit_vector);
    assert(0 < x < 32 ==> ((i >> 1) >> sub(31u32, x)) == (i >> sub(31u32, sub(x, 1))))
        by (bit_vector);
    assert(0 < x <= 32 ==> (i >> 1) >> sub(32, x) == 0 ==> i >> sub(32, sub(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u32_leading_zeros(i / 2);
    }
    assert forall|j: u32| 32 - u32_leading_zeros(i) <= j < 32 implies #[trigger] (i >> j) & 1u32
        == 0u32 by {
        let y = u32_leading_zeros(i) as u32;
        assert(y <= 32 ==> i >> sub(32, y) == 0 ==> sub(32, y) <= j < 32 ==> (i >> j) & 1u32
            == 0u32) by (bit_vector);
    }
}

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn axiom_u32_leading_ones(i: u32)
    ensures
        0 <= #[trigger] u32_leading_ones(i) <= 32,
        i == 0xffff_ffffu32 <==> u32_leading_ones(i) == 32,
        // i^th bit from the left is 0
        0 <= u32_leading_ones(i) < 32 ==> (i >> sub(31u32, u32_leading_ones(i) as u32)) & 1u32
            == 0u32,
        (!i) >> sub(32, u32_leading_ones(i) as u32) == 0,
        forall|j: u32| 32 - u32_leading_ones(i) <= j < 32 ==> #[trigger] (i >> j) & 1u32 == 1u32,
{
    axiom_u32_leading_zeros(!i);
    assert(!0xffff_ffffu32 == 0) by (bit_vector);
    assert(!i == 0 ==> i == 0xffff_ffffu32) by (bit_vector);
    let x = u32_leading_ones(i) as u32;
    assert(((!i) >> sub(31u32, x)) & 1u32 != 0u32 ==> (i >> sub(31u32, x)) & 1u32 == 0u32)
        by (bit_vector);
    assert forall|j: u32| 32 - u32_leading_ones(i) <= j < 32 implies #[trigger] (i >> j) & 1u32
        == 1u32 by {
        let y = u32_leading_ones(i) as u32;
        assert(y <= 32 ==> (!i) >> sub(32, y) == 0 ==> sub(32, y) <= j < 32 ==> (i >> j) & 1u32
            == 1u32) by (bit_vector);
    }
}

///////////////////////////
/////////////////////////// For u64
/// Equivalent to `i.trailing_zeros()`.
/// See [`axiom_u64_trailing_zeros`] for useful properties.
pub closed spec fn u64_trailing_zeros(i: u64) -> u32
    decreases i,
{
    if i == 0 {
        64
    } else if (i & 1) != 0 {
        0
    } else {
        (1 + u64_trailing_zeros(i / 2)) as u32
    }
}

/// Equivalent to `i.leading_zeros()`.
/// See [`axiom_u64_leading_zeros`] for useful properties.
#[verifier::opaque]
pub open spec fn u64_leading_zeros(i: u64) -> int
    decreases i,
{
    if i == 0 {
        64
    } else {
        u64_leading_zeros(i / 2) - 1
    }
}

/// Equivalent to `i.trailing_ones()`.
/// See [`axiom_u64_trailing_ones`] for useful properties.
pub open spec fn u64_trailing_ones(i: u64) -> u32 {
    u64_trailing_zeros(!i) as u32
}

/// Equivalent to `i.leading_ones()`.
/// See [`axiom_u64_leading_ones`] for useful properties.
pub open spec fn u64_leading_ones(i: u64) -> u32 {
    u64_leading_zeros(!i) as u32
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u64_trailing_zeros)]
pub fn ex_u64_trailing_zeros(i: u64) -> (r: u32)
    ensures
        r == u64_trailing_zeros(i),
{
    i.trailing_zeros()
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u64_trailing_ones)]
pub fn ex_u64_trailing_ones(i: u64) -> (r: u32)
    ensures
        r == u64_trailing_ones(i),
{
    i.trailing_ones()
}

#[verifier::external_fn_specification]
//#[verifier::when_used_as_spec(u64_leading_zeros)]
pub fn ex_u64_leading_zeros(i: u64) -> (r: u32)
    ensures
        r as int == u64_leading_zeros(i),
{
    i.leading_zeros()
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u64_leading_ones)]
pub fn ex_u64_leading_ones(i: u64) -> (r: u32)
    ensures
        r == u64_leading_ones(i),
{
    i.leading_ones()
}

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn axiom_u64_trailing_zeros(i: u64)
    ensures
        0 <= #[trigger] u64_trailing_zeros(i) <= 64,
        i == 0 <==> u64_trailing_zeros(i) == 64,
        // i^th bit is 1
        0 <= u64_trailing_zeros(i) < 64 ==> (i >> u64_trailing_zeros(i) as u64) & 1u64 == 1u64,
        // trailing bits are 0
        i << sub(64, u64_trailing_zeros(i) as u64) == 0,
        forall|j: u64| 0 <= j < u64_trailing_zeros(i) ==> #[trigger] (i >> j) & 1u64 == 0u64,
    decreases i,
{
    assert(i >> 0 == i) by (bit_vector);
    assert(i << 0 == i) by (bit_vector);
    assert(i & 0 == 0) by (bit_vector);
    assert(i / 2 == (i >> 1u64)) by (bit_vector);
    assert((i & 1) == 0 ==> i != 1) by (bit_vector);
    let x = u64_trailing_zeros(i / 2) as u64;
    assert(x < 64 ==> (i >> 1) >> x == (i >> add(x, 1))) by (bit_vector);
    assert(i << 64 == 0) by (bit_vector);
    assert(i & 1 != 0 ==> i & 1 == 1) by (bit_vector);
    assert((i & 1) == 0 ==> (i >> 1) << sub(64, x) == 0 ==> i << sub(64, add(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u64_trailing_zeros(i / 2);
    }
    assert forall|j: u64| 0 <= j < u64_trailing_zeros(i) implies #[trigger] (i >> j) & 1u64
        == 0u64 by {
        let y = u64_trailing_zeros(i) as u64;
        assert(y <= 64 ==> i << sub(64, y) == 0 && 0 <= j < y ==> (i >> j) & 1u64 == 0u64)
            by (bit_vector);
    }
}

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn axiom_u64_trailing_ones(i: u64)
    ensures
        0 <= #[trigger] u64_trailing_ones(i) <= 64,
        i == 0xffff_ffff_ffff_ffffu64 <==> u64_trailing_ones(i) == 64,
        // i^th bit is 0
        0 <= u64_trailing_ones(i) < 64 ==> (i >> u64_trailing_ones(i) as u64) & 1u64 == 0u64,
        // trailing bits are 1
        (!i) << sub(64, u64_trailing_ones(i) as u64) == 0,
        forall|j: u64| 0 <= j < u64_trailing_ones(i) ==> #[trigger] (i >> j) & 1u64 == 1u64,
{
    axiom_u64_trailing_zeros(!i);
    assert(!0xffff_ffff_ffff_ffffu64 == 0) by (bit_vector);
    assert(!i == 0 ==> i == 0xffff_ffff_ffff_ffffu64) by (bit_vector);
    let x = u64_trailing_ones(i) as u64;
    assert(((!i) >> x) & 1u64 == 1u64 ==> (i >> x) & 1u64 == 0u64) by (bit_vector);
    assert forall|j: u64| 0 <= j < u64_trailing_ones(i) implies #[trigger] (i >> j) & 1u64
        == 1u64 by {
        let y = u64_trailing_ones(i) as u64;
        assert(y <= 64 ==> (!i) << sub(64, y) == 0 && 0 <= j < y ==> (i >> j) & 1u64 == 1u64)
            by (bit_vector);
    }
}

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn axiom_u64_leading_zeros(i: u64)
    ensures
        0 <= #[trigger] u64_leading_zeros(i) <= 64,
        i == 0 <==> u64_leading_zeros(i) == 64,
        // i^th bit from the left is 1
        0 <= u64_leading_zeros(i) < 64 ==> (i >> sub(63u64, u64_leading_zeros(i) as u64)) & 1u64
            != 0u64,
        // leading bits are 0
        i >> sub(64, u64_leading_zeros(i) as u64) == 0,
        forall|j: u64| 64 - u64_leading_zeros(i) <= j < 64 ==> #[trigger] (i >> j) & 1u64 == 0u64,
    decreases i,
{
    assert(i / 2 == (i >> 1u64)) by (bit_vector);
    assert(((i >> 1) >> sub(63u64, 0)) & 1u64 == 0u64) by (bit_vector);
    let x = u64_leading_zeros(i / 2) as u64;
    assert(i >> 0 == i) by (bit_vector);
    assert(1u64 & 1u64 == 1u64) by (bit_vector);
    assert(0 < x < 64 ==> ((i >> 1) >> sub(63u64, x)) == (i >> sub(63u64, sub(x, 1))))
        by (bit_vector);
    assert(0 < x <= 64 ==> (i >> 1) >> sub(64, x) == 0 ==> i >> sub(64, sub(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u64_leading_zeros(i / 2);
    }
    assert forall|j: u64| 64 - u64_leading_zeros(i) <= j < 64 implies #[trigger] (i >> j) & 1u64
        == 0u64 by {
        let y = u64_leading_zeros(i) as u64;
        assert(y <= 64 ==> i >> sub(64, y) == 0 ==> sub(64, y) <= j < 64 ==> (i >> j) & 1u64
            == 0u64) by (bit_vector);
    }
}

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn axiom_u64_leading_ones(i: u64)
    ensures
        0 <= #[trigger] u64_leading_ones(i) <= 64,
        i == 0xffff_ffff_ffff_ffffu64 <==> u64_leading_ones(i) == 64,
        // i^th bit from the left is 0
        0 <= u64_leading_ones(i) < 64 ==> (i >> sub(63u64, u64_leading_ones(i) as u64)) & 1u64
            == 0u64,
        (!i) >> sub(64, u64_leading_ones(i) as u64) == 0,
        forall|j: u64| 64 - u64_leading_ones(i) <= j < 64 ==> #[trigger] (i >> j) & 1u64 == 1u64,
{
    axiom_u64_leading_zeros(!i);
    assert(!0xffff_ffff_ffff_ffffu64 == 0) by (bit_vector);
    assert(!i == 0 ==> i == 0xffff_ffff_ffff_ffffu64) by (bit_vector);
    let x = u64_leading_ones(i) as u64;
    assert(((!i) >> sub(63u64, x)) & 1u64 != 0u64 ==> (i >> sub(63u64, x)) & 1u64 == 0u64)
        by (bit_vector);
    assert forall|j: u64| 64 - u64_leading_ones(i) <= j < 64 implies #[trigger] (i >> j) & 1u64
        == 1u64 by {
        let y = u64_leading_ones(i) as u64;
        assert(y <= 64 ==> (!i) >> sub(64, y) == 0 ==> sub(64, y) <= j < 64 ==> (i >> j) & 1u64
            == 1u64) by (bit_vector);
    }
}

} // verus!
    }

    pub mod control_flow {
        use crate::prelude::*;
        use core::convert::Infallible;
        use core::ops::ControlFlow;
        use core::ops::FromResidual;
        use core::ops::Try;

        verus! {

#[verifier(external_type_specification)]
#[verifier::accept_recursive_types(B)]
#[verifier::reject_recursive_types_in_ground_variants(C)]
pub struct ExControlFlow<B, C>(ControlFlow<B, C>);

#[verifier(external_type_specification)]
#[verifier(external_body)]
pub struct ExInfallible(Infallible);

#[verifier::external_fn_specification]
pub fn ex_result_branch<T, E>(result: Result<T, E>) -> (cf: ControlFlow<
    <Result<T, E> as Try>::Residual,
    <Result<T, E> as Try>::Output,
>)
    ensures
        cf === match result {
            Ok(v) => ControlFlow::Continue(v),
            Err(e) => ControlFlow::Break(Err(e)),
        },
{
    result.branch()
}

#[verifier::external_fn_specification]
pub fn ex_option_branch<T>(option: Option<T>) -> (cf: ControlFlow<
    <Option<T> as Try>::Residual,
    <Option<T> as Try>::Output,
>)
    ensures
        cf === match option {
            Some(v) => ControlFlow::Continue(v),
            None => ControlFlow::Break(None),
        },
{
    option.branch()
}

#[verifier::external_fn_specification]
pub fn ex_option_from_residual<T>(option: Option<Infallible>) -> (option2: Option<T>)
    ensures
        option.is_none(),
        option2.is_none(),
{
    Option::from_residual(option)
}

pub spec fn spec_from<S, T>(value: T, ret: S) -> bool;

#[verifier::broadcast_forall]
#[verifier::external_body]
pub proof fn spec_from_blanket_identity<T>(t: T, s: T)
    ensures
        spec_from::<T, T>(t, s) ==> t == s,
{
}

#[verifier::external_fn_specification]
pub fn ex_result_from_residual<T, E, F: From<E>>(result: Result<Infallible, E>) -> (result2: Result<
    T,
    F,
>)
    ensures
        match (result, result2) {
            (Err(e), Err(e2)) => spec_from::<F, E>(e, e2),
            _ => false,
        },
{
    Result::from_residual(result)
}

} // verus!
    }

    pub mod core {
        use crate::prelude::*;

        verus! {

#[verifier(external_fn_specification)]
pub fn ex_swap<T>(a: &mut T, b: &mut T)
    ensures
        *a == *old(b),
        *b == *old(a),
{
    core::mem::swap(a, b)
}

#[verifier(external_type_specification)]
#[verifier::accept_recursive_types(V)]
#[verifier::ext_equal]
pub struct ExOption<V>(core::option::Option<V>);

#[verifier(external_type_specification)]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types_in_ground_variants(E)]
pub struct ExResult<T, E>(core::result::Result<T, E>);

pub open spec fn iter_into_iter_spec<I: Iterator>(i: I) -> I {
    i
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(iter_into_iter_spec)]
pub fn ex_iter_into_iter<I: Iterator>(i: I) -> (r: I)
    ensures
        r == i,
{
    i.into_iter()
}

// I don't really expect this to be particularly useful;
// this is mostly here because I wanted an easy way to test
// the combination of external_type_specification & external_body
// in a cross-crate context.
#[verifier(external_type_specification)]
#[verifier(external_body)]
pub struct ExDuration(core::time::Duration);

#[verifier(external_type_specification)]
#[verifier(external_body)]
#[verifier::reject_recursive_types_in_ground_variants(V)]
pub struct ExPhantomData<V: ?Sized>(core::marker::PhantomData<V>);

#[verifier::external_fn_specification]
pub fn ex_intrinsics_likely(b: bool) -> (c: bool)
    ensures
        c == b,
{
    core::intrinsics::likely(b)
}

#[verifier::external_fn_specification]
pub fn ex_intrinsics_unlikely(b: bool) -> (c: bool)
    ensures
        c == b,
{
    core::intrinsics::unlikely(b)
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types_in_ground_variants(V)]
pub struct ExManuallyDrop<V: ?Sized>(core::mem::ManuallyDrop<V>);

} // verus!
    }

    pub mod num {
        #![allow(unused_imports)]
        use crate::prelude::*;
        use builtin::*;
        use builtin_macros::*;

        macro_rules! num_specs {
            ($uN: ty, $iN: ty, $modname_u:ident, $modname_i:ident, $range:expr) => {
                verus! {

        // Unsigned ints (u8, u16, etc.)

        // Put in separate module to avoid name collisions.
        // Names don't matter - the user uses the stdlib functions.
        mod $modname_u {
            use super::*;

            pub open spec fn wrapping_add(x: $uN, y: $uN) -> $uN {
                if x + y > <$uN>::MAX {
                    (x + y - $range) as $uN
                } else {
                    (x + y) as $uN
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(wrapping_add)]
            pub fn ex_wrapping_add(x: $uN, y: $uN) -> (res: $uN)
                ensures res == wrapping_add(x, y)
            {
                x.wrapping_add(y)
            }

            pub open spec fn wrapping_add_signed(x: $uN, y: $iN) -> $uN {
                if x + y > <$uN>::MAX {
                    (x + y - $range) as $uN
                } else if x + y < 0 {
                    (x + y + $range) as $uN
                } else {
                    (x + y) as $uN
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(wrapping_add_signed)]
            pub fn ex_wrapping_add_signed(x: $uN, y: $iN) -> (res: $uN)
                ensures res == wrapping_add_signed(x, y)
            {
                x.wrapping_add_signed(y)
            }

            pub open spec fn wrapping_sub(x: $uN, y: $uN) -> $uN {
                if x - y < 0 {
                    (x - y + $range) as $uN
                } else {
                    (x - y) as $uN
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(wrapping_sub)]
            pub fn ex_wrapping_sub(x: $uN, y: $uN) -> (res: $uN)
                ensures res == wrapping_sub(x, y)
            {
                x.wrapping_sub(y)
            }
        }

        // Signed ints (i8, i16, etc.)

        mod $modname_i {
            use super::*;

            pub open spec fn wrapping_add(x: $iN, y: $iN) -> $iN {
                if x + y > <$iN>::MAX {
                    (x + y - $range) as $iN
                } else if x + y < <$iN>::MIN {
                    (x + y + $range) as $iN
                } else {
                    (x + y) as $iN
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(wrapping_add)]
            pub fn ex_wrapping_add(x: $iN, y: $iN) -> (res: $iN)
                ensures res == wrapping_add(x, y)
            {
                x.wrapping_add(y)
            }

            pub open spec fn wrapping_add_unsigned(x: $iN, y: $uN) -> $iN {
                if x + y > <$iN>::MAX {
                    (x + y - $range) as $iN
                } else {
                    (x + y) as $iN
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(wrapping_add_unsigned)]
            pub fn ex_wrapping_add_unsigned(x: $iN, y: $uN) -> (res: $iN)
                ensures res == wrapping_add_unsigned(x, y)
            {
                x.wrapping_add_unsigned(y)
            }

            pub open spec fn wrapping_sub(x: $iN, y: $iN) -> $iN {
                if x - y > <$iN>::MAX {
                    (x - y - $range) as $iN
                } else if x - y < <$iN>::MIN {
                    (x - y + $range) as $iN
                } else {
                    (x - y) as $iN
                }
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(wrapping_sub)]
            pub fn ex_wrapping_sub(x: $iN, y: $iN) -> (res: $iN)
                ensures res == wrapping_sub(x, y)
            {
                x.wrapping_sub(y)
            }

            pub open spec fn signed_crop(x: int) -> $iN {
                if (x % ($range as int)) > (<$iN>::MAX as int) {
                    ((x % ($range as int)) - $range) as $iN
                } else {
                    (x % ($range as int)) as $iN
                }
            }

            pub open spec fn wrapping_mul(x: $iN, y: $iN) -> $iN {
                signed_crop(x * y)
            }

            #[verifier::external_fn_specification]
            #[verifier::when_used_as_spec(wrapping_mul)]
            pub fn ex_wrapping_mul(x: $iN, y: $iN) -> (res: $iN)
                ensures res == wrapping_mul(x, y)
            {
                x.wrapping_mul(y)
            }
        }

        }
            };
        }

        num_specs!(u8, i8, u8_specs, i8_specs, 0x100);
        num_specs!(u16, i16, u16_specs, i16_specs, 0x1_0000);
        num_specs!(u32, i32, u32_specs, i32_specs, 0x1_0000_0000);
        num_specs!(u64, i64, u64_specs, i64_specs, 0x1_0000_0000_0000_0000);
        num_specs!(
            u128,
            i128,
            u128_specs,
            i128_specs,
            0x1_0000_0000_0000_0000_0000_0000_0000_0000
        );
        num_specs!(
            usize,
            isize,
            usize_specs,
            isize_specs,
            (usize::MAX - usize::MIN + 1)
        );

        verus! {

// == u32 methods ==
#[verifier::external_fn_specification]
pub fn ex_u32_checked_add(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures
        lhs + rhs > u32::MAX ==> result.is_None(),
        lhs + rhs <= u32::MAX ==> result == Some((lhs + rhs) as u32),
{
    lhs.checked_add(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_add_signed(lhs: u32, rhs: i32) -> (result: Option<u32>)
    ensures
        lhs + rhs > u32::MAX || lhs + rhs < 0 ==> result.is_None(),
        lhs + rhs <= u32::MAX ==> result == Some((lhs + rhs) as u32),
{
    lhs.checked_add_signed(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_sub(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures
        lhs - rhs < 0 ==> result.is_None(),
        lhs - rhs >= 0 ==> result == Some((lhs - rhs) as u32),
{
    lhs.checked_sub(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_mul(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures
        lhs * rhs > u32::MAX ==> result.is_None(),
        lhs * rhs <= u32::MAX ==> result == Some((lhs * rhs) as u32),
{
    lhs.checked_mul(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_div(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures
        rhs == 0 ==> result.is_None(),
        rhs != 0 ==> result == Some((lhs / rhs) as u32),
{
    lhs.checked_div(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_div_euclid(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures
        rhs == 0 ==> result.is_None(),
        rhs != 0 ==> result == Some((lhs / rhs) as u32),
{
    lhs.checked_div_euclid(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_rem(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures
        rhs == 0 ==> result.is_None(),
        rhs != 0 ==> result == Some((lhs % rhs) as u32),
{
    lhs.checked_rem(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_u32_checked_rem_euclid(lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures
        rhs == 0 ==> result.is_None(),
        rhs != 0 ==> result == Some((lhs % rhs) as u32),
{
    lhs.checked_rem_euclid(rhs)
}

// == i32 methods ==
#[verifier::external_fn_specification]
pub fn ex_i32_checked_add(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures
        lhs + rhs > i32::MAX || lhs + rhs < i32::MIN ==> result.is_None(),
        i32::MIN <= lhs + rhs <= i32::MAX ==> result == Some((lhs + rhs) as i32),
{
    lhs.checked_add(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_add_unsigned(lhs: i32, rhs: u32) -> (result: Option<i32>)
    ensures
        lhs + rhs > i32::MAX ==> result.is_None(),
        lhs + rhs <= i32::MAX ==> result == Some((lhs + rhs) as i32),
{
    lhs.checked_add_unsigned(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_sub(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures
        lhs - rhs > i32::MAX || lhs - rhs < i32::MIN ==> result.is_None(),
        i32::MIN <= lhs - rhs <= i32::MAX ==> result == Some((lhs - rhs) as i32),
{
    lhs.checked_sub(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_sub_unsigned(lhs: i32, rhs: u32) -> (result: Option<i32>)
    ensures
        lhs - rhs < i32::MIN ==> result.is_None(),
        i32::MIN <= lhs - rhs ==> result == Some((lhs - rhs) as i32),
{
    lhs.checked_sub_unsigned(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_mul(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures
        lhs * rhs < i32::MIN || lhs * rhs > i32::MAX ==> result.is_None(),
        i32::MIN <= lhs * rhs <= i32::MAX ==> result == Some((lhs * rhs) as i32),
{
    lhs.checked_mul(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_div(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures
        rhs == 0 ==> result.is_None(),
        ({
            let x = lhs as int;
            let d = rhs as int;
            let output = if x == 0 {
                0
            } else if x > 0 && d > 0 {
                x / d
            } else if x < 0 && d < 0 {
                ((x * -1) / (d * -1))
            } else if x < 0 {
                ((x * -1) / d) * -1
            } else {  // d < 0
                (x / (d * -1)) * -1
            };
            if output < i32::MIN || output > i32::MAX {
                result.is_None()
            } else {
                result == Some(output as i32)
            }
        }),
{
    lhs.checked_div(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_div_euclid(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures
        rhs == 0 ==> result.is_None(),
        lhs / rhs < i32::MIN || lhs / rhs > i32::MAX ==> result.is_None(),
        i32::MIN <= lhs / rhs <= i32::MAX ==> result == Some((lhs / rhs) as i32),
{
    lhs.checked_div_euclid(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_rem(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures
        rhs == 0 ==> result.is_None(),
        ({
            let x = lhs as int;
            let d = rhs as int;
            let output = if x == 0 {
                0
            } else if x > 0 && d > 0 {
                x % d
            } else if x < 0 && d < 0 {
                ((x * -1) % (d * -1)) * -1
            } else if x < 0 {
                ((x * -1) % d) * -1
            } else {  // d < 0
                x % (d * -1)
            };
            if output < i32::MIN || output > i32::MAX {
                result.is_None()
            } else {
                result == Some(output as i32)
            }
        }),
{
    lhs.checked_rem(rhs)
}

#[verifier::external_fn_specification]
pub fn ex_i32_checked_rem_euclid(lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures
        rhs == 0 ==> result.is_None(),
        lhs % rhs < i32::MIN || lhs % rhs > i32::MAX ==> result.is_None(),
        i32::MIN <= lhs % rhs <= i32::MAX ==> result == Some((lhs % rhs) as i32),
{
    lhs.checked_rem_euclid(rhs)
}

} // verus!
    }

    pub mod option {
        #![allow(unused_imports)]
        use crate::prelude::*;

        use core::option::Option;
        use core::option::Option::None;
        use core::option::Option::Some;

        verus! {

////// Add is_variant-style spec functions
pub trait OptionAdditionalFns<T>: Sized {
    #[allow(non_snake_case)]
    spec fn is_Some(&self) -> bool;

    #[allow(non_snake_case)]
    spec fn get_Some_0(&self) -> T;

    #[allow(non_snake_case)]
    spec fn is_None(&self) -> bool;

    #[allow(non_snake_case)]
    spec fn arrow_Some_0(&self) -> T;

    #[allow(non_snake_case)]
    spec fn arrow_0(&self) -> T;

    proof fn tracked_unwrap(tracked self) -> (tracked t: T)
        requires
            self.is_Some(),
        ensures
            t == self.get_Some_0(),
    ;

    proof fn tracked_borrow(tracked &self) -> (tracked t: &T)
        requires
            self.is_Some(),
        ensures
            t == self.get_Some_0(),
    ;
}

impl<T> OptionAdditionalFns<T> for Option<T> {
    #[verifier(inline)]
    open spec fn is_Some(&self) -> bool {
        builtin::is_variant(self, "Some")
    }

    #[verifier(inline)]
    open spec fn get_Some_0(&self) -> T {
        builtin::get_variant_field(self, "Some", "0")
    }

    #[verifier(inline)]
    open spec fn is_None(&self) -> bool {
        builtin::is_variant(self, "None")
    }

    #[verifier(inline)]
    open spec fn arrow_Some_0(&self) -> T {
        builtin::get_variant_field(self, "Some", "0")
    }

    #[verifier(inline)]
    open spec fn arrow_0(&self) -> T {
        builtin::get_variant_field(self, "Some", "0")
    }

    proof fn tracked_unwrap(tracked self) -> (tracked t: T) {
        match self {
            Option::Some(t) => t,
            Option::None => proof_from_false(),
        }
    }

    proof fn tracked_borrow(tracked &self) -> (tracked t: &T) {
        match self {
            Option::Some(t) => t,
            Option::None => proof_from_false(),
        }
    }
}

////// Specs for std methods
// is_some
#[verifier(inline)]
pub open spec fn is_some<T>(option: &Option<T>) -> bool {
    builtin::is_variant(option, "Some")
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(is_some)]
pub fn ex_option_is_some<T>(option: &Option<T>) -> (b: bool)
    ensures
        b == is_some(option),
{
    option.is_some()
}

// is_none
#[verifier(inline)]
pub open spec fn is_none<T>(option: &Option<T>) -> bool {
    builtin::is_variant(option, "None")
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(is_none)]
pub fn ex_option_is_none<T>(option: &Option<T>) -> (b: bool)
    ensures
        b == is_none(option),
{
    option.is_none()
}

// as_ref
#[verifier::external_fn_specification]
pub fn as_ref<T>(option: &Option<T>) -> (a: Option<&T>)
    ensures
        a.is_Some() <==> option.is_Some(),
        a.is_Some() ==> option.get_Some_0() == a.get_Some_0(),
{
    option.as_ref()
}

// unwrap
#[verifier(inline)]
pub open spec fn spec_unwrap<T>(option: Option<T>) -> T
    recommends
        option.is_Some(),
{
    option.get_Some_0()
}

#[verifier(when_used_as_spec(spec_unwrap))]
#[verifier::external_fn_specification]
pub fn unwrap<T>(option: Option<T>) -> (t: T)
    requires
        option.is_Some(),
    ensures
        t == spec_unwrap(option),
{
    option.unwrap()
}

// unwrap_or
#[verifier(inline)]
pub open spec fn spec_unwrap_or<T>(option: Option<T>, default: T) -> T {
    match option {
        Some(t) => t,
        None => default,
    }
}

#[verifier(when_used_as_spec(spec_unwrap_or))]
#[verifier::external_fn_specification]
pub fn unwrap_or<T>(option: Option<T>, default: T) -> (t: T)
    ensures
        t == spec_unwrap_or(option, default),
{
    option.unwrap_or(default)
}

#[verifier::external_fn_specification]
pub fn take<T>(option: &mut Option<T>) -> (t: Option<T>)
    ensures
        t == old(option),
        *option is None,
{
    option.take()
}

} // verus!
    }

    pub mod range {
        use crate::prelude::*;
        use core::ops::Range;

        verus! {

#[verifier(external_type_specification)]
#[verifier::reject_recursive_types_in_ground_variants(Idx)]
pub struct ExRange<Idx>(Range<Idx>);

pub trait StepSpec where Self: Sized {
    // REVIEW: it would be nice to be able to use SpecOrd::spec_lt (not yet supported)
    spec fn spec_is_lt(self, other: Self) -> bool;

    spec fn spec_steps_between(self, end: Self) -> Option<usize>;

    spec fn spec_steps_between_int(self, end: Self) -> int;

    spec fn spec_forward_checked(self, count: usize) -> Option<Self>;

    spec fn spec_forward_checked_int(self, count: int) -> Option<Self>;

    spec fn spec_backward_checked(self, count: usize) -> Option<Self>;

    spec fn spec_backward_checked_int(self, count: int) -> Option<Self>;
}

pub spec fn spec_range_next<A>(a: Range<A>) -> (Range<A>, Option<A>);

#[verifier::external_fn_specification]
pub fn ex_range_next<A: core::iter::Step>(range: &mut Range<A>) -> (r: Option<A>)
    ensures
        (*range, r) == spec_range_next(*old(range)),
{
    range.next()
}

pub struct RangeGhostIterator<A> {
    pub start: A,
    pub cur: A,
    pub end: A,
}

impl<A: StepSpec> crate::pervasive::ForLoopGhostIteratorNew for Range<A> {
    type GhostIter = RangeGhostIterator<A>;

    open spec fn ghost_iter(&self) -> RangeGhostIterator<A> {
        RangeGhostIterator { start: self.start, cur: self.start, end: self.end }
    }
}

impl<A: StepSpec + core::iter::Step> crate::pervasive::ForLoopGhostIterator for RangeGhostIterator<
    A,
> {
    type ExecIter = Range<A>;

    type Item = A;

    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &Range<A>) -> bool {
        &&& self.cur == exec_iter.start
        &&& self.end == exec_iter.end
    }

    open spec fn ghost_invariant(&self, init: Option<&Self>) -> bool {
        &&& self.start.spec_is_lt(self.cur) || self.start == self.cur
        &&& self.cur.spec_is_lt(self.end) || self.cur
            == self.end
        // TODO (not important): use new "matches ==>" syntax here

        &&& if let Some(init) = init {
            &&& init.start == init.cur
            &&& init.start == self.start
            &&& init.end == self.end
        } else {
            true
        }
    }

    open spec fn ghost_ensures(&self) -> bool {
        !self.cur.spec_is_lt(self.end)
    }

    open spec fn ghost_decrease(&self) -> Option<int> {
        Some(self.cur.spec_steps_between_int(self.end))
    }

    open spec fn ghost_peek_next(&self) -> Option<A> {
        Some(self.cur)
    }

    open spec fn ghost_advance(&self, _exec_iter: &Range<A>) -> RangeGhostIterator<A> {
        RangeGhostIterator { cur: self.cur.spec_forward_checked(1).unwrap(), ..*self }
    }
}

impl<A: StepSpec + core::iter::Step> crate::view::View for RangeGhostIterator<A> {
    type V = Seq<A>;

    // generate seq![start, start + 1, start + 2, ..., cur - 1]
    open spec fn view(&self) -> Seq<A> {
        Seq::new(
            self.start.spec_steps_between_int(self.cur) as nat,
            |i: int| self.start.spec_forward_checked_int(i).unwrap(),
        )
    }
}

} // verus!
        macro_rules! step_specs {
            ($t: ty, $axiom: ident) => {
                verus! {
        impl StepSpec for $t {
            open spec fn spec_is_lt(self, other: Self) -> bool {
                self < other
            }
            open spec fn spec_steps_between(self, end: Self) -> Option<usize> {
                let n = end - self;
                if usize::MIN <= n <= usize::MAX {
                    Some(n as usize)
                } else {
                    None
                }
            }
            open spec fn spec_steps_between_int(self, end: Self) -> int {
                end - self
            }
            open spec fn spec_forward_checked(self, count: usize) -> Option<Self> {
                self.spec_forward_checked_int(count as int)
            }
            open spec fn spec_forward_checked_int(self, count: int) -> Option<Self> {
                if self + count <= $t::MAX {
                    Some((self + count) as $t)
                } else {
                    None
                }
            }
            open spec fn spec_backward_checked(self, count: usize) -> Option<Self> {
                self.spec_backward_checked_int(count as int)
            }
            open spec fn spec_backward_checked_int(self, count: int) -> Option<Self> {
                if self - count >= $t::MIN {
                    Some((self - count) as $t)
                } else {
                    None
                }
            }
        }
        // TODO: we might be able to make this generic over A: StepSpec
        // once we settle on a way to connect std traits like Step with spec traits like StepSpec.
        #[verifier::external_body]
        #[verifier::broadcast_forall]
        pub proof fn $axiom(range: Range<$t>)
            ensures
                range.start.spec_is_lt(range.end) ==>
                    // TODO (not important): use new "matches ==>" syntax here
                    (if let Some(n) = range.start.spec_forward_checked(1) {
                        spec_range_next(range) == (Range { start: n, ..range }, Some(range.start))
                    } else {
                        true
                    }),
                !range.start.spec_is_lt(range.end) ==>
                    #[trigger] spec_range_next(range) == (range, None::<$t>),
        {
        }
        } // verus!
            };
        }

        step_specs!(u8, axiom_spec_range_next_u8);
        step_specs!(u16, axiom_spec_range_next_u16);
        step_specs!(u32, axiom_spec_range_next_u32);
        step_specs!(u64, axiom_spec_range_next_u64);
        step_specs!(u128, axiom_spec_range_next_u128);
        step_specs!(usize, axiom_spec_range_next_usize);
        step_specs!(i8, axiom_spec_range_next_i8);
        step_specs!(i16, axiom_spec_range_next_i16);
        step_specs!(i32, axiom_spec_range_next_i32);
        step_specs!(i64, axiom_spec_range_next_i64);
        step_specs!(i128, axiom_spec_range_next_i128);
        step_specs!(isize, axiom_spec_range_next_isize);
    }

    pub mod result {
        #![allow(unused_imports)]
        use crate::prelude::*;

        use core::option::Option;
        use core::option::Option::None;
        use core::option::Option::Some;

        use core::result::Result;
        use core::result::Result::Err;
        use core::result::Result::Ok;

        verus! {

////// Add is_variant-style spec functions
pub trait ResultAdditionalSpecFns<T, E> {
    #[allow(non_snake_case)]
    spec fn is_Ok(&self) -> bool;

    #[allow(non_snake_case)]
    spec fn get_Ok_0(&self) -> T;

    #[allow(non_snake_case)]
    spec fn is_Err(&self) -> bool;

    #[allow(non_snake_case)]
    spec fn get_Err_0(&self) -> E;
}

impl<T, E> ResultAdditionalSpecFns<T, E> for Result<T, E> {
    #[verifier(inline)]
    open spec fn is_Ok(&self) -> bool {
        builtin::is_variant(self, "Ok")
    }

    #[verifier(inline)]
    open spec fn get_Ok_0(&self) -> T {
        builtin::get_variant_field(self, "Ok", "0")
    }

    #[verifier(inline)]
    open spec fn is_Err(&self) -> bool {
        builtin::is_variant(self, "Err")
    }

    #[verifier(inline)]
    open spec fn get_Err_0(&self) -> E {
        builtin::get_variant_field(self, "Err", "0")
    }
}

////// Specs for std methods
// is_ok
#[verifier(inline)]
pub open spec fn is_ok<T, E>(result: &Result<T, E>) -> bool {
    builtin::is_variant(result, "Ok")
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(is_ok)]
pub fn ex_result_is_ok<T, E>(result: &Result<T, E>) -> (b: bool)
    ensures
        b == is_ok(result),
{
    result.is_ok()
}

// is_err
#[verifier(inline)]
pub open spec fn is_err<T, E>(result: &Result<T, E>) -> bool {
    builtin::is_variant(result, "Err")
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(is_err)]
pub fn ex_result_is_err<T, E>(result: &Result<T, E>) -> (b: bool)
    ensures
        b == is_err(result),
{
    result.is_err()
}

// as_ref
#[verifier::external_fn_specification]
pub fn as_ref<T, E>(result: &Result<T, E>) -> (r: Result<&T, &E>)
    ensures
        r.is_Ok() <==> result.is_Ok(),
        r.is_Ok() ==> result.get_Ok_0() == r.get_Ok_0(),
        r.is_Err() <==> result.is_Err(),
        r.is_Err() ==> result.get_Err_0() == r.get_Err_0(),
{
    result.as_ref()
}

// unwrap
#[verifier(inline)]
pub open spec fn spec_unwrap<T, E: core::fmt::Debug>(result: Result<T, E>) -> T
    recommends
        result.is_Ok(),
{
    result.get_Ok_0()
}

#[verifier(when_used_as_spec(spec_unwrap))]
#[verifier::external_fn_specification]
pub fn unwrap<T, E: core::fmt::Debug>(result: Result<T, E>) -> (t: T)
    requires
        result.is_Ok(),
    ensures
        t == result.get_Ok_0(),
{
    result.unwrap()
}

// unwrap_err
#[verifier(inline)]
pub open spec fn spec_unwrap_err<T: core::fmt::Debug, E>(result: Result<T, E>) -> E
    recommends
        result.is_Err(),
{
    result.get_Err_0()
}

#[verifier(when_used_as_spec(spec_unwrap_err))]
#[verifier::external_fn_specification]
pub fn unwrap_err<T: core::fmt::Debug, E>(result: Result<T, E>) -> (e: E)
    requires
        result.is_Err(),
    ensures
        e == result.get_Err_0(),
{
    result.unwrap_err()
}

// map
#[verifier::external_fn_specification]
pub fn map<T, E, U, F: FnOnce(T) -> U>(result: Result<T, E>, op: F) -> (mapped_result: Result<U, E>)
    requires
        result.is_ok() ==> op.requires((result.get_Ok_0(),)),
    ensures
        result.is_ok() ==> mapped_result.is_ok() && op.ensures(
            (result.get_Ok_0(),),
            mapped_result.get_Ok_0(),
        ),
        result.is_err() ==> mapped_result == Result::<U, E>::Err(result.get_Err_0()),
{
    result.map(op)
}

// ok
#[verifier(inline)]
pub open spec fn ok<T, E>(result: Result<T, E>) -> Option<T> {
    match result {
        Ok(t) => Some(t),
        Err(_) => None,
    }
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(ok)]
pub fn ex_result_ok<T, E>(result: Result<T, E>) -> (opt: Option<T>)
    ensures
        opt == ok(result),
{
    result.ok()
}

// err
#[verifier(inline)]
pub open spec fn err<T, E>(result: Result<T, E>) -> Option<E> {
    match result {
        Ok(_) => None,
        Err(e) => Some(e),
    }
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(err)]
pub fn ex_result_err<T, E>(result: Result<T, E>) -> (opt: Option<E>)
    ensures
        opt == err(result),
{
    result.err()
}

} // verus!
    }

    #[cfg(feature = "alloc")]
    pub mod vec {
        use crate::prelude::*;
        use builtin::*;

        use alloc::vec::Vec;
        use core::alloc::Allocator;
        use core::option::Option;
        use core::option::Option::None;
        use core::option::Option::Some;

        verus! {

#[verifier(external_type_specification)]
#[verifier(external_body)]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub struct ExVec<T, A: Allocator>(Vec<T, A>);

#[verifier(external_type_specification)]
#[verifier(external_body)]
pub struct ExGlobal(alloc::alloc::Global);

////// Declare 'view' function
pub trait VecAdditionalSpecFns<T> {
    spec fn spec_len(&self) -> nat;

    spec fn spec_index(&self, i: int) -> T
        recommends
            0 <= i < self.spec_len(),
    ;
}

impl<T, A: Allocator> View for Vec<T, A> {
    type V = Seq<T>;

    spec fn view(&self) -> Seq<T>;
}

impl<T, A: Allocator> VecAdditionalSpecFns<T> for Vec<T, A> {
    #[verifier(inline)]
    open spec fn spec_len(&self) -> nat {
        self.view().len()
    }

    #[verifier(inline)]
    open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
}

// TODO this should really be a 'external_fn_specification' function
// but it's difficult to handle vec.index right now because
// it uses more trait polymorphism than we can handle right now.
//
// So this is a bit of a hack, but I'm just manually redirecting
// `vec[i]` to this function here from rust_to_vir_expr.
//
// It's not ideal, but I think it's better than the alternative, which would
// be to have users call some function with a nonstandard name to perform indexing.
/// This is a specification for the indexing operator `vec[i]`
#[verifier::external_body]
pub fn vec_index<T, A: Allocator>(vec: &Vec<T, A>, i: usize) -> (element: &T)
    requires
        i < vec.view().len(),
    ensures
        *element == vec.view().index(i as int),
{
    &vec[i]
}

////// Len (with autospec)
pub open spec fn spec_vec_len<T, A: Allocator>(v: &Vec<T, A>) -> usize;

// This axiom is slightly better than defining spec_vec_len to just be `v@.len() as usize`
// (the axiom also shows that v@.len() is in-bounds for usize)
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_spec_len<A>(v: &Vec<A>)
    ensures
        #[trigger] spec_vec_len(v) == v@.len(),
{
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(spec_vec_len)]
pub fn ex_vec_len<T, A: Allocator>(vec: &Vec<T, A>) -> (len: usize)
    ensures
        len == spec_vec_len(vec),
{
    vec.len()
}

////// Other functions
#[verifier::external_fn_specification]
pub fn ex_vec_new<T>() -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty(),
{
    Vec::<T>::new()
}

#[verifier::external_fn_specification]
pub fn ex_vec_with_capacity<T>(capacity: usize) -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty(),
{
    Vec::<T>::with_capacity(capacity)
}

#[verifier::external_fn_specification]
pub fn ex_vec_reserve<T, A: Allocator>(vec: &mut Vec<T, A>, additional: usize)
    ensures
        vec@ == old(vec)@,
{
    vec.reserve(additional)
}

#[verifier::external_fn_specification]
pub fn ex_vec_push<T, A: Allocator>(vec: &mut Vec<T, A>, value: T)
    ensures
        vec@ == old(vec)@.push(value),
{
    vec.push(value)
}

#[verifier::external_fn_specification]
pub fn ex_vec_pop<T, A: Allocator>(vec: &mut Vec<T, A>) -> (value: Option<T>)
    ensures
        old(vec)@.len() > 0 ==> value == Some(old(vec)@[old(vec)@.len() - 1]) && vec@ == old(
            vec,
        )@.subrange(0, old(vec)@.len() - 1),
        old(vec)@.len() == 0 ==> value == None::<T> && vec@ == old(vec)@,
{
    vec.pop()
}

#[verifier::external_fn_specification]
pub fn ex_vec_append<T, A: Allocator>(vec: &mut Vec<T, A>, other: &mut Vec<T, A>)
    ensures
        vec@ == old(vec)@ + old(other)@,
{
    vec.append(other)
}

/*
// TODO find a way to support this
// This is difficult because of the SliceIndex trait
use std::ops::Index;

#[verifier::external_fn_specification]
pub fn index<T, A: Allocator>(vec: &Vec<T>, i: usize) -> (r: &T)
    requires
        i < vec.len(),
    ensures
        *r == vec[i as int],
{

    vec.index(i)
}
*/

#[verifier::external_fn_specification]
pub fn ex_vec_insert<T, A: Allocator>(vec: &mut Vec<T, A>, i: usize, element: T)
    requires
        i <= old(vec).len(),
    ensures
        vec@ == old(vec)@.insert(i as int, element),
{
    vec.insert(i, element)
}

#[verifier::external_fn_specification]
pub fn ex_vec_remove<T, A: Allocator>(vec: &mut Vec<T, A>, i: usize) -> (element: T)
    requires
        i < old(vec).len(),
    ensures
        element == old(vec)[i as int],
        vec@ == old(vec)@.remove(i as int),
{
    vec.remove(i)
}

#[verifier::external_fn_specification]
pub fn ex_vec_clear<T, A: Allocator>(vec: &mut Vec<T, A>)
    ensures
        vec.view() == Seq::<T>::empty(),
{
    vec.clear()
}

#[verifier::external_fn_specification]
pub fn ex_vec_as_slice<T, A: Allocator>(vec: &Vec<T, A>) -> (slice: &[T])
    ensures
        slice@ == vec@,
{
    vec.as_slice()
}

#[verifier::external_fn_specification]
pub fn ex_vec_split_off<T, A: Allocator + core::clone::Clone>(
    vec: &mut Vec<T, A>,
    at: usize,
) -> (return_value: Vec<T, A>)
    ensures
        vec@ == old(vec)@.subrange(0, at as int),
        return_value@ == old(vec)@.subrange(at as int, old(vec)@.len() as int),
{
    vec.split_off(at)
}

#[verifier::external_fn_specification]
pub fn ex_vec_truncate<T, A: Allocator>(vec: &mut Vec<T, A>, len: usize)
    ensures
        len <= vec.len() ==> vec@ == old(vec)@.subrange(0, len as int),
        len > vec.len() ==> vec@ == old(vec)@,
{
    vec.truncate(len)
}

} // verus!
    }
}

// Re-exports all vstd types, traits, and functions that are commonly used or replace
// regular `core` or `std` definitions.
pub mod prelude {
    pub use builtin::*;
    pub use builtin_macros::*;

    pub use super::map::map;
    pub use super::map::Map;
    pub use super::seq::seq;
    pub use super::seq::Seq;
    pub use super::set::set;
    pub use super::set::Set;
    pub use super::view::*;

    pub use super::string::StrSlice;
    #[cfg(feature = "alloc")]
    pub use super::string::String;

    #[cfg(verus_keep_ghost)]
    pub use super::pervasive::{affirm, arbitrary, proof_from_false, spec_affirm, unreached};

    pub use super::array::ArrayAdditionalExecFns;
    pub use super::array::ArrayAdditionalSpecFns;
    #[cfg(verus_keep_ghost)]
    pub use super::pervasive::FnWithRequiresEnsures;
    pub use super::slice::SliceAdditionalSpecFns;
    #[cfg(verus_keep_ghost)]
    pub use super::std_specs::option::OptionAdditionalFns;
    #[cfg(verus_keep_ghost)]
    pub use super::std_specs::result::ResultAdditionalSpecFns;

    #[cfg(verus_keep_ghost)]
    #[cfg(feature = "alloc")]
    pub use super::std_specs::vec::VecAdditionalSpecFns;

    #[cfg(feature = "alloc")]
    pub use super::pervasive::VecAdditionalExecFns;
}
