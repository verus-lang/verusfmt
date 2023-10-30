verus! {

#[verifier(external_body)]
pub fn func1() {
}

pub fn func2() {
}

#[verifier(external_body)]
pub fn func3() {
}

impl cfg_alice {
    #[verifier(external_body)]
    pub fn func1() {
    }

    pub fn func2() {
    }

    #[verifier(external_body)]
    pub fn func3() {
    }
}

} // verus!
