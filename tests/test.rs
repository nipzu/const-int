use const_int::{U256, foo};

#[test]
fn test() {
    const A: U256 = foo(U256::one(), U256::zero());
    assert_eq!(A, U256::one());
}