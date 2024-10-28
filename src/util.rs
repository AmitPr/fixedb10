use typenum::{IsLessOrEqual, True, Unsigned};

/*
log10(2^256) ≈ 77.06 = 77 decimal digits of precision
log10(2^128) ≈ 38.53 = 38 decimal digits of precision
log10(2^64) ≈ 19.26 = 19 decimal digits of precision
log10(2^32) ≈ 9.63 = 9 decimal digits of precision
*/

// pub trait IsLeq38: Unsigned + IsLessOrEqual<U38, Output = True> {}
// impl<T: Unsigned + IsLessOrEqual<U38, Output = True>> IsLeq38 for T {}

macro_rules! trait_isleq {
    ($trait_name:ident, $bound:ident) => {
        pub trait $trait_name: Unsigned + IsLessOrEqual<typenum::$bound, Output = True> {}
        impl<T: Unsigned + IsLessOrEqual<typenum::$bound, Output = True>> $trait_name for T {}
    };
}

trait_isleq!(IsLeq9, U9);
trait_isleq!(IsLeq19, U19);
trait_isleq!(IsLeq38, U38);
trait_isleq!(IsLeq77, U77);
