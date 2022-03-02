use strum::{EnumString, EnumVariantNames, IntoStaticStr};

#[derive(Debug, EnumString, EnumVariantNames, IntoStaticStr)]
#[strum(serialize_all = "kebab_case")]
pub enum SmtType {
    Generic,
    #[cfg(feature = "boolector")]
    Boolector,
    #[cfg(feature = "z3")]
    Z3,
}
