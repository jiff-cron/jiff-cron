use std::{borrow::Cow, sync::LazyLock};

use phf::phf_map;

use crate::{
    error::*,
    ordinal::{Ordinal, OrdinalSet},
    time_unit::TimeUnitField,
};

static MONTH_MAP: phf::Map<&'static str, Ordinal> = phf_map! {
    "jan" => 1,
    "january" => 1,
    "feb" => 2,
    "february" => 2,
    "mar" => 3,
    "march" => 3,
    "apr" => 4,
    "april" => 4,
    "may" => 5,
    "jun" => 6,
    "june" => 6,
    "jul" => 7,
    "july" => 7,
    "aug" => 8,
    "august" => 8,
    "sep" => 9,
    "september" => 9,
    "oct" => 10,
    "october" => 10,
    "nov" => 11,
    "november" => 11,
    "dec" => 12,
    "december" => 12,
};

static ALL: LazyLock<OrdinalSet> = LazyLock::new(Months::supported_ordinals);

#[derive(Clone, Eq, Debug)]
pub struct Months {
    ordinals: Option<OrdinalSet>,
}

impl TimeUnitField for Months {
    fn from_optional_ordinal_set(ordinal_set: Option<OrdinalSet>) -> Self {
        Months {
            ordinals: ordinal_set,
        }
    }
    fn name() -> Cow<'static, str> {
        Cow::from("Months")
    }
    fn inclusive_min() -> Ordinal {
        1
    }
    fn inclusive_max() -> Ordinal {
        12
    }
    fn ordinal_from_name(name: &str) -> Result<Ordinal, Error> {
        MONTH_MAP
            .get(name.to_lowercase().as_ref())
            .copied()
            .ok_or_else(|| {
                ErrorKind::Expression(format!("'{name}' is not a valid month name.")).into()
            })
    }
    fn ordinals(&self) -> &OrdinalSet {
        match &self.ordinals {
            Some(ordinal_set) => ordinal_set,
            None => &ALL,
        }
    }
}

impl PartialEq for Months {
    fn eq(&self, other: &Months) -> bool {
        self.ordinals() == other.ordinals()
    }
}
