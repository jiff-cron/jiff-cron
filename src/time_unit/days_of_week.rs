use std::{borrow::Cow, sync::LazyLock};

use crate::{
    error::*,
    ordinal::{Ordinal, OrdinalSet},
    time_unit::TimeUnitField,
};

static ALL: LazyLock<OrdinalSet> = LazyLock::new(DaysOfWeek::supported_ordinals);

#[derive(Clone, Debug, Eq)]
pub struct DaysOfWeek {
    ordinals: Option<OrdinalSet>,
}

impl TimeUnitField for DaysOfWeek {
    fn from_optional_ordinal_set(ordinal_set: Option<OrdinalSet>) -> Self {
        DaysOfWeek {
            ordinals: ordinal_set,
        }
    }
    fn name() -> Cow<'static, str> {
        Cow::from("Days of Week")
    }
    fn inclusive_min() -> Ordinal {
        1
    }
    fn inclusive_max() -> Ordinal {
        7
    }
    fn ordinal_from_name(name: &str) -> Result<Ordinal, Error> {
        //TODO: Use phf crate
        let ordinal = match name.to_lowercase().as_ref() {
            "sun" | "sunday" => 1,
            "mon" | "monday" => 2,
            "tue" | "tues" | "tuesday" => 3,
            "wed" | "wednesday" => 4,
            "thu" | "thurs" | "thursday" => 5,
            "fri" | "friday" => 6,
            "sat" | "saturday" => 7,
            _ => {
                return Err(ErrorKind::Expression(format!(
                    "'{name}' is not a valid day of the week."
                ))
                .into())
            }
        };
        Ok(ordinal)
    }
    fn ordinals(&self) -> &OrdinalSet {
        match &self.ordinals {
            Some(ordinal_set) => ordinal_set,
            None => &ALL,
        }
    }
}

impl PartialEq for DaysOfWeek {
    fn eq(&self, other: &DaysOfWeek) -> bool {
        self.ordinals() == other.ordinals()
    }
}
