#[cfg(test)]
mod tests {
    use std::{
        ops::Bound::{Excluded, Included},
        str::FromStr,
    };

    use jiff::{civil::date, tz::TimeZone, Zoned};
    use jiff_cron::{Schedule, TimeUnitSpec};

    #[test]
    fn test_readme() {
        let expression = "0   30   9,12,15     1,15       May-Aug  Mon,Wed,Fri  2018/2";
        let schedule = Schedule::from_str(expression).unwrap();
        println!("README: Upcoming fire times for '{expression}':");
        for datetime in schedule.upcoming(TimeZone::UTC).take(10) {
            println!("README: -> {datetime}");
        }
    }

    #[test]
    fn test_anything_goes() {
        let expression = "* * * * * * *";
        let schedule = Schedule::from_str(expression).unwrap();
        println!("All stars: Upcoming fire times for '{expression}':");
        for datetime in schedule.upcoming(TimeZone::UTC).take(10) {
            println!("All stars: -> {datetime}");
        }
    }

    #[test]
    fn test_parse_with_year() {
        let expression = "1 2 3 4 5 6 2015";
        assert!(Schedule::from_str(expression).is_ok());
    }

    #[test]
    fn test_parse_with_seconds_list() {
        let expression = "1,30,40 2 3 4 5 Mon-Fri";
        assert!(Schedule::from_str(expression).is_ok());
    }

    #[test]
    fn test_parse_with_lists() {
        let expression = "1 2,17,51 1-3,6,9-11 4,29 2,3,7 Tues";
        let schedule = Schedule::from_str(expression).unwrap();
        let mut date = Zoned::now().with_time_zone(TimeZone::UTC);
        println!("Fire times for {expression}:");
        for _ in 0..20 {
            date = schedule.after(&date).next().expect("No further dates!");
            println!("-> {date}");
        }
    }

    #[test]
    fn test_upcoming_iterator() {
        let expression = "0 2,17,51 1-3,6,9-11 4,29 2,3,7 Wed";
        let schedule = Schedule::from_str(expression).unwrap();
        println!("Upcoming fire times for '{expression}':");
        for datetime in schedule.upcoming(TimeZone::UTC).take(12) {
            println!("-> {datetime}");
        }
    }

    #[test]
    fn test_parse_without_year() {
        let expression = "1 2 3 4 5 6";
        assert!(Schedule::from_str(expression).is_ok());
    }

    #[test]
    fn test_parse_too_many_fields() {
        let expression = "1 2 3 4 5 6 7 8 9 2019";
        assert!(Schedule::from_str(expression).is_err());
    }

    #[test]
    fn test_not_enough_fields() {
        let expression = "1 2 3 2019";
        assert!(Schedule::from_str(expression).is_err());
    }

    #[test]
    fn test_next_utc() {
        let expression = "1 2 3 4 10 Fri";
        let schedule = Schedule::from_str(expression).unwrap();
        let next = schedule
            .upcoming(TimeZone::UTC)
            .next()
            .expect("There was no upcoming fire time.");
        println!("Next fire time: {next}");
    }

    #[test]
    fn test_prev_utc() {
        let expression = "1 2 3 4 10 Fri";
        let schedule = Schedule::from_str(expression).unwrap();
        let prev = schedule
            .upcoming(TimeZone::UTC)
            .next_back()
            .expect("There was no previous upcoming fire time.");
        println!("Previous fire time: {prev}");
    }

    #[test]
    fn test_yearly() {
        let expression = "@yearly";
        let schedule = Schedule::from_str(expression).expect("Failed to parse @yearly.");
        let starting_date = date(2017, 6, 15)
            .at(14, 29, 36, 0)
            .to_zoned(TimeZone::UTC)
            .unwrap();
        let mut events = schedule.after(&starting_date);
        assert_eq!(
            date(2018, 1, 1)
                .at(0, 0, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
        assert_eq!(
            date(2019, 1, 1)
                .at(0, 0, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
        assert_eq!(
            date(2020, 1, 1)
                .at(0, 0, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
    }

    #[test]
    fn test_monthly() {
        let expression = "@monthly";
        let schedule = Schedule::from_str(expression).expect("Failed to parse @monthly.");
        let starting_date = date(2017, 10, 15)
            .at(14, 29, 36, 0)
            .to_zoned(TimeZone::UTC)
            .unwrap();
        let mut events = schedule.after(&starting_date);
        assert_eq!(
            date(2017, 11, 1)
                .at(0, 0, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
        assert_eq!(
            date(2017, 12, 1)
                .at(0, 0, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
        assert_eq!(
            date(2018, 1, 1)
                .at(0, 0, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
    }

    #[test]
    fn test_weekly() {
        let expression = "@weekly";
        let schedule = Schedule::from_str(expression).expect("Failed to parse @weekly.");
        let starting_date = date(2016, 12, 23)
            .at(14, 29, 36, 0)
            .to_zoned(TimeZone::UTC)
            .unwrap();
        let mut events = schedule.after(&starting_date);
        assert_eq!(
            date(2016, 12, 25)
                .at(0, 0, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
        assert_eq!(
            date(2017, 1, 1)
                .at(0, 0, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
        assert_eq!(
            date(2017, 1, 8)
                .at(0, 0, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
    }

    #[test]
    fn test_daily() {
        let expression = "@daily";
        let schedule = Schedule::from_str(expression).expect("Failed to parse @daily.");
        let starting_date = date(2016, 12, 23)
            .at(14, 29, 36, 0)
            .to_zoned(TimeZone::UTC)
            .unwrap();
        let mut events = schedule.after(&starting_date);
        assert_eq!(
            date(2016, 12, 24)
                .at(0, 0, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
        assert_eq!(
            date(2016, 12, 25)
                .at(0, 0, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
        assert_eq!(
            date(2016, 12, 26)
                .at(0, 0, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
    }

    #[test]
    fn test_hourly() {
        let expression = "@hourly";
        let schedule = Schedule::from_str(expression).expect("Failed to parse @hourly.");
        let starting_date = date(2017, 2, 25)
            .at(22, 29, 36, 0)
            .to_zoned(TimeZone::UTC)
            .unwrap();
        let mut events = schedule.after(&starting_date);
        assert_eq!(
            date(2017, 2, 25)
                .at(23, 0, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
        assert_eq!(
            date(2017, 2, 26)
                .at(0, 0, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
        assert_eq!(
            date(2017, 2, 26)
                .at(1, 0, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
    }

    #[test]
    fn test_step_schedule() {
        let expression = "0/20 0/5 0 1 1 * *";
        let schedule = Schedule::from_str(expression).expect("Failed to parse expression.");
        let starting_date = date(2017, 6, 15)
            .at(14, 29, 36, 0)
            .to_zoned(TimeZone::UTC)
            .unwrap();
        let mut events = schedule.after(&starting_date);

        assert_eq!(
            date(2018, 1, 1)
                .at(0, 0, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
        assert_eq!(
            date(2018, 1, 1)
                .at(0, 0, 20, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
        assert_eq!(
            date(2018, 1, 1)
                .at(0, 0, 40, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );

        assert_eq!(
            date(2018, 1, 1)
                .at(0, 5, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
        assert_eq!(
            date(2018, 1, 1)
                .at(0, 5, 20, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
        assert_eq!(
            date(2018, 1, 1)
                .at(0, 5, 40, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );

        assert_eq!(
            date(2018, 1, 1)
                .at(0, 10, 0, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
        assert_eq!(
            date(2018, 1, 1)
                .at(0, 10, 20, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
        assert_eq!(
            date(2018, 1, 1)
                .at(0, 10, 40, 0)
                .to_zoned(TimeZone::UTC)
                .unwrap(),
            events.next().unwrap()
        );
    }

    #[test]
    fn test_invalid_step() {
        let expression = "0/0 * * * *";
        assert!(Schedule::from_str(expression).is_err());
    }

    #[test]
    fn test_time_unit_spec_years() {
        let expression = "* * * * * * 2015-2044";
        let schedule = Schedule::from_str(expression).expect("Failed to parse expression.");

        // Membership
        assert!(schedule.years().includes(2031));
        assert!(!schedule.years().includes(1969));

        // Number of years specified
        assert_eq!(30, schedule.years().count());

        // Iterator
        let mut years_iter = schedule.years().iter();
        assert_eq!(Some(2015), years_iter.next());
        assert_eq!(Some(2016), years_iter.next());
        // ...

        // Range Iterator
        let mut five_year_plan = schedule.years().range((Included(2017), Excluded(2017 + 5)));
        assert_eq!(Some(2017), five_year_plan.next());
        assert_eq!(Some(2018), five_year_plan.next());
        assert_eq!(Some(2019), five_year_plan.next());
        assert_eq!(Some(2020), five_year_plan.next());
        assert_eq!(Some(2021), five_year_plan.next());
        assert_eq!(None, five_year_plan.next());
    }

    #[test]
    fn test_time_unit_spec_months() {
        let expression = "* * * * 5-8 * *";
        let schedule = Schedule::from_str(expression).expect("Failed to parse expression.");

        // Membership
        assert!(!schedule.months().includes(4));
        assert!(schedule.months().includes(6));

        // Iterator
        let mut summer = schedule.months().iter();
        assert_eq!(Some(5), summer.next());
        assert_eq!(Some(6), summer.next());
        assert_eq!(Some(7), summer.next());
        assert_eq!(Some(8), summer.next());
        assert_eq!(None, summer.next());

        // Number of months specified
        assert_eq!(4, schedule.months().count());

        // Range Iterator
        let mut first_half_of_summer = schedule.months().range((Included(1), Included(6)));
        assert_eq!(Some(5), first_half_of_summer.next());
        assert_eq!(Some(6), first_half_of_summer.next());
        assert_eq!(None, first_half_of_summer.next());
    }

    #[test]
    fn test_time_unit_spec_days_of_month() {
        let expression = "* * * 1,15 * * *";
        let schedule = Schedule::from_str(expression).expect("Failed to parse expression.");
        // Membership
        assert!(schedule.days_of_month().includes(1));
        assert!(!schedule.days_of_month().includes(7));

        // Iterator
        let mut paydays = schedule.days_of_month().iter();
        assert_eq!(Some(1), paydays.next());
        assert_eq!(Some(15), paydays.next());
        assert_eq!(None, paydays.next());

        // Number of years specified
        assert_eq!(2, schedule.days_of_month().count());

        // Range Iterator
        let mut mid_month_paydays = schedule.days_of_month().range((Included(5), Included(25)));
        assert_eq!(Some(15), mid_month_paydays.next());
        assert_eq!(None, mid_month_paydays.next());
    }

    #[test]
    fn test_first_ordinals_not_in_set_1() {
        let schedule = "0 0/10 * * * * *".parse::<Schedule>().unwrap();
        let start_time_1 = date(2017, 10, 24)
            .at(0, 0, 59, 0)
            .to_zoned(TimeZone::UTC)
            .unwrap();
        let next_time_1 = schedule.after(&start_time_1).next().unwrap();

        let start_time_2 = date(2017, 10, 24)
            .at(0, 1, 0, 0)
            .to_zoned(TimeZone::UTC)
            .unwrap();
        let next_time_2 = schedule.after(&start_time_2).next().unwrap();
        assert_eq!(next_time_1, next_time_2);
    }

    #[test]
    fn test_first_ordinals_not_in_set_2() {
        let schedule_1 = "00 00 23 * * * *".parse::<Schedule>().unwrap();
        let start_time = date(2018, 11, 15)
            .at(22, 30, 0, 0)
            .to_zoned(TimeZone::UTC)
            .unwrap();
        let next_time_1 = schedule_1.after(&start_time).next().unwrap();

        let schedule_2 = "00 00 * * * * *".parse::<Schedule>().unwrap();
        let next_time_2 = schedule_2.after(&start_time).next().unwrap();
        assert_eq!(next_time_1, next_time_2);
    }

    #[test]
    fn test_period_values_any_dom() {
        let schedule = Schedule::from_str("0 0 0 ? * *").unwrap();
        let schedule_tz = TimeZone::get("Europe/London").unwrap();
        let dt = date(2020, 9, 17)
            .at(0, 0, 0, 0)
            .to_zoned(schedule_tz.clone())
            .unwrap();

        let mut schedule_iter = schedule.after(&dt);
        assert_eq!(
            date(2020, 9, 18)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz)
                .unwrap(),
            schedule_iter.next().unwrap()
        );
    }

    #[test]
    fn test_period_values_any_dow() {
        let schedule = Schedule::from_str("0 0 0 * * ?").unwrap();
        let schedule_tz = TimeZone::get("Europe/London").unwrap();
        let dt = date(2020, 9, 17)
            .at(0, 0, 0, 0)
            .to_zoned(schedule_tz.clone())
            .unwrap();

        let mut schedule_iter = schedule.after(&dt);
        assert_eq!(
            date(2020, 9, 18)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            schedule_iter.next().unwrap()
        );
    }

    #[test]
    fn test_period_values_all_seconds() {
        let schedule = Schedule::from_str("*/17 * * * * ?").unwrap();
        let schedule_tz = TimeZone::get("Europe/London").unwrap();
        let dt = date(2020, 1, 1)
            .at(0, 0, 0, 0)
            .to_zoned(schedule_tz.clone())
            .unwrap();

        let mut schedule_iter = schedule.after(&dt);
        let expected_values = vec![
            date(2020, 1, 1)
                .at(0, 0, 17, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 1)
                .at(0, 0, 34, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 1)
                .at(0, 0, 51, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 1)
                .at(0, 1, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 1)
                .at(0, 1, 17, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 1)
                .at(0, 1, 34, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
        ];
        for expected_value in expected_values.iter() {
            assert_eq!(*expected_value, schedule_iter.next().unwrap());
        }
    }

    #[test]
    fn test_period_values_range() {
        let schedule = Schedule::from_str("0 0 0 1 1-4/2 ?").unwrap();
        let schedule_tz = TimeZone::get("Europe/London").unwrap();
        let dt = date(2020, 1, 1)
            .at(0, 0, 0, 0)
            .to_zoned(schedule_tz.clone())
            .unwrap();
        let mut schedule_iter = schedule.after(&dt);
        let expected_values = vec![
            date(2020, 3, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2021, 1, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2021, 3, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2022, 1, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
        ];
        for expected_value in expected_values.iter() {
            assert_eq!(*expected_value, schedule_iter.next().unwrap());
        }
    }

    #[test]
    fn test_period_values_range_hours() {
        let schedule = Schedule::from_str("0 0 10-12/2 * * ?").unwrap();
        let schedule_tz = TimeZone::get("Europe/London").unwrap();
        let dt = date(2020, 1, 1)
            .at(0, 0, 0, 0)
            .to_zoned(schedule_tz.clone())
            .unwrap();
        let mut schedule_iter = schedule.after(&dt);
        let expected_values = vec![
            date(2020, 1, 1)
                .at(10, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 1)
                .at(12, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 2)
                .at(10, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 2)
                .at(12, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
        ];
        for expected_value in expected_values.iter() {
            assert_eq!(*expected_value, schedule_iter.next().unwrap());
        }
    }

    #[test]
    fn test_period_values_range_days() {
        let schedule = Schedule::from_str("0 0 0 1-31/10 * ?").unwrap();
        let schedule_tz = TimeZone::get("Europe/London").unwrap();
        let dt = date(2020, 1, 1)
            .at(0, 0, 0, 0)
            .to_zoned(schedule_tz.clone())
            .unwrap();
        let mut schedule_iter = schedule.after(&dt);
        let expected_values = vec![
            date(2020, 1, 11)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 21)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 31)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 2, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 2, 11)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 2, 21)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 3, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
        ];
        for expected_value in expected_values.iter() {
            assert_eq!(*expected_value, schedule_iter.next().unwrap());
        }
    }

    #[test]
    fn test_period_values_range_months() {
        let schedule = Schedule::from_str("0 0 0 1 January-June/1 *").unwrap();
        let schedule_tz = TimeZone::get("Europe/London").unwrap();
        let dt = date(2020, 1, 1)
            .at(0, 0, 0, 0)
            .to_zoned(schedule_tz.clone())
            .unwrap();
        let mut schedule_iter = schedule.after(&dt);
        let expected_values = vec![
            date(2020, 2, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 3, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 4, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 5, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 6, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2021, 1, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
        ];
        for expected_value in expected_values.iter() {
            assert_eq!(*expected_value, schedule_iter.next().unwrap());
        }
    }

    #[test]
    fn test_period_values_range_years() {
        let schedule = Schedule::from_str("0 0 0 1 1 ? 2020-2040/10").unwrap();
        let schedule_tz = TimeZone::get("Europe/London").unwrap();
        let dt = date(2020, 1, 1)
            .at(0, 0, 0, 0)
            .to_zoned(schedule_tz.clone())
            .unwrap();
        let mut schedule_iter = schedule.after(&dt);
        let expected_values = [
            date(2030, 1, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2040, 1, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
        ];
        for expected_value in expected_values.iter() {
            assert_eq!(*expected_value, schedule_iter.next().unwrap());
        }
    }

    #[test]
    fn test_period_values_point() {
        let schedule = Schedule::from_str("0 */21 * * * ?").unwrap();
        let schedule_tz = TimeZone::get("Europe/London").unwrap();
        let dt = date(2020, 1, 1)
            .at(0, 0, 0, 0)
            .to_zoned(schedule_tz.clone())
            .unwrap();
        let mut schedule_iter = schedule.after(&dt);
        let expected_values = vec![
            date(2020, 1, 1)
                .at(0, 21, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 1)
                .at(0, 42, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 1)
                .at(1, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 1)
                .at(1, 21, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 1)
                .at(1, 42, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 1)
                .at(2, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 1)
                .at(2, 21, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2020, 1, 1)
                .at(2, 42, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
        ];
        for expected_value in expected_values.iter() {
            assert_eq!(*expected_value, schedule_iter.next().unwrap());
        }
    }

    #[test]
    fn test_period_values_named_range() {
        let schedule = Schedule::from_str("0 0 0 1 January-April/2 ?").unwrap();
        let schedule_tz = TimeZone::get("Europe/London").unwrap();
        let dt = date(2020, 1, 1)
            .at(0, 0, 0, 0)
            .to_zoned(schedule_tz.clone())
            .unwrap();
        let mut schedule_iter = schedule.after(&dt);
        let expected_values = vec![
            date(2020, 3, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2021, 1, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2021, 3, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
            date(2022, 1, 1)
                .at(0, 0, 0, 0)
                .to_zoned(schedule_tz.clone())
                .unwrap(),
        ];
        for expected_value in expected_values.iter() {
            assert_eq!(*expected_value, schedule_iter.next().unwrap());
        }
    }

    #[test]
    fn test_is_all() {
        let schedule = Schedule::from_str("0-59 * 0-23 ?/2 1,2-4 ? *").unwrap();
        assert!(schedule.years().is_all());
        assert!(!schedule.days_of_month().is_all());
        assert!(schedule.days_of_week().is_all());
        assert!(!schedule.months().is_all());
        assert!(schedule.hours().is_all());
        assert!(schedule.minutes().is_all());
        assert!(schedule.seconds().is_all());
    }

    #[test]
    fn test_includes() {
        let schedule = Schedule::from_str("0 0 0 2-31/10 * ?").unwrap();
        let schedule_tz = TimeZone::get("Europe/London").unwrap();
        let included = date(2020, 1, 12)
            .at(0, 0, 0, 0)
            .to_zoned(schedule_tz.clone())
            .unwrap();
        let not_included = date(2020, 1, 11)
            .at(0, 0, 0, 0)
            .to_zoned(schedule_tz.clone())
            .unwrap();
        assert!(schedule.includes(included));
        assert!(!schedule.includes(not_included));
    }
}
