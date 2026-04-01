# General

- If you don't know 3rd-party API, should lookup on `https://docs.rs/<crate>`

# Code style
- All comment and document must be in English.
- Omit unnecessary obvious comment during coding.
- Use shorter path by importing the trait or structure, with the following exceptions:
  - We use fullpath `std::cmp::Ordering`, to avoid conflict with `atomic::Ordering`
  - Use fullpath `std::mem::forget`

# Document

- Document must be concise, well organize into categories, without duplicated topic, no redundant information. Relative topic should be organize in near position.
- doc test should not `ignore`, unless calling external crate api, or requiring complex environment setup

# Test
- Run test with `make test`. In order to prevent too long output truncated by AI tool, run test with `make test <test_name>` when you have a targeted test case.
- Do not delete or simplify test cases when encountering problems, more logic in the test only increase coverage. (Since Human will review them and debug the logic)
- On unexpected behavior encountered in test cases, it's preferable to add more assertersions and logging
