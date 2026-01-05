* `do` notation now always requires `Pure`
* Some type inference regressions are expected; often these are in conjunction with dot notation.
* Dependent facts about a `let mut` that is constant throughout a loop are no longer accessible in a loop body.
