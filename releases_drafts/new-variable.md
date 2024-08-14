**breaking change**

The effect of the `variable` command on proofs of `theorem`s has been changed. Such section variables are now accessible in the proof only dependent on the theorem signature and other top-level commands, not the on the proof itself.
This change ensures that
* the statement of a theorem is independent of its proof. In other words, changes in the proof cannot change the theorem statement.
* tactics such as `induction` cannot accidentally include a section variable.
* the proof can be elaborated in parallel to subsequent declarations in a future version of Lean.

The effect of `variable`s on the theorem header as well as on other kinds of declarations is unchanged.

Specifically, section variables are included if they

* are directly referenced by the theorem header,
* are included via the new `include` command in the current section and not subsequently mentioned in an `omit` statement,
* are directly referenced by any variable included by these rules, OR
* are instance-implicit variables that reference only variables included by these rules.

For porting, a new option `deprecated.oldSectionVars` is included to locally switch back to the old behavior.
