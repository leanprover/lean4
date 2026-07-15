set_option doc.verso true

/-!
This test checks that header nesting rules are enforced within and across Verso module docs.

First, within.

# A
## B
### C
-/


/-- error: Incorrect header nesting: expected at most `###` but got `####` -/
#guard_msgs in
/-!
# A
## B
#### C
-/

/-- error: Incorrect header nesting: expected at most `##` but got `###` -/
#guard_msgs in
/-!
# A
## B
### C
#### D
# E
### F
-/

/-!
Now, check between blocks.

# A
## B
-/

/-!
### C
-/

/-- error: Incorrect header nesting: expected at most `####` but got `#####` -/
#guard_msgs in
/-!
##### D
-/

/-!
# A
-/

/-- error: Incorrect header nesting: expected at most `##` but got `#####` -/
#guard_msgs in
/-!
##### B
-/
