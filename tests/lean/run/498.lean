structure ParamType where
  /-- Name of the type, used when displaying the help. -/
  name    : String
  /-- Function to check whether a value conforms to the type. -/
  isValid : String → Bool

structure Flag where
  /-- Designates `x` in `-x`. -/
  shortName?  : Option String := none
  /-- Designates `x` in `--x`. -/
  longName    : String
  /-- Description that is displayed in the help. -/
  description : String
  /--
  Type according to which the parameter is validated.
  `Unit` is used to designate flags without a parameter.
  -/
  type        : ParamType

structure InputFlag where
  /-- Flag name input by the user. -/
  name    : String
  /-- Whether the flag input by the user was a short one. -/
  isShort : Bool

instance : ToString InputFlag where
  toString f :=
    let pre := if f.isShort then "-" else "--"
    s!"{pre}{f.name}"

structure Arg where
  /- Name that is displayed in the help. -/
  name        : String
  /- Description that is displayed in the help. -/
  description : String
  /- Description that is displayed in the help. -/
  type        : ParamType

-- (deterministic) timeout at 'whnf', maximum number of heartbeats (50000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)
inductive Kind
| unknownFlag
  (inputFlag : InputFlag)
  (msg       : String :=
    s!"Unknown flag `{inputFlag}`.")
| missingFlagArg
  (flag      : Flag)
  (inputFlag : InputFlag)
  (msg       : String :=
    s!"Missing argument for flag `{inputFlag}`.")
| duplicateFlag
  (flag      : Flag)
  (inputFlag : InputFlag)
  (msg       : String :=
    let complementaryName? : Option String := OptionM.run do
      if inputFlag.isShort then
        s!" (`--{flag.longName}`)"
      else
        s!" (`-{← flag.shortName?}`)"
    s!"Duplicate flag `{inputFlag}`.")
| redundantFlagArg
  (flag       : Flag)
  (inputFlag  : InputFlag)
  (inputValue : String)
  (msg        : String :=
    s!"Redundant argument `{inputValue}` for flag `{inputFlag}` that takes no arguments.")
| invalidFlagType
  (flag       : Flag)
  (inputFlag  : InputFlag)
  (inputValue : String)
  (msg        : String :=
    s!"Invalid type of argument `{inputValue}` for flag `{inputFlag} : {flag.type.name}`.")
| missingPositionalArg
  (arg : Arg)
  (msg : String :=
    s!"Missing positional argument `<{arg.name}>.`")
| invalidPositionalArgType
  (arg      : Arg)
  (inputArg : String)
  (msg      : String :=
    s!"Invalid type of argument `{inputArg}` for positional argument `<{arg.name} : {arg.type.name}>`.")
| redundantPositionalArg
  (inputArg : String)
  (msg      : String :=
    s!"Redundant positional argument `{inputArg}`.")
| invalidVariableArgType
  (arg      : Arg)
  (inputArg : String)
  (msg      : String :=
    s!"Invalid type of argument `{inputArg}` for variable argument `<{arg.name} : {arg.type.name}>...`.")

#check @Kind.missingFlagArg.inj
