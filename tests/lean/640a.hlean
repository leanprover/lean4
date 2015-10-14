section
  parameter {A : Type}
  definition relation : A → A → Type := λa b, a = b
  local abbreviation R := relation
  local abbreviation S [parsing_only] := relation
  variable {a : A}
  check relation a a
  check R a a
  check S a a
end

section
  parameter {A : Type}
  definition relation' : A → A → Type := λa b, a = b
  local infix ` ~1 `:50 := relation'
  local infix [parsing_only] ` ~2 `:50 := relation'
  variable {a : A}
  check relation' a a
  check a ~1 a
  check a ~2 a
end

section
  parameter {A : Type}
  definition relation'' : A → A → Type := λa b, a = b
  local infix [parsing_only] ` ~2 `:50 := relation''
  variable {a : A}
  check relation'' a a
  check a ~2 a
  check a ~2 a
end

section
  parameter {A : Type}
  definition relation''' : A → A → Type := λa b, a = b
  local abbreviation S [parsing_only] := relation'''
  variable {a : A}
  check relation''' a a
  check S a a
end
