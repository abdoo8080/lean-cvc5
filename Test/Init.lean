import cvc5



namespace cvc5.Test

def assertEq [Repr α] [BEq α] (lft rgt : α) (hint := "") : IO Unit := do
  if lft != rgt then
    let pref := if hint.isEmpty then "" else s!"[{hint}] "
    IO.eprintln s!"\
{pref}comparison failed: `{reprPrec lft 1}` is different from `{reprPrec rgt 1}\
      "
