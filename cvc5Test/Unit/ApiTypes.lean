import cvc5Test.Init

/-! # Black box testing of the `Op` type

- <https://github.com/cvc5/cvc5/blob/main/test/unit/api/cpp/api_types_black.cpp>
-/

namespace cvc5.Test

test![TestApiTypes, printEnum] do
  let expected :=
    "LT ARRAY_SORT RTZ UNKNOWN_REASON literals preprocess full enum smt_lib_2_6 lfsc"
  let mut string := s!"\
    {Kind.LT} {SortKind.ARRAY_SORT} {RoundingMode.ROUND_TOWARD_ZERO} \
    {UnknownExplanation.UNKNOWN_REASON} {BlockModelsMode.LITERALS} \
    {LearnedLitType.PREPROCESS} {ProofComponent.FULL} {FindSynthTarget.ENUM} \
    {InputLanguage.SMT_LIB_2_6} {ProofFormat.LFSC}\
  "
  assertEq string expected
