// Lean compiler output
// Module: init.lean.parser.parsec
// Imports: init.data.tostring init.data.string.basic init.data.list.basic init.control.except init.data.repr init.lean.name init.data.dlist init.control.monadfail init.control.combinators
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_Lean_Parser_MonadParsec_foldlAux___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_notFollowedBySat___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil1___spec__3(obj*);
obj* l_Lean_Parser_Parsec_Message_toString___rarg___closed__3;
uint8 l_List_hasDecEq___main___at_Lean_Parser_Parsec_Message_text___spec__1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many_x_27___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_HasMonadLift(obj*);
uint32 l_String_Iterator_curr___main(obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_ExceptT_lift___rarg___closed__1;
obj* l_Lean_Parser_ParsecT_labels___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__5(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux___main(obj*);
obj* l_Lean_Parser_Lean_Parser_MonadParsec(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux___main___boxed(obj*);
obj* l_Lean_Parser_monadParsecTrans___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ensure___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_notFollowedBy___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldrAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_runFrom___boxed(obj*);
obj* l_Lean_Parser_ParsecT_run___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_parseWithEoi___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_2__takeAux___boxed(obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_num___spec__3(obj*);
obj* l_Lean_Parser_ParsecT_pure(obj*);
obj* l_Lean_Parser_MonadParsec_cond___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldr___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_bind___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_monadParsecTrans___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_parse(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_try___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_eps___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_3__mkStringResult___rarg(obj*, obj*);
obj* l___private_init_lean_parser_parsec_2__takeAux___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_str___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___at_Lean_Parser_MonadParsec_whitespace___spec__2___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_failure___boxed(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_String_toNat(obj*);
obj* l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_upper___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_orelse___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__11(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_notFollowedBy(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldl___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__5(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_pos___rarg___lambda__1(obj*);
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1___rarg___lambda__1(obj*);
uint8 l_String_isEmpty(obj*);
obj* l_Lean_Parser_ParsecT_parseWithLeftOver___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_take___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_MonadParsec_longestMatch___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_labels___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_label___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_String_intercalate(obj*, obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithLeftOver___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_lookahead___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_hidden___boxed(obj*, obj*, obj*);
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_String_lineColumn(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeUntil1___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_parseWithEoi___rarg___lambda__2(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_MonadParsec_foldrAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
uint8 l_Char_isLower(uint32);
obj* l_Lean_Parser_MonadParsec_eoiError(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__6(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_any(obj*, obj*);
obj* l_Lean_Parser_Lean_Parser_MonadParsec___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_labels___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_labelsMkRes(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldrAux___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_eps___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Alternative___boxed(obj*);
obj* l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_num___spec__2(obj*, obj*, obj*);
obj* l_Lean_Parser_Parsec_HasLift(obj*);
obj* l_Lean_Parser_MonadParsec_lookahead___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_SepBy___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_longestMatch(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_fix___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Lean_Parser_MonadParsec___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___at_Lean_Parser_MonadParsec_whitespace___spec__2___boxed(obj*);
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_MonadExcept___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_error___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_SepBy___boxed(obj*, obj*);
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_num___spec__1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ensure(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_leftOver___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_HasMonadLift___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_ParsecT_parseWithEoi___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Char_isAlpha(uint32);
obj* l_Lean_Parser_MonadParsec_takeWhile1___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_fixAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux___main___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeUntil___boxed(obj*, obj*);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_MonadParsec_longestMatch___spec__1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_MonadParsec_takeUntil___spec__1___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_ParsecT_labelsMkRes___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_bind___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_3__mkStringResult___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_try___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_cond___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_notFollowedBySat___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_any___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_strCore___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ch___rarg___lambda__1(obj*, uint32, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_num___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_num___rarg___closed__1;
obj* l___private_init_lean_parser_parsec_2__takeAux(obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_num___spec__3___boxed(obj*);
obj* l_Lean_Parser_Parsec_Message_toString___rarg(obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___main___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_pure___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_error___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_unexpected___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_try___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_sepBy1___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_lower(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_takeUntil1___spec__2___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__8___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_parseWithEoi___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Alternative___rarg___lambda__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__6(obj*, obj*, obj*, obj*);
obj* l_id___rarg___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_sepBy1___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_upper___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_digit___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__3(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_longestMatch___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1___closed__2;
obj* l_Lean_Parser_MonadParsec_digit___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_try___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_satisfy___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_2__takeAux___main___boxed(obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__13___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldrAux(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Format_be___main___closed__1;
obj* l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_unexpectedAt(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_sepBy1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_observing___boxed(obj*, obj*);
obj* l_Lean_Parser_monadParsecTrans___rarg___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Parsec_parse___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_strCore___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil1___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_notFollowedBy___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldr___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeUntil___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Alternative(obj*);
obj* l_Lean_Parser_MonadParsec_hidden___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_try___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Parsec_Message_text___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_eoi(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_ParsecT_parseWithEoi___spec__1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_fixAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_num___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_unexpected(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_fix___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_pos(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_longestMatch___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_cond___rarg___lambda__1(obj*, obj*, uint8);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithEoi___spec__3(obj*);
obj* l_Lean_Parser_monadParsecTrans___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_digit___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_eoi___rarg(obj*, obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithLeftOver___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ensure___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1_x_27(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__9(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__mkConsumedResult___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_lexeme___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___main___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_lookahead(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldl___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldrAux___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Lean_Parser_MonadParsec___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_parseWithLeftOver___boxed(obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Lean_Parser_MonadParsec_error___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_expect___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_lookahead___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldr___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_fixAux___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_lookahead___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Lean_Parser_MonadParsec___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_labelsMkRes___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux___main___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_monadParsecTrans(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_ParsecT_parseWithEoi___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Parsec_parse(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1_x_27___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Alternative___rarg___lambda__2(obj*, obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_Parser_MonadParsec_SepBy___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux___boxed(obj*, obj*);
obj* l_String_Iterator_remaining___main(obj*);
obj* l_Lean_Parser_MonadParsec_takeUntil1___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_bind_x_27___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_takeUntil1___spec__2___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_2__takeAux___main___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_try(obj*);
obj* l_Lean_Parser_MonadParsec_lower___rarg(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__7(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_takeUntil1___spec__2(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_unexpectedAt___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_observing(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_fixAux___main___rarg___closed__1;
obj* l_Lean_Parser_Parsec_parse___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_notFollowedBySat(obj*, obj*);
extern usize l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
obj* l_Lean_Parser_MonadParsec_hidden___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1_x_27___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_parseWithLeftOver(obj*, obj*);
obj* l_Lean_Parser_Parsec_Message_text(obj*);
obj* l_Lean_Parser_ParsecT_eps___boxed(obj*);
obj* l_Lean_Parser_ParsecT_run___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Alternative___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_tryMkRes___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_merge___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_notFollowedBy___rarg___lambda__2(obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_MonadParsec_num___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ch(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_remaining___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_lower___rarg___lambda__1(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___rarg(obj*, obj*, uint8, obj*);
obj* l_Lean_Parser_MonadParsec_eoiError___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many_x_27___boxed(obj*, obj*);
obj* l_String_Iterator_next___main(obj*);
obj* l_Lean_Parser_MonadParsec_satisfy___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_bind_x_27___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_cond___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_MonadFail___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_fixAux___main___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_remaining___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_upper___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_lookahead___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_fixAux(obj*, obj*);
obj* l_Lean_Parser_ParsecT_expect(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Parser_ParsecT_try___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_run___boxed(obj*);
obj* l_Lean_Parser_ParsecT_MonadFail___rarg(obj*, obj*);
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___lambda__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg(obj*, obj*);
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__2(obj*, uint8, obj*);
extern obj* l_List_reprAux___main___rarg___closed__1;
obj* l_Lean_Parser_ParsecT_failure___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_notFollowedBy___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_pos___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_bind(obj*);
obj* l_Option_getOrElse___main___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_unexpected___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_label___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_bind_x_27___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ch___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_sepBy1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_any___rarg___lambda__1(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main(obj*);
obj* l_Lean_Parser_MonadParsec_SepBy(obj*, obj*);
obj* l___private_init_lean_parser_parsec_3__mkStringResult(obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_Parser_MonadParsec_lexeme(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_hidden___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_fix___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_ParsecT_parseWithEoi___spec__2(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__11(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_labels(obj*);
obj* l_Lean_Parser_MonadParsec_notFollowedBySat___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_MonadParsec_takeUntil___spec__1___rarg(obj*, obj*);
obj* l_Lean_Parser_ParsecT_bindMkRes___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_longestMatch___boxed(obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___main(obj*, obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Parsec_Message_toString___rarg___closed__2;
obj* l_Lean_Parser_ParsecT_try___boxed(obj*);
uint8 l_Char_isUpper(uint32);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__14(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Parsec_Result_mkEps___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_labels___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_append___rarg(obj*, obj*);
obj* l_Lean_Parser_ParsecT_HasMonadLift___rarg___lambda__1(obj*, obj*, obj*);
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_notFollowedBy___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Char_quoteCore(uint32);
obj* l_Lean_Parser_MonadParsec_satisfy(obj*, obj*);
obj* l_Lean_Parser_ParsecT_orelseMkRes___rarg(obj*, obj*);
obj* l_Lean_Parser_ParsecT_labels___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_num(obj*, obj*);
obj* l_Lean_Parser_ParsecT_merge(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27(obj*);
obj* l_Lean_Parser_ParsecT_runFrom___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27(obj*);
obj* l_Lean_Parser_Parsec_Result_mkEps___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___at_Lean_Parser_MonadParsec_whitespace___spec__2(obj*);
obj* l_Lean_Parser_MonadParsec_upper(obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_Parsec_Message_toString(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_label(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_num___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_unexpectedAt___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Parsec_HasLift___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_alpha(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeUntil___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_run(obj*);
obj* l_ExceptT_Monad___rarg___lambda__8___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__3(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_tryMkRes___rarg(obj*);
obj* l_Lean_Parser_ParsecT_runFrom___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_whitespace___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_Parsec_Message_text___rarg(obj*);
obj* l_Lean_Parser_MonadParsec_lower___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__8(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_pure___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___boxed(obj*);
obj* l_Lean_Parser_Parsec_Message_text___boxed(obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithEoi___spec__3___boxed(obj*);
obj* l_Lean_Parser_ParsecT_pure___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_fixAux___main(obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main(obj*);
obj* l_Lean_Parser_MonadParsec_try___rarg___closed__1;
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_labels___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many_x_27___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_takeUntil1___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_fix(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_leftOver(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil___spec__2(obj*);
obj* l_Lean_Parser_MonadParsec_remaining___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_whitespace___boxed(obj*, obj*);
obj* l_Dlist_singleton___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldr___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_runFrom(obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_MonadParsec_alpha___rarg(obj*, obj*);
obj* l_Lean_Parser_ParsecT_orelse___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_lexeme___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_num___spec__3___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Parsec_HasToString(obj*);
obj* l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1(obj*, uint32, obj*);
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__4___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Parsec_expected_toString(obj*);
obj* l___private_init_lean_parser_parsec_5__mkConsumedResult(obj*);
obj* l_Lean_Parser_MonadParsec_foldrAux___main(obj*, obj*, obj*);
obj* l_String_Iterator_remaining___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad(obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_bind_x_27___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many_x_27(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_cond(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ch___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_try___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Dlist_toList___main___rarg(obj*);
obj* l_Lean_Parser_MonadParsec_alpha___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_num___spec__2___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldl___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_cond___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux___main___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_curr___rarg___closed__1;
uint8 l_Char_isDigit(uint32);
obj* l_Lean_Parser_MonadParsec_foldlAux___main(obj*);
obj* l_Lean_Parser_MonadParsec_ch___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__mkConsumedResult___rarg(uint8, obj*);
obj* l_Lean_Parser_MonadParsec_error___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_2__takeAux___main(obj*);
obj* l_Lean_Parser_MonadParsec_curr___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux(obj*);
obj* l_Lean_Parser_MonadParsec_any___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_bind___boxed(obj*);
obj* l___private_init_lean_parser_parsec_5__mkConsumedResult___boxed(obj*);
obj* l_Lean_Parser_ParsecT_Alternative___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1(obj*, obj*);
obj* l_Lean_Parser_monadParsecTrans___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeUntil(obj*, obj*);
obj* l_Lean_Parser_ParsecT_parseWithEoi(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1_x_27___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_notFollowedBy___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_hasDecEq___main___at_Lean_Parser_Parsec_Message_text___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_notFollowedBy___rarg___lambda__1___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__11___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_sepBy1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldr___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Lean_Parser_MonadParsec___rarg(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___main___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead(obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__9(obj*, obj*, obj*);
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_bindMkRes___rarg(obj*, obj*);
obj* l___private_init_lean_parser_parsec_1__strAux(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_parseWithLeftOver___rarg___lambda__4(obj*, obj*, obj*);
obj* l_Lean_Parser_Parsec_expected_toString___main(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_MonadParsec_takeUntil___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__14___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_num___spec__1___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_longestMatch___rarg___lambda__2___closed__1;
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__7(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_num___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_try(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1_x_27(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1_x_27___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_orelseMkRes___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeUntil1(obj*, obj*);
obj* l_Lean_Parser_Parsec_Result_mkEps(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_whitespace___rarg(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_leftOver___rarg___lambda__1(obj*);
obj* l_Lean_Parser_ParsecT_eps(obj*);
obj* l_Lean_Parser_Parsec_HasToString___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
obj* l_Lean_Parser_ParsecT_bind___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Parsec_Message_toString___rarg___closed__1;
obj* l_Lean_Parser_monadParsecTrans___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Parsec_Message_toString___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_labels(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_parseWithLeftOver___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_ParsecT_parseWithLeftOver___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_labels___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__10(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__10(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__13(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_fixAux___boxed(obj*, obj*);
obj* l_Lean_Parser_Parsec_expected_toString___main___closed__1;
obj* l_Lean_Parser_MonadParsec_digit(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_eoi___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Lean_Parser_MonadParsec___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__5___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___rarg___lambda__1(obj*, obj*, uint32);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__11___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_parseWithEoi___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_notFollowedBySat___boxed(obj*, obj*);
uint8 l_Char_isWhitespace(uint32);
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_ParsecT_parseWithEoi___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithLeftOver___spec__1(obj*);
obj* l_Lean_Parser_MonadParsec_fix___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_bindMkRes(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1___rarg___lambda__2(obj*, obj*, obj*, uint32);
obj* l_Lean_Parser_Parsec_Message_text___rarg___closed__3;
obj* l_Lean_Parser_MonadParsec_strCore(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_strCore___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_curr(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_pos___rarg___closed__1;
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___boxed(obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__12(obj*, obj*, obj*);
obj* l_Lean_Parser_monadParsecTrans___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_curr___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_leftOver___rarg(obj*);
obj* l_Lean_Parser_MonadParsec_lexeme___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_1__strAux___main(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_labels___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_unexpectedAt___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux___main___rarg___lambda__3(obj*, obj*);
obj* l_Lean_Parser_ParsecT_bind_x_27(obj*);
extern uint8 l_True_Decidable;
obj* l_Lean_Parser_ParsecT_parse___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Alternative___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_ParsecT_parseWithEoi___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_longestMatch___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_tryMkRes(obj*, obj*);
obj* l_Lean_Parser_monadParsecTrans___rarg___lambda__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_parseWithLeftOver___rarg___lambda__3(obj*, obj*, obj*);
obj* l_Lean_Parser_Parsec_Message_text___rarg___closed__2;
uint8 l_String_Iterator_hasNext___main(obj*);
obj* l_Lean_Parser_MonadParsec_foldrAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldl___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_hidden___rarg___closed__1;
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_whitespace(obj*, obj*);
obj* l_Lean_Parser_Parsec_parse___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_expect___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_foldl(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_sepBy1___boxed(obj*, obj*);
obj* l_String_Iterator_curr___boxed(obj*);
obj* l_Lean_Parser_ParsecT_failure___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_parse___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_hidden___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_observing___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_ParsecT_HasMonadLift___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_fixAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1___rarg(obj*);
obj* l_Lean_Parser_MonadParsec_observing___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_fix___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_String_Iterator_toString___main(obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___at_Lean_Parser_MonadParsec_whitespace___spec__2___rarg(obj*, uint8, obj*);
obj* l_Lean_Parser_MonadParsec_pos___rarg___lambda__1___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_lookahead___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_eoiError___rarg(obj*);
obj* l_Lean_Parser_MonadParsec_labels___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Alternative___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_try___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_parse___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithEoi___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_MonadParsec_longestMatch___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_str___boxed(obj*, obj*);
obj* l_String_quote(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_MonadParsec_takeUntil___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_observing___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_MonadFail(obj*);
obj* l_Lean_Parser_MonadParsec_foldr(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_orelse(obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_ParsecT_parseWithEoi___spec__2___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_merge___rarg(obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_many___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_longestMatch___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_failure___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_hidden(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_label___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_alpha___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_remaining(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_parseWithLeftOver___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_List_zip___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__10___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1_x_27___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__8___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_orelseMkRes(obj*, obj*);
obj* l_Lean_Parser_ParsecT_orelse___rarg___lambda__1(obj*, obj*, obj*);
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil___spec__2___boxed(obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__8(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_parseWithEoi___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___rarg(obj*, obj*, uint8, obj*);
obj* l_Lean_Parser_MonadParsec_take(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_take___boxed(obj*, obj*);
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldl___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_orelse___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_MonadParsec_longestMatch___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__6___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_String_Iterator_extract___main___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhile1___boxed(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_pos___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_str(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ch___rarg(obj*, obj*, uint32);
obj* l_Lean_Parser_ParsecT_MonadFail___rarg___closed__1;
obj* l_Lean_Parser_ParsecT_HasMonadLift___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_run___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_notFollowedBy___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_ParsecT_MonadExcept(obj*);
obj* l_Lean_Parser_MonadParsec_unexpected___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_num___spec__2___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithLeftOver___spec__1___boxed(obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithEoi___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_ParsecT_parseWithEoi___spec__1___rarg(obj*, obj*);
obj* l_Lean_Parser_ParsecT_orelse___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil1___spec__3___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_foldrAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux(obj*, obj*);
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_num___spec__1___rarg___lambda__1(obj*, obj*, uint32);
obj* l_Lean_Parser_MonadParsec_hidden___rarg___lambda__1(obj*, obj*);
namespace lean {
obj* string_length(obj*);
}
obj* l_Lean_Parser_ParsecT_failure(obj*);
obj* _init_l_Lean_Parser_Parsec_expected_toString___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" or ");
return x_0;
}
}
obj* l_Lean_Parser_Parsec_expected_toString___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_String_Iterator_extract___main___closed__1;
return x_1;
}
else
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
return x_4;
}
else
{
obj* x_7; 
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; obj* x_17; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
lean::dec(x_2);
x_15 = l_Lean_Parser_Parsec_expected_toString___main___closed__1;
x_16 = lean::string_append(x_9, x_15);
x_17 = lean::string_append(x_16, x_12);
lean::dec(x_12);
return x_17;
}
else
{
obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_7);
x_20 = lean::cnstr_get(x_0, 0);
lean::inc(x_20);
lean::dec(x_0);
x_23 = l_List_reprAux___main___rarg___closed__1;
x_24 = lean::string_append(x_20, x_23);
x_25 = l_Lean_Parser_Parsec_expected_toString___main(x_2);
x_26 = lean::string_append(x_24, x_25);
lean::dec(x_25);
return x_26;
}
}
}
}
}
obj* l_Lean_Parser_Parsec_expected_toString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Parsec_expected_toString___main(x_0);
return x_1;
}
}
uint8 l_List_hasDecEq___main___at_Lean_Parser_Parsec_Message_text___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
else
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_5 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_0, 1);
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
x_9 = lean::string_dec_eq(x_5, x_7);
if (x_9 == 0)
{
uint8 x_10; 
x_10 = 0;
return x_10;
}
else
{
uint8 x_11; 
x_11 = l_List_hasDecEq___main___at_Lean_Parser_Parsec_Message_text___spec__1(x_6, x_8);
if (x_11 == 0)
{
uint8 x_12; 
x_12 = 0;
return x_12;
}
else
{
uint8 x_13; 
x_13 = 1;
return x_13;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_Parsec_Message_text___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unexpected ");
return x_0;
}
}
obj* _init_l_Lean_Parser_Parsec_Message_text___rarg___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("expected ");
return x_0;
}
}
obj* _init_l_Lean_Parser_Parsec_Message_text___rarg___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = l_List_append___rarg(x_0, x_0);
x_2 = lean::mk_string("\n");
x_3 = l_String_intercalate(x_2, x_1);
return x_3;
}
}
obj* l_Lean_Parser_Parsec_Message_text___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; uint8 x_4; obj* x_5; obj* x_8; obj* x_9; uint8 x_10; 
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
x_3 = l_String_Iterator_extract___main___closed__1;
x_4 = lean::string_dec_eq(x_1, x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_Dlist_toList___main___rarg(x_5);
x_9 = lean::box(0);
x_10 = l_List_hasDecEq___main___at_Lean_Parser_Parsec_Message_text___spec__1(x_8, x_9);
if (x_4 == 0)
{
obj* x_11; obj* x_12; obj* x_14; 
x_11 = l_Lean_Parser_Parsec_Message_text___rarg___closed__1;
x_12 = lean::string_append(x_11, x_1);
lean::dec(x_1);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_9);
if (x_10 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = l_Lean_Parser_Parsec_expected_toString___main(x_8);
x_16 = l_Lean_Parser_Parsec_Message_text___rarg___closed__2;
x_17 = lean::string_append(x_16, x_15);
lean::dec(x_15);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_9);
x_20 = l_List_append___rarg(x_14, x_19);
x_21 = l_Lean_Format_be___main___closed__1;
x_22 = l_String_intercalate(x_21, x_20);
return x_22;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_8);
x_24 = l_List_append___rarg(x_14, x_9);
x_25 = l_Lean_Format_be___main___closed__1;
x_26 = l_String_intercalate(x_25, x_24);
return x_26;
}
}
else
{
lean::dec(x_1);
if (x_10 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_28 = l_Lean_Parser_Parsec_expected_toString___main(x_8);
x_29 = l_Lean_Parser_Parsec_Message_text___rarg___closed__2;
x_30 = lean::string_append(x_29, x_28);
lean::dec(x_28);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_9);
x_33 = l_List_append___rarg(x_9, x_32);
x_34 = l_Lean_Format_be___main___closed__1;
x_35 = l_String_intercalate(x_34, x_33);
return x_35;
}
else
{
obj* x_37; 
lean::dec(x_8);
x_37 = l_Lean_Parser_Parsec_Message_text___rarg___closed__3;
return x_37;
}
}
}
}
obj* l_Lean_Parser_Parsec_Message_text(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Parsec_Message_text___rarg), 1, 0);
return x_1;
}
}
obj* l_List_hasDecEq___main___at_Lean_Parser_Parsec_Message_text___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_List_hasDecEq___main___at_Lean_Parser_Parsec_Message_text___spec__1(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_Parsec_Message_text___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Parsec_Message_text(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Parsec_Message_toString___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("error at line ");
return x_0;
}
}
obj* _init_l_Lean_Parser_Parsec_Message_toString___rarg___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", column ");
return x_0;
}
}
obj* _init_l_Lean_Parser_Parsec_Message_toString___rarg___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(":\n");
return x_0;
}
}
obj* l_Lean_Parser_Parsec_Message_toString___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = l_String_Iterator_toString___main(x_1);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_String_lineColumn(x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = l_Nat_repr(x_8);
x_14 = l_Lean_Parser_Parsec_Message_toString___rarg___closed__1;
x_15 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_17 = l_Lean_Parser_Parsec_Message_toString___rarg___closed__2;
x_18 = lean::string_append(x_15, x_17);
x_19 = l_Nat_repr(x_10);
x_20 = lean::string_append(x_18, x_19);
lean::dec(x_19);
x_22 = l_Lean_Parser_Parsec_Message_toString___rarg___closed__3;
x_23 = lean::string_append(x_20, x_22);
x_24 = l_Lean_Parser_Parsec_Message_text___rarg(x_0);
x_25 = lean::string_append(x_23, x_24);
lean::dec(x_24);
return x_25;
}
}
obj* l_Lean_Parser_Parsec_Message_toString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Parsec_Message_toString___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_Parsec_Message_toString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Parsec_Message_toString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Parsec_HasToString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Parsec_Message_toString___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_Parsec_HasToString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Parsec_HasToString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Parsec_HasLift(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Parsec_Message_toString___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_Parsec_HasLift___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Parsec_HasLift(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Parser_Parsec_Result_mkEps___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Parsec_Result_mkEps(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Parsec_Result_mkEps___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_Parsec_Result_mkEps___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Parsec_Result_mkEps(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_run___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_5; obj* x_8; obj* x_11; obj* x_12; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
x_12 = lean::apply_2(x_5, lean::box(0), x_11);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_19; obj* x_22; obj* x_23; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::cnstr_get(x_1, 0);
lean::inc(x_19);
lean::dec(x_1);
x_22 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_22, 0, x_19);
x_23 = lean::apply_2(x_16, lean::box(0), x_22);
return x_23;
}
}
}
obj* l_Lean_Parser_ParsecT_run___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; usize x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
x_10 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_9);
x_11 = x_10;
x_12 = lean::apply_1(x_3, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_run___rarg___lambda__1), 2, 1);
lean::closure_set(x_13, 0, x_0);
x_14 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* l_Lean_Parser_ParsecT_run(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_run___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_run___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_run___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_run___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_run(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_runFrom___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_3, x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_run___rarg___lambda__1), 2, 1);
lean::closure_set(x_9, 0, x_0);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_ParsecT_runFrom(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_runFrom___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_runFrom___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_runFrom___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_runFrom___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_runFrom(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_pure___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_3);
lean::cnstr_set(x_12, 1, x_4);
lean::cnstr_set(x_12, 2, x_11);
x_13 = lean::apply_2(x_8, lean::box(0), x_12);
return x_13;
}
}
obj* l_Lean_Parser_ParsecT_pure(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_pure___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_pure___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_ParsecT_pure___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_ParsecT_pure___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_pure(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_eps___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::box(0);
x_10 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_2);
lean::cnstr_set(x_11, 2, x_10);
x_12 = lean::apply_2(x_6, lean::box(0), x_11);
return x_12;
}
}
obj* l_Lean_Parser_ParsecT_eps(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_eps___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_eps___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_ParsecT_eps___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_ParsecT_eps___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_eps(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_ParsecT_failure___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("failure");
return x_0;
}
}
obj* l_Lean_Parser_ParsecT_failure___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::box(0);
x_11 = l_Lean_Parser_ParsecT_failure___rarg___closed__1;
x_12 = l_mjoin___rarg___closed__1;
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_3);
lean::cnstr_set(x_13, 1, x_11);
lean::cnstr_set(x_13, 2, x_12);
lean::cnstr_set(x_13, 3, x_10);
x_14 = 0;
x_15 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set_scalar(x_15, sizeof(void*)*1, x_14);
x_16 = x_15;
x_17 = lean::apply_2(x_7, lean::box(0), x_16);
return x_17;
}
}
obj* l_Lean_Parser_ParsecT_failure(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_failure___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_failure___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_ParsecT_failure___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_ParsecT_failure___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_failure(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_merge___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_15; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_11, 0, x_6);
lean::closure_set(x_11, 1, x_8);
x_12 = lean::cnstr_get(x_0, 3);
lean::inc(x_12);
lean::dec(x_0);
x_15 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_15, 0, x_2);
lean::cnstr_set(x_15, 1, x_4);
lean::cnstr_set(x_15, 2, x_11);
lean::cnstr_set(x_15, 3, x_12);
return x_15;
}
}
obj* l_Lean_Parser_ParsecT_merge(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_merge___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_merge___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_merge(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_bindMkRes___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 2);
 x_6 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_7 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_7 = x_6;
}
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_0);
return x_7;
}
else
{
obj* x_8; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; 
x_8 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_10 = x_1;
} else {
 lean::inc(x_8);
 lean::dec(x_1);
 x_10 = lean::box(0);
}
x_11 = 1;
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set_scalar(x_12, sizeof(void*)*1, x_11);
x_13 = x_12;
return x_13;
}
}
else
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_14; 
x_14 = lean::cnstr_get(x_1, 2);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_17; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
x_20 = lean::cnstr_get(x_1, 0);
x_22 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 2);
 x_24 = x_1;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_1);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_27 = x_14;
} else {
 lean::inc(x_25);
 lean::dec(x_14);
 x_27 = lean::box(0);
}
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_28, 0, x_17);
lean::closure_set(x_28, 1, x_25);
if (lean::is_scalar(x_27)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_27;
}
lean::cnstr_set(x_29, 0, x_28);
if (lean::is_scalar(x_24)) {
 x_30 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_30 = x_24;
}
lean::cnstr_set(x_30, 0, x_20);
lean::cnstr_set(x_30, 1, x_22);
lean::cnstr_set(x_30, 2, x_29);
return x_30;
}
}
else
{
uint8 x_31; 
x_31 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (x_31 == 0)
{
obj* x_32; obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_48; obj* x_49; obj* x_50; 
x_32 = lean::cnstr_get(x_0, 0);
lean::inc(x_32);
lean::dec(x_0);
x_35 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_37 = x_1;
} else {
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_35, 2);
lean::inc(x_42);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_44, 0, x_32);
lean::closure_set(x_44, 1, x_42);
x_45 = lean::cnstr_get(x_35, 3);
lean::inc(x_45);
lean::dec(x_35);
x_48 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_48, 0, x_38);
lean::cnstr_set(x_48, 1, x_40);
lean::cnstr_set(x_48, 2, x_44);
lean::cnstr_set(x_48, 3, x_45);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*1, x_31);
x_50 = x_49;
return x_50;
}
else
{
lean::dec(x_0);
return x_1;
}
}
}
}
}
obj* l_Lean_Parser_ParsecT_bindMkRes(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bindMkRes___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_bindMkRes___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParsecT_bindMkRes(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_bind___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_13; obj* x_16; obj* x_19; obj* x_20; obj* x_21; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bindMkRes___rarg), 2, 1);
lean::closure_set(x_19, 0, x_7);
x_20 = lean::apply_2(x_1, x_3, x_5);
x_21 = lean::apply_4(x_16, lean::box(0), lean::box(0), x_19, x_20);
return x_21;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_30; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_1);
x_23 = lean::cnstr_get(x_2, 0);
x_25 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_26 = x_2;
} else {
 lean::inc(x_23);
 lean::dec(x_2);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_0, 0);
lean::inc(x_27);
lean::dec(x_0);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
if (lean::is_scalar(x_26)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_26;
}
lean::cnstr_set(x_33, 0, x_23);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_25);
x_34 = x_33;
x_35 = lean::apply_2(x_30, lean::box(0), x_34);
return x_35;
}
}
}
obj* l_Lean_Parser_ParsecT_bind___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::apply_1(x_4, x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bind___rarg___lambda__1), 3, 2);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_5);
x_11 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_Lean_Parser_ParsecT_bind(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bind___rarg___boxed), 7, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_bind___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_ParsecT_bind___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_Parser_ParsecT_bind___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_bind(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_bind_x_27___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_9; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::apply_2(x_0, x_4, x_6);
return x_9;
}
else
{
obj* x_11; uint8 x_13; obj* x_14; obj* x_15; obj* x_18; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_0);
x_11 = lean::cnstr_get(x_2, 0);
x_13 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_14 = x_2;
} else {
 lean::inc(x_11);
 lean::dec(x_2);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_1, 0);
lean::inc(x_15);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
if (lean::is_scalar(x_14)) {
 x_21 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_21 = x_14;
}
lean::cnstr_set(x_21, 0, x_11);
lean::cnstr_set_scalar(x_21, sizeof(void*)*1, x_13);
x_22 = x_21;
x_23 = lean::apply_2(x_18, lean::box(0), x_22);
return x_23;
}
}
}
obj* l_Lean_Parser_ParsecT_bind_x_27___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::apply_1(x_4, x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bind_x_27___rarg___lambda__1), 3, 2);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_0);
x_11 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_Lean_Parser_ParsecT_bind_x_27(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bind_x_27___rarg___boxed), 7, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_bind_x_27___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_ParsecT_bind_x_27___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_Parser_ParsecT_bind_x_27___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_bind_x_27(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_7 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 x_9 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bindMkRes___rarg), 2, 1);
lean::closure_set(x_18, 0, x_7);
x_19 = lean::apply_1(x_1, x_3);
x_20 = lean::cnstr_get(x_10, 1);
lean::inc(x_20);
lean::dec(x_10);
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_9)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_9;
}
lean::cnstr_set(x_24, 0, x_19);
lean::cnstr_set(x_24, 1, x_5);
lean::cnstr_set(x_24, 2, x_23);
x_25 = lean::apply_2(x_20, lean::box(0), x_24);
x_26 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_18, x_25);
return x_26;
}
else
{
obj* x_28; uint8 x_30; obj* x_31; obj* x_32; obj* x_35; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_1);
x_28 = lean::cnstr_get(x_2, 0);
x_30 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_31 = x_2;
} else {
 lean::inc(x_28);
 lean::dec(x_2);
 x_31 = lean::box(0);
}
x_32 = lean::cnstr_get(x_0, 0);
lean::inc(x_32);
lean::dec(x_0);
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
lean::dec(x_32);
if (lean::is_scalar(x_31)) {
 x_38 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_38 = x_31;
}
lean::cnstr_set(x_38, 0, x_28);
lean::cnstr_set_scalar(x_38, sizeof(void*)*1, x_30);
x_39 = x_38;
x_40 = lean::apply_2(x_35, lean::box(0), x_39);
return x_40;
}
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_4, x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__1), 3, 2);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_3);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_3 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
lean::dec(x_11);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bindMkRes___rarg), 2, 1);
lean::closure_set(x_16, 0, x_5);
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
lean::dec(x_8);
x_20 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_7)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_7;
}
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_3);
lean::cnstr_set(x_21, 2, x_20);
x_22 = lean::apply_2(x_17, lean::box(0), x_21);
x_23 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_16, x_22);
return x_23;
}
else
{
obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_32; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_1);
x_25 = lean::cnstr_get(x_2, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_28 = x_2;
} else {
 lean::inc(x_25);
 lean::dec(x_2);
 x_28 = lean::box(0);
}
x_29 = lean::cnstr_get(x_0, 0);
lean::inc(x_29);
lean::dec(x_0);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
if (lean::is_scalar(x_28)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_28;
}
lean::cnstr_set(x_35, 0, x_25);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_27);
x_36 = x_35;
x_37 = lean::apply_2(x_32, lean::box(0), x_36);
return x_37;
}
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_4, x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__3), 3, 2);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_3);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set(x_11, 1, x_3);
lean::cnstr_set(x_11, 2, x_10);
x_12 = lean::apply_2(x_7, lean::box(0), x_11);
return x_12;
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_8 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bindMkRes___rarg), 2, 1);
lean::closure_set(x_11, 0, x_8);
x_12 = lean::apply_1(x_0, x_4);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::dec(x_1);
x_16 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_6);
lean::cnstr_set(x_17, 2, x_16);
x_18 = lean::apply_2(x_13, lean::box(0), x_17);
x_19 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_11, x_18);
return x_19;
}
else
{
obj* x_22; uint8 x_24; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
lean::dec(x_2);
x_22 = lean::cnstr_get(x_3, 0);
x_24 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_25 = x_3;
} else {
 lean::inc(x_22);
 lean::dec(x_3);
 x_25 = lean::box(0);
}
x_26 = lean::cnstr_get(x_1, 1);
lean::inc(x_26);
lean::dec(x_1);
if (lean::is_scalar(x_25)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_25;
}
lean::cnstr_set(x_29, 0, x_22);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_24);
x_30 = x_29;
x_31 = lean::apply_2(x_26, lean::box(0), x_30);
return x_31;
}
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 2);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
lean::dec(x_14);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bindMkRes___rarg), 2, 1);
lean::closure_set(x_19, 0, x_8);
x_20 = lean::apply_1(x_1, x_6);
lean::inc(x_16);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__6), 4, 3);
lean::closure_set(x_22, 0, x_4);
lean::closure_set(x_22, 1, x_11);
lean::closure_set(x_22, 2, x_16);
x_23 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_20, x_22);
x_24 = lean::apply_4(x_16, lean::box(0), lean::box(0), x_19, x_23);
return x_24;
}
else
{
obj* x_27; uint8 x_29; obj* x_30; obj* x_31; obj* x_34; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_1);
lean::dec(x_2);
x_27 = lean::cnstr_get(x_3, 0);
x_29 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_30 = x_3;
} else {
 lean::inc(x_27);
 lean::dec(x_3);
 x_30 = lean::box(0);
}
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
lean::dec(x_0);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
if (lean::is_scalar(x_30)) {
 x_37 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_37 = x_30;
}
lean::cnstr_set(x_37, 0, x_27);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_29);
x_38 = x_37;
x_39 = lean::apply_2(x_34, lean::box(0), x_38);
return x_39;
}
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_3, x_5);
lean::inc(x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__7), 4, 3);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_4);
lean::closure_set(x_10, 2, x_6);
x_11 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_10);
return x_11;
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_4 = lean::cnstr_get(x_3, 1);
x_6 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bindMkRes___rarg), 2, 1);
lean::closure_set(x_9, 0, x_6);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_1);
lean::cnstr_set(x_14, 1, x_4);
lean::cnstr_set(x_14, 2, x_13);
x_15 = lean::apply_2(x_10, lean::box(0), x_14);
x_16 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_15);
return x_16;
}
else
{
obj* x_19; uint8 x_21; obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_1);
lean::dec(x_2);
x_19 = lean::cnstr_get(x_3, 0);
x_21 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_22 = x_3;
} else {
 lean::inc(x_19);
 lean::dec(x_3);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_0, 1);
lean::inc(x_23);
lean::dec(x_0);
if (lean::is_scalar(x_22)) {
 x_26 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_26 = x_22;
}
lean::cnstr_set(x_26, 0, x_19);
lean::cnstr_set_scalar(x_26, sizeof(void*)*1, x_21);
x_27 = x_26;
x_28 = lean::apply_2(x_23, lean::box(0), x_27);
return x_28;
}
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 2);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
lean::dec(x_14);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bindMkRes___rarg), 2, 1);
lean::closure_set(x_19, 0, x_8);
x_20 = lean::apply_1(x_1, x_6);
lean::inc(x_16);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__9), 4, 3);
lean::closure_set(x_22, 0, x_11);
lean::closure_set(x_22, 1, x_4);
lean::closure_set(x_22, 2, x_16);
x_23 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_20, x_22);
x_24 = lean::apply_4(x_16, lean::box(0), lean::box(0), x_19, x_23);
return x_24;
}
else
{
obj* x_27; uint8 x_29; obj* x_30; obj* x_31; obj* x_34; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_1);
lean::dec(x_2);
x_27 = lean::cnstr_get(x_3, 0);
x_29 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_30 = x_3;
} else {
 lean::inc(x_27);
 lean::dec(x_3);
 x_30 = lean::box(0);
}
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
lean::dec(x_0);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
if (lean::is_scalar(x_30)) {
 x_37 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_37 = x_30;
}
lean::cnstr_set(x_37, 0, x_27);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_29);
x_38 = x_37;
x_39 = lean::apply_2(x_34, lean::box(0), x_38);
return x_39;
}
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_3, x_5);
lean::inc(x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__10), 4, 3);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_4);
lean::closure_set(x_10, 2, x_6);
x_11 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_10);
return x_11;
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_17; obj* x_18; obj* x_19; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bindMkRes___rarg), 2, 1);
lean::closure_set(x_17, 0, x_5);
x_18 = lean::apply_1(x_1, x_3);
x_19 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_17, x_18);
return x_19;
}
else
{
obj* x_21; uint8 x_23; obj* x_24; obj* x_25; obj* x_28; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_21 = lean::cnstr_get(x_2, 0);
x_23 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_24 = x_2;
} else {
 lean::inc(x_21);
 lean::dec(x_2);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_0, 0);
lean::inc(x_25);
lean::dec(x_0);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_21);
lean::cnstr_set_scalar(x_31, sizeof(void*)*1, x_23);
x_32 = x_31;
x_33 = lean::apply_2(x_28, lean::box(0), x_32);
return x_33;
}
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__13(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_3, x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__12), 3, 2);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_4);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__14(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_3, x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bind___rarg___lambda__1), 3, 2);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_4);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::inc(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__2___boxed), 6, 1);
lean::closure_set(x_3, 0, x_0);
lean::inc(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__4___boxed), 6, 1);
lean::closure_set(x_5, 0, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_5);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__5___boxed), 4, 1);
lean::closure_set(x_8, 0, x_0);
lean::inc(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__8___boxed), 6, 1);
lean::closure_set(x_10, 0, x_0);
lean::inc(x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__11___boxed), 6, 1);
lean::closure_set(x_12, 0, x_0);
lean::inc(x_0);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__13___boxed), 6, 1);
lean::closure_set(x_14, 0, x_0);
x_15 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_15, 0, x_6);
lean::cnstr_set(x_15, 1, x_8);
lean::cnstr_set(x_15, 2, x_10);
lean::cnstr_set(x_15, 3, x_12);
lean::cnstr_set(x_15, 4, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__14___boxed), 6, 1);
lean::closure_set(x_16, 0, x_0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* l_Lean_Parser_ParsecT_Monad(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_Monad___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_Monad___rarg___lambda__4(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_ParsecT_Monad___rarg___lambda__5(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_Monad___rarg___lambda__8(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__11___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_Monad___rarg___lambda__11(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_Monad___rarg___lambda__13(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___lambda__14___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_Monad___rarg___lambda__14(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_Monad___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParsecT_Monad___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_Monad___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_Monad(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_15; obj* x_16; obj* x_17; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 2);
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = lean::apply_1(x_0, x_3);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_8);
lean::cnstr_set(x_16, 1, x_5);
lean::cnstr_set(x_16, 2, x_15);
x_17 = lean::apply_2(x_12, lean::box(0), x_16);
return x_17;
}
else
{
obj* x_19; uint8 x_21; obj* x_22; obj* x_23; obj* x_26; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_19 = lean::cnstr_get(x_2, 0);
x_21 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_22 = x_2;
} else {
 lean::inc(x_19);
 lean::dec(x_2);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_1, 0);
lean::inc(x_23);
lean::dec(x_1);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
if (lean::is_scalar(x_22)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_22;
}
lean::cnstr_set(x_29, 0, x_19);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_21);
x_30 = x_29;
x_31 = lean::apply_2(x_26, lean::box(0), x_30);
return x_31;
}
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_4, x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__1), 3, 2);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_0);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_6; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 2);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_5)) {
 x_13 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_13 = x_5;
}
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_3);
lean::cnstr_set(x_13, 2, x_12);
x_14 = lean::apply_2(x_9, lean::box(0), x_13);
return x_14;
}
else
{
obj* x_16; uint8 x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_1);
x_16 = lean::cnstr_get(x_2, 0);
x_18 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_19 = x_2;
} else {
 lean::inc(x_16);
 lean::dec(x_2);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_0, 0);
lean::inc(x_20);
lean::dec(x_0);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_16);
lean::cnstr_set_scalar(x_26, sizeof(void*)*1, x_18);
x_27 = x_26;
x_28 = lean::apply_2(x_23, lean::box(0), x_27);
return x_28;
}
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_4, x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__3), 3, 2);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_3);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::apply_1(x_0, x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__1), 3, 2);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_1);
x_11 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
else
{
obj* x_14; uint8 x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_0);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_3, 0);
x_16 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_17 = x_3;
} else {
 lean::inc(x_14);
 lean::dec(x_3);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_14);
lean::cnstr_set_scalar(x_24, sizeof(void*)*1, x_16);
x_25 = x_24;
x_26 = lean::apply_2(x_21, lean::box(0), x_25);
return x_26;
}
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_3, x_5);
lean::inc(x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__5), 4, 3);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_0);
lean::closure_set(x_10, 2, x_6);
x_11 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_10);
return x_11;
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::apply_1(x_0, x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__3), 3, 2);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_4);
x_11 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
else
{
obj* x_14; uint8 x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_0);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_3, 0);
x_16 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_17 = x_3;
} else {
 lean::inc(x_14);
 lean::dec(x_3);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_14);
lean::cnstr_set_scalar(x_24, sizeof(void*)*1, x_16);
x_25 = x_24;
x_26 = lean::apply_2(x_21, lean::box(0), x_25);
return x_26;
}
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_3, x_5);
lean::inc(x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__7), 4, 3);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_0);
lean::closure_set(x_10, 2, x_6);
x_11 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_10);
return x_11;
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_0, x_4);
return x_7;
}
else
{
obj* x_9; uint8 x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_0);
x_9 = lean::cnstr_get(x_2, 0);
x_11 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_12 = x_2;
} else {
 lean::inc(x_9);
 lean::dec(x_2);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
if (lean::is_scalar(x_12)) {
 x_19 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_19 = x_12;
}
lean::cnstr_set(x_19, 0, x_9);
lean::cnstr_set_scalar(x_19, sizeof(void*)*1, x_11);
x_20 = x_19;
x_21 = lean::apply_2(x_16, lean::box(0), x_20);
return x_21;
}
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_3, x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__9), 3, 2);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_0);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_3, x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bind_x_27___rarg___lambda__1), 3, 2);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_0);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::inc(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__2___boxed), 6, 1);
lean::closure_set(x_3, 0, x_0);
lean::inc(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__4___boxed), 6, 1);
lean::closure_set(x_5, 0, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_5);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__5___boxed), 4, 1);
lean::closure_set(x_8, 0, x_0);
lean::inc(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__6___boxed), 6, 1);
lean::closure_set(x_10, 0, x_0);
lean::inc(x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__8___boxed), 6, 1);
lean::closure_set(x_12, 0, x_0);
lean::inc(x_0);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__10___boxed), 6, 1);
lean::closure_set(x_14, 0, x_0);
x_15 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_15, 0, x_6);
lean::cnstr_set(x_15, 1, x_8);
lean::cnstr_set(x_15, 2, x_10);
lean::cnstr_set(x_15, 3, x_12);
lean::cnstr_set(x_15, 4, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__11___boxed), 6, 1);
lean::closure_set(x_16, 0, x_0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad_x_27___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__4(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__6(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__8(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__10___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__10(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__11___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_Monad_x_27___rarg___lambda__11(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParsecT_Monad_x_27___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_Monad_x_27___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_Monad_x_27(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_ParsecT_MonadFail___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_MonadFail___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; 
x_2 = l_mjoin___rarg___closed__1;
x_3 = l_Lean_Parser_ParsecT_MonadFail___rarg___closed__1;
x_4 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_0);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_3);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set_scalar(x_6, sizeof(void*)*1, x_5);
x_7 = x_6;
return x_7;
}
}
obj* l_Lean_Parser_ParsecT_MonadFail(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_MonadFail___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_MonadFail___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_MonadFail(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = 0;
x_11 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set_scalar(x_11, sizeof(void*)*1, x_10);
x_12 = x_11;
x_13 = lean::apply_2(x_7, lean::box(0), x_12);
return x_13;
}
}
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__2(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_6; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::apply_2(x_6, lean::box(0), x_2);
return x_9;
}
else
{
uint8 x_10; 
x_10 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (x_1 == 0)
{
obj* x_11; obj* x_14; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_19 = x_2;
} else {
 lean::inc(x_17);
 lean::dec(x_2);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set_scalar(x_20, sizeof(void*)*1, x_10);
x_21 = x_20;
x_22 = lean::apply_2(x_14, lean::box(0), x_21);
return x_22;
}
else
{
obj* x_23; obj* x_26; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
lean::dec(x_0);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
x_29 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_31 = x_2;
} else {
 lean::inc(x_29);
 lean::dec(x_2);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_29);
lean::cnstr_set_scalar(x_32, sizeof(void*)*1, x_1);
x_33 = x_32;
x_34 = lean::apply_2(x_26, lean::box(0), x_33);
return x_34;
}
}
}
}
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; obj* x_9; obj* x_12; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::apply_2(x_9, lean::box(0), x_3);
return x_12;
}
else
{
obj* x_13; uint8 x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_13 = lean::cnstr_get(x_3, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
lean::dec(x_3);
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
x_19 = lean::apply_2(x_1, x_13, x_17);
x_20 = lean::box(x_15);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__2___boxed), 3, 2);
lean::closure_set(x_21, 0, x_0);
lean::closure_set(x_21, 1, x_20);
x_22 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_19, x_21);
return x_22;
}
}
}
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::apply_1(x_2, x_4);
lean::inc(x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__3), 4, 3);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_3);
lean::closure_set(x_9, 2, x_5);
x_10 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_9);
return x_10;
}
}
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
lean::inc(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__1___boxed), 4, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__4___boxed), 5, 1);
lean::closure_set(x_4, 0, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_Lean_Parser_ParsecT_MonadExcept(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_MonadExcept___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__2(x_0, x_3, x_2);
return x_4;
}
}
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_ParsecT_MonadExcept___rarg___lambda__4(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_ParsecT_MonadExcept___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParsecT_MonadExcept___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_MonadExcept___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_MonadExcept(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_HasMonadLift___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_2);
lean::cnstr_set(x_10, 1, x_1);
lean::cnstr_set(x_10, 2, x_9);
x_11 = lean::apply_2(x_6, lean::box(0), x_10);
return x_11;
}
}
obj* l_Lean_Parser_ParsecT_HasMonadLift___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_HasMonadLift___rarg___lambda__1), 3, 2);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, x_4);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_3, x_7);
return x_8;
}
}
obj* l_Lean_Parser_ParsecT_HasMonadLift(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_HasMonadLift___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_HasMonadLift___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_ParsecT_HasMonadLift___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_ParsecT_HasMonadLift___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_HasMonadLift(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_expect___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Dlist_singleton___rarg), 2, 1);
lean::closure_set(x_6, 0, x_1);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_10, 0, x_2);
lean::cnstr_set(x_10, 1, x_4);
lean::cnstr_set(x_10, 2, x_6);
lean::cnstr_set(x_10, 3, x_7);
return x_10;
}
}
obj* l_Lean_Parser_ParsecT_expect(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_expect___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_expect___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_expect(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_labelsMkRes___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 2);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_0, 0);
x_8 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 2);
 x_10 = x_0;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_0);
 x_10 = lean::box(0);
}
if (lean::is_scalar(x_5)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_5;
}
lean::cnstr_set(x_11, 0, x_1);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_6);
lean::cnstr_set(x_12, 1, x_8);
lean::cnstr_set(x_12, 2, x_11);
return x_12;
}
}
else
{
uint8 x_13; 
x_13 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
if (x_13 == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_25; obj* x_26; 
x_14 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_16 = x_0;
} else {
 lean::inc(x_14);
 lean::dec(x_0);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_14, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_14, 3);
lean::inc(x_21);
lean::dec(x_14);
x_24 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_24, 0, x_17);
lean::cnstr_set(x_24, 1, x_19);
lean::cnstr_set(x_24, 2, x_1);
lean::cnstr_set(x_24, 3, x_21);
if (lean::is_scalar(x_16)) {
 x_25 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_25 = x_16;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*1, x_13);
x_26 = x_25;
return x_26;
}
else
{
lean::dec(x_1);
return x_0;
}
}
}
}
obj* l_Lean_Parser_ParsecT_labelsMkRes(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_labelsMkRes___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_labelsMkRes___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParsecT_labelsMkRes(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_labels___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_2, x_1);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_Lean_Parser_ParsecT_labels___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_3, x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_labels___rarg___lambda__1), 3, 2);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_4);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_ParsecT_labels(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_labels___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_labels___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_labels___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_labels___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_labels(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_tryMkRes___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_0;
}
else
{
obj* x_1; obj* x_3; uint8 x_4; obj* x_5; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_3 = x_0;
} else {
 lean::inc(x_1);
 lean::dec(x_0);
 x_3 = lean::box(0);
}
x_4 = 0;
if (lean::is_scalar(x_3)) {
 x_5 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_5 = x_3;
}
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*1, x_4);
x_6 = x_5;
return x_6;
}
}
}
obj* l_Lean_Parser_ParsecT_tryMkRes(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_tryMkRes___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_tryMkRes___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParsecT_tryMkRes(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_try___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_1);
x_9 = lean::apply_2(x_5, lean::box(0), x_8);
return x_9;
}
}
obj* l_Lean_Parser_ParsecT_try___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::apply_1(x_3, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_try___rarg___lambda__1), 2, 1);
lean::closure_set(x_8, 0, x_0);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_ParsecT_try(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_try___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_try___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_ParsecT_try___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_ParsecT_try___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_try(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_orelseMkRes___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 2);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_18; 
x_5 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 2);
 x_9 = x_1;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_1);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_12 = x_2;
} else {
 lean::inc(x_10);
 lean::dec(x_2);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_0, 2);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_16, 0, x_13);
lean::closure_set(x_16, 1, x_10);
if (lean::is_scalar(x_12)) {
 x_17 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_17 = x_12;
}
lean::cnstr_set(x_17, 0, x_16);
if (lean::is_scalar(x_9)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_9;
}
lean::cnstr_set(x_18, 0, x_5);
lean::cnstr_set(x_18, 1, x_7);
lean::cnstr_set(x_18, 2, x_17);
return x_18;
}
}
else
{
uint8 x_19; 
x_19 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (x_19 == 0)
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_20 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_22 = x_1;
} else {
 lean::inc(x_20);
 lean::dec(x_1);
 x_22 = lean::box(0);
}
x_23 = l_Lean_Parser_ParsecT_merge___rarg(x_0, x_20);
if (lean::is_scalar(x_22)) {
 x_24 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_24 = x_22;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*1, x_19);
x_25 = x_24;
return x_25;
}
else
{
lean::dec(x_0);
return x_1;
}
}
}
}
obj* l_Lean_Parser_ParsecT_orelseMkRes(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_orelseMkRes___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_orelseMkRes___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParsecT_orelseMkRes(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_orelse___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_1, x_2);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_Lean_Parser_ParsecT_orelse___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
if (lean::obj_tag(x_4) == 0)
{
obj* x_10; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_10 = lean::box(0);
x_5 = x_10;
goto lbl_6;
}
else
{
uint8 x_11; 
x_11 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (x_11 == 0)
{
obj* x_12; obj* x_15; obj* x_16; obj* x_17; 
x_12 = lean::cnstr_get(x_4, 0);
lean::inc(x_12);
lean::dec(x_4);
x_15 = lean::apply_1(x_1, x_2);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_orelse___rarg___lambda__1), 3, 2);
lean::closure_set(x_16, 0, x_0);
lean::closure_set(x_16, 1, x_12);
x_17 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_15, x_16);
return x_17;
}
else
{
obj* x_21; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_21 = lean::box(0);
x_5 = x_21;
goto lbl_6;
}
}
lbl_6:
{
obj* x_23; obj* x_26; obj* x_29; 
lean::dec(x_5);
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
lean::dec(x_0);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
x_29 = lean::apply_2(x_26, lean::box(0), x_4);
return x_29;
}
}
}
obj* l_Lean_Parser_ParsecT_orelse___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_11; obj* x_12; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::inc(x_5);
x_9 = lean::apply_1(x_3, x_5);
lean::inc(x_6);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_orelse___rarg___lambda__2), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_4);
lean::closure_set(x_11, 2, x_5);
lean::closure_set(x_11, 3, x_6);
x_12 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_9, x_11);
return x_12;
}
}
obj* l_Lean_Parser_ParsecT_orelse(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_orelse___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_orelse___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_orelse___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_orelse___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_orelse(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_Alternative___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::inc(x_4);
x_8 = lean::apply_1(x_2, x_4);
lean::inc(x_5);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_orelse___rarg___lambda__2), 5, 4);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_3);
lean::closure_set(x_10, 2, x_4);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_8, x_10);
return x_11;
}
}
obj* l_Lean_Parser_ParsecT_Alternative___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_ParsecT_failure___rarg(x_0, lean::box(0), lean::box(0), x_2);
return x_3;
}
}
obj* l_Lean_Parser_ParsecT_Alternative___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; 
lean::inc(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__2___boxed), 6, 1);
lean::closure_set(x_3, 0, x_0);
lean::inc(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__4___boxed), 6, 1);
lean::closure_set(x_5, 0, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_5);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__5___boxed), 4, 1);
lean::closure_set(x_8, 0, x_0);
lean::inc(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__8___boxed), 6, 1);
lean::closure_set(x_10, 0, x_0);
lean::inc(x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__11___boxed), 6, 1);
lean::closure_set(x_12, 0, x_0);
lean::inc(x_0);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__13___boxed), 6, 1);
lean::closure_set(x_14, 0, x_0);
x_15 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_15, 0, x_6);
lean::cnstr_set(x_15, 1, x_8);
lean::cnstr_set(x_15, 2, x_10);
lean::cnstr_set(x_15, 3, x_12);
lean::cnstr_set(x_15, 4, x_14);
lean::inc(x_0);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Alternative___rarg___lambda__1___boxed), 5, 1);
lean::closure_set(x_17, 0, x_0);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Alternative___rarg___lambda__2___boxed), 3, 1);
lean::closure_set(x_18, 0, x_0);
x_19 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_19, 0, x_15);
lean::cnstr_set(x_19, 1, x_17);
lean::cnstr_set(x_19, 2, x_18);
return x_19;
}
}
obj* l_Lean_Parser_ParsecT_Alternative(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Alternative___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_Alternative___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_ParsecT_Alternative___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_ParsecT_Alternative___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_ParsecT_Alternative___rarg___lambda__2(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_ParsecT_Alternative___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParsecT_Alternative___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_Alternative___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_Alternative(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_6; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_11 = x_2;
} else {
 lean::inc(x_9);
 lean::dec(x_2);
 x_11 = lean::box(0);
}
x_12 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_11)) {
 x_13 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_13 = x_11;
}
lean::cnstr_set(x_13, 0, x_9);
lean::cnstr_set(x_13, 1, x_1);
lean::cnstr_set(x_13, 2, x_12);
x_14 = lean::apply_2(x_6, lean::box(0), x_13);
return x_14;
}
else
{
obj* x_16; obj* x_19; obj* x_22; 
lean::dec(x_1);
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::apply_2(x_19, lean::box(0), x_2);
return x_22;
}
}
}
obj* l_Lean_Parser_ParsecT_lookahead___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::inc(x_4);
x_8 = lean::apply_1(x_3, x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_lookahead___rarg___lambda__1), 3, 2);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_4);
x_10 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_ParsecT_lookahead(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_lookahead___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_ParsecT_lookahead___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_lookahead(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Lean_Parser_MonadParsec___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::apply_1(x_2, x_3);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_Lean_Parser_Lean_Parser_MonadParsec___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_5(x_2, lean::box(0), x_0, lean::box(0), x_3, x_4);
return x_5;
}
}
obj* l_Lean_Parser_Lean_Parser_MonadParsec___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Lean_Parser_MonadParsec___rarg___lambda__1___boxed), 4, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Lean_Parser_MonadParsec___rarg___lambda__2___boxed), 5, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_Lean_Parser_MonadParsec(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Lean_Parser_MonadParsec___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_Lean_Parser_MonadParsec___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Lean_Parser_MonadParsec___rarg___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_Lean_Parser_MonadParsec___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Lean_Parser_MonadParsec___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_Lean_Parser_MonadParsec___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Lean_Parser_MonadParsec(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_monadParsecTrans___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::apply_2(x_4, lean::box(0), x_3);
x_8 = lean::apply_2(x_1, lean::box(0), x_7);
return x_8;
}
}
obj* l_Lean_Parser_monadParsecTrans___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::apply_3(x_4, lean::box(0), x_1, x_3);
return x_7;
}
}
obj* l_Lean_Parser_monadParsecTrans___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_monadParsecTrans___rarg___lambda__2___boxed), 4, 2);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_3);
x_6 = lean::apply_3(x_1, lean::box(0), x_5, x_4);
return x_6;
}
}
obj* l_Lean_Parser_monadParsecTrans___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_monadParsecTrans___rarg___lambda__1___boxed), 4, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_monadParsecTrans___rarg___lambda__3___boxed), 5, 2);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_1);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_Lean_Parser_monadParsecTrans(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_monadParsecTrans___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_monadParsecTrans___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_monadParsecTrans___rarg___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_monadParsecTrans___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_monadParsecTrans___rarg___lambda__2(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_monadParsecTrans___rarg___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_monadParsecTrans___rarg___lambda__3(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_monadParsecTrans___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_monadParsecTrans(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_error___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
x_5 = l_Option_getOrElse___main___rarg(x_0, x_4);
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_3);
x_7 = 0;
x_8 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*1, x_7);
x_9 = x_8;
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_error___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
lean::closure_set(x_9, 3, x_5);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_Lean_Parser_MonadParsec_error(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_error___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_error___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_error___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_error___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_error___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_error(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_leftOver___rarg___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::inc(x_0);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_0);
lean::cnstr_set(x_3, 2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_leftOver___rarg___lambda__1), 1, 0);
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_leftOver___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_5 = lean::apply_2(x_1, lean::box(0), x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_leftOver(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_leftOver___rarg), 1, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_leftOver___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_leftOver(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_MonadParsec_remaining___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_String_Iterator_remaining___boxed), 1, 0);
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_remaining___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_14 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_15 = lean::apply_2(x_11, lean::box(0), x_14);
x_16 = l_Lean_Parser_MonadParsec_remaining___rarg___closed__1;
x_17 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_16, x_15);
return x_17;
}
}
obj* l_Lean_Parser_MonadParsec_remaining(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_remaining___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_remaining___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_remaining(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_labels___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_4, x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_labels___rarg___lambda__1), 3, 2);
lean::closure_set(x_9, 0, x_2);
lean::closure_set(x_9, 1, x_0);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_MonadParsec_labels___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_labels___rarg___lambda__1___boxed), 6, 1);
lean::closure_set(x_7, 0, x_3);
x_8 = lean::apply_3(x_4, lean::box(0), x_7, x_2);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_labels(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_labels___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_labels___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_labels___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_labels___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_labels___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_labels___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_labels(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_label___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Dlist_singleton___rarg), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_labels___rarg___lambda__1___boxed), 6, 1);
lean::closure_set(x_8, 0, x_4);
x_9 = lean::apply_3(x_5, lean::box(0), x_8, x_2);
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_label(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_label___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_label___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_label___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_label___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_label(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_hidden___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_1, x_8);
x_10 = lean::apply_2(x_5, lean::box(0), x_9);
return x_10;
}
}
obj* l_Lean_Parser_MonadParsec_hidden___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_7 = lean::apply_1(x_3, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_hidden___rarg___lambda__1), 2, 1);
lean::closure_set(x_8, 0, x_1);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_MonadParsec_hidden___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_hidden___rarg___lambda__2___boxed), 5, 0);
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_hidden___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_MonadParsec_hidden___rarg___closed__1;
x_7 = lean::apply_3(x_3, lean::box(0), x_6, x_2);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_hidden(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_hidden___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_hidden___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_hidden___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_hidden___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_hidden___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_hidden___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_hidden(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_try___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_7 = lean::apply_1(x_3, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_try___rarg___lambda__1), 2, 1);
lean::closure_set(x_8, 0, x_1);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* _init_l_Lean_Parser_MonadParsec_try___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_try___rarg___lambda__1___boxed), 5, 0);
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_try___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_MonadParsec_try___rarg___closed__1;
x_7 = lean::apply_3(x_3, lean::box(0), x_6, x_2);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_try(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_try___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_try___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_try___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_try___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_try___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_try___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_try(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_lookahead___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_ParsecT_lookahead___rarg(x_1, lean::box(0), lean::box(0), x_3, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_MonadParsec_lookahead___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_lookahead___rarg___lambda__1___boxed), 5, 0);
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_lookahead___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_MonadParsec_lookahead___rarg___closed__1;
x_7 = lean::apply_3(x_3, lean::box(0), x_6, x_2);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_lookahead(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_lookahead___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_lookahead___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_lookahead___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_lookahead___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_lookahead___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_lookahead___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_lookahead(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_notFollowedBySat___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_String_Iterator_hasNext___main(x_3);
if (x_4 == 0)
{
obj* x_7; obj* x_10; obj* x_13; obj* x_14; 
lean::dec(x_1);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::box(0);
x_14 = lean::apply_2(x_10, lean::box(0), x_13);
return x_14;
}
else
{
uint32 x_15; obj* x_16; obj* x_17; uint8 x_18; 
x_15 = l_String_Iterator_curr___main(x_3);
x_16 = lean::box_uint32(x_15);
x_17 = lean::apply_1(x_1, x_16);
x_18 = lean::unbox(x_17);
if (x_18 == 0)
{
obj* x_20; obj* x_23; obj* x_26; obj* x_27; 
lean::dec(x_2);
x_20 = lean::cnstr_get(x_0, 0);
lean::inc(x_20);
lean::dec(x_0);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
x_26 = lean::box(0);
x_27 = lean::apply_2(x_23, lean::box(0), x_26);
return x_27;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_0);
x_29 = l_Char_quoteCore(x_15);
x_30 = l_Char_HasRepr___closed__1;
x_31 = lean::string_append(x_30, x_29);
lean::dec(x_29);
x_33 = lean::string_append(x_31, x_30);
x_34 = lean::box(0);
x_35 = l_mjoin___rarg___closed__1;
x_36 = l_Lean_Parser_MonadParsec_error___rarg(x_2, lean::box(0), x_33, x_35, x_34, x_34);
return x_36;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_notFollowedBySat___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_8 = lean::apply_2(x_5, lean::box(0), x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_notFollowedBySat___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_1);
x_10 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_MonadParsec_notFollowedBySat(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_notFollowedBySat___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_notFollowedBySat___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_notFollowedBySat___rarg___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_notFollowedBySat___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_notFollowedBySat(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("end of input");
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_eoiError___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_3 = l_mjoin___rarg___closed__1;
x_4 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 3, x_1);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set_scalar(x_6, sizeof(void*)*1, x_5);
x_7 = x_6;
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_eoiError(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_eoiError___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_eoiError___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_eoiError(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_MonadParsec_curr___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_String_Iterator_curr___boxed), 1, 0);
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_curr___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_14 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_15 = lean::apply_2(x_11, lean::box(0), x_14);
x_16 = l_Lean_Parser_MonadParsec_curr___rarg___closed__1;
x_17 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_16, x_15);
return x_17;
}
}
obj* l_Lean_Parser_MonadParsec_curr(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_curr___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_curr___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_curr(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_cond___rarg___lambda__1(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
if (x_2 == 0)
{
lean::inc(x_0);
return x_0;
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
obj* l_Lean_Parser_MonadParsec_cond___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_16 = l_Lean_Parser_MonadParsec_curr___rarg(x_0, x_1);
x_17 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_3, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_cond___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_18, 0, x_5);
lean::closure_set(x_18, 1, x_4);
x_19 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_17, x_18);
return x_19;
}
}
obj* l_Lean_Parser_MonadParsec_cond(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_cond___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_cond___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_Lean_Parser_MonadParsec_cond___rarg___lambda__1(x_0, x_1, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_cond___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_cond___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_cond___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_cond(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1(obj* x_0, uint32 x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_String_Iterator_next___main(x_0);
x_4 = lean::box(0);
x_5 = lean::box_uint32(x_1);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
lean::cnstr_set(x_6, 2, x_4);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_String_Iterator_hasNext___main(x_3);
if (x_4 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
x_11 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_9, x_10, x_8, x_8);
return x_11;
}
else
{
uint32 x_12; obj* x_13; obj* x_15; uint8 x_16; 
x_12 = l_String_Iterator_curr___main(x_3);
x_13 = lean::box_uint32(x_12);
lean::inc(x_13);
x_15 = lean::apply_1(x_1, x_13);
x_16 = lean::unbox(x_15);
if (x_16 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_3);
lean::dec(x_2);
x_20 = l_Char_quoteCore(x_12);
x_21 = l_Char_HasRepr___closed__1;
x_22 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_24 = lean::string_append(x_22, x_21);
x_25 = lean::box(0);
x_26 = l_mjoin___rarg___closed__1;
x_27 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_24, x_26, x_25, x_25);
return x_27;
}
else
{
obj* x_29; obj* x_30; 
lean::dec(x_0);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_29, 0, x_3);
lean::closure_set(x_29, 1, x_13);
x_30 = lean::apply_2(x_2, lean::box(0), x_29);
return x_30;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_satisfy___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_6);
x_10 = lean::apply_2(x_6, lean::box(0), x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__2), 4, 3);
lean::closure_set(x_11, 0, x_1);
lean::closure_set(x_11, 1, x_2);
lean::closure_set(x_11, 2, x_6);
x_12 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_11);
return x_12;
}
}
obj* l_Lean_Parser_MonadParsec_satisfy(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1(x_0, x_3, x_2);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_satisfy___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_satisfy(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_ch___rarg___lambda__1(obj* x_0, uint32 x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_String_Iterator_hasNext___main(x_3);
if (x_4 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
x_10 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_8, x_9, x_7, x_7);
return x_10;
}
else
{
uint32 x_11; uint8 x_12; 
x_11 = l_String_Iterator_curr___main(x_3);
x_12 = x_11 == x_1;
if (x_12 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_3);
lean::dec(x_2);
x_15 = l_Char_quoteCore(x_11);
x_16 = l_Char_HasRepr___closed__1;
x_17 = lean::string_append(x_16, x_15);
lean::dec(x_15);
x_19 = lean::string_append(x_17, x_16);
x_20 = lean::box(0);
x_21 = l_mjoin___rarg___closed__1;
x_22 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_19, x_21, x_20, x_20);
return x_22;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_0);
x_24 = lean::box_uint32(x_11);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_25, 0, x_3);
lean::closure_set(x_25, 1, x_24);
x_26 = lean::apply_2(x_2, lean::box(0), x_25);
return x_26;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_ch___rarg(obj* x_0, obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_6);
x_10 = lean::apply_2(x_6, lean::box(0), x_8);
x_11 = lean::box_uint32(x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_ch___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_12, 0, x_1);
lean::closure_set(x_12, 1, x_11);
lean::closure_set(x_12, 2, x_6);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* l_Lean_Parser_MonadParsec_ch(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_ch___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_ch___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_1);
x_5 = l_Lean_Parser_MonadParsec_ch___rarg___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_ch___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_Lean_Parser_MonadParsec_ch___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_ch___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_ch(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_alpha___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_Iterator_hasNext___main(x_2);
if (x_3 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_7, x_8, x_6, x_6);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_Iterator_curr___main(x_2);
x_11 = l_Char_isAlpha(x_10);
if (x_11 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_1);
lean::dec(x_2);
x_14 = l_Char_quoteCore(x_10);
x_15 = l_Char_HasRepr___closed__1;
x_16 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_18 = lean::string_append(x_16, x_15);
x_19 = lean::box(0);
x_20 = l_mjoin___rarg___closed__1;
x_21 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_18, x_20, x_19, x_19);
return x_21;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_0);
x_23 = lean::box_uint32(x_10);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_24, 0, x_2);
lean::closure_set(x_24, 1, x_23);
x_25 = lean::apply_2(x_1, lean::box(0), x_24);
return x_25;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_alpha___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_5);
x_9 = lean::apply_2(x_5, lean::box(0), x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_alpha___rarg___lambda__1), 3, 2);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_5);
x_11 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_Lean_Parser_MonadParsec_alpha(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_alpha___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_alpha___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_alpha(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_digit___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_Iterator_hasNext___main(x_2);
if (x_3 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_7, x_8, x_6, x_6);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_Iterator_curr___main(x_2);
x_11 = l_Char_isDigit(x_10);
if (x_11 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_1);
lean::dec(x_2);
x_14 = l_Char_quoteCore(x_10);
x_15 = l_Char_HasRepr___closed__1;
x_16 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_18 = lean::string_append(x_16, x_15);
x_19 = lean::box(0);
x_20 = l_mjoin___rarg___closed__1;
x_21 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_18, x_20, x_19, x_19);
return x_21;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_0);
x_23 = lean::box_uint32(x_10);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_24, 0, x_2);
lean::closure_set(x_24, 1, x_23);
x_25 = lean::apply_2(x_1, lean::box(0), x_24);
return x_25;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_digit___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_5);
x_9 = lean::apply_2(x_5, lean::box(0), x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_digit___rarg___lambda__1), 3, 2);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_5);
x_11 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_Lean_Parser_MonadParsec_digit(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_digit___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_digit___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_digit(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_upper___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_Iterator_hasNext___main(x_2);
if (x_3 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_7, x_8, x_6, x_6);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_Iterator_curr___main(x_2);
x_11 = l_Char_isUpper(x_10);
if (x_11 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_1);
lean::dec(x_2);
x_14 = l_Char_quoteCore(x_10);
x_15 = l_Char_HasRepr___closed__1;
x_16 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_18 = lean::string_append(x_16, x_15);
x_19 = lean::box(0);
x_20 = l_mjoin___rarg___closed__1;
x_21 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_18, x_20, x_19, x_19);
return x_21;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_0);
x_23 = lean::box_uint32(x_10);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_24, 0, x_2);
lean::closure_set(x_24, 1, x_23);
x_25 = lean::apply_2(x_1, lean::box(0), x_24);
return x_25;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_upper___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_5);
x_9 = lean::apply_2(x_5, lean::box(0), x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_upper___rarg___lambda__1), 3, 2);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_5);
x_11 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_Lean_Parser_MonadParsec_upper(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_upper___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_upper___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_upper(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_lower___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_Iterator_hasNext___main(x_2);
if (x_3 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_7, x_8, x_6, x_6);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_Iterator_curr___main(x_2);
x_11 = l_Char_isLower(x_10);
if (x_11 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_1);
lean::dec(x_2);
x_14 = l_Char_quoteCore(x_10);
x_15 = l_Char_HasRepr___closed__1;
x_16 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_18 = lean::string_append(x_16, x_15);
x_19 = lean::box(0);
x_20 = l_mjoin___rarg___closed__1;
x_21 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_18, x_20, x_19, x_19);
return x_21;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_0);
x_23 = lean::box_uint32(x_10);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_24, 0, x_2);
lean::closure_set(x_24, 1, x_23);
x_25 = lean::apply_2(x_1, lean::box(0), x_24);
return x_25;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_lower___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_5);
x_9 = lean::apply_2(x_5, lean::box(0), x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_lower___rarg___lambda__1), 3, 2);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_5);
x_11 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_Lean_Parser_MonadParsec_lower(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_lower___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_lower___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_lower(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_any___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_Iterator_hasNext___main(x_2);
if (x_3 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_7, x_8, x_6, x_6);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_Iterator_curr___main(x_2);
x_11 = l_True_Decidable;
if (x_11 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_1);
lean::dec(x_2);
x_14 = l_Char_quoteCore(x_10);
x_15 = l_Char_HasRepr___closed__1;
x_16 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_18 = lean::string_append(x_16, x_15);
x_19 = lean::box(0);
x_20 = l_mjoin___rarg___closed__1;
x_21 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_18, x_20, x_19, x_19);
return x_21;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_0);
x_23 = lean::box_uint32(x_10);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_24, 0, x_2);
lean::closure_set(x_24, 1, x_23);
x_25 = lean::apply_2(x_1, lean::box(0), x_24);
return x_25;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_any___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_5);
x_9 = lean::apply_2(x_5, lean::box(0), x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_any___rarg___lambda__1), 3, 2);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_5);
x_11 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_Lean_Parser_MonadParsec_any(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_any___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_any___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_any(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_1__strAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_Iterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_9 = lean::box(0);
return x_9;
}
else
{
uint32 x_10; uint32 x_11; uint8 x_12; 
x_10 = l_String_Iterator_curr___main(x_1);
x_11 = l_String_Iterator_curr___main(x_2);
x_12 = x_10 == x_11;
if (x_12 == 0)
{
obj* x_16; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_16 = lean::box(0);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_sub(x_0, x_17);
lean::dec(x_0);
x_20 = l_String_Iterator_next___main(x_1);
x_21 = l_String_Iterator_next___main(x_2);
x_0 = x_18;
x_1 = x_20;
x_2 = x_21;
goto _start;
}
}
}
else
{
obj* x_25; 
lean::dec(x_1);
lean::dec(x_0);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_2);
return x_25;
}
}
}
obj* l___private_init_lean_parser_parsec_1__strAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_parsec_1__strAux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_strCore___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; usize x_5; obj* x_7; obj* x_8; obj* x_10; 
x_3 = lean::string_length(x_0);
x_4 = lean::mk_nat_obj(0u);
x_5 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
lean::inc(x_0);
x_7 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set_scalar(x_7, sizeof(void*)*2, x_5);
x_8 = x_7;
lean::inc(x_2);
x_10 = l___private_init_lean_parser_parsec_1__strAux___main(x_3, x_8, x_2);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; 
lean::dec(x_0);
x_12 = lean::box(0);
x_13 = l_String_Iterator_extract___main___closed__1;
x_14 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set(x_14, 2, x_1);
lean::cnstr_set(x_14, 3, x_12);
x_15 = 0;
x_16 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set_scalar(x_16, sizeof(void*)*1, x_15);
x_17 = x_16;
return x_17;
}
else
{
obj* x_20; obj* x_23; obj* x_24; 
lean::dec(x_1);
lean::dec(x_2);
x_20 = lean::cnstr_get(x_10, 0);
lean::inc(x_20);
lean::dec(x_10);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_0);
lean::cnstr_set(x_24, 1, x_20);
lean::cnstr_set(x_24, 2, x_23);
return x_24;
}
}
}
obj* l_Lean_Parser_MonadParsec_strCore___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_String_isEmpty(x_2);
if (x_4 == 0)
{
obj* x_6; obj* x_9; obj* x_10; 
lean::dec(x_0);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_strCore___rarg___lambda__1), 3, 2);
lean::closure_set(x_9, 0, x_2);
lean::closure_set(x_9, 1, x_3);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
else
{
obj* x_14; obj* x_17; obj* x_20; obj* x_21; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_String_Iterator_extract___main___closed__1;
x_21 = lean::apply_2(x_17, lean::box(0), x_20);
return x_21;
}
}
}
obj* l_Lean_Parser_MonadParsec_strCore(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_strCore___rarg), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_strCore___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_strCore(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_str___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_2);
x_4 = l_String_quote(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Dlist_singleton___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = l_Lean_Parser_MonadParsec_strCore___rarg(x_0, x_1, x_2, x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_str(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_str___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_str___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_str(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_2__takeAux___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_Iterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_8; 
lean::dec(x_1);
lean::dec(x_0);
x_8 = l_Lean_Parser_MonadParsec_eoiError___rarg(x_2);
return x_8;
}
else
{
obj* x_9; obj* x_10; uint32 x_12; obj* x_13; obj* x_14; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_0, x_9);
lean::dec(x_0);
x_12 = l_String_Iterator_curr___main(x_2);
x_13 = lean::string_push(x_1, x_12);
x_14 = l_String_Iterator_next___main(x_2);
x_0 = x_10;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_0);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_1);
lean::cnstr_set(x_18, 1, x_2);
lean::cnstr_set(x_18, 2, x_17);
return x_18;
}
}
}
obj* l___private_init_lean_parser_parsec_2__takeAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_2__takeAux___main___rarg), 3, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_2__takeAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_2__takeAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_2__takeAux___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_parsec_2__takeAux___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_2__takeAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_2__takeAux___rarg), 3, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_2__takeAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_2__takeAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_take___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_0);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_9 = l_String_Iterator_extract___main___closed__1;
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_2__takeAux___rarg), 3, 2);
lean::closure_set(x_10, 0, x_2);
lean::closure_set(x_10, 1, x_9);
x_11 = lean::apply_2(x_6, lean::box(0), x_10);
return x_11;
}
else
{
obj* x_14; obj* x_17; obj* x_20; obj* x_21; 
lean::dec(x_1);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_String_Iterator_extract___main___closed__1;
x_21 = lean::apply_2(x_17, lean::box(0), x_20);
return x_21;
}
}
}
obj* l_Lean_Parser_MonadParsec_take(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_take___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_take___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_take(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_3__mkStringResult___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_String_isEmpty(x_0);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_3);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_5);
return x_6;
}
}
}
obj* l___private_init_lean_parser_parsec_3__mkStringResult(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_3__mkStringResult___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_3__mkStringResult___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_3__mkStringResult(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = l_String_Iterator_hasNext___main(x_3);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
x_9 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_2, x_3);
return x_9;
}
else
{
uint32 x_10; obj* x_11; obj* x_13; uint8 x_14; 
x_10 = l_String_Iterator_curr___main(x_3);
x_11 = lean::box_uint32(x_10);
lean::inc(x_0);
x_13 = lean::apply_1(x_0, x_11);
x_14 = lean::unbox(x_13);
if (x_14 == 0)
{
obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_2, x_3);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_21; obj* x_22; 
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_sub(x_1, x_18);
lean::dec(x_1);
x_21 = lean::string_push(x_2, x_10);
x_22 = l_String_Iterator_next___main(x_3);
x_1 = x_19;
x_2 = x_21;
x_3 = x_22;
goto _start;
}
}
}
else
{
obj* x_26; 
lean::dec(x_1);
lean::dec(x_0);
x_26 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_2, x_3);
return x_26;
}
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_4__takeWhileAux___main___rarg), 4, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_4__takeWhileAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_4__takeWhileAux___rarg), 4, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_4__takeWhileAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_String_Iterator_remaining___main(x_1);
x_3 = l_String_Iterator_extract___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___rarg(x_0, x_2, x_3, x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___rarg___lambda__1), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::apply_2(x_2, lean::box(0), x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___rarg), 2, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_String_Iterator_remaining___main(x_2);
x_4 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___rarg(x_0, x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___rarg___lambda__1), 3, 2);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_2);
x_7 = lean::apply_2(x_3, lean::box(0), x_6);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhileCont(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___rarg___lambda__1(obj* x_0, obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_String_Iterator_extract___main___closed__1;
x_4 = lean::string_push(x_3, x_2);
x_5 = l_Lean_Parser_MonadParsec_takeWhileCont___rarg(x_0, x_1, x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_6);
x_10 = lean::apply_2(x_6, lean::box(0), x_8);
lean::inc(x_2);
lean::inc(x_1);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__2), 4, 3);
lean::closure_set(x_13, 0, x_1);
lean::closure_set(x_13, 1, x_2);
lean::closure_set(x_13, 2, x_6);
lean::inc(x_3);
x_15 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile1___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_16, 0, x_1);
lean::closure_set(x_16, 1, x_2);
x_17 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_15, x_16);
return x_17;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile1___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_Lean_Parser_MonadParsec_takeWhile1___rarg___lambda__1(x_0, x_1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_takeWhile1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = l_String_Iterator_hasNext___main(x_3);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
x_9 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_2, x_3);
return x_9;
}
else
{
uint32 x_10; obj* x_11; obj* x_13; uint8 x_14; 
x_10 = l_String_Iterator_curr___main(x_3);
x_11 = lean::box_uint32(x_10);
lean::inc(x_0);
x_13 = lean::apply_1(x_0, x_11);
x_14 = lean::unbox(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_sub(x_1, x_15);
lean::dec(x_1);
x_18 = lean::string_push(x_2, x_10);
x_19 = l_String_Iterator_next___main(x_3);
x_1 = x_16;
x_2 = x_18;
x_3 = x_19;
goto _start;
}
else
{
obj* x_23; 
lean::dec(x_1);
lean::dec(x_0);
x_23 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_2, x_3);
return x_23;
}
}
}
else
{
obj* x_26; 
lean::dec(x_1);
lean::dec(x_0);
x_26 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_2, x_3);
return x_26;
}
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil___spec__2___rarg), 4, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_MonadParsec_takeUntil___spec__1___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_String_Iterator_remaining___main(x_1);
x_3 = l_String_Iterator_extract___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil___spec__2___rarg(x_0, x_2, x_3, x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_MonadParsec_takeUntil___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_MonadParsec_takeUntil___spec__1___rarg___lambda__1), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::apply_2(x_2, lean::box(0), x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_MonadParsec_takeUntil___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_MonadParsec_takeUntil___spec__1___rarg), 2, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeUntil___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_MonadParsec_takeUntil___spec__1___rarg(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeUntil(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeUntil___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_MonadParsec_takeUntil___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_MonadParsec_takeUntil___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeUntil___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeUntil___rarg(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeUntil___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_takeUntil(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil1___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = l_String_Iterator_hasNext___main(x_3);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
x_9 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_2, x_3);
return x_9;
}
else
{
uint32 x_10; obj* x_11; obj* x_13; uint8 x_14; 
x_10 = l_String_Iterator_curr___main(x_3);
x_11 = lean::box_uint32(x_10);
lean::inc(x_0);
x_13 = lean::apply_1(x_0, x_11);
x_14 = lean::unbox(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_sub(x_1, x_15);
lean::dec(x_1);
x_18 = lean::string_push(x_2, x_10);
x_19 = l_String_Iterator_next___main(x_3);
x_1 = x_16;
x_2 = x_18;
x_3 = x_19;
goto _start;
}
else
{
obj* x_23; 
lean::dec(x_1);
lean::dec(x_0);
x_23 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_2, x_3);
return x_23;
}
}
}
else
{
obj* x_26; 
lean::dec(x_1);
lean::dec(x_0);
x_26 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_2, x_3);
return x_26;
}
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil1___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil1___spec__3___rarg), 4, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_takeUntil1___spec__2___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_String_Iterator_remaining___main(x_2);
x_4 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil1___spec__3___rarg(x_0, x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_takeUntil1___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_takeUntil1___spec__2___rarg___lambda__1), 3, 2);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_2);
x_7 = lean::apply_2(x_3, lean::box(0), x_6);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_takeUntil1___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_takeUntil1___spec__2___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_String_Iterator_hasNext___main(x_3);
if (x_4 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
x_11 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_9, x_10, x_8, x_8);
return x_11;
}
else
{
uint32 x_12; obj* x_13; obj* x_15; uint8 x_16; 
x_12 = l_String_Iterator_curr___main(x_3);
x_13 = lean::box_uint32(x_12);
lean::inc(x_13);
x_15 = lean::apply_1(x_1, x_13);
x_16 = lean::unbox(x_15);
if (x_16 == 0)
{
obj* x_18; obj* x_19; 
lean::dec(x_0);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_18, 0, x_3);
lean::closure_set(x_18, 1, x_13);
x_19 = lean::apply_2(x_2, lean::box(0), x_18);
return x_19;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_13);
lean::dec(x_3);
lean::dec(x_2);
x_23 = l_Char_quoteCore(x_12);
x_24 = l_Char_HasRepr___closed__1;
x_25 = lean::string_append(x_24, x_23);
lean::dec(x_23);
x_27 = lean::string_append(x_25, x_24);
x_28 = lean::box(0);
x_29 = l_mjoin___rarg___closed__1;
x_30 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_27, x_29, x_28, x_28);
return x_30;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, uint32 x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_Iterator_extract___main___closed__1;
x_5 = lean::string_push(x_4, x_3);
x_6 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_takeUntil1___spec__2___rarg(x_1, x_2, x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_5);
x_9 = lean::apply_2(x_5, lean::box(0), x_7);
lean::inc(x_2);
lean::inc(x_1);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1___rarg___lambda__1), 4, 3);
lean::closure_set(x_12, 0, x_1);
lean::closure_set(x_12, 1, x_2);
lean::closure_set(x_12, 2, x_5);
lean::inc(x_3);
x_14 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_9, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1___rarg___lambda__2___boxed), 4, 3);
lean::closure_set(x_15, 0, x_0);
lean::closure_set(x_15, 1, x_1);
lean::closure_set(x_15, 2, x_2);
x_16 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_14, x_15);
return x_16;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_takeUntil1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeUntil1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeUntil1___rarg), 3, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil1___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_takeUntil1___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_takeUntil1___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_takeUntil1___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_3);
x_5 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1___rarg___lambda__2(x_0, x_1, x_2, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_takeUntil1___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_takeUntil1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_takeUntil1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_5__mkConsumedResult___rarg(uint8 x_0, obj* x_1) {
_start:
{
if (x_0 == 0)
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box(0);
x_3 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_3);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::box(0);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_1);
lean::cnstr_set(x_7, 2, x_5);
return x_7;
}
}
}
obj* l___private_init_lean_parser_parsec_5__mkConsumedResult(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_5__mkConsumedResult___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_5__mkConsumedResult___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = l___private_init_lean_parser_parsec_5__mkConsumedResult___rarg(x_2, x_1);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_5__mkConsumedResult___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_5__mkConsumedResult(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___rarg(obj* x_0, obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = l_String_Iterator_hasNext___main(x_3);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
x_9 = l___private_init_lean_parser_parsec_5__mkConsumedResult___rarg(x_2, x_3);
return x_9;
}
else
{
uint32 x_10; obj* x_11; obj* x_13; uint8 x_14; 
x_10 = l_String_Iterator_curr___main(x_3);
x_11 = lean::box_uint32(x_10);
lean::inc(x_0);
x_13 = lean::apply_1(x_0, x_11);
x_14 = lean::unbox(x_13);
if (x_14 == 0)
{
obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_5__mkConsumedResult___rarg(x_2, x_3);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_21; uint8 x_22; 
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_sub(x_1, x_18);
lean::dec(x_1);
x_21 = l_String_Iterator_next___main(x_3);
x_22 = 1;
x_1 = x_19;
x_2 = x_22;
x_3 = x_21;
goto _start;
}
}
}
else
{
obj* x_26; 
lean::dec(x_1);
lean::dec(x_0);
x_26 = l___private_init_lean_parser_parsec_5__mkConsumedResult___rarg(x_2, x_3);
return x_26;
}
}
}
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
x_5 = l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___rarg(x_0, x_1, x_4, x_3);
return x_5;
}
}
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___rarg(obj* x_0, obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
x_5 = l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___rarg(x_0, x_1, x_4, x_3);
return x_5;
}
}
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_6__takeWhileAux_x_27(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; obj* x_4; 
x_2 = l_String_Iterator_remaining___main(x_1);
x_3 = 0;
x_4 = l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___rarg(x_0, x_2, x_3, x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile_x_27___rarg___lambda__1), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::apply_2(x_2, lean::box(0), x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile_x_27___rarg), 2, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile_x_27(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1_x_27___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_3, 4);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
x_13 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_11);
x_15 = lean::apply_2(x_11, lean::box(0), x_13);
lean::inc(x_2);
lean::inc(x_1);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_satisfy___rarg___lambda__2), 4, 3);
lean::closure_set(x_18, 0, x_1);
lean::closure_set(x_18, 1, x_2);
lean::closure_set(x_18, 2, x_11);
x_19 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_15, x_18);
x_20 = l_Lean_Parser_MonadParsec_takeWhile_x_27___rarg(x_1, x_2);
x_21 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_19, x_20);
return x_21;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1_x_27(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile1_x_27___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1_x_27___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_takeWhile1_x_27(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___at_Lean_Parser_MonadParsec_whitespace___spec__2___rarg(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_Iterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_5__mkConsumedResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_Iterator_curr___main(x_2);
x_9 = l_Char_isWhitespace(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_5__mkConsumedResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; uint8 x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = l_String_Iterator_next___main(x_2);
x_16 = 1;
x_0 = x_13;
x_1 = x_16;
x_2 = x_15;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_5__mkConsumedResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___at_Lean_Parser_MonadParsec_whitespace___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___at_Lean_Parser_MonadParsec_whitespace___spec__2___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1___rarg___lambda__1(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; 
x_1 = l_String_Iterator_remaining___main(x_0);
x_2 = 0;
x_3 = l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___at_Lean_Parser_MonadParsec_whitespace___spec__2___rarg(x_1, x_2, x_0);
return x_3;
}
}
obj* _init_l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1___rarg___lambda__1), 1, 0);
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1___rarg___closed__1;
x_5 = lean::apply_2(x_1, lean::box(0), x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1___rarg), 1, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_whitespace___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_whitespace(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_whitespace___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___at_Lean_Parser_MonadParsec_whitespace___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___at_Lean_Parser_MonadParsec_whitespace___spec__2___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___at_Lean_Parser_MonadParsec_whitespace___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_6__takeWhileAux_x_27___main___at_Lean_Parser_MonadParsec_whitespace___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_whitespace___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_whitespace___rarg(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_whitespace___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_whitespace(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_lexeme___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_4, 3);
lean::inc(x_6);
lean::dec(x_4);
x_9 = l_Lean_Parser_MonadParsec_whitespace___rarg(x_0, x_1);
lean::dec(x_0);
x_11 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_3, x_9);
return x_11;
}
}
obj* l_Lean_Parser_MonadParsec_lexeme(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_lexeme___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_lexeme___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_lexeme___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_lexeme___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_lexeme(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_num___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_Iterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_Iterator_curr___main(x_2);
x_9 = l_Char_isDigit(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_Iterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_num___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_num___spec__3___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_num___spec__2___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_String_Iterator_remaining___main(x_1);
x_3 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_num___spec__3___rarg(x_2, x_0, x_1);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_num___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_num___spec__2___rarg___lambda__1), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::apply_2(x_2, lean::box(0), x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_num___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_num___spec__2___rarg), 2, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_num___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, uint32 x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_String_Iterator_extract___main___closed__1;
x_4 = lean::string_push(x_3, x_2);
x_5 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_num___spec__2___rarg(x_1, x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_num___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_4);
x_8 = lean::apply_2(x_4, lean::box(0), x_6);
lean::inc(x_1);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_digit___rarg___lambda__1), 3, 2);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_4);
lean::inc(x_2);
x_12 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_8, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_num___spec__1___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
x_14 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_num___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_num___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_MonadParsec_num___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_String_toNat), 1, 0);
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_num___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_10; obj* x_11; obj* x_12; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_num___spec__1___rarg(x_0, x_1);
x_11 = l_Lean_Parser_MonadParsec_num___rarg___closed__1;
x_12 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_11, x_10);
return x_12;
}
}
obj* l_Lean_Parser_MonadParsec_num(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_num___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_num___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_parsec_4__takeWhileAux___main___at_Lean_Parser_MonadParsec_num___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_num___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_MonadParsec_num___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_num___spec__1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_num___spec__1___rarg___lambda__1(x_0, x_1, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_num___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_MonadParsec_num___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_num___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_num(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("at least ");
return x_0;
}
}
obj* _init_l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" characters");
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = l_String_Iterator_remaining___main(x_3);
x_5 = lean::nat_dec_le(x_0, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_2);
x_8 = l_Nat_repr(x_0);
x_9 = l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1___closed__1;
x_10 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_12 = l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1___closed__2;
x_13 = lean::string_append(x_10, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Dlist_singleton___rarg), 2, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::box(0);
x_16 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_17 = l_Lean_Parser_MonadParsec_error___rarg(x_1, lean::box(0), x_16, x_14, x_15, x_15);
return x_17;
}
else
{
obj* x_20; obj* x_23; obj* x_26; obj* x_27; 
lean::dec(x_1);
lean::dec(x_0);
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
x_26 = lean::box(0);
x_27 = lean::apply_2(x_23, lean::box(0), x_26);
return x_27;
}
}
}
obj* l_Lean_Parser_MonadParsec_ensure___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_8 = lean::apply_2(x_5, lean::box(0), x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_9, 0, x_2);
lean::closure_set(x_9, 1, x_1);
lean::closure_set(x_9, 2, x_0);
x_10 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_MonadParsec_ensure(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_ensure___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_ensure___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_ensure(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_pos___rarg___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_Lean_Parser_MonadParsec_pos___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_pos___rarg___lambda__1___boxed), 1, 0);
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_pos___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_14 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_15 = lean::apply_2(x_11, lean::box(0), x_14);
x_16 = l_Lean_Parser_MonadParsec_pos___rarg___closed__1;
x_17 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_16, x_15);
return x_17;
}
}
obj* l_Lean_Parser_MonadParsec_pos(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_pos___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_pos___rarg___lambda__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_pos___rarg___lambda__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_pos___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_pos(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_notFollowedBy___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; obj* x_4; 
x_2 = 1;
x_3 = lean::box(x_2);
x_4 = lean::apply_2(x_0, lean::box(0), x_3);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_notFollowedBy___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, uint8 x_4) {
_start:
{
if (x_4 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_0);
x_7 = lean::box(0);
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___rarg(x_1, lean::box(0), x_2, x_8, x_6, x_7);
return x_9;
}
else
{
obj* x_13; obj* x_14; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_13 = lean::box(0);
x_14 = lean::apply_2(x_3, lean::box(0), x_13);
return x_14;
}
}
}
obj* l_Lean_Parser_MonadParsec_notFollowedBy___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_10; obj* x_13; obj* x_15; uint8 x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_10, 4);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
lean::dec(x_10);
x_18 = 0;
x_19 = lean::box(x_18);
lean::inc(x_15);
x_21 = lean::apply_2(x_15, lean::box(0), x_19);
x_22 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_2, x_21);
lean::inc(x_15);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_notFollowedBy___rarg___lambda__1___boxed), 2, 1);
lean::closure_set(x_24, 0, x_15);
x_25 = lean::apply_3(x_7, lean::box(0), x_22, x_24);
x_26 = lean::cnstr_get(x_3, 1);
lean::inc(x_26);
x_28 = l_Lean_Parser_MonadParsec_lookahead___rarg___closed__1;
x_29 = lean::apply_3(x_26, lean::box(0), x_28, x_25);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_notFollowedBy___rarg___lambda__2___boxed), 5, 4);
lean::closure_set(x_30, 0, x_6);
lean::closure_set(x_30, 1, x_3);
lean::closure_set(x_30, 2, x_4);
lean::closure_set(x_30, 3, x_15);
x_31 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_29, x_30);
return x_31;
}
}
obj* l_Lean_Parser_MonadParsec_notFollowedBy___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_11 = lean::apply_2(x_8, lean::box(0), x_10);
lean::inc(x_6);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_notFollowedBy___rarg___lambda__3), 7, 6);
lean::closure_set(x_13, 0, x_3);
lean::closure_set(x_13, 1, x_0);
lean::closure_set(x_13, 2, x_4);
lean::closure_set(x_13, 3, x_1);
lean::closure_set(x_13, 4, x_5);
lean::closure_set(x_13, 5, x_6);
x_14 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_11, x_13);
return x_14;
}
}
obj* l_Lean_Parser_MonadParsec_notFollowedBy(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_notFollowedBy___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_notFollowedBy___rarg___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_notFollowedBy___rarg___lambda__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_notFollowedBy___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_4);
x_6 = l_Lean_Parser_MonadParsec_notFollowedBy___rarg___lambda__2(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_notFollowedBy___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_notFollowedBy___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_notFollowedBy___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_notFollowedBy(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("end of input");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = l_String_Iterator_remaining___main(x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_3, x_4);
lean::dec(x_3);
if (x_5 == 0)
{
uint32 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_1);
x_8 = l_String_Iterator_curr___main(x_2);
x_9 = l_Char_quoteCore(x_8);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_10, x_9);
lean::dec(x_9);
x_13 = lean::string_append(x_11, x_10);
x_14 = lean::box(0);
x_15 = l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___closed__1;
x_16 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_13, x_15, x_14, x_14);
return x_16;
}
else
{
obj* x_18; obj* x_21; obj* x_24; obj* x_25; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = lean::box(0);
x_25 = lean::apply_2(x_21, lean::box(0), x_24);
return x_25;
}
}
}
obj* l_Lean_Parser_MonadParsec_eoi___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_7 = lean::apply_2(x_4, lean::box(0), x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_0);
x_9 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_eoi(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_eoi___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_eoi___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_eoi(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::apply_2(x_1, lean::box(0), x_3);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux___main___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::inc(x_0);
x_9 = l_Lean_Parser_MonadParsec_many1Aux___main___rarg(x_1, lean::box(0), x_0, x_2, x_3);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::box(0);
lean::inc(x_13);
x_18 = lean::apply_2(x_13, lean::box(0), x_16);
x_19 = lean::apply_3(x_6, lean::box(0), x_9, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_many1Aux___main___rarg___lambda__1), 3, 2);
lean::closure_set(x_20, 0, x_5);
lean::closure_set(x_20, 1, x_13);
x_21 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_19, x_20);
return x_21;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux___main___rarg___lambda__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::apply_2(x_5, lean::box(0), x_9);
return x_10;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_13; obj* x_14; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_4, x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::inc(x_9);
lean::inc(x_3);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_many1Aux___main___rarg___lambda__2___boxed), 6, 5);
lean::closure_set(x_13, 0, x_2);
lean::closure_set(x_13, 1, x_0);
lean::closure_set(x_13, 2, x_3);
lean::closure_set(x_13, 3, x_8);
lean::closure_set(x_13, 4, x_9);
x_14 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_3, x_13);
return x_14;
}
else
{
obj* x_15; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_0, 1);
lean::inc(x_15);
lean::dec(x_0);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_many1Aux___main___rarg___lambda__3), 2, 1);
lean::closure_set(x_18, 0, x_2);
x_19 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_3, x_18);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_many1Aux___main___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux___main___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_many1Aux___main___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_many1Aux___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_many1Aux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_many1Aux___main___rarg(x_0, lean::box(0), x_3, x_4, x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_many1Aux___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_many1Aux___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_many1Aux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_many1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_12; obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
lean::dec(x_7);
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::cnstr_get(x_1, 0);
lean::inc(x_15);
lean::dec(x_1);
x_18 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_19 = lean::apply_2(x_15, lean::box(0), x_18);
x_20 = l_Lean_Parser_MonadParsec_remaining___rarg___closed__1;
x_21 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_20, x_19);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_many1Aux___main___rarg___boxed), 5, 4);
lean::closure_set(x_22, 0, x_0);
lean::closure_set(x_22, 1, lean::box(0));
lean::closure_set(x_22, 2, x_3);
lean::closure_set(x_22, 3, x_4);
x_23 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_21, x_22);
return x_23;
}
}
obj* l_Lean_Parser_MonadParsec_many1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_many1___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_many1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_many1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_many1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_many1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_many___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; obj* x_12; obj* x_15; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::inc(x_3);
x_8 = l_Lean_Parser_MonadParsec_many1___rarg(x_0, x_1, lean::box(0), x_3, x_4);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
x_17 = lean::apply_3(x_5, lean::box(0), x_8, x_16);
return x_17;
}
}
obj* l_Lean_Parser_MonadParsec_many(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_many___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_many___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_many___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_many___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_many(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_2, x_5);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 4);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
lean::inc(x_1);
x_14 = l_Lean_Parser_MonadParsec_many1Aux_x_27___main___rarg(x_0, x_1, x_6);
lean::dec(x_6);
x_16 = lean::cnstr_get(x_7, 1);
lean::inc(x_16);
lean::dec(x_7);
x_19 = lean::box(0);
x_20 = lean::apply_2(x_16, lean::box(0), x_19);
x_21 = lean::apply_3(x_11, lean::box(0), x_14, x_20);
x_22 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_1, x_21);
return x_22;
}
else
{
obj* x_23; obj* x_26; obj* x_28; obj* x_31; obj* x_32; obj* x_33; 
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
lean::dec(x_0);
x_26 = lean::cnstr_get(x_23, 4);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_23, 1);
lean::inc(x_28);
lean::dec(x_23);
x_31 = lean::box(0);
x_32 = lean::apply_2(x_28, lean::box(0), x_31);
x_33 = lean::apply_4(x_26, lean::box(0), lean::box(0), x_1, x_32);
return x_33;
}
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_many1Aux_x_27___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_many1Aux_x_27___main___rarg(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_many1Aux_x_27___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_many1Aux_x_27___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_many1Aux_x_27___rarg___boxed), 3, 0);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_many1Aux_x_27___rarg(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_many1Aux_x_27(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_many1_x_27___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_10; obj* x_13; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
lean::dec(x_1);
x_19 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_20 = lean::apply_2(x_16, lean::box(0), x_19);
x_21 = l_Lean_Parser_MonadParsec_remaining___rarg___closed__1;
x_22 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_21, x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_many1Aux_x_27___main___rarg___boxed), 3, 2);
lean::closure_set(x_23, 0, x_3);
lean::closure_set(x_23, 1, x_4);
x_24 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_22, x_23);
return x_24;
}
}
obj* l_Lean_Parser_MonadParsec_many1_x_27(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_many1_x_27___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_many1_x_27___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_many1_x_27___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_many1_x_27___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_many1_x_27(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_many_x_27___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_12; obj* x_15; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_31; obj* x_34; obj* x_35; obj* x_36; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
lean::dec(x_1);
x_21 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_22 = lean::apply_2(x_18, lean::box(0), x_21);
x_23 = l_Lean_Parser_MonadParsec_remaining___rarg___closed__1;
x_24 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_23, x_22);
lean::inc(x_3);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_many1Aux_x_27___main___rarg___boxed), 3, 2);
lean::closure_set(x_26, 0, x_3);
lean::closure_set(x_26, 1, x_4);
x_27 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_24, x_26);
x_28 = lean::cnstr_get(x_3, 0);
lean::inc(x_28);
lean::dec(x_3);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
x_34 = lean::box(0);
x_35 = lean::apply_2(x_31, lean::box(0), x_34);
x_36 = lean::apply_3(x_5, lean::box(0), x_27, x_35);
return x_36;
}
}
obj* l_Lean_Parser_MonadParsec_many_x_27(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_many_x_27___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_many_x_27___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_many_x_27___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_many_x_27___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_many_x_27(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_sepBy1___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_MonadParsec_sepBy1___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_sepBy1___rarg___lambda__1), 2, 0);
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_sepBy1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_7, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
lean::dec(x_11);
x_16 = l_Lean_Parser_MonadParsec_sepBy1___rarg___closed__1;
lean::inc(x_5);
x_18 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_16, x_5);
x_19 = lean::cnstr_get(x_7, 4);
lean::inc(x_19);
lean::dec(x_7);
x_22 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_6, x_5);
x_23 = l_Lean_Parser_MonadParsec_many___rarg(x_0, x_1, lean::box(0), x_4, x_22);
x_24 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_18, x_23);
return x_24;
}
}
obj* l_Lean_Parser_MonadParsec_sepBy1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_sepBy1___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_sepBy1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_MonadParsec_sepBy1___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_sepBy1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_sepBy1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_SepBy___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; obj* x_19; 
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::inc(x_4);
x_10 = l_Lean_Parser_MonadParsec_sepBy1___rarg(x_0, x_1, lean::box(0), lean::box(0), x_4, x_5, x_6);
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
lean::dec(x_4);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::box(0);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
x_19 = lean::apply_3(x_7, lean::box(0), x_10, x_18);
return x_19;
}
}
obj* l_Lean_Parser_MonadParsec_SepBy(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_SepBy___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_SepBy___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_MonadParsec_SepBy___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_SepBy___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_SepBy(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_MonadParsec_fixAux___main___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("fixAux: no progress");
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_fixAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_10; obj* x_12; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_4, x_7);
lean::inc(x_3);
x_10 = l_Lean_Parser_MonadParsec_fixAux___main___rarg(x_0, x_1, lean::box(0), x_3, x_8);
lean::dec(x_8);
x_12 = lean::apply_1(x_3, x_10);
return x_12;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_3);
x_14 = lean::box(0);
x_15 = l_Lean_Parser_MonadParsec_fixAux___main___rarg___closed__1;
x_16 = l_mjoin___rarg___closed__1;
x_17 = l_Lean_Parser_MonadParsec_error___rarg(x_1, lean::box(0), x_15, x_16, x_14, x_14);
return x_17;
}
}
}
obj* l_Lean_Parser_MonadParsec_fixAux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_fixAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_fixAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_fixAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_fixAux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_fixAux___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_fixAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_fixAux___main___rarg(x_0, x_1, lean::box(0), x_4, x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_fixAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_fixAux___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_fixAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_fixAux___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_fixAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_fixAux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_fix___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_add(x_3, x_4);
x_6 = l_Lean_Parser_MonadParsec_fixAux___main___rarg(x_0, x_1, lean::box(0), x_2, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_fix___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_12; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
lean::dec(x_7);
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::cnstr_get(x_1, 0);
lean::inc(x_15);
x_17 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_18 = lean::apply_2(x_15, lean::box(0), x_17);
x_19 = l_Lean_Parser_MonadParsec_remaining___rarg___closed__1;
x_20 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_19, x_18);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_fix___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_21, 0, x_0);
lean::closure_set(x_21, 1, x_1);
lean::closure_set(x_21, 2, x_4);
x_22 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_20, x_21);
return x_22;
}
}
obj* l_Lean_Parser_MonadParsec_fix(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_fix___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_fix___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_fix___rarg___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_fix___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_fix___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_fix___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_fix(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_foldrAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_30; obj* x_31; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_4, x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 2);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
lean::dec(x_15);
lean::inc(x_2);
lean::inc(x_1);
x_22 = lean::apply_4(x_17, lean::box(0), lean::box(0), x_1, x_2);
lean::inc(x_3);
x_24 = l_Lean_Parser_MonadParsec_foldrAux___main___rarg(x_0, x_1, x_2, x_3, x_8);
lean::dec(x_8);
x_26 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_22, x_24);
x_27 = lean::cnstr_get(x_11, 1);
lean::inc(x_27);
lean::dec(x_11);
x_30 = lean::apply_2(x_27, lean::box(0), x_3);
x_31 = lean::apply_3(x_9, lean::box(0), x_26, x_30);
return x_31;
}
else
{
obj* x_34; obj* x_37; obj* x_40; 
lean::dec(x_1);
lean::dec(x_2);
x_34 = lean::cnstr_get(x_0, 0);
lean::inc(x_34);
lean::dec(x_0);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
x_40 = lean::apply_2(x_37, lean::box(0), x_3);
return x_40;
}
}
}
obj* l_Lean_Parser_MonadParsec_foldrAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldrAux___main___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_foldrAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_foldrAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_foldrAux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_foldrAux___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_foldrAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_foldrAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_foldrAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldrAux___rarg___boxed), 5, 0);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_foldrAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_foldrAux___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_foldrAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_foldrAux(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_foldr___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_String_Iterator_remaining___main(x_4);
x_6 = l_Lean_Parser_MonadParsec_foldrAux___main___rarg(x_0, x_1, x_2, x_3, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_foldr___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_14 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_15 = lean::apply_2(x_11, lean::box(0), x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldr___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_16, 0, x_4);
lean::closure_set(x_16, 1, x_5);
lean::closure_set(x_16, 2, x_6);
lean::closure_set(x_16, 3, x_7);
x_17 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_15, x_16);
return x_17;
}
}
obj* l_Lean_Parser_MonadParsec_foldr(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldr___rarg___boxed), 8, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_foldr___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_foldr___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_foldr___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_MonadParsec_foldr___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_2);
lean::dec(x_3);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_foldr___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_foldr(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_9; 
lean::inc(x_0);
x_8 = lean::apply_2(x_0, x_1, x_6);
x_9 = l_Lean_Parser_MonadParsec_foldlAux___main___rarg(x_2, lean::box(0), lean::box(0), x_3, x_0, x_4, x_8, x_5);
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_19; obj* x_20; obj* x_21; obj* x_24; obj* x_27; obj* x_28; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_7, x_10);
x_12 = lean::cnstr_get(x_3, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_0, 1);
lean::inc(x_14);
lean::inc(x_5);
lean::inc(x_3);
lean::inc(x_6);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldlAux___main___rarg___lambda__1___boxed), 7, 6);
lean::closure_set(x_19, 0, x_4);
lean::closure_set(x_19, 1, x_6);
lean::closure_set(x_19, 2, x_0);
lean::closure_set(x_19, 3, x_3);
lean::closure_set(x_19, 4, x_5);
lean::closure_set(x_19, 5, x_11);
x_20 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_5, x_19);
x_21 = lean::cnstr_get(x_3, 0);
lean::inc(x_21);
lean::dec(x_3);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
x_27 = lean::apply_2(x_24, lean::box(0), x_6);
x_28 = lean::apply_3(x_12, lean::box(0), x_20, x_27);
return x_28;
}
else
{
obj* x_32; obj* x_35; obj* x_38; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_0);
x_32 = lean::cnstr_get(x_3, 0);
lean::inc(x_32);
lean::dec(x_3);
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
lean::dec(x_32);
x_38 = lean::apply_2(x_35, lean::box(0), x_6);
return x_38;
}
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldlAux___main___rarg___boxed), 8, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_MonadParsec_foldlAux___main___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_MonadParsec_foldlAux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_7);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_foldlAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_MonadParsec_foldlAux___main___rarg(x_0, lean::box(0), lean::box(0), x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldlAux___rarg___boxed), 9, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_MonadParsec_foldlAux___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_8);
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_foldlAux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_foldl___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = l_String_Iterator_remaining___main(x_5);
x_7 = l_Lean_Parser_MonadParsec_foldlAux___main___rarg(x_0, lean::box(0), lean::box(0), x_1, x_2, x_3, x_4, x_6);
lean::dec(x_6);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_foldl___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_13 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_14 = lean::apply_2(x_10, lean::box(0), x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldl___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_15, 0, x_0);
lean::closure_set(x_15, 1, x_4);
lean::closure_set(x_15, 2, x_5);
lean::closure_set(x_15, 3, x_7);
lean::closure_set(x_15, 4, x_6);
x_16 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_14, x_15);
return x_16;
}
}
obj* l_Lean_Parser_MonadParsec_foldl(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_foldl___rarg___boxed), 8, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_foldl___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_foldl___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_foldl___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_MonadParsec_foldl___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_2);
lean::dec(x_3);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_foldl___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_foldl(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_unexpected___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::box(0);
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_2, x_4, x_3, x_3);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_unexpected(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_unexpected___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_unexpected___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_unexpected___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_unexpected___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_unexpected(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = lean::box(0);
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_2, x_6, x_4, x_5);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_unexpectedAt___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_unexpectedAt___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_unexpectedAt(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_MonadParsec_longestMatch___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
x_5 = l_Option_getOrElse___main___rarg(x_2, x_4);
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_0);
lean::cnstr_set(x_6, 2, x_1);
lean::cnstr_set(x_6, 3, x_3);
x_7 = 0;
x_8 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*1, x_7);
x_9 = x_8;
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_MonadParsec_longestMatch___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_MonadParsec_longestMatch___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
if (lean::obj_tag(x_2) == 0)
{
obj* x_12; 
x_12 = lean::cnstr_get(x_2, 2);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_20; uint8 x_23; 
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_2, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_3, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_16, 1);
lean::inc(x_20);
lean::dec(x_16);
x_23 = lean::nat_dec_lt(x_18, x_20);
if (x_23 == 0)
{
obj* x_24; uint8 x_25; 
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_24 = x_2;
} else {
 lean::dec(x_2);
 x_24 = lean::box(0);
}
x_25 = lean::nat_dec_lt(x_20, x_18);
lean::dec(x_18);
lean::dec(x_20);
if (x_25 == 0)
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_1);
lean::cnstr_set(x_28, 1, x_14);
if (lean::is_scalar(x_24)) {
 x_29 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_29 = x_24;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_3);
lean::cnstr_set(x_29, 2, x_12);
x_30 = lean::apply_2(x_7, lean::box(0), x_29);
return x_30;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_14);
x_32 = lean::box(0);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_1);
lean::cnstr_set(x_33, 1, x_32);
if (lean::is_scalar(x_24)) {
 x_34 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_34 = x_24;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_3);
lean::cnstr_set(x_34, 2, x_12);
x_35 = lean::apply_2(x_7, lean::box(0), x_34);
return x_35;
}
}
else
{
obj* x_41; 
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_18);
lean::dec(x_20);
x_41 = lean::apply_2(x_7, lean::box(0), x_2);
return x_41;
}
}
else
{
obj* x_44; 
lean::dec(x_12);
lean::dec(x_2);
x_44 = lean::box(0);
x_10 = x_44;
goto lbl_11;
}
}
else
{
obj* x_46; 
lean::dec(x_2);
x_46 = lean::box(0);
x_10 = x_46;
goto lbl_11;
}
lbl_11:
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_10);
x_48 = lean::box(0);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_1);
lean::cnstr_set(x_49, 1, x_48);
x_50 = lean::box(0);
x_51 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_3);
lean::cnstr_set(x_51, 2, x_50);
x_52 = lean::apply_2(x_7, lean::box(0), x_51);
return x_52;
}
}
}
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___lambda__1), 4, 3);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_1);
x_6 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_3, x_5);
return x_6;
}
}
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; obj* x_8; obj* x_11; 
lean::dec(x_3);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_2(x_8, lean::box(0), x_1);
return x_11;
}
else
{
obj* x_12; obj* x_15; obj* x_18; obj* x_20; obj* x_22; obj* x_25; obj* x_27; uint8 x_30; 
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
lean::dec(x_0);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_3, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_20, 1);
lean::inc(x_22);
lean::dec(x_20);
x_25 = lean::cnstr_get(x_18, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_25, 1);
lean::inc(x_27);
lean::dec(x_25);
x_30 = lean::nat_dec_lt(x_22, x_27);
if (x_30 == 0)
{
obj* x_31; uint8 x_32; 
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_31 = x_1;
} else {
 lean::dec(x_1);
 x_31 = lean::box(0);
}
x_32 = lean::nat_dec_lt(x_27, x_22);
lean::dec(x_27);
if (x_32 == 0)
{
obj* x_34; obj* x_35; uint8 x_36; 
x_34 = l_Lean_Parser_ParsecT_merge___rarg(x_3, x_18);
x_35 = lean::cnstr_get(x_2, 1);
x_36 = lean::nat_dec_lt(x_35, x_22);
lean::dec(x_22);
if (x_36 == 0)
{
uint8 x_38; obj* x_39; obj* x_40; obj* x_41; 
x_38 = 0;
if (lean::is_scalar(x_31)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_31;
}
lean::cnstr_set(x_39, 0, x_34);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_38);
x_40 = x_39;
x_41 = lean::apply_2(x_15, lean::box(0), x_40);
return x_41;
}
else
{
uint8 x_42; obj* x_43; obj* x_44; obj* x_45; 
x_42 = 1;
if (lean::is_scalar(x_31)) {
 x_43 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_43 = x_31;
}
lean::cnstr_set(x_43, 0, x_34);
lean::cnstr_set_scalar(x_43, sizeof(void*)*1, x_42);
x_44 = x_43;
x_45 = lean::apply_2(x_15, lean::box(0), x_44);
return x_45;
}
}
else
{
uint8 x_48; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_22);
lean::dec(x_18);
x_48 = 1;
if (lean::is_scalar(x_31)) {
 x_49 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_49 = x_31;
}
lean::cnstr_set(x_49, 0, x_3);
lean::cnstr_set_scalar(x_49, sizeof(void*)*1, x_48);
x_50 = x_49;
x_51 = lean::apply_2(x_15, lean::box(0), x_50);
return x_51;
}
}
else
{
obj* x_56; 
lean::dec(x_3);
lean::dec(x_22);
lean::dec(x_27);
lean::dec(x_18);
x_56 = lean::apply_2(x_15, lean::box(0), x_1);
return x_56;
}
}
}
}
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; 
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_2);
lean::inc(x_7);
lean::inc(x_1);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___lambda__2), 5, 4);
lean::closure_set(x_14, 0, x_1);
lean::closure_set(x_14, 1, x_7);
lean::closure_set(x_14, 2, x_2);
lean::closure_set(x_14, 3, x_3);
x_15 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_4, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___lambda__3___boxed), 4, 3);
lean::closure_set(x_16, 0, x_1);
lean::closure_set(x_16, 1, x_7);
lean::closure_set(x_16, 2, x_5);
x_17 = lean::apply_3(x_8, lean::box(0), x_15, x_16);
x_18 = lean::cnstr_get(x_6, 1);
lean::inc(x_18);
lean::dec(x_6);
x_21 = l_Lean_Parser_MonadParsec_lookahead___rarg___closed__1;
x_22 = lean::apply_3(x_18, lean::box(0), x_21, x_17);
return x_22;
}
}
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_14; obj* x_17; obj* x_20; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = lean::apply_2(x_17, lean::box(0), x_7);
return x_20;
}
else
{
obj* x_21; obj* x_23; obj* x_26; obj* x_34; obj* x_35; obj* x_36; 
x_21 = lean::cnstr_get(x_8, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_8, 1);
lean::inc(x_23);
lean::dec(x_8);
x_26 = lean::cnstr_get(x_0, 1);
lean::inc(x_26);
lean::inc(x_6);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_1);
lean::inc(x_0);
x_34 = l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg(x_0, x_1, lean::box(0), x_3, x_4, x_5, x_6, x_7, x_23);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___lambda__4), 8, 7);
lean::closure_set(x_35, 0, x_3);
lean::closure_set(x_35, 1, x_0);
lean::closure_set(x_35, 2, x_4);
lean::closure_set(x_35, 3, x_5);
lean::closure_set(x_35, 4, x_21);
lean::closure_set(x_35, 5, x_6);
lean::closure_set(x_35, 6, x_1);
x_36 = lean::apply_4(x_26, lean::box(0), lean::box(0), x_34, x_35);
return x_36;
}
}
}
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___boxed), 9, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_longestMatch___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ExceptT_Monad___rarg___lambda__8___boxed), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::apply_2(x_0, lean::box(0), x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_MonadParsec_longestMatch___rarg___lambda__2___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("longestMatch: Empty List");
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_longestMatch___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_8 = lean::box(0);
x_9 = l_Lean_Parser_MonadParsec_longestMatch___rarg___lambda__2___closed__1;
x_10 = l_mjoin___rarg___closed__1;
x_11 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_MonadParsec_longestMatch___spec__1___rarg(x_9, x_10, x_8, x_8, x_7);
lean::inc(x_3);
x_13 = l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg(x_0, x_1, lean::box(0), x_2, x_3, x_4, x_7, x_11, x_5);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_longestMatch___rarg___lambda__1), 2, 1);
lean::closure_set(x_14, 0, x_6);
x_15 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
obj* l_Lean_Parser_MonadParsec_longestMatch___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
lean::inc(x_7);
x_11 = lean::apply_2(x_7, lean::box(0), x_9);
lean::inc(x_11);
lean::inc(x_5);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_longestMatch___rarg___lambda__2), 8, 7);
lean::closure_set(x_14, 0, x_0);
lean::closure_set(x_14, 1, x_1);
lean::closure_set(x_14, 2, x_3);
lean::closure_set(x_14, 3, x_5);
lean::closure_set(x_14, 4, x_11);
lean::closure_set(x_14, 5, x_4);
lean::closure_set(x_14, 6, x_7);
x_15 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_11, x_14);
return x_15;
}
}
obj* l_Lean_Parser_MonadParsec_longestMatch(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_longestMatch___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_MonadParsec_longestMatch___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_MonadParsec_longestMatch___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_MonadParsec_longestMatch___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_MonadParsec_longestMatch___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___lambda__3(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_2);
return x_9;
}
}
obj* l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mfoldr___main___at_Lean_Parser_MonadParsec_longestMatch___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_longestMatch___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_longestMatch___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_longestMatch___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_longestMatch(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_observing___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_1);
x_6 = lean::apply_2(x_2, lean::box(0), x_5);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_observing___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
lean::dec(x_11);
x_16 = l_ExceptT_lift___rarg___closed__1;
x_17 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_16, x_4);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_observing___rarg___lambda__1), 2, 1);
lean::closure_set(x_18, 0, x_8);
x_19 = lean::apply_3(x_5, lean::box(0), x_17, x_18);
return x_19;
}
}
obj* l_Lean_Parser_MonadParsec_observing(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_observing___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_observing___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_observing___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_observing___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_observing(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_parse___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_ParsecT_run___rarg(x_0, lean::box(0), lean::box(0), x_2, x_3, x_4);
return x_5;
}
}
obj* l_Lean_Parser_ParsecT_parse(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_parse___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_parse___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_ParsecT_parse___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_ParsecT_parse___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParsecT_parse(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_ParsecT_parseWithEoi___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_10; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = l_Option_getOrElse___main___rarg(x_4, x_6);
x_14 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_2);
lean::cnstr_set(x_14, 2, x_3);
lean::cnstr_set(x_14, 3, x_5);
x_15 = 0;
x_16 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set_scalar(x_16, sizeof(void*)*1, x_15);
x_17 = x_16;
x_18 = lean::apply_2(x_10, lean::box(0), x_17);
return x_18;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_ParsecT_parseWithEoi___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_ParsecT_parseWithEoi___spec__2___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_ParsecT_parseWithEoi___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_15; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
x_9 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 lean::cnstr_set(x_4, 2, lean::box(0));
 x_11 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
lean::dec(x_0);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bindMkRes___rarg), 2, 1);
lean::closure_set(x_18, 0, x_9);
x_19 = l_String_Iterator_remaining___main(x_5);
x_20 = lean::mk_nat_obj(0u);
x_21 = lean::nat_dec_eq(x_19, x_20);
lean::dec(x_19);
if (x_21 == 0)
{
uint32 x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_37; 
lean::dec(x_3);
lean::dec(x_11);
lean::dec(x_2);
x_26 = l_String_Iterator_curr___main(x_5);
lean::dec(x_5);
x_28 = l_Char_quoteCore(x_26);
x_29 = l_Char_HasRepr___closed__1;
x_30 = lean::string_append(x_29, x_28);
lean::dec(x_28);
x_32 = lean::string_append(x_30, x_29);
x_33 = lean::box(0);
x_34 = l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___closed__1;
x_35 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_ParsecT_parseWithEoi___spec__2___rarg(x_1, lean::box(0), x_32, x_34, x_33, x_33, x_7);
lean::dec(x_7);
x_37 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_18, x_35);
return x_37;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_5);
lean::dec(x_1);
x_40 = lean::box(0);
if (lean::is_scalar(x_11)) {
 x_41 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_41 = x_11;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_7);
lean::cnstr_set(x_41, 2, x_2);
x_42 = lean::apply_2(x_3, lean::box(0), x_41);
x_43 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_18, x_42);
return x_43;
}
}
else
{
obj* x_47; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_47 = lean::cnstr_get(x_4, 0);
x_49 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_50 = x_4;
} else {
 lean::inc(x_47);
 lean::dec(x_4);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_47);
lean::cnstr_set_scalar(x_51, sizeof(void*)*1, x_49);
x_52 = x_51;
x_53 = lean::apply_2(x_3, lean::box(0), x_52);
return x_53;
}
}
}
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_ParsecT_parseWithEoi___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
x_8 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::inc(x_1);
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_1);
lean::cnstr_set(x_10, 2, x_8);
lean::inc(x_6);
x_12 = lean::apply_2(x_6, lean::box(0), x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_ParsecT_parseWithEoi___spec__1___rarg___lambda__1), 5, 4);
lean::closure_set(x_13, 0, x_4);
lean::closure_set(x_13, 1, x_0);
lean::closure_set(x_13, 2, x_8);
lean::closure_set(x_13, 3, x_6);
x_14 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_ParsecT_parseWithEoi___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_ParsecT_parseWithEoi___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithEoi___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; usize x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
x_10 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_9);
x_11 = x_10;
x_12 = lean::apply_1(x_3, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_run___rarg___lambda__1), 2, 1);
lean::closure_set(x_13, 0, x_0);
x_14 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithEoi___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithEoi___spec__3___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_parseWithEoi___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bindMkRes___rarg), 2, 1);
lean::closure_set(x_17, 0, x_7);
x_18 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_ParsecT_parseWithEoi___spec__1___rarg(x_0, x_5);
lean::inc(x_14);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_Monad___rarg___lambda__9), 4, 3);
lean::closure_set(x_20, 0, x_10);
lean::closure_set(x_20, 1, x_3);
lean::closure_set(x_20, 2, x_14);
x_21 = lean::apply_4(x_1, lean::box(0), lean::box(0), x_18, x_20);
x_22 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_17, x_21);
return x_22;
}
else
{
obj* x_24; uint8 x_26; obj* x_27; obj* x_28; obj* x_31; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_1);
x_24 = lean::cnstr_get(x_2, 0);
x_26 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_27 = x_2;
} else {
 lean::inc(x_24);
 lean::dec(x_2);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_0, 0);
lean::inc(x_28);
lean::dec(x_0);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
if (lean::is_scalar(x_27)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_27;
}
lean::cnstr_set(x_34, 0, x_24);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_26);
x_35 = x_34;
x_36 = lean::apply_2(x_31, lean::box(0), x_35);
return x_36;
}
}
}
obj* l_Lean_Parser_ParsecT_parseWithEoi___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::apply_1(x_1, x_2);
lean::inc(x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_parseWithEoi___rarg___lambda__1), 3, 2);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, x_3);
x_8 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_5, x_7);
return x_8;
}
}
obj* l_Lean_Parser_ParsecT_parseWithEoi___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_parseWithEoi___rarg___lambda__2), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_2);
x_7 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithEoi___spec__3___rarg(x_0, lean::box(0), lean::box(0), x_6, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_ParsecT_parseWithEoi(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_parseWithEoi___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_ParsecT_parseWithEoi___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_ParsecT_parseWithEoi___spec__2___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
lean::dec(x_4);
lean::dec(x_6);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_ParsecT_parseWithEoi___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_ParsecT_parseWithEoi___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_ParsecT_parseWithEoi___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_eoi___at_Lean_Parser_ParsecT_parseWithEoi___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithEoi___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithEoi___spec__3___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithEoi___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithEoi___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_parseWithEoi___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_ParsecT_parseWithEoi___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_ParsecT_parseWithEoi___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParsecT_parseWithEoi(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithLeftOver___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; usize x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::mk_nat_obj(0u);
x_9 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
x_10 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_9);
x_11 = x_10;
x_12 = lean::apply_1(x_3, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_run___rarg___lambda__1), 2, 1);
lean::closure_set(x_13, 0, x_0);
x_14 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithLeftOver___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithLeftOver___spec__1___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_parseWithLeftOver___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 x_8 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bindMkRes___rarg), 2, 1);
lean::closure_set(x_17, 0, x_6);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_List_zip___rarg___lambda__1), 2, 1);
lean::closure_set(x_18, 0, x_2);
x_19 = lean::cnstr_get(x_9, 1);
lean::inc(x_19);
lean::dec(x_9);
x_22 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_8)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_8;
}
lean::cnstr_set(x_23, 0, x_18);
lean::cnstr_set(x_23, 1, x_4);
lean::cnstr_set(x_23, 2, x_22);
x_24 = lean::apply_2(x_19, lean::box(0), x_23);
x_25 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_17, x_24);
return x_25;
}
else
{
obj* x_26; uint8 x_28; obj* x_29; obj* x_30; obj* x_33; obj* x_36; obj* x_37; obj* x_38; 
x_26 = lean::cnstr_get(x_1, 0);
x_28 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_exclusive(x_1)) {
 x_29 = x_1;
} else {
 lean::inc(x_26);
 lean::dec(x_1);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
lean::dec(x_0);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
if (lean::is_scalar(x_29)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_29;
}
lean::cnstr_set(x_36, 0, x_26);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_28);
x_37 = x_36;
x_38 = lean::apply_2(x_33, lean::box(0), x_37);
return x_38;
}
}
}
obj* l_Lean_Parser_ParsecT_parseWithLeftOver___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
x_9 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 x_11 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bindMkRes___rarg), 2, 1);
lean::closure_set(x_12, 0, x_9);
x_13 = lean::apply_1(x_0, x_5);
if (lean::is_scalar(x_11)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_11;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_1);
x_15 = lean::apply_2(x_2, lean::box(0), x_14);
x_16 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_12, x_15);
return x_16;
}
else
{
obj* x_20; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_20 = lean::cnstr_get(x_4, 0);
x_22 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_23 = x_4;
} else {
 lean::inc(x_20);
 lean::dec(x_4);
 x_23 = lean::box(0);
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_20);
lean::cnstr_set_scalar(x_24, sizeof(void*)*1, x_22);
x_25 = x_24;
x_26 = lean::apply_2(x_2, lean::box(0), x_25);
return x_26;
}
}
}
obj* l_Lean_Parser_ParsecT_parseWithLeftOver___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_7 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 x_9 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_bindMkRes___rarg), 2, 1);
lean::closure_set(x_18, 0, x_7);
x_19 = lean::cnstr_get(x_10, 1);
lean::inc(x_19);
lean::dec(x_10);
x_22 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::inc(x_5);
if (lean::is_scalar(x_9)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_9;
}
lean::cnstr_set(x_24, 0, x_5);
lean::cnstr_set(x_24, 1, x_5);
lean::cnstr_set(x_24, 2, x_22);
lean::inc(x_19);
x_26 = lean::apply_2(x_19, lean::box(0), x_24);
lean::inc(x_15);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_parseWithLeftOver___rarg___lambda__2), 5, 4);
lean::closure_set(x_28, 0, x_3);
lean::closure_set(x_28, 1, x_22);
lean::closure_set(x_28, 2, x_19);
lean::closure_set(x_28, 3, x_15);
x_29 = lean::apply_4(x_1, lean::box(0), lean::box(0), x_26, x_28);
x_30 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_18, x_29);
return x_30;
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_39; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_1);
x_32 = lean::cnstr_get(x_2, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_35 = x_2;
} else {
 lean::inc(x_32);
 lean::dec(x_2);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_0, 0);
lean::inc(x_36);
lean::dec(x_0);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
if (lean::is_scalar(x_35)) {
 x_42 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_42 = x_35;
}
lean::cnstr_set(x_42, 0, x_32);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_34);
x_43 = x_42;
x_44 = lean::apply_2(x_39, lean::box(0), x_43);
return x_44;
}
}
}
obj* l_Lean_Parser_ParsecT_parseWithLeftOver___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::apply_1(x_1, x_2);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_parseWithLeftOver___rarg___lambda__1), 2, 1);
lean::closure_set(x_7, 0, x_0);
lean::inc(x_3);
x_9 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_5, x_7);
lean::inc(x_3);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_parseWithLeftOver___rarg___lambda__3), 3, 2);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_3);
x_12 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_9, x_11);
return x_12;
}
}
obj* l_Lean_Parser_ParsecT_parseWithLeftOver___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_parseWithLeftOver___rarg___lambda__4), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_2);
x_7 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithLeftOver___spec__1___rarg(x_0, lean::box(0), lean::box(0), x_6, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_ParsecT_parseWithLeftOver(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_parseWithLeftOver___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithLeftOver___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithLeftOver___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithLeftOver___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_ParsecT_parseWithLeftOver___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ParsecT_parseWithLeftOver___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_ParsecT_parseWithLeftOver___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_ParsecT_parseWithLeftOver___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParsecT_parseWithLeftOver(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; usize x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l___private_init_data_string_basic_5__utf8PrevAux___main___closed__1;
x_5 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_4);
x_6 = x_5;
x_7 = lean::apply_1(x_0, x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
else
{
obj* x_12; obj* x_15; 
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
lean::dec(x_7);
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_12);
return x_15;
}
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_Parsec_parse___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Parsec_parse(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Parsec_parse___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___rarg(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Parsec_parse___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Parsec_parse___rarg(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_Parsec_parse___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Parsec_parse(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_data_tostring(obj*);
obj* initialize_init_data_string_basic(obj*);
obj* initialize_init_data_list_basic(obj*);
obj* initialize_init_control_except(obj*);
obj* initialize_init_data_repr(obj*);
obj* initialize_init_lean_name(obj*);
obj* initialize_init_data_dlist(obj*);
obj* initialize_init_control_monadfail(obj*);
obj* initialize_init_control_combinators(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_parsec(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_tostring(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_string_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_list_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_except(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_repr(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_dlist(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_monadfail(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_combinators(w);
 l_Lean_Parser_Parsec_expected_toString___main___closed__1 = _init_l_Lean_Parser_Parsec_expected_toString___main___closed__1();
lean::mark_persistent(l_Lean_Parser_Parsec_expected_toString___main___closed__1);
 l_Lean_Parser_Parsec_Message_text___rarg___closed__1 = _init_l_Lean_Parser_Parsec_Message_text___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Parsec_Message_text___rarg___closed__1);
 l_Lean_Parser_Parsec_Message_text___rarg___closed__2 = _init_l_Lean_Parser_Parsec_Message_text___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Parsec_Message_text___rarg___closed__2);
 l_Lean_Parser_Parsec_Message_text___rarg___closed__3 = _init_l_Lean_Parser_Parsec_Message_text___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Parsec_Message_text___rarg___closed__3);
 l_Lean_Parser_Parsec_Message_toString___rarg___closed__1 = _init_l_Lean_Parser_Parsec_Message_toString___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Parsec_Message_toString___rarg___closed__1);
 l_Lean_Parser_Parsec_Message_toString___rarg___closed__2 = _init_l_Lean_Parser_Parsec_Message_toString___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Parsec_Message_toString___rarg___closed__2);
 l_Lean_Parser_Parsec_Message_toString___rarg___closed__3 = _init_l_Lean_Parser_Parsec_Message_toString___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Parsec_Message_toString___rarg___closed__3);
 l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1 = _init_l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1);
 l_Lean_Parser_ParsecT_failure___rarg___closed__1 = _init_l_Lean_Parser_ParsecT_failure___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_ParsecT_failure___rarg___closed__1);
 l_Lean_Parser_ParsecT_MonadFail___rarg___closed__1 = _init_l_Lean_Parser_ParsecT_MonadFail___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_ParsecT_MonadFail___rarg___closed__1);
 l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1 = _init_l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1);
 l_Lean_Parser_MonadParsec_remaining___rarg___closed__1 = _init_l_Lean_Parser_MonadParsec_remaining___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_remaining___rarg___closed__1);
 l_Lean_Parser_MonadParsec_hidden___rarg___closed__1 = _init_l_Lean_Parser_MonadParsec_hidden___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_hidden___rarg___closed__1);
 l_Lean_Parser_MonadParsec_try___rarg___closed__1 = _init_l_Lean_Parser_MonadParsec_try___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_try___rarg___closed__1);
 l_Lean_Parser_MonadParsec_lookahead___rarg___closed__1 = _init_l_Lean_Parser_MonadParsec_lookahead___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_lookahead___rarg___closed__1);
 l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1 = _init_l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1);
 l_Lean_Parser_MonadParsec_curr___rarg___closed__1 = _init_l_Lean_Parser_MonadParsec_curr___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_curr___rarg___closed__1);
 l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1___rarg___closed__1 = _init_l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_takeWhile_x_27___at_Lean_Parser_MonadParsec_whitespace___spec__1___rarg___closed__1);
 l_Lean_Parser_MonadParsec_num___rarg___closed__1 = _init_l_Lean_Parser_MonadParsec_num___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_num___rarg___closed__1);
 l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1___closed__1 = _init_l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1___closed__1);
 l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1___closed__2 = _init_l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_MonadParsec_ensure___rarg___lambda__1___closed__2);
 l_Lean_Parser_MonadParsec_pos___rarg___closed__1 = _init_l_Lean_Parser_MonadParsec_pos___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_pos___rarg___closed__1);
 l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___closed__1 = _init_l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_eoi___rarg___lambda__1___closed__1);
 l_Lean_Parser_MonadParsec_sepBy1___rarg___closed__1 = _init_l_Lean_Parser_MonadParsec_sepBy1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_sepBy1___rarg___closed__1);
 l_Lean_Parser_MonadParsec_fixAux___main___rarg___closed__1 = _init_l_Lean_Parser_MonadParsec_fixAux___main___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_fixAux___main___rarg___closed__1);
 l_Lean_Parser_MonadParsec_longestMatch___rarg___lambda__2___closed__1 = _init_l_Lean_Parser_MonadParsec_longestMatch___rarg___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_MonadParsec_longestMatch___rarg___lambda__2___closed__1);
return w;
}
