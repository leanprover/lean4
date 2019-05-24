// Lean compiler output
// Module: init.lean.parser.combinators
// Imports: init.lean.parser.basic init.data.list.instances
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
obj* l_Lean_Parser_Combinators_coe_view___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_node_view___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_anyOf_view___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many1_view___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_seqRight_tokens___rarg___boxed(obj*);
obj* l_Lean_Parser_Combinators_recurse_view(obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___boxed(obj*);
obj* l_Lean_Parser_Combinators_label_view___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_longestChoice_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_monadLift_view___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy1_tokens(obj*, obj*, obj*, obj*, obj*, obj*, obj*, uint8);
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_coe_tokens(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many_tokens___rarg___boxed(obj*);
obj* l_Lean_Parser_Combinators_anyOf_view(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_coe_view___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_choice___rarg(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Parser_Combinators_sepBy1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, uint8, obj*, obj*);
obj* l_Lean_Parser_Combinators_longestChoice___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_choiceAux___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_optional___boxed(obj*);
obj* l_Lean_Parser_Combinators_monadLift_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_1__many1Aux___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_monadLift_view(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many1_tokens___rarg___boxed(obj*);
obj* l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___boxed(obj*);
obj* l___private_init_lean_parser_combinators_1__many1Aux___main(obj*);
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_choice_tokens___rarg(obj*);
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy1___boxed(obj*);
obj* l_Lean_Parser_Combinators_optional_viewDefault___boxed(obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy1_tokens___rarg(obj*, obj*);
obj* l_Lean_Parser_Combinators_longestMatch_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_node___boxed(obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_Lean_Parser_Combinators_recurse_view___boxed(obj*, obj*, obj*);
extern obj* l_Lean_Parser_choice;
obj* l_Lean_Parser_Combinators_many_tokens___rarg(obj*);
obj* l_Lean_Parser_Combinators_seq___boxed(obj*);
obj* l_Lean_Parser_Combinators_optional_view___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_Combinators_monadLift_view___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_anyOf_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_recurse_tokens(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, uint8, obj*);
obj* l_Lean_Parser_Combinators_optional(obj*);
obj* l_Lean_Parser_Combinators_anyOf(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_seqLeft_view___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_label_tokens___rarg(obj*);
obj* l_Lean_Parser_Combinators_node___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_node_tokens___rarg___boxed(obj*);
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_monadLift_tokens___rarg___boxed(obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_Lean_Parser_Combinators_node___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_seqRight_view___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_label_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_longestMatch___boxed(obj*);
obj* l_Lean_Parser_Combinators_recurse_tokens___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_coe_viewDefault___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_seqLeft_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy_tokens___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy1_View___boxed(obj*);
obj* l_Lean_Parser_Combinators_longestChoice_tokens___rarg___boxed(obj*);
obj* l_Lean_Parser_Combinators_sepBy1_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_longestChoice___boxed(obj*);
obj* l_Lean_Parser_Combinators_sepBy___rarg(obj*, obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_Combinators_try_view___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_List_map___main___rarg(obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_try_view(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_choiceAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_label_view(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_anyOf___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_longestMatch___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy1_View(obj*);
obj* l_Lean_Parser_Combinators_label_tokens___rarg___boxed(obj*);
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_coe_view___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy_tokens(obj*, obj*, obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_Combinators_sepBy1_View___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_coe_viewDefault___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_optional_viewDefault(obj*, obj*);
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l_Lean_Parser_Combinators_longestMatch_tokens___rarg(obj*);
obj* l_Lean_Parser_Combinators_longestChoice___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_longestChoice_tokens___rarg(obj*);
obj* l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1___boxed(obj*);
obj* l_Lean_Parser_Combinators_anyOf_tokens(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_optional_viewDefault___rarg(obj*, obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_Combinators_seq(obj*);
obj* l_Lean_Parser_Combinators_recurse_view___rarg(obj*, obj*);
obj* l_List_enumFrom___main___rarg(obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy_tokens___rarg(obj*, obj*);
obj* l___private_init_lean_parser_combinators_2__sepByAux(obj*);
obj* l_Lean_Parser_Combinators_anyOf_view___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_try_view___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_monadLift_view___rarg(obj*, obj*, obj*);
extern obj* l_Lean_Parser_MonadParsec_remaining___rarg___closed__1;
obj* l_Lean_Parser_Combinators_choice_tokens(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_join___main___rarg(obj*);
obj* l_Lean_Parser_Combinators_choice___boxed(obj*);
obj* l_Lean_Parser_Combinators_sepBy___boxed(obj*);
obj* l_Lean_Parser_Combinators_many1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_seqRight_tokens(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_longestMatch_view___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_coe_view(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many_view(obj*, obj*);
obj* l_Lean_Parser_Combinators_many(obj*);
obj* l_Lean_Parser_Combinators_sepBy_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_anyOf___rarg___closed__1;
obj* l_Lean_Parser_Combinators_optional___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_Syntax_mkNode(obj*, obj*);
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_seqRight_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_try_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_seqLeft_tokens___rarg___boxed(obj*);
obj* l_Lean_Parser_Combinators_seqRight_tokens___rarg(obj*);
obj* l_Lean_Parser_Combinators_choice_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_choiceAux___boxed(obj*);
obj* l_Lean_Parser_Combinators_anyOf_tokens___rarg(obj*);
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_node_tokens(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_noKind;
obj* l_Lean_Parser_Combinators_longestMatch(obj*);
obj* l_Lean_Parser_Combinators_optional_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_append___rarg(obj*, obj*);
obj* l_Lean_Parser_Combinators_choice(obj*);
obj* l_Lean_Parser_Combinators_many___boxed(obj*);
obj* l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_Combinators_optional_view___rarg___lambda__2(obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy1_View___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_longestMatch_view___rarg(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Parser_Combinators_seqLeft_view(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_tokens___rarg(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_Combinators_seqLeft_view___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_choice_tokens___rarg___boxed(obj*);
obj* l_Lean_Parser_Combinators_many_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_MonadParsec_try___rarg___closed__1;
obj* l___private_init_lean_parser_combinators_2__sepByAux___boxed(obj*);
obj* l_Lean_Parser_Combinators_coe_tokens___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_Combinators_coe_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy_view___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_optional___rarg___lambda__2(obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_longestMatch___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_try_tokens(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_seqRight_view(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_longestMatch___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_Combinators_longestChoice(obj*);
obj* l_Lean_Parser_Combinators_seqRight_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_label_view___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_node_view(obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_longestMatch_tokens(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_try_tokens___rarg___boxed(obj*);
obj* l_Lean_Parser_Combinators_optional___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy1_tokens___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_Combinators_longestChoice_tokens(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many1_view(obj*, obj*);
obj* l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1(obj*);
obj* l_Lean_Parser_Combinators_anyOf_view___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_2__sepByAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_node_view___boxed(obj*, obj*);
obj* l___private_init_lean_parser_combinators_1__many1Aux___boxed(obj*);
obj* l_Lean_Parser_Combinators_node_tokens___rarg(obj*);
obj* l_Lean_Parser_Combinators_monadLift_tokens___rarg(obj*);
obj* l_Lean_Parser_Combinators_many1_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_seq___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many1___boxed(obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1(obj*);
obj* l_Lean_Parser_Combinators_many1(obj*);
obj* l_Lean_Parser_Combinators_SepBy_Elem_View_itemCoe(obj*, obj*);
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_label_view___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main(obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1___rarg(obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg___lambda__2(obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_2__sepByAux___rarg(obj*, obj*, obj*, obj*, obj*, obj*, uint8, uint8, obj*, obj*);
obj* l_Lean_Parser_Combinators_anyOf___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy1_View___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, uint8, obj*, obj*);
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_coe_viewDefault(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy(obj*);
obj* l_Lean_Parser_Combinators_optional_view___boxed(obj*, obj*);
obj* l_Lean_Parser_Combinators_choiceAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_Lean_Parser_Combinators_choiceAux___main(obj*);
obj* l_Lean_Parser_Combinators_seqLeft_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy1(obj*);
obj* l_Lean_Parser_Combinators_longestMatch_view(obj*);
extern obj* l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*, uint8, uint8, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_choiceAux___main___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_label_tokens(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many1_tokens(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_optional___rarg___closed__1;
obj* l_Lean_Parser_Combinators_node(obj*);
obj* l_Lean_Parser_Combinators_many_tokens(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many1_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy_view(obj*);
obj* l_Lean_Parser_Combinators_optional_tokens___rarg(obj*, uint8);
obj* l_Lean_Parser_Combinators_choiceAux(obj*);
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, uint8, obj*, obj*);
obj* l_Lean_Parser_Combinators_optional_view___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_node___rarg___lambda__1(obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_seqLeft_tokens(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_optional_tokens___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_Combinators_choice___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many_view___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_optional___rarg___lambda__2___boxed(obj*, obj*);
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_optional_tokens(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_coe_tokens___rarg(obj*, obj*);
obj* l_Lean_Parser_Combinators_choiceAux___main___boxed(obj*);
obj* l_Lean_Parser_Combinators_optional___rarg(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l___private_init_lean_parser_combinators_1__many1Aux(obj*);
obj* l_Lean_Parser_Combinators_longestMatch_tokens___rarg___boxed(obj*);
obj* l_Lean_Parser_Combinators_seq___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_longestMatch_view___boxed(obj*);
obj* l_Lean_Parser_Combinators_monadLift_tokens(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy1_View___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_SepBy_Elem_View_itemCoe___rarg(obj*);
obj* l___private_init_lean_parser_combinators_1__many1Aux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___boxed(obj*);
obj* l_Lean_Parser_Combinators_optional_view(obj*, obj*);
obj* l_Lean_Parser_Combinators_many1_view___rarg___lambda__2(obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, uint8, obj*);
obj* l_Lean_Parser_Combinators_optional_viewDefault___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_seqRight_view___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_coe_viewDefault___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many___rarg___closed__1;
obj* l___private_init_lean_parser_combinators_2__sepByAux___main(obj*);
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many1_view___boxed(obj*, obj*);
obj* l_Lean_Parser_Combinators_node_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many1_tokens___rarg(obj*);
obj* l_Lean_Parser_Combinators_seqLeft_tokens___rarg(obj*);
obj* l_Lean_Parser_Combinators_optional_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_Combinators_recurse_view___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_Combinators_many_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_try_view___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_try_tokens___rarg(obj*);
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many1_view___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_Combinators_anyOf_tokens___rarg___boxed(obj*);
obj* l_Lean_Parser_Combinators_many_view___boxed(obj*, obj*);
obj* l_Lean_Parser_Combinators_sepBy_view___boxed(obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_3);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_6 = lean::apply_2(x_5, lean::box(0), x_4);
return x_6;
}
else
{
obj* x_7; 
x_7 = lean::cnstr_get(x_4, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
lean::dec(x_7);
x_8 = !lean::is_exclusive(x_4);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_4, 3);
lean::dec(x_9);
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
lean::dec(x_2);
x_11 = lean::box(3);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_1);
x_13 = l_List_reverse___rarg(x_12);
x_14 = l_Lean_Parser_Syntax_mkNode(x_3, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_4, 3, x_15);
x_16 = lean::apply_2(x_10, lean::box(0), x_4);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_17 = lean::cnstr_get(x_4, 0);
x_18 = lean::cnstr_get(x_4, 1);
x_19 = lean::cnstr_get(x_4, 2);
lean::inc(x_19);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_4);
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_21 = lean::box(3);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_1);
x_23 = l_List_reverse___rarg(x_22);
x_24 = l_Lean_Parser_Syntax_mkNode(x_3, x_23);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
x_26 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_26, 0, x_17);
lean::cnstr_set(x_26, 1, x_18);
lean::cnstr_set(x_26, 2, x_19);
lean::cnstr_set(x_26, 3, x_25);
x_27 = lean::apply_2(x_20, lean::box(0), x_26);
return x_27;
}
}
else
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_4);
if (x_28 == 0)
{
obj* x_29; obj* x_30; uint8 x_31; 
x_29 = lean::cnstr_get(x_4, 3);
lean::dec(x_29);
x_30 = lean::cnstr_get(x_2, 0);
lean::inc(x_30);
lean::dec(x_2);
x_31 = !lean::is_exclusive(x_7);
if (x_31 == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_32 = lean::cnstr_get(x_7, 0);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_1);
x_34 = l_List_reverse___rarg(x_33);
x_35 = l_Lean_Parser_Syntax_mkNode(x_3, x_34);
lean::cnstr_set(x_7, 0, x_35);
x_36 = lean::apply_2(x_30, lean::box(0), x_4);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_37 = lean::cnstr_get(x_7, 0);
lean::inc(x_37);
lean::dec(x_7);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_1);
x_39 = l_List_reverse___rarg(x_38);
x_40 = l_Lean_Parser_Syntax_mkNode(x_3, x_39);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_4, 3, x_41);
x_42 = lean::apply_2(x_30, lean::box(0), x_4);
return x_42;
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_43 = lean::cnstr_get(x_4, 0);
x_44 = lean::cnstr_get(x_4, 1);
x_45 = lean::cnstr_get(x_4, 2);
lean::inc(x_45);
lean::inc(x_44);
lean::inc(x_43);
lean::dec(x_4);
x_46 = lean::cnstr_get(x_2, 0);
lean::inc(x_46);
lean::dec(x_2);
x_47 = lean::cnstr_get(x_7, 0);
lean::inc(x_47);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_48 = x_7;
} else {
 lean::dec_ref(x_7);
 x_48 = lean::box(0);
}
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_1);
x_50 = l_List_reverse___rarg(x_49);
x_51 = l_Lean_Parser_Syntax_mkNode(x_3, x_50);
if (lean::is_scalar(x_48)) {
 x_52 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_52 = x_48;
}
lean::cnstr_set(x_52, 0, x_51);
x_53 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_53, 0, x_43);
lean::cnstr_set(x_53, 1, x_44);
lean::cnstr_set(x_53, 2, x_45);
lean::cnstr_set(x_53, 3, x_52);
x_54 = lean::apply_2(x_46, lean::box(0), x_53);
return x_54;
}
}
}
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
return x_7;
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg___lambda__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_7, x_6);
return x_8;
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_10 = lean::apply_2(x_9, lean::box(0), x_6);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_11 = lean::cnstr_get(x_7, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
lean::inc(x_4);
lean::inc(x_2);
lean::inc(x_6);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg___lambda__1), 4, 3);
lean::closure_set(x_15, 0, x_6);
lean::closure_set(x_15, 1, x_2);
lean::closure_set(x_15, 2, x_4);
x_16 = lean::apply_3(x_14, lean::box(0), x_11, x_15);
lean::inc(x_3);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg___lambda__2), 3, 2);
lean::closure_set(x_17, 0, x_3);
lean::closure_set(x_17, 1, x_6);
lean::inc(x_5);
x_18 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_16, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg___lambda__3), 7, 6);
lean::closure_set(x_19, 0, x_1);
lean::closure_set(x_19, 1, x_2);
lean::closure_set(x_19, 2, x_3);
lean::closure_set(x_19, 3, x_4);
lean::closure_set(x_19, 4, x_5);
lean::closure_set(x_19, 5, x_12);
x_20 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_18, x_19);
return x_20;
}
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg), 7, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_node___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = l_List_reverse___rarg(x_3);
x_7 = l_Lean_Parser_Syntax_mkNode(x_2, x_6);
x_8 = lean::apply_2(x_5, lean::box(0), x_7);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_node___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_8 = lean::box(0);
lean::inc(x_7);
lean::inc(x_5);
lean::inc(x_4);
x_9 = l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg(x_1, x_2, x_4, x_5, x_7, x_8, x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___rarg___lambda__1), 3, 2);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_5);
x_11 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_Lean_Parser_Combinators_node(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_node___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_node___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_node___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_node(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_seq___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = l_Lean_Parser_noKind;
x_7 = l_Lean_Parser_Combinators_node___rarg(x_1, x_2, x_3, x_4, x_6, x_5);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_seq(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_seq___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_seq___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_seq___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_seq___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_seq(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_node_tokens___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tokens___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_node_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node_tokens___rarg___boxed), 1, 0);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_node_tokens___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_node_tokens___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_node_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_Combinators_node_tokens(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_node_view___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_7, 0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_7);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
}
obj* l_Lean_Parser_Combinators_node_view(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node_view___rarg___boxed), 7, 0);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_node_view___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_node_view___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Combinators_node_view(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_3, 3);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; uint8 x_6; 
lean::dec(x_4);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_7 = lean::cnstr_get(x_3, 3);
lean::dec(x_7);
x_8 = lean::box(3);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_2);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
x_11 = l_List_reverse___rarg(x_10);
x_12 = l_Lean_Parser_noKind;
x_13 = l_Lean_Parser_Syntax_mkNode(x_12, x_11);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_3, 3, x_14);
x_15 = lean::apply_2(x_5, lean::box(0), x_3);
return x_15;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_16 = lean::cnstr_get(x_3, 0);
x_17 = lean::cnstr_get(x_3, 1);
x_18 = lean::cnstr_get(x_3, 2);
lean::inc(x_18);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_3);
x_19 = lean::box(3);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
x_22 = l_List_reverse___rarg(x_21);
x_23 = l_Lean_Parser_noKind;
x_24 = l_Lean_Parser_Syntax_mkNode(x_23, x_22);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
x_26 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_26, 0, x_16);
lean::cnstr_set(x_26, 1, x_17);
lean::cnstr_set(x_26, 2, x_18);
lean::cnstr_set(x_26, 3, x_25);
x_27 = lean::apply_2(x_5, lean::box(0), x_26);
return x_27;
}
}
else
{
obj* x_28; uint8 x_29; 
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
lean::dec(x_1);
x_29 = !lean::is_exclusive(x_3);
if (x_29 == 0)
{
obj* x_30; uint8 x_31; 
x_30 = lean::cnstr_get(x_3, 3);
lean::dec(x_30);
x_31 = !lean::is_exclusive(x_4);
if (x_31 == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_32 = lean::cnstr_get(x_4, 0);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_2);
x_34 = lean::box(3);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_33);
x_36 = l_List_reverse___rarg(x_35);
x_37 = l_Lean_Parser_noKind;
x_38 = l_Lean_Parser_Syntax_mkNode(x_37, x_36);
lean::cnstr_set(x_4, 0, x_38);
x_39 = lean::apply_2(x_28, lean::box(0), x_3);
return x_39;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_40 = lean::cnstr_get(x_4, 0);
lean::inc(x_40);
lean::dec(x_4);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_2);
x_42 = lean::box(3);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_41);
x_44 = l_List_reverse___rarg(x_43);
x_45 = l_Lean_Parser_noKind;
x_46 = l_Lean_Parser_Syntax_mkNode(x_45, x_44);
x_47 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_3, 3, x_47);
x_48 = lean::apply_2(x_28, lean::box(0), x_3);
return x_48;
}
}
else
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_49 = lean::cnstr_get(x_3, 0);
x_50 = lean::cnstr_get(x_3, 1);
x_51 = lean::cnstr_get(x_3, 2);
lean::inc(x_51);
lean::inc(x_50);
lean::inc(x_49);
lean::dec(x_3);
x_52 = lean::cnstr_get(x_4, 0);
lean::inc(x_52);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_53 = x_4;
} else {
 lean::dec_ref(x_4);
 x_53 = lean::box(0);
}
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_52);
lean::cnstr_set(x_54, 1, x_2);
x_55 = lean::box(3);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_54);
x_57 = l_List_reverse___rarg(x_56);
x_58 = l_Lean_Parser_noKind;
x_59 = l_Lean_Parser_Syntax_mkNode(x_58, x_57);
if (lean::is_scalar(x_53)) {
 x_60 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_60 = x_53;
}
lean::cnstr_set(x_60, 0, x_59);
x_61 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_61, 0, x_49);
lean::cnstr_set(x_61, 1, x_50);
lean::cnstr_set(x_61, 2, x_51);
lean::cnstr_set(x_61, 3, x_60);
x_62 = lean::apply_2(x_28, lean::box(0), x_61);
return x_62;
}
}
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_9 = lean::cnstr_get(x_1, 2);
lean::inc(x_9);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_2);
lean::inc(x_10);
lean::inc(x_1);
x_11 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg(x_3, x_4, x_5, x_1, x_6, x_10, x_7);
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
lean::dec(x_12);
x_14 = l_List_reverse___rarg(x_10);
x_15 = l_Lean_Parser_noKind;
x_16 = l_Lean_Parser_Syntax_mkNode(x_15, x_14);
x_17 = lean::apply_2(x_13, lean::box(0), x_16);
x_18 = lean::apply_3(x_9, lean::box(0), x_11, x_17);
return x_18;
}
}
obj* _init_l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unreachable");
return x_1;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_7, x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
lean::inc(x_6);
lean::inc(x_2);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__1), 3, 2);
lean::closure_set(x_14, 0, x_2);
lean::closure_set(x_14, 1, x_6);
lean::inc(x_5);
x_15 = lean::apply_3(x_13, lean::box(0), x_5, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__2___boxed), 8, 7);
lean::closure_set(x_16, 0, x_4);
lean::closure_set(x_16, 1, x_6);
lean::closure_set(x_16, 2, x_1);
lean::closure_set(x_16, 3, x_2);
lean::closure_set(x_16, 4, x_3);
lean::closure_set(x_16, 5, x_5);
lean::closure_set(x_16, 6, x_11);
x_17 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_15, x_16);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_18 = lean::box(0);
x_19 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_20 = l_mjoin___rarg___closed__1;
x_21 = l_Lean_Parser_MonadParsec_error___rarg(x_3, lean::box(0), x_19, x_20, x_18, x_18);
return x_21;
}
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_7);
return x_9;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_7);
return x_8;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_parser_combinators_1__many1Aux___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_1__many1Aux___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l___private_init_lean_parser_combinators_1__many1Aux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_7);
return x_8;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_parser_combinators_1__many1Aux(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_many1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::box(0);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_6, x_8);
x_10 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_7, x_9);
lean::dec(x_9);
return x_10;
}
}
obj* l_Lean_Parser_Combinators_many1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
lean::dec(x_8);
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
x_11 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_12 = lean::apply_2(x_10, lean::box(0), x_11);
x_13 = l_Lean_Parser_MonadParsec_remaining___rarg___closed__1;
x_14 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_13, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_15, 0, x_1);
lean::closure_set(x_15, 1, x_2);
lean::closure_set(x_15, 2, x_3);
lean::closure_set(x_15, 3, x_4);
lean::closure_set(x_15, 4, x_5);
x_16 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_14, x_15);
return x_16;
}
}
obj* l_Lean_Parser_Combinators_many1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___rarg), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_many1___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_many1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_many1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_many1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_many1_tokens___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tokens___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_many1_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1_tokens___rarg___boxed), 1, 0);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_many1_tokens___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_many1_tokens___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_many1_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_many1_tokens(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_many1_view___rarg___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_3);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::box(3);
x_6 = lean::apply_1(x_4, x_5);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
x_12 = l_List_map___main___rarg(x_10, x_11);
return x_12;
}
}
}
obj* l_Lean_Parser_Combinators_many1_view___rarg___lambda__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_List_map___main___rarg(x_3, x_2);
x_5 = l_Lean_Parser_noKind;
x_6 = l_Lean_Parser_Syntax_mkNode(x_5, x_4);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_many1_view___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1_view___rarg___lambda__1), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1_view___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_6);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_many1_view(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1_view___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_many1_view___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_many1_view___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_many1_view___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Combinators_many1_view(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Combinators_many___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_noKind;
x_3 = l_Lean_Parser_Syntax_mkNode(x_2, x_1);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_many___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::cnstr_get(x_4, 2);
lean::inc(x_6);
lean::inc(x_4);
x_7 = l_Lean_Parser_Combinators_many1___rarg(x_1, x_2, x_3, x_4, x_5);
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_10 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_11 = lean::apply_2(x_9, lean::box(0), x_10);
x_12 = lean::apply_3(x_6, lean::box(0), x_7, x_11);
return x_12;
}
}
obj* l_Lean_Parser_Combinators_many(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___rarg), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_many___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_many(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_many_tokens___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tokens___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_many_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many_tokens___rarg___boxed), 1, 0);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_many_tokens___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_many_tokens___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_many_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_many_tokens(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_many_view___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_6);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1_view___rarg___lambda__1), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1_view___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_6);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_many_view(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many_view___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_many_view___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_many_view___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_many_view___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Combinators_many_view(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, uint8 x_10, obj* x_11, obj* x_12) {
_start:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_2);
x_14 = l_List_reverse___rarg(x_13);
x_15 = l_Lean_Parser_noKind;
x_16 = l_Lean_Parser_Syntax_mkNode(x_15, x_14);
x_17 = lean::apply_2(x_3, lean::box(0), x_16);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_3);
x_18 = lean::cnstr_get(x_12, 0);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_1);
lean::cnstr_set(x_19, 1, x_2);
lean::inc(x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l___private_init_lean_parser_combinators_2__sepByAux___main___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_10, x_20, x_11);
return x_21;
}
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, uint8 x_8, obj* x_9, obj* x_10, obj* x_11) {
_start:
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
lean::dec(x_12);
x_14 = l_List_reverse___rarg(x_2);
x_15 = l_Lean_Parser_noKind;
x_16 = l_Lean_Parser_Syntax_mkNode(x_15, x_14);
x_17 = lean::apply_2(x_13, lean::box(0), x_16);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
lean::dec(x_11);
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
x_20 = l_Lean_Parser_MonadParsec_try___rarg___closed__1;
lean::inc(x_4);
x_21 = lean::apply_3(x_19, lean::box(0), x_20, x_4);
x_22 = lean::cnstr_get(x_1, 2);
lean::inc(x_22);
x_23 = lean::cnstr_get(x_1, 0);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
lean::dec(x_24);
x_26 = l_optional___rarg___closed__1;
x_27 = lean::apply_4(x_25, lean::box(0), lean::box(0), x_26, x_21);
x_28 = lean::cnstr_get(x_23, 1);
lean::inc(x_28);
lean::dec(x_23);
x_29 = lean::box(0);
lean::inc(x_28);
x_30 = lean::apply_2(x_28, lean::box(0), x_29);
x_31 = lean::apply_3(x_22, lean::box(0), x_27, x_30);
x_32 = lean::box(x_8);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__1___boxed), 12, 11);
lean::closure_set(x_33, 0, x_18);
lean::closure_set(x_33, 1, x_2);
lean::closure_set(x_33, 2, x_28);
lean::closure_set(x_33, 3, x_5);
lean::closure_set(x_33, 4, x_6);
lean::closure_set(x_33, 5, x_3);
lean::closure_set(x_33, 6, x_1);
lean::closure_set(x_33, 7, x_7);
lean::closure_set(x_33, 8, x_4);
lean::closure_set(x_33, 9, x_32);
lean::closure_set(x_33, 10, x_9);
x_34 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_31, x_33);
return x_34;
}
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, uint8 x_7, uint8 x_8, obj* x_9, obj* x_10) {
_start:
{
obj* x_11; uint8 x_12; 
x_11 = lean::mk_nat_obj(0u);
x_12 = lean::nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_10, x_13);
x_15 = lean::cnstr_get(x_1, 1);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_2, 1);
lean::inc(x_16);
lean::inc(x_9);
lean::inc(x_2);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__1), 3, 2);
lean::closure_set(x_17, 0, x_2);
lean::closure_set(x_17, 1, x_9);
x_18 = lean::box(x_7);
lean::inc(x_15);
lean::inc(x_5);
lean::inc(x_4);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__2___boxed), 11, 10);
lean::closure_set(x_19, 0, x_4);
lean::closure_set(x_19, 1, x_9);
lean::closure_set(x_19, 2, x_3);
lean::closure_set(x_19, 3, x_6);
lean::closure_set(x_19, 4, x_1);
lean::closure_set(x_19, 5, x_2);
lean::closure_set(x_19, 6, x_5);
lean::closure_set(x_19, 7, x_18);
lean::closure_set(x_19, 8, x_14);
lean::closure_set(x_19, 9, x_15);
if (x_8 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
lean::dec(x_4);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
lean::dec(x_20);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
lean::dec(x_21);
x_23 = l_optional___rarg___closed__1;
x_24 = lean::apply_4(x_22, lean::box(0), lean::box(0), x_23, x_5);
x_25 = lean::apply_3(x_16, lean::box(0), x_24, x_17);
x_26 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_25, x_19);
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_27 = lean::cnstr_get(x_4, 2);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_4, 0);
lean::inc(x_28);
lean::dec(x_4);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
lean::dec(x_29);
x_31 = l_optional___rarg___closed__1;
x_32 = lean::apply_4(x_30, lean::box(0), lean::box(0), x_31, x_5);
x_33 = lean::cnstr_get(x_28, 1);
lean::inc(x_33);
lean::dec(x_28);
x_34 = lean::box(0);
x_35 = lean::apply_2(x_33, lean::box(0), x_34);
x_36 = lean::apply_3(x_27, lean::box(0), x_32, x_35);
x_37 = lean::apply_3(x_16, lean::box(0), x_36, x_17);
x_38 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_37, x_19);
return x_38;
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_9);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_39 = lean::box(0);
x_40 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_41 = l_mjoin___rarg___closed__1;
x_42 = l_Lean_Parser_MonadParsec_error___rarg(x_3, lean::box(0), x_40, x_41, x_39, x_39);
return x_42;
}
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___boxed), 10, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12) {
_start:
{
uint8 x_13; obj* x_14; 
x_13 = lean::unbox(x_10);
lean::dec(x_10);
x_14 = l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13, x_11, x_12);
lean::dec(x_12);
lean::dec(x_11);
return x_14;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11) {
_start:
{
uint8 x_12; obj* x_13; 
x_12 = lean::unbox(x_8);
lean::dec(x_8);
x_13 = l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_9, x_10, x_11);
return x_13;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10) {
_start:
{
uint8 x_11; uint8 x_12; obj* x_13; 
x_11 = lean::unbox(x_7);
lean::dec(x_7);
x_12 = lean::unbox(x_8);
lean::dec(x_8);
x_13 = l___private_init_lean_parser_combinators_2__sepByAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_12, x_9, x_10);
lean::dec(x_10);
return x_13;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_parser_combinators_2__sepByAux___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, uint8 x_7, uint8 x_8, obj* x_9, obj* x_10) {
_start:
{
obj* x_11; 
x_11 = l___private_init_lean_parser_combinators_2__sepByAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_2__sepByAux___rarg___boxed), 10, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10) {
_start:
{
uint8 x_11; uint8 x_12; obj* x_13; 
x_11 = lean::unbox(x_7);
lean::dec(x_7);
x_12 = lean::unbox(x_8);
lean::dec(x_8);
x_13 = l___private_init_lean_parser_combinators_2__sepByAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_12, x_9, x_10);
lean::dec(x_10);
return x_13;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_parser_combinators_2__sepByAux(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_sepBy___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, uint8 x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; 
x_9 = lean::box(0);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_8, x_10);
x_12 = 1;
x_13 = l___private_init_lean_parser_combinators_2__sepByAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_9, x_11);
lean::dec(x_11);
return x_13;
}
}
obj* l_Lean_Parser_Combinators_sepBy___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, uint8 x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
x_12 = lean::cnstr_get(x_3, 0);
lean::inc(x_12);
x_13 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_14 = lean::apply_2(x_12, lean::box(0), x_13);
x_15 = l_Lean_Parser_MonadParsec_remaining___rarg___closed__1;
x_16 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_15, x_14);
x_17 = lean::box(x_7);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy___rarg___lambda__1___boxed), 8, 7);
lean::closure_set(x_18, 0, x_1);
lean::closure_set(x_18, 1, x_2);
lean::closure_set(x_18, 2, x_3);
lean::closure_set(x_18, 3, x_4);
lean::closure_set(x_18, 4, x_5);
lean::closure_set(x_18, 5, x_6);
lean::closure_set(x_18, 6, x_17);
x_19 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_16, x_18);
return x_19;
}
}
obj* l_Lean_Parser_Combinators_sepBy(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_sepBy___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint8 x_9; obj* x_10; 
x_9 = lean::unbox(x_7);
lean::dec(x_7);
x_10 = l_Lean_Parser_Combinators_sepBy___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_8);
lean::dec(x_8);
return x_10;
}
}
obj* l_Lean_Parser_Combinators_sepBy___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_7);
lean::dec(x_7);
x_9 = l_Lean_Parser_Combinators_sepBy___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_sepBy___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_sepBy(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_sepBy1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, uint8 x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; 
x_9 = lean::box(0);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_8, x_10);
x_12 = 0;
x_13 = l___private_init_lean_parser_combinators_2__sepByAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_9, x_11);
lean::dec(x_11);
return x_13;
}
}
obj* l_Lean_Parser_Combinators_sepBy1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, uint8 x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
x_12 = lean::cnstr_get(x_3, 0);
lean::inc(x_12);
x_13 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_14 = lean::apply_2(x_12, lean::box(0), x_13);
x_15 = l_Lean_Parser_MonadParsec_remaining___rarg___closed__1;
x_16 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_15, x_14);
x_17 = lean::box(x_7);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1___rarg___lambda__1___boxed), 8, 7);
lean::closure_set(x_18, 0, x_1);
lean::closure_set(x_18, 1, x_2);
lean::closure_set(x_18, 2, x_3);
lean::closure_set(x_18, 3, x_4);
lean::closure_set(x_18, 4, x_5);
lean::closure_set(x_18, 5, x_6);
lean::closure_set(x_18, 6, x_17);
x_19 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_16, x_18);
return x_19;
}
}
obj* l_Lean_Parser_Combinators_sepBy1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_sepBy1___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint8 x_9; obj* x_10; 
x_9 = lean::unbox(x_7);
lean::dec(x_7);
x_10 = l_Lean_Parser_Combinators_sepBy1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_8);
lean::dec(x_8);
return x_10;
}
}
obj* l_Lean_Parser_Combinators_sepBy1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_7);
lean::dec(x_7);
x_9 = l_Lean_Parser_Combinators_sepBy1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_sepBy1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_sepBy1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_sepBy_tokens___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Parser_tokens___rarg(x_1);
x_4 = l_Lean_Parser_tokens___rarg(x_2);
x_5 = l_List_append___rarg(x_3, x_4);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_sepBy_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, uint8 x_8) {
_start:
{
obj* x_9; 
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy_tokens___rarg___boxed), 2, 0);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_sepBy_tokens___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Combinators_sepBy_tokens___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_sepBy_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint8 x_9; obj* x_10; 
x_9 = lean::unbox(x_8);
lean::dec(x_8);
x_10 = l_Lean_Parser_Combinators_sepBy_tokens(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_10;
}
}
obj* l_Lean_Parser_Combinators_SepBy_Elem_View_itemCoe___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_SepBy_Elem_View_itemCoe(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_SepBy_Elem_View_itemCoe___rarg), 1, 0);
return x_3;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; 
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
lean::dec(x_7);
lean::dec(x_4);
x_8 = !lean::is_exclusive(x_5);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_9 = lean::cnstr_get(x_5, 0);
x_10 = lean::cnstr_get(x_5, 1);
lean::dec(x_10);
x_11 = lean::cnstr_get(x_3, 0);
lean::inc(x_11);
lean::dec(x_3);
x_12 = lean::apply_1(x_11, x_9);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::box(0);
lean::cnstr_set(x_5, 1, x_15);
lean::cnstr_set(x_5, 0, x_14);
return x_5;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_16 = lean::cnstr_get(x_5, 0);
lean::inc(x_16);
lean::dec(x_5);
x_17 = lean::cnstr_get(x_3, 0);
lean::inc(x_17);
lean::dec(x_3);
x_18 = lean::apply_1(x_17, x_16);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
}
else
{
obj* x_23; uint8 x_24; 
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
lean::dec(x_5);
x_24 = !lean::is_exclusive(x_7);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_25 = lean::cnstr_get(x_7, 0);
x_26 = lean::cnstr_get(x_7, 1);
x_27 = lean::cnstr_get(x_3, 0);
lean::inc(x_27);
x_28 = lean::apply_1(x_27, x_23);
x_29 = lean::cnstr_get(x_4, 0);
lean::inc(x_29);
x_30 = lean::apply_1(x_29, x_25);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_28);
lean::cnstr_set(x_32, 1, x_31);
x_33 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg(x_1, x_2, x_3, x_4, x_26);
lean::cnstr_set(x_7, 1, x_33);
lean::cnstr_set(x_7, 0, x_32);
return x_7;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_34 = lean::cnstr_get(x_7, 0);
x_35 = lean::cnstr_get(x_7, 1);
lean::inc(x_35);
lean::inc(x_34);
lean::dec(x_7);
x_36 = lean::cnstr_get(x_3, 0);
lean::inc(x_36);
x_37 = lean::apply_1(x_36, x_23);
x_38 = lean::cnstr_get(x_4, 0);
lean::inc(x_38);
x_39 = lean::apply_1(x_38, x_34);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_37);
lean::cnstr_set(x_41, 1, x_40);
x_42 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg(x_1, x_2, x_3, x_4, x_35);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg___boxed), 5, 0);
return x_4;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_3__sepBy_viewAux___rarg___boxed), 5, 0);
return x_8;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l___private_init_lean_parser_combinators_3__sepBy_viewAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_8;
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_6 = lean::box(0);
return x_6;
}
else
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_5, 0);
x_9 = lean::cnstr_get(x_5, 1);
lean::inc(x_4);
lean::inc(x_3);
x_10 = l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___rarg(x_1, x_2, x_3, x_4, x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_11);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_8, 0);
lean::inc(x_12);
lean::dec(x_8);
x_13 = lean::cnstr_get(x_3, 1);
lean::inc(x_13);
lean::dec(x_3);
x_14 = lean::apply_1(x_13, x_12);
x_15 = lean::box(0);
lean::cnstr_set(x_5, 1, x_15);
lean::cnstr_set(x_5, 0, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_5);
lean::cnstr_set(x_16, 1, x_10);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_17 = lean::cnstr_get(x_8, 0);
lean::inc(x_17);
lean::dec(x_8);
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
lean::dec(x_11);
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
lean::dec(x_3);
x_20 = lean::apply_1(x_19, x_17);
x_21 = lean::cnstr_get(x_4, 1);
lean::inc(x_21);
lean::dec(x_4);
x_22 = lean::apply_1(x_21, x_18);
x_23 = lean::box(0);
lean::cnstr_set(x_5, 1, x_23);
lean::cnstr_set(x_5, 0, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_20);
lean::cnstr_set(x_24, 1, x_5);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_10);
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_26 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get(x_5, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_28 = l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___rarg(x_1, x_2, x_3, x_4, x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_29);
lean::dec(x_4);
x_30 = lean::cnstr_get(x_26, 0);
lean::inc(x_30);
lean::dec(x_26);
x_31 = lean::cnstr_get(x_3, 1);
lean::inc(x_31);
lean::dec(x_3);
x_32 = lean::apply_1(x_31, x_30);
x_33 = lean::box(0);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_28);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_36 = lean::cnstr_get(x_26, 0);
lean::inc(x_36);
lean::dec(x_26);
x_37 = lean::cnstr_get(x_29, 0);
lean::inc(x_37);
lean::dec(x_29);
x_38 = lean::cnstr_get(x_3, 1);
lean::inc(x_38);
lean::dec(x_3);
x_39 = lean::apply_1(x_38, x_36);
x_40 = lean::cnstr_get(x_4, 1);
lean::inc(x_40);
lean::dec(x_4);
x_41 = lean::apply_1(x_40, x_37);
x_42 = lean::box(0);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_39);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_28);
return x_45;
}
}
}
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___rarg___boxed), 5, 0);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Syntax_asNode___main(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
lean::dec(x_6);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::box(3);
x_9 = lean::apply_1(x_7, x_8);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_6, 0);
lean::inc(x_14);
lean::dec(x_6);
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
lean::dec(x_14);
x_16 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg(x_2, x_3, x_1, x_4, x_15);
return x_16;
}
}
}
obj* l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
x_7 = l_List_join___main___rarg(x_6);
x_8 = l_Lean_Parser_noKind;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_sepBy_view___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, uint8 x_9, obj* x_10, obj* x_11) {
_start:
{
obj* x_12; obj* x_13; obj* x_14; 
lean::inc(x_11);
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_12, 0, x_10);
lean::closure_set(x_12, 1, x_7);
lean::closure_set(x_12, 2, x_8);
lean::closure_set(x_12, 3, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__2___boxed), 5, 4);
lean::closure_set(x_13, 0, x_7);
lean::closure_set(x_13, 1, x_8);
lean::closure_set(x_13, 2, x_10);
lean::closure_set(x_13, 3, x_11);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
obj* l_Lean_Parser_Combinators_sepBy_view(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy_view___rarg___boxed), 11, 0);
return x_2;
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_sepBy_view___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11) {
_start:
{
uint8 x_12; obj* x_13; 
x_12 = lean::unbox(x_9);
lean::dec(x_9);
x_13 = l_Lean_Parser_Combinators_sepBy_view___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_10, x_11);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_13;
}
}
obj* l_Lean_Parser_Combinators_sepBy_view___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_sepBy_view(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_tokens___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_Combinators_sepBy_tokens___rarg(x_1, x_2);
x_4 = l_Lean_Parser_tokens___rarg(x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, uint8 x_8) {
_start:
{
obj* x_9; 
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1_tokens___rarg___boxed), 2, 0);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_tokens___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Combinators_sepBy1_tokens___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint8 x_9; obj* x_10; 
x_9 = lean::unbox(x_8);
lean::dec(x_8);
x_10 = l_Lean_Parser_Combinators_sepBy1_tokens(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_10;
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_6 = lean::box(0);
return x_6;
}
else
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_5, 0);
x_9 = lean::cnstr_get(x_5, 1);
lean::inc(x_4);
lean::inc(x_3);
x_10 = l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___rarg(x_1, x_2, x_3, x_4, x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_11);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_8, 0);
lean::inc(x_12);
lean::dec(x_8);
x_13 = lean::cnstr_get(x_3, 1);
lean::inc(x_13);
lean::dec(x_3);
x_14 = lean::apply_1(x_13, x_12);
x_15 = lean::box(0);
lean::cnstr_set(x_5, 1, x_15);
lean::cnstr_set(x_5, 0, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_5);
lean::cnstr_set(x_16, 1, x_10);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_17 = lean::cnstr_get(x_8, 0);
lean::inc(x_17);
lean::dec(x_8);
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
lean::dec(x_11);
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
lean::dec(x_3);
x_20 = lean::apply_1(x_19, x_17);
x_21 = lean::cnstr_get(x_4, 1);
lean::inc(x_21);
lean::dec(x_4);
x_22 = lean::apply_1(x_21, x_18);
x_23 = lean::box(0);
lean::cnstr_set(x_5, 1, x_23);
lean::cnstr_set(x_5, 0, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_20);
lean::cnstr_set(x_24, 1, x_5);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_10);
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_26 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get(x_5, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_28 = l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___rarg(x_1, x_2, x_3, x_4, x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_29);
lean::dec(x_4);
x_30 = lean::cnstr_get(x_26, 0);
lean::inc(x_30);
lean::dec(x_26);
x_31 = lean::cnstr_get(x_3, 1);
lean::inc(x_31);
lean::dec(x_3);
x_32 = lean::apply_1(x_31, x_30);
x_33 = lean::box(0);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_28);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_36 = lean::cnstr_get(x_26, 0);
lean::inc(x_36);
lean::dec(x_26);
x_37 = lean::cnstr_get(x_29, 0);
lean::inc(x_37);
lean::dec(x_29);
x_38 = lean::cnstr_get(x_3, 1);
lean::inc(x_38);
lean::dec(x_3);
x_39 = lean::apply_1(x_38, x_36);
x_40 = lean::cnstr_get(x_4, 1);
lean::inc(x_40);
lean::dec(x_4);
x_41 = lean::apply_1(x_40, x_37);
x_42 = lean::box(0);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_39);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_28);
return x_45;
}
}
}
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___rarg___boxed), 5, 0);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_View___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
x_7 = l_List_join___main___rarg(x_6);
x_8 = l_Lean_Parser_noKind;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_View___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, uint8 x_9, obj* x_10, obj* x_11) {
_start:
{
obj* x_12; obj* x_13; obj* x_14; 
lean::inc(x_11);
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_12, 0, x_10);
lean::closure_set(x_12, 1, x_7);
lean::closure_set(x_12, 2, x_8);
lean::closure_set(x_12, 3, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1_View___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_13, 0, x_7);
lean::closure_set(x_13, 1, x_8);
lean::closure_set(x_13, 2, x_10);
lean::closure_set(x_13, 3, x_11);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_View(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1_View___rarg___boxed), 11, 0);
return x_2;
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_View___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_sepBy1_View___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_View___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11) {
_start:
{
uint8 x_12; obj* x_13; 
x_12 = lean::unbox(x_9);
lean::dec(x_9);
x_13 = l_Lean_Parser_Combinators_sepBy1_View___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_10, x_11);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_13;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_View___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_sepBy1_View(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = l_Lean_Parser_noKind;
x_5 = l_Lean_Parser_Syntax_mkNode(x_4, x_3);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_optional___rarg___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_2, 3);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; uint8 x_5; 
lean::dec(x_3);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = !lean::is_exclusive(x_2);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_2, 3);
lean::dec(x_6);
x_7 = l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
lean::cnstr_set(x_2, 3, x_7);
x_8 = lean::apply_2(x_4, lean::box(0), x_2);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_2, 1);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_2);
x_12 = l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_9);
lean::cnstr_set(x_13, 1, x_10);
lean::cnstr_set(x_13, 2, x_11);
lean::cnstr_set(x_13, 3, x_12);
x_14 = lean::apply_2(x_4, lean::box(0), x_13);
return x_14;
}
}
else
{
obj* x_15; uint8 x_16; 
x_15 = lean::cnstr_get(x_1, 0);
lean::inc(x_15);
lean::dec(x_1);
x_16 = !lean::is_exclusive(x_2);
if (x_16 == 0)
{
obj* x_17; uint8 x_18; 
x_17 = lean::cnstr_get(x_2, 3);
lean::dec(x_17);
x_18 = !lean::is_exclusive(x_3);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_19 = lean::cnstr_get(x_3, 0);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
x_22 = l_Lean_Parser_noKind;
x_23 = l_Lean_Parser_Syntax_mkNode(x_22, x_21);
lean::cnstr_set(x_3, 0, x_23);
x_24 = lean::apply_2(x_15, lean::box(0), x_2);
return x_24;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_25 = lean::cnstr_get(x_3, 0);
lean::inc(x_25);
lean::dec(x_3);
x_26 = lean::box(0);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_Lean_Parser_noKind;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_2, 3, x_30);
x_31 = lean::apply_2(x_15, lean::box(0), x_2);
return x_31;
}
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_32 = lean::cnstr_get(x_2, 0);
x_33 = lean::cnstr_get(x_2, 1);
x_34 = lean::cnstr_get(x_2, 2);
lean::inc(x_34);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_2);
x_35 = lean::cnstr_get(x_3, 0);
lean::inc(x_35);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_36 = x_3;
} else {
 lean::dec_ref(x_3);
 x_36 = lean::box(0);
}
x_37 = lean::box(0);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_35);
lean::cnstr_set(x_38, 1, x_37);
x_39 = l_Lean_Parser_noKind;
x_40 = l_Lean_Parser_Syntax_mkNode(x_39, x_38);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_40);
x_42 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_42, 0, x_32);
lean::cnstr_set(x_42, 1, x_33);
lean::cnstr_set(x_42, 2, x_34);
lean::cnstr_set(x_42, 3, x_41);
x_43 = lean::apply_2(x_15, lean::box(0), x_42);
return x_43;
}
}
}
}
obj* l_Lean_Parser_Combinators_optional___rarg___lambda__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_4 = lean::apply_2(x_1, lean::box(0), x_3);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::box(0);
lean::inc(x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_noKind;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
x_10 = lean::apply_2(x_1, lean::box(0), x_9);
return x_10;
}
}
}
obj* l_Lean_Parser_Combinators_optional___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint8 x_6) {
_start:
{
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___rarg___lambda__1), 2, 1);
lean::closure_set(x_9, 0, x_2);
x_10 = lean::apply_3(x_8, lean::box(0), x_5, x_9);
x_11 = lean::cnstr_get(x_4, 2);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_4, 0);
lean::inc(x_12);
lean::dec(x_4);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
lean::dec(x_13);
x_15 = l_optional___rarg___closed__1;
x_16 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_15, x_10);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
x_18 = lean::box(0);
lean::inc(x_17);
x_19 = lean::apply_2(x_17, lean::box(0), x_18);
x_20 = lean::apply_3(x_11, lean::box(0), x_16, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_21, 0, x_17);
x_22 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_20, x_21);
return x_22;
}
else
{
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
}
obj* l_Lean_Parser_Combinators_optional(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_optional___rarg___lambda__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Combinators_optional___rarg___lambda__2(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_optional___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_Combinators_optional___rarg(x_1, x_2, x_3, x_4, x_5, x_7);
lean::dec(x_3);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_optional___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_optional(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_optional_tokens___rarg(obj* x_1, uint8 x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_tokens___rarg(x_1);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_optional_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional_tokens___rarg___boxed), 2, 0);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_optional_tokens___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_Combinators_optional_tokens___rarg(x_1, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_optional_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_optional_tokens(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_optional_view___rarg___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Syntax_asNode___main(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_3);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::box(3);
x_6 = lean::apply_1(x_4, x_5);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_3);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_3, 0);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; 
lean::dec(x_10);
lean::free_heap_obj(x_3);
lean::dec(x_1);
x_11 = lean::box(0);
return x_11;
}
else
{
obj* x_12; 
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_12);
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_14 = lean::cnstr_get(x_1, 0);
lean::inc(x_14);
lean::dec(x_1);
x_15 = lean::apply_1(x_14, x_13);
lean::cnstr_set(x_3, 0, x_15);
return x_3;
}
else
{
obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_12);
lean::dec(x_10);
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
lean::dec(x_1);
x_17 = lean::box(3);
x_18 = lean::apply_1(x_16, x_17);
lean::cnstr_set(x_3, 0, x_18);
return x_3;
}
}
}
else
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_3, 0);
lean::inc(x_19);
lean::dec(x_3);
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; 
lean::dec(x_20);
lean::dec(x_1);
x_21 = lean::box(0);
return x_21;
}
else
{
obj* x_22; 
x_22 = lean::cnstr_get(x_20, 1);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_22);
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
lean::dec(x_20);
x_24 = lean::cnstr_get(x_1, 0);
lean::inc(x_24);
lean::dec(x_1);
x_25 = lean::apply_1(x_24, x_23);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_22);
lean::dec(x_20);
x_27 = lean::cnstr_get(x_1, 0);
lean::inc(x_27);
lean::dec(x_1);
x_28 = lean::box(3);
x_29 = lean::apply_1(x_27, x_28);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
}
}
}
}
}
obj* l_Lean_Parser_Combinators_optional_view___rarg___lambda__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_2);
lean::dec(x_1);
x_3 = l_Lean_Parser_Combinators_many___rarg___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::apply_1(x_5, x_4);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_noKind;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
}
obj* l_Lean_Parser_Combinators_optional_view___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, uint8 x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional_view___rarg___lambda__1), 2, 1);
lean::closure_set(x_8, 0, x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional_view___rarg___lambda__2), 2, 1);
lean::closure_set(x_9, 0, x_6);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_Lean_Parser_Combinators_optional_view(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional_view___rarg___boxed), 7, 0);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_optional_view___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_7);
lean::dec(x_7);
x_9 = l_Lean_Parser_Combinators_optional_view___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_optional_view___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Combinators_optional_view(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_optional_viewDefault___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, uint8 x_7) {
_start:
{
obj* x_8; 
x_8 = lean::box(0);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_optional_viewDefault(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional_viewDefault___rarg___boxed), 7, 0);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_optional_viewDefault___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_7);
lean::dec(x_7);
x_9 = l_Lean_Parser_Combinators_optional_viewDefault___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_optional_viewDefault___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Combinators_optional_viewDefault(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Combinators_anyOf___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("anyOf");
return x_1;
}
}
obj* l_Lean_Parser_Combinators_anyOf___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_3);
lean::dec(x_2);
x_4 = lean::box(0);
x_5 = l_Lean_Parser_Combinators_anyOf___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___rarg(x_1, lean::box(0), x_5, x_6, x_4, x_4);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_10 = lean::cnstr_get(x_2, 2);
lean::inc(x_10);
lean::dec(x_2);
x_11 = lean::apply_1(x_10, lean::box(0));
x_12 = l_List_foldl___main___rarg(x_11, x_8, x_9);
return x_12;
}
}
}
obj* l_Lean_Parser_Combinators_anyOf(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_anyOf___rarg), 3, 0);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_anyOf___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Combinators_anyOf(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_anyOf_tokens___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tokens___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_anyOf_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_anyOf_tokens___rarg___boxed), 1, 0);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_anyOf_tokens___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_anyOf_tokens___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_anyOf_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_anyOf_tokens(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_anyOf_view___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_mjoin___rarg___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_anyOf_view(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_anyOf_view___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_anyOf_view___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Combinators_anyOf_view___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_anyOf_view___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Combinators_anyOf_view(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_longestMatch___rarg___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
if (lean::obj_tag(x_2) == 0)
{
obj* x_10; 
x_10 = lean::box(0);
x_3 = x_10;
goto block_9;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_11);
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
lean::dec(x_13);
x_15 = lean::apply_2(x_14, lean::box(0), x_12);
return x_15;
}
else
{
obj* x_16; 
lean::dec(x_11);
x_16 = lean::box(0);
x_3 = x_16;
goto block_9;
}
}
block_9:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_3);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = l_Lean_Parser_choice;
x_7 = l_Lean_Parser_Syntax_mkNode(x_6, x_2);
x_8 = lean::apply_2(x_5, lean::box(0), x_7);
return x_8;
}
}
}
obj* l_Lean_Parser_Combinators_longestMatch___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = l_Lean_Parser_MonadParsec_longestMatch___rarg(x_1, x_3, lean::box(0), x_2, x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_longestMatch___rarg___lambda__1), 2, 1);
lean::closure_set(x_8, 0, x_4);
x_9 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_longestMatch(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_longestMatch___rarg), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_longestMatch___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_longestMatch(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_longestMatch_tokens___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tokens___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_longestMatch_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_longestMatch_tokens___rarg___boxed), 1, 0);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_longestMatch_tokens___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_longestMatch_tokens___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_longestMatch_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_longestMatch_tokens(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_longestMatch_view___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = l_mjoin___rarg___closed__1;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_longestMatch_view(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_longestMatch_view___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_longestMatch_view___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_longestMatch_view___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_longestMatch_view___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_longestMatch_view(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::box(0);
x_7 = lean_name_mk_numeral(x_6, x_2);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_Syntax_mkNode(x_7, x_9);
x_11 = lean::apply_2(x_5, lean::box(0), x_10);
return x_11;
}
}
obj* _init_l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("choice: Empty List");
return x_1;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___rarg(x_2, lean::box(0), x_7, x_8, x_6, x_6);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_3, 2);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::inc(x_5);
lean::inc(x_3);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___rarg___lambda__1), 3, 2);
lean::closure_set(x_14, 0, x_3);
lean::closure_set(x_14, 1, x_5);
x_15 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_10, x_14);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_add(x_5, x_16);
lean::dec(x_5);
x_18 = l_Lean_Parser_Combinators_choiceAux___main___rarg(x_1, x_2, x_3, x_11, x_17);
x_19 = lean::apply_3(x_12, lean::box(0), x_15, x_18);
return x_19;
}
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___rarg), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_choiceAux___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_choiceAux___main___rarg(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_choiceAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_choiceAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_choiceAux(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_choice___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Lean_Parser_Combinators_choiceAux___main___rarg(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_choice(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choice___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_choice___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_choice___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_choice___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_choice(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_choice_tokens___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tokens___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_choice_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choice_tokens___rarg___boxed), 1, 0);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_choice_tokens___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_choice_tokens___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_choice_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_choice_tokens(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_2);
lean::inc(x_1);
x_8 = l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1___rarg(x_1, x_2, x_7);
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
lean::dec(x_6);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___rarg___lambda__1), 3, 2);
lean::closure_set(x_11, 0, x_1);
lean::closure_set(x_11, 1, x_9);
x_12 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_10, x_11);
lean::cnstr_set(x_3, 1, x_8);
lean::cnstr_set(x_3, 0, x_12);
return x_3;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_3, 0);
x_14 = lean::cnstr_get(x_3, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_15 = l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1___rarg(x_1, x_2, x_14);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_13, 1);
lean::inc(x_17);
lean::dec(x_13);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___rarg___lambda__1), 3, 2);
lean::closure_set(x_18, 0, x_1);
lean::closure_set(x_18, 1, x_16);
x_19 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_17, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_15);
return x_20;
}
}
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_longestChoice___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_3);
lean::dec(x_2);
x_4 = lean::box(0);
x_5 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___rarg(x_1, lean::box(0), x_5, x_6, x_4, x_4);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::apply_2(x_10, lean::box(0), x_8);
return x_11;
}
}
}
obj* l_Lean_Parser_Combinators_longestChoice___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_List_enumFrom___main___rarg(x_7, x_5);
lean::inc(x_6);
lean::inc(x_4);
x_9 = l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1___rarg(x_4, x_6, x_8);
lean::inc(x_3);
x_10 = l_Lean_Parser_MonadParsec_longestMatch___rarg(x_1, x_3, lean::box(0), x_2, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_longestChoice___rarg___lambda__1), 3, 2);
lean::closure_set(x_11, 0, x_3);
lean::closure_set(x_11, 1, x_4);
x_12 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_10, x_11);
return x_12;
}
}
obj* l_Lean_Parser_Combinators_longestChoice(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_longestChoice___rarg), 5, 0);
return x_2;
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_longestChoice___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_longestChoice(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_longestChoice_tokens___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tokens___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_longestChoice_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_longestChoice_tokens___rarg___boxed), 1, 0);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_longestChoice_tokens___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_longestChoice_tokens___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_longestChoice_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_longestChoice_tokens(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_try_tokens___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tokens___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_try_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_try_tokens___rarg___boxed), 1, 0);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_try_tokens___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_try_tokens___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_try_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_try_tokens(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_try_view___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_4);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
}
obj* l_Lean_Parser_Combinators_try_view(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_try_view___rarg___boxed), 4, 0);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_try_view___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Combinators_try_view___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_try_view___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Combinators_try_view(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_label_tokens___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tokens___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_label_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_label_tokens___rarg___boxed), 1, 0);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_label_tokens___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_label_tokens___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_label_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_Combinators_label_tokens(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_label_view___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_5);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_Lean_Parser_Combinators_label_view(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_label_view___rarg___boxed), 5, 0);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_label_view___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_label_view___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_label_view___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Combinators_label_view(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_recurse_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::box(0);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_recurse_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_recurse_tokens(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_recurse_view___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_mjoin___rarg___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_recurse_view(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_recurse_view___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_recurse_view___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Combinators_recurse_view___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_recurse_view___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Combinators_recurse_view(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_monadLift_tokens___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tokens___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_monadLift_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_monadLift_tokens___rarg___boxed), 1, 0);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_monadLift_tokens___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_monadLift_tokens___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_monadLift_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_Combinators_monadLift_tokens(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_monadLift_view___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::inc(x_5);
lean::dec(x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
}
obj* l_Lean_Parser_Combinators_monadLift_view(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_monadLift_view___rarg___boxed), 3, 0);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_monadLift_view___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Combinators_monadLift_view___rarg(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_monadLift_view___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_Combinators_monadLift_view(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_seqLeft_tokens___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tokens___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_seqLeft_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_seqLeft_tokens___rarg___boxed), 1, 0);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_seqLeft_tokens___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_seqLeft_tokens___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_seqLeft_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_Combinators_seqLeft_tokens(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_seqLeft_view___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_6);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_Lean_Parser_Combinators_seqLeft_view(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_seqLeft_view___rarg___boxed), 6, 0);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_seqLeft_view___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_seqLeft_view___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_seqLeft_view___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Combinators_seqLeft_view(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_seqRight_tokens___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tokens___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_seqRight_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_seqRight_tokens___rarg___boxed), 1, 0);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_seqRight_tokens___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_seqRight_tokens___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_seqRight_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_Combinators_seqRight_tokens(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_seqRight_view___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_6);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_Lean_Parser_Combinators_seqRight_view(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_seqRight_view___rarg___boxed), 6, 0);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_seqRight_view___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_seqRight_view___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_seqRight_view___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Combinators_seqRight_view(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_coe_tokens___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_tokens___rarg(x_1);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_coe_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_coe_tokens___rarg___boxed), 2, 0);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_coe_tokens___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Combinators_coe_tokens___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_coe_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_Combinators_coe_tokens(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_coe_view___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
return x_2;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::inc(x_5);
lean::dec(x_2);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
}
obj* l_Lean_Parser_Combinators_coe_view(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_coe_view___rarg___boxed), 3, 0);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_coe_view___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Combinators_coe_view___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_coe_view___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_Combinators_coe_view(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_coe_viewDefault___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::box(0);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_coe_viewDefault(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_coe_viewDefault___rarg___boxed), 5, 0);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_coe_viewDefault___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_coe_viewDefault___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_coe_viewDefault___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_Combinators_coe_viewDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_8;
}
}
obj* initialize_init_lean_parser_basic(obj*);
obj* initialize_init_data_list_instances(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_combinators(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_list_instances(w);
if (io_result_is_error(w)) return w;
l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1 = _init_l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1();
lean::mark_persistent(l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1);
l_Lean_Parser_Combinators_many___rarg___closed__1 = _init_l_Lean_Parser_Combinators_many___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Combinators_many___rarg___closed__1);
l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1 = _init_l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1);
l_Lean_Parser_Combinators_anyOf___rarg___closed__1 = _init_l_Lean_Parser_Combinators_anyOf___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Combinators_anyOf___rarg___closed__1);
l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1 = _init_l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1);
return w;
}
