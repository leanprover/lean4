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
obj* l_Option_get___main___at_Lean_Parser_run___spec__2(obj*);
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
obj* l_Lean_Parser_Combinators_optional_viewDefault___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
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
obj* l_Lean_Parser_Combinators_SepBy_Elem_View_itemCoe___boxed(obj*, obj*);
obj* l_Lean_Parser_Combinators_optional_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_append___rarg(obj*, obj*);
obj* l_Lean_Parser_Combinators_choice(obj*);
obj* l_Lean_Parser_Combinators_many___boxed(obj*);
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
obj* l_Lean_Parser_Combinators_optional___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
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
obj* l_Lean_Parser_Combinators_optional_tokens___rarg(obj*);
obj* l_Lean_Parser_Combinators_choiceAux(obj*);
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, uint8, obj*, obj*);
obj* l_Lean_Parser_Combinators_optional_view___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_node___rarg___lambda__1(obj*, obj*, obj*);
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_seqLeft_tokens(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_optional_tokens___rarg___boxed(obj*);
obj* l_Lean_Parser_Combinators_choice___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_many_view___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_optional_tokens(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_coe_tokens___rarg(obj*, obj*);
obj* l_Lean_Parser_Combinators_choiceAux___main___boxed(obj*);
obj* l_Lean_Parser_Combinators_optional___rarg(obj*, obj*, obj*, obj*, obj*);
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
obj* l_Lean_Parser_Combinators_optional_viewDefault___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
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
obj* l_Lean_Parser_Combinators_optional_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
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
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_8; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::apply_2(x_5, lean::box(0), x_3);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_9 = lean::cnstr_get(x_3, 3);
lean::inc(x_9);
x_11 = l_Option_get___main___at_Lean_Parser_run___spec__2(x_9);
lean::dec(x_9);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_0);
x_14 = lean::cnstr_get(x_1, 0);
lean::inc(x_14);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_3, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_3, 2);
lean::inc(x_21);
lean::dec(x_3);
x_24 = l_List_reverse___rarg(x_13);
x_25 = l_Lean_Parser_Syntax_mkNode(x_2, x_24);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_27, 0, x_17);
lean::cnstr_set(x_27, 1, x_19);
lean::cnstr_set(x_27, 2, x_21);
lean::cnstr_set(x_27, 3, x_26);
x_28 = lean::apply_2(x_14, lean::box(0), x_27);
return x_28;
}
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_1);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_6, x_5);
return x_7;
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_11; obj* x_14; obj* x_17; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::apply_2(x_14, lean::box(0), x_5);
return x_17;
}
else
{
obj* x_18; obj* x_20; obj* x_23; obj* x_25; obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
x_18 = lean::cnstr_get(x_6, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_6, 1);
lean::inc(x_20);
lean::dec(x_6);
x_23 = lean::cnstr_get(x_0, 1);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_1, 1);
lean::inc(x_25);
lean::inc(x_3);
lean::inc(x_1);
lean::inc(x_5);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg___lambda__1), 4, 3);
lean::closure_set(x_30, 0, x_5);
lean::closure_set(x_30, 1, x_1);
lean::closure_set(x_30, 2, x_3);
x_31 = lean::apply_3(x_25, lean::box(0), x_18, x_30);
lean::inc(x_2);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg___lambda__2), 3, 2);
lean::closure_set(x_33, 0, x_2);
lean::closure_set(x_33, 1, x_5);
lean::inc(x_4);
x_35 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_31, x_33);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg___lambda__3), 7, 6);
lean::closure_set(x_36, 0, x_0);
lean::closure_set(x_36, 1, x_1);
lean::closure_set(x_36, 2, x_2);
lean::closure_set(x_36, 3, x_3);
lean::closure_set(x_36, 4, x_4);
lean::closure_set(x_36, 5, x_20);
x_37 = lean::apply_4(x_23, lean::box(0), lean::box(0), x_35, x_36);
return x_37;
}
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg), 7, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_node___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_List_reverse___rarg(x_2);
x_10 = l_Lean_Parser_Syntax_mkNode(x_1, x_9);
x_11 = lean::apply_2(x_6, lean::box(0), x_10);
return x_11;
}
}
obj* l_Lean_Parser_Combinators_node___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::box(0);
lean::inc(x_6);
lean::inc(x_4);
lean::inc(x_3);
x_12 = l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___rarg(x_0, x_1, x_3, x_4, x_6, x_8, x_5);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___rarg___lambda__1), 3, 2);
lean::closure_set(x_13, 0, x_3);
lean::closure_set(x_13, 1, x_4);
x_14 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* l_Lean_Parser_Combinators_node(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_mfoldl___main___at_Lean_Parser_Combinators_node___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_node___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_node___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_node___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_node(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_seq___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_Parser_noKind;
x_6 = l_Lean_Parser_Combinators_node___rarg(x_0, x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_seq(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_seq___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_seq___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Combinators_seq___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_seq___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_seq(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_node_tokens___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_node_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node_tokens___rarg___boxed), 1, 0);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_node_tokens___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_node_tokens___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_node_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_node_tokens(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_node_view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_12; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_9);
return x_12;
}
}
obj* l_Lean_Parser_Combinators_node_view(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node_view___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_node_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_node_view___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_node_view___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_node_view(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 3);
lean::inc(x_12);
lean::dec(x_2);
x_15 = l_Option_get___main___at_Lean_Parser_run___spec__2(x_12);
lean::dec(x_12);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_1);
x_18 = lean::box(3);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
x_20 = l_List_reverse___rarg(x_19);
x_21 = l_Lean_Parser_noKind;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_24, 0, x_6);
lean::cnstr_set(x_24, 1, x_8);
lean::cnstr_set(x_24, 2, x_10);
lean::cnstr_set(x_24, 3, x_23);
x_25 = lean::apply_2(x_3, lean::box(0), x_24);
return x_25;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_1);
lean::inc(x_10);
lean::inc(x_0);
x_13 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg(x_2, x_3, x_4, x_0, x_5, x_10, x_6);
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_List_reverse___rarg(x_10);
x_21 = l_Lean_Parser_noKind;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
x_23 = lean::apply_2(x_17, lean::box(0), x_22);
x_24 = lean::apply_3(x_8, lean::box(0), x_13, x_23);
return x_24;
}
}
obj* _init_l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unreachable");
return x_0;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_6, x_9);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::inc(x_5);
lean::inc(x_1);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__1), 3, 2);
lean::closure_set(x_17, 0, x_1);
lean::closure_set(x_17, 1, x_5);
lean::inc(x_4);
x_19 = lean::apply_3(x_13, lean::box(0), x_4, x_17);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__2___boxed), 8, 7);
lean::closure_set(x_20, 0, x_3);
lean::closure_set(x_20, 1, x_5);
lean::closure_set(x_20, 2, x_0);
lean::closure_set(x_20, 3, x_1);
lean::closure_set(x_20, 4, x_2);
lean::closure_set(x_20, 5, x_4);
lean::closure_set(x_20, 6, x_10);
x_21 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_19, x_20);
return x_21;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_27 = lean::box(0);
x_28 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_29 = l_mjoin___rarg___closed__1;
x_30 = l_Lean_Parser_MonadParsec_error___rarg(x_2, lean::box(0), x_28, x_29, x_27, x_27);
return x_30;
}
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___boxed), 7, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
return x_8;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
return x_7;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_combinators_1__many1Aux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_1__many1Aux___rarg___boxed), 7, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l___private_init_lean_parser_combinators_1__many1Aux___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
return x_7;
}
}
obj* l___private_init_lean_parser_combinators_1__many1Aux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_combinators_1__many1Aux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_many1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::box(0);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_5, x_7);
x_9 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_6, x_8);
lean::dec(x_8);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_many1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
x_17 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_18 = lean::apply_2(x_15, lean::box(0), x_17);
x_19 = l_Lean_Parser_MonadParsec_remaining___rarg___closed__1;
x_20 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_19, x_18);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_21, 0, x_0);
lean::closure_set(x_21, 1, x_1);
lean::closure_set(x_21, 2, x_2);
lean::closure_set(x_21, 3, x_3);
lean::closure_set(x_21, 4, x_4);
x_22 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_20, x_21);
return x_22;
}
}
obj* l_Lean_Parser_Combinators_many1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1___rarg), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_many1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_many1___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_many1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_many1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_many1_tokens___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_many1_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1_tokens___rarg___boxed), 1, 0);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_many1_tokens___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_many1_tokens___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_many1_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_many1_tokens(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_many1_view___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::box(3);
x_7 = lean::apply_1(x_3, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_13; obj* x_16; obj* x_19; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_19 = l_List_map___main___rarg(x_13, x_16);
return x_19;
}
}
}
obj* l_Lean_Parser_Combinators_many1_view___rarg___lambda__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_List_map___main___rarg(x_2, x_1);
x_6 = l_Lean_Parser_noKind;
x_7 = l_Lean_Parser_Syntax_mkNode(x_6, x_5);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_many1_view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1_view___rarg___lambda__1), 2, 1);
lean::closure_set(x_7, 0, x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1_view___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_5);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_many1_view(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1_view___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_many1_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_many1_view___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_many1_view___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_many1_view(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Combinators_many___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_noKind;
x_2 = l_Lean_Parser_Syntax_mkNode(x_1, x_0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_many___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; obj* x_12; obj* x_15; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::inc(x_3);
x_8 = l_Lean_Parser_Combinators_many1___rarg(x_0, x_1, x_2, x_3, x_4);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
x_17 = lean::apply_3(x_5, lean::box(0), x_8, x_16);
return x_17;
}
}
obj* l_Lean_Parser_Combinators_many(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many___rarg), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_many___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_many(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_many_tokens___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_many_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many_tokens___rarg___boxed), 1, 0);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_many_tokens___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_many_tokens___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_many_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_many_tokens(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_many_view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1_view___rarg___lambda__1), 2, 1);
lean::closure_set(x_7, 0, x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many1_view___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_5);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_many_view(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_many_view___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_many_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_many_view___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_many_view___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_many_view(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, uint8 x_9, obj* x_10, obj* x_11) {
_start:
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_5);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_0);
lean::cnstr_set(x_18, 1, x_1);
x_19 = l_List_reverse___rarg(x_18);
x_20 = l_Lean_Parser_noKind;
x_21 = l_Lean_Parser_Syntax_mkNode(x_20, x_19);
x_22 = lean::apply_2(x_2, lean::box(0), x_21);
return x_22;
}
else
{
obj* x_24; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_2);
x_24 = lean::cnstr_get(x_11, 0);
lean::inc(x_24);
lean::dec(x_11);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_0);
lean::cnstr_set(x_27, 1, x_1);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_24);
lean::cnstr_set(x_28, 1, x_27);
x_29 = l___private_init_lean_parser_combinators_2__sepByAux___main___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_9, x_28, x_10);
return x_29;
}
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, uint8 x_7, obj* x_8, obj* x_9, obj* x_10) {
_start:
{
if (lean::obj_tag(x_10) == 0)
{
obj* x_18; obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = l_List_reverse___rarg(x_1);
x_25 = l_Lean_Parser_noKind;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
x_27 = lean::apply_2(x_21, lean::box(0), x_26);
return x_27;
}
else
{
obj* x_28; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_45; obj* x_46; obj* x_47; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_28 = lean::cnstr_get(x_10, 0);
lean::inc(x_28);
lean::dec(x_10);
x_31 = lean::cnstr_get(x_2, 1);
lean::inc(x_31);
x_33 = l_Lean_Parser_MonadParsec_try___rarg___closed__1;
lean::inc(x_3);
x_35 = lean::apply_3(x_31, lean::box(0), x_33, x_3);
x_36 = lean::cnstr_get(x_0, 1);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_0, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_38, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_40, 0);
lean::inc(x_42);
lean::dec(x_40);
x_45 = l_optional___rarg___closed__1;
x_46 = lean::apply_4(x_42, lean::box(0), lean::box(0), x_45, x_35);
x_47 = lean::cnstr_get(x_38, 1);
lean::inc(x_47);
lean::dec(x_38);
x_50 = lean::box(0);
lean::inc(x_47);
x_52 = lean::apply_2(x_47, lean::box(0), x_50);
x_53 = lean::apply_3(x_36, lean::box(0), x_46, x_52);
x_54 = lean::box(x_7);
x_55 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__1___boxed), 12, 11);
lean::closure_set(x_55, 0, x_28);
lean::closure_set(x_55, 1, x_1);
lean::closure_set(x_55, 2, x_47);
lean::closure_set(x_55, 3, x_4);
lean::closure_set(x_55, 4, x_5);
lean::closure_set(x_55, 5, x_2);
lean::closure_set(x_55, 6, x_0);
lean::closure_set(x_55, 7, x_6);
lean::closure_set(x_55, 8, x_3);
lean::closure_set(x_55, 9, x_54);
lean::closure_set(x_55, 10, x_8);
x_56 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_53, x_55);
return x_56;
}
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint8 x_6, uint8 x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; uint8 x_11; 
x_10 = lean::mk_nat_obj(0u);
x_11 = lean::nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_20; obj* x_21; obj* x_25; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_9, x_12);
x_14 = lean::cnstr_get(x_0, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_1, 1);
lean::inc(x_16);
lean::inc(x_8);
lean::inc(x_1);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___lambda__1), 3, 2);
lean::closure_set(x_20, 0, x_1);
lean::closure_set(x_20, 1, x_8);
x_21 = lean::box(x_6);
lean::inc(x_14);
lean::inc(x_4);
lean::inc(x_3);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__2___boxed), 11, 10);
lean::closure_set(x_25, 0, x_3);
lean::closure_set(x_25, 1, x_8);
lean::closure_set(x_25, 2, x_2);
lean::closure_set(x_25, 3, x_5);
lean::closure_set(x_25, 4, x_0);
lean::closure_set(x_25, 5, x_1);
lean::closure_set(x_25, 6, x_4);
lean::closure_set(x_25, 7, x_21);
lean::closure_set(x_25, 8, x_13);
lean::closure_set(x_25, 9, x_14);
if (x_7 == 0)
{
obj* x_26; obj* x_29; obj* x_32; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_26 = lean::cnstr_get(x_3, 0);
lean::inc(x_26);
lean::dec(x_3);
x_29 = lean::cnstr_get(x_26, 0);
lean::inc(x_29);
lean::dec(x_26);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
lean::dec(x_29);
x_35 = l_optional___rarg___closed__1;
x_36 = lean::apply_4(x_32, lean::box(0), lean::box(0), x_35, x_4);
x_37 = lean::apply_3(x_16, lean::box(0), x_36, x_20);
x_38 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_37, x_25);
return x_38;
}
else
{
obj* x_39; obj* x_41; obj* x_44; obj* x_46; obj* x_49; obj* x_50; obj* x_51; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_39 = lean::cnstr_get(x_3, 1);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_3, 0);
lean::inc(x_41);
lean::dec(x_3);
x_44 = lean::cnstr_get(x_41, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_44, 0);
lean::inc(x_46);
lean::dec(x_44);
x_49 = l_optional___rarg___closed__1;
x_50 = lean::apply_4(x_46, lean::box(0), lean::box(0), x_49, x_4);
x_51 = lean::cnstr_get(x_41, 1);
lean::inc(x_51);
lean::dec(x_41);
x_54 = lean::box(0);
x_55 = lean::apply_2(x_51, lean::box(0), x_54);
x_56 = lean::apply_3(x_39, lean::box(0), x_50, x_55);
x_57 = lean::apply_3(x_16, lean::box(0), x_56, x_20);
x_58 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_57, x_25);
return x_58;
}
}
else
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_5);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_65 = lean::box(0);
x_66 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_67 = l_mjoin___rarg___closed__1;
x_68 = l_Lean_Parser_MonadParsec_error___rarg(x_2, lean::box(0), x_66, x_67, x_65, x_65);
return x_68;
}
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___boxed), 10, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11) {
_start:
{
uint8 x_12; obj* x_13; 
x_12 = lean::unbox(x_9);
x_13 = l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_10, x_11);
lean::dec(x_10);
return x_13;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10) {
_start:
{
uint8 x_11; obj* x_12; 
x_11 = lean::unbox(x_7);
x_12 = l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
return x_12;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
uint8 x_10; uint8 x_11; obj* x_12; 
x_10 = lean::unbox(x_6);
x_11 = lean::unbox(x_7);
x_12 = l___private_init_lean_parser_combinators_2__sepByAux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_10, x_11, x_8, x_9);
lean::dec(x_9);
return x_12;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_combinators_2__sepByAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint8 x_6, uint8 x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; 
x_10 = l___private_init_lean_parser_combinators_2__sepByAux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_2__sepByAux___rarg___boxed), 10, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
uint8 x_10; uint8 x_11; obj* x_12; 
x_10 = lean::unbox(x_6);
x_11 = lean::unbox(x_7);
x_12 = l___private_init_lean_parser_combinators_2__sepByAux___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_10, x_11, x_8, x_9);
lean::dec(x_9);
return x_12;
}
}
obj* l___private_init_lean_parser_combinators_2__sepByAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_combinators_2__sepByAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_sepBy___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint8 x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; uint8 x_11; obj* x_12; 
x_8 = lean::box(0);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_7, x_9);
x_11 = 1;
x_12 = l___private_init_lean_parser_combinators_2__sepByAux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_10);
lean::dec(x_10);
return x_12;
}
}
obj* l_Lean_Parser_Combinators_sepBy___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint8 x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_2, 0);
lean::inc(x_17);
x_19 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_20 = lean::apply_2(x_17, lean::box(0), x_19);
x_21 = l_Lean_Parser_MonadParsec_remaining___rarg___closed__1;
x_22 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_21, x_20);
x_23 = lean::box(x_6);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy___rarg___lambda__1___boxed), 8, 7);
lean::closure_set(x_24, 0, x_0);
lean::closure_set(x_24, 1, x_1);
lean::closure_set(x_24, 2, x_2);
lean::closure_set(x_24, 3, x_3);
lean::closure_set(x_24, 4, x_4);
lean::closure_set(x_24, 5, x_5);
lean::closure_set(x_24, 6, x_23);
x_25 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_22, x_24);
return x_25;
}
}
obj* l_Lean_Parser_Combinators_sepBy(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy___rarg___boxed), 7, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_sepBy___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_6);
x_9 = l_Lean_Parser_Combinators_sepBy___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5, x_8, x_7);
lean::dec(x_7);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_sepBy___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_6);
x_8 = l_Lean_Parser_Combinators_sepBy___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_sepBy___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_sepBy(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_sepBy1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint8 x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; uint8 x_11; obj* x_12; 
x_8 = lean::box(0);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_7, x_9);
x_11 = 0;
x_12 = l___private_init_lean_parser_combinators_2__sepByAux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_10);
lean::dec(x_10);
return x_12;
}
}
obj* l_Lean_Parser_Combinators_sepBy1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint8 x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_2, 0);
lean::inc(x_17);
x_19 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_20 = lean::apply_2(x_17, lean::box(0), x_19);
x_21 = l_Lean_Parser_MonadParsec_remaining___rarg___closed__1;
x_22 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_21, x_20);
x_23 = lean::box(x_6);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1___rarg___lambda__1___boxed), 8, 7);
lean::closure_set(x_24, 0, x_0);
lean::closure_set(x_24, 1, x_1);
lean::closure_set(x_24, 2, x_2);
lean::closure_set(x_24, 3, x_3);
lean::closure_set(x_24, 4, x_4);
lean::closure_set(x_24, 5, x_5);
lean::closure_set(x_24, 6, x_23);
x_25 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_22, x_24);
return x_25;
}
}
obj* l_Lean_Parser_Combinators_sepBy1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1___rarg___boxed), 7, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_sepBy1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_6);
x_9 = l_Lean_Parser_Combinators_sepBy1___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5, x_8, x_7);
lean::dec(x_7);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_sepBy1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_6);
x_8 = l_Lean_Parser_Combinators_sepBy1___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_sepBy1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_sepBy1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_sepBy_tokens___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Parser_tokens___rarg(x_0);
x_3 = l_Lean_Parser_tokens___rarg(x_1);
x_4 = l_List_append___rarg(x_2, x_3);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_sepBy_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, uint8 x_7) {
_start:
{
obj* x_8; 
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy_tokens___rarg___boxed), 2, 0);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_sepBy_tokens___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_sepBy_tokens___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_sepBy_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_7);
x_9 = l_Lean_Parser_Combinators_sepBy_tokens(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_8);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_SepBy_Elem_View_itemCoe___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_SepBy_Elem_View_itemCoe(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_SepBy_Elem_View_itemCoe___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_SepBy_Elem_View_itemCoe___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_SepBy_Elem_View_itemCoe(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; 
x_8 = lean::cnstr_get(x_4, 1);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_3);
x_11 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 1);
 x_13 = x_4;
} else {
 lean::inc(x_11);
 lean::dec(x_4);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
lean::dec(x_2);
x_17 = lean::apply_1(x_14, x_11);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::box(0);
if (lean::is_scalar(x_13)) {
 x_21 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_21 = x_13;
}
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_22 = lean::cnstr_get(x_4, 0);
lean::inc(x_22);
lean::dec(x_4);
x_25 = lean::cnstr_get(x_8, 0);
x_27 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 x_29 = x_8;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_8);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_2, 0);
lean::inc(x_30);
x_32 = lean::apply_1(x_30, x_22);
x_33 = lean::cnstr_get(x_3, 0);
lean::inc(x_33);
x_35 = lean::apply_1(x_33, x_25);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_32);
lean::cnstr_set(x_37, 1, x_36);
x_38 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg(x_0, x_1, x_2, x_3, x_27);
if (lean::is_scalar(x_29)) {
 x_39 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_39 = x_29;
}
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_combinators_3__sepBy_viewAux___rarg___boxed), 5, 0);
return x_7;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_combinators_3__sepBy_viewAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l___private_init_lean_parser_combinators_3__sepBy_viewAux(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_7;
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_20; 
x_8 = lean::cnstr_get(x_4, 0);
x_10 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_12 = x_4;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_4);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_8, 1);
lean::inc(x_15);
lean::dec(x_8);
lean::inc(x_3);
lean::inc(x_2);
x_20 = l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___rarg(x_0, x_1, x_2, x_3, x_10);
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_3);
x_22 = lean::cnstr_get(x_2, 1);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::apply_1(x_22, x_13);
x_26 = lean::box(0);
if (lean::is_scalar(x_12)) {
 x_27 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_27 = x_12;
}
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_20);
return x_28;
}
else
{
obj* x_29; obj* x_32; obj* x_35; obj* x_36; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_29 = lean::cnstr_get(x_15, 0);
lean::inc(x_29);
lean::dec(x_15);
x_32 = lean::cnstr_get(x_2, 1);
lean::inc(x_32);
lean::dec(x_2);
x_35 = lean::apply_1(x_32, x_13);
x_36 = lean::cnstr_get(x_3, 1);
lean::inc(x_36);
lean::dec(x_3);
x_39 = lean::apply_1(x_36, x_29);
x_40 = lean::box(0);
if (lean::is_scalar(x_12)) {
 x_41 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_41 = x_12;
}
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_35);
lean::cnstr_set(x_42, 1, x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_20);
return x_43;
}
}
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Syntax_asNode___main(x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_3);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::box(3);
x_11 = lean::apply_1(x_7, x_10);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_22; 
x_16 = lean::cnstr_get(x_5, 0);
lean::inc(x_16);
lean::dec(x_5);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_22 = l___private_init_lean_parser_combinators_3__sepBy_viewAux___main___rarg(x_1, x_2, x_0, x_3, x_19);
return x_22;
}
}
}
obj* l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
x_6 = l_List_join___main___rarg(x_5);
x_7 = l_Lean_Parser_noKind;
x_8 = l_Lean_Parser_Syntax_mkNode(x_7, x_6);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_sepBy_view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, uint8 x_8, obj* x_9, obj* x_10) {
_start:
{
obj* x_15; obj* x_16; obj* x_17; 
lean::inc(x_10);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_9);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_6);
lean::closure_set(x_15, 2, x_7);
lean::closure_set(x_15, 3, x_10);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__2___boxed), 5, 4);
lean::closure_set(x_16, 0, x_6);
lean::closure_set(x_16, 1, x_7);
lean::closure_set(x_16, 2, x_9);
lean::closure_set(x_16, 3, x_10);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* l_Lean_Parser_Combinators_sepBy_view(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy_view___rarg___boxed), 11, 0);
return x_1;
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_map___main___at_Lean_Parser_Combinators_sepBy_view___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_sepBy_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10) {
_start:
{
uint8 x_11; obj* x_12; 
x_11 = lean::unbox(x_8);
x_12 = l_Lean_Parser_Combinators_sepBy_view___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_9, x_10);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_12;
}
}
obj* l_Lean_Parser_Combinators_sepBy_view___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_sepBy_view(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_tokens___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_Combinators_sepBy_tokens___rarg(x_0, x_1);
x_3 = l_Lean_Parser_tokens___rarg(x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, uint8 x_7) {
_start:
{
obj* x_8; 
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1_tokens___rarg___boxed), 2, 0);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_tokens___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_sepBy1_tokens___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_7);
x_9 = l_Lean_Parser_Combinators_sepBy1_tokens(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_8);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_9;
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_20; 
x_8 = lean::cnstr_get(x_4, 0);
x_10 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_12 = x_4;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_4);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_8, 1);
lean::inc(x_15);
lean::dec(x_8);
lean::inc(x_3);
lean::inc(x_2);
x_20 = l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___rarg(x_0, x_1, x_2, x_3, x_10);
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_3);
x_22 = lean::cnstr_get(x_2, 1);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::apply_1(x_22, x_13);
x_26 = lean::box(0);
if (lean::is_scalar(x_12)) {
 x_27 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_27 = x_12;
}
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_20);
return x_28;
}
else
{
obj* x_29; obj* x_32; obj* x_35; obj* x_36; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_29 = lean::cnstr_get(x_15, 0);
lean::inc(x_29);
lean::dec(x_15);
x_32 = lean::cnstr_get(x_2, 1);
lean::inc(x_32);
lean::dec(x_2);
x_35 = lean::apply_1(x_32, x_13);
x_36 = lean::cnstr_get(x_3, 1);
lean::inc(x_36);
lean::dec(x_3);
x_39 = lean::apply_1(x_36, x_29);
x_40 = lean::box(0);
if (lean::is_scalar(x_12)) {
 x_41 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_41 = x_12;
}
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_35);
lean::cnstr_set(x_42, 1, x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_20);
return x_43;
}
}
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_View___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
x_6 = l_List_join___main___rarg(x_5);
x_7 = l_Lean_Parser_noKind;
x_8 = l_Lean_Parser_Syntax_mkNode(x_7, x_6);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_View___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, uint8 x_8, obj* x_9, obj* x_10) {
_start:
{
obj* x_15; obj* x_16; obj* x_17; 
lean::inc(x_10);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_9);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy_view___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_6);
lean::closure_set(x_15, 2, x_7);
lean::closure_set(x_15, 3, x_10);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1_View___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_16, 0, x_6);
lean::closure_set(x_16, 1, x_7);
lean::closure_set(x_16, 2, x_9);
lean::closure_set(x_16, 3, x_10);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_View(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_sepBy1_View___rarg___boxed), 11, 0);
return x_1;
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_map___main___at_Lean_Parser_Combinators_sepBy1_View___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_View___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Combinators_sepBy1_View___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_View___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10) {
_start:
{
uint8 x_11; obj* x_12; 
x_11 = lean::unbox(x_8);
x_12 = l_Lean_Parser_Combinators_sepBy1_View___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_9, x_10);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_12;
}
}
obj* l_Lean_Parser_Combinators_sepBy1_View___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_sepBy1_View(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_optional___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 3);
lean::inc(x_11);
lean::dec(x_1);
x_14 = l_Option_get___main___at_Lean_Parser_run___spec__2(x_11);
lean::dec(x_11);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_Lean_Parser_noKind;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_21, 0, x_5);
lean::cnstr_set(x_21, 1, x_7);
lean::cnstr_set(x_21, 2, x_9);
lean::cnstr_set(x_21, 3, x_20);
x_22 = lean::apply_2(x_2, lean::box(0), x_21);
return x_22;
}
}
obj* l_Lean_Parser_Combinators_optional___rarg___lambda__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_3 = lean::apply_2(x_0, lean::box(0), x_2);
return x_3;
}
else
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_noKind;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
x_11 = lean::apply_2(x_0, lean::box(0), x_10);
return x_11;
}
}
}
obj* l_Lean_Parser_Combinators_optional___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___rarg___lambda__1), 2, 1);
lean::closure_set(x_10, 0, x_1);
x_11 = lean::apply_3(x_8, lean::box(0), x_4, x_10);
x_12 = lean::cnstr_get(x_3, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_3, 0);
lean::inc(x_14);
lean::dec(x_3);
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
lean::dec(x_17);
x_22 = l_optional___rarg___closed__1;
x_23 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_22, x_11);
x_24 = lean::cnstr_get(x_14, 1);
lean::inc(x_24);
lean::dec(x_14);
x_27 = lean::box(0);
lean::inc(x_24);
x_29 = lean::apply_2(x_24, lean::box(0), x_27);
x_30 = lean::apply_3(x_12, lean::box(0), x_23, x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___rarg___lambda__2), 2, 1);
lean::closure_set(x_31, 0, x_24);
x_32 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_30, x_31);
return x_32;
}
}
obj* l_Lean_Parser_Combinators_optional(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_optional___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Combinators_optional___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_optional___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_optional(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_optional_tokens___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_optional_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional_tokens___rarg___boxed), 1, 0);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_optional_tokens___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_optional_tokens___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_optional_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_optional_tokens(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_optional_view___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::box(3);
x_7 = lean::apply_1(x_3, x_6);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_11 = x_2;
} else {
 lean::inc(x_9);
 lean::dec(x_2);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; 
lean::dec(x_0);
lean::dec(x_11);
x_17 = lean::box(0);
return x_17;
}
else
{
obj* x_18; 
x_18 = lean::cnstr_get(x_12, 1);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
obj* x_20; obj* x_23; obj* x_26; obj* x_27; 
x_20 = lean::cnstr_get(x_12, 0);
lean::inc(x_20);
lean::dec(x_12);
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
lean::dec(x_0);
x_26 = lean::apply_1(x_23, x_20);
if (lean::is_scalar(x_11)) {
 x_27 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_27 = x_11;
}
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
else
{
obj* x_30; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_12);
lean::dec(x_18);
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
lean::dec(x_0);
x_33 = lean::box(3);
x_34 = lean::apply_1(x_30, x_33);
if (lean::is_scalar(x_11)) {
 x_35 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_35 = x_11;
}
lean::cnstr_set(x_35, 0, x_34);
return x_35;
}
}
}
}
}
obj* l_Lean_Parser_Combinators_optional_view___rarg___lambda__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = l_Lean_Parser_Combinators_many___rarg___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::apply_1(x_7, x_4);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_noKind;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
}
}
obj* l_Lean_Parser_Combinators_optional_view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional_view___rarg___lambda__1), 2, 1);
lean::closure_set(x_7, 0, x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional_view___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_5);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_optional_view(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional_view___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_optional_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_optional_view___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_optional_view___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_optional_view(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_optional_viewDefault___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::box(0);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_optional_viewDefault(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional_viewDefault___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_optional_viewDefault___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_optional_viewDefault___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_optional_viewDefault___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_optional_viewDefault(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Combinators_anyOf___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("anyOf");
return x_0;
}
}
obj* l_Lean_Parser_Combinators_anyOf___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = l_Lean_Parser_Combinators_anyOf___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_5, x_6, x_4, x_4);
return x_7;
}
else
{
obj* x_9; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_0);
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
lean::dec(x_1);
x_17 = lean::apply_1(x_14, lean::box(0));
x_18 = l_List_foldl___main___rarg(x_17, x_9, x_11);
return x_18;
}
}
}
obj* l_Lean_Parser_Combinators_anyOf(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_anyOf___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_anyOf___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Combinators_anyOf(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_anyOf_tokens___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_anyOf_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_anyOf_tokens___rarg___boxed), 1, 0);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_anyOf_tokens___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_anyOf_tokens___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_anyOf_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_anyOf_tokens(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_anyOf_view___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_Lean_Parser_Combinators_anyOf_view(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_anyOf_view___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_anyOf_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Combinators_anyOf_view___rarg(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_anyOf_view___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Combinators_anyOf_view(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_longestMatch___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
x_4 = lean::box(0);
x_2 = x_4;
goto lbl_3;
}
else
{
obj* x_5; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_10; obj* x_13; obj* x_16; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::apply_2(x_13, lean::box(0), x_7);
return x_16;
}
else
{
obj* x_18; 
lean::dec(x_5);
x_18 = lean::box(0);
x_2 = x_18;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; obj* x_23; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_2);
x_20 = lean::cnstr_get(x_0, 0);
lean::inc(x_20);
lean::dec(x_0);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
x_26 = l_Lean_Parser_choice;
x_27 = l_Lean_Parser_Syntax_mkNode(x_26, x_1);
x_28 = lean::apply_2(x_23, lean::box(0), x_27);
return x_28;
}
}
}
obj* l_Lean_Parser_Combinators_longestMatch___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = l_Lean_Parser_MonadParsec_longestMatch___rarg(x_0, x_2, lean::box(0), x_1, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_longestMatch___rarg___lambda__1), 2, 1);
lean::closure_set(x_8, 0, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_longestMatch(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_longestMatch___rarg), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_longestMatch___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_longestMatch(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_longestMatch_tokens___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_longestMatch_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_longestMatch_tokens___rarg___boxed), 1, 0);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_longestMatch_tokens___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_longestMatch_tokens___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_longestMatch_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_longestMatch_tokens(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_longestMatch_view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_mjoin___rarg___closed__1;
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_longestMatch_view(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_longestMatch_view___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_longestMatch_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Combinators_longestMatch_view___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_longestMatch_view___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_longestMatch_view(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::box(0);
x_10 = lean_name_mk_numeral(x_9, x_1);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_Syntax_mkNode(x_10, x_12);
x_14 = lean::apply_2(x_6, lean::box(0), x_13);
return x_14;
}
}
obj* _init_l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("choice: Empty List");
return x_0;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
x_11 = l_Lean_Parser_MonadParsec_error___rarg(x_1, lean::box(0), x_9, x_10, x_8, x_8);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_17; obj* x_19; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; 
x_12 = lean::cnstr_get(x_3, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_3, 1);
lean::inc(x_14);
lean::dec(x_3);
x_17 = lean::cnstr_get(x_2, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::inc(x_4);
lean::inc(x_2);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___rarg___lambda__1), 3, 2);
lean::closure_set(x_23, 0, x_2);
lean::closure_set(x_23, 1, x_4);
x_24 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_12, x_23);
x_25 = lean::mk_nat_obj(1u);
x_26 = lean::nat_add(x_4, x_25);
lean::dec(x_4);
x_28 = l_Lean_Parser_Combinators_choiceAux___main___rarg(x_0, x_1, x_2, x_14, x_26);
x_29 = lean::apply_3(x_17, lean::box(0), x_24, x_28);
return x_29;
}
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___rarg), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_choiceAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_choiceAux___main___rarg(x_0, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_choiceAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_choiceAux___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_choiceAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_choice___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Lean_Parser_Combinators_choiceAux___main___rarg(x_0, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_choice(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choice___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_choice___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Combinators_choice___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_choice___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_choice(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_choice_tokens___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_choice_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choice_tokens___rarg___boxed), 1, 0);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_choice_tokens___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_choice_tokens___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_choice_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_choice_tokens(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_6 = lean::cnstr_get(x_2, 0);
x_8 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_10 = x_2;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_2);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
lean::dec(x_6);
lean::inc(x_1);
lean::inc(x_0);
x_18 = l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1___rarg(x_0, x_1, x_8);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___rarg___lambda__1), 3, 2);
lean::closure_set(x_19, 0, x_0);
lean::closure_set(x_19, 1, x_11);
x_20 = lean::apply_4(x_1, lean::box(0), lean::box(0), x_13, x_19);
if (lean::is_scalar(x_10)) {
 x_21 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_21 = x_10;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_18);
return x_21;
}
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_longestChoice___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___rarg(x_0, lean::box(0), x_5, x_6, x_4, x_4);
return x_7;
}
else
{
obj* x_9; obj* x_12; obj* x_15; obj* x_18; 
lean::dec(x_0);
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
lean::dec(x_2);
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
lean::dec(x_1);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::apply_2(x_15, lean::box(0), x_9);
return x_18;
}
}
}
obj* l_Lean_Parser_Combinators_longestChoice___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_List_enumFrom___main___rarg(x_7, x_4);
lean::inc(x_5);
lean::inc(x_3);
x_11 = l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1___rarg(x_3, x_5, x_8);
lean::inc(x_2);
x_13 = l_Lean_Parser_MonadParsec_longestMatch___rarg(x_0, x_2, lean::box(0), x_1, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_longestChoice___rarg___lambda__1), 3, 2);
lean::closure_set(x_14, 0, x_2);
lean::closure_set(x_14, 1, x_3);
x_15 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
obj* l_Lean_Parser_Combinators_longestChoice(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_longestChoice___rarg), 5, 0);
return x_1;
}
}
obj* l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_map___main___at_Lean_Parser_Combinators_longestChoice___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_longestChoice___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_longestChoice(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_longestChoice_tokens___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_longestChoice_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_longestChoice_tokens___rarg___boxed), 1, 0);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_longestChoice_tokens___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_longestChoice_tokens___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_longestChoice_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_longestChoice_tokens(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_try_tokens___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_try_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_try_tokens___rarg___boxed), 1, 0);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_try_tokens___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_try_tokens___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_try_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_try_tokens(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_try_view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_6);
return x_9;
}
}
obj* l_Lean_Parser_Combinators_try_view(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_try_view___rarg___boxed), 4, 0);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_try_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Combinators_try_view___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_try_view___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Combinators_try_view(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_label_tokens___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_label_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_label_tokens___rarg___boxed), 1, 0);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_label_tokens___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_label_tokens___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_label_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_label_tokens(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_label_view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_10; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_7);
return x_10;
}
}
obj* l_Lean_Parser_Combinators_label_view(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_label_view___rarg___boxed), 5, 0);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_label_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Combinators_label_view___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_label_view___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Combinators_label_view(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_recurse_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_recurse_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Combinators_recurse_tokens(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_recurse_view___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_mjoin___rarg___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_recurse_view(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_recurse_view___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_recurse_view___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_recurse_view___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_recurse_view___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Combinators_recurse_view(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_monadLift_tokens___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_monadLift_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_monadLift_tokens___rarg___boxed), 1, 0);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_monadLift_tokens___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_monadLift_tokens___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_monadLift_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_Combinators_monadLift_tokens(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_7);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_monadLift_view___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_monadLift_view(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_monadLift_view___rarg___boxed), 3, 0);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_monadLift_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Combinators_monadLift_view___rarg(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_monadLift_view___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_monadLift_view(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_seqLeft_tokens___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_seqLeft_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_seqLeft_tokens___rarg___boxed), 1, 0);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_seqLeft_tokens___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_seqLeft_tokens___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_seqLeft_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_Combinators_seqLeft_tokens(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_7);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_seqLeft_view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_11; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
return x_11;
}
}
obj* l_Lean_Parser_Combinators_seqLeft_view(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_seqLeft_view___rarg___boxed), 6, 0);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_seqLeft_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_seqLeft_view___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_seqLeft_view___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Combinators_seqLeft_view(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_seqRight_tokens___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_seqRight_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_seqRight_tokens___rarg___boxed), 1, 0);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_seqRight_tokens___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Combinators_seqRight_tokens___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_seqRight_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_Combinators_seqRight_tokens(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_7);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_seqRight_view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_11; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
return x_11;
}
}
obj* l_Lean_Parser_Combinators_seqRight_view(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_seqRight_view___rarg___boxed), 6, 0);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_seqRight_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_Combinators_seqRight_view___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_seqRight_view___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Combinators_seqRight_view(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Parser_Combinators_coe_tokens___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tokens___rarg(x_0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_coe_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_coe_tokens___rarg___boxed), 2, 0);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_coe_tokens___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Combinators_coe_tokens___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_coe_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_coe_tokens(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_coe_view___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
}
obj* l_Lean_Parser_Combinators_coe_view(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_coe_view___rarg___boxed), 3, 0);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_coe_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Combinators_coe_view___rarg(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_Combinators_coe_view___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_coe_view(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_coe_viewDefault___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_coe_viewDefault(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_coe_viewDefault___rarg___boxed), 5, 0);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_coe_viewDefault___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_Combinators_coe_viewDefault___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_Combinators_coe_viewDefault___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_Combinators_coe_viewDefault(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_7;
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
 l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1 = _init_l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1();
lean::mark_persistent(l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1);
 l_Lean_Parser_Combinators_many___rarg___closed__1 = _init_l_Lean_Parser_Combinators_many___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Combinators_many___rarg___closed__1);
 l_Lean_Parser_Combinators_anyOf___rarg___closed__1 = _init_l_Lean_Parser_Combinators_anyOf___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Combinators_anyOf___rarg___closed__1);
 l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1 = _init_l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1);
return w;
}
