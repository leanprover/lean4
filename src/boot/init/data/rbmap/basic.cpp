// Lean compiler output
// Module: init.data.rbmap.basic
// Imports: init.data.ordering.basic init.coe init.data.option.basic
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
obj* l_rbnode_fold(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_mfold___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap_from__list___spec__2(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_rbmap__of___spec__1___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap__of___spec__4___boxed(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__3(obj*, obj*, obj*);
obj* l_rbnode_mfold___main___at_rbmap_mfor___spec__1(obj*, obj*, obj*, obj*);
obj* l_rbnode_is__red___main(obj*, obj*);
obj* l_rbmap_find___main(obj*, obj*, obj*);
obj* l_rbnode_rev__fold___boxed(obj*, obj*, obj*);
obj* l_rbnode_fold___main(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__4(obj*, obj*, obj*);
obj* l_rbmap_find__core___boxed(obj*, obj*, obj*);
obj* l_rbmap_rev__fold(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap__of___spec__4(obj*, obj*, obj*);
obj* l_rbnode_mfold___main___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___boxed(obj*, obj*, obj*);
obj* l_rbmap_has__repr___boxed(obj*, obj*, obj*);
obj* l_rbnode_any___main(obj*, obj*);
obj* l_rbnode_balance2___rarg(obj*, obj*);
obj* l_rbnode_set__black___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_of__list___main___boxed(obj*, obj*, obj*);
obj* l_rbmap_max___main___boxed(obj*, obj*, obj*);
obj* l_rbmap_mfold___main(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_max___main___rarg(obj*);
obj* l_rbnode_all___rarg(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_rbmap;
obj* l_rbmap_insert___main___rarg(obj*, obj*, obj*, obj*);
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(obj*, obj*, uint8, obj*);
obj* l_rbmap_all___main(obj*, obj*, obj*);
obj* l_rbnode_fold___rarg(obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap_of__list___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_rbmap_mfold___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_fold___rarg(obj*, obj*, obj*);
obj* l_rbnode_lower__bound___main(obj*, obj*, obj*);
obj* l_rbnode_max___rarg(obj*);
obj* l_rbnode_fold___main___boxed(obj*, obj*, obj*);
obj* l_rbmap_min(obj*, obj*, obj*);
obj* l_rbnode_depth___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__3___boxed(obj*, obj*, obj*);
obj* l_rbmap_find__core___rarg(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap__of___spec__2___boxed(obj*, obj*, obj*);
obj* l_rbnode_mfold___main___at_rbmap_mfor___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap_from__list___spec__1___boxed(obj*, obj*, obj*);
obj* l_rbnode_set__black(obj*, obj*);
obj* l_rbnode_max___main___boxed(obj*, obj*);
obj* l_rbnode_ins___main___boxed(obj*, obj*, obj*);
obj* l_rbnode_ins___main(obj*, obj*, obj*);
obj* l_rbmap_find(obj*, obj*, obj*);
obj* l_rbmap_mfor(obj*, obj*, obj*, obj*, obj*);
obj* l_mk__rbmap___boxed(obj*, obj*, obj*);
obj* l_rbnode_all(obj*, obj*);
obj* l_rbnode_find(obj*, obj*);
obj* l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_balance1___main___boxed(obj*, obj*);
obj* l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1(obj*, obj*);
obj* l_rbnode_ins___main___at_rbnode_insert___spec__2(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbnode_insert___spec__2___boxed(obj*, obj*, obj*);
obj* l_rbnode_find__core___main(obj*, obj*, obj*);
obj* l_rbmap_find__core___main___boxed(obj*, obj*, obj*);
obj* l_rbnode_min___main___rarg(obj*);
obj* l_mk__rbmap(obj*, obj*, obj*);
obj* l_rbnode_find___main___at_rbmap_contains___spec__2(obj*, obj*);
obj* l_rbmap_from__list___at_rbmap__of___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbnode_any___main___rarg(obj*, obj*);
obj* l_rbnode_min(obj*, obj*);
obj* l_rbmap_insert___boxed(obj*, obj*, obj*);
obj* l_rbnode_balance1(obj*, obj*);
obj* l_rbmap_of__list(obj*, obj*, obj*);
obj* l_rbnode_depth___main(obj*, obj*);
obj* l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___boxed(obj*, obj*);
obj* l_rbnode_find__core___rarg(obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap__of___spec__3___boxed(obj*, obj*, obj*);
obj* l_rbmap_min___main___rarg(obj*);
obj* l_rbmap__of___rarg(obj*, obj*, obj*);
obj* l_rbmap_has__repr(obj*, obj*, obj*);
obj* l_rbnode_balance1___boxed(obj*, obj*);
obj* l_rbmap_all___main___boxed(obj*, obj*, obj*);
obj* l_rbnode_insert___boxed(obj*, obj*, obj*);
obj* l_rbnode_mfold___main(obj*, obj*, obj*, obj*);
uint8 l_rbmap_contains___rarg(obj*, obj*, obj*);
obj* l_rbmap_has__repr___rarg___closed__1;
obj* l_rbnode_rev__fold(obj*, obj*, obj*);
obj* l_rbnode_set__black___main___boxed(obj*, obj*);
obj* l_rbmap_contains___boxed(obj*, obj*, obj*);
obj* l_list_foldl___main___at_rbmap__of___spec__6___boxed(obj*, obj*, obj*);
obj* l_rbnode_find___main___at_rbmap_contains___spec__2___boxed(obj*, obj*);
obj* l_rbnode_lower__bound___main___boxed(obj*, obj*, obj*);
obj* l_rbnode_depth___main___rarg(obj*, obj*);
obj* l_rbmap_fold___main___rarg(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_rbmap_contains___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbmap_find___main___boxed(obj*, obj*, obj*);
obj* l_rbnode_balance2___boxed(obj*, obj*);
obj* l_rbnode_depth___rarg___boxed(obj*, obj*);
obj* l_rbmap_lower__bound___main___rarg(obj*, obj*, obj*);
obj* l_rbmap_mfor___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_list_repr___main___at_rbmap_has__repr___spec__1___boxed(obj*, obj*);
obj* l_rbnode_any___main___boxed(obj*, obj*);
obj* l_rbnode_rev__fold___rarg(obj*, obj*, obj*);
obj* l_rbnode_find___main(obj*, obj*);
extern obj* l_list_repr___main___rarg___closed__1;
obj* l_rbnode_rev__fold___main(obj*, obj*, obj*);
obj* l_rbmap_to__list___main___rarg(obj*);
obj* l_list_foldl___main___at_rbmap_from__list___spec__5___boxed(obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap__of___spec__3(obj*, obj*, obj*);
obj* l_rbnode_lower__bound___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_empty___main(obj*, obj*, obj*);
obj* l_rbnode_find___main___at_rbmap_find___main___spec__1(obj*, obj*);
obj* l_rbnode_all___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__4(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_rbmap_contains(obj*, obj*, obj*);
obj* l_rbmap_empty___main___rarg___boxed(obj*);
obj* l_rbnode_find__core(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbnode_insert___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__3(obj*, obj*, obj*);
uint8 l_option_is__some___main___rarg(obj*);
obj* l_rbnode_insert___at_rbmap_from__list___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_find__core___main___boxed(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap__of___spec__2(obj*, obj*, obj*);
obj* l_rbmap__of___rarg___boxed(obj*, obj*, obj*);
obj* l_rbnode_all___main___boxed(obj*, obj*);
uint8 l_rbmap_empty___main___rarg(obj*);
uint8 l_rbnode_is__red___rarg(obj*);
obj* l_rbmap_any___main(obj*, obj*, obj*);
obj* l_rbnode_ins___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_min___main___boxed(obj*, obj*);
obj* l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1(obj*, obj*, obj*);
obj* l_rbmap_from__list___rarg___boxed(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap_of__list___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_rbmap__of(obj*, obj*);
obj* l_rbnode_all___main___rarg(obj*, obj*);
obj* l_rbnode_mfold___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap_from__list___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_rbmap__of___spec__6(obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap_of__list___main___spec__2(obj*, obj*, obj*);
obj* l_rbnode_any___boxed(obj*, obj*);
obj* l_rbmap_insert___main(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap__of___spec__5___boxed(obj*, obj*, obj*);
obj* l_rbmap_fold(obj*, obj*, obj*, obj*);
obj* l_rbmap__of___boxed(obj*, obj*);
obj* l_rbmap_any___boxed(obj*, obj*, obj*, obj*);
extern obj* l_list_repr__aux___main___rarg___closed__1;
obj* l_rbnode_find___main___boxed(obj*, obj*);
obj* l_rbnode_set__black___rarg(obj*);
obj* l_rbmap_min___main___boxed(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbnode_insert___spec__1(obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap_insert___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_rbnode_depth___main___rarg___boxed(obj*, obj*);
obj* l_rbnode_is__red___rarg___boxed(obj*);
obj* l_rbmap_of__list___boxed(obj*, obj*, obj*);
extern obj* l_list_repr___main___rarg___closed__3;
obj* l_rbmap_mfold___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_balance1___rarg(obj*, obj*);
obj* l_rbmap_rev__fold___main___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_any(obj*, obj*, obj*, obj*);
obj* l_rbnode_is__red(obj*, obj*);
obj* l_rbmap_find__core___main(obj*, obj*, obj*);
obj* l_rbnode_find__core___boxed(obj*, obj*, obj*);
obj* l_rbmap_lower__bound___boxed(obj*, obj*, obj*);
obj* l_rbnode_mfold___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_from__list___boxed(obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_rbmap_from__list___at_rbmap__of___spec__1(obj*, obj*);
obj* l_rbnode_any___rarg(obj*, obj*);
obj* l_rbmap_mfold(obj*, obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_rbmap_from__list___spec__5___rarg(obj*, obj*, obj*);
obj* l_rbnode_find___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___at_rbmap_contains___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap_of__list___main___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_is__red___boxed(obj*, obj*);
obj* l_rbmap_to__list___boxed(obj*, obj*, obj*);
obj* l_rbmap_max___main(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__3(obj*, obj*, obj*);
obj* l_rbmap_from__list(obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___boxed(obj*, obj*, obj*);
obj* l_rbnode_lower__bound(obj*, obj*, obj*);
obj* l_rbmap_max(obj*, obj*, obj*);
obj* l_rbmap_to__list(obj*, obj*, obj*);
obj* l_rbnode_balance2___main___rarg(obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___at_rbmap_find___main___spec__1___boxed(obj*, obj*);
obj* l_rbnode_mfold___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap_from__list___spec__1(obj*, obj*, obj*);
obj* l_rbmap_insert(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap_of__list___main___spec__1(obj*, obj*, obj*);
uint8 l_rbmap_empty___rarg(obj*);
obj* l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_rbmap_lower__bound___main(obj*, obj*, obj*);
obj* l_rbmap_all___rarg(obj*, obj*);
obj* l_rbnode_find__core___main___rarg(obj*, obj*, obj*);
obj* l_rbnode_find___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_is__red___main___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap__of___spec__5(obj*, obj*, obj*);
obj* l_rbmap_any___main___boxed(obj*, obj*, obj*);
obj* l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___rarg(obj*, obj*);
obj* l_rbmap_has__repr___rarg(obj*, obj*, obj*);
obj* l_rbmap_fold___main___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_depth___rarg(obj*, obj*);
obj* l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg(obj*, obj*, obj*, obj*);
extern obj* l_list_repr___main___rarg___closed__2;
obj* l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1(obj*, obj*, obj*);
obj* l_rbmap_from__list___at_rbmap__of___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap_insert___main___spec__1(obj*, obj*, obj*);
obj* l_rbmap_from__list___rarg(obj*, obj*, obj*);
obj* l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_rbnode_lower__bound___boxed(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbnode_insert___spec__1___boxed(obj*, obj*, obj*);
extern obj* l_prod_has__repr___rarg___closed__1;
obj* l_rbmap_max___rarg(obj*);
obj* l_rbnode_max___boxed(obj*, obj*);
obj* l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_mfold___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_rev__fold___main___rarg(obj*, obj*, obj*);
obj* l_rbmap_find___rarg(obj*, obj*, obj*);
obj* l_rbmap_insert___main___boxed(obj*, obj*, obj*);
obj* l_rbmap_empty___boxed(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__3___boxed(obj*, obj*, obj*);
obj* l_rbnode_max(obj*, obj*);
obj* l_rbnode_min___main(obj*, obj*);
obj* l_rbnode_mfold(obj*, obj*, obj*, obj*);
obj* l_rbmap_depth___rarg(obj*, obj*);
obj* l_rbnode_fold___main___rarg(obj*, obj*, obj*);
obj* l_rbnode_mfold___main___boxed(obj*, obj*, obj*, obj*);
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_list_repr___main___at_rbmap_has__repr___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbnode_is__red___main___rarg___boxed(obj*);
obj* l_rbnode_set__black___main(obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap__of___spec__5___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_balance1___main___rarg(obj*, obj*);
obj* l_rbnode_insert___at_rbmap__of___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_max___boxed(obj*, obj*, obj*);
obj* l_rbmap_depth___boxed(obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap_insert___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_balance2___main___boxed(obj*, obj*);
obj* l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__2(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap_of__list___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_empty___main___boxed(obj*, obj*, obj*);
obj* l_rbmap_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_depth(obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins(obj*, obj*, obj*);
obj* l_rbmap_depth(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_to__list___main___boxed(obj*, obj*, obj*);
obj* l_rbnode_all___main(obj*, obj*);
obj* l_rbmap_to__list___main(obj*, obj*, obj*);
obj* l_rbmap_depth___rarg___boxed(obj*, obj*);
obj* l_rbmap_of__list___rarg(obj*, obj*);
obj* l_rbnode_find___boxed(obj*, obj*);
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2(obj*, obj*);
obj* l_rbmap_min___main(obj*, obj*, obj*);
obj* l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_rev__fold___main___rarg(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__4___boxed(obj*, obj*, obj*);
obj* l_rbmap_mfor___rarg(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_rbmap_contains___spec__1___boxed(obj*, obj*, obj*);
obj* l_rbnode_depth___main___boxed(obj*, obj*);
obj* l_rbnode_any(obj*, obj*);
obj* l_rbmap_all___main___rarg(obj*, obj*);
obj* l_rbmap_find___main___rarg(obj*, obj*, obj*);
obj* l_rbnode_balance2(obj*, obj*);
obj* l_rbnode_find___main___at_rbmap_contains___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___rarg(obj*, obj*, obj*, obj*);
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2___boxed(obj*, obj*);
obj* l_rbnode_insert(obj*, obj*, obj*);
obj* l_rbnode_find___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_min___rarg(obj*);
obj* l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_of__list___main___rarg(obj*, obj*);
obj* l_rbmap_lower__bound(obj*, obj*, obj*);
obj* l_rbnode_max___main(obj*, obj*);
obj* l_rbnode_max___main___rarg(obj*);
extern obj* l_option_has__repr___rarg___closed__3;
obj* l_rbmap_rev__fold___rarg(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_rbmap_contains___spec__1(obj*, obj*, obj*);
uint8 l_rbnode_is__red___main___rarg(obj*);
obj* l_rbmap_lower__bound___rarg(obj*, obj*, obj*);
obj* l_rbmap_of__list___main(obj*, obj*, obj*);
obj* l_rbmap_min___boxed(obj*, obj*, obj*);
obj* l_rbmap_contains___rarg___boxed(obj*, obj*, obj*);
obj* l_list_foldl___main___at_rbmap_from__list___spec__5(obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap_from__list___spec__2___boxed(obj*, obj*, obj*);
obj* l_rbmap_all(obj*, obj*, obj*, obj*);
obj* l_rbmap_find___boxed(obj*, obj*, obj*);
obj* l_list_repr___main___at_rbmap_has__repr___spec__1(obj*, obj*);
obj* l_rbnode_balance2___main(obj*, obj*);
obj* l_rbnode_rev__fold___main___boxed(obj*, obj*, obj*);
obj* l_rbmap_any___main___rarg(obj*, obj*);
obj* l_rbmap_empty(obj*, obj*, obj*);
obj* l_rbmap_to__list___rarg(obj*);
obj* l_rbmap_empty___rarg___boxed(obj*);
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__4___boxed(obj*, obj*, obj*);
obj* l_rbmap_lower__bound___main___boxed(obj*, obj*, obj*);
obj* l_rbmap_fold___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_lower__bound___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_rev__fold___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_balance1___main(obj*, obj*);
obj* l_rbnode_min___boxed(obj*, obj*);
obj* l_rbmap_find__core(obj*, obj*, obj*);
obj* l_rbmap_rev__fold___main(obj*, obj*, obj*, obj*);
obj* l_rbmap_fold___main(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_rbmap__of___spec__6___rarg(obj*, obj*, obj*);
obj* l_rbnode_set__black___main___rarg(obj*);
obj* l_rbmap_insert___main___at_rbmap__of___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_fold___boxed(obj*, obj*, obj*);
obj* l_rbmap_all___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_min___rarg(obj*);
obj* l_rbmap_any___rarg(obj*, obj*);
obj* l_rbmap_find__core___main___rarg(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_depth___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::mk_nat_obj(0u);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 3);
lean::inc(x_0);
x_7 = l_rbnode_depth___main___rarg(x_0, x_4);
lean::inc(x_0);
x_9 = l_rbnode_depth___main___rarg(x_0, x_5);
x_10 = lean::apply_2(x_0, x_7, x_9);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_10, x_11);
lean::dec(x_10);
return x_12;
}
}
}
obj* l_rbnode_depth___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_depth___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_rbnode_depth___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_depth___main___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_depth___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_depth___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_depth___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_depth___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbnode_depth(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_depth___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_rbnode_depth___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_depth___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_depth___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_depth(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_min___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
else
{
lean::dec(x_0);
x_0 = x_2;
goto _start;
}
}
}
}
obj* l_rbnode_min___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_min___main___rarg), 1, 0);
return x_2;
}
}
obj* l_rbnode_min___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_min___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_min___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_min___main___rarg(x_0);
return x_1;
}
}
obj* l_rbnode_min(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_min___rarg), 1, 0);
return x_2;
}
}
obj* l_rbnode_min___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_min(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_max___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 3);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
else
{
lean::dec(x_0);
x_0 = x_2;
goto _start;
}
}
}
}
obj* l_rbnode_max___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_max___main___rarg), 1, 0);
return x_2;
}
}
obj* l_rbnode_max___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_max___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_max___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_max___main___rarg(x_0);
return x_1;
}
}
obj* l_rbnode_max(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_max___rarg), 1, 0);
return x_2;
}
}
obj* l_rbnode_max___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_max(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_fold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_14; obj* x_16; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = l_rbnode_fold___main___rarg(x_0, x_4, x_2);
lean::inc(x_0);
x_16 = lean::apply_3(x_0, x_6, x_8, x_14);
x_1 = x_10;
x_2 = x_16;
goto _start;
}
}
}
obj* l_rbnode_fold___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_fold___main___rarg), 3, 0);
return x_3;
}
}
obj* l_rbnode_fold___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_fold___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbnode_fold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_fold___rarg), 3, 0);
return x_3;
}
}
obj* l_rbnode_fold___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_fold(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_mfold___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_0);
x_8 = lean::apply_3(x_0, x_1, x_2, x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___rarg), 4, 3);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_0);
lean::closure_set(x_9, 2, x_4);
x_10 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_rbnode_mfold___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_8; obj* x_11; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_2(x_8, lean::box(0), x_3);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_25; obj* x_27; obj* x_28; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_2, 2);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_2, 3);
lean::inc(x_18);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::inc(x_1);
lean::inc(x_0);
x_25 = l_rbnode_mfold___main___rarg(x_0, x_1, x_12, x_3);
lean::inc(x_21);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___rarg___lambda__1), 7, 6);
lean::closure_set(x_27, 0, x_1);
lean::closure_set(x_27, 1, x_14);
lean::closure_set(x_27, 2, x_16);
lean::closure_set(x_27, 3, x_0);
lean::closure_set(x_27, 4, x_18);
lean::closure_set(x_27, 5, x_21);
x_28 = lean::apply_4(x_21, lean::box(0), lean::box(0), x_25, x_27);
return x_28;
}
}
}
obj* l_rbnode_mfold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___rarg), 4, 0);
return x_4;
}
}
obj* l_rbnode_mfold___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_mfold___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_rbnode_mfold___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_mfold___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbnode_mfold(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___rarg), 4, 0);
return x_4;
}
}
obj* l_rbnode_mfold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_mfold(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_rbnode_rev__fold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_14; obj* x_16; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = l_rbnode_rev__fold___main___rarg(x_0, x_10, x_2);
lean::inc(x_0);
x_16 = lean::apply_3(x_0, x_6, x_8, x_14);
x_1 = x_4;
x_2 = x_16;
goto _start;
}
}
}
obj* l_rbnode_rev__fold___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_rev__fold___main___rarg), 3, 0);
return x_3;
}
}
obj* l_rbnode_rev__fold___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_rev__fold___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_rev__fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_rev__fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbnode_rev__fold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_rev__fold___rarg), 3, 0);
return x_3;
}
}
obj* l_rbnode_rev__fold___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_rev__fold(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_all___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; obj* x_4; 
lean::dec(x_0);
x_3 = 1;
x_4 = lean::box(x_3);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_15; uint8 x_16; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 3);
lean::inc(x_11);
lean::dec(x_1);
lean::inc(x_0);
x_15 = lean::apply_2(x_0, x_7, x_9);
x_16 = lean::unbox(x_15);
if (x_16 == 0)
{
lean::dec(x_5);
if (x_16 == 0)
{
lean::dec(x_0);
lean::dec(x_11);
return x_15;
}
else
{
x_1 = x_11;
goto _start;
}
}
else
{
obj* x_22; uint8 x_23; 
lean::inc(x_0);
x_22 = l_rbnode_all___main___rarg(x_0, x_5);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
lean::dec(x_0);
lean::dec(x_11);
return x_22;
}
else
{
x_1 = x_11;
goto _start;
}
}
}
}
}
obj* l_rbnode_all___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_all___main___rarg), 2, 0);
return x_2;
}
}
obj* l_rbnode_all___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_all___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_all___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_all___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbnode_all(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_all___rarg), 2, 0);
return x_2;
}
}
obj* l_rbnode_all___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_all(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_any___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; obj* x_4; 
lean::dec(x_0);
x_3 = 0;
x_4 = lean::box(x_3);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_15; uint8 x_16; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 3);
lean::inc(x_11);
lean::dec(x_1);
lean::inc(x_0);
x_15 = lean::apply_2(x_0, x_7, x_9);
x_16 = lean::unbox(x_15);
if (x_16 == 0)
{
obj* x_18; uint8 x_19; 
lean::inc(x_0);
x_18 = l_rbnode_any___main___rarg(x_0, x_5);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
x_1 = x_11;
goto _start;
}
else
{
lean::dec(x_0);
lean::dec(x_11);
return x_18;
}
}
else
{
lean::dec(x_5);
if (x_16 == 0)
{
x_1 = x_11;
goto _start;
}
else
{
lean::dec(x_0);
lean::dec(x_11);
return x_15;
}
}
}
}
}
obj* l_rbnode_any___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_any___main___rarg), 2, 0);
return x_2;
}
}
obj* l_rbnode_any___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_any___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_any___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_any___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbnode_any(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_any___rarg), 2, 0);
return x_2;
}
}
obj* l_rbnode_any___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_any(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_balance1___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
x_6 = lean::cnstr_get(x_1, 3);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; uint8 x_23; obj* x_24; obj* x_25; 
x_8 = lean::cnstr_get(x_0, 1);
x_10 = lean::cnstr_get(x_0, 2);
x_12 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_14 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_0);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_1, 1);
x_17 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 3);
 x_19 = x_1;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_1);
 x_19 = lean::box(0);
}
x_20 = 0;
if (lean::is_scalar(x_19)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_19;
}
lean::cnstr_set(x_21, 0, x_6);
lean::cnstr_set(x_21, 1, x_15);
lean::cnstr_set(x_21, 2, x_17);
lean::cnstr_set(x_21, 3, x_6);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_20);
x_22 = x_21;
x_23 = 1;
if (lean::is_scalar(x_14)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_14;
}
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_8);
lean::cnstr_set(x_24, 2, x_10);
lean::cnstr_set(x_24, 3, x_12);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_23);
x_25 = x_24;
return x_25;
}
else
{
obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_26 = lean::cnstr_get(x_0, 1);
x_28 = lean::cnstr_get(x_0, 2);
x_30 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_32 = x_0;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_0);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_1, 1);
x_35 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_release(x_1, 3);
 x_37 = x_1;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*4);
if (x_38 == 0)
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_39 = lean::cnstr_get(x_6, 0);
x_41 = lean::cnstr_get(x_6, 1);
x_43 = lean::cnstr_get(x_6, 2);
x_45 = lean::cnstr_get(x_6, 3);
if (lean::is_exclusive(x_6)) {
 x_47 = x_6;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_6);
 x_47 = lean::box(0);
}
x_48 = 1;
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_4);
lean::cnstr_set(x_49, 1, x_33);
lean::cnstr_set(x_49, 2, x_35);
lean::cnstr_set(x_49, 3, x_39);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_48);
x_50 = x_49;
if (lean::is_scalar(x_37)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_37;
}
lean::cnstr_set(x_51, 0, x_45);
lean::cnstr_set(x_51, 1, x_26);
lean::cnstr_set(x_51, 2, x_28);
lean::cnstr_set(x_51, 3, x_30);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_48);
x_52 = x_51;
if (lean::is_scalar(x_32)) {
 x_53 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_53 = x_32;
}
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set(x_53, 1, x_41);
lean::cnstr_set(x_53, 2, x_43);
lean::cnstr_set(x_53, 3, x_52);
lean::cnstr_set_scalar(x_53, sizeof(void*)*4, x_38);
x_54 = x_53;
return x_54;
}
else
{
uint8 x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_55 = 0;
if (lean::is_scalar(x_37)) {
 x_56 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_56 = x_37;
}
lean::cnstr_set(x_56, 0, x_4);
lean::cnstr_set(x_56, 1, x_33);
lean::cnstr_set(x_56, 2, x_35);
lean::cnstr_set(x_56, 3, x_6);
lean::cnstr_set_scalar(x_56, sizeof(void*)*4, x_55);
x_57 = x_56;
if (lean::is_scalar(x_32)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_32;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_26);
lean::cnstr_set(x_58, 2, x_28);
lean::cnstr_set(x_58, 3, x_30);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_38);
x_59 = x_58;
return x_59;
}
}
}
else
{
obj* x_60; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_69; obj* x_71; obj* x_73; uint8 x_74; 
x_60 = lean::cnstr_get(x_0, 1);
x_62 = lean::cnstr_get(x_0, 2);
x_64 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_66 = x_0;
} else {
 lean::inc(x_60);
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_0);
 x_66 = lean::box(0);
}
x_67 = lean::cnstr_get(x_1, 1);
x_69 = lean::cnstr_get(x_1, 2);
x_71 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_73 = x_1;
} else {
 lean::inc(x_67);
 lean::inc(x_69);
 lean::inc(x_71);
 lean::dec(x_1);
 x_73 = lean::box(0);
}
x_74 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*4);
if (x_74 == 0)
{
if (lean::obj_tag(x_71) == 0)
{
obj* x_75; obj* x_77; obj* x_79; obj* x_81; obj* x_83; uint8 x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_75 = lean::cnstr_get(x_4, 0);
x_77 = lean::cnstr_get(x_4, 1);
x_79 = lean::cnstr_get(x_4, 2);
x_81 = lean::cnstr_get(x_4, 3);
if (lean::is_exclusive(x_4)) {
 x_83 = x_4;
} else {
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::inc(x_81);
 lean::dec(x_4);
 x_83 = lean::box(0);
}
x_84 = 1;
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_75);
lean::cnstr_set(x_85, 1, x_77);
lean::cnstr_set(x_85, 2, x_79);
lean::cnstr_set(x_85, 3, x_81);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_84);
x_86 = x_85;
if (lean::is_scalar(x_73)) {
 x_87 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_87 = x_73;
}
lean::cnstr_set(x_87, 0, x_71);
lean::cnstr_set(x_87, 1, x_60);
lean::cnstr_set(x_87, 2, x_62);
lean::cnstr_set(x_87, 3, x_64);
lean::cnstr_set_scalar(x_87, sizeof(void*)*4, x_84);
x_88 = x_87;
if (lean::is_scalar(x_66)) {
 x_89 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_89 = x_66;
}
lean::cnstr_set(x_89, 0, x_86);
lean::cnstr_set(x_89, 1, x_67);
lean::cnstr_set(x_89, 2, x_69);
lean::cnstr_set(x_89, 3, x_88);
lean::cnstr_set_scalar(x_89, sizeof(void*)*4, x_74);
x_90 = x_89;
return x_90;
}
else
{
obj* x_91; obj* x_93; obj* x_95; obj* x_97; obj* x_99; uint8 x_100; 
x_91 = lean::cnstr_get(x_4, 0);
x_93 = lean::cnstr_get(x_4, 1);
x_95 = lean::cnstr_get(x_4, 2);
x_97 = lean::cnstr_get(x_4, 3);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 lean::cnstr_set(x_4, 2, lean::box(0));
 lean::cnstr_set(x_4, 3, lean::box(0));
 x_99 = x_4;
} else {
 lean::inc(x_91);
 lean::inc(x_93);
 lean::inc(x_95);
 lean::inc(x_97);
 lean::dec(x_4);
 x_99 = lean::box(0);
}
x_100 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*4);
if (x_100 == 0)
{
uint8 x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_101 = 1;
if (lean::is_scalar(x_99)) {
 x_102 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_102 = x_99;
}
lean::cnstr_set(x_102, 0, x_91);
lean::cnstr_set(x_102, 1, x_93);
lean::cnstr_set(x_102, 2, x_95);
lean::cnstr_set(x_102, 3, x_97);
lean::cnstr_set_scalar(x_102, sizeof(void*)*4, x_101);
x_103 = x_102;
if (lean::is_scalar(x_73)) {
 x_104 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_104 = x_73;
}
lean::cnstr_set(x_104, 0, x_71);
lean::cnstr_set(x_104, 1, x_60);
lean::cnstr_set(x_104, 2, x_62);
lean::cnstr_set(x_104, 3, x_64);
lean::cnstr_set_scalar(x_104, sizeof(void*)*4, x_101);
x_105 = x_104;
if (lean::is_scalar(x_66)) {
 x_106 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_106 = x_66;
}
lean::cnstr_set(x_106, 0, x_103);
lean::cnstr_set(x_106, 1, x_67);
lean::cnstr_set(x_106, 2, x_69);
lean::cnstr_set(x_106, 3, x_105);
lean::cnstr_set_scalar(x_106, sizeof(void*)*4, x_100);
x_107 = x_106;
return x_107;
}
else
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
if (lean::is_scalar(x_99)) {
 x_108 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_108 = x_99;
}
lean::cnstr_set(x_108, 0, x_91);
lean::cnstr_set(x_108, 1, x_93);
lean::cnstr_set(x_108, 2, x_95);
lean::cnstr_set(x_108, 3, x_97);
lean::cnstr_set_scalar(x_108, sizeof(void*)*4, x_100);
x_109 = x_108;
if (lean::is_scalar(x_73)) {
 x_110 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_110 = x_73;
}
lean::cnstr_set(x_110, 0, x_71);
lean::cnstr_set(x_110, 1, x_60);
lean::cnstr_set(x_110, 2, x_62);
lean::cnstr_set(x_110, 3, x_64);
lean::cnstr_set_scalar(x_110, sizeof(void*)*4, x_100);
x_111 = x_110;
if (lean::is_scalar(x_66)) {
 x_112 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_112 = x_66;
}
lean::cnstr_set(x_112, 0, x_109);
lean::cnstr_set(x_112, 1, x_67);
lean::cnstr_set(x_112, 2, x_69);
lean::cnstr_set(x_112, 3, x_111);
lean::cnstr_set_scalar(x_112, sizeof(void*)*4, x_74);
x_113 = x_112;
return x_113;
}
}
}
else
{
if (lean::obj_tag(x_71) == 0)
{
uint8 x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_114 = 0;
if (lean::is_scalar(x_73)) {
 x_115 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_115 = x_73;
}
lean::cnstr_set(x_115, 0, x_4);
lean::cnstr_set(x_115, 1, x_67);
lean::cnstr_set(x_115, 2, x_69);
lean::cnstr_set(x_115, 3, x_71);
lean::cnstr_set_scalar(x_115, sizeof(void*)*4, x_114);
x_116 = x_115;
if (lean::is_scalar(x_66)) {
 x_117 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_117 = x_66;
}
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_60);
lean::cnstr_set(x_117, 2, x_62);
lean::cnstr_set(x_117, 3, x_64);
lean::cnstr_set_scalar(x_117, sizeof(void*)*4, x_74);
x_118 = x_117;
return x_118;
}
else
{
obj* x_119; obj* x_121; obj* x_123; obj* x_125; uint8 x_127; 
x_119 = lean::cnstr_get(x_4, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_4, 1);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_4, 2);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_4, 3);
lean::inc(x_125);
x_127 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*4);
if (x_127 == 0)
{
obj* x_133; obj* x_135; obj* x_137; obj* x_139; obj* x_141; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
lean::dec(x_123);
lean::dec(x_121);
lean::dec(x_119);
lean::dec(x_125);
lean::dec(x_66);
x_133 = lean::cnstr_get(x_71, 0);
x_135 = lean::cnstr_get(x_71, 1);
x_137 = lean::cnstr_get(x_71, 2);
x_139 = lean::cnstr_get(x_71, 3);
if (lean::is_exclusive(x_71)) {
 x_141 = x_71;
} else {
 lean::inc(x_133);
 lean::inc(x_135);
 lean::inc(x_137);
 lean::inc(x_139);
 lean::dec(x_71);
 x_141 = lean::box(0);
}
lean::inc(x_4);
if (lean::is_scalar(x_141)) {
 x_143 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_143 = x_141;
}
lean::cnstr_set(x_143, 0, x_4);
lean::cnstr_set(x_143, 1, x_67);
lean::cnstr_set(x_143, 2, x_69);
lean::cnstr_set(x_143, 3, x_133);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_144 = x_4;
} else {
 lean::dec(x_4);
 x_144 = lean::box(0);
}
lean::cnstr_set_scalar(x_143, sizeof(void*)*4, x_74);
x_145 = x_143;
if (lean::is_scalar(x_144)) {
 x_146 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_146 = x_144;
}
lean::cnstr_set(x_146, 0, x_139);
lean::cnstr_set(x_146, 1, x_60);
lean::cnstr_set(x_146, 2, x_62);
lean::cnstr_set(x_146, 3, x_64);
lean::cnstr_set_scalar(x_146, sizeof(void*)*4, x_74);
x_147 = x_146;
if (lean::is_scalar(x_73)) {
 x_148 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_148 = x_73;
}
lean::cnstr_set(x_148, 0, x_145);
lean::cnstr_set(x_148, 1, x_135);
lean::cnstr_set(x_148, 2, x_137);
lean::cnstr_set(x_148, 3, x_147);
lean::cnstr_set_scalar(x_148, sizeof(void*)*4, x_127);
x_149 = x_148;
return x_149;
}
else
{
obj* x_150; obj* x_151; obj* x_152; uint8 x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_150 = x_4;
} else {
 lean::dec(x_4);
 x_150 = lean::box(0);
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_119);
lean::cnstr_set(x_151, 1, x_121);
lean::cnstr_set(x_151, 2, x_123);
lean::cnstr_set(x_151, 3, x_125);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_127);
x_152 = x_151;
x_153 = 0;
if (lean::is_scalar(x_73)) {
 x_154 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_154 = x_73;
}
lean::cnstr_set(x_154, 0, x_152);
lean::cnstr_set(x_154, 1, x_67);
lean::cnstr_set(x_154, 2, x_69);
lean::cnstr_set(x_154, 3, x_71);
lean::cnstr_set_scalar(x_154, sizeof(void*)*4, x_153);
x_155 = x_154;
if (lean::is_scalar(x_66)) {
 x_156 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_156 = x_66;
}
lean::cnstr_set(x_156, 0, x_155);
lean::cnstr_set(x_156, 1, x_60);
lean::cnstr_set(x_156, 2, x_62);
lean::cnstr_set(x_156, 3, x_64);
lean::cnstr_set_scalar(x_156, sizeof(void*)*4, x_127);
x_157 = x_156;
return x_157;
}
}
}
}
}
}
}
}
obj* l_rbnode_balance1___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_balance1___main___rarg), 2, 0);
return x_2;
}
}
obj* l_rbnode_balance1___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_balance1___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_balance1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_balance1___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbnode_balance1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_balance1___rarg), 2, 0);
return x_2;
}
}
obj* l_rbnode_balance1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_balance1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_balance2___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
x_6 = lean::cnstr_get(x_1, 3);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; uint8 x_23; obj* x_24; obj* x_25; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
x_12 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 3);
 x_14 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_0);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_1, 1);
x_17 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 3);
 x_19 = x_1;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_1);
 x_19 = lean::box(0);
}
x_20 = 0;
if (lean::is_scalar(x_19)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_19;
}
lean::cnstr_set(x_21, 0, x_6);
lean::cnstr_set(x_21, 1, x_15);
lean::cnstr_set(x_21, 2, x_17);
lean::cnstr_set(x_21, 3, x_6);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_20);
x_22 = x_21;
x_23 = 1;
if (lean::is_scalar(x_14)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_14;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_22);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_23);
x_25 = x_24;
return x_25;
}
else
{
obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_37; uint8 x_38; 
x_26 = lean::cnstr_get(x_0, 0);
x_28 = lean::cnstr_get(x_0, 1);
x_30 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_release(x_0, 3);
 x_32 = x_0;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_0);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_1, 1);
x_35 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_release(x_1, 3);
 x_37 = x_1;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_1);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*4);
if (x_38 == 0)
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_39 = lean::cnstr_get(x_6, 0);
x_41 = lean::cnstr_get(x_6, 1);
x_43 = lean::cnstr_get(x_6, 2);
x_45 = lean::cnstr_get(x_6, 3);
if (lean::is_exclusive(x_6)) {
 x_47 = x_6;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_6);
 x_47 = lean::box(0);
}
x_48 = 1;
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_26);
lean::cnstr_set(x_49, 1, x_28);
lean::cnstr_set(x_49, 2, x_30);
lean::cnstr_set(x_49, 3, x_4);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_48);
x_50 = x_49;
if (lean::is_scalar(x_37)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_37;
}
lean::cnstr_set(x_51, 0, x_39);
lean::cnstr_set(x_51, 1, x_41);
lean::cnstr_set(x_51, 2, x_43);
lean::cnstr_set(x_51, 3, x_45);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_48);
x_52 = x_51;
if (lean::is_scalar(x_32)) {
 x_53 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_53 = x_32;
}
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set(x_53, 1, x_33);
lean::cnstr_set(x_53, 2, x_35);
lean::cnstr_set(x_53, 3, x_52);
lean::cnstr_set_scalar(x_53, sizeof(void*)*4, x_38);
x_54 = x_53;
return x_54;
}
else
{
uint8 x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_55 = 0;
if (lean::is_scalar(x_37)) {
 x_56 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_56 = x_37;
}
lean::cnstr_set(x_56, 0, x_4);
lean::cnstr_set(x_56, 1, x_33);
lean::cnstr_set(x_56, 2, x_35);
lean::cnstr_set(x_56, 3, x_6);
lean::cnstr_set_scalar(x_56, sizeof(void*)*4, x_55);
x_57 = x_56;
if (lean::is_scalar(x_32)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_32;
}
lean::cnstr_set(x_58, 0, x_26);
lean::cnstr_set(x_58, 1, x_28);
lean::cnstr_set(x_58, 2, x_30);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_38);
x_59 = x_58;
return x_59;
}
}
}
else
{
obj* x_60; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_69; obj* x_71; obj* x_73; uint8 x_74; 
x_60 = lean::cnstr_get(x_0, 0);
x_62 = lean::cnstr_get(x_0, 1);
x_64 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_release(x_0, 3);
 x_66 = x_0;
} else {
 lean::inc(x_60);
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_0);
 x_66 = lean::box(0);
}
x_67 = lean::cnstr_get(x_1, 1);
x_69 = lean::cnstr_get(x_1, 2);
x_71 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_73 = x_1;
} else {
 lean::inc(x_67);
 lean::inc(x_69);
 lean::inc(x_71);
 lean::dec(x_1);
 x_73 = lean::box(0);
}
x_74 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*4);
if (x_74 == 0)
{
if (lean::obj_tag(x_71) == 0)
{
obj* x_75; obj* x_77; obj* x_79; obj* x_81; obj* x_83; uint8 x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_75 = lean::cnstr_get(x_4, 0);
x_77 = lean::cnstr_get(x_4, 1);
x_79 = lean::cnstr_get(x_4, 2);
x_81 = lean::cnstr_get(x_4, 3);
if (lean::is_exclusive(x_4)) {
 x_83 = x_4;
} else {
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::inc(x_81);
 lean::dec(x_4);
 x_83 = lean::box(0);
}
x_84 = 1;
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_60);
lean::cnstr_set(x_85, 1, x_62);
lean::cnstr_set(x_85, 2, x_64);
lean::cnstr_set(x_85, 3, x_75);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_84);
x_86 = x_85;
if (lean::is_scalar(x_73)) {
 x_87 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_87 = x_73;
}
lean::cnstr_set(x_87, 0, x_81);
lean::cnstr_set(x_87, 1, x_67);
lean::cnstr_set(x_87, 2, x_69);
lean::cnstr_set(x_87, 3, x_71);
lean::cnstr_set_scalar(x_87, sizeof(void*)*4, x_84);
x_88 = x_87;
if (lean::is_scalar(x_66)) {
 x_89 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_89 = x_66;
}
lean::cnstr_set(x_89, 0, x_86);
lean::cnstr_set(x_89, 1, x_77);
lean::cnstr_set(x_89, 2, x_79);
lean::cnstr_set(x_89, 3, x_88);
lean::cnstr_set_scalar(x_89, sizeof(void*)*4, x_74);
x_90 = x_89;
return x_90;
}
else
{
obj* x_91; obj* x_93; obj* x_95; obj* x_97; obj* x_99; uint8 x_100; 
x_91 = lean::cnstr_get(x_4, 0);
x_93 = lean::cnstr_get(x_4, 1);
x_95 = lean::cnstr_get(x_4, 2);
x_97 = lean::cnstr_get(x_4, 3);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 lean::cnstr_set(x_4, 2, lean::box(0));
 lean::cnstr_set(x_4, 3, lean::box(0));
 x_99 = x_4;
} else {
 lean::inc(x_91);
 lean::inc(x_93);
 lean::inc(x_95);
 lean::inc(x_97);
 lean::dec(x_4);
 x_99 = lean::box(0);
}
x_100 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*4);
if (x_100 == 0)
{
uint8 x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_101 = 1;
if (lean::is_scalar(x_99)) {
 x_102 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_102 = x_99;
}
lean::cnstr_set(x_102, 0, x_60);
lean::cnstr_set(x_102, 1, x_62);
lean::cnstr_set(x_102, 2, x_64);
lean::cnstr_set(x_102, 3, x_91);
lean::cnstr_set_scalar(x_102, sizeof(void*)*4, x_101);
x_103 = x_102;
if (lean::is_scalar(x_73)) {
 x_104 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_104 = x_73;
}
lean::cnstr_set(x_104, 0, x_97);
lean::cnstr_set(x_104, 1, x_67);
lean::cnstr_set(x_104, 2, x_69);
lean::cnstr_set(x_104, 3, x_71);
lean::cnstr_set_scalar(x_104, sizeof(void*)*4, x_101);
x_105 = x_104;
if (lean::is_scalar(x_66)) {
 x_106 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_106 = x_66;
}
lean::cnstr_set(x_106, 0, x_103);
lean::cnstr_set(x_106, 1, x_93);
lean::cnstr_set(x_106, 2, x_95);
lean::cnstr_set(x_106, 3, x_105);
lean::cnstr_set_scalar(x_106, sizeof(void*)*4, x_100);
x_107 = x_106;
return x_107;
}
else
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
if (lean::is_scalar(x_99)) {
 x_108 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_108 = x_99;
}
lean::cnstr_set(x_108, 0, x_60);
lean::cnstr_set(x_108, 1, x_62);
lean::cnstr_set(x_108, 2, x_64);
lean::cnstr_set(x_108, 3, x_91);
lean::cnstr_set_scalar(x_108, sizeof(void*)*4, x_100);
x_109 = x_108;
if (lean::is_scalar(x_73)) {
 x_110 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_110 = x_73;
}
lean::cnstr_set(x_110, 0, x_97);
lean::cnstr_set(x_110, 1, x_67);
lean::cnstr_set(x_110, 2, x_69);
lean::cnstr_set(x_110, 3, x_71);
lean::cnstr_set_scalar(x_110, sizeof(void*)*4, x_100);
x_111 = x_110;
if (lean::is_scalar(x_66)) {
 x_112 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_112 = x_66;
}
lean::cnstr_set(x_112, 0, x_109);
lean::cnstr_set(x_112, 1, x_93);
lean::cnstr_set(x_112, 2, x_95);
lean::cnstr_set(x_112, 3, x_111);
lean::cnstr_set_scalar(x_112, sizeof(void*)*4, x_74);
x_113 = x_112;
return x_113;
}
}
}
else
{
if (lean::obj_tag(x_71) == 0)
{
uint8 x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_114 = 0;
if (lean::is_scalar(x_73)) {
 x_115 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_115 = x_73;
}
lean::cnstr_set(x_115, 0, x_4);
lean::cnstr_set(x_115, 1, x_67);
lean::cnstr_set(x_115, 2, x_69);
lean::cnstr_set(x_115, 3, x_71);
lean::cnstr_set_scalar(x_115, sizeof(void*)*4, x_114);
x_116 = x_115;
if (lean::is_scalar(x_66)) {
 x_117 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_117 = x_66;
}
lean::cnstr_set(x_117, 0, x_60);
lean::cnstr_set(x_117, 1, x_62);
lean::cnstr_set(x_117, 2, x_64);
lean::cnstr_set(x_117, 3, x_116);
lean::cnstr_set_scalar(x_117, sizeof(void*)*4, x_74);
x_118 = x_117;
return x_118;
}
else
{
obj* x_119; obj* x_121; obj* x_123; obj* x_125; uint8 x_127; 
x_119 = lean::cnstr_get(x_4, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_4, 1);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_4, 2);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_4, 3);
lean::inc(x_125);
x_127 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*4);
if (x_127 == 0)
{
obj* x_133; obj* x_135; obj* x_137; obj* x_139; obj* x_141; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
lean::dec(x_123);
lean::dec(x_121);
lean::dec(x_119);
lean::dec(x_125);
lean::dec(x_66);
x_133 = lean::cnstr_get(x_71, 0);
x_135 = lean::cnstr_get(x_71, 1);
x_137 = lean::cnstr_get(x_71, 2);
x_139 = lean::cnstr_get(x_71, 3);
if (lean::is_exclusive(x_71)) {
 x_141 = x_71;
} else {
 lean::inc(x_133);
 lean::inc(x_135);
 lean::inc(x_137);
 lean::inc(x_139);
 lean::dec(x_71);
 x_141 = lean::box(0);
}
lean::inc(x_4);
if (lean::is_scalar(x_141)) {
 x_143 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_143 = x_141;
}
lean::cnstr_set(x_143, 0, x_60);
lean::cnstr_set(x_143, 1, x_62);
lean::cnstr_set(x_143, 2, x_64);
lean::cnstr_set(x_143, 3, x_4);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_144 = x_4;
} else {
 lean::dec(x_4);
 x_144 = lean::box(0);
}
lean::cnstr_set_scalar(x_143, sizeof(void*)*4, x_74);
x_145 = x_143;
if (lean::is_scalar(x_144)) {
 x_146 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_146 = x_144;
}
lean::cnstr_set(x_146, 0, x_133);
lean::cnstr_set(x_146, 1, x_135);
lean::cnstr_set(x_146, 2, x_137);
lean::cnstr_set(x_146, 3, x_139);
lean::cnstr_set_scalar(x_146, sizeof(void*)*4, x_74);
x_147 = x_146;
if (lean::is_scalar(x_73)) {
 x_148 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_148 = x_73;
}
lean::cnstr_set(x_148, 0, x_145);
lean::cnstr_set(x_148, 1, x_67);
lean::cnstr_set(x_148, 2, x_69);
lean::cnstr_set(x_148, 3, x_147);
lean::cnstr_set_scalar(x_148, sizeof(void*)*4, x_127);
x_149 = x_148;
return x_149;
}
else
{
obj* x_150; obj* x_151; obj* x_152; uint8 x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_150 = x_4;
} else {
 lean::dec(x_4);
 x_150 = lean::box(0);
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_119);
lean::cnstr_set(x_151, 1, x_121);
lean::cnstr_set(x_151, 2, x_123);
lean::cnstr_set(x_151, 3, x_125);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_127);
x_152 = x_151;
x_153 = 0;
if (lean::is_scalar(x_73)) {
 x_154 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_154 = x_73;
}
lean::cnstr_set(x_154, 0, x_152);
lean::cnstr_set(x_154, 1, x_67);
lean::cnstr_set(x_154, 2, x_69);
lean::cnstr_set(x_154, 3, x_71);
lean::cnstr_set_scalar(x_154, sizeof(void*)*4, x_153);
x_155 = x_154;
if (lean::is_scalar(x_66)) {
 x_156 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_156 = x_66;
}
lean::cnstr_set(x_156, 0, x_60);
lean::cnstr_set(x_156, 1, x_62);
lean::cnstr_set(x_156, 2, x_64);
lean::cnstr_set(x_156, 3, x_155);
lean::cnstr_set_scalar(x_156, sizeof(void*)*4, x_127);
x_157 = x_156;
return x_157;
}
}
}
}
}
}
}
}
obj* l_rbnode_balance2___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_balance2___main___rarg), 2, 0);
return x_2;
}
}
obj* l_rbnode_balance2___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_balance2___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_balance2___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_balance2___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbnode_balance2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_balance2___rarg), 2, 0);
return x_2;
}
}
obj* l_rbnode_balance2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_balance2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_rbnode_is__red___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
else
{
uint8 x_2; 
x_2 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
}
}
}
obj* l_rbnode_is__red___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_is__red___main___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_rbnode_is__red___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_rbnode_is__red___main___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_rbnode_is__red___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_is__red___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_rbnode_is__red___rarg(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_rbnode_is__red___main___rarg(x_0);
return x_1;
}
}
obj* l_rbnode_is__red(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_is__red___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_rbnode_is__red___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_rbnode_is__red___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_rbnode_is__red___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_is__red(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_ins___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_rbnode_ins___main___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_rbnode_ins___main___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_rbnode_is__red___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_rbnode_ins___main___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_rbnode_ins___main___rarg(x_0, x_45, x_2, x_3);
x_71 = l_rbnode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_rbnode_is__red___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_rbnode_ins___main___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_rbnode_ins___main___rarg(x_0, x_39, x_2, x_3);
x_80 = l_rbnode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_rbnode_ins___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_ins___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbnode_ins(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_ins___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_set__black___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_0;
}
else
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_0, 2);
x_7 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_9 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_0);
 x_9 = lean::box(0);
}
x_10 = 1;
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_3);
lean::cnstr_set(x_11, 2, x_5);
lean::cnstr_set(x_11, 3, x_7);
lean::cnstr_set_scalar(x_11, sizeof(void*)*4, x_10);
x_12 = x_11;
return x_12;
}
}
}
obj* l_rbnode_set__black___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_set__black___main___rarg), 1, 0);
return x_2;
}
}
obj* l_rbnode_set__black___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_set__black___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_set__black___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_set__black___main___rarg(x_0);
return x_1;
}
}
obj* l_rbnode_set__black(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_set__black___rarg), 1, 0);
return x_2;
}
}
obj* l_rbnode_set__black___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_set__black(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_rbnode_is__red___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_45, x_2, x_3);
x_71 = l_rbnode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_rbnode_is__red___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_39, x_2, x_3);
x_80 = l_rbnode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbnode_insert___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbnode_insert___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_rbnode_ins___main___at_rbnode_insert___spec__2___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_rbnode_ins___main___at_rbnode_insert___spec__2___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_rbnode_is__red___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_rbnode_ins___main___at_rbnode_insert___spec__2___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_rbnode_ins___main___at_rbnode_insert___spec__2___rarg(x_0, x_45, x_2, x_3);
x_71 = l_rbnode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_rbnode_is__red___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_rbnode_ins___main___at_rbnode_insert___spec__2___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_rbnode_ins___main___at_rbnode_insert___spec__2___rarg(x_0, x_39, x_2, x_3);
x_80 = l_rbnode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbnode_insert___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbnode_insert___spec__2___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_rbnode_is__red___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_rbnode_insert___spec__2___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
}
}
}
obj* l_rbnode_insert(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbnode_insert___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_rbnode_insert___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbnode_insert___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_rbnode_insert___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_find__core___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; 
lean::dec(x_0);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_24; uint8 x_25; 
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_8, x_2);
x_25 = lean::unbox(x_24);
if (x_25 == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_8);
lean::cnstr_set(x_29, 1, x_10);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
else
{
lean::dec(x_8);
lean::dec(x_10);
x_1 = x_12;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_12);
x_1 = x_6;
goto _start;
}
}
}
}
obj* l_rbnode_find__core___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find__core___main___rarg), 3, 0);
return x_3;
}
}
obj* l_rbnode_find__core___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_find__core___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbnode_find__core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find__core___rarg), 3, 0);
return x_3;
}
}
obj* l_rbnode_find__core___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_find___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 3);
lean::inc(x_13);
lean::dec(x_2);
lean::inc(x_9);
lean::inc(x_3);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_3, x_9);
x_20 = lean::unbox(x_19);
if (x_20 == 0)
{
obj* x_24; uint8 x_25; 
lean::dec(x_7);
lean::inc(x_3);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_9, x_3);
x_25 = lean::unbox(x_24);
if (x_25 == 0)
{
obj* x_29; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_13);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_11);
return x_29;
}
else
{
lean::dec(x_11);
x_1 = x_0;
x_2 = x_13;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_13);
x_1 = x_0;
x_2 = x_7;
goto _start;
}
}
}
}
obj* l_rbnode_find___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_rbnode_find___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_find___main___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_rbnode_find___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_find___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_find___main___rarg(x_0, lean::box(0), x_2, x_3);
return x_4;
}
}
obj* l_rbnode_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_rbnode_find___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_find___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_rbnode_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_lower__bound___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_25; uint8 x_26; 
lean::dec(x_3);
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_8, x_2);
x_26 = lean::unbox(x_25);
if (x_26 == 0)
{
obj* x_30; obj* x_31; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_8);
lean::cnstr_set(x_30, 1, x_10);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
return x_31;
}
else
{
obj* x_32; obj* x_33; 
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_8);
lean::cnstr_set(x_32, 1, x_10);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_1 = x_12;
x_3 = x_33;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_12);
x_1 = x_6;
goto _start;
}
}
}
}
obj* l_rbnode_lower__bound___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_lower__bound___main___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_lower__bound___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_lower__bound___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_lower__bound___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_lower__bound___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbnode_lower__bound(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_lower__bound___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_lower__bound___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_lower__bound(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_rbmap() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_mk__rbmap(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_mk__rbmap___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_mk__rbmap(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_depth___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_depth___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_depth(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_depth___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_rbmap_depth___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_depth___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_depth___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_depth(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_fold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_fold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_fold___main___rarg), 3, 0);
return x_4;
}
}
obj* l_rbmap_fold___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbmap_fold___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_rbmap_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_fold(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_fold___rarg), 3, 0);
return x_4;
}
}
obj* l_rbmap_fold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbmap_fold(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_rbmap_rev__fold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_rev__fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_rev__fold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_rev__fold___main___rarg), 3, 0);
return x_4;
}
}
obj* l_rbmap_rev__fold___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbmap_rev__fold___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_rbmap_rev__fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_rev__fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_rev__fold(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_rev__fold___rarg), 3, 0);
return x_4;
}
}
obj* l_rbmap_rev__fold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbmap_rev__fold(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_rbmap_mfold___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_mfold___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_mfold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_mfold___main___rarg), 4, 0);
return x_5;
}
}
obj* l_rbmap_mfold___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_rbmap_mfold___main(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_rbmap_mfold___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_mfold___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_mfold(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_mfold___rarg), 4, 0);
return x_5;
}
}
obj* l_rbmap_mfold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_rbmap_mfold(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 4);
lean::inc(x_9);
lean::inc(x_1);
x_12 = lean::apply_2(x_1, x_2, x_3);
x_13 = lean::cnstr_get(x_7, 1);
lean::inc(x_13);
lean::dec(x_7);
x_16 = lean::box(0);
x_17 = lean::apply_2(x_13, lean::box(0), x_16);
x_18 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_12, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg), 4, 3);
lean::closure_set(x_19, 0, x_0);
lean::closure_set(x_19, 1, x_1);
lean::closure_set(x_19, 2, x_4);
x_20 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_18, x_19);
return x_20;
}
}
obj* l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_8; obj* x_11; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_2(x_8, lean::box(0), x_3);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_25; obj* x_27; obj* x_28; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_2, 2);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_2, 3);
lean::inc(x_18);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::inc(x_1);
lean::inc(x_0);
x_25 = l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg(x_0, x_1, x_12, x_3);
lean::inc(x_21);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg___lambda__1___boxed), 7, 6);
lean::closure_set(x_27, 0, x_0);
lean::closure_set(x_27, 1, x_1);
lean::closure_set(x_27, 2, x_14);
lean::closure_set(x_27, 3, x_16);
lean::closure_set(x_27, 4, x_18);
lean::closure_set(x_27, 5, x_21);
x_28 = lean::apply_4(x_21, lean::box(0), lean::box(0), x_25, x_27);
return x_28;
}
}
}
obj* l_rbnode_mfold___main___at_rbmap_mfor___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg), 4, 0);
return x_4;
}
}
obj* l_rbmap_mfor___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_mfor(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_mfor___rarg), 3, 0);
return x_5;
}
}
obj* l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
return x_7;
}
}
obj* l_rbnode_mfold___main___at_rbmap_mfor___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_mfold___main___at_rbmap_mfor___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_rbmap_mfor___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_rbmap_mfor(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
uint8 l_rbmap_empty___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
}
}
obj* l_rbmap_empty___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_empty___main___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_rbmap_empty___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_rbmap_empty___main___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_rbmap_empty___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_empty___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_rbmap_empty___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
}
}
obj* l_rbmap_empty(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_empty___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_rbmap_empty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_rbmap_empty___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_rbmap_empty___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_empty(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_13; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 3);
lean::inc(x_8);
lean::dec(x_0);
x_11 = l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___rarg(x_8, x_1);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_6);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_0 = x_2;
x_1 = x_13;
goto _start;
}
}
}
obj* l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_rbmap_to__list___main___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_to__list___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_to__list___main___rarg), 1, 0);
return x_3;
}
}
obj* l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_to__list___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_to__list___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_to__list___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbmap_to__list___main___rarg(x_0);
return x_1;
}
}
obj* l_rbmap_to__list(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_to__list___rarg), 1, 0);
return x_3;
}
}
obj* l_rbmap_to__list___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_to__list(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_min___main___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_min___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_rbmap_min___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_min___main___rarg), 1, 0);
return x_3;
}
}
obj* l_rbmap_min___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_min___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_min___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_min___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_rbmap_min(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_min___rarg), 1, 0);
return x_3;
}
}
obj* l_rbmap_min___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_min(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_max___main___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_max___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_rbmap_max___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_max___main___rarg), 1, 0);
return x_3;
}
}
obj* l_rbmap_max___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_max___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_max___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_max___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_rbmap_max(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_max___rarg), 1, 0);
return x_3;
}
}
obj* l_rbmap_max___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_max(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(obj* x_0, obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
if (x_2 == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = l_string_join___closed__1;
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_14; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_33; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
lean::dec(x_7);
lean::inc(x_1);
lean::inc(x_0);
x_19 = l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(x_0, x_1, x_2, x_9);
x_20 = lean::apply_1(x_0, x_12);
x_21 = l_prod_has__repr___rarg___closed__1;
x_22 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_24 = l_list_repr__aux___main___rarg___closed__1;
x_25 = lean::string_append(x_22, x_24);
x_26 = lean::apply_1(x_1, x_14);
x_27 = lean::string_append(x_25, x_26);
lean::dec(x_26);
x_29 = l_option_has__repr___rarg___closed__3;
x_30 = lean::string_append(x_27, x_29);
x_31 = lean::string_append(x_24, x_30);
lean::dec(x_30);
x_33 = lean::string_append(x_31, x_19);
lean::dec(x_19);
return x_33;
}
}
else
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_37; 
lean::dec(x_1);
lean::dec(x_0);
x_37 = l_string_join___closed__1;
return x_37;
}
else
{
obj* x_38; obj* x_40; obj* x_43; obj* x_45; uint8 x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
x_38 = lean::cnstr_get(x_3, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_3, 1);
lean::inc(x_40);
lean::dec(x_3);
x_43 = lean::cnstr_get(x_38, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_38, 1);
lean::inc(x_45);
lean::dec(x_38);
x_48 = 0;
lean::inc(x_1);
lean::inc(x_0);
x_51 = l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(x_0, x_1, x_48, x_40);
x_52 = lean::apply_1(x_0, x_43);
x_53 = l_prod_has__repr___rarg___closed__1;
x_54 = lean::string_append(x_53, x_52);
lean::dec(x_52);
x_56 = l_list_repr__aux___main___rarg___closed__1;
x_57 = lean::string_append(x_54, x_56);
x_58 = lean::apply_1(x_1, x_45);
x_59 = lean::string_append(x_57, x_58);
lean::dec(x_58);
x_61 = l_option_has__repr___rarg___closed__3;
x_62 = lean::string_append(x_59, x_61);
x_63 = lean::string_append(x_62, x_51);
lean::dec(x_51);
return x_63;
}
}
}
}
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_list_repr___main___at_rbmap_has__repr___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_list_repr___main___rarg___closed__1;
return x_5;
}
else
{
uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
x_6 = 1;
x_7 = l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(x_0, x_1, x_6, x_2);
x_8 = l_list_repr___main___rarg___closed__2;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_11 = l_list_repr___main___rarg___closed__3;
x_12 = lean::string_append(x_9, x_11);
return x_12;
}
}
}
obj* l_list_repr___main___at_rbmap_has__repr___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repr___main___at_rbmap_has__repr___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* _init_l_rbmap_has__repr___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("rbmap_of ");
return x_0;
}
}
obj* l_rbmap_has__repr___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_rbmap_to__list___main___rarg(x_2);
x_4 = l_list_repr___main___at_rbmap_has__repr___spec__1___rarg(x_0, x_1, x_3);
x_5 = l_rbmap_has__repr___rarg___closed__1;
x_6 = lean::string_append(x_5, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l_rbmap_has__repr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_has__repr___rarg), 3, 0);
return x_3;
}
}
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
x_5 = l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(x_0, x_1, x_4, x_3);
return x_5;
}
}
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_repr__aux___main___at_rbmap_has__repr___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_repr___main___at_rbmap_has__repr___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_repr___main___at_rbmap_has__repr___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_has__repr___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_has__repr(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_rbnode_is__red___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_45, x_2, x_3);
x_71 = l_rbnode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_rbnode_is__red___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_39, x_2, x_3);
x_80 = l_rbnode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_rbnode_ins___main___at_rbmap_insert___main___spec__3___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_rbnode_ins___main___at_rbmap_insert___main___spec__3___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_rbnode_is__red___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_rbnode_ins___main___at_rbmap_insert___main___spec__3___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_rbnode_ins___main___at_rbmap_insert___main___spec__3___rarg(x_0, x_45, x_2, x_3);
x_71 = l_rbnode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_rbnode_is__red___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_rbnode_ins___main___at_rbmap_insert___main___spec__3___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_rbnode_ins___main___at_rbmap_insert___main___spec__3___rarg(x_0, x_39, x_2, x_3);
x_80 = l_rbnode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbmap_insert___main___spec__3___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_insert___at_rbmap_insert___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_rbnode_is__red___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_rbmap_insert___main___spec__3___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
}
}
}
obj* l_rbnode_insert___at_rbmap_insert___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_rbmap_insert___main___spec__1___rarg), 4, 0);
return x_3;
}
}
obj* l_rbmap_insert___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_rbmap_insert___main___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_rbmap_insert___main___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_rbmap_insert___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_rbmap_insert___main___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_rbmap_insert___main___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___rarg), 4, 0);
return x_3;
}
}
obj* l_rbmap_insert___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_rbnode_is__red___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_45, x_2, x_3);
x_71 = l_rbnode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_rbnode_is__red___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_39, x_2, x_3);
x_80 = l_rbnode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__4___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__4___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_rbnode_is__red___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__4___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__4___rarg(x_0, x_45, x_2, x_3);
x_71 = l_rbnode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_rbnode_is__red___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__4___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__4___rarg(x_0, x_39, x_2, x_3);
x_80 = l_rbnode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbmap_of__list___main___spec__4___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_insert___at_rbmap_of__list___main___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_rbnode_is__red___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__4___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
}
}
}
obj* l_rbnode_insert___at_rbmap_of__list___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_rbmap_of__list___main___spec__2___rarg), 4, 0);
return x_3;
}
}
obj* l_rbmap_insert___main___at_rbmap_of__list___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_rbmap_of__list___main___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbmap_of__list___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_rbmap_of__list___main___spec__1___rarg), 4, 0);
return x_3;
}
}
obj* l_rbmap_of__list___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_15; obj* x_16; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
lean::inc(x_0);
x_15 = l_rbmap_of__list___main___rarg(x_0, x_6);
x_16 = l_rbnode_insert___at_rbmap_of__list___main___spec__2___rarg(x_0, x_15, x_9, x_11);
return x_16;
}
}
}
obj* l_rbmap_of__list___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_of__list___main___rarg), 2, 0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_rbmap_of__list___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_rbmap_of__list___main___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_rbmap_of__list___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_rbmap_of__list___main___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_of__list___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_of__list___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_of__list___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_of__list___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_of__list(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_of__list___rarg), 2, 0);
return x_3;
}
}
obj* l_rbmap_of__list___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_of__list(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; 
lean::dec(x_0);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_24; uint8 x_25; 
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_8, x_2);
x_25 = lean::unbox(x_24);
if (x_25 == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_8);
lean::cnstr_set(x_29, 1, x_10);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
else
{
lean::dec(x_8);
lean::dec(x_10);
x_1 = x_12;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_12);
x_1 = x_6;
goto _start;
}
}
}
}
obj* l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___rarg), 3, 0);
return x_3;
}
}
obj* l_rbmap_find__core___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find__core___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find__core___main___rarg), 3, 0);
return x_3;
}
}
obj* l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_find__core___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_find__core___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_find__core___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find__core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find__core___rarg), 3, 0);
return x_3;
}
}
obj* l_rbmap_find__core___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_find__core(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 3);
lean::inc(x_13);
lean::dec(x_2);
lean::inc(x_9);
lean::inc(x_3);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_3, x_9);
x_20 = lean::unbox(x_19);
if (x_20 == 0)
{
obj* x_24; uint8 x_25; 
lean::dec(x_7);
lean::inc(x_3);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_9, x_3);
x_25 = lean::unbox(x_24);
if (x_25 == 0)
{
obj* x_29; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_13);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_11);
return x_29;
}
else
{
lean::dec(x_11);
x_1 = x_0;
x_2 = x_13;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_13);
x_1 = x_0;
x_2 = x_7;
goto _start;
}
}
}
}
obj* l_rbnode_find___main___at_rbmap_find___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_rbmap_find___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___rarg), 3, 0);
return x_3;
}
}
obj* l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_rbnode_find___main___at_rbmap_find___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_rbmap_find___main___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_find___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_find___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_find___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___rarg), 3, 0);
return x_3;
}
}
obj* l_rbmap_find___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_find(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_25; uint8 x_26; 
lean::dec(x_3);
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_8, x_2);
x_26 = lean::unbox(x_25);
if (x_26 == 0)
{
obj* x_30; obj* x_31; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_8);
lean::cnstr_set(x_30, 1, x_10);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
return x_31;
}
else
{
obj* x_32; obj* x_33; 
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_8);
lean::cnstr_set(x_32, 1, x_10);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_1 = x_12;
x_3 = x_33;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_12);
x_1 = x_6;
goto _start;
}
}
}
}
obj* l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1___rarg), 4, 0);
return x_3;
}
}
obj* l_rbmap_lower__bound___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_lower__bound___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_lower__bound___main___rarg), 3, 0);
return x_3;
}
}
obj* l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_lower__bound___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_lower__bound___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_lower__bound___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_lower__bound___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_lower__bound(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_lower__bound___rarg), 3, 0);
return x_3;
}
}
obj* l_rbmap_lower__bound___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_lower__bound(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_find___main___at_rbmap_contains___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 3);
lean::inc(x_13);
lean::dec(x_2);
lean::inc(x_9);
lean::inc(x_3);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_3, x_9);
x_20 = lean::unbox(x_19);
if (x_20 == 0)
{
obj* x_24; uint8 x_25; 
lean::dec(x_7);
lean::inc(x_3);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_9, x_3);
x_25 = lean::unbox(x_24);
if (x_25 == 0)
{
obj* x_29; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_13);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_11);
return x_29;
}
else
{
lean::dec(x_11);
x_1 = x_0;
x_2 = x_13;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_13);
x_1 = x_0;
x_2 = x_7;
goto _start;
}
}
}
}
obj* l_rbnode_find___main___at_rbmap_contains___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_rbmap_contains___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_rbmap_find___main___at_rbmap_contains___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find___main___at_rbmap_contains___spec__2___rarg(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find___main___at_rbmap_contains___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_rbmap_contains___spec__1___rarg), 3, 0);
return x_3;
}
}
uint8 l_rbmap_contains___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_rbnode_find___main___at_rbmap_contains___spec__2___rarg(x_0, lean::box(0), x_1, x_2);
x_4 = l_option_is__some___main___rarg(x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_rbmap_contains(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_contains___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_rbnode_find___main___at_rbmap_contains___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_find___main___at_rbmap_contains___spec__2___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_rbnode_find___main___at_rbmap_contains___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_rbmap_contains___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_rbmap_contains___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_find___main___at_rbmap_contains___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_contains___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_rbmap_contains___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_rbmap_contains___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_contains(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_rbnode_is__red___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_45, x_2, x_3);
x_71 = l_rbnode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_rbnode_is__red___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_39, x_2, x_3);
x_80 = l_rbnode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_rbnode_ins___main___at_rbmap_from__list___spec__4___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_rbnode_ins___main___at_rbmap_from__list___spec__4___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_rbnode_is__red___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_rbnode_ins___main___at_rbmap_from__list___spec__4___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_rbnode_ins___main___at_rbmap_from__list___spec__4___rarg(x_0, x_45, x_2, x_3);
x_71 = l_rbnode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_rbnode_is__red___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_rbnode_ins___main___at_rbmap_from__list___spec__4___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_rbnode_ins___main___at_rbmap_from__list___spec__4___rarg(x_0, x_39, x_2, x_3);
x_80 = l_rbnode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbmap_from__list___spec__4___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_insert___at_rbmap_from__list___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_rbnode_is__red___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_rbmap_from__list___spec__4___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
}
}
}
obj* l_rbnode_insert___at_rbmap_from__list___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_rbmap_from__list___spec__2___rarg), 4, 0);
return x_3;
}
}
obj* l_rbmap_insert___main___at_rbmap_from__list___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_rbmap_from__list___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbmap_from__list___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_rbmap_from__list___spec__1___rarg), 4, 0);
return x_3;
}
}
obj* l_list_foldl___main___at_rbmap_from__list___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_15; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
lean::inc(x_0);
x_15 = l_rbnode_insert___at_rbmap_from__list___spec__2___rarg(x_0, x_1, x_9, x_11);
x_1 = x_15;
x_2 = x_6;
goto _start;
}
}
}
obj* l_list_foldl___main___at_rbmap_from__list___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldl___main___at_rbmap_from__list___spec__5___rarg), 3, 0);
return x_3;
}
}
obj* l_rbmap_from__list___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_list_foldl___main___at_rbmap_from__list___spec__5___rarg(x_2, x_3, x_0);
return x_4;
}
}
obj* l_rbmap_from__list(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_rbmap_from__list___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_rbmap_from__list___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_rbmap_from__list___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_rbmap_from__list___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_rbmap_from__list___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_rbmap_from__list___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_foldl___main___at_rbmap_from__list___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_foldl___main___at_rbmap_from__list___spec__5(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_from__list___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_from__list___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_rbmap_from__list___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_from__list(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_all___main___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_all___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_rbmap_all___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_all___main___rarg), 2, 0);
return x_3;
}
}
obj* l_rbmap_all___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_all___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_all___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_all___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_rbmap_all(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_all___rarg), 2, 0);
return x_4;
}
}
obj* l_rbmap_all___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbmap_all(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_rbmap_any___main___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_any___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_rbmap_any___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_any___main___rarg), 2, 0);
return x_3;
}
}
obj* l_rbmap_any___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_any___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_any___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_any___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_rbmap_any(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_any___rarg), 2, 0);
return x_4;
}
}
obj* l_rbmap_any___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbmap_any(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_rbnode_is__red___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_45, x_2, x_3);
x_71 = l_rbnode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_rbnode_is__red___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_39, x_2, x_3);
x_80 = l_rbnode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbmap__of___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbmap__of___spec__4___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbmap__of___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_rbnode_ins___main___at_rbmap__of___spec__5___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_rbnode_ins___main___at_rbmap__of___spec__5___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_rbnode_is__red___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_rbnode_ins___main___at_rbmap__of___spec__5___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_rbnode_ins___main___at_rbmap__of___spec__5___rarg(x_0, x_45, x_2, x_3);
x_71 = l_rbnode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_rbnode_is__red___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_rbnode_ins___main___at_rbmap__of___spec__5___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_rbnode_ins___main___at_rbmap__of___spec__5___rarg(x_0, x_39, x_2, x_3);
x_80 = l_rbnode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbmap__of___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbmap__of___spec__5___rarg), 4, 0);
return x_3;
}
}
obj* l_rbnode_insert___at_rbmap__of___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_rbnode_is__red___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_rbmap__of___spec__5___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
}
}
}
obj* l_rbnode_insert___at_rbmap__of___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_rbmap__of___spec__3___rarg), 4, 0);
return x_3;
}
}
obj* l_rbmap_insert___main___at_rbmap__of___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_rbmap__of___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbmap__of___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_rbmap__of___spec__2___rarg), 4, 0);
return x_3;
}
}
obj* l_list_foldl___main___at_rbmap__of___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_15; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
lean::inc(x_0);
x_15 = l_rbnode_insert___at_rbmap__of___spec__3___rarg(x_0, x_1, x_9, x_11);
x_1 = x_15;
x_2 = x_6;
goto _start;
}
}
}
obj* l_list_foldl___main___at_rbmap__of___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldl___main___at_rbmap__of___spec__6___rarg), 3, 0);
return x_3;
}
}
obj* l_rbmap_from__list___at_rbmap__of___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_list_foldl___main___at_rbmap__of___spec__6___rarg(x_2, x_3, x_0);
return x_4;
}
}
obj* l_rbmap_from__list___at_rbmap__of___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_rbmap__of___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_rbmap__of___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_from__list___at_rbmap__of___spec__1___rarg(x_0, lean::box(0), x_2);
return x_3;
}
}
obj* l_rbmap__of(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap__of___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_rbnode_ins___main___at_rbmap__of___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_rbmap__of___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbmap__of___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_rbmap__of___spec__5(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_rbmap__of___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_rbmap__of___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_rbmap__of___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_rbmap__of___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_foldl___main___at_rbmap__of___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_foldl___main___at_rbmap__of___spec__6(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_from__list___at_rbmap__of___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_from__list___at_rbmap__of___spec__1___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_rbmap_from__list___at_rbmap__of___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_from__list___at_rbmap__of___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap__of___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap__of___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_rbmap__of___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap__of(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
void initialize_init_data_ordering_basic();
void initialize_init_coe();
void initialize_init_data_option_basic();
static bool _G_initialized = false;
void initialize_init_data_rbmap_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_ordering_basic();
 initialize_init_coe();
 initialize_init_data_option_basic();
 l_rbmap = _init_l_rbmap();
lean::mark_persistent(l_rbmap);
 l_rbmap_has__repr___rarg___closed__1 = _init_l_rbmap_has__repr___rarg___closed__1();
lean::mark_persistent(l_rbmap_has__repr___rarg___closed__1);
}
