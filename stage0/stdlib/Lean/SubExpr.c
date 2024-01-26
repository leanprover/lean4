// Lean compiler output
// Module: Lean.SubExpr
// Imports: Init Lean.Meta.Basic Lean.Data.Json Lean.Data.RBMap
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_Lean_SubExpr_Pos_push___closed__3;
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
lean_object* l_List_join___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonMVarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___at_Lean_SubExpr_Pos_all___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instToJsonPos___lambda__1(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_tail___closed__2;
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_all(lean_object*, lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_toJsonGoalLocation____x40_Lean_SubExpr___hyg_1606____closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_SubExpr_bindingBody_x21___spec__1(lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_tail(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_instToStringPos___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppFn(lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__7;
static lean_object* l_Lean_SubExpr_Pos_instOrdPos___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_fromString_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___boxed(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Array_push___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instInhabitedPos;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_bindingBody_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushProj___boxed(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_fromString_x3f___closed__1;
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldr___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_ofArray___boxed(lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_SubExpr_Pos_fromString_x3f___spec__1(size_t, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_append___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetBody(lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2;
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonFVarId___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742_(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_push___closed__1;
static lean_object* l_Lean_instInhabitedSubExpr___closed__1;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__18;
LEAN_EXPORT uint8_t l_Lean_SubExpr_isRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonGoalsLocation;
static lean_object* l_Lean_SubExpr_Pos_tail___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instOrdPos;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__16;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instReprPos(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedJson;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__1;
static lean_object* l_Lean_SubExpr_instFromJsonGoalLocation___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingBody___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instToJsonPos;
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instToStringPos;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instFromJsonPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_all___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_maxChildren;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instFromJsonPos(lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__15;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_toJsonGoalsLocation____x40_Lean_SubExpr___hyg_1842_(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_SubExpr_Pos_ofArray___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_all___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_toArray___closed__1;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_SubExpr_bindingBody_x21___closed__3;
static lean_object* l_Lean_SubExpr_instFromJsonFVarId___closed__4;
lean_object* l_panic___at_String_toNat_x21___spec__1(lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__12;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_push___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM(lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_instReprPos___closed__3;
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_instFromJsonFVarId___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_typeCoord;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__6;
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonGoalLocation;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetVarType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingDomain___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_SubExpr_Pos_fromString_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1___closed__2;
static lean_object* l_Lean_SubExpr_bindingDomain_x21___closed__1;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNthBindingDomain(lean_object*, lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__9;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__10;
static lean_object* l_Lean_SubExpr_Pos_instReprPos___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_asNat___boxed(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_append___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_root;
static lean_object* l_Lean_SubExpr_instFromJsonFVarId___closed__2;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__4;
static lean_object* l_Lean_SubExpr_Pos_depth___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetValue___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_SubExpr_Pos_tail___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_head___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_head___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetBody___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingDomain(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instEmptyCollectionPos;
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____boxed(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_toJsonGoalLocation____x40_Lean_SubExpr___hyg_1606_(lean_object*);
lean_object* l_instOrdNat___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNthBindingBody(lean_object*, lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_fromString_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetVarType(lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_ofArray(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_instReprPos___closed__2;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppFn___boxed(lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__14;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_push(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_instDecidableEqPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_asNat(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_typeCoord___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_head(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____spec__2___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__8;
static lean_object* l_Lean_SubExpr_Pos_toString___closed__1;
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_isRoot(lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__3;
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_head___closed__2;
LEAN_EXPORT lean_object* l_Lean_SubExpr_bindingDomain_x21(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_fromString_x3f___closed__2;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__17;
static lean_object* l_Lean_SubExpr_bindingDomain_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingBody(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_bindingBody_x21___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354_(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_head___closed__3;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__5;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_append(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
static lean_object* l_Lean_SubExpr_instToJsonGoalsLocation___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_mkRoot(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_toArray___closed__2;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonMVarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation;
lean_object* l_Except_orElseLazy___rarg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedSubExpr;
static lean_object* l_Lean_instInhabitedSubExpr___closed__2;
static lean_object* l_Lean_SubExpr_Pos_push___closed__2;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__2;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_SubExpr_Pos_toString___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonFVarId___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instReprPos___boxed(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushProj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_SubExpr_Pos_instToJsonPos___closed__2;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_isRoot___boxed(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryFn(lean_object*, lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__13;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__9;
lean_object* l_List_redLength___rarg(lean_object*);
static lean_object* l_Lean_SubExpr_instToJsonGoalLocation___closed__1;
static lean_object* l_Lean_SubExpr_instFromJsonFVarId___closed__3;
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_SubExpr_Pos_ofArray___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_isRoot___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonGoalLocation;
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonFVarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonFVarId(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instDecidableEqPos___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_head___closed__1;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_MetavarContext_MkBinding_instToStringException___spec__2(lean_object*);
static lean_object* l_Lean_SubExpr_Pos_fromString_x21___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_SubExpr_Pos_instToJsonPos___closed__1;
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetValue(lean_object*);
lean_object* l_String_splitOn(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM(lean_object*);
static lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__11;
static lean_object* _init_l_Lean_SubExpr_Pos_maxChildren() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(4u);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_typeCoord___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SubExpr_Pos_maxChildren;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_typeCoord() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_Pos_typeCoord___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_asNat(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_asNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_asNat(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_root() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instInhabitedPos() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_Pos_root;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_isRoot(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_SubExpr_Pos_maxChildren;
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_isRoot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_SubExpr_Pos_isRoot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_head___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.SubExpr", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_head___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.SubExpr.Pos.head", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_head___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("already at top", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_head___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_SubExpr_Pos_head___closed__1;
x_2 = l_Lean_SubExpr_Pos_head___closed__2;
x_3 = lean_unsigned_to_nat(42u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_SubExpr_Pos_head___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_head(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_SubExpr_Pos_maxChildren;
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_nat_mod(x_1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_SubExpr_Pos_head___closed__4;
x_6 = l_panic___at_String_toNat_x21___spec__1(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_head___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_head(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_SubExpr_Pos_tail___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_SubExpr_Pos_instInhabitedPos;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_tail___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.SubExpr.Pos.tail", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_tail___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_SubExpr_Pos_head___closed__1;
x_2 = l_Lean_SubExpr_Pos_tail___closed__1;
x_3 = lean_unsigned_to_nat(46u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_SubExpr_Pos_head___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_tail(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_SubExpr_Pos_maxChildren;
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_SubExpr_Pos_head(x_1);
x_5 = lean_nat_sub(x_1, x_4);
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_nat_div(x_5, x_2);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = l_Lean_SubExpr_Pos_tail___closed__2;
x_8 = l_panic___at_Lean_SubExpr_Pos_tail___spec__1(x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_push___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid coordinate ", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_push___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_push___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.SubExpr.Pos.push", 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_push(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_SubExpr_Pos_maxChildren;
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_nat_mul(x_1, x_3);
x_6 = lean_nat_add(x_5, x_2);
lean_dec(x_2);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = l_Nat_repr(x_2);
x_8 = l_Lean_SubExpr_Pos_push___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_SubExpr_Pos_push___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_SubExpr_Pos_head___closed__1;
x_13 = l_Lean_SubExpr_Pos_push___closed__3;
x_14 = lean_unsigned_to_nat(50u);
x_15 = lean_unsigned_to_nat(27u);
x_16 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_12, x_13, x_14, x_15, x_11);
lean_dec(x_11);
x_17 = l_panic___at_Lean_SubExpr_Pos_tail___spec__1(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_push___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_SubExpr_Pos_maxChildren;
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_3);
x_6 = l_Lean_SubExpr_Pos_tail(x_3);
lean_inc(x_1);
x_7 = l_Lean_SubExpr_Pos_foldl___rarg(x_1, x_2, x_6);
x_8 = l_Lean_SubExpr_Pos_head(x_3);
lean_dec(x_3);
x_9 = lean_apply_2(x_1, x_7, x_8);
return x_9;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldl___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SubExpr_Pos_foldl___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_SubExpr_Pos_maxChildren;
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_6 = l_Lean_SubExpr_Pos_tail(x_2);
x_7 = l_Lean_SubExpr_Pos_head(x_2);
lean_dec(x_2);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_7, x_3);
x_2 = x_6;
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldr___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_SubExpr_Pos_head(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_SubExpr_Pos_maxChildren;
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_6);
x_10 = l_Lean_SubExpr_Pos_tail(x_6);
lean_inc(x_4);
x_11 = l_Lean_SubExpr_Pos_foldlM___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldlM___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_4);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_4);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_2(x_15, lean_box(0), x_5);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldlM___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SubExpr_Pos_foldlM___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_SubExpr_Pos_foldlM___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_SubExpr_Pos_maxChildren;
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l_Lean_SubExpr_Pos_head(x_3);
lean_inc(x_2);
x_9 = lean_apply_2(x_2, x_8, x_4);
x_10 = l_Lean_SubExpr_Pos_tail(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldrM___rarg), 4, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_10);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldrM___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_depth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_depth___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_SubExpr_Pos_depth___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_SubExpr_Pos_foldr___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SubExpr_Pos_depth___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___at_Lean_SubExpr_Pos_all___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_SubExpr_Pos_maxChildren;
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_SubExpr_Pos_head(x_2);
lean_inc(x_1);
x_7 = lean_apply_2(x_1, x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_SubExpr_Pos_tail(x_2);
x_2 = x_10;
x_3 = x_9;
goto _start;
}
}
else
{
lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_all___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_all(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_all___lambda__1), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_box(0);
x_5 = l_Lean_SubExpr_Pos_foldrM___at_Lean_SubExpr_Pos_all___spec__1(x_3, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 1;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_all___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_SubExpr_Pos_all(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_append___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_push___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_SubExpr_Pos_append___closed__1;
x_4 = l_Lean_SubExpr_Pos_foldl___rarg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_append___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SubExpr_Pos_append(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_SubExpr_Pos_ofArray___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_SubExpr_Pos_push(x_4, x_6);
lean_dec(x_4);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_ofArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Lean_SubExpr_Pos_root;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Lean_SubExpr_Pos_root;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Lean_SubExpr_Pos_root;
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_SubExpr_Pos_ofArray___spec__1(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_SubExpr_Pos_ofArray___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_SubExpr_Pos_ofArray___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_ofArray___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_ofArray(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_toArray___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_push___boxed), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_toArray___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_SubExpr_Pos_toArray___closed__1;
x_3 = l_Lean_SubExpr_Pos_toArray___closed__2;
x_4 = l_Lean_SubExpr_Pos_foldl___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingDomain(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingDomain___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_pushBindingDomain(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingBody(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingBody___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_pushBindingBody(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetVarType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetVarType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_pushLetVarType(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetValue(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetValue___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_pushLetValue(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetBody(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetBody___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_pushLetBody(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppFn(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_pushAppFn(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_pushAppArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushProj(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_SubExpr_Pos_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushProj___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_pushProj(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_SubExpr_Pos_maxChildren;
x_4 = lean_nat_pow(x_3, x_1);
x_5 = lean_nat_mul(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SubExpr_Pos_pushNaryFn(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_nat_sub(x_1, x_2);
x_5 = l_Lean_SubExpr_Pos_maxChildren;
x_6 = lean_nat_pow(x_5, x_4);
lean_dec(x_4);
x_7 = lean_nat_mul(x_3, x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SubExpr_Pos_pushNaryArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNthBindingDomain(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_1);
x_7 = l_Lean_SubExpr_Pos_push(x_2, x_5);
lean_dec(x_2);
x_1 = x_6;
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lean_SubExpr_Pos_push(x_2, x_3);
lean_dec(x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNthBindingBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_1);
x_7 = l_Lean_SubExpr_Pos_push(x_2, x_5);
lean_dec(x_2);
x_1 = x_6;
x_2 = x_7;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_SubExpr_Pos_toString___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Nat_repr(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Nat_repr(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("/", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_SubExpr_Pos_toArray(x_1);
x_3 = lean_array_to_list(lean_box(0), x_2);
x_4 = lean_box(0);
x_5 = l_List_mapTR_loop___at_Lean_SubExpr_Pos_toString___spec__1(x_3, x_4);
x_6 = l_Lean_SubExpr_Pos_toString___closed__1;
x_7 = l_String_intercalate(x_6, x_5);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("0", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("1", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("2", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("3", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Invalid coordinate ", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1;
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2;
x_5 = lean_string_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3;
x_7 = lean_string_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4;
x_9 = lean_string_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5;
x_11 = lean_string_append(x_10, x_1);
x_12 = l_Lean_SubExpr_Pos_push___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6;
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7;
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8;
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__9;
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_SubExpr_Pos_fromString_x3f___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_fromString_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("malformed ", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_fromString_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_SubExpr_Pos_root;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_fromString_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_SubExpr_Pos_toString___closed__1;
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_String_splitOn(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_List_toString___at_Lean_MetavarContext_MkBinding_instToStringException___spec__2(x_4);
x_6 = l_Lean_SubExpr_Pos_fromString_x3f___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_SubExpr_Pos_push___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = l_Lean_SubExpr_Pos_push___closed__2;
x_14 = lean_string_dec_eq(x_11, x_13);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_15 = l_List_toString___at_Lean_MetavarContext_MkBinding_instToStringException___spec__2(x_4);
lean_dec(x_4);
x_16 = l_Lean_SubExpr_Pos_fromString_x3f___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = lean_string_append(x_17, x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
lean_dec(x_4);
x_20 = l_List_redLength___rarg(x_12);
x_21 = lean_mk_empty_array_with_capacity(x_20);
lean_dec(x_20);
x_22 = l_List_toArrayAux___rarg(x_12, x_21);
x_23 = lean_array_get_size(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at_Lean_SubExpr_Pos_fromString_x3f___spec__1(x_24, x_25, x_22);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = l_Lean_SubExpr_Pos_ofArray(x_31);
lean_dec(x_31);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = l_Lean_SubExpr_Pos_ofArray(x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_1);
x_36 = l_Lean_SubExpr_Pos_fromString_x3f___closed__2;
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_SubExpr_Pos_fromString_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_SubExpr_Pos_fromString_x3f___spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_fromString_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.SubExpr.Pos.fromString!", 28);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_fromString_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_fromString_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_SubExpr_Pos_head___closed__1;
x_5 = l_Lean_SubExpr_Pos_fromString_x21___closed__1;
x_6 = lean_unsigned_to_nat(137u);
x_7 = lean_unsigned_to_nat(22u);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_3);
lean_dec(x_3);
x_9 = l_panic___at_Lean_SubExpr_Pos_tail___spec__1(x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
return x_10;
}
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instOrdPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instOrdNat___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instOrdPos() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_Pos_instOrdPos___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_instDecidableEqPos(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instDecidableEqPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_SubExpr_Pos_instDecidableEqPos(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instToStringPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_toString), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instToStringPos() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_Pos_instToStringPos___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instEmptyCollectionPos() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_Pos_root;
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instReprPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Pos.fromString! ", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instReprPos___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_SubExpr_Pos_instReprPos___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instReprPos___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_SubExpr_Pos_push___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instReprPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_SubExpr_Pos_toString(x_1);
x_4 = l_String_quote(x_3);
lean_dec(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_SubExpr_Pos_instReprPos___closed__2;
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_SubExpr_Pos_instReprPos___closed__3;
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instReprPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SubExpr_Pos_instReprPos(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instToJsonPos___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instToJsonPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_instToJsonPos___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instToJsonPos___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SubExpr_Pos_instToJsonPos___closed__1;
x_2 = l_Lean_SubExpr_Pos_instToStringPos___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instToJsonPos() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_Pos_instToJsonPos___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instFromJsonPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getStr_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_SubExpr_Pos_fromString_x3f(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instFromJsonPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SubExpr_Pos_instFromJsonPos(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedSubExpr___closed__1;
x_2 = l_Lean_SubExpr_Pos_root;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedSubExpr___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_mkRoot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_SubExpr_Pos_root;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_SubExpr_isRoot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_SubExpr_Pos_maxChildren;
x_4 = lean_nat_dec_lt(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_isRoot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_SubExpr_isRoot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_SubExpr_bindingBody_x21___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedSubExpr;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_SubExpr_bindingBody_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.SubExpr.bindingBody!", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_bindingBody_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("subexpr is not a binder", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_bindingBody_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_SubExpr_Pos_head___closed__1;
x_2 = l_Lean_SubExpr_bindingBody_x21___closed__1;
x_3 = lean_unsigned_to_nat(176u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_SubExpr_bindingBody_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_bindingBody_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
switch (lean_obj_tag(x_2)) {
case 6:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 0);
lean_dec(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_SubExpr_Pos_push(x_4, x_7);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_SubExpr_Pos_push(x_9, x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
case 7:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_SubExpr_Pos_push(x_15, x_18);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_SubExpr_Pos_push(x_20, x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
default: 
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = l_Lean_SubExpr_bindingBody_x21___closed__3;
x_26 = l_panic___at_Lean_SubExpr_bindingBody_x21___spec__1(x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_SubExpr_bindingDomain_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.SubExpr.bindingDomain!", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_bindingDomain_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_SubExpr_Pos_head___closed__1;
x_2 = l_Lean_SubExpr_bindingDomain_x21___closed__1;
x_3 = lean_unsigned_to_nat(181u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_SubExpr_bindingBody_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_bindingDomain_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
switch (lean_obj_tag(x_2)) {
case 6:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 0);
lean_dec(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_SubExpr_Pos_push(x_4, x_7);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_SubExpr_Pos_push(x_9, x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
case 7:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_SubExpr_Pos_push(x_15, x_18);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_SubExpr_Pos_push(x_20, x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
default: 
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = l_Lean_SubExpr_bindingDomain_x21___closed__2;
x_26 = l_panic___at_Lean_SubExpr_bindingBody_x21___spec__1(x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonFVarId(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonMVarId(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonFVarId___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonFVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[anonymous]", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonFVarId___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected a `Name`, got '", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonFVarId___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonFVarId___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonFVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getStr_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lean_SubExpr_instFromJsonFVarId___closed__1;
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_String_toName(x_7);
x_11 = l_Lean_Name_isAnonymous(x_10);
if (x_11 == 0)
{
lean_dec(x_1);
lean_ctor_set(x_2, 0, x_10);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(80u);
x_13 = l_Lean_Json_pretty(x_1, x_12);
x_14 = l_Lean_SubExpr_instFromJsonFVarId___closed__2;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lean_SubExpr_instFromJsonFVarId___closed__3;
x_17 = lean_string_append(x_15, x_16);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_17);
return x_2;
}
}
else
{
lean_object* x_18; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_1);
x_18 = l_Lean_SubExpr_instFromJsonFVarId___closed__4;
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_Lean_SubExpr_instFromJsonFVarId___closed__1;
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_String_toName(x_19);
x_23 = l_Lean_Name_isAnonymous(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(80u);
x_26 = l_Lean_Json_pretty(x_1, x_25);
x_27 = l_Lean_SubExpr_instFromJsonFVarId___closed__2;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_Lean_SubExpr_instFromJsonFVarId___closed__3;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_19);
lean_dec(x_1);
x_32 = l_Lean_SubExpr_instFromJsonFVarId___closed__4;
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonFVarId___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SubExpr_instFromJsonFVarId___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonMVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getStr_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lean_SubExpr_instFromJsonFVarId___closed__1;
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_String_toName(x_7);
x_11 = l_Lean_Name_isAnonymous(x_10);
if (x_11 == 0)
{
lean_dec(x_1);
lean_ctor_set(x_2, 0, x_10);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(80u);
x_13 = l_Lean_Json_pretty(x_1, x_12);
x_14 = l_Lean_SubExpr_instFromJsonFVarId___closed__2;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lean_SubExpr_instFromJsonFVarId___closed__3;
x_17 = lean_string_append(x_15, x_16);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_17);
return x_2;
}
}
else
{
lean_object* x_18; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_1);
x_18 = l_Lean_SubExpr_instFromJsonFVarId___closed__4;
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_Lean_SubExpr_instFromJsonFVarId___closed__1;
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_String_toName(x_19);
x_23 = l_Lean_Name_isAnonymous(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(80u);
x_26 = l_Lean_Json_pretty(x_1, x_25);
x_27 = l_Lean_SubExpr_instFromJsonFVarId___closed__2;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_Lean_SubExpr_instFromJsonFVarId___closed__3;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_19);
lean_dec(x_1);
x_32 = l_Lean_SubExpr_instFromJsonFVarId___closed__4;
return x_32;
}
}
}
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("no inductive constructor matched", 32);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1___closed__2;
return x_2;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hypValue", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__1;
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_9 = l_Except_orElseLazy___rarg(x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_13 = l_Except_orElseLazy___rarg(x_11, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_77; lean_object* x_117; uint8_t x_118; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_array_get_size(x_14);
x_117 = lean_unsigned_to_nat(0u);
x_118 = lean_nat_dec_lt(x_117, x_15);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = l_Lean_instInhabitedJson;
x_120 = l___private_Init_Util_0__outOfBounds___rarg(x_119);
x_77 = x_120;
goto block_116;
}
else
{
lean_object* x_121; 
x_121 = lean_array_fget(x_14, x_117);
x_77 = x_121;
goto block_116;
}
block_76:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_dec_lt(x_17, x_15);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
x_19 = l_Lean_instInhabitedJson;
x_20 = l___private_Init_Util_0__outOfBounds___rarg(x_19);
x_21 = l_Lean_Json_getStr_x3f(x_20);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_24 = l_Except_orElseLazy___rarg(x_21, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_28 = l_Except_orElseLazy___rarg(x_26, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_SubExpr_Pos_fromString_x3f(x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_16);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_33 = l_Except_orElseLazy___rarg(x_30, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_37 = l_Except_orElseLazy___rarg(x_35, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_16);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_30, 0, x_40);
x_41 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_42 = l_Except_orElseLazy___rarg(x_30, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
lean_dec(x_30);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_16);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_47 = l_Except_orElseLazy___rarg(x_45, x_46);
return x_47;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_array_fget(x_14, x_17);
lean_dec(x_14);
x_49 = l_Lean_Json_getStr_x3f(x_48);
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_16);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_52 = l_Except_orElseLazy___rarg(x_49, x_51);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_56 = l_Except_orElseLazy___rarg(x_54, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_49, 0);
lean_inc(x_57);
lean_dec(x_49);
x_58 = l_Lean_SubExpr_Pos_fromString_x3f(x_57);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
lean_dec(x_16);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_61 = l_Except_orElseLazy___rarg(x_58, x_60);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_65 = l_Except_orElseLazy___rarg(x_63, x_64);
return x_65;
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_58);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_58, 0);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_16);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_58, 0, x_68);
x_69 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_70 = l_Except_orElseLazy___rarg(x_58, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_58, 0);
lean_inc(x_71);
lean_dec(x_58);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_16);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_75 = l_Except_orElseLazy___rarg(x_73, x_74);
return x_75;
}
}
}
}
}
block_116:
{
lean_object* x_78; 
x_78 = l_Lean_Json_getStr_x3f(x_77);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
lean_dec(x_77);
lean_dec(x_15);
lean_dec(x_14);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_81 = l_Except_orElseLazy___rarg(x_78, x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_78, 0);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_85 = l_Except_orElseLazy___rarg(x_83, x_84);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_78);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_78, 0);
x_88 = l_Lean_SubExpr_instFromJsonFVarId___closed__1;
x_89 = lean_string_dec_eq(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = l_String_toName(x_87);
x_91 = l_Lean_Name_isAnonymous(x_90);
if (x_91 == 0)
{
lean_free_object(x_78);
lean_dec(x_77);
x_16 = x_90;
goto block_76;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_90);
lean_dec(x_15);
lean_dec(x_14);
x_92 = lean_unsigned_to_nat(80u);
x_93 = l_Lean_Json_pretty(x_77, x_92);
x_94 = l_Lean_SubExpr_instFromJsonFVarId___closed__2;
x_95 = lean_string_append(x_94, x_93);
lean_dec(x_93);
x_96 = l_Lean_SubExpr_instFromJsonFVarId___closed__3;
x_97 = lean_string_append(x_95, x_96);
lean_ctor_set_tag(x_78, 0);
lean_ctor_set(x_78, 0, x_97);
x_98 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_99 = l_Except_orElseLazy___rarg(x_78, x_98);
return x_99;
}
}
else
{
lean_object* x_100; 
lean_free_object(x_78);
lean_dec(x_87);
lean_dec(x_77);
x_100 = lean_box(0);
x_16 = x_100;
goto block_76;
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_78, 0);
lean_inc(x_101);
lean_dec(x_78);
x_102 = l_Lean_SubExpr_instFromJsonFVarId___closed__1;
x_103 = lean_string_dec_eq(x_101, x_102);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = l_String_toName(x_101);
x_105 = l_Lean_Name_isAnonymous(x_104);
if (x_105 == 0)
{
lean_dec(x_77);
x_16 = x_104;
goto block_76;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_104);
lean_dec(x_15);
lean_dec(x_14);
x_106 = lean_unsigned_to_nat(80u);
x_107 = l_Lean_Json_pretty(x_77, x_106);
x_108 = l_Lean_SubExpr_instFromJsonFVarId___closed__2;
x_109 = lean_string_append(x_108, x_107);
lean_dec(x_107);
x_110 = l_Lean_SubExpr_instFromJsonFVarId___closed__3;
x_111 = lean_string_append(x_109, x_110);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2;
x_114 = l_Except_orElseLazy___rarg(x_112, x_113);
return x_114;
}
}
else
{
lean_object* x_115; 
lean_dec(x_101);
lean_dec(x_77);
x_115 = lean_box(0);
x_16 = x_115;
goto block_76;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hypType", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__3___closed__1;
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_2);
x_7 = lean_alloc_closure((void*)(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Except_orElseLazy___rarg(x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Except_orElseLazy___rarg(x_11, x_7);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_64; lean_object* x_100; uint8_t x_101; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_array_get_size(x_13);
x_100 = lean_unsigned_to_nat(0u);
x_101 = lean_nat_dec_lt(x_100, x_14);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = l_Lean_instInhabitedJson;
x_103 = l___private_Init_Util_0__outOfBounds___rarg(x_102);
x_64 = x_103;
goto block_99;
}
else
{
lean_object* x_104; 
x_104 = lean_array_fget(x_13, x_100);
x_64 = x_104;
goto block_99;
}
block_63:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_dec_lt(x_16, x_14);
lean_dec(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_18 = l_Lean_instInhabitedJson;
x_19 = l___private_Init_Util_0__outOfBounds___rarg(x_18);
x_20 = l_Lean_Json_getStr_x3f(x_19);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l_Except_orElseLazy___rarg(x_20, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Except_orElseLazy___rarg(x_24, x_7);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = l_Lean_SubExpr_Pos_fromString_x3f(x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_15);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l_Except_orElseLazy___rarg(x_27, x_7);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Except_orElseLazy___rarg(x_31, x_7);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_15);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_27, 0, x_35);
x_36 = l_Except_orElseLazy___rarg(x_27, x_7);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_15);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Except_orElseLazy___rarg(x_39, x_7);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_array_fget(x_13, x_16);
lean_dec(x_13);
x_42 = l_Lean_Json_getStr_x3f(x_41);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_dec(x_15);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = l_Except_orElseLazy___rarg(x_42, x_7);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Except_orElseLazy___rarg(x_46, x_7);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
lean_dec(x_42);
x_49 = l_Lean_SubExpr_Pos_fromString_x3f(x_48);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_15);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Except_orElseLazy___rarg(x_49, x_7);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Except_orElseLazy___rarg(x_53, x_7);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_49);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_49, 0);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_15);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_49, 0, x_57);
x_58 = l_Except_orElseLazy___rarg(x_49, x_7);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_49, 0);
lean_inc(x_59);
lean_dec(x_49);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_15);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Except_orElseLazy___rarg(x_61, x_7);
return x_62;
}
}
}
}
}
block_99:
{
lean_object* x_65; 
x_65 = l_Lean_Json_getStr_x3f(x_64);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
lean_dec(x_64);
lean_dec(x_14);
lean_dec(x_13);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = l_Except_orElseLazy___rarg(x_65, x_7);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Except_orElseLazy___rarg(x_69, x_7);
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_65, 0);
x_73 = l_Lean_SubExpr_instFromJsonFVarId___closed__1;
x_74 = lean_string_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = l_String_toName(x_72);
x_76 = l_Lean_Name_isAnonymous(x_75);
if (x_76 == 0)
{
lean_free_object(x_65);
lean_dec(x_64);
x_15 = x_75;
goto block_63;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_75);
lean_dec(x_14);
lean_dec(x_13);
x_77 = lean_unsigned_to_nat(80u);
x_78 = l_Lean_Json_pretty(x_64, x_77);
x_79 = l_Lean_SubExpr_instFromJsonFVarId___closed__2;
x_80 = lean_string_append(x_79, x_78);
lean_dec(x_78);
x_81 = l_Lean_SubExpr_instFromJsonFVarId___closed__3;
x_82 = lean_string_append(x_80, x_81);
lean_ctor_set_tag(x_65, 0);
lean_ctor_set(x_65, 0, x_82);
x_83 = l_Except_orElseLazy___rarg(x_65, x_7);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_free_object(x_65);
lean_dec(x_72);
lean_dec(x_64);
x_84 = lean_box(0);
x_15 = x_84;
goto block_63;
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_65, 0);
lean_inc(x_85);
lean_dec(x_65);
x_86 = l_Lean_SubExpr_instFromJsonFVarId___closed__1;
x_87 = lean_string_dec_eq(x_85, x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = l_String_toName(x_85);
x_89 = l_Lean_Name_isAnonymous(x_88);
if (x_89 == 0)
{
lean_dec(x_64);
x_15 = x_88;
goto block_63;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_88);
lean_dec(x_14);
lean_dec(x_13);
x_90 = lean_unsigned_to_nat(80u);
x_91 = l_Lean_Json_pretty(x_64, x_90);
x_92 = l_Lean_SubExpr_instFromJsonFVarId___closed__2;
x_93 = lean_string_append(x_92, x_91);
lean_dec(x_91);
x_94 = l_Lean_SubExpr_instFromJsonFVarId___closed__3;
x_95 = lean_string_append(x_93, x_94);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = l_Except_orElseLazy___rarg(x_96, x_7);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_85);
lean_dec(x_64);
x_98 = lean_box(0);
x_15 = x_98;
goto block_63;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hyp", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__1;
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_2);
x_7 = lean_alloc_closure((void*)(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__3___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_6);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Except_orElseLazy___rarg(x_6, x_7);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_6, 0);
lean_inc(x_53);
lean_dec(x_6);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Except_orElseLazy___rarg(x_54, x_7);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_6, 0);
lean_inc(x_56);
lean_dec(x_6);
x_57 = lean_array_get_size(x_56);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_lt(x_58, x_57);
lean_dec(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_56);
x_60 = l_Lean_instInhabitedJson;
x_61 = l___private_Init_Util_0__outOfBounds___rarg(x_60);
x_8 = x_61;
goto block_50;
}
else
{
lean_object* x_62; 
x_62 = lean_array_fget(x_56, x_58);
lean_dec(x_56);
x_8 = x_62;
goto block_50;
}
}
block_50:
{
lean_object* x_9; 
x_9 = l_Lean_Json_getStr_x3f(x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Except_orElseLazy___rarg(x_9, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Except_orElseLazy___rarg(x_13, x_7);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = l_Lean_SubExpr_instFromJsonFVarId___closed__1;
x_18 = lean_string_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_String_toName(x_16);
x_20 = l_Lean_Name_isAnonymous(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_9, 0, x_21);
x_22 = l_Except_orElseLazy___rarg(x_9, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
x_23 = lean_unsigned_to_nat(80u);
x_24 = l_Lean_Json_pretty(x_8, x_23);
x_25 = l_Lean_SubExpr_instFromJsonFVarId___closed__2;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Lean_SubExpr_instFromJsonFVarId___closed__3;
x_28 = lean_string_append(x_26, x_27);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_28);
x_29 = l_Except_orElseLazy___rarg(x_9, x_7);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_9);
lean_dec(x_16);
lean_dec(x_8);
x_30 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__3;
x_31 = l_Except_orElseLazy___rarg(x_30, x_7);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_9, 0);
lean_inc(x_32);
lean_dec(x_9);
x_33 = l_Lean_SubExpr_instFromJsonFVarId___closed__1;
x_34 = lean_string_dec_eq(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_String_toName(x_32);
x_36 = l_Lean_Name_isAnonymous(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_8);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Except_orElseLazy___rarg(x_38, x_7);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_35);
x_40 = lean_unsigned_to_nat(80u);
x_41 = l_Lean_Json_pretty(x_8, x_40);
x_42 = l_Lean_SubExpr_instFromJsonFVarId___closed__2;
x_43 = lean_string_append(x_42, x_41);
lean_dec(x_41);
x_44 = l_Lean_SubExpr_instFromJsonFVarId___closed__3;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Except_orElseLazy___rarg(x_46, x_7);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_32);
lean_dec(x_8);
x_48 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__3;
x_49 = l_Except_orElseLazy___rarg(x_48, x_7);
return x_49;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("target", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_box(0);
x_3 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____closed__1;
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Json_parseTagged(x_1, x_3, x_4, x_2);
x_6 = lean_alloc_closure((void*)(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Except_orElseLazy___rarg(x_5, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Except_orElseLazy___rarg(x_10, x_6);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
x_16 = l_Lean_instInhabitedJson;
x_17 = l___private_Init_Util_0__outOfBounds___rarg(x_16);
x_18 = l_Lean_Json_getStr_x3f(x_17);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Except_orElseLazy___rarg(x_18, x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Except_orElseLazy___rarg(x_22, x_6);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l_Lean_SubExpr_Pos_fromString_x3f(x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Except_orElseLazy___rarg(x_25, x_6);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Except_orElseLazy___rarg(x_29, x_6);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_25, 0, x_33);
x_34 = l_Except_orElseLazy___rarg(x_25, x_6);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Except_orElseLazy___rarg(x_37, x_6);
return x_38;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_array_fget(x_12, x_14);
lean_dec(x_12);
x_40 = l_Lean_Json_getStr_x3f(x_39);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Except_orElseLazy___rarg(x_40, x_6);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Except_orElseLazy___rarg(x_44, x_6);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
lean_dec(x_40);
x_47 = l_Lean_SubExpr_Pos_fromString_x3f(x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = l_Except_orElseLazy___rarg(x_47, x_6);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Except_orElseLazy___rarg(x_51, x_6);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_47);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_47, 0, x_55);
x_56 = l_Except_orElseLazy___rarg(x_47, x_6);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_47, 0);
lean_inc(x_57);
lean_dec(x_47);
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_Except_orElseLazy___rarg(x_59, x_6);
return x_60;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalLocation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalLocation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_instFromJsonGoalLocation___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_toJsonGoalLocation____x40_Lean_SubExpr___hyg_1606____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_toJsonGoalLocation____x40_Lean_SubExpr___hyg_1606_(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = 1;
x_4 = l_Lean_Name_toString(x_2, x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Json_mkObj(x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = 1;
x_14 = l_Lean_Name_toString(x_11, x_13);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_SubExpr_Pos_toString(x_12);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l___private_Lean_SubExpr_0__Lean_SubExpr_toJsonGoalLocation____x40_Lean_SubExpr___hyg_1606____closed__1;
x_19 = lean_array_push(x_18, x_15);
x_20 = lean_array_push(x_19, x_17);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__3___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Json_mkObj(x_25);
return x_26;
}
case 2:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = 1;
x_30 = l_Lean_Name_toString(x_27, x_29);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_SubExpr_Pos_toString(x_28);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l___private_Lean_SubExpr_0__Lean_SubExpr_toJsonGoalLocation____x40_Lean_SubExpr___hyg_1606____closed__1;
x_35 = lean_array_push(x_34, x_31);
x_36 = lean_array_push(x_35, x_33);
x_37 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Json_mkObj(x_41);
return x_42;
}
default: 
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
lean_dec(x_1);
x_44 = l_Lean_SubExpr_Pos_toString(x_43);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____closed__1;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Json_mkObj(x_49);
return x_50;
}
}
}
}
static lean_object* _init_l_Lean_SubExpr_instToJsonGoalLocation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_SubExpr_0__Lean_SubExpr_toJsonGoalLocation____x40_Lean_SubExpr___hyg_1606_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_instToJsonGoalLocation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_instToJsonGoalLocation___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = l_Lean_SubExpr_instFromJsonFVarId___closed__1;
x_11 = lean_string_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_String_toName(x_9);
x_13 = l_Lean_Name_isAnonymous(x_12);
if (x_13 == 0)
{
lean_dec(x_3);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(80u);
x_15 = l_Lean_Json_pretty(x_3, x_14);
x_16 = l_Lean_SubExpr_instFromJsonFVarId___closed__2;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_SubExpr_instFromJsonFVarId___closed__3;
x_19 = lean_string_append(x_17, x_18);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_19);
return x_4;
}
}
else
{
lean_object* x_20; 
lean_free_object(x_4);
lean_dec(x_9);
lean_dec(x_3);
x_20 = l_Lean_SubExpr_instFromJsonFVarId___closed__4;
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = l_Lean_SubExpr_instFromJsonFVarId___closed__1;
x_23 = lean_string_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_String_toName(x_21);
x_25 = l_Lean_Name_isAnonymous(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_3);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
x_27 = lean_unsigned_to_nat(80u);
x_28 = l_Lean_Json_pretty(x_3, x_27);
x_29 = l_Lean_SubExpr_instFromJsonFVarId___closed__2;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Lean_SubExpr_instFromJsonFVarId___closed__3;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_21);
lean_dec(x_3);
x_34 = l_Lean_SubExpr_instFromJsonFVarId___closed__4;
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354_(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mvarId", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("SubExpr", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("GoalsLocation", 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__2;
x_2 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__3;
x_3 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__5;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__6;
x_2 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__10() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__9;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__8;
x_2 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__11;
x_2 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__12;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("loc", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__16() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__15;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__8;
x_2 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__16;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__17;
x_2 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__12;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__13;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__13;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__14;
x_14 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____spec__2(x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__18;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__18;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_instFromJsonGoalsLocation___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_toJsonGoalsLocation____x40_Lean_SubExpr___hyg_1842_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = 1;
x_4 = l_Lean_Name_toString(x_2, x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l___private_Lean_SubExpr_0__Lean_SubExpr_toJsonGoalLocation____x40_Lean_SubExpr___hyg_1606_(x_10);
x_12 = l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__14;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_List_join___rarg(x_16);
x_18 = l_Lean_Json_mkObj(x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_SubExpr_instToJsonGoalsLocation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_SubExpr_0__Lean_SubExpr_toJsonGoalsLocation____x40_Lean_SubExpr___hyg_1842_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_instToJsonGoalsLocation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_instToJsonGoalsLocation___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_SubExpr_Pos_push(x_1, x_5);
x_7 = lean_apply_2(x_2, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_SubExpr_Pos_push(x_3, x_12);
lean_inc(x_2);
x_14 = l_Lean_Expr_traverseAppWithPos___rarg(x_1, x_2, x_13, x_5);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Expr_traverseAppWithPos___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_6);
x_17 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_apply_2(x_2, x_3, x_4);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_traverseAppWithPos___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_traverseAppWithPos___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RBMap(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_SubExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_SubExpr_Pos_maxChildren = _init_l_Lean_SubExpr_Pos_maxChildren();
lean_mark_persistent(l_Lean_SubExpr_Pos_maxChildren);
l_Lean_SubExpr_Pos_typeCoord___closed__1 = _init_l_Lean_SubExpr_Pos_typeCoord___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_typeCoord___closed__1);
l_Lean_SubExpr_Pos_typeCoord = _init_l_Lean_SubExpr_Pos_typeCoord();
lean_mark_persistent(l_Lean_SubExpr_Pos_typeCoord);
l_Lean_SubExpr_Pos_root = _init_l_Lean_SubExpr_Pos_root();
lean_mark_persistent(l_Lean_SubExpr_Pos_root);
l_Lean_SubExpr_Pos_instInhabitedPos = _init_l_Lean_SubExpr_Pos_instInhabitedPos();
lean_mark_persistent(l_Lean_SubExpr_Pos_instInhabitedPos);
l_Lean_SubExpr_Pos_head___closed__1 = _init_l_Lean_SubExpr_Pos_head___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_head___closed__1);
l_Lean_SubExpr_Pos_head___closed__2 = _init_l_Lean_SubExpr_Pos_head___closed__2();
lean_mark_persistent(l_Lean_SubExpr_Pos_head___closed__2);
l_Lean_SubExpr_Pos_head___closed__3 = _init_l_Lean_SubExpr_Pos_head___closed__3();
lean_mark_persistent(l_Lean_SubExpr_Pos_head___closed__3);
l_Lean_SubExpr_Pos_head___closed__4 = _init_l_Lean_SubExpr_Pos_head___closed__4();
lean_mark_persistent(l_Lean_SubExpr_Pos_head___closed__4);
l_Lean_SubExpr_Pos_tail___closed__1 = _init_l_Lean_SubExpr_Pos_tail___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_tail___closed__1);
l_Lean_SubExpr_Pos_tail___closed__2 = _init_l_Lean_SubExpr_Pos_tail___closed__2();
lean_mark_persistent(l_Lean_SubExpr_Pos_tail___closed__2);
l_Lean_SubExpr_Pos_push___closed__1 = _init_l_Lean_SubExpr_Pos_push___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_push___closed__1);
l_Lean_SubExpr_Pos_push___closed__2 = _init_l_Lean_SubExpr_Pos_push___closed__2();
lean_mark_persistent(l_Lean_SubExpr_Pos_push___closed__2);
l_Lean_SubExpr_Pos_push___closed__3 = _init_l_Lean_SubExpr_Pos_push___closed__3();
lean_mark_persistent(l_Lean_SubExpr_Pos_push___closed__3);
l_Lean_SubExpr_Pos_depth___closed__1 = _init_l_Lean_SubExpr_Pos_depth___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_depth___closed__1);
l_Lean_SubExpr_Pos_append___closed__1 = _init_l_Lean_SubExpr_Pos_append___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_append___closed__1);
l_Lean_SubExpr_Pos_toArray___closed__1 = _init_l_Lean_SubExpr_Pos_toArray___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_toArray___closed__1);
l_Lean_SubExpr_Pos_toArray___closed__2 = _init_l_Lean_SubExpr_Pos_toArray___closed__2();
lean_mark_persistent(l_Lean_SubExpr_Pos_toArray___closed__2);
l_Lean_SubExpr_Pos_toString___closed__1 = _init_l_Lean_SubExpr_Pos_toString___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_toString___closed__1);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8);
l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__9 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__9();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__9);
l_Lean_SubExpr_Pos_fromString_x3f___closed__1 = _init_l_Lean_SubExpr_Pos_fromString_x3f___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_fromString_x3f___closed__1);
l_Lean_SubExpr_Pos_fromString_x3f___closed__2 = _init_l_Lean_SubExpr_Pos_fromString_x3f___closed__2();
lean_mark_persistent(l_Lean_SubExpr_Pos_fromString_x3f___closed__2);
l_Lean_SubExpr_Pos_fromString_x21___closed__1 = _init_l_Lean_SubExpr_Pos_fromString_x21___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_fromString_x21___closed__1);
l_Lean_SubExpr_Pos_instOrdPos___closed__1 = _init_l_Lean_SubExpr_Pos_instOrdPos___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_instOrdPos___closed__1);
l_Lean_SubExpr_Pos_instOrdPos = _init_l_Lean_SubExpr_Pos_instOrdPos();
lean_mark_persistent(l_Lean_SubExpr_Pos_instOrdPos);
l_Lean_SubExpr_Pos_instToStringPos___closed__1 = _init_l_Lean_SubExpr_Pos_instToStringPos___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_instToStringPos___closed__1);
l_Lean_SubExpr_Pos_instToStringPos = _init_l_Lean_SubExpr_Pos_instToStringPos();
lean_mark_persistent(l_Lean_SubExpr_Pos_instToStringPos);
l_Lean_SubExpr_Pos_instEmptyCollectionPos = _init_l_Lean_SubExpr_Pos_instEmptyCollectionPos();
lean_mark_persistent(l_Lean_SubExpr_Pos_instEmptyCollectionPos);
l_Lean_SubExpr_Pos_instReprPos___closed__1 = _init_l_Lean_SubExpr_Pos_instReprPos___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_instReprPos___closed__1);
l_Lean_SubExpr_Pos_instReprPos___closed__2 = _init_l_Lean_SubExpr_Pos_instReprPos___closed__2();
lean_mark_persistent(l_Lean_SubExpr_Pos_instReprPos___closed__2);
l_Lean_SubExpr_Pos_instReprPos___closed__3 = _init_l_Lean_SubExpr_Pos_instReprPos___closed__3();
lean_mark_persistent(l_Lean_SubExpr_Pos_instReprPos___closed__3);
l_Lean_SubExpr_Pos_instToJsonPos___closed__1 = _init_l_Lean_SubExpr_Pos_instToJsonPos___closed__1();
lean_mark_persistent(l_Lean_SubExpr_Pos_instToJsonPos___closed__1);
l_Lean_SubExpr_Pos_instToJsonPos___closed__2 = _init_l_Lean_SubExpr_Pos_instToJsonPos___closed__2();
lean_mark_persistent(l_Lean_SubExpr_Pos_instToJsonPos___closed__2);
l_Lean_SubExpr_Pos_instToJsonPos = _init_l_Lean_SubExpr_Pos_instToJsonPos();
lean_mark_persistent(l_Lean_SubExpr_Pos_instToJsonPos);
l_Lean_instInhabitedSubExpr___closed__1 = _init_l_Lean_instInhabitedSubExpr___closed__1();
lean_mark_persistent(l_Lean_instInhabitedSubExpr___closed__1);
l_Lean_instInhabitedSubExpr___closed__2 = _init_l_Lean_instInhabitedSubExpr___closed__2();
lean_mark_persistent(l_Lean_instInhabitedSubExpr___closed__2);
l_Lean_instInhabitedSubExpr = _init_l_Lean_instInhabitedSubExpr();
lean_mark_persistent(l_Lean_instInhabitedSubExpr);
l_Lean_SubExpr_bindingBody_x21___closed__1 = _init_l_Lean_SubExpr_bindingBody_x21___closed__1();
lean_mark_persistent(l_Lean_SubExpr_bindingBody_x21___closed__1);
l_Lean_SubExpr_bindingBody_x21___closed__2 = _init_l_Lean_SubExpr_bindingBody_x21___closed__2();
lean_mark_persistent(l_Lean_SubExpr_bindingBody_x21___closed__2);
l_Lean_SubExpr_bindingBody_x21___closed__3 = _init_l_Lean_SubExpr_bindingBody_x21___closed__3();
lean_mark_persistent(l_Lean_SubExpr_bindingBody_x21___closed__3);
l_Lean_SubExpr_bindingDomain_x21___closed__1 = _init_l_Lean_SubExpr_bindingDomain_x21___closed__1();
lean_mark_persistent(l_Lean_SubExpr_bindingDomain_x21___closed__1);
l_Lean_SubExpr_bindingDomain_x21___closed__2 = _init_l_Lean_SubExpr_bindingDomain_x21___closed__2();
lean_mark_persistent(l_Lean_SubExpr_bindingDomain_x21___closed__2);
l_Lean_SubExpr_instFromJsonFVarId___closed__1 = _init_l_Lean_SubExpr_instFromJsonFVarId___closed__1();
lean_mark_persistent(l_Lean_SubExpr_instFromJsonFVarId___closed__1);
l_Lean_SubExpr_instFromJsonFVarId___closed__2 = _init_l_Lean_SubExpr_instFromJsonFVarId___closed__2();
lean_mark_persistent(l_Lean_SubExpr_instFromJsonFVarId___closed__2);
l_Lean_SubExpr_instFromJsonFVarId___closed__3 = _init_l_Lean_SubExpr_instFromJsonFVarId___closed__3();
lean_mark_persistent(l_Lean_SubExpr_instFromJsonFVarId___closed__3);
l_Lean_SubExpr_instFromJsonFVarId___closed__4 = _init_l_Lean_SubExpr_instFromJsonFVarId___closed__4();
lean_mark_persistent(l_Lean_SubExpr_instFromJsonFVarId___closed__4);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1___closed__1 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1___closed__1);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1___closed__2 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__1___closed__2);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__1 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__1);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__2___closed__2);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__3___closed__1 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__3___closed__1);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__1 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__1);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__2 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__2();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__2);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__3 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__3();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____lambda__4___closed__3);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____closed__1 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____closed__1();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalLocation____x40_Lean_SubExpr___hyg_1354____closed__1);
l_Lean_SubExpr_instFromJsonGoalLocation___closed__1 = _init_l_Lean_SubExpr_instFromJsonGoalLocation___closed__1();
lean_mark_persistent(l_Lean_SubExpr_instFromJsonGoalLocation___closed__1);
l_Lean_SubExpr_instFromJsonGoalLocation = _init_l_Lean_SubExpr_instFromJsonGoalLocation();
lean_mark_persistent(l_Lean_SubExpr_instFromJsonGoalLocation);
l___private_Lean_SubExpr_0__Lean_SubExpr_toJsonGoalLocation____x40_Lean_SubExpr___hyg_1606____closed__1 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_toJsonGoalLocation____x40_Lean_SubExpr___hyg_1606____closed__1();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_toJsonGoalLocation____x40_Lean_SubExpr___hyg_1606____closed__1);
l_Lean_SubExpr_instToJsonGoalLocation___closed__1 = _init_l_Lean_SubExpr_instToJsonGoalLocation___closed__1();
lean_mark_persistent(l_Lean_SubExpr_instToJsonGoalLocation___closed__1);
l_Lean_SubExpr_instToJsonGoalLocation = _init_l_Lean_SubExpr_instToJsonGoalLocation();
lean_mark_persistent(l_Lean_SubExpr_instToJsonGoalLocation);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__1 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__1();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__1);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__2 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__2();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__2);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__3 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__3();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__3);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__4 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__4();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__4);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__5 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__5();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__5);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__6 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__6();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__6);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__7 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__7();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__7);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__8 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__8();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__8);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__9 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__9();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__9);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__10 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__10();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__10);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__11 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__11();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__11);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__12 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__12();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__12);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__13 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__13();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__13);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__14 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__14();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__14);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__15 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__15();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__15);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__16 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__16();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__16);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__17 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__17();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__17);
l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__18 = _init_l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__18();
lean_mark_persistent(l___private_Lean_SubExpr_0__Lean_SubExpr_fromJsonGoalsLocation____x40_Lean_SubExpr___hyg_1742____closed__18);
l_Lean_SubExpr_instFromJsonGoalsLocation___closed__1 = _init_l_Lean_SubExpr_instFromJsonGoalsLocation___closed__1();
lean_mark_persistent(l_Lean_SubExpr_instFromJsonGoalsLocation___closed__1);
l_Lean_SubExpr_instFromJsonGoalsLocation = _init_l_Lean_SubExpr_instFromJsonGoalsLocation();
lean_mark_persistent(l_Lean_SubExpr_instFromJsonGoalsLocation);
l_Lean_SubExpr_instToJsonGoalsLocation___closed__1 = _init_l_Lean_SubExpr_instToJsonGoalsLocation___closed__1();
lean_mark_persistent(l_Lean_SubExpr_instToJsonGoalsLocation___closed__1);
l_Lean_SubExpr_instToJsonGoalsLocation = _init_l_Lean_SubExpr_instToJsonGoalsLocation();
lean_mark_persistent(l_Lean_SubExpr_instToJsonGoalsLocation);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
