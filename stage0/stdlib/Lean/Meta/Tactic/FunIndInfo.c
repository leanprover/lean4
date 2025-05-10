// Lean compiler output
// Module: Lean.Meta.Tactic.FunIndInfo
// Imports: Lean.Meta.Basic Lean.ScopedEnvExtension Lean.ReservedNameAction
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
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_setFunIndInfo___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__3;
lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__3;
static lean_object* l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_setFunIndInfo___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_toCtorIdx(uint8_t);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___rarg___lambda__1(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__7(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__5;
lean_object* l_Lean_Core_instInhabitedCoreM___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__14;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__1;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__17;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getFunCasesName___closed__2;
static lean_object* l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__3;
static lean_object* l_Lean_Meta_getFunInductName___closed__2;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__5;
static lean_object* l_Lean_Meta_getMutualInductName___closed__3;
static lean_object* l_Lean_Meta_instInhabitedFunIndInfo___closed__1;
static lean_object* l_Lean_Meta_getFunCasesName___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__15;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__7;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__9;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__18;
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedFunIndParamKind;
uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__16;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__14;
static lean_object* l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__11;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__12;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__1;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedFunIndInfo;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__1;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__20;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__5;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__11;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__6;
static lean_object* l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__7;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__7;
static lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__8;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__9;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_toCtorIdx___boxed(lean_object*);
static lean_object* l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__9;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_toArray___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__10;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__16;
LEAN_EXPORT lean_object* l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28_(uint8_t, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_funIndInfoExt;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getMutualInductName___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__19;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__10;
static lean_object* l_Lean_Meta_setFunIndInfo___closed__9;
static lean_object* l_Lean_Meta_getMutualInductName___closed__1;
static lean_object* l_panic___at_Lean_Meta_setFunIndInfo___spec__1___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_beqFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_10_(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__3;
static lean_object* l_Lean_Meta_getFunCasesName___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_setFunIndInfo___closed__8;
static lean_object* l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__4;
LEAN_EXPORT lean_object* l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__5(lean_object*);
static lean_object* l_Lean_Meta_setFunIndInfo___closed__2;
static lean_object* l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName___boxed(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion(lean_object*);
static lean_object* l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__10;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__18;
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__19;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__1;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__8;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__13;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__4;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__6;
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__6___boxed(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__12;
static lean_object* l_Lean_Meta_instReprFunIndInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__2___boxed(lean_object*);
static lean_object* l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__8;
lean_object* l_Lean_mkMapDeclarationExtension___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__3(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__7;
lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instBEqFunIndParamKind___closed__1;
static lean_object* l_Lean_Meta_getFunInductName___closed__1;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprFunIndParamKind___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqFunIndParamKind;
static lean_object* l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__2;
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__2(uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getFunInductName___closed__4;
static lean_object* l_Lean_Meta_instInhabitedFunIndInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__13;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_getMutualInductName___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__15;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__10;
static lean_object* l_Lean_Meta_getFunInductName___closed__3;
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__6(uint8_t);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__8(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndInfo;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_beqFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_10____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_setFunIndInfo___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__11;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setFunIndInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Bool_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndParamKind;
static lean_object* l_Lean_Meta_getFunCasesName___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_FunIndParamKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_FunIndParamKind_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_FunIndParamKind_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_FunIndParamKind_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_FunIndParamKind_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_FunIndParamKind_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_FunIndParamKind_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_beqFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_10_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_FunIndParamKind_toCtorIdx(x_1);
x_4 = l_Lean_Meta_FunIndParamKind_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_beqFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_10____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_beqFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_10_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_instBEqFunIndParamKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_beqFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_10____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instBEqFunIndParamKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instBEqFunIndParamKind___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.FunIndParamKind.dropped", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__3;
x_2 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__4;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__6;
x_2 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__7;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.FunIndParamKind.param", 31, 31);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__3;
x_2 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__10;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__6;
x_2 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__10;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__14() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__13;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.FunIndParamKind.target", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__3;
x_2 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__16;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__17;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__6;
x_2 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__16;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__20() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__19;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28_(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__5;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__8;
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
case 1:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1024u);
x_10 = lean_nat_dec_le(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__12;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__14;
x_14 = l_Repr_addAppParen(x_13, x_2);
return x_14;
}
}
default: 
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_nat_dec_le(x_15, x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__18;
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__20;
x_20 = l_Repr_addAppParen(x_19, x_2);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndParamKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndParamKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instReprFunIndParamKind___closed__1;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedFunIndParamKind() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedFunIndInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedFunIndInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_instInhabitedFunIndInfo___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedFunIndInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedFunIndInfo___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__2(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Bool_repr(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Bool_repr(x_8, x_7);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
x_2 = x_10;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_1);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_unbox(x_12);
lean_dec(x_12);
x_17 = l_Bool_repr(x_16, x_15);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_2 = x_18;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Bool_repr(x_7, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unbox(x_9);
lean_dec(x_9);
x_12 = l_Bool_repr(x_11, x_10);
x_13 = l_List_foldl___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__4(x_2, x_12, x_4);
return x_13;
}
}
}
}
static lean_object* _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__2;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__4;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__5;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[]", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_5 = lean_array_to_list(x_1);
x_6 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__3;
x_7 = l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__3(x_5, x_6);
x_8 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__7;
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__9;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__6;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = 1;
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__11;
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__6(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28_(x_8, x_7);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
x_2 = x_10;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_1);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_unbox(x_12);
lean_dec(x_12);
x_17 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28_(x_16, x_15);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_2 = x_18;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28_(x_7, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unbox(x_9);
lean_dec(x_9);
x_12 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28_(x_11, x_10);
x_13 = l_List_foldl___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__8(x_2, x_12, x_4);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_5 = lean_array_to_list(x_1);
x_6 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__3;
x_7 = l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__7(x_5, x_6);
x_8 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__7;
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__9;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__6;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = 1;
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__11;
return x_16;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("funIndName", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__3;
x_2 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__5;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(14u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("levelMask", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("params", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__11;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__14;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__15;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__18;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Name_reprPrec(x_3, x_4);
x_6 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__7;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = 0;
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__6;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__2;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__9;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__5;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1(x_20);
x_22 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__10;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_8);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_14);
x_28 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__12;
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_18);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__5(x_31);
x_33 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__13;
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_8);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__17;
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__19;
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__16;
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_8);
return x_43;
}
}
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__2(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__6___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__6(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instReprFunIndInfo___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Lean_RBNode_fold___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__2(x_1, x_3);
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lean_RBMap_toArray___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_RBMap_toArray___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__1___closed__1;
x_3 = l_Lean_RBNode_fold___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("funIndInfoExt", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_RBMap_toArray___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__5;
x_4 = l_Lean_mkMapDeclarationExtension___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBMap_toArray___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getFunInductName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("induct", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getFunInductName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_getFunInductName___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_getFunInductName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("induct_unfolding", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getFunInductName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_getFunInductName___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_getFunInductName___closed__2;
x_4 = l_Lean_Name_append(x_1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_getFunInductName___closed__4;
x_6 = l_Lean_Name_append(x_1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Meta_getFunInductName(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_getFunCasesName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fun_cases", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getFunCasesName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_getFunCasesName___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_getFunCasesName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fun_cases_unfolding", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getFunCasesName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_getFunCasesName___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_getFunCasesName___closed__2;
x_4 = l_Lean_Name_append(x_1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_getFunCasesName___closed__4;
x_6 = l_Lean_Name_append(x_1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Meta_getFunCasesName(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_getMutualInductName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mutual_induct", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getMutualInductName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_getMutualInductName___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_getMutualInductName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mutual_induct_unfolding", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getMutualInductName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_getMutualInductName___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_getMutualInductName___closed__2;
x_4 = l_Lean_Name_append(x_1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_getMutualInductName___closed__4;
x_6 = l_Lean_Name_append(x_1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Meta_getMutualInductName(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
if (x_1 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = 0;
x_12 = l_Lean_Meta_getFunInductName(x_2, x_11);
x_13 = l_Lean_realizeGlobalConstNoOverloadCore(x_12, x_3, x_4, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_7, 0, x_15);
lean_ctor_set(x_13, 0, x_7);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_7, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_free_object(x_7);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = l_Lean_Exception_isInterrupt(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isRuntime(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
x_23 = lean_box(0);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
return x_13;
}
}
else
{
return x_13;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = l_Lean_Exception_isInterrupt(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Exception_isRuntime(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
}
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_dec(x_6);
x_33 = 0;
x_34 = l_Lean_Meta_getFunCasesName(x_2, x_33);
x_35 = l_Lean_realizeGlobalConstNoOverloadCore(x_34, x_3, x_4, x_32);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_ctor_set(x_7, 0, x_37);
lean_ctor_set(x_35, 0, x_7);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_35);
lean_ctor_set(x_7, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_7);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_free_object(x_7);
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = l_Lean_Exception_isInterrupt(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = l_Lean_Exception_isRuntime(x_42);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_42);
x_45 = lean_box(0);
lean_ctor_set_tag(x_35, 0);
lean_ctor_set(x_35, 0, x_45);
return x_35;
}
else
{
return x_35;
}
}
else
{
return x_35;
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_35, 0);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_35);
x_48 = l_Lean_Exception_isInterrupt(x_46);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_Exception_isRuntime(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_46);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_47);
return x_52;
}
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
}
}
}
}
else
{
lean_dec(x_7);
if (x_1 == 0)
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_6, 1);
lean_inc(x_54);
lean_dec(x_6);
x_55 = 0;
x_56 = l_Lean_Meta_getFunInductName(x_2, x_55);
x_57 = l_Lean_realizeGlobalConstNoOverloadCore(x_56, x_3, x_4, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_58);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_65 = x_57;
} else {
 lean_dec_ref(x_57);
 x_65 = lean_box(0);
}
x_66 = l_Lean_Exception_isInterrupt(x_63);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = l_Lean_Exception_isRuntime(x_63);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_63);
x_68 = lean_box(0);
if (lean_is_scalar(x_65)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_65;
 lean_ctor_set_tag(x_69, 0);
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
return x_69;
}
else
{
lean_object* x_70; 
if (lean_is_scalar(x_65)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_65;
}
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_64);
return x_70;
}
}
else
{
lean_object* x_71; 
if (lean_is_scalar(x_65)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_65;
}
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_64);
return x_71;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_6, 1);
lean_inc(x_72);
lean_dec(x_6);
x_73 = 0;
x_74 = l_Lean_Meta_getFunCasesName(x_2, x_73);
x_75 = l_Lean_realizeGlobalConstNoOverloadCore(x_74, x_3, x_4, x_72);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_76);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_75, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_75, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_83 = x_75;
} else {
 lean_dec_ref(x_75);
 x_83 = lean_box(0);
}
x_84 = l_Lean_Exception_isInterrupt(x_81);
if (x_84 == 0)
{
uint8_t x_85; 
x_85 = l_Lean_Exception_isRuntime(x_81);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_81);
x_86 = lean_box(0);
if (lean_is_scalar(x_83)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_83;
 lean_ctor_set_tag(x_87, 0);
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_82);
return x_87;
}
else
{
lean_object* x_88; 
if (lean_is_scalar(x_83)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_83;
}
lean_ctor_set(x_88, 0, x_81);
lean_ctor_set(x_88, 1, x_82);
return x_88;
}
}
else
{
lean_object* x_89; 
if (lean_is_scalar(x_83)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_83;
}
lean_ctor_set(x_89, 0, x_81);
lean_ctor_set(x_89, 1, x_82);
return x_89;
}
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_6);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_6, 0);
lean_dec(x_91);
x_92 = lean_box(0);
lean_ctor_set(x_6, 0, x_92);
return x_6;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_6, 1);
lean_inc(x_93);
lean_dec(x_6);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_6);
if (x_96 == 0)
{
return x_6;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_6, 0);
x_98 = lean_ctor_get(x_6, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_6);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Meta_getFunInduct_x3f(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_setFunIndInfo___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___boxed), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_setFunIndInfo___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_panic___at_Lean_Meta_setFunIndInfo___spec__1___closed__1;
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_funIndInfoExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_setFunIndInfo___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_setFunIndInfo___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("!(funIndInfoExt.contains ( __do_lift._@.Lean.Meta.Tactic.FunIndInfo._hyg.500.0 ) funIndInfo.funIndName)\n  ", 106, 106);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_setFunIndInfo___closed__5;
x_2 = l_Lean_Meta_setFunIndInfo___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.FunIndInfo", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.setFunIndInfo", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_setFunIndInfo___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_setFunIndInfo___closed__8;
x_2 = l_Lean_Meta_setFunIndInfo___closed__9;
x_3 = lean_unsigned_to_nat(75u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Meta_setFunIndInfo___closed__7;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setFunIndInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = l_Lean_Meta_instInhabitedFunIndInfo;
x_11 = l_Lean_Meta_setFunIndInfo___closed__1;
lean_inc(x_9);
x_12 = l_Lean_MapDeclarationExtension_contains___rarg(x_10, x_11, x_8, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_2);
x_13 = lean_st_ref_take(x_3, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 4);
lean_dec(x_18);
x_19 = l_Lean_MapDeclarationExtension_insert___rarg(x_11, x_17, x_9, x_1);
x_20 = l_Lean_Meta_setFunIndInfo___closed__4;
lean_ctor_set(x_14, 4, x_20);
lean_ctor_set(x_14, 0, x_19);
x_21 = lean_st_ref_set(x_3, x_14, x_15);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
x_30 = lean_ctor_get(x_14, 2);
x_31 = lean_ctor_get(x_14, 3);
x_32 = lean_ctor_get(x_14, 5);
x_33 = lean_ctor_get(x_14, 6);
x_34 = lean_ctor_get(x_14, 7);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_35 = l_Lean_MapDeclarationExtension_insert___rarg(x_11, x_28, x_9, x_1);
x_36 = l_Lean_Meta_setFunIndInfo___closed__4;
x_37 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_32);
lean_ctor_set(x_37, 6, x_33);
lean_ctor_set(x_37, 7, x_34);
x_38 = lean_st_ref_set(x_3, x_37, x_15);
lean_dec(x_3);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_9);
lean_dec(x_1);
x_43 = l_Lean_Meta_setFunIndInfo___closed__10;
x_44 = l_panic___at_Lean_Meta_setFunIndInfo___spec__1(x_43, x_2, x_3, x_7);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_instInhabitedFunIndInfo;
x_10 = l_Lean_Meta_setFunIndInfo___closed__1;
x_11 = 0;
x_12 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_9, x_10, x_8, x_1, x_11);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_instInhabitedFunIndInfo;
x_17 = l_Lean_Meta_setFunIndInfo___closed__1;
x_18 = 0;
x_19 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_16, x_17, x_15, x_1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_getFunIndInfoForInduct_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = l_Lean_Meta_getFunInduct_x3f(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_Lean_Meta_getFunIndInfoForInduct_x3f(x_15, x_3, x_4, x_14);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Meta_getFunIndInfo_x3f(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_FunIndInfo(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReservedNameAction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_FunIndParamKind_noConfusion___rarg___closed__1 = _init_l_Lean_Meta_FunIndParamKind_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_FunIndParamKind_noConfusion___rarg___closed__1);
l_Lean_Meta_instBEqFunIndParamKind___closed__1 = _init_l_Lean_Meta_instBEqFunIndParamKind___closed__1();
lean_mark_persistent(l_Lean_Meta_instBEqFunIndParamKind___closed__1);
l_Lean_Meta_instBEqFunIndParamKind = _init_l_Lean_Meta_instBEqFunIndParamKind();
lean_mark_persistent(l_Lean_Meta_instBEqFunIndParamKind);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__1 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__1);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__2 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__2);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__3 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__3);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__4 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__4);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__5 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__5);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__6 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__6);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__7 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__7);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__8 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__8);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__9 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__9);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__10 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__10);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__11 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__11);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__12 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__12);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__13 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__13);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__14 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__14);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__15 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__15);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__16 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__16();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__16);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__17 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__17();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__17);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__18 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__18();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__18);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__19 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__19();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__19);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__20 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__20();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____closed__20);
l_Lean_Meta_instReprFunIndParamKind___closed__1 = _init_l_Lean_Meta_instReprFunIndParamKind___closed__1();
lean_mark_persistent(l_Lean_Meta_instReprFunIndParamKind___closed__1);
l_Lean_Meta_instReprFunIndParamKind = _init_l_Lean_Meta_instReprFunIndParamKind();
lean_mark_persistent(l_Lean_Meta_instReprFunIndParamKind);
l_Lean_Meta_instInhabitedFunIndParamKind = _init_l_Lean_Meta_instInhabitedFunIndParamKind();
l_Lean_Meta_instInhabitedFunIndInfo___closed__1 = _init_l_Lean_Meta_instInhabitedFunIndInfo___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedFunIndInfo___closed__1);
l_Lean_Meta_instInhabitedFunIndInfo___closed__2 = _init_l_Lean_Meta_instInhabitedFunIndInfo___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedFunIndInfo___closed__2);
l_Lean_Meta_instInhabitedFunIndInfo = _init_l_Lean_Meta_instInhabitedFunIndInfo();
lean_mark_persistent(l_Lean_Meta_instInhabitedFunIndInfo);
l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__1 = _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__1();
lean_mark_persistent(l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__1);
l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__2 = _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__2();
lean_mark_persistent(l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__2);
l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__3 = _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__3();
lean_mark_persistent(l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__3);
l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__4 = _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__4();
lean_mark_persistent(l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__4);
l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__5 = _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__5();
lean_mark_persistent(l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__5);
l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__6 = _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__6();
lean_mark_persistent(l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__6);
l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__7 = _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__7();
lean_mark_persistent(l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__7);
l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__8 = _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__8();
lean_mark_persistent(l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__8);
l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__9 = _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__9();
lean_mark_persistent(l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__9);
l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__10 = _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__10();
lean_mark_persistent(l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__10);
l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__11 = _init_l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__11();
lean_mark_persistent(l_Array_Array_repr___at___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____spec__1___closed__11);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__1 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__1);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__2 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__2);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__3 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__3);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__4 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__4);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__5 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__5);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__6 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__6);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__7 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__7);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__8 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__8);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__9 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__9);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__10 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__10);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__11 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__11);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__12 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__12);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__13 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__13);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__14 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__14);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__15 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__15);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__16 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__16();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__16);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__17 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__17();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__17);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__18 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__18();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__18);
l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__19 = _init_l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__19();
lean_mark_persistent(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____closed__19);
l_Lean_Meta_instReprFunIndInfo___closed__1 = _init_l_Lean_Meta_instReprFunIndInfo___closed__1();
lean_mark_persistent(l_Lean_Meta_instReprFunIndInfo___closed__1);
l_Lean_Meta_instReprFunIndInfo = _init_l_Lean_Meta_instReprFunIndInfo();
lean_mark_persistent(l_Lean_Meta_instReprFunIndInfo);
l_Lean_RBMap_toArray___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__1___closed__1 = _init_l_Lean_RBMap_toArray___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__1___closed__1();
lean_mark_persistent(l_Lean_RBMap_toArray___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____spec__1___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____closed__5);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_funIndInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_funIndInfoExt);
lean_dec_ref(res);
}l_Lean_Meta_getFunInductName___closed__1 = _init_l_Lean_Meta_getFunInductName___closed__1();
lean_mark_persistent(l_Lean_Meta_getFunInductName___closed__1);
l_Lean_Meta_getFunInductName___closed__2 = _init_l_Lean_Meta_getFunInductName___closed__2();
lean_mark_persistent(l_Lean_Meta_getFunInductName___closed__2);
l_Lean_Meta_getFunInductName___closed__3 = _init_l_Lean_Meta_getFunInductName___closed__3();
lean_mark_persistent(l_Lean_Meta_getFunInductName___closed__3);
l_Lean_Meta_getFunInductName___closed__4 = _init_l_Lean_Meta_getFunInductName___closed__4();
lean_mark_persistent(l_Lean_Meta_getFunInductName___closed__4);
l_Lean_Meta_getFunCasesName___closed__1 = _init_l_Lean_Meta_getFunCasesName___closed__1();
lean_mark_persistent(l_Lean_Meta_getFunCasesName___closed__1);
l_Lean_Meta_getFunCasesName___closed__2 = _init_l_Lean_Meta_getFunCasesName___closed__2();
lean_mark_persistent(l_Lean_Meta_getFunCasesName___closed__2);
l_Lean_Meta_getFunCasesName___closed__3 = _init_l_Lean_Meta_getFunCasesName___closed__3();
lean_mark_persistent(l_Lean_Meta_getFunCasesName___closed__3);
l_Lean_Meta_getFunCasesName___closed__4 = _init_l_Lean_Meta_getFunCasesName___closed__4();
lean_mark_persistent(l_Lean_Meta_getFunCasesName___closed__4);
l_Lean_Meta_getMutualInductName___closed__1 = _init_l_Lean_Meta_getMutualInductName___closed__1();
lean_mark_persistent(l_Lean_Meta_getMutualInductName___closed__1);
l_Lean_Meta_getMutualInductName___closed__2 = _init_l_Lean_Meta_getMutualInductName___closed__2();
lean_mark_persistent(l_Lean_Meta_getMutualInductName___closed__2);
l_Lean_Meta_getMutualInductName___closed__3 = _init_l_Lean_Meta_getMutualInductName___closed__3();
lean_mark_persistent(l_Lean_Meta_getMutualInductName___closed__3);
l_Lean_Meta_getMutualInductName___closed__4 = _init_l_Lean_Meta_getMutualInductName___closed__4();
lean_mark_persistent(l_Lean_Meta_getMutualInductName___closed__4);
l_panic___at_Lean_Meta_setFunIndInfo___spec__1___closed__1 = _init_l_panic___at_Lean_Meta_setFunIndInfo___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_setFunIndInfo___spec__1___closed__1);
l_Lean_Meta_setFunIndInfo___closed__1 = _init_l_Lean_Meta_setFunIndInfo___closed__1();
lean_mark_persistent(l_Lean_Meta_setFunIndInfo___closed__1);
l_Lean_Meta_setFunIndInfo___closed__2 = _init_l_Lean_Meta_setFunIndInfo___closed__2();
lean_mark_persistent(l_Lean_Meta_setFunIndInfo___closed__2);
l_Lean_Meta_setFunIndInfo___closed__3 = _init_l_Lean_Meta_setFunIndInfo___closed__3();
lean_mark_persistent(l_Lean_Meta_setFunIndInfo___closed__3);
l_Lean_Meta_setFunIndInfo___closed__4 = _init_l_Lean_Meta_setFunIndInfo___closed__4();
lean_mark_persistent(l_Lean_Meta_setFunIndInfo___closed__4);
l_Lean_Meta_setFunIndInfo___closed__5 = _init_l_Lean_Meta_setFunIndInfo___closed__5();
lean_mark_persistent(l_Lean_Meta_setFunIndInfo___closed__5);
l_Lean_Meta_setFunIndInfo___closed__6 = _init_l_Lean_Meta_setFunIndInfo___closed__6();
lean_mark_persistent(l_Lean_Meta_setFunIndInfo___closed__6);
l_Lean_Meta_setFunIndInfo___closed__7 = _init_l_Lean_Meta_setFunIndInfo___closed__7();
lean_mark_persistent(l_Lean_Meta_setFunIndInfo___closed__7);
l_Lean_Meta_setFunIndInfo___closed__8 = _init_l_Lean_Meta_setFunIndInfo___closed__8();
lean_mark_persistent(l_Lean_Meta_setFunIndInfo___closed__8);
l_Lean_Meta_setFunIndInfo___closed__9 = _init_l_Lean_Meta_setFunIndInfo___closed__9();
lean_mark_persistent(l_Lean_Meta_setFunIndInfo___closed__9);
l_Lean_Meta_setFunIndInfo___closed__10 = _init_l_Lean_Meta_setFunIndInfo___closed__10();
lean_mark_persistent(l_Lean_Meta_setFunIndInfo___closed__10);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
